/**
 * Implementacja uproszczonego symulatora układów cyfrowych Nysa.
 *
 * autor: Mateusz Sulimowicz
 */
#include <iostream>
#include <map>
#include <queue>
#include <regex>
#include <set>
#include <sstream>
#include <unordered_map>

using namespace std;

// ----- Sygnał -----

using signal_id = uint32_t; // numer sygnału

// To jest wektor id sygnałów będących użytkownikami danego sygnału,
// czyli takich, których wartości obliczane są
// za pomocą bramek mających na wejściu dany sygnał
using user_ids = vector<signal_id>;

// To jest poziom ewaluacji sygnału, czyli etap na którym wyznaczone
// są już wartości wszystkich sygnałów
// na wejściu bramki, której wyjściem jest dany sygnał.
using eval_lvl = uint32_t;

// To jest reprezentacja sygnału
using Signal = tuple<user_ids, bool, eval_lvl>;
#define USER_IDS 0
#define CURRENT_VALUE 1
#define EVALUATION_LEVEL 2

Signal getNewSignal() {
    vector<signal_id> user_ids;
    return make_tuple(user_ids, false, 0);
}

// ------------------

// mapa sygnałów
using signal_map = map<signal_id, Signal>;

// ----- Bramka -----

// Rodzaje bramek
enum GateType {
    AND,
    NAND,
    OR,
    NOR,
    XOR,
    NOT
};

// numer sygnału wyjściowego
using output_id = signal_id;

// To jest wektor id sygnałów będących wejściem bramki.
using input_ids = vector<signal_id>;

// To jest reprezentacja bramki
using Gate = tuple<input_ids, GateType>;
#define INPUT_IDS 0
#define GATE_TYPE 1

GateType getGateType(string &gateName) {
    if (gateName == "AND") {
        return AND;
    } else if (gateName == "NAND") {
        return NAND;
    } else if (gateName == "OR") {
        return OR;
    } else if (gateName == "NOR") {
        return NOR;
    } else if (gateName == "XOR") {
        return XOR;
    } else if (gateName == "NOT") {
        return NOT;
    } else {
        throw invalid_argument("Gate type " + gateName + " does not exist!");
    }
}

// ------------------

// mapa bramek
using gate_map = unordered_map<output_id, Gate>;

class Parser {

public:
    static bool parseData(signal_map &signals, gate_map &gates) {
        bool isInputCorrect = parseGates(gates);

        if (isInputCorrect) {
            addAllSignals(signals, gates);
            setAllSignalsUsers(signals, gates);
        }

        return isInputCorrect;
    }

private:
    inline static regex xor_gate_regex = regex(
            "[[:space:]]*XOR([[:space:]]+[1-9][[:digit:]]{0,8}){3}[[:space:]]*");
    inline static regex not_gate_regex = regex(
            "[[:space:]]*NOT([[:space:]]+[1-9][[:digit:]]{0,8}){2}[[:space:]]*");
    inline static regex casual_gate_regex =
            regex("[[:space:]]*(AND|NAND|OR|NOR)([[:space:]]+[1-9][[:digit:]]"
                  "{0,8}){3,}[[:space:]]*");

    static bool parseGates(gate_map &gates) {
        bool success = true;
        string line;
        size_t line_id = 0;
        while (getline(cin, line)) {
            ++line_id;
            success &= parseGate(line, line_id, gates);
        }

        return success;
    }

    // Parsuje bramkę z linii wejścia i wstawia ją do mapy bramek.
    // Zwraca `true` wttw bramka została sparsowana bez błędów.
    static bool parseGate(string &line, size_t line_id, gate_map &gates) {
        if (!isLineValid(line)) {
            cerr << "Error in line " << line_id << ": " << line << "\n";
            return false;
        }

        stringstream linestream(line);
        GateType gateType = parseGateType(linestream);
        signal_id output_id = parseGateOutputId(linestream);
        vector<signal_id> input_ids = parseGateInputIds(linestream);

        if (gates.contains(output_id)) {
            cerr << "Error in line " << line_id << ": "
                 << "signal " << output_id
                 << " is assigned to multiple outputs.\n";
            return false;
        }

        gates[output_id] = make_tuple(input_ids, gateType);
        return true;
    }

    static GateType parseGateType(stringstream &linestream) {
        string gateName;
        linestream >> gateName;
        return getGateType(gateName);
    }

    static signal_id parseGateOutputId(stringstream &linestream) {
        signal_id output_id;
        linestream >> output_id;
        return output_id;
    }

    static vector<signal_id> parseGateInputIds(stringstream &linestream) {
        vector<signal_id> input_ids;
        signal_id id;
        while (linestream >> id) {
            input_ids.push_back(id);
        }
        return input_ids;
    }

    static bool isLineValid(string &line) {
        return regex_match(line, xor_gate_regex) ||
               regex_match(line, not_gate_regex) ||
               regex_match(line, casual_gate_regex);
    }

    static void addAllSignals(signal_map &signals, gate_map &gates) {
        for (const auto &gateData: gates) {
            signal_id outputId = gateData.first;
            if (!signals.contains(outputId)) {
                signals[outputId] = getNewSignal();
            }

            for (signal_id id: get<INPUT_IDS>(gateData.second)) {
                if (!signals.contains(id)) {
                    signals[id] = getNewSignal();
                }
            }
        }
    }

    static void setAllSignalsUsers(signal_map &signals, gate_map &gates) {
        for (const auto &gateData: gates) {
            signal_id output_id = gateData.first;
            for (signal_id id: get<INPUT_IDS>(gateData.second)) {
                get<USER_IDS>(signals[id]).push_back(output_id);
            }
        }
    }
};

class CycleFinder {

public:
    // Sprawdza, czy dany układ logiczny zawiera cykl.
    static bool hasCircuitCycle(const set<signal_id> &inputSignalsIDs,
                                signal_map &signals) {
        bool res = false;

        if (!signals.empty() && inputSignalsIDs.empty()) {
            // Jeśli nie istnieje sygnał, który nie jest wyjściem żadnej bramki,
            // to każdy sygnał jest wyjściem jakiejś bramki, więc musi być cykl.
            return true;
        }

        unordered_map<signal_id, bool> visited = getVisitedMap(signals);
        unordered_map<signal_id, bool> visitedInCurrentTraversal = getVisitedMap(
                signals);
        for (signal_id id: inputSignalsIDs) {
            res |= existsCycle(id, signals, visited, visitedInCurrentTraversal);
        }
        return res;
    }

private:
    static unordered_map<signal_id, bool>
    getVisitedMap(const signal_map &signals) {
        unordered_map<signal_id, bool> visited;
        visited.reserve(signals.size());
        for (pair<signal_id, Signal> signalData: signals) {
            visited[signalData.first] = false;
        }
        return visited;
    }

    // Sprawdza, czy startując od sygnału o numerze `currentId` wejdziemy w cykl.
    static bool existsCycle(signal_id currentId, signal_map &signals,
                            unordered_map<signal_id, bool> &visited,
                            unordered_map<signal_id, bool> &visitedInCurrentTraversal) {
        // Przejście DFS po grafie sygnałów, startując od sygnału o numerze
        // `currentId`. W grafie sygnałów istnieje krawędź (s1, s2) wttw s2 jest
        // wyjściem bramki, której wejściem jest s1.
        if (visitedInCurrentTraversal[currentId]) {
            return true;
        } else if (visited[currentId]) {
            // Jeśli sygnał, na który wchodzimy, był już odwiedzony,
            // to nie ma potrzeby znowu przez niego przechodzić
            return false;
        } else {
            bool res = false;
            visited[currentId] = true;
            visitedInCurrentTraversal[currentId] = true;
            for (signal_id id: get<USER_IDS>(signals[currentId])) {
                res |= existsCycle(id, signals, visited,
                                   visitedInCurrentTraversal);
            }
            visitedInCurrentTraversal[currentId] = false;
            return res;
        }
    }
};

class EvaluationOrderProvider {

public:
    // Ustala kolejność, w jakiej powinny być wyznaczone wartości na sygnałach.
    static vector<signal_id>
    getEvaluationOrder(signal_map &signals,
                       const set<signal_id> &inputSignalsIDs) {
        setEvaluationLevels(signals, inputSignalsIDs);

        vector<pair<signal_id, eval_lvl>> signalEvaluationLevels =
                getEvaluationLevels(signals);
        // Sortuje wektor par (numer sygnału, poziom ewaluacji) niemalejąco po
        // poziomie ewaluacji.
        sort(signalEvaluationLevels.begin(), signalEvaluationLevels.end(),
             evaluationLevelComparator);

        // Tworzy wektor numerów sygnałów uporządkowany tak, że
        // wartości na sygnałach powinny być wyznaczone w kolejności
        // występowania na wektorze.
        vector<signal_id> evaluationOrder;
        evaluationOrder.reserve(signalEvaluationLevels.size());
        for (pair<signal_id, eval_lvl> p: signalEvaluationLevels) {
            evaluationOrder.push_back(p.first);
        }

        return evaluationOrder;
    }

private:
    // Wyznacza poziom ewaluacji sygnału o numerze `currentId`.
    static void
    setEvaluationLevel(signal_id currentId, eval_lvl evaluationLevel,
                       signal_map &signals) {
        eval_lvl &currentEvaluationLevel = get<EVALUATION_LEVEL>(
                signals[currentId]);
        eval_lvl newEvaluationLevel = max(currentEvaluationLevel,
                                          evaluationLevel);
        currentEvaluationLevel = newEvaluationLevel;
    }

    // Dla każdego sygnału, wyznacza jego poziom ewaluacji.
    static void setEvaluationLevels(signal_map &signals,
                                    const set<signal_id> &inputSignalsIDs) {
        // Za pomocą BFS, ustalane są poziomy ewaluacji wszystkich sygnałów układu.
        queue<signal_id> signalsQueue;
        for (signal_id id: inputSignalsIDs) {
            // Algorytm zaczyna na sygnałach wejściowych.
            signalsQueue.push(id);
        }

        while (!signalsQueue.empty()) {
            signal_id currentId = signalsQueue.front();
            signalsQueue.pop();
            eval_lvl currentEvaluationLevel =
                    get<EVALUATION_LEVEL>(signals[currentId]);
            for (signal_id id: get<USER_IDS>(signals[currentId])) {
                setEvaluationLevel(id, currentEvaluationLevel + 1, signals);
                signalsQueue.push(id);
            }
        }
    }

    // Dla sygnałów s1, s2,
    // s1 < s2 wttw wartość na s1 musi być wyznaczona wcześniej niż wartość na s2,
    // czyli wttw s1.evaluationLevel < s2.evaluationLevel.
    static bool evaluationLevelComparator(const pair<signal_id, eval_lvl> &a,
                                          const pair<signal_id, eval_lvl> &b) {
        return a.second < b.second;
    }

    static vector<pair<signal_id, eval_lvl>>
    getEvaluationLevels(const signal_map &signals) {
        vector<pair<signal_id, eval_lvl>> signalEvaluationLevels;
        for (const auto &signal: signals) {
            signal_id currentId = signal.first;
            eval_lvl currentEvaluationLevel = get<EVALUATION_LEVEL>(
                    signal.second);
            if (currentEvaluationLevel > 0) {
                // Sygnał nie jest sygnałem wejściowym.
                signalEvaluationLevels.emplace_back(currentId,
                                                    currentEvaluationLevel);
            }
        }
        return signalEvaluationLevels;
    }
};

class GateExecutor {

public:
    // Wyznacza wartość sygnału o numerze `outputId`.
    static bool evaluate(const Gate &gate, signal_map &signals) {
        GateType gateType = get<GATE_TYPE>(gate);
        vector<signal_id> inputIds = get<INPUT_IDS>(gate);

        switch (gateType) {
            case AND:
                return gateAND(inputIds, signals);
            case OR:
                return gateOR(inputIds, signals);
            case NAND:
                return gateNAND(inputIds, signals);
            case NOR:
                return gateNOR(inputIds, signals);
            case NOT:
                return gateNOT(inputIds, signals);
            case XOR:
                return gateXOR(inputIds, signals);
            default:
                return false;
        }
    }

private:
    static bool
    gateAND(const vector<signal_id> &inputIds, signal_map &signals) {
        bool res = true;
        for (signal_id id: inputIds) {
            Signal signal = signals[id];
            res &= get<CURRENT_VALUE>(signal);
        }
        return res;
    }

    static bool
    gateNAND(const vector<signal_id> &inputIds, signal_map &signals) {
        return !gateAND(inputIds, signals);
    }

    static bool gateOR(const vector<signal_id> &inputIds, signal_map &signals) {
        bool res = false;
        for (signal_id id: inputIds) {
            Signal signal = signals[id];
            res |= get<CURRENT_VALUE>(signal);
        }
        return res;
    }

    static bool
    gateNOR(const vector<signal_id> &inputIds, signal_map &signals) {
        return !gateOR(inputIds, signals);
    }

    static bool
    gateNOT(const vector<signal_id> &inputIds, signal_map &signals) {
        return !get<CURRENT_VALUE>(signals[inputIds[0]]);
    }

    static bool
    gateXOR(const vector<signal_id> &inputIds, signal_map &signals) {
        bool a = get<CURRENT_VALUE>(signals[inputIds[0]]);
        bool b = get<CURRENT_VALUE>(signals[inputIds[1]]);
        return (a && !b) || (!a && b);
    }
};

// Symulator układów cyfrowych Nysa.
class Nysa {

public:
    static void execute(const gate_map &gates, signal_map &signals) {
        set<signal_id> inputIds = getInputIds(signals, gates);

        if (CycleFinder::hasCircuitCycle(inputIds, signals)) {
            cerr << "Error: "
                 << "sequential logic analysis has not yet been implemented.\n";
            return;
        }

        vector<signal_id> evaluationOrder =
                EvaluationOrderProvider::getEvaluationOrder(signals, inputIds);
        do {
            evaluateSignals(gates, evaluationOrder, signals);
        } while (prepareNextCombination(signals, inputIds));
    }

private:
    static set<signal_id> getInputIds(const signal_map &signals,
                                      const gate_map &gates) {
        set<signal_id> inputIds;
        for (const auto &signalData: signals) {
            signal_id id = signalData.first;
            if (!gates.contains(id)) {
                inputIds.insert(id);
            }
        }
        return inputIds;
    }

    // Wyznacza, za pomocą odpowiedniej bramki, wartość sygnału o numerze `id`.
    static void calculateSignalValue(signal_id id, signal_map &signals,
                                     const gate_map &gates) {
        get<CURRENT_VALUE>(signals.at(id)) =
                GateExecutor::evaluate(gates.at(id), signals);
    }

    // Przygotowuje następną kombinację wartości na sygnałach wejściowych.
    // Zwraca `true` wttw istnieje następna, jeszcze niewykorzystana, kombinacja
    // wejść.
    static bool prepareNextCombination(signal_map &signals,
                                       const set<signal_id> &inputIds) {
        for (reverse_iterator rit = inputIds.rbegin(); rit != inputIds.rend();
             ++rit) {
            signal_id currentId = *rit;
            bool &currentValue = get<CURRENT_VALUE>(signals[currentId]);
            if (currentValue) {
                currentValue = false;
            } else {
                currentValue = true;
                return true;
            }
        }
        return false;
    }

    // Wypisuje na standardowe wyjście aktualne wartości sygnałów,
    // w kolejności rosnących numerów sygnałów.
    static void printCurrentSignalValues(const signal_map &signals) {
        for (const auto &signal: signals) {
            Signal s = signal.second;
            cout << get<CURRENT_VALUE>(s);
        }
        cout << "\n";
    }

    // Wyznacza wartości wszystkich sygnałów układu w odpowiedniej kolejności.
    static void evaluateSignals(const gate_map &gates,
                                const vector<signal_id> &evaluationOrder,
                                signal_map &signals) {
        for (signal_id id: evaluationOrder) {
            calculateSignalValue(id, signals, gates);
        }
        printCurrentSignalValues(signals);
    }
};

int main() {
    gate_map gates;
    signal_map signals;

    bool isInputCorrect = Parser::parseData(signals, gates);

    if (isInputCorrect) {
        Nysa::execute(gates, signals);
    }
    return 0;
}
