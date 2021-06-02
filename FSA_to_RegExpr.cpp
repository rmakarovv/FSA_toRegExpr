/**
 * FSA to RegExpr translator.
 *
 * @author Roman Makarov, github.com/rmakarovv
 */

#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <map>
#include <set>

using namespace std;

class State;

// This class allows storing transitions with pointers to endpoints
class Transition {
public:
    std::string command;
    State* from;
    State* to;

    Transition(std::string c, State *from, State *to) {
        this->command = c;
        this->from = from;
        this->to = to;
    }

    bool operator == (const Transition& s1) const {
        return (this->command == s1.command && this->from == s1.from);
    }
};

// This class allows storing states with transitions from them
class State {
public:
    std::string name;
    std::vector<Transition> transitions;

    State(){}

    State(std::string n) {
        name = n;
    }

    State(const State *s) {
        this->name = s->name;
        this->transitions = s->transitions;
    }

    bool operator == (const State* s1) const {
        return (this->name == s1->name);
    }
};

// Overloaded operators for States
bool operator < (const State& s1, const State& s2) {
    return (s2.name < s1.name);
}
bool operator == (const State& s1, const State& s2) {
    return (s1.name == s2.name);
}


void looped(string **reg, const int n) {
    string **temp;
    temp = new string*[n];
    for (int i = 0; i < n; ++i) {
        temp[i] = new string[n];
    }
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            for (int k = 0; k < n; ++k) {
                temp[j][k] = "(" + reg[j][i] + ")(" + reg[i][i] + ")*("
                             + reg[i][k] + ")|(" + reg[j][k] + ")";
            }
        }

        for (int j = 0; j < n; ++j) {
            for (int k = 0; k < n; ++k) {
                reg[j][k] = temp[j][k];
            }
        }
    }
}

/*
 * This function creates a regular expression using Kleene's algorithm
 * The input that is needed: vector of all states, initial state and vector of final states
 */
string createRegExpr(vector<State> states, const State& initial, vector<State> final) {
    const int n = states.size();
    string regExpr[n][n], regEx, temp[n][n];
    int initialState = -1;

    // Check if initial state is defined
    for (int i = 0; i < n; ++i) {
        if (states[i] == initial)
            initialState = i;
    }
    if (initialState == -1) {
        return "initial state is not defined";
    }

    // Generating R(-1)
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            regEx = "";
            for (const Transition& el : states[i].transitions) {
                if (el.to == states[j]) {
                    regEx += el.command + "|";
                }
            }

            if (regEx.empty() && !(states[i] == states[j])) {
                regExpr[i][j] = "{}";
            } else {
                if (states[i] == states[j]) regEx += "eps";
                else regEx = regEx.substr(0, regEx.size() - 1);
                regExpr[i][j] = regEx;
            }
        }
    }


    string **reg;
    reg = new string*[n];
    for (int i = 0; i < n; ++i) {
        reg[i] = new string[n];
    }
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            reg[i][j] = regExpr[i][j];
        }
    }
    // Computing R(0), R(1), R(2) .... R(n-1) until we get to the answer
    // So the cycle is repeated n times.
    looped(reg, n);

    // Finalizing the computation and converting result to string
    string regExprFinal = "";
    for (int i = 0; i < n; ++i) {
        if (find(final.begin(), final.end(), states[i]) != final.end()) {
            regExprFinal += reg[initialState][i] + "|";
        }
    }
    const int s = regExprFinal.size();
    if (regExprFinal.empty()) {
        return "{}";
    } else if (regExprFinal[s - 1] == '|')
        regExprFinal = regExprFinal.substr(0, s - 1);
    return regExprFinal;
}


class CheckForErrors {
    // This class is created to store all functions to detect errors
public:

    CheckForErrors(){}

    // Check for E0
    static bool inputFileIsMalformed(string states, string alpha, string init, string fin, string trans) {
        if (states.substr(0, 8) != "states=[" || states[states.length() - 1] != ']')
            return false;

        if (alpha.substr(0, 7) != "alpha=[" || alpha[alpha.length() - 1] != ']')
            return false;

        if (init.substr(0, 9) != "initial=[" || init[init.length() - 1] != ']')
            return false;

        if (fin.substr(0, 11) != "accepting=[" || fin[fin.length() - 1] != ']')
            return false;

        if (trans.substr(0, 7) != "trans=[" || trans[trans.length() - 1] != ']')
            return false;

        return true;
    }

    // Check for E5
    static bool nondeterminism(const vector<Transition>& transitions) {
        vector<Transition> toCheck;
        for (const Transition &el : transitions) {
            // If the transition with the same "from" state and "command" is found
            // then FSA is nondeterministic.
            // In the class Transition operator "==" is overloaded specially for this comparison
            if (find(toCheck.begin(), toCheck.end(), el) != toCheck.end()) {
                return true;
            } else {
                toCheck.push_back(el);
            }
        }
        return false;
    }

    // To check if all states can be reached from initial set
    // simple Depth First Search is performed and sets
    // that were covered are stored in set found
    void DFS(const State& start, set<State> &found) {
        found.insert(start);
        for (const Transition& transition : start.transitions) {
            State s(transition.to);
            if (find(found.begin(), found.end(), s) == found.end())
                DFS(transition.to, found);
        }
    }

    // Check if all states in transitions, final states and initial state exist.
    // Error E1
    static bool checkStates(vector<State> allStates, const set<string>& statesInTransitions,
                     const State &initial, const vector<State> &final, ofstream &output) {

        for (const string &el : statesInTransitions) {
            State state(el);
            if (find(allStates.begin(), allStates.end(), state) == allStates.end()) {
                output << "Error:\nE1: A state '" << state.name << "' is not in the set of states";
                return false;
            }
        }

        if (find(allStates.begin(), allStates.end(), initial) == allStates.end()) {
            output << "Error:\nE1: A state '" << initial.name << "' is not in the set of states";
            return false;
        }

        for (const State &el : final) {
            if (find(allStates.begin(), allStates.end(), el) == allStates.end()) {
                output << "Error:\nE1: A state '" << el.name << "' is not in the set of states";
                return false;
            }
        }
        return true;
    }
};

// This function is used to simplify "main" and parse input states
void produceStates(vector<State> &states, string statesString){
    vector<string> words;
    int i = 7;
    if (statesString[i] == '[') {
        i++;
        while (i < statesString.length() && statesString[i] != ']') {
            string word = "";
            while (statesString[i] != ']' && statesString[i] != ',') {
                word += statesString[i];
                i++;
            }
            if (!word.empty()) {
                words.push_back(word);
                word = "";
            }
            i++;
        }
    }

    for (string &el : words) {
        State state(el);
        states.push_back(state);
    }
}

// This function is used to simplify "main" and parse input commands
void produceCommands(string alpha, int i, vector<string> &possibleCommands) {
    if (alpha[i] == '[') {
        while (alpha[i] != ']') {
            i++;
            string word = "";
            while (alpha[i] != ',' && alpha[i] != ']') {
                word += alpha[i];
                i++;
            }
            possibleCommands.push_back(word);
        }
    }
}


int main() {
    ifstream input("input.txt");
    ofstream output("output.txt");

    // Reading input.
    string statesString; input >> statesString;
    string alpha; input >> alpha;
    string initialString; input >> initialString;
    string final; input >> final;
    string trans; input >> trans;
    // Creating a class for checking errors.
    CheckForErrors errorChecker;

    bool malformed = CheckForErrors::inputFileIsMalformed(statesString, alpha, initialString, final, trans);
    if (!malformed) {
        output << "Error:\nE0: Input file is malformed";
        return 0;
    }

    // Filling the states,
    // and mapping their name of the state to the pointer to this state.
    vector<State> states;
    produceStates(states, statesString);

    map<string, State*> statesMap;
    for (State &el : states) {
        statesMap[el.name] = &el;
    }

    // filling possible transitions
    int i = 6;
    vector<string> possibleTransitions;
    produceCommands(alpha, i, possibleTransitions);

    // Creating initial state
    i = 9;
    // Check for Error E4
    if (initialString[9] == ']') {
        output << "Error:\nE4: Initial state is not defined";
        return 0;
    }
    string word = "";
    while (initialString[i] != ']') {
        word += initialString[i];
        i++;
    }
    State initial(word);

    // Parsing and filling the vector with final states
    i = 11;
    word = "";
    vector<string> accepting;
    while (final[i] != ']') {
        while (final[i] != ',' && final[i] != ']') {
            word += final[i];
            i++;
        }
        if (!word.empty()) {
            accepting.push_back(word);
        }
        word = "";
        if (final[i] != ']') i++;
    }
    vector<State> finalStates;
    for (auto & ii : accepting) {
        State state(ii);
        finalStates.push_back(state);
    }


    // Parsing all transitions and filling vector with them.
    // Additionally map and set is made for further functions.
    i = 7;
    map<string, vector<Transition>> transitions;
    vector<Transition> allTransitions;
    set<string> statesInTransitions;
    word = "";
    string tr = "", st = "";
    while (trans[i] != ']') {
        while ( trans[i] != '>') {
            word += trans[i];
            i++;
        }
        i++;
        while ( trans[i] != '>') {
            tr += trans[i];
            i++;
        }
        i++;
        while ( trans[i] != ',' && trans[i] != ']') {
            st += trans[i];
            i++;
        }
        if (trans[i] != ']') i++;
        statesInTransitions.insert(word);
        statesInTransitions.insert(st);
        Transition transition(tr, statesMap[word], statesMap[st]);
        allTransitions.push_back(transition);
        transitions[word].push_back(transition);

        word = "", tr = "", st = "";
    }

    // Filling states with transitions
    for (State &state : states) {
        state.transitions = transitions[state.name];
    }


    // Check for the Error E3
    for (Transition const &el : allTransitions) {
        if (find(possibleTransitions.begin(), possibleTransitions.end(), el.command) == possibleTransitions.end()) {
            output << "Error:\nE3: A transition '" <<  el.command << "' is not represented in the alphabet";
            return 0;
        }
    }

    // Checking that all states in transitions final states and initial state exist.
    // Error E1
    if (!CheckForErrors::checkStates(states, statesInTransitions, initial, finalStates, output)) {
        return 0;
    }

    // Checking Error E5: Nondeterminism
    if (CheckForErrors::nondeterminism(allTransitions)) {
        output << "Error:\nE5: FSA is nondeterministic";
        return 0;
    }


    // Updating information about initial state after transitions were added.
    for (State &sta : states) {
        if (sta.name == initial.name) {
            initial = sta;
            break;
        }
    }

    // This is the check for disjoint states Error E2
    set<State> statesFound;
    errorChecker.DFS(initial, statesFound);
    if (statesFound.size() < states.size()) {
        output << "Error:\nE2: Some states are disjoint";
        return 0;
    }


    for (auto const& el : transitions) {
        statesMap[el.first]->transitions = el.second;
    }


    string answer = createRegExpr(states, initial, finalStates);

    // Check for the Error E4: not defined initial state
    if (answer == "initial state is not defined") {
        output << "Error:\nE4: Initial state is not defined";
        return 0;
    }
    output << answer;

    input.close();
    output.close();

    return 0;
}
