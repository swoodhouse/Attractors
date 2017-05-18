#include "stdafx.h"

BDD representState(const Cudd& manager, const std::vector<bool>& values) {
    BDD bdd = manager.bddOne();
    for (int i = 0; i < values.size(); i++) {
        BDD var = manager.bddVar(i);
        if (!values[i]) {
            var = !var;
        }
        bdd *= var;
    }
    return bdd;
}

BDD representClause(const Cudd& manager, const std::vector<int>& clause) {
    BDD bdd = manager.bddZero();
    for (auto it = std::begin(clause); it != std::end(clause); ++it) {
        BDD var = manager.bddVar(abs(*it));
        if (*it < 0) {
            var = !var;
        }
        bdd = var + bdd;
    }
    return bdd;
}

BDD representUpdateFunction(const Cudd& manager, const std::vector<std::vector<int>>& cnf) {
    BDD bdd = manager.bddOne();
    for (auto it = std::begin(cnf); it != std::end(cnf); ++it) {
        bdd = bdd * representClause(manager, *it);
    }
    return bdd;
}

inline BDD logicalEquivalence(const BDD& a, const BDD& b) {
    return !(a ^ b);
}

BDD representSyncTransitionRelation(const Cudd& manager, const std::vector<std::vector<std::vector<int>>>& network) {
    BDD bdd = manager.bddOne();
    int i = 0;
    for (auto it = std::begin(network); it != std::end(network); ++it) {
        BDD f = representUpdateFunction(manager, *it);
        BDD vPrime = manager.bddVar(network.size() + i);
        BDD transition = logicalEquivalence(vPrime, f);
        bdd = transition * bdd;
        i++;
    }
    return bdd;
}

BDD otherVarsDoNotChange(const Cudd& manager, int i, int numVars) {
    BDD bdd = manager.bddOne();
    for (int j = 0; j < numVars; j++) {
        if (j != i) {
            BDD v = manager.bddVar(j);
            BDD vPrime = manager.bddVar(numVars + j);
            bdd = bdd * logicalEquivalence(v, vPrime);
        }
    }
    return bdd;
}

BDD representAsyncTransitionRelation(const Cudd& manager, const std::vector<std::vector<std::vector<int>>>& network) {
    BDD fixpoint = manager.bddOne();
    for (size_t i = 0; i < network.size(); i++) {
        BDD v = manager.bddVar(i);
        BDD vPrime = manager.bddVar(network.size() + i);
        fixpoint = fixpoint * logicalEquivalence(v, vPrime);
    }

    BDD bdd = manager.bddZero();
    int i = 0;
    for (auto it = std::begin(network); it != std::end(network); ++it) {
        BDD v = manager.bddVar(i);
        BDD vPrime = manager.bddVar(network.size() + i);
        BDD vChanges = !logicalEquivalence(v, vPrime);
        BDD f = representUpdateFunction(manager, *it);
        BDD update = logicalEquivalence(vPrime, f) * otherVarsDoNotChange(manager, i, network.size());
        BDD transition = update * (fixpoint + vChanges);
        bdd = transition + bdd;
        i++;
    }

    return bdd;
}

BDD renameRemovingPrimes(const BDD& bdd, int numUnprimedBDDVars) {
    int *permute = new int[numUnprimedBDDVars * 2];
    for (int i = 0; i < numUnprimedBDDVars; i++) {
        permute[i] = i;
        permute[i + numUnprimedBDDVars] = i;
    }
    BDD r = bdd.Permute(permute);
    delete[] permute;
    return r;
}

inline BDD nonPrimeVariables(const Cudd& manager, int numUnprimedBDDVars) {
    return representState(manager, std::vector<bool>(numUnprimedBDDVars, true));
}

BDD primeVariables(const Cudd& manager, int numUnprimedBDDVars) {
    BDD bdd = manager.bddOne();
    for (int i = numUnprimedBDDVars; i < numUnprimedBDDVars * 2; i++) {
        BDD var = manager.bddVar(i);
        bdd *= var;
    }
    return bdd;
}

BDD immediateSuccessorStates(const Cudd& manager, const BDD& transitionBdd, const BDD& valuesBdd, int numUnprimedBDDVars) {
    BDD bdd = transitionBdd * valuesBdd;
    bdd = bdd.ExistAbstract(nonPrimeVariables(manager, numUnprimedBDDVars));
    return renameRemovingPrimes(bdd, numUnprimedBDDVars);
}

BDD forwardReachableStates(const Cudd& manager, const BDD& transitionBdd, const BDD& valuesBdd, int numUnprimedBDDVars) {
    BDD reachable = manager.bddZero();
    BDD frontier = valuesBdd;

    while (frontier != manager.bddZero()) {
        frontier = immediateSuccessorStates(manager, transitionBdd, frontier, numUnprimedBDDVars) * !reachable;
        reachable += frontier;
    }
    return reachable;
}

BDD renameAddingPrimes(const BDD& bdd, int numUnprimedBDDVars) {
    int *permute = new int[numUnprimedBDDVars * 2];
    for (int i = 0; i < numUnprimedBDDVars; i++) {
        permute[i] = i + numUnprimedBDDVars;
        permute[i + numUnprimedBDDVars] = i + numUnprimedBDDVars;
    }

    BDD r = bdd.Permute(permute);
    delete[] permute;
    return r;
}

BDD immediatePredecessorStates(const Cudd& manager, const BDD& transitionBdd, const BDD& valuesBdd, int numUnprimedBDDVars) {
    BDD bdd = renameAddingPrimes(valuesBdd, numUnprimedBDDVars);
    bdd *= transitionBdd;
    return bdd.ExistAbstract(primeVariables(manager, numUnprimedBDDVars));
}

BDD backwardReachableStates(const Cudd& manager, const BDD& transitionBdd, const BDD& valuesBdd, int numUnprimedBDDVars) {
    BDD reachable = manager.bddZero();
    BDD frontier = valuesBdd;

    while (frontier != manager.bddZero()) {
        frontier = immediatePredecessorStates(manager, transitionBdd, frontier, numUnprimedBDDVars) * !reachable;
        reachable += frontier;
    }
    return reachable;
}

BDD randomState(const Cudd& manager, const BDD& S, int numVars) {
    char *out = new char[numVars * 2];
    S.PickOneCube(out);
    std::vector<bool> values;
    for (int i = 0; i < numVars; i++) {
        if (out[i] == 0) {
            values.push_back(false);
        }
        else {
            values.push_back(true);
        }
    }
    delete[] out;
    return representState(manager, values);
}

std::list<BDD> attractorsBN(const Cudd&  manager, const BDD& transitionBdd, int numVars) {
    std::list<BDD> attractors;
    BDD S = manager.bddOne();

    while (S != manager.bddZero()) {
        BDD s = randomState(manager, S, numVars);

        for (int i = 0; i < 20; i++) {
            BDD sP = immediateSuccessorStates(manager, transitionBdd, s, numVars);
            s = randomState(manager, sP, numVars);
        }

        BDD fr = forwardReachableStates(manager, transitionBdd, s, numVars);
        BDD br = backwardReachableStates(manager, transitionBdd, s, numVars);

        if ((fr * !br) == manager.bddZero()) {
            attractors.push_back(fr);
        }

        S = S * !(s + br);
    }
    return attractors;
}

int log2(unsigned int i) {
    unsigned int r = 0;
    while (i >>= 1) r++;
    return r;
}

int bits(unsigned int i) {
    return i == 0 ? 0 : log2(i) + 1;
}

bool nthBitSet(int i, int n) {
    return (1 << n) & i;
}

BDD representUnprimedVarQN(const Cudd& manager, int var, int val, const std::vector<int>& ranges) {
    BDD bdd = manager.bddOne();
    auto lambda = [](int a, int b) { return a + bits(b); };
    int i = std::accumulate(ranges.begin(), ranges.begin() + var, 0, lambda);

    int b = bits(ranges[var]);
    for (int n = 0; n < b; n++) {
        BDD var = manager.bddVar(i);
        if (!nthBitSet(val, n)) {
            var = !var;
        }
        bdd *= var;
        i++;
    }

    return bdd;
}

BDD representPrimedVarQN(const Cudd& manager, int var, int val, const std::vector<int>& ranges) {
    BDD bdd = manager.bddOne();
    auto lambda = [](int a, int b) { return a + bits(b); };
    int i = std::accumulate(ranges.begin(), ranges.end(), 0, lambda) + std::accumulate(ranges.begin(), ranges.begin() + var, 0, lambda);

    int b = bits(ranges[var]);
    for (int n = 0; n < b; n++) {
        BDD var = manager.bddVar(i);
        if (!nthBitSet(val, n)) {
            var = !var;
        }
        bdd *= var;
        i++;
    }

    return bdd;
}

BDD representStateQN(const Cudd& manager, const std::vector<int>& vars, const std::vector<int>& values, const std::vector<int>& ranges) {
    BDD bdd = manager.bddOne();
    for (size_t i = 0; i < vars.size(); i++) {
        int var = vars[i];
        int val = values[i];
        bdd *= representUnprimedVarQN(manager, var, val, ranges);
    }
    return bdd;
}

void removeInvalidBitCombinations(const Cudd& manager, BDD& S, const std::vector<int>& ranges) {
    for (int var = 0; var < ranges.size(); var++) {
        if (ranges[var] > 0) {
            int b = bits(ranges[var]);
            int theoreticalMax = (1 << b) - 1;

            for (int val = ranges[var] + 1; val <= theoreticalMax; val++) {
                S *= !representUnprimedVarQN(manager, var, val, ranges);
            }
        }
    }
}

BDD representSyncQNTransitionRelation(const Cudd& manager, const std::vector<int>& ranges, const std::vector<std::vector<int>>& inputVars,
    const std::vector<std::vector<std::vector<int>>>& inputValues, const std::vector<std::vector<int>>& outputValues) {
    BDD bdd = manager.bddOne();
    int v = 0;

    for (int v = 0; v < ranges.size(); v++) {
        if (ranges[v] > 0) {
            const auto& iVars = inputVars[v];
            const auto& iValues = inputValues[v];
            const auto& oValues = outputValues[v];

            std::vector<BDD> states(ranges[v] + 1, manager.bddZero());
            for (int i = 0; i < oValues.size(); i++) {
                states[oValues[i]] += representStateQN(manager, iVars, iValues[i], ranges);
            }
            for (int val = 0; val <= ranges[v]; val++) {
                BDD vPrime = representPrimedVarQN(manager, v, val, ranges);
                bdd *= logicalEquivalence(states[val], vPrime);
            }
        }
    }
    return bdd;
}

std::list<BDD> attractorsQN(Cudd manager, const BDD& transitionBdd, const std::vector<int>& ranges, const BDD& statesToRemove) {
    auto lambda = [](int a, int b) { return a + bits(b); };
    int numUnprimedBDDVars = std::accumulate(ranges.begin(), ranges.end(), 0, lambda);
    std::list<BDD> attractors;
    BDD S = manager.bddOne();
    removeInvalidBitCombinations(manager, S, ranges);
    S *= !statesToRemove;

    while (S != manager.bddZero()) {
        BDD s = randomState(manager, S, numUnprimedBDDVars);

        for (int i = 0; i < 20; i++) {
            BDD sP = immediateSuccessorStates(manager, transitionBdd, s, numUnprimedBDDVars);
            s = randomState(manager, sP, numUnprimedBDDVars);
        }

        BDD fr = forwardReachableStates(manager, transitionBdd, s, numUnprimedBDDVars);
        BDD br = backwardReachableStates(manager, transitionBdd, s, numUnprimedBDDVars);

        if ((fr * !br) == manager.bddZero()) {
            attractors.push_back(fr);
        }

        S *= !(s + br);
    }
    return attractors;
}

BDD varDoesChangeQN(const Cudd& manager, int var, const std::vector<int>& ranges) {
    auto lambda = [](int a, int b) { return a + bits(b); };
    int start = std::accumulate(ranges.begin(), ranges.begin() + var, 0, lambda);
    int numUnprimedBDDVars = std::accumulate(ranges.begin(), ranges.end(), 0, lambda);
    int numBits = bits(ranges[var]);

    BDD bdd = manager.bddZero();
    for (int i = start; i < start + numBits; i++) {
        BDD v = manager.bddVar(i);
        BDD vPrime = manager.bddVar(i + numUnprimedBDDVars);
        bdd += v ^ vPrime;
    }
    return bdd;
}

BDD otherVarsDoNotChangeQN(const Cudd& manager, int var, const std::vector<int>& ranges) {
    BDD bdd = manager.bddOne();
    for (int i = 0; i < ranges.size(); i++) {
        if (i != var) {
            bdd *= !varDoesChangeQN(manager, i, ranges);
        }
    }

    return bdd;
}

BDD representAsyncQNTransitionRelation(const Cudd& manager, const std::vector<int>& ranges, const std::vector<std::vector<int>>& inputVars,
    const std::vector<std::vector<std::vector<int>>>& inputValues, const std::vector<std::vector<int>>& outputValues) {
    auto lambda = [](int a, int b) { return a + bits(b); };
    int numUnprimedBDDVars = std::accumulate(ranges.begin(), ranges.end(), 0, lambda);

    BDD fixpoint = manager.bddOne();
    for (int i = 0; i < numUnprimedBDDVars; i++) {
        BDD v = manager.bddVar(i);
        BDD vPrime = manager.bddVar(numUnprimedBDDVars + i);
        fixpoint *= logicalEquivalence(v, vPrime);
    }

    BDD bdd = manager.bddZero();
    int v = 0;

    for (int v = 0; v < ranges.size(); v++) {
        if (ranges[v] > 0) {
            const auto& iVars = inputVars[v];
            const auto& iValues = inputValues[v];
            const auto& oValues = outputValues[v];
            std::vector<BDD> states(ranges[v] + 1, manager.bddZero());

            for (int i = 0; i < oValues.size(); i++) {
                states[oValues[i]] += representStateQN(manager, iVars, iValues[i], ranges);
            }
            BDD updates = manager.bddOne();
            for (int val = 0; val <= ranges[v]; val++) {
                BDD vPrime = representPrimedVarQN(manager, v, val, ranges);
                BDD u = logicalEquivalence(states[val], vPrime);
                updates *= u;
            }
            BDD otherVarsDoNotChange = otherVarsDoNotChangeQN(manager, v, ranges);
            BDD vChanges = varDoesChangeQN(manager, v, ranges);
            BDD transition = updates * otherVarsDoNotChange * (fixpoint + vChanges);
            bdd += transition;
        }
    }

    return bdd;
}

bool isAsyncLoop(const Cudd& manager, const BDD& S, const BDD& syncTransitionBdd, const std::vector<int>& ranges, int numUnprimedBDDVars) {
    BDD reached = manager.bddZero();
    BDD s = randomState(manager, S, numUnprimedBDDVars);

    while (s != manager.bddZero()) {
        BDD sP = immediateSuccessorStates(manager, syncTransitionBdd, s, numUnprimedBDDVars);
        char *sCube = new char[numUnprimedBDDVars * 2];
        s.PickOneCube(sCube);
        char *sPCube = new char[numUnprimedBDDVars * 2];
        sP.PickOneCube(sPCube);

        int nVarDiff = 0;
        int i = 0;
        for (int range : ranges) {
            int b = bits(range);
            for (int j = i; j < i + b; j++) {
                if (sCube[j] != sPCube[j]) {
                    nVarDiff++;
                    break;
                }
            }
            if (nVarDiff >= 2) return false;
            i += b;
        }
        s = sP * !reached;
        reached += s;
    }
    return true;
}

std::list<BDD> combinedAlgorithm(Cudd manager, const BDD& syncTransitionBdd, const BDD& asyncTransitionBdd, const std::vector<int>& ranges) {
    auto lambda = [](int a, int b) { return a + bits(b); };
    int numUnprimedBDDVars = std::accumulate(ranges.begin(), ranges.end(), 0, lambda);
    std::list<BDD> asyncAttractors;
    std::list<BDD> syncAttractors = attractorsQN(manager, syncTransitionBdd, ranges, manager.bddZero());
    BDD syncAsyncAttractors = manager.bddZero();
    for (const BDD& a : syncAttractors) {
        if (isAsyncLoop(manager, a, syncTransitionBdd, ranges, numUnprimedBDDVars)) {
            syncAsyncAttractors += a;
            asyncAttractors.push_back(a);
        }
    }
    BDD br = backwardReachableStates(manager, asyncTransitionBdd, syncAsyncAttractors, numUnprimedBDDVars);
    asyncAttractors.splice(asyncAttractors.end(), attractorsQN(manager, asyncTransitionBdd, ranges, syncAsyncAttractors + br));
    return asyncAttractors;
}

std::string printRange(const std::list<int>& values) {
    std::string s("[");
    s += std::to_string(values.front());
    std::for_each(std::next(values.begin()), values.end(), [&s](int b) { s += "; "; s += std::to_string(b); });
    s += "]";
    return s;
}

std::string fromBinary(const std::string& bits, int offset) {
    int i = 0;
    auto lambda = [&i](int a) { return a + std::pow(2.0f, i); };
    std::list<int> values{ offset };

    for (auto it = std::begin(bits); it < std::end(bits); ++it) {
        if (*it == '-') {
            std::list<int> copy(values);
            std::transform(copy.begin(), copy.end(), copy.begin(), lambda);
            values.splice(values.end(), copy);
        }
        else if (*it == '1') {
            std::transform(values.begin(), values.end(), values.begin(), lambda);
        }
        i++;
    }
    return values.size() > 1 ? printRange(values) : std::to_string(values.front());
}

std::string prettyPrint(const Cudd& manager, const BDD& attractor, const std::vector<int>& ranges, const std::vector<int>& offsets) {
    FILE *old = manager.ReadStdout();
    FILE *fp = fopen("temp.txt", "w");
    manager.SetStdout(fp);
    attractor.PrintMinterm();
    manager.SetStdout(old);
    fclose(fp);

    std::string out;
    std::ifstream infile("temp.txt");
    std::string line;
    auto lambda = [](std::string a, std::string b) { return a + ", " + b; };
    while (std::getline(infile, line)) {
        std::list<std::string> output;
        int i = 0;
        for (int v = 0; v < ranges.size(); v++) {
            if (ranges[v] == 0) {
                output.push_back(std::to_string(offsets[v]));
            }
            else {
                int b = bits(ranges[v]);
                output.push_back(fromBinary(line.substr(i, b), offsets[v]));
                i += b;
            }
        }

        out += std::accumulate(std::next(output.begin()), output.end(), output.front(), lambda) + "\n";
    }

    return out;
}

BDD findFixpoints(Cudd manager, const BDD& syncTransitionBdd, const std::vector<int>& ranges) {
    auto lambda = [](int a, int b) { return a + bits(b); };
    int numUnprimedBDDVars = std::accumulate(ranges.begin(), ranges.end(), 0, lambda);

    BDD fixpoint = manager.bddOne();
    for (int i = 0; i < numUnprimedBDDVars; i++) {
        BDD v = manager.bddVar(i);
        BDD vPrime = manager.bddVar(numUnprimedBDDVars + i);
        fixpoint *= logicalEquivalence(v, vPrime);
    }

    BDD bdd = renameRemovingPrimes(syncTransitionBdd * fixpoint, numUnprimedBDDVars);
    removeInvalidBitCombinations(manager, bdd, ranges);
    return bdd;
}

extern "C" __declspec(dllexport) int attractors(int numVars, int ranges[], int minValues[], int numInputs[], int inputVars[], int numUpdates[], int inputValues[], int outputValues[], const char *output, int outputLength, int mode) {
    std::string out(output, outputLength);
    std::vector<int> rangesV(ranges, ranges + numVars);
    std::vector<int> minValuesV(minValues, minValues + numVars);
    std::vector<std::vector<int>> inputVarsV;
    std::vector<std::vector<int>> outputValuesV;
    std::vector<std::vector<std::vector<int>>> inputValuesV;

    int k = 0;
    for (int i = 0; i < numVars; i++) {
        std::vector<int> in;
        for (int j = 0; j < numInputs[i]; j++) {
            in.push_back(inputVars[k]);
            k++;
        }
        inputVarsV.push_back(in);
    }

    k = 0;
    for (int i = 0; i < numVars; i++) {
        std::vector<int> out;
        for (int j = 0; j < numUpdates[i]; j++) {
            out.push_back(outputValues[k]);
            k++;
        }
        outputValuesV.push_back(out);
    }

    k = 0;
    for (int i = 0; i < numVars; i++) {
        std::vector<std::vector<int>> in;
        for (int j = 0; j < numUpdates[i]; j++) {
            std::vector<int> v;
            for (int l = 0; l < numInputs[i]; l++) {
                v.push_back(inputValues[k]);
                k++;
            }
            in.push_back(v);
        }
        inputValuesV.push_back(in);
    }

    Cudd manager(0, 0);
    manager.AutodynEnable(CUDD_REORDER_GROUP_SIFT); // seems to beat CUDD_REORDER_SIFT

    if (mode == 0) {
        std::cout << "Building synchronous transition relation..." << std::endl;
        BDD transitionBdd = representSyncQNTransitionRelation(manager, rangesV, inputVarsV, inputValuesV, outputValuesV);

        if (transitionBdd == manager.bddZero()) {
            std::cout << "TransitionBDD is zero!" << std::endl;
        }

        std::cout << "Finding attractors..." << std::endl;

        std::list<BDD> atts = attractorsQN(manager, transitionBdd, rangesV, manager.bddZero());
        int i = 0;
        for (const BDD& attractor : atts) {
            std::ofstream file(out + "Attractor" + std::to_string(i) + ".csv");
            file << prettyPrint(manager, attractor, rangesV, minValuesV) << std::endl;
            i++;
        }
        return i;
    }
    else {
        std::cout << "Building synchronous transition relation..." << std::endl;
        BDD syncTransitionBdd = representSyncQNTransitionRelation(manager, rangesV, inputVarsV, inputValuesV, outputValuesV);

        std::cout << "Building asynchronous transition relation..." << std::endl;
        BDD asyncTransitionBdd = representAsyncQNTransitionRelation(manager, rangesV, inputVarsV, inputValuesV, outputValuesV);

        std::cout << "Finding attractors with combined algorithm..." << std::endl;
        std::list<BDD> atts = combinedAlgorithm(manager, syncTransitionBdd, asyncTransitionBdd, rangesV);
        int i = 0;

        std::cout << "Pretty printing..." << std::endl;

        for (const BDD& attractor : atts) {
            std::ofstream file(out + "Attractor" + std::to_string(i) + ".csv");
            file << prettyPrint(manager, attractor, rangesV, minValuesV) << std::endl;
            i++;
        }
        return i;
    }
}
