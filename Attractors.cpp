// TODO: add defensive size checks, refactor, optimise

#include "stdafx.h"

BDD representState(const Cudd& manager, const std::vector<bool>& values) {
    BDD bdd = manager.bddOne();
    int i = 0;
    for (auto it = std::begin(values); it != std::end(values); ++it) {
        BDD var = manager.bddVar(i);
        if (!*it) {
            var = !var;
        }
        bdd = var * bdd;
        i++;
    }
    return bdd;
}

BDD representCnf(const Cudd& manager, const std::vector<int>& cnf) {
    BDD bdd = manager.bddZero();
    for (auto it = std::begin(cnf); it != std::end(cnf); ++it) {
        BDD var = manager.bddVar(abs(*it));
        if (*it < 0) {
            var = !var;
        }
        bdd = var + bdd;
    }
    return bdd;
}

BDD representUpdateFunction(const Cudd& manager, const std::vector<std::vector<int>>& cnfs) {
    BDD bdd = manager.bddOne();
    for (auto it = std::begin(cnfs); it != std::end(cnfs); ++it) {
        bdd = bdd * representCnf(manager, *it);
    }
    return bdd;
}

BDD implication(const BDD& a, const BDD& b) {
    return !a + b;
}

BDD logicalEquivalence(const BDD& a, const BDD& b) {
    return implication(a, b) * implication(b, a);
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

BDD nonPrimeVariables(const Cudd& manager, int numUnprimedBDDVars) {
    return representState(manager, std::vector<bool>(numUnprimedBDDVars, true));
}

BDD primeVariables(const Cudd& manager, int numUnprimedBDDVars) {
    BDD bdd = manager.bddOne();
    for (int i = numUnprimedBDDVars; i < numUnprimedBDDVars * 2; i++) {
        BDD var = manager.bddVar(i);
        bdd = var * bdd;
    }
    return bdd;
}

BDD immediateSuccessorStates(const Cudd& manager, const BDD& transitionBdd, const BDD& valuesBdd, int numUnprimedBDDVars) {
    BDD bdd = transitionBdd * valuesBdd;
    bdd = bdd.ExistAbstract(nonPrimeVariables(manager, numUnprimedBDDVars));
    bdd = renameRemovingPrimes(bdd, numUnprimedBDDVars);

    return bdd;
}

BDD forwardReachableStates(const Cudd& manager, const BDD& transitionBdd, const BDD& valuesBdd, int numUnprimedBDDVars) {
    BDD reachable = manager.bddZero();
    BDD frontier = valuesBdd;

    while (frontier != manager.bddZero()) {
        frontier = immediateSuccessorStates(manager, transitionBdd, frontier, numUnprimedBDDVars) * !reachable;
        reachable = reachable + frontier;
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
    bdd = transitionBdd * bdd;
    bdd = bdd.ExistAbstract(primeVariables(manager, numUnprimedBDDVars));
    return bdd;
}

BDD backwardReachableStates(const Cudd& manager, const BDD& transitionBdd, const BDD& valuesBdd, int numUnprimedBDDVars) {
    BDD reachable = manager.bddZero();
    BDD frontier = valuesBdd;

    while (frontier != manager.bddZero()) {
        frontier = immediatePredecessorStates(manager, transitionBdd, frontier, numUnprimedBDDVars) * !reachable;
        reachable = reachable + frontier;
    }
    return reachable;
}

BDD randomState(const Cudd& manager, const BDD& S, int numUnprimedBDDVars) {
    std::vector<BDD> vars;
    for (int i = 0; i < numUnprimedBDDVars; i++) {
        vars.push_back(manager.bddVar(i));
    }

    return S.PickOneMinterm(vars);
}

std::list<BDD> attractorsBN(const Cudd&  manager, const BDD& transitionBdd, int numVars) {
    std::list<BDD> attractors;
    BDD S = manager.bddOne();
    while (S != manager.bddZero()) {
        BDD s = randomState(manager, S, numVars);
        BDD fr = forwardReachableStates(manager, transitionBdd, s, numVars);
        BDD br = backwardReachableStates(manager, transitionBdd, s, numVars);

        if ((fr * !br) == manager.bddZero()) {
            attractors.push_back(fr);
        }

        S = S * !(s + br);
    }
    return attractors;
}

BDD representUnprimedVarQN(const Cudd& manager, int var, int val, const std::vector<int>& ranges) {
    BDD bdd = manager.bddOne();
    int i = std::accumulate(ranges.begin(), ranges.begin() + var, 0);
    int max = ranges[var];

    for (int j = 0; j < max; j++) {
        BDD var = manager.bddVar(i);
        if (val <= j) {
            var = !var;
        }
        bdd = bdd * var;
        i++;
    }

    return bdd;
}

BDD representStateQN(const Cudd& manager, const std::vector<int>& vars, const std::vector<int>& values, const std::vector<int>& ranges) {
    BDD bdd = manager.bddOne();
    for (size_t i = 0; i < vars.size(); i++) {
        int var = vars[i];
        int val = values[i];
        bdd = bdd * representUnprimedVarQN(manager, var, val, ranges);
    }
    return bdd;
}

BDD representPrimedVarQN(const Cudd& manager, int var, int val, const std::vector<int>& ranges) {
    BDD bdd = manager.bddOne();
    int i = std::accumulate(ranges.begin(), ranges.end(), 0) + std::accumulate(ranges.begin(), ranges.begin() + var, 0);
    int max = ranges[var];

    for (int j = 0; j < max; j++) {
        BDD var = manager.bddVar(i);
        if (val <= j) {
            var = !var;
        }
        bdd = bdd * var;
        i++;
    }
    return bdd;
}

BDD removeInvalidBitCombinations(const Cudd& manager, const BDD& S, const std::vector<int>& ranges) {
    BDD bdd = S;
    int i = 0;
    for (int max : ranges) {
        for (int j = 1; j < max; j++) {
            BDD a = manager.bddVar(i);
            BDD b = manager.bddVar(i + 1);
            bdd = bdd * implication(b, a);
            i++;
        }
        i++;
    }
    return bdd;
}

BDD representSyncQNTransitionRelation(const Cudd& manager, const std::vector<int>& ranges, const std::vector<std::vector<int>>& inputVars,
    const std::vector<std::vector<std::vector<int>>>& inputValues, const std::vector<std::vector<int>>& outputValues) {
    BDD bdd = manager.bddOne();
    int v = 0;
    auto itVars = std::begin(inputVars);
    auto itIn = std::begin(inputValues);
    auto itOut = std::begin(outputValues);
    while (itOut != std::end(outputValues)) {
        auto itVals = std::begin(*itIn);
        auto itO = std::begin(*itOut);
        while (itO != std::end(*itOut)) {
            BDD state = representStateQN(manager, *itVars, *itVals, ranges);
            BDD vPrime = representPrimedVarQN(manager, v, *itO, ranges);
            bdd = bdd * implication(state, vPrime);;
            ++itVals;
            ++itO;
        }
        v++;
        ++itVars;
        ++itIn;
        ++itOut;
    }
    return bdd;
}

std::list<BDD> attractorsQN(const Cudd& manager, const BDD& transitionBdd, const std::vector<int>& ranges) {
    int numUnprimedBDDVars = std::accumulate(ranges.begin(), ranges.end(), 0);
    std::list<BDD> attractors;
    BDD S = manager.bddOne();
    S = removeInvalidBitCombinations(manager, S, ranges);

    while (S != manager.bddZero()) {
        BDD s = randomState(manager, S, numUnprimedBDDVars);
        BDD fr = forwardReachableStates(manager, transitionBdd, s, numUnprimedBDDVars);
        BDD br = backwardReachableStates(manager, transitionBdd, s, numUnprimedBDDVars);

        if ((fr * !br) == manager.bddZero()) {
            attractors.push_back(fr);
        }

        S = S * !(s + br);
    }
    return attractors;
}
