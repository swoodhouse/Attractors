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

int main() {
    //Cebpa, Pu.1, Gata2, Gata1, Fog1, EKLF, Fli1, Scl, cJun, EgrNab, Gfi1
    std::vector<bool> cmpInitial{ true, true, true, false, false, false, false, false, false, false, false };
    std::vector<std::vector<int>> cebpa{ { 0 },{ -7 },{ -3, -4 } };
    std::vector<std::vector<int>> pu1{ { 0, 1 },{ -2 },{ -3 } };
    std::vector<std::vector<int>> gata2{ { 3 },{ -1 },{ -3, -4 } };
    std::vector<std::vector<int>> gata1{ { 2, 3, 6 },{ -1 } };
    std::vector<std::vector<int>> fog1{ { 3 } };
    std::vector<std::vector<int>> eklf{ { 3 },{ -6 } };
    std::vector<std::vector<int>> fli1{ { 3 },{ -5 } };
    std::vector<std::vector<int>> scl{ { 3 },{ -1 } };
    std::vector<std::vector<int>> cJun{ { 1 },{ -10 } };
    std::vector<std::vector<int>> egrNab{ { 1 },{ 8 },{ -10 } };
    std::vector<std::vector<int>> gfi1{ { 0 },{ -9 } };
    std::vector<std::vector<std::vector<int>>> cmp{ cebpa, pu1, gata2, gata1, fog1, eklf, fli1, scl, cJun, egrNab, gfi1 };

    Cudd manager(0, 0);
    BDD initialStateBdd = representState(manager, cmpInitial);

    BDD transitionBddA = representAsyncTransitionRelation(manager, cmp);
    BDD statespace = forwardReachableStates(manager, transitionBddA, initialStateBdd, cmpInitial.size());
    std::cout << statespace.CountMinterm(cmpInitial.size());
    std::cout << "\n";

    std::list<BDD> attsA = attractorsBN(manager, transitionBddA, cmpInitial.size());
    for (BDD attractor : attsA) {
        attractor.PrintMinterm();
        std::cout << "\n";
    }

    std::cout << "--------------------------------\n";

    BDD transitionBddS = representSyncTransitionRelation(manager, cmp);
    std::list<BDD> attsS = attractorsBN(manager, transitionBddS, cmpInitial.size());
    for (BDD attractor : attsS) {
        attractor.PrintMinterm();
        std::cout << "\n";
    }

    return 0;
}
