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

BDD randomState(const Cudd& manager, BDD S, int numVars) {
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

	int b = bits(ranges[var]); //1.. be careful with zero max/=  just add an if?
	for (int n = 0; n < b; n++) {
		BDD var = manager.bddVar(i);
		if (!nthBitSet(val, n)) {
			var = !var;
		}
		bdd = bdd * var;
		i++;
	}

	return bdd;
}

BDD representPrimedVarQN(const Cudd& manager, int var, int val, const std::vector<int>& ranges) {
	BDD bdd = manager.bddOne();
	auto lambda = [](int a, int b) { return a + bits(b); };
	int i = std::accumulate(ranges.begin(), ranges.end(), 0, lambda) + std::accumulate(ranges.begin(), ranges.begin() + var, 0, lambda);

	int b = bits(ranges[var]); //1.. be careful with zero max/=  just add an if?
	for (int n = 0; n < b; n++) {
		BDD var = manager.bddVar(i);
		if (!nthBitSet(val, n)) {
			var = !var;
		}
		bdd = bdd * var;
		i++;
	}

	return bdd;
}

BDD representStateQN(const Cudd& manager, const std::vector<int>& vars, const std::vector<int>& values, const std::vector<int>& ranges) {
	BDD bdd = manager.bddOne();
	for (/*std::vector<int>::size_type*/ size_t i = 0; i < vars.size(); i++) {
		int var = vars[i];
		int val = values[i];
		bdd = bdd * representUnprimedVarQN(manager, var, val, ranges); // inefficent, because we do the find beginning loop many times
	}
	return bdd;
}

BDD removeInvalidBitCombinations(const Cudd& manager, const BDD& S, const std::vector<int>& ranges) {
	BDD bdd = S;
	for (int var = 0; var < ranges.size(); var++) {
		if (ranges[var] > 0) {
			int b = bits(ranges[var]);
			int theoreticalMax = (1 << b) - 1; //this...

			for (int val = ranges[var] + 1; val <= theoreticalMax; val++) { //this... // <= or <?
				bdd = bdd * !representUnprimedVarQN(manager, var, val, ranges); // only have to do unprimed, right?
			}
		}
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
			BDD i = implication(state, vPrime);
			bdd = bdd * i;
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

std::list<BDD> attractorsQN(Cudd manager, const BDD& transitionBdd, const std::vector<int>& ranges) {
	auto lambda = [](int a, int b) { return a + bits(b); };
	int numUnprimedBDDVars = std::accumulate(ranges.begin(), ranges.end(), 0, lambda);
	std::list<BDD> attractors;
	BDD S = manager.bddOne();
	S = removeInvalidBitCombinations(manager, S, ranges);

	manager.ReduceHeap(CUDD_REORDER_SIFT, 0); // maybe?

	while (S != manager.bddZero()) {
		BDD s = randomState(manager, S, numUnprimedBDDVars); //here... pick a state.run it.pick a state.run it.stop after n steps, or something.

		for (int i = 0; i < 20; i++) {
			BDD sP = forwardReachableStates(manager, transitionBdd, s, numUnprimedBDDVars);
			s = randomState(manager, sP, numUnprimedBDDVars); //here... pick a state.run it.pick a state.run it.stop after n steps, or something.
		}

		BDD fr = forwardReachableStates(manager, transitionBdd, s, numUnprimedBDDVars); // pass vars here too instead of num
		//std::cout << "3" << std::endl;
		BDD br = backwardReachableStates(manager, transitionBdd, s, numUnprimedBDDVars);

		if ((fr * !br) == manager.bddZero()) { // check if its backward set contains its forward set
			std::cout << "Attractor found" << std::endl;
			attractors.push_back(fr);
		}

		S = S * !(s + br);
	}
	return attractors;
}

BDD varDoesChangeQN(const Cudd& manager, int var, const std::vector<int>& ranges) {
	auto lambda = [](int a, int b) { return a + bits(b); };
	int start = std::accumulate(ranges.begin(), ranges.begin() + var, 0, lambda);
	int numUnprimedBDDVars = std::accumulate(ranges.begin(), ranges.end(), 0, lambda);
	int numBits = bits(ranges[var]);

	BDD bdd = manager.bddZero();
	for (int i = start; i < start + numBits; i++) { // right??
		BDD v = manager.bddVar(i);
		BDD vPrime = manager.bddVar(i + numUnprimedBDDVars);
		bdd = bdd + !logicalEquivalence(v, vPrime);
	}
	return bdd;
}

BDD otherVarsDoNotChangeQN(const Cudd& manager, int var, const std::vector<int>& ranges) {
	BDD bdd = manager.bddOne();
	for (int i = 0; i < ranges.size(); i++) {
		if (i != var) {
			bdd = bdd * !varDoesChangeQN(manager, i, ranges);
		}
	}

	return bdd;
}

BDD representAsyncQNTransitionRelation(/*const*/ Cudd& manager, const std::vector<int>& ranges, const std::vector<std::vector<int>>& inputVars,
	const std::vector<std::vector<std::vector<int>>>& inputValues, const std::vector<std::vector<int>>& outputValues) {
	auto lambda = [](int a, int b) { return a + bits(b); };
	int numUnprimedBDDVars = std::accumulate(ranges.begin(), ranges.end(), 0, lambda);

	BDD fixpoint = manager.bddOne();
	for (int i = 0; i < numUnprimedBDDVars; i++) {
		BDD v = manager.bddVar(i);
		BDD vPrime = manager.bddVar(numUnprimedBDDVars + i);
		fixpoint = fixpoint * logicalEquivalence(v, vPrime);

		manager.ReduceHeap(CUDD_REORDER_SIFT, 0); // maybe? // here??
	}

	BDD bdd = manager.bddZero();
	int v = 0;

	for (int v = 0; v < ranges.size(); v++) {
		if (ranges[v] > 0) { // ??????
			auto iVars = inputVars[v];
			auto iValues = inputValues[v];
			auto oValues = outputValues[v];

			std::vector<BDD> states(ranges[v] + 1, manager.bddZero());

			for (int i = 0; i < oValues.size(); i++) {
				states[oValues[i]] = states[oValues[i]] + representStateQN(manager, iVars, iValues[i], ranges);
				manager.ReduceHeap(CUDD_REORDER_SIFT, 0); // maybe? // here?
			}
			BDD updates = manager.bddOne();
			for (int val = 0; val <= ranges[v]; val++) {
				BDD vPrime = representPrimedVarQN(manager, v, val, ranges);
				BDD u = logicalEquivalence(states[val], vPrime);
				updates = updates * u;
				manager.ReduceHeap(CUDD_REORDER_SIFT, 0); // maybe? // here?
			}
			BDD otherVarsDoNotChange = otherVarsDoNotChangeQN(manager, v, ranges);
			BDD vChanges = varDoesChangeQN(manager, v, ranges);
			BDD transition = updates * otherVarsDoNotChange * (fixpoint + vChanges);
			bdd = bdd + transition;
		}
	}

	return bdd;
}