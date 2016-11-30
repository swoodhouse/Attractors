#include "stdafx.h"

BDD representState(Cudd manager, std::vector<bool> values) {
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

BDD representCnf(Cudd manager, std::vector<int> cnf) {
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

BDD representUpdateFunction(Cudd manager, std::vector<std::vector<int>> cnfs) {
	BDD bdd = manager.bddOne();
	for (auto it = std::begin(cnfs); it != std::end(cnfs); ++it) {
		bdd = bdd * representCnf(manager, *it);
	}
	return bdd;
}

BDD logicalEquivalence(BDD a, BDD b) {
	return (a * b) + ((!a) * (!b));
}

BDD representSyncTransitionRelation(Cudd manager, std::vector<std::vector<std::vector<int>>> network) {
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

BDD otherVarsDoNotChange(Cudd manager, int i, int numVars) {
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

BDD representAsyncTransitionRelation(Cudd manager, std::vector<std::vector<std::vector<int>>> network) {
	BDD fixpoint = manager.bddOne();
	for (int i = 0; i < network.size(); i++) {
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

BDD renameRemovingPrimes(BDD bdd, int numVars) {
	int *permute = new int[numVars * 2];
	for (int i = 0; i < numVars; i++) {
		permute[i] = i;
		permute[i + numVars] = i;
	}
	BDD r = bdd.Permute(permute);
	delete[] permute;
	return r;
}

BDD nonPrimeVariables(Cudd manager, int numVars) {
	return representState(manager, std::vector<bool>(numVars, true));
}

BDD primeVariables(Cudd manager, int numVars) {
	BDD bdd = manager.bddOne();
	for (int i = numVars; i < numVars * 2; i++) {
		BDD var = manager.bddVar(i);
		bdd = var * bdd;
	}
	return bdd;
}

BDD immediateSuccessorStates(Cudd manager, BDD transitionBdd, BDD valuesBdd, int numVars) {
	BDD bdd = transitionBdd * valuesBdd;
	bdd = bdd.ExistAbstract(nonPrimeVariables(manager, numVars));
	bdd = renameRemovingPrimes(bdd, numVars);
	return bdd;
}

BDD forwardReachableStates(Cudd manager, BDD transitionBdd, BDD valuesBdd, int numVars) {
	BDD reachable = manager.bddZero();
	BDD frontier = valuesBdd;

	while (frontier != manager.bddZero()) {
		frontier = immediateSuccessorStates(manager, transitionBdd, frontier, numVars) * !reachable;
		reachable = reachable + frontier;
	}
	return reachable;
}

BDD renameAddingPrimes(BDD bdd, int numVars) {
	int *permute = new int[numVars * 2];
	for (int i = 0; i < numVars; i++) {
		permute[i] = i + numVars;
		permute[i + numVars] = i + numVars;
	}

	BDD r = bdd.Permute(permute);
	delete[] permute;
	return r;
}

BDD immediatePredecessorStates(Cudd manager, BDD transitionBdd, BDD valuesBdd, int numVars) {
	valuesBdd = renameAddingPrimes(valuesBdd, numVars);
	BDD bdd = transitionBdd * valuesBdd;
	bdd = bdd.ExistAbstract(primeVariables(manager, numVars));
	return bdd;
}

BDD backwardReachableStates(Cudd manager, BDD transitionBdd, BDD valuesBdd, int numVars) {
	BDD reachable = manager.bddZero();
	BDD frontier = valuesBdd;

	while (frontier != manager.bddZero()) {
		frontier = immediatePredecessorStates(manager, transitionBdd, frontier, numVars) * !reachable;
		reachable = reachable + frontier;
	}
	return reachable;
}

BDD randomState(Cudd manager, BDD S, int numVars) {
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

std::vector<BDD> attractors(Cudd manager, BDD transitionBdd, int numVars) {
	std::vector<BDD> attractors = std::vector<BDD>();
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
	std::vector<bool> cmpInitial = { true, true, true, false, false, false, false, false, false, false, false };
	std::vector<std::vector<int>> cebpa = { { 0 },{ -7 },{ -3, -4 } };
	std::vector<std::vector<int>> pu1 = { { 0, 1 },{ -2 },{ -3 } };
	std::vector<std::vector<int>> gata2 = { { 3 },{ -1 },{ -3, -4 } };
	std::vector<std::vector<int>> gata1 = { { 2, 3, 6 },{ -1 } };
	std::vector<std::vector<int>> fog1 = { { 3 } };
	std::vector<std::vector<int>> eklf = { { 3 },{ -6 } };
	std::vector<std::vector<int>> fli1 = { { 3 },{ -5 } };
	std::vector<std::vector<int>> scl = { { 3 },{ -1 } };
	std::vector<std::vector<int>> cJun = { { 1 },{ -10 } };
	std::vector<std::vector<int>> egrNab = { { 1 },{ 8 },{ -10 } };
	std::vector<std::vector<int>> gfi1 = { { 0 },{ -9 } };
	std::vector<std::vector<std::vector<int>>> cmp = { cebpa, pu1, gata2, gata1, fog1, eklf, fli1, scl, cJun, egrNab, gfi1 };

	Cudd manager(0, 0);
	BDD initialStateBdd = representState(manager, cmpInitial);

	BDD transitionBddA = representAsyncTransitionRelation(manager, cmp);
	BDD statespace = forwardReachableStates(manager, transitionBddA, initialStateBdd, cmpInitial.size());
	std::cout << statespace.CountMinterm(cmpInitial.size());
	std::cout << "\n";

	std::vector<BDD> attsA = attractors(manager, transitionBddA, cmpInitial.size());
	for (BDD attractor : attsA) {
		attractor.PrintMinterm();
		std::cout << "\n";
	}

	std::cout << "--------------------------------\n";

	BDD transitionBddS = representSyncTransitionRelation(manager, cmp);
	std::vector<BDD> attsS = attractors(manager, transitionBddS, cmpInitial.size());
	for (BDD attractor : attsS) {
		attractor.PrintMinterm();
		std::cout << "\n";
	}

	return 0;
}
