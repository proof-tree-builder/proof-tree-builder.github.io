// hint which rules are applicable (sequent calculus)

function LKapplicable(sequent) {
	arr = []
	
	lhs = sequent.precedents
	rhs = sequent.antecedents
	
	// left rules: falsity, or, and, implies, not
	for (i = 0; i < lhs.length; i++) {
		// get formula
		f = lhs[i]
		// add rule to list
		if (f instanceof Falsity) {
			arr.push(FalsityLeft)
		} else if (f instanceof Or) {
			arr.push(OrLeft)
		} else if (f instanceof And) {
			arr.push(AndLeft)
		} else if (f instanceof Implies) {
			arr.push(ImpliesLeft)
		} else if (f instanceof Not) {
			arr.push(NotLeft)
		}
	}
	
	// right rules: truth, or, and, implies, not
	for (i = 0; i < rhs.length; i++) {
		// get formula
		f = rhs[i]
		// add rule to list
		if (f instanceof Truth) {
			arr.push(TruthRight)
		} else if (f instanceof Or) {
			arr.push(OrRight)
		} else if (f instanceof And) {
			arr.push(AndRight)
		} else if (f instanceof Implies) {
			arr.push(ImpliesRight)
		} else if (f instanceof Not) {
			arr.push(NotRight)
		}
	}
	
	// other: identity
	for (i = 0; i < rhs.length; i++) {
		formula = rhs[i]
		found = false
		// if we find match, stop looking
		for (j = 0; j < lhs.length; j++) {
			if (deepEqual(formula, lhs[j])) {
				found = true;
				break;
			}
		}
		// if match found, can apply identity
		if (found) {
			arr.push(Identity)
		}
	}
	
	return arr
}



