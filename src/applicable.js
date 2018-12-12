/*so what we need is a function that takes a sequent, and a rule name 
(remember that rules are classes, so if the argument is named rule you can do 
rule === Identity to check if that is the identity rule.

the function then
1) either returns the proof tree. this means it has to figure out the proper 
indices for the locations of the formulas in the sequents. 
let me know if you need help with understanding what the index arguments mean in each rule

2) or throws an error about how the indices are ambiguous, with the indices of possible options.
 we will then present these options to the user, but not in this function

3) throws an error that says the rule is completely inapplicable */

function applicable(sequent, rule) {
	lhs = sequent.precedents;
	rhs = sequent.antecedents;
	
	// what kind of formula are we looking for
	formula = Formula;
	if (rule === NotLeft || rule === NotRight) {
		formula = Not;
	} else if (rule === OrLeft || rule === OrRight) {
		formula = Or;
	} else if (rule === AndLeft || rule === AndRight) {
		formula = And;
	} else if (rule === ImpliesLeft || rule === ImpliesRight) {
		formula = Implies;
	} else if (rule === TruthRight) {
		formula = Truth;
	} else if (rule === FalsityLeft) {
		formula = Falsity;
	}
	
	
	// if dealing with Left rules
	// or, and, implies, not, falsity
	if (rule.name.includes("Left")) {
		
		// get all applicable indices
		indices = []
		for (i = 0; i < lhs.length; i++) {
			if (lhs[i] instanceof formula)
				indices.push(i);
		}
		
		// if none, then can't apply rule
		if (indices.length == 0) {
			throw new Error("Rule not applicable.");
		}
		
		// if more than one, ambiguous
		if (indices.length > 1) {
			throw new Error("Rule application ambiguous.");
		}
		
		// this is the index
		idx = indices[0];
		
		// CASE: FALSITY LEFT
		if (rule === FalsityLeft) {
			
			return new FalsityLeft(sequent, idx);
			
			// CASE: NOT 	
		} else if (rule === NotLeft) {
			// original NOT formula
			og = lhs[idx];
			// formula that's negated (new object)
			inner = og.subformulas[0];
			// make shallow copies
			plhs = lhs.slice()
			prhs = rhs.slice()
			// remove NOT from lhs
			plhs.splice(idx, 1);
			// add formula to rhs
			prhs.unshift(inner);
			premise = new Sequent(plhs, prhs)
			incomplete = new LKIncomplete(premise);
			tree = new NotLeft(incomplete, sequent, 0, idx);
			return tree;
		}

		
	}
	
	
	





	
	
	// if dealing with Right rules
	// or, and, implies, not, truth
	if (rule.name.includes("Right")) {
		
		// get all applicable indices
		indices = []
		for (i = 0; i < lhs.length; i++) {
			if (lhs[i] instanceof formula)
				indices.push(i);
		}
		
		// if none, then can't apply rule
		if (indices.length == 0) {
			throw new Error("Rule not applicable.");
		}
		
		// if more than one, ambiguous
		if (indices.length > 1) {
			throw new Error("Rule application ambiguous.")
		}
		
		// this is the index
		idx = indices[0]
	}
	
	
	
	
	
	
	
	
	
	
	// if dealing with both sides
	// identity

	throw new Error("no other rules");
}




pq = new And(new Var("p"), new Var("q"))
sk = new And(new Var("s"), new Var("k"))
p = new Var("p")
notp = new Not(p)

seq = new Sequent([pq, notp], [sk])