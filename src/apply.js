
function apply(sequent, rule) {
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
			inner = og.one;
			// make shallow copies
			plhs = lhs.slice()
			prhs = rhs.slice()
			// remove NOT from lhs
			plhs.splice(idx, 1);
			// add formula to rhs
			prhs.unshift(inner);
			premise = new LKIncomplete(new Sequent(plhs, prhs));
			tree = new NotLeft(premise, sequent, 0, idx);
			return tree;
		
		// CASE: OR
		} else if (rule === OrLeft) {
			// original OR formula
			og = lhs[idx];
			// subformulas
			left = og.left
			right = og.right
			
			// make premise1
			plhs = lhs.slice()
			delete plhs[idx];
			plhs[idx] = left;
			premise1 = new LKIncomplete(new Sequent(plhs, rhs.slice()))
			
			// make premise2
			plhs = lhs.slice()
			delete plhs[idx];
		    plhs[idx] = right;
			premise2 = new LKIncomplete(new Sequent(plhs, rhs.slice()))
			
			tree = new OrLeft(premise1, premise2, sequent, idx, idx, idx);
			return tree;
		
		// CASE: AND	
		} else if (rule === AndLeft) {
			// original AND formula
			og = lhs[idx];
			// subformulas
			left = og.left
			right = og.right
			
			// make premise
			plhs = lhs.slice()
			delete plhs[idx];
			plhs[idx] = right;
			plhs.unshift(left);
			premise = new LKIncomplete(new Sequent(plhs, rhs.slice()))
			
			tree = new AndLeft(premise, sequent, idx, idx + 1, idx);
			return tree;
			
		} else if (rule === ImpliesLeft) {
			// original OR formula
			og = lhs[idx];
			// subformulas
			left = og.left
			right = og.right
			
			// make premise1
			plhs = lhs.slice()
			plhs.splice(idx, 1)
			prhs = rhs.slice()
			prhs.unshift(left)
			premise1 = new LKIncomplete(new Sequent(plhs, prhs))
			
			// make premise2
			plhs = lhs.slice()
			delete plhs[idx];
		    plhs[idx] = right;
			premise2 = new LKIncomplete(new Sequent(plhs, rhs.slice()))
			
			tree = new ImpliesLeft(premise1, premise2, sequent, 0, idx, idx);
			return tree;
			
		}

	}
	
	
	





	
	
	// if dealing with Right rules
	// or, and, implies, not, truth
	if (rule.name.includes("Right")) {
		// get all applicable indices
		indices = []
		for (i = 0; i < rhs.length; i++) {
			if (rhs[i] instanceof formula)
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
		
		// CASE: TRUTH
		if (rule === TruthRight) {
			return new TruthRight(sequent, idx);
			
		// CASE: NOT 	
		} else if (rule === NotRight) {
			// original NOT formula
			og = rhs[idx];
			inner = og.one;
			// make shallow copies
			plhs = lhs.slice()
			prhs = rhs.slice()
			// remove NOT from lhs
			prhs.splice(idx, 1);
			// add formula to rhs
			plhs.push(inner);
			premise = new LKIncomplete(new Sequent(plhs, prhs));
			tree = new NotRight(premise, sequent, plhs.length - 1, idx);
			return tree;
		
		// CASE: OR
		} else if (rule === OrRight) {
			// original OR formula
			og = rhs[idx];
			// subformulas
			left = og.left
			right = og.right
			
			// make premise
			prhs = rhs.slice()
			delete prhs[idx];
			prhs[idx] = left;
			prhs.push(right)
			premise = new LKIncomplete(new Sequent(lhs.slice(), prhs))
			
			tree = new OrRight(premise, sequent, idx, idx + 1, idx);
			return tree;
		
		// CASE: AND	
		} else if (rule === AndRight) {
			// original AND formula
			og = rhs[idx];
			// subformulas
			left = og.left
			right = og.right
			
			// make premise1
			prhs = rhs.slice()
			delete prhs[idx];
			prhs[idx] = left;
			premise1 = new LKIncomplete(new Sequent(lhs.slice(), prhs))
			
			// make premise2
			prhs = rhs.slice()
			delete prhs[idx];
			prhs[idx] = right;
			premise2 = new LKIncomplete(new Sequent(lhs.slice(), prhs))
			
			tree = new AndRight(premise1, premise2, sequent, idx, idx, idx);
			return tree;
			
		} else if (rule === ImpliesRight) {
			// original OR formula
			og = rhs[idx];
			// subformulas
			left = og.left
			right = og.right
			
			// make premise1
			plhs = lhs.slice()
			plhs.push(left)
			prhs = rhs.slice()
			delete prhs[idx];
		    prhs[idx] = right;
			premise = new LKIncomplete(new Sequent(plhs, prhs))
			
			tree = new ImpliesRight(premise, sequent, plhs.length - 1, idx, idx);
			return tree;
			
		}
		
	}
	
	
	// if dealing with both sides
	// identity
	
	if (rule === Identity) {
		
	}

	throw new Error("no such rule so far");
}




pq = new And(new Var("p"), new Var("q"))
sk = new Implies(new Var("s"), new Var("k"))
p = new Var("p")
notp = new Not(p)

seq = new Sequent([pq], [notp, sk])