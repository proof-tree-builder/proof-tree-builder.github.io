const isString = (s) => typeof s === "string" || s instanceof String

const deepEqual = (x, y) => {
  const ok = Object.keys,
        tx = typeof x,
        ty = typeof y;
  return x && y && tx === 'object' && tx === ty && x.constructor === y.constructor ? (
    ok(x).length === ok(y).length &&
      ok(x).every(key => deepEqual(x[key], y[key]))
  ) : (x === y);
}

const arrayOf = (arr, cl) => arr instanceof Array && arr.every(a => a instanceof cl)

// Formula abstract class and kinds of formulas

class Formula {
  constructor() {
    if (new.target === Formula) {
      throw new TypeError("Cannot construct Formula instances directly");
    }
  }
}

class Truth extends Formula { constructor() { super(); } }

class Falsity extends Formula { constructor() { super(); } }

class Var extends Formula {
  constructor(v) {
		super();
	  if (isString(v)) {
			this.v = v;
    } else {
      throw new TypeError("Var has to contain a String");
    }
  }
}

class And extends Formula {
  constructor(left, right) {
		super();
	  if (left instanceof Formula && right instanceof Formula) {
			this.left = left;
			this.right = right;
    } else {
      throw new TypeError("And has to contain Formulas");
    }
  }
}

class Or extends Formula {
  constructor(left, right) {
		super();
	  if (left instanceof Formula && right instanceof Formula) {
			this.left = left;
			this.right = right;
    } else {
      throw new TypeError("Or has to contain Formulas");
    }
  }
}

class Implies extends Formula {
  constructor(left, right) {
		super();
	  if (left instanceof Formula && right instanceof Formula) {
			this.left = left;
			this.right = right;
    } else {
      throw new TypeError("Implies has to contain Formulas");
    }
  }
}

class Not extends Formula {
  constructor(one) {
		super();
	  if (one instanceof Formula) {
			this.one = one;
    } else {
      throw new TypeError("Not has to contain a Formula");
    }
  }
}

class Forall extends Formula {
  constructor(v, one) {
		super();
	  if (isString(v) && one instanceof Formula) {
			this.v = v;
			this.one = one;
    } else {
      throw new TypeError("Forall has to contain a String and a Formula");
    }
  }
}

class Exists extends Formula {
  constructor(v, one) {
		super();
	  if (isString(v) && one instanceof Formula) {
			this.v = v;
			this.one = one;
    } else {
      throw new TypeError("Exists has to contain a String and a Formula");
    }
  }
}

class Sequent {
  constructor(precedents, antecedents) {
	  if (arrayOf(precedents, Formula) && arrayOf(antecedents, Formula)) {
			this.precedents = precedents;
			this.antecedents = antecedents;
    } else {
      throw new TypeError("Sequent has to contain Formulas");
    }
  }
}

// Judgment abstract class and kinds of judgments

class Judgment {
  constructor() {
    if (new.target === Judgment) {
      throw new TypeError("Cannot construct Judgment instances directly");
    }
  }
}

class LKJudgment extends Judgment {
  constructor(premises, conclusion) {
		super();
	  if (arrayOf(premises, LKJudgment) && conclusion instanceof Sequent) {
			this.premises = premises;
			this.conclusion = conclusion;
    } else {
      throw new TypeError("LKJudgment has to contain Judgments and a Sequent");
    }
  }
}

// Beginning of LK rules

class TruthRight extends LKJudgment {
  constructor(conclusion, conclusionFormulaIndex) {
    super([], conclusion);
    this.isLeft = false;
    this.isRight = true;
	  if (conclusion.antecedent[conclusionFormulaIndex] instanceof Truth) {
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

class FalsityLeft extends LKJudgment {
  constructor(conclusion, conclusionFormulaIndex) {
    super([], conclusion);
    this.isLeft = true;
    this.isRight = false;
	  if (conclusion.precedent[conclusionFormulaIndex] instanceof Falsity) {
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

const getPremiseFormula = (premises, isInPrecedent, premiseIndex, premiseFormulaIndex) =>
  premises[premiseIndex]["conclusion"][isInPrecedent ? "precedent" : "antecedent"][premiseFormulaIndex]

class AndLeft extends LKJudgment {
  constructor(premises, conclusion, isInPrecedent, premiseIndex, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super(premises, conclusion);
    this.isLeft = true;
    this.isRight = false;
    if (premises.length !== 1) {
      throw new TypeError("Not the right number of premises");
    }
    const f1 = getPremiseFormula(premises, isInPrecedent, premiseIndex, premiseFormulaIndex1)
    const f2 = getPremiseFormula(premises, isInPrecedent, premiseIndex, premiseFormulaIndex2)

	  if (   getPremiseFormula(premises, isInPrecedent, premiseIndex, premiseFormulaIndex1) instanceof And
        && conclusion.precedent[conclusionFormulaIndex] instanceof And) {
      this.isInPrecedent = isInPrecedent;
      this.premiseIndex = premiseIndex;
      this.premiseFormulaIndex = premiseFormulaIndex;
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

class AndRight extends LKJudgment {
  constructor(premises, conclusion, isInPrecedent, premiseIndex, premiseFormulaIndex, conclusionFormulaIndex) {
    super(premises, conclusion);
    this.isLeft = false;
    this.isRight = true;
    if (premises.length !== 2) {
      throw new TypeError("Not the right number of premises");
    }
	  if (   getPremiseFormula(premises, isInPrecedent, premiseIndex, premiseFormulaIndex) instanceof And
        && conclusion.precedent[conclusionFormulaIndex] instanceof And) {
      this.isInPrecedent = isInPrecedent;
      this.premiseIndex = premiseIndex;
      this.premiseFormulaIndex = premiseFormulaIndex;
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

class ImpliesRight extends LKJudgment {
  constructor(premises, conclusion, premiseIndex, premiseFormulaIndex, conclusionFormulaIndex) {
    super(premises, conclusion);
    this.isLeft = false;
    this.isRight = true;
    if (premises.length !== 1) {
      throw new TypeError("Not the right number of premises");
    }
	  if (   getPremiseFormula(premises, isInPrecedent, premiseIndex, premiseFormulaIndex) instanceof Implies
        && conclusion.precedent[conclusionFormulaIndex] instanceof Implies) {
      this.isInPrecedent = isInPrecedent;
      this.premiseIndex = premiseIndex;
      this.premiseFormulaIndex = premiseFormulaIndex;
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

// End of LK rules
