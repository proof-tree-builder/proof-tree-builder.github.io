const isString = (s) => typeof s === "string" || s instanceof String
const arrayOf = (arr, cl) = arr instanceof Array && arr.every(a => a instanceof cl)

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
