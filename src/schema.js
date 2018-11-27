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
  shouldParen () {
    return !(this instanceof Var || this instanceof Truth || this instanceof Falsity)
  }
  // parenthesize the formula if necessary in the Unicode or LaTeX rendering
  punicode() { return this.shouldParen() ?  `(${this.unicode()})` : this.unicode() }
  platex() { return this.shouldParen() ? `(${this.latex()})` : this.latex() }

  isQuantifier() {
    return this instanceof Forall || this instanceof Exists;
  }

  isQuantifierFree() {
    return !this.isQuantifier && this.subformulas.every(f => f.isQuantifierFree())
  }
}

class Truth extends Formula {
  constructor() {
    super();
    this.subformulas = [];
  }
  unicode() { return "⊤" }
  latex() { return "\\top" }
}

class Falsity extends Formula {
  constructor() {
    super();
    this.subformulas = [];
  }
  unicode() { return "⊥" }
  latex() { return "\\bot" }
}

class Var extends Formula {
  constructor(v) {
		super();
	  if (isString(v)) {
			this.v = v;
    } else {
      throw new TypeError("Var has to contain a String");
    }
  }
  unicode() { return this.v }
  latex() { return this.v }
}

class And extends Formula {
  constructor(left, right) {
		super();
	  if (left instanceof Formula && right instanceof Formula) {
			this.left = left;
			this.right = right;
      this.subformulas = [left, right];
    } else {
      throw new TypeError("And has to contain Formulas");
    }
  }
  unicode() { return `${this.left.punicode()} ∧ ${this.right.punicode()}` }
  latex() { return `${this.left.platex()} \\land ${this.right.platex()}` }
}

class Or extends Formula {
  constructor(left, right) {
		super();
	  if (left instanceof Formula && right instanceof Formula) {
			this.left = left;
			this.right = right;
      this.subformulas = [left, right];
    } else {
      throw new TypeError("Or has to contain Formulas");
    }
  }
  unicode() { return `${this.left.punicode()} ∨ ${this.right.punicode()}` }
  latex() { return `${this.left.platex()} \\lor ${this.right.platex()}` }
}

class Implies extends Formula {
  constructor(left, right) {
		super();
	  if (left instanceof Formula && right instanceof Formula) {
			this.left = left;
			this.right = right;
      this.subformulas = [left, right];
    } else {
      throw new TypeError("Implies has to contain Formulas");
    }
  }
  unicode() { return `${this.left.punicode()} ⇒ ${this.right.punicode()}` }
  latex() { return `${this.left.platex()} \\Rightarrow ${this.right.platex()}` }
}

class Not extends Formula {
  constructor(one) {
		super();
	  if (one instanceof Formula) {
			this.one = one;
      this.subformulas = [one];
    } else {
      throw new TypeError("Not has to contain a Formula");
    }
  }
  unicode() { return `¬ ${this.one.punicode()}` }
  latex() { return `\\lnot ${this.one.platex()}` }
}

class Forall extends Formula {
  constructor(v, one) {
		super();
	  if (isString(v) && one instanceof Formula) {
			this.v = v;
			this.one = one;
      this.subformulas = [one];
    } else {
      throw new TypeError("Forall has to contain a String and a Formula");
    }
  }
  unicode() { return `∀ ${this.v}. (${this.left.unicode()})` }
  latex() { return `\\forall ${this.v}. (${this.left.latex()})` }
}

class Exists extends Formula {
  constructor(v, one) {
		super();
	  if (isString(v) && one instanceof Formula) {
			this.v = v;
			this.one = one;
      this.subformulas = [one];
    } else {
      throw new TypeError("Exists has to contain a String and a Formula");
    }
  }
  unicode() { return `∃ ${this.v}. (${this.left.unicode()})` }
  latex() { return `\\exists ${this.v}. (${this.left.latex()})` }
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
  unicode() {
    const left = this.precedents.length ? this.precedents.map(f => f.unicode()).join(", ") + " " : ""
    const right = this.antecedents.map(f => f.unicode())
    return `${left}⊢ ${right}`
  }
  latex() {
    const left = this.precedents.length ? this.precedents.map(f => f.latex()).join(", ") + " " : ""
    const right = this.antecedents.map(f => f.latex())
    return `${left}\\vdash ${right}`
  }
}

// Judgment abstract class and kinds of judgments

class Judgment {
  constructor() {
    if (new.target === Judgment) {
      throw new TypeError("Cannot construct Judgment instances directly");
    }
  }

  wrappedLatex () {
    return `% in the preamble
\\usepackage{bussproofs}

% where you want to have the proof tree
\\begin{prooftree}
${this.latex()}
\\end{prooftree}`;
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

  latex() {
    switch (this.premises.length) {
      case 0:
        return `\\AxiomC{${this.conclusion.latex()}}`
      case 1:
        return `${this.premises[0].latex()}\n\\UnaryC{${this.conclusion.latex()}}`
      case 2:
        return `${this.premises[0].latex()}\n${this.premises[1].latex()}\n\\BinaryC{${this.conclusion.latex()}}`
      default:
        throw new TypeError(`Don't know how to typeset a judgment with ${this.premises.length} premises`);
    }

  }
}

// Beginning of LK rules

/*
  −−−−−−−−− ⊤_R
  Γ ⊢ Δ, ⊤
*/
class TruthRight extends LKJudgment {
  constructor(conclusion, conclusionFormulaIndex) {
    super([], conclusion);
    this.isLeft = false;
    this.isRight = true;
	  if (conclusion.antecedents[conclusionFormulaIndex] instanceof Truth) {
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

/*
  −−−−−−−−− ⊥_L
  Γ, ⊥ ⊢ Δ
*/
class FalsityLeft extends LKJudgment {
  constructor(conclusion, conclusionFormulaIndex) {
    super([], conclusion);
    this.isLeft = true;
    this.isRight = false;
	  if (conclusion.precedents[conclusionFormulaIndex] instanceof Falsity) {
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

const getPremiseFormula = (premises, isInPrecedent, premiseIndex, premiseFormulaIndex) =>
  premises[premiseIndex]["conclusion"][isInPrecedent ? "precedents" : "antecedents"][premiseFormulaIndex]

/*
  −−−−−−−−−−−− I
  Γ, F ⊢ Δ, F
*/
class Identity extends LKJudgment {
  constructor(conclusion, conclusionFormulaIndex1, conclusionFormulaIndex2) {
    super([], conclusion);
    this.isLeft = false;
    this.isRight = false;

    if (deepEqual(conclusion.precedents[conclusionFormulaIndex1], conclusion.antecedents[conclusionFormulaIndex2])) {
			this.conclusionFormulaIndex1 = conclusionFormulaIndex1;
			this.conclusionFormulaIndex2 = conclusionFormulaIndex2;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

/*
  Γ, F, G ⊢ Δ
  −−−−−−−−−−−− ∧_L
  Γ, F ∧ G ⊢ Δ
*/
class AndLeft extends LKJudgment {
  constructor(premise, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise], conclusion);
    this.isLeft = true;
    this.isRight = false;
    const f1 = getPremiseFormula(this.premises, true, 0, premiseFormulaIndex1)
    const f2 = getPremiseFormula(this.premises, true, 0, premiseFormulaIndex2)

    if (deepEqual(new And(f1, f2), conclusion.precedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex1 = premiseFormulaIndex1;
      this.premiseFormulaIndex2 = premiseFormulaIndex2;
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

/*
  Γ ⊢ Δ, F     Γ ⊢ Δ, G
  −−−−−−−−−−−−--------- ∧_R
      Γ ⊢ Δ, F ∧ G
*/
class AndRight extends LKJudgment {
  constructor(premise1, premise2, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise1, premise2], conclusion);
    this.isLeft = false;
    this.isRight = true;
    const f1 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex1)
    const f2 = getPremiseFormula(this.premises, false, 1, premiseFormulaIndex2)

    if (deepEqual(new And(f1, f2), conclusion.antecedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex1 = premiseFormulaIndex1;
      this.premiseFormulaIndex2 = premiseFormulaIndex2;
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

/*
  Γ ⊢ F, Δ     Γ, G ⊢ Δ
  −−−−−−−−−−−−−−−−−−−−−− ⇒_L
      Γ, F ⇒ G ⊢ Δ
*/
class ImpliesLeft extends LKJudgment {
  constructor(premise1, premise2, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise1, premise2], conclusion);
    this.isLeft = true;
    this.isRight = false;
    const f1 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex1)
    const f2 = getPremiseFormula(this.premises, false, 1, premiseFormulaIndex2)

    if (deepEqual(new Implies(f1, f2), conclusion.precedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex1 = premiseFormulaIndex1;
      this.premiseFormulaIndex2 = premiseFormulaIndex2;
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

/*
  Γ, F ⊢ Δ, G
  −−−−−−−−−−−−- ⇒_R
  Γ ⊢ Δ, F ⇒ G
*/
class ImpliesRight extends LKJudgment {
  constructor(premise, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise], conclusion);
    this.isLeft = false;
    this.isRight = true;
    const f1 = getPremiseFormula(this.premises, true, 0, premiseFormulaIndex1)
    const f2 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex2)
    if (deepEqual(new Implies(f1, f2), conclusion.antecedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex1 = premiseFormulaIndex1;
      this.premiseFormulaIndex2 = premiseFormulaIndex2;
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

/*
  Γ, F ⊢ Δ     Γ, G ⊢ Δ
  −−−−−−−−−−−−−−−−−−−−− ∨_R
      Γ, F ∨ G ⊢ Δ
*/
class OrLeft extends LKJudgment {
  constructor(premise1, premise2, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise1, premise2], conclusion);
    this.isLeft = true;
    this.isRight = false;
    const f1 = getPremiseFormula(this.premises, true, 0, premiseFormulaIndex1)
    const f2 = getPremiseFormula(this.premises, true, 1, premiseFormulaIndex2)

    if (deepEqual(new Or(f1, f2), conclusion.precedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex1 = premiseFormulaIndex1;
      this.premiseFormulaIndex2 = premiseFormulaIndex2;
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

/*
  Γ ⊢ Δ, F, G
  −−−−−−−−−−−− ∨_R
  Γ ⊢ Δ, F ∨ G
*/
class OrRight extends LKJudgment {
  constructor(premise, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise], conclusion);
    this.isLeft = false;
    this.isRight = true;
    const f1 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex1)
    const f2 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex2)

    if (deepEqual(new Or(f1, f2), conclusion.antecedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex1 = premiseFormulaIndex1;
      this.premiseFormulaIndex2 = premiseFormulaIndex2;
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

/*
  Γ ⊢ Δ, F
  −−−−−−−−−−− ¬_L
  Γ, ¬ F ⊢ Δ
*/
class NotLeft extends LKJudgment {
  constructor(premise, conclusion, premiseFormulaIndex, conclusionFormulaIndex) {
    super([premise], conclusion);
    this.isLeft = true;
    this.isRight = false;
    const f1 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex1)

    if (deepEqual(new Not(f1), conclusion.precedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex = premiseFormulaIndex;
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

/*
  Γ, F ⊢ Δ
  −−−−−−−−−−− ¬_R
  Γ ⊢ ¬ F, Δ
*/
class NotRight extends LKJudgment {
  constructor(premise, conclusion, premiseFormulaIndex, conclusionFormulaIndex) {
    super([premise], conclusion);
    this.isLeft = false;
    this.isRight = true;
    const f1 = getPremiseFormula(this.premises, true, 0, premiseFormulaIndex1)

    if (deepEqual(new Not(f1), conclusion.antecedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex = premiseFormulaIndex;
			this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

// End of LK rules
