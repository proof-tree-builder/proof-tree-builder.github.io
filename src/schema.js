
////////UTILITY FUNCTIONS ///////

// Check if argument (s) is a string
const isString = (s) => typeof s === "string" || s instanceof String


// Check deep equality
const deepEqual = (x, y) => {
  const ok = Object.keys,
        tx = typeof x,
        ty = typeof y;
  return x && y && tx === 'object' && tx === ty && x.constructor === y.constructor ? (
    ok(x).length === ok(y).length &&
      ok(x).every(key => deepEqual(x[key], y[key]))
  ) : (x === y);
}


// Check if argument (arr) is array of objects type (cl)
const arrayOf = (arr, cl) => arr instanceof Array && arr.every(a => a instanceof cl)

/////////FORMULA CLASS & CHILDREN ///////////

class Term {
  constructor() {
    if (new.target === Term) {
      throw new TypeError("Cannot construct Term instances directly");
    }
  }
}

class TermVar extends Term {
  constructor(v) {
    super()
    if (isString(v)) {
      this.v = v;
    } else {
      throw new TypeError("TermVar has to contain a String");
    }
  }
  unicode() { return this.v; }
  latex() { return this.v; }
}

class TermFun extends Term {
  constructor(name, args) {
    super()
    if (isString(name) && arrayOf(args, Term)) {
      this.name = name;
      this.args = args;
    } else {
      throw new TypeError("TermFun has to contain a String and Terms");
    }
  }
  unicode() { return `${this.name}(${this.args.map(x => x.unicode()).join(", ")})`; }
  latex() { return `${this.name}(${this.args.map(x => x.unicode()).join(", ")})`; }
}

// TODO think about this later.
// class TermConst extends Term {
// }


/////////FORMULA CLASS & CHILDREN ///////////

class Formula {

  constructor() {
    if (new.target === Formula) {
      throw new TypeError("Cannot construct Formula instances directly");
    }
  }

  // checks if we should put parens around this formula
  shouldParen () {
    return !(this instanceof Var || this instanceof Truth || this instanceof Falsity)
  }

  // parenthesize the formula if necessary in the Unicode or LaTeX rendering
  punicode() { return this.shouldParen() ?  `(${this.unicode()})` : this.unicode() }
  platex() { return this.shouldParen() ? `(${this.latex()})` : this.latex() }

  // checks if formula is quantified
  isQuantifier() {
    return this instanceof Forall || this instanceof Exists;
  }

  // checks if formula is quantifier free
  isQuantifierFree() {
    return !this.isQuantifier() && this.subformulas.every(f => f.isQuantifierFree())
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
    this.subformulas = [];
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

class Relation extends Formula {
  constructor(name, args) {
    super()
    if (isString(name) && arrayOf(args, Term)) {
      this.name = name;
      this.args = args;
      this.subformulas = [];
    } else {
      throw new TypeError("Relation has to contain a String and Terms");
    }
  }
  unicode() { return `${this.name}(${this.args.map(x => x.unicode()).join(", ")})`; }
  latex() { return `${this.name}(${this.args.map(x => x.unicode()).join(", ")})`; }
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

  unicode() { return `∀ ${this.v}. (${this.one.unicode()})` }
  latex() { return `\\forall ${this.v}. (${this.one.latex()})` }
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

  unicode() { return `∃ ${this.v}. (${this.one.unicode()})` }
  latex() { return `\\exists ${this.v}. (${this.one.latex()})` }
}


//////////SEQUENT CLASS //////////////

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

  isQuantifierFree() {
    return this.precedents.every(p => p.isQuantifierFree()) &&
           this.antecedents.every(q => q.isQuantifierFree());
  }
}


//////PROOFTREE ABSTRACT CLASS AND CHILDREN ////////

class ProofTree {
  constructor() {
    if (new.target === ProofTree) {
      throw new TypeError("Cannot construct ProofTree instances directly");
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


class LKProofTree extends ProofTree {
  constructor(premises, conclusion) {
    super();
    if (arrayOf(premises, LKProofTree) && conclusion instanceof Sequent) {
      this.premises = premises;
      this.conclusion = conclusion;
    } else {
      throw new TypeError("LKProofTree has to contain ProofTrees and a Sequent");
    }
  }

  latex() {
    var rule = `\\RightLabel{\\scriptsize $${this.latexName}$}`;
    switch (this.premises.length) {
      case 0:
        return `${rule}
\\AxiomC{$${this.conclusion.latex()}$}`
      case 1:
        return `${this.premises[0].latex()}
${rule}
\\UnaryC{$${this.conclusion.latex()}$}`
      case 2:
        return `${this.premises[0].latex()}
${this.premises[1].latex()}
${rule}
\\BinaryC{$${this.conclusion.latex()}$}`
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
class TruthRight extends LKProofTree {
  constructor(conclusion, conclusionFormulaIndex) {
    super([], conclusion);
    this.isLeft = false;
    this.isRight = true;
    this.unicodeName = "⊤-R"
    this.latexName = "\\top_R"
    this.connective = Truth;
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
class FalsityLeft extends LKProofTree {
  constructor(conclusion, conclusionFormulaIndex) {
    super([], conclusion);
    this.isLeft = true;
    this.isRight = false;
    this.unicodeName = "⊥-L"
    this.latexName = "\\bot_L"
    this.connective = Falsity;
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
class Identity extends LKProofTree {
  constructor(conclusion, conclusionFormulaIndex1, conclusionFormulaIndex2) {
    super([], conclusion);
    this.isLeft = false;
    this.isRight = false;
    this.connective = null;
    this.unicodeName = "Id"
    this.latexName = "Id"

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
class AndLeft extends LKProofTree {
  constructor(premise, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise], conclusion);
    this.isLeft = true;
    this.isRight = false;
    this.connective = And;
    this.unicodeName = "∧-L"
    this.latexName = "\\land_L"
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
class AndRight extends LKProofTree {
  constructor(premise1, premise2, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise1, premise2], conclusion);
    this.isLeft = false;
    this.isRight = true;
    this.connective = And;
    this.unicodeName = "∧-R"
    this.latexName = "\\land_R"
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
class ImpliesLeft extends LKProofTree {
  constructor(premise1, premise2, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise1, premise2], conclusion);
    this.isLeft = true;
    this.isRight = false;
    this.connective = Implies;
    this.unicodeName = "⇒-L"
    this.latexName = "\\Rightarrow_L"
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
class ImpliesRight extends LKProofTree {
  constructor(premise, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise], conclusion);
    this.isLeft = false;
    this.isRight = true;
    this.connective = Implies;
    this.unicodeName = "⇒-R"
    this.latexName = "\\Rightarrow_R"
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
class OrLeft extends LKProofTree {
  constructor(premise1, premise2, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise1, premise2], conclusion);
    this.isLeft = true;
    this.isRight = false;
    this.connective = Or;
    this.unicodeName = "∨-L"
    this.latexName = "\\lor_L"
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
class OrRight extends LKProofTree {
  constructor(premise, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise], conclusion);
    this.isLeft = false;
    this.isRight = true;
    this.connective = Or;
    this.unicodeName = "∨-R"
    this.latexName = "\\lor_R"
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
class NotLeft extends LKProofTree {
  constructor(premise, conclusion, premiseFormulaIndex, conclusionFormulaIndex) {
    console.log(premise);
    console.log(conclusion);
    super([premise], conclusion);
    this.isLeft = true;
    this.isRight = false;
    this.connective = Not;
    this.unicodeName = "¬-L"
    this.latexName = "\\lnot_L"
    const f1 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex)

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
class NotRight extends LKProofTree {
  constructor(premise, conclusion, premiseFormulaIndex, conclusionFormulaIndex) {
    super([premise], conclusion);
    this.isLeft = false;
    this.isRight = true;
    this.connective = Not;
    this.unicodeName = "¬-R"
    this.latexName = "\\lnot_R"
    const f1 = getPremiseFormula(this.premises, true, 0, premiseFormulaIndex)

    if (deepEqual(new Not(f1), conclusion.antecedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex = premiseFormulaIndex;
      this.conclusionFormulaIndex = conclusionFormulaIndex;
    } else {
      throw new TypeError("Not the right kind of formula at index");
    }
  }
}

// TODO forall and exists rules, and maybe cut?

class LKIncomplete extends LKProofTree {
  constructor(conclusion) {
    super([], conclusion)
    this.isLeft = false;
    this.isRight = false;
    this.connective = null;
    this.unicodeName = "?"
    this.latexName = "?"
  }
}

// End of LK rules
