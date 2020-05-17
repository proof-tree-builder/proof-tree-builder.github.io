
/// /////UTILITY FUNCTIONS ///////

// Check if argument (s) is a string
const isString = (s) => typeof s === 'string' || s instanceof String

// Check deep equality
const deepEqual = (x, y) => {
  const ok = Object.keys

  const tx = typeof x

  const ty = typeof y
  return x && y && tx === 'object' && tx === ty && x.constructor === y.constructor ? (
    ok(x).length === ok(y).length &&
      ok(x).every(key => deepEqual(x[key], y[key]))
  ) : (x === y)
}

// Check if argument (arr) is array of objects type (cl)
const arrayOf = (arr, cl) => arr instanceof Array && arr.every(a => a instanceof cl)

/// //////TERM CLASS & CHILDREN ///////////

class Term {
  constructor () {
    if (new.target === Term) {
      throw new TypeError('Cannot construct Term instances directly')
    }
  }
}

class TermVar extends Term {
  constructor (v) {
    super()
    if (isString(v)) {
      this.v = v
    } else {
      throw new TypeError('TermVar has to contain a String')
    }
  }
  unicode () { return this.v }
  latex () { return this.v }
  smtlib () { return this.v }
}

class TermFun extends Term {
  constructor (name, args) {
    super()
    if (isString(name) && arrayOf(args, Term)) {
      this.name = name
      this.args = args
    } else {
      throw new TypeError('TermFun has to contain a String and Terms')
    }
  }
  unicode () { return `${this.name}(${this.args.map(x => x.unicode()).join(', ')})` }
  latex () { return `${this.name}(${this.args.map(x => x.latex()).join(', ')})` }
  smtlib () { return `(${this.name} ${this.args.map(x => x.smtlib()).join(' ')})` }
}

class TermInt extends Term {
  constructor (i) {
    super()
    if (Number.isInteger(i)) {
      this.i = i
    } else {
      throw new TypeError('TermInt has to contain an Integer')
    }
  }
  unicode () { return this.i }
  latex () { return this.i }
  smtlib () { return this.i >= 0 ? this.i : `(- ${-this.i})` }
}

/// //////FORMULA CLASS & CHILDREN ///////////

class Formula {
  constructor () {
    if (new.target === Formula) {
      throw new TypeError('Cannot construct Formula instances directly')
    }
  }

  // checks if we should put parens around this formula
  shouldParen () {
    return !(this instanceof Var || this instanceof Truth || this instanceof Falsity)
  }

  // parenthesize the formula if necessary in the Unicode or LaTeX rendering
  punicode () { return this.shouldParen() ? `(${this.unicode()})` : this.unicode() }
  platex () { return this.shouldParen() ? `(${this.latex()})` : this.latex() }

  // checks if formula is quantified
  isQuantifier () {
    return this instanceof Forall || this instanceof Exists
  }

  // checks if formula is quantifier free
  isQuantifierFree () {
    return !this.isQuantifier() && this.subformulas.every(f => f.isQuantifierFree())
  }
}

class Truth extends Formula {
  constructor () {
    super()
    this.subformulas = []
  }

  unicode () { return '⊤' }
  latex () { return '\\top' }
  smtlib () { return 'true' }
}

class Falsity extends Formula {
  constructor () {
    super()
    this.subformulas = []
  }

  unicode () { return '⊥' }
  latex () { return '\\bot' }
  smtlib () { return 'false' }
}

class Var extends Formula {
  constructor (v) {
    super()
    this.subformulas = []
    if (isString(v)) {
      this.v = v
    } else {
      throw new TypeError('Var has to contain a String')
    }
  }

  unicode () { return this.v }
  latex () { return this.v }
  smtlib () { return this.v }
}

class And extends Formula {
  constructor (left, right) {
    super()
    if (left instanceof Formula && right instanceof Formula) {
      this.left = left
      this.right = right
      this.subformulas = [left, right]
    } else {
      throw new TypeError('And has to contain Formulas')
    }
  }

  unicode () { return `${this.left.punicode()} ∧ ${this.right.punicode()}` }
  latex () { return `${this.left.platex()} \\land ${this.right.platex()}` }
  smtlib () { return `(and ${this.left.smtlib()} ${this.right.smtlib()})` }
}

class Or extends Formula {
  constructor (left, right) {
    super()
    if (left instanceof Formula && right instanceof Formula) {
      this.left = left
      this.right = right
      this.subformulas = [left, right]
    } else {
      throw new TypeError('Or has to contain Formulas')
    }
  }

  unicode () { return `${this.left.punicode()} ∨ ${this.right.punicode()}` }
  latex () { return `${this.left.platex()} \\lor ${this.right.platex()}` }
  smtlib () { return `(or ${this.left.smtlib()} ${this.right.smtlib()})` }
}

class Implies extends Formula {
  constructor (left, right) {
    super()
    if (left instanceof Formula && right instanceof Formula) {
      this.left = left
      this.right = right
      this.subformulas = [left, right]
    } else {
      throw new TypeError('Implies has to contain Formulas')
    }
  }

  unicode () { return `${this.left.punicode()} ⇒ ${this.right.punicode()}` }
  latex () { return `${this.left.platex()} \\Rightarrow ${this.right.platex()}` }
  smtlib () { return `(=> ${this.left.smtlib()} ${this.right.smtlib()})` }
}

class Not extends Formula {
  constructor (one) {
    super()
    if (one instanceof Formula) {
      this.one = one
      this.subformulas = [one]
    } else {
      throw new TypeError('Not has to contain a Formula')
    }
  }

  unicode () { return `¬ ${this.one.punicode()}` }
  latex () { return `\\lnot ${this.one.platex()}` }
  smtlib () { return `(not ${this.one.smtlib()})` }
}

class Relation extends Formula {
  constructor (name, args) {
    super()
    if (isString(name) && arrayOf(args, Term)) {
      this.name = name
      this.args = args
      this.subformulas = []
    } else {
      throw new TypeError('Relation has to contain a String and Terms')
    }
  }
  unicode () { return `${this.name}(${this.args.map(x => x.unicode()).join(', ')})` }
  latex () { return `${this.name}(${this.args.map(x => x.latex()).join(', ')})` }
  smtlib () { return `(${this.name} ${this.args.map(x => x.smtlib()).join(' ')})` }
}

class Forall extends Formula {
  constructor (v, one) {
    super()
    if (v instanceof TermVar && one instanceof Formula) {
      this.v = v
      this.one = one
      this.subformulas = [one]
    } else {
      throw new TypeError('Forall has to contain a TermVar and a Formula')
    }
  }

  unicode () { return `∀ ${this.v.unicode()}. (${this.one.unicode()})` }
  latex () { return `\\forall ${this.v.latex()}. (${this.one.latex()})` }
  // TODO right now all quantification we can do is with integers, might wanna change that later
  smtlib () { return `(forall (${this.v.latex()} Int) ${this.one.smtlib()})` }
}

class Exists extends Formula {
  constructor (v, one) {
    super()
    if (v instanceof TermVar && one instanceof Formula) {
      this.v = v
      this.one = one
      this.subformulas = [one]
    } else {
      throw new TypeError('Exists has to contain a TermVar and a Formula')
    }
  }

  unicode () { return `∃ ${this.v.unicode()}. (${this.one.unicode()})` }
  latex () { return `\\exists ${this.v.latex()}. (${this.one.latex()})` }
  // TODO right now all quantification we can do is with integers, might wanna change that later
  smtlib () { return `(exists (${this.v.latex()} Int) ${this.one.smtlib()})` }
}

/// ///////SEQUENT CLASS //////////////

class Sequent {
  constructor (precedents, antecedents) {
    if (arrayOf(precedents, Formula) && arrayOf(antecedents, Formula)) {
      this.precedents = precedents
      this.antecedents = antecedents
    } else {
      throw new TypeError('Sequent has to contain Formulas')
    }
  }

  unicode () {
    const left = this.precedents.length ? this.precedents.map(f => f.unicode()).join(', ') + ' ' : ''
    const right = this.antecedents.map(f => f.unicode())
    return `${left}⊢ ${right}`
  }

  latex () {
    const left = this.precedents.length ? this.precedents.map(f => f.latex()).join(', ') + ' ' : ''
    const right = this.antecedents.map(f => f.latex())
    return `${left}\\vdash ${right}`
  }

  smtlib () {
    const nest = (connective, formulae, baseCase) => {
      if(formulae.length === 0) {
        return baseCase
      } else if(formulae.length === 1) {
        return formulae[0].smtlib()
      } else {
        first = formulae[0]
        formulae.shift()
        return `(${connective} ${first.smtlib()} ${nest(connective, formulae, baseCase)})`
      }
    }

    const left = nest("and", this.precedents, "true")
    const right = nest("or", this.antecedents, "false")
    return `(=> ${left} ${right})`
  }

  isQuantifierFree () {
    return this.precedents.every(p => p.isQuantifierFree()) &&
           this.antecedents.every(q => q.isQuantifierFree())
  }
}

/// ///PROOFTREE ABSTRACT CLASS AND CHILDREN ////////

class ProofTree {
  constructor () {
    if (new.target === ProofTree) {
      throw new TypeError('Cannot construct ProofTree instances directly')
    }
  }

  wrappedLatex () {
    return `% in the preamble
\\usepackage{bussproofs}

% where you want to have the proof tree
\\begin{prooftree}
${this.latex()}
\\end{prooftree}`
  }
}

class LKProofTree extends ProofTree {
  constructor (premises, conclusion) {
    super()
    if (arrayOf(premises, LKProofTree) && conclusion instanceof Sequent) {
      this.premises = premises
      this.conclusion = conclusion
    } else {
      throw new TypeError('LKProofTree has to contain ProofTrees and a Sequent')
    }
  }

  latex () {
    var rule = `\\RightLabel{\\scriptsize $${this.latexName}$}`
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
        throw new TypeError(`Don't know how to typeset a judgment with ${this.premises.length} premises`)
    }
  }
}

// Beginning of LK rules

/*
  −−−−−−−−− ⊤_R
  Γ ⊢ Δ, ⊤
*/
class TruthRight extends LKProofTree {
  constructor (conclusion, conclusionFormulaIndex) {
    super([], conclusion)
    this.isLeft = false
    this.isRight = true
    this.unicodeName = '⊤-R'
    this.latexName = '\\top_R'
    this.connective = Truth
    if (conclusion.antecedents[conclusionFormulaIndex] instanceof Truth) {
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

/*
  −−−−−−−−− ⊥_L
  Γ, ⊥ ⊢ Δ
*/
class FalsityLeft extends LKProofTree {
  constructor (conclusion, conclusionFormulaIndex) {
    super([], conclusion)
    this.isLeft = true
    this.isRight = false
    this.unicodeName = '⊥-L'
    this.latexName = '\\bot_L'
    this.connective = Falsity
    if (conclusion.precedents[conclusionFormulaIndex] instanceof Falsity) {
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

const getPremiseFormula = (premises, isInPrecedent, premiseIndex, premiseFormulaIndex) =>
  premises[premiseIndex]['conclusion'][isInPrecedent ? 'precedents' : 'antecedents'][premiseFormulaIndex]

/*
  −−−−−−−−−−−− I
  Γ, F ⊢ Δ, F
*/
class Identity extends LKProofTree {
  constructor (conclusion, conclusionFormulaIndex1, conclusionFormulaIndex2) {
    super([], conclusion)
    this.isLeft = false
    this.isRight = false
    this.connective = null
    this.unicodeName = 'Id'
    this.latexName = 'Id'

    if (deepEqual(conclusion.precedents[conclusionFormulaIndex1], conclusion.antecedents[conclusionFormulaIndex2])) {
      this.conclusionFormulaIndex1 = conclusionFormulaIndex1
      this.conclusionFormulaIndex2 = conclusionFormulaIndex2
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

/*
  Γ, F, G ⊢ Δ
  −−−−−−−−−−−− ∧_L
  Γ, F ∧ G ⊢ Δ
*/
class AndLeft extends LKProofTree {
  constructor (premise, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise], conclusion)
    this.isLeft = true
    this.isRight = false
    this.connective = And
    this.unicodeName = '∧-L'
    this.latexName = '\\land_L'
    const f1 = getPremiseFormula(this.premises, true, 0, premiseFormulaIndex1)
    const f2 = getPremiseFormula(this.premises, true, 0, premiseFormulaIndex2)

    if (deepEqual(new And(f1, f2), conclusion.precedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex1 = premiseFormulaIndex1
      this.premiseFormulaIndex2 = premiseFormulaIndex2
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

/*
  Γ ⊢ Δ, F     Γ ⊢ Δ, G
  −−−−−−−−−−−−--------- ∧_R
      Γ ⊢ Δ, F ∧ G
*/
class AndRight extends LKProofTree {
  constructor (premise1, premise2, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise1, premise2], conclusion)
    this.isLeft = false
    this.isRight = true
    this.connective = And
    this.unicodeName = '∧-R'
    this.latexName = '\\land_R'
    const f1 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex1)
    const f2 = getPremiseFormula(this.premises, false, 1, premiseFormulaIndex2)

    if (deepEqual(new And(f1, f2), conclusion.antecedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex1 = premiseFormulaIndex1
      this.premiseFormulaIndex2 = premiseFormulaIndex2
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

/*
  Γ ⊢ F, Δ     Γ, G ⊢ Δ
  −−−−−−−−−−−−−−−−−−−−−− ⇒_L
      Γ, F ⇒ G ⊢ Δ
*/
class ImpliesLeft extends LKProofTree {
  constructor (premise1, premise2, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise1, premise2], conclusion)
    this.isLeft = true
    this.isRight = false
    this.connective = Implies
    this.unicodeName = '⇒-L'
    this.latexName = '\\Rightarrow_L'
    const f1 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex1)
    // changed false to true
    const f2 = getPremiseFormula(this.premises, true, 1, premiseFormulaIndex2)
    console.log((new Implies(f1, f2)).unicode())
    console.log(conclusion.precedents[conclusionFormulaIndex].unicode())

    if (deepEqual(new Implies(f1, f2), conclusion.precedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex1 = premiseFormulaIndex1
      this.premiseFormulaIndex2 = premiseFormulaIndex2
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

/*
  Γ, F ⊢ Δ, G
  −−−−−−−−−−−−- ⇒_R
  Γ ⊢ Δ, F ⇒ G
*/
class ImpliesRight extends LKProofTree {
  constructor (premise, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise], conclusion)
    this.isLeft = false
    this.isRight = true
    this.connective = Implies
    this.unicodeName = '⇒-R'
    this.latexName = '\\Rightarrow_R'
    const f1 = getPremiseFormula(this.premises, true, 0, premiseFormulaIndex1)
    const f2 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex2)
    if (deepEqual(new Implies(f1, f2), conclusion.antecedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex1 = premiseFormulaIndex1
      this.premiseFormulaIndex2 = premiseFormulaIndex2
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

/*
  Γ, F ⊢ Δ     Γ, G ⊢ Δ
  −−−−−−−−−−−−−−−−−−−−− ∨_R
      Γ, F ∨ G ⊢ Δ
*/
class OrLeft extends LKProofTree {
  constructor (premise1, premise2, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise1, premise2], conclusion)
    this.isLeft = true
    this.isRight = false
    this.connective = Or
    this.unicodeName = '∨-L'
    this.latexName = '\\lor_L'
    const f1 = getPremiseFormula(this.premises, true, 0, premiseFormulaIndex1)
    const f2 = getPremiseFormula(this.premises, true, 1, premiseFormulaIndex2)

    if (deepEqual(new Or(f1, f2), conclusion.precedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex1 = premiseFormulaIndex1
      this.premiseFormulaIndex2 = premiseFormulaIndex2
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

/*
  Γ ⊢ Δ, F, G
  −−−−−−−−−−−− ∨_R
  Γ ⊢ Δ, F ∨ G
*/
class OrRight extends LKProofTree {
  constructor (premise, conclusion, premiseFormulaIndex1, premiseFormulaIndex2, conclusionFormulaIndex) {
    super([premise], conclusion)
    this.isLeft = false
    this.isRight = true
    this.connective = Or
    this.unicodeName = '∨-R'
    this.latexName = '\\lor_R'
    const f1 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex1)
    const f2 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex2)

    if (deepEqual(new Or(f1, f2), conclusion.antecedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex1 = premiseFormulaIndex1
      this.premiseFormulaIndex2 = premiseFormulaIndex2
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

/*
  Γ ⊢ Δ, F
  −−−−−−−−−−− ¬_L
  Γ, ¬ F ⊢ Δ
*/
class NotLeft extends LKProofTree {
  constructor (premise, conclusion, premiseFormulaIndex, conclusionFormulaIndex) {
    super([premise], conclusion)
    this.isLeft = true
    this.isRight = false
    this.connective = Not
    this.unicodeName = '¬-L'
    this.latexName = '\\lnot_L'
    const f1 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex)

    if (deepEqual(new Not(f1), conclusion.precedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex = premiseFormulaIndex
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

/*
  Γ, F ⊢ Δ
  −−−−−−−−−−− ¬_R
  Γ ⊢ ¬ F, Δ
*/
class NotRight extends LKProofTree {
  constructor (premise, conclusion, premiseFormulaIndex, conclusionFormulaIndex) {
    super([premise], conclusion)
    this.isLeft = false
    this.isRight = true
    this.connective = Not
    this.unicodeName = '¬-R'
    this.latexName = '\\lnot_R'
    const f1 = getPremiseFormula(this.premises, true, 0, premiseFormulaIndex)

    if (deepEqual(new Not(f1), conclusion.antecedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex = premiseFormulaIndex
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

/// ////////////////// FORALL & EXISTS //////////

class ForallLeft extends LKProofTree {
  constructor (premise, conclusion, premiseFormulaIndex, conclusionFormulaIndex, t) {
    super([premise], conclusion)
    this.isLeft = true
    this.isRight = false
    this.connective = Forall
    this.unicodeName = '∀-L'
    this.latexName = '\\forall_L'

    // get the premise function
    const f1 = getPremiseFormula(this.premises, true, 0, premiseFormulaIndex)
    const f2 = conclusion.precedents[conclusionFormulaIndex]

    if (deepEqual(substituteTerm(f2.one, f2.v, t), f1)) {
      this.premiseFormulaIndex = premiseFormulaIndex
      this.conclusionFormulaIndex = conclusionFormulaIndex
      this.t = t
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

class ForallRight extends LKProofTree {
  constructor (premise, conclusion, premiseFormulaIndex, conclusionFormulaIndex, y) {
    super([premise], conclusion)
    this.isLeft = false
    this.isRight = true
    this.connective = Forall
    this.unicodeName = '∀-R'
    this.latexName = '\\forall_R'

    const f1 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex)
    const f2 = conclusion.antecedents[conclusionFormulaIndex]

    if (deepEqual(substituteTerm(f2.one, f2.v, y), f1)) {
      this.premiseFormulaIndex = premiseFormulaIndex
      this.conclusionFormulaIndex = conclusionFormulaIndex
      this.y = y
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

class ExistsLeft extends LKProofTree {
  constructor (premise, conclusion, premiseFormulaIndex, conclusionFormulaIndex, y) {
    super([premise], conclusion)
    this.isLeft = true
    this.isRight = false
    this.connective = Exists
    this.unicodeName = '∃-L'
    this.latexName = '\\exists_L'

    // get the premise function
    const f1 = getPremiseFormula(this.premises, true, 0, premiseFormulaIndex)
    const f2 = conclusion.precedents[conclusionFormulaIndex]

    if (deepEqual(substituteTerm(f2.one, f2.v, y), f1)) {
      this.premiseFormulaIndex = premiseFormulaIndex
      this.conclusionFormulaIndex = conclusionFormulaIndex
      this.y = y
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

class ExistsRight extends LKProofTree {
  constructor (premise, conclusion, premiseFormulaIndex, conclusionFormulaIndex, t) {
    super([premise], conclusion)
    this.isLeft = false
    this.isRight = true
    this.connective = Exists
    this.unicodeName = '∃-R'
    this.latexName = '\\exists_R'

    const f1 = getPremiseFormula(this.premises, false, 0, premiseFormulaIndex)
    const f2 = conclusion.antecedents[conclusionFormulaIndex]

    if (deepEqual(substituteTerm(f2.one, f2.v, t), f1)) {
      this.premiseFormulaIndex = premiseFormulaIndex
      this.conclusionFormulaIndex = conclusionFormulaIndex
      this.t = t
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }
}

class Cut extends LKProofTree {
  constructor (premise1, premise2, conclusion) {
    super([premise1, premise2], conclusion)
    this.unicodeName = 'Cut'
    this.latexName = '\\textrm{Cut}'
  }
}

class LKIncomplete extends LKProofTree {
  constructor (conclusion) {
    super([], conclusion)
    this.isLeft = false
    this.isRight = false
    this.connective = null
    this.unicodeName = '?'
    this.latexName = '?'
  }

  latex () {
    if (this.completer) {
      return this.completer.latex()
    } else {
      var rule = `\\RightLabel{\\scriptsize $${this.latexName}$}`
      return `${rule}\n\\AxiomC{$${this.conclusion.latex()}$}`
    }
  }
}

// End of LK rules

/// ////////////// HOARE STUFF /////////////////////////////

class AddTerms extends TermFun {
  constructor (first, second) {
    // parent constructor will throw error if arguments are not terms
    super('+', [first, second])
    this.first = first
    this.second = second
  }
  unicode () { return `${this.first.unicode()} + ${this.second.unicode()}` }
  latex () { return `${this.first.latex()} + ${this.second.latex()}` }
}

class SubtractTerms extends TermFun {
  constructor (first, second) {
    // parent constructor will throw error if arguments are not terms
    super('-', [first, second])
    this.first = first
    this.second = second
  }
  unicode () { return `${this.first.unicode()} - ${this.second.unicode()}` }
  latex () { return `${this.first.latex()} - ${this.second.latex()}` }
}

class MultiplyTerms extends TermFun {
  constructor (first, second) {
    // parent constructor will throw error if arguments are not terms
    super('*', [first, second])
    this.first = first
    this.second = second
  }
  unicode () { return `${this.first.unicode()} * ${this.second.unicode()}` }
  latex () { return `${this.first.latex()} * ${this.second.latex()}` }
}

class DivideTerms extends TermFun {
  constructor (first, second) {
    // parent constructor will throw error if arguments are not terms
    super('/', [first, second])
    this.first = first
    this.second = second
  }
  unicode () { return `${this.first.unicode()} / ${this.second.unicode()}` }
  latex () { return `${this.first.latex()} / ${this.second.latex()}` }
}

class LessThan extends Relation {
  constructor (lhs, rhs) {
    // parent constructor will throw error if arguments are not terms
    super('<', [lhs, rhs])
    this.lhs = lhs
    this.rhs = rhs
  }
  unicode () { return `${this.lhs.unicode()} < ${this.rhs.unicode()}` }
  latex () { return `${this.lhs.latex()} < ${this.rhs.latex()}` }
}

class GreaterThan extends Relation {
  constructor (lhs, rhs) {
    // parent constructor will throw error if arguments are not terms
    super('>', [lhs, rhs])
    this.lhs = lhs
    this.rhs = rhs
  }
  unicode () { return `${this.lhs.unicode()} > ${this.rhs.unicode()}` }
  latex () { return `${this.lhs.latex()} > ${this.rhs.latex()}` }
}

class LeqThan extends Relation {
  constructor (lhs, rhs) {
    // parent constructor will throw error if arguments are not terms
    super('<=', [lhs, rhs])
    this.lhs = lhs
    this.rhs = rhs
  }
  unicode () { return `${this.lhs.unicode()} ≤ ${this.rhs.unicode()}` }
  latex () { return `${this.lhs.latex()} \\leq ${this.rhs.latex()}` }
}

class GeqThan extends Relation {
  constructor (lhs, rhs) {
    // parent constructor will throw error if arguments are not terms
    super('>=', [lhs, rhs])
    this.lhs = lhs
    this.rhs = rhs
  }
  unicode () { return `${this.lhs.unicode()} ≥ ${this.rhs.unicode()}` }
  latex () { return `${this.lhs.latex()} \\geq ${this.rhs.latex()}` }
}

class Equal extends Relation {
  constructor (lhs, rhs) {
    // parent constructor will throw error if arguments are not terms
    super('=', [lhs, rhs])
    this.lhs = lhs
    this.rhs = rhs
  }
  unicode () { return `${this.lhs.unicode()} = ${this.rhs.unicode()}` }
  latex () { return `${this.lhs.latex()} = ${this.rhs.latex()}` }
}

/// ////////////// COMMANDS /////////////////////////////

class Command {
  constructor () {
    if (new.target === Command) {
      throw new TypeError('Cannot construct Command instances directly')
    }
  }
}

class CmdAssign extends Command {
  constructor (v, t) {
    super()
    this.subcommands = []
    if (v instanceof TermVar && t instanceof Term) {
      this.v = v
      this.t = t
    } else {
      throw new TypeError('Assign has to contain a variable and a term')
    }
  }

  unicode () { return `${this.v.unicode()} := ${this.t.unicode()}` }
  latex () { return `${this.v.latex()} := ${this.t.latex()}` }
}

class CmdSeq extends Command {
  constructor (first, second) {
    super()
    if (first instanceof Command && second instanceof Command) {
      this.first = first
      this.second = second
      this.subcommands = [first, second]
    } else {
      throw new TypeError('Seq has to contain Commands')
    }
  }

  unicode () { return `${this.first.unicode()} ; ${this.second.unicode()}` }
  latex () { return `${this.first.latex()} ; ${this.second.latex()}` }
}

class CmdIf extends Command {
  constructor (condition, btrue, bfalse) {
    super()
    if (btrue instanceof Command && bfalse instanceof Command && condition instanceof Formula) {
      this.condition = condition
      this.btrue = btrue
      this.bfalse = bfalse
      this.subcommands = [btrue, bfalse]
    } else {
      throw new TypeError('If has to contain Commands and a Formula')
    }
  }

  unicode () { return `if (${this.condition.unicode()}) then (${this.btrue.unicode()}) else (${this.bfalse.unicode()})` }
  latex () { return `if (${this.condition.latex()}) then (${this.btrue.latex()}) else (${this.bfalse.latex()})` }
}

class CmdWhile extends Command {
  constructor (condition, body) {
    super()
    if (body instanceof Command && condition instanceof Formula) {
      this.condition = condition
      this.body = body
      this.subcommands = [body]
    } else {
      throw new TypeError('While has to contain Commands and a Formula')
    }
  }

  unicode () { return `while (${this.condition.unicode()}) do (${this.body.unicode()})` }
  latex () { return `while (${this.condition.latex()}) do (${this.body.latex()})` }
}

/// ////////////// HOARE TRIPLE /////////////////////////////

class HoareTriple {
  constructor (pre, command, post) {
    if (pre instanceof Formula && post instanceof Formula && command instanceof Command) {
      this.pre = pre
      this.post = post
      this.command = command
    } else {
      throw new TypeError('Hoare Triple has to contain Formulas and a Command')
    }
  }

  unicode () {
    return `⊢ {${this.pre.unicode()}} ${this.command.unicode()} {${this.post.unicode()}}`
  }

  latex () {
    return `\\vdash {${this.pre.latex()}} ${this.command.latex()} {${this.post.latex()}}`
  }
}

/// ////////////// HOARE PROOF TREE /////////////////////////////

class HoareProofTree extends ProofTree {
  constructor (premises, conclusion) {
    super()
    if (premises.length === 0 && conclusion == null) {
      this.premises = []
      this.conclusion = null
    } else if (arrayOf(premises, HoareProofTree) && conclusion instanceof HoareTriple) {
      this.premises = premises
      this.conclusion = conclusion
    } else {
      throw new TypeError('HoareProofTree must have trees and a triple')
    }
  }

  latex () {
    var rule = `\\RightLabel{\\scriptsize $${this.latexName}$}`
    if (this.premises.length === 0 && this.conclusion == null) {
      return ''
    }
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
      case 3:
        return `${this.premises[0].latex()}
${this.premises[1].latex()}
${this.premises[2].latex()}
${rule}
\\TernaryC{$${this.conclusion.latex()}$}`
      default:
        throw new TypeError(`Don't know how to typeset a judgment with ${this.premises.length} premises`)
    }
  }
}

class ChangeCondition extends HoareProofTree {
  constructor (left, right) {
    super([], null)
    this.left = left
    this.right = right
    this.unicodeName = ''
    this.latexName = ''
    this.command = null
  }

  unicode () { return `${this.left.unicode()} ⊢ ${this.right.unicode()}` }
  latex () { return `${this.left.latex()} \\vdash ${this.right.latex()}` }
}

// formula classes: Truth, Falsity, Var, And, Or, Implies, Not, Exists, Forall, Relation
// term classes: TermVar, TermFun, TermInt

// v has to be a termvar
function substituteTerm (formula, v, term) {
  if (!(v instanceof TermVar && term instanceof Term)) {
    throw new TypeError('Substitution can only be done using terms.')
  }

  // base cases
  if (formula instanceof Truth) {
    return new Truth()
  }
  if (formula instanceof Falsity) {
    return new Falsity()
  }
  if (formula instanceof Var) {
    return new Var(formula.v)
  }

  if (formula instanceof And) {
    return new And(substituteTerm(formula.left, v, term),
      substituteTerm(formula.right, v, term))
  }
  if (formula instanceof Or) {
    return new Or(substituteTerm(formula.left, v, term),
      substituteTerm(formula.right, v, term))
  }
  if (formula instanceof Implies) {
    return new Implies(substituteTerm(formula.left, v, term),
      substituteTerm(formula.right, v, term))
  }
  if (formula instanceof Not) {
    return new Not(substituteTerm(clone.one, v, term))
  }

  if (formula instanceof LessThan) {
    var args = formula.args
    var newargs = args.slice()
    var newRelation = new LessThan(formula.lhs, formula.rhs)

    if (deepEqual(v, formula.lhs)) {
      newRelation.lhs = term
    }
    if (deepEqual(v, formula.rhs)) {
      newRelation.rhs = term
    }

    newRelation.args = [newRelation.lhs, newRelation.rhs]

    return newRelation
  }
  if (formula instanceof GreaterThan) {
    var args = formula.args
    var newargs = args.slice()
    var newRelation = new GreaterThan(formula.lhs, formula.rhs)

    if (deepEqual(v, formula.lhs)) {
      newRelation.lhs = term
    }
    if (deepEqual(v, formula.rhs)) {
      newRelation.rhs = term
    }

    newRelation.args = [newRelation.lhs, newRelation.rhs]

    return newRelation
  }
  if (formula instanceof LeqThan) {
    var args = formula.args
    var newargs = args.slice()
    var newRelation = new LeqThan(formula.lhs, formula.rhs)

    if (deepEqual(v, formula.lhs)) {
      newRelation.lhs = term
    }
    if (deepEqual(v, formula.rhs)) {
      newRelation.rhs = term
    }

    newRelation.args = [newRelation.lhs, newRelation.rhs]

    return newRelation
  }
  if (formula instanceof GeqThan) {
    var args = formula.args
    var newargs = args.slice()
    var newRelation = new GeqThan(formula.lhs, formula.rhs)

    if (deepEqual(v, formula.lhs)) {
      newRelation.lhs = term
    }
    if (deepEqual(v, formula.rhs)) {
      newRelation.rhs = term
    }

    newRelation.args = [newRelation.lhs, newRelation.rhs]

    return newRelation
  }

  if (formula instanceof Relation) {
    var args = formula.args
    var newargs = args.slice()

    for (var i = 0; i < args.length; i++) {
      element = args[i]
      if (deepEqual(v, element)) {
        newargs[i] = term
      }
    }

    return new Relation(formula.name, newargs)
  }

  if (formula instanceof Exists) {
    var quantvar = clone.v
    var body = clone.one

    if (deepEqual(v, quantvar)) {
      // case: replace one var with another
      if (term instanceof TermVar) {
        return new Exists(term, substituteTerm(body, v, term))
      } else {
        return substituteTerm(body, v, term)
      }
    } else {
      return new Exists(formula.v, substituteTerm(body, v, term))
    }
  }

  if (formula instanceof Forall) {
    var quantvar = clone.v
    var body = clone.one

    if (deepEqual(v, quantvar)) {
      // case: replace one var with another
      if (term instanceof TermVar) {
        return new Forall(term, substituteTerm(body, v, term))
      } else {
        return substituteTerm(body, v, term)
      }
    } else {
      return new Forall(formula.v, substituteTerm(body, v, term))
    }
  }
}

/*
  −−−−−−−−−---------------  ASGN
  ⊢ {F[v -> t]} v := t {F}
*/
class Assignment extends HoareProofTree {
  constructor (conclusion) {
    super([], conclusion)
    this.unicodeName = 'ASGN'
    this.latexName = 'ASGN'
    this.command = CmdAssign
    if (!(conclusion.command instanceof CmdAssign)) {
      throw new TypeError('Not the right kind of Command')
    }
  }
}

/*
  ⊢ {F} S1 {F'}  ⊢ {F'} S2 {F''}
  −−−−−−−−−−−−------------------- SEQ
      ⊢ {F} S1; S2 {F''}
*/
class Sequencing extends HoareProofTree {
  constructor (premise1, premise2, conclusion) {
    super([premise1, premise2], conclusion)
    this.command = CmdSeq
    this.unicodeName = 'SEQ'
    this.latexName = 'SEQ'

    if (!(deepEqual(premise1.conclusion.command, conclusion.command.first) &&
    deepEqual(premise2.conclusion.command, conclusion.command.second) &&
    deepEqual(premise1.conclusion.pre, conclusion.pre) &&
    deepEqual(premise2.conclusion.post, conclusion.post) &&
    deepEqual(premise1.conclusion.post, premise2.conclusion.pre))) {
      throw new TypeError("Commands and conditions don't match up")
    }
  }
}

/*
  F ⊢ F'  ⊢ {F'} S {G'} G' ⊢ G
  −−−−−−−−−−−−---------------------- CONS
        ⊢ {F} S {G}
*/
class Consequence extends HoareProofTree {
  constructor (premise1, premise2, premise3, conclusion) {
    super([premise1, premise2, premise3], conclusion)
    if (arrayOf([premise1, premise3], ChangeCondition)) {
      this.command = conclusion.command
      this.unicodeName = 'CONS'
      this.latexName = 'CONS'
    } else {
      throw new TypeError('First and last premise must be ChangeCondition')
    }

    if (!(deepEqual(premise2.conclusion.command, conclusion.command) &&
    deepEqual(premise1.left, conclusion.pre) &&
    deepEqual(premise3.right, conclusion.post) &&
    deepEqual(premise1.right, premise2.conclusion.pre) &&
    deepEqual(premise3.left, premise2.conclusion.post))) {
      throw new TypeError("Commands and conditions don't match up")
    }
  }
}

/*
  ⊢ {F ∧ c} S {F'}    ⊢ {F ∧ ¬c} S' {F'}
  −−−−−−−−−−−−---------------------------- COND
    ⊢ {F} if c then S else S' {F'}
*/

class Conditional extends HoareProofTree {
  constructor (premise1, premise2, conclusion) {
    super([premise1, premise2], conclusion)
    this.command = CmdIf
    this.unicodeName = 'COND'
    this.latexName = 'COND'

    var c = conclusion.command.condition

    if (!(deepEqual(premise1.conclusion.command, conclusion.command.btrue) &&
    deepEqual(premise2.conclusion.command, conclusion.command.bfalse) &&
    deepEqual(premise1.conclusion.post, conclusion.post) &&
    deepEqual(premise2.conclusion.post, conclusion.post) &&
    deepEqual(premise1.conclusion.pre, new And(conclusion.pre, c)) &&
    deepEqual(premise2.conclusion.pre, new And(conclusion.pre, new Not(c))))) {
      throw new TypeError("Commands and conditions don't match up")
    }
  }
}

/*
        ⊢ {F ∧ c} S {F}
  −−−−−−−−−−−−------------------- LOOP
    ⊢ {F} while c do S {F ∧ ¬c}
*/

class Loop extends HoareProofTree {
  constructor (premise, conclusion) {
    super([premise], conclusion)
    this.command = CmdWhile
    this.unicodeName = 'LOOP'
    this.latexName = 'LOOP'

    var c = conclusion.command.condition

    if (!(deepEqual(premise.conclusion.command, conclusion.command.body) &&
    deepEqual(premise.conclusion.post, conclusion.pre) &&
    deepEqual(premise.conclusion.pre, new And(conclusion.pre, c)) &&
    deepEqual(conclusion.post, new And(conclusion.pre, new Not(c))))) {
      throw new TypeError("Commands and conditions don't match up")
    }
  }
}

class HoareIncomplete extends HoareProofTree {
  constructor (conclusion) {
    super([], conclusion)
    this.connective = null
    this.unicodeName = '?'
    this.latexName = '?'
  }

  latex () {
    if (this.completer) {
      return this.completer.latex()
    } else {
      var rule = `\\RightLabel{\\scriptsize $${this.latexName}$}`
      return `${rule}\n\\AxiomC{$${this.conclusion.latex()}$}`
    }
  }
}
