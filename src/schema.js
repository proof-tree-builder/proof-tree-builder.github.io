// Check if argument (s) is a string
const isString = (s) => typeof s === 'string' || s instanceof String

// Check deep equality
const deepEqual = (x, y) => {
  const tx = typeof x
  const ty = typeof y
  return x && y && tx === 'object' && tx === ty && x.constructor === y.constructor ? (
    Object.keys(x).length === Object.keys(y).length &&
      Object.keys(x).every(key => deepEqual(x[key], y[key]))
  ) : (x === y)
}

// Check if argument (arr) is array of objects type (cl)
const arrayOf = (arr, cl) => arr instanceof Array && arr.every(a => a instanceof cl)

class Term {
  constructor () {
    if (new.target === Term) {
      throw new TypeError('Cannot construct Term instances directly')
    }
  }

  // checks if we should put parens around this formula
  shouldParen () {
    return !(this instanceof TermVar || this instanceof TermInt || this instanceof TermFun)
  }

  // parenthesize the formula if necessary in the Unicode or LaTeX rendering
  punicode () { return this.shouldParen() ? `(${this.unicode()})` : this.unicode() }
  platex () { return this.shouldParen() ? `(${this.latex()})` : this.latex() }
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

  subst(v, term) {
    return (deepEqual(this, v)) ? term : this
  }

  unicode () { return this.v }
  latex () { return this.v }
  smtlib () { return this.v }
  reconstructor () { return `new TermVar("${this.v}")` }

  getFreeVars () { return [this] }
  getFunctions () { return [] }
}

class TermFun extends Term {
  constructor (name, args) {
    super()
    if (isString(name) && arrayOf(args, Term)) {
      this.name = name
      this.args = args
      this.primitive = false
    } else {
      throw new TypeError('TermFun has to contain a String and Terms')
    }
  }

  subst(v, term) {
    let subargs = this.args.map(t => t.subst(v, term))
    return new TermFun(this.name, subargs)
  }

  unicode () { return `${this.name}(${this.args.map(x => x.punicode()).join(', ')})` }
  latex () { return `${this.name}(${this.args.map(x => x.platex()).join(', ')})` }
  smtlib () { return `(${this.name}${this.primitive ? '' : '_' + this.args.length} ${this.args.map(x => x.smtlib()).join(' ')})` }
  reconstructor () { return `new TermFun("${this.name}", [${this.args.map(arg => arg.reconstructor()).join(", ")}])` }

  getFreeVars () { return this.args.map(arg => arg.getFreeVars()).flat() }
  getFunctions () { return this.args.map(arg => arg.getFunctions()).flat().concat(this) }
}

class TermInt extends Term {
  constructor (i) {
    super()
    this.args = []
    if (Number.isInteger(i)) {
      this.i = i
    } else {
      throw new TypeError('TermInt has to contain an Integer')
    }
  }

  subst (v, term) { return this }

  unicode () { return this.i }
  latex () { return this.i }
  smtlib () { return this.i >= 0 ? this.i : `(- ${-this.i})` }
  reconstructor () { return `new TermInt(${ this.i })` }

  getFreeVars () { return [] }
  getFunctions () { return [] }
}

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

  getFreeTermVars () { return this.subformulas.map(f => f.getFreeTermVars()).flat() }
  getFreePropVars () { return this.subformulas.map(f => f.getFreePropVars()).flat() }
  getRelations () { return this.subformulas.map(f => f.getRelations()).flat() }
  getFunctions () { return this.subformulas.map(f => f.getFunctions()).flat() }
}

class Truth extends Formula {
  constructor () {
    super()
    this.subformulas = []
  }

  subst (v, term) { return this }

  unicode () { return '⊤' }
  latex () { return '\\top' }
  smtlib () { return 'true' }
  reconstructor () { return `new Truth()` }
}

class Falsity extends Formula {
  constructor () {
    super()
    this.subformulas = []
  }

  subst (v, term) { return this }

  unicode () { return '⊥' }
  latex () { return '\\bot' }
  smtlib () { return 'false' }
  reconstructor () { return `new Falsity()` }
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

  subst (v, term) { return this }

  unicode () { return this.v }
  latex () { return this.v }
  smtlib () { return this.v }
  reconstructor () { return `new Var("${this.v}")` }
  getFreePropVars () { return [this] }
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

  subst (v, term) {
    return new And(this.left.subst(v, term),
                   this.right.subst(v, term))
  }

  unicode () { return `${this.left.punicode()} ∧ ${this.right.punicode()}` }
  latex () { return `${this.left.platex()} \\land ${this.right.platex()}` }
  smtlib () { return `(and ${this.left.smtlib()} ${this.right.smtlib()})` }
  reconstructor () { return `new And(${this.left.reconstructor()}, ${this.right.reconstructor()})` }
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

  subst (v, term) {
    return new Or(this.left.subst(v, term),
                  this.right.subst(v, term))
  }

  unicode () { return `${this.left.punicode()} ∨ ${this.right.punicode()}` }
  latex () { return `${this.left.platex()} \\lor ${this.right.platex()}` }
  smtlib () { return `(or ${this.left.smtlib()} ${this.right.smtlib()})` }
  reconstructor () { return `new Or(${this.left.reconstructor()}, ${this.right.reconstructor()})` }
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

  subst (v, term) {
    return new Implies(this.left.subst(v, term),
                       this.right.subst(v, term))
  }

  unicode () { return `${this.left.punicode()} ⇒ ${this.right.punicode()}` }
  latex () { return `${this.left.platex()} \\Rightarrow ${this.right.platex()}` }
  smtlib () { return `(=> ${this.left.smtlib()} ${this.right.smtlib()})` }
  reconstructor () { return `new Implies(${this.left.reconstructor()}, ${this.right.reconstructor()})` }
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

  subst (v, term) {
    return new Not(this.one.subst(v, term))
  }

  unicode () { return `¬ ${this.one.punicode()}` }
  latex () { return `\\lnot ${this.one.platex()}` }
  smtlib () { return `(not ${this.one.smtlib()})` }
  reconstructor () { return `new Not(${this.one.reconstructor()})` }
}

class Relation extends Formula {
  constructor (name, args) {
    super()
    if (isString(name) && arrayOf(args, Term)) {
      this.name = name
      this.args = args
      this.subformulas = []
      this.primitive = false
    } else {
      throw new TypeError('Relation has to contain a String and Terms')
    }
  }

  subst (v, term) {
    return new Relation(this.name, this.args.map(arg => arg.subst(v, term)))
  }

  unicode () { return `${this.name}(${this.args.map(x => x.unicode()).join(', ')})` }
  latex () { return `${this.name}(${this.args.map(x => x.latex()).join(', ')})` }
  smtlib () { return `(${this.name}${this.primitive ? '' : '_' + this.args.length} ${this.args.map(x => x.smtlib()).join(' ')})` }
  reconstructor () { return `new Relation("${this.name}", [${this.args.map(arg => arg.reconstructor()).join(", ")}])` }

  getFreeTermVars () { return this.args.map(f => f.getFreeVars()).flat() }
  getRelations () { return [this] }
  getFunctions () { return this.args.map(f => f.getFunctions()).flat() }
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

  subst (v, term) {
    if(deepEqual(this.v, v)) {
      return this
    } else {
      let fvs = term.getFreeVars()
      if(fvs.some(fv => deepEqual(fv, this.v))) {
        // avoid capture
        let v2 = new TermVar(this.v.v + "1") // FIXME no guarantee this is fresh
        return new Forall(v2, this.one.subst(this.v, v2).subst(v, term))
      } else {
        return new Forall(this.v, this.one.subst(v, term))
      }
    }
  }


  unicode () { return `∀ ${this.v.unicode()}. (${this.one.unicode()})` }
  latex () { return `\\forall ${this.v.latex()}. (${this.one.latex()})` }
  // TODO right now all quantification we can do is with integers, might wanna change that later
  smtlib () { return `(forall ((${this.v.latex()} Int)) ${this.one.smtlib()})` }
  reconstructor () { return `new Forall(${this.v.reconstructor()}, ${this.one.reconstructor()})` }

  getFreeTermVars () { return this.one.getFreeTermVars().filter(fv => !deepEqual(fv, this.v)) }
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

  subst (v, term) {
    if(deepEqual(this.v, v)) {
      return this
    } else {
      let fvs = term.getFreeVars()
      if(fvs.some(fv => deepEqual(fv, this.v))) {
        // avoid capture
        let v2 = new TermVar(this.v.v + "1") // FIXME no guarantee this is fresh
        return new Exists(v2, this.one.subst(this.v, v2).subst(v, term))
      } else {
        return new Exists(this.v, this.one.subst(v, term))
      }
    }
  }

  unicode () { return `∃ ${this.v.unicode()}. (${this.one.unicode()})` }
  latex () { return `\\exists ${this.v.latex()}. (${this.one.latex()})` }
  // TODO right now all quantification we can do is with integers, might wanna change that later
  smtlib () { return `(exists ((${this.v.latex()} Int)) ${this.one.smtlib()})` }
  reconstructor () { return `new Exists(${this.v.reconstructor()}, ${this.one.reconstructor()})` }

  getFreeTermVars () { return this.one.getFreeTermVars().filter(fv => !deepEqual(fv, this.v)) }
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
    const right = this.antecedents.length ? this.antecedents.map(f => f.unicode()).join(', ') + ' ' : ''
    return `${left}⊢ ${right}`
  }

  latex () {
    const left = this.precedents.length ? this.precedents.map(f => f.latex()).join(', ') + ' ' : ''
    const right = this.antecedents.length ? this.antecedents.map(f => f.latex()).join(', ') + ' ' : ''
    return `${left}\\vdash ${right}`
  }

  smtlib () {
    const nest = (connective, formulae, baseCase) => {
      if(formulae.length === 0) {
        return baseCase
      } else if(formulae.length === 1) {
        return formulae[0].smtlib()
      } else {
        const first = formulae[0]
        return `(${connective} ${first.smtlib()} ${nest(connective, formulae.slice(1), baseCase)})`
      }
    }

    const left = nest("and", this.precedents, "true")
    const right = nest("or", this.antecedents, "false")
    return `(=> ${left} ${right})`
  }

  reconstructor () { 
    return `new Sequent([${this.precedents.map(f => f.reconstructor()).join(", ")}], [${this.antecedents.map(f => f.reconstructor()).join(", ")}])` 
  }

  isQuantifierFree () {
    return this.precedents.every(p => p.isQuantifierFree()) &&
           this.antecedents.every(q => q.isQuantifierFree())
  }

  getFreeTermVars () {
    return this.precedents.map(p => p.getFreeTermVars()).flat()
            .concat(this.antecedents.map(q => q.getFreeTermVars()).flat())
  }
  getFreePropVars () {
    return this.precedents.map(p => p.getFreePropVars()).flat()
            .concat(this.antecedents.map(q => q.getFreePropVars()).flat())
  }
  getRelations () {
    return this.precedents.map(p => p.getRelations()).flat()
            .concat(this.antecedents.map(q => q.getRelations()).flat())
  }
  getFunctions () {
    return this.precedents.map(p => p.getFunctions()).flat()
            .concat(this.antecedents.map(q => q.getFunctions()).flat())
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
    var prefix = this.premises.length === 0 ? '\\AxiomC{}' : ''
    var rule = prefix + `\\RightLabel{\\scriptsize $${this.latexName}$}`
    switch (this.premises.length) {
      case 0:
        return `${rule}
\\UnaryInfC{$${this.conclusion.latex()}$}`
      case 1:
        return `${this.premises[0].latex()}
${rule}
\\UnaryInfC{$${this.conclusion.latex()}$}`
      case 2:
        return `${this.premises[0].latex()}
${this.premises[1].latex()}
${rule}
\\BinaryInfC{$${this.conclusion.latex()}$}`
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

  reconstructor () {
    return `new TruthRight(${this.conclusion.reconstructor()}, ${this.conclusionFormulaIndex})`
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

  reconstructor () {
    return `new FalsityLeft(${this.conclusion.reconstructor()}, ${this.conclusionFormulaIndex})`
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

  reconstructor () {
    return `new Identity(${this.conclusion.reconstructor()}, ${this.conclusionFormulaIndex1}, ${this.conclusionFormulaIndex2})`
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

  reconstructor () {
    return `new AndLeft(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.premiseFormulaIndex1}, ${this.premiseFormulaIndex2}, ${this.conclusionFormulaIndex})`
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

  reconstructor () {
    return `new AndRight(${this.premises[0].reconstructor()}, ${this.premises[1].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.premiseFormulaIndex1}, ${this.premiseFormulaIndex2}, ${this.conclusionFormulaIndex})`
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

    if (deepEqual(new Implies(f1, f2), conclusion.precedents[conclusionFormulaIndex])) {
      this.premiseFormulaIndex1 = premiseFormulaIndex1
      this.premiseFormulaIndex2 = premiseFormulaIndex2
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }

  reconstructor () {
    return `new ImpliesLeft(${this.premises[0].reconstructor()}, ${this.premises[1].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.premiseFormulaIndex1}, ${this.premiseFormulaIndex2}, ${this.conclusionFormulaIndex})`
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

  reconstructor () {
    return `new ImpliesRight(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.premiseFormulaIndex1}, ${this.premiseFormulaIndex2}, ${this.conclusionFormulaIndex})`
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

  reconstructor () {
    return `new OrLeft(${this.premises[0].reconstructor()}, ${this.premises[1].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.premiseFormulaIndex1}, ${this.premiseFormulaIndex2}, ${this.conclusionFormulaIndex})`
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

  reconstructor () {
    return `new OrRight(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.premiseFormulaIndex1}, ${this.premiseFormulaIndex2}, ${this.conclusionFormulaIndex})`
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

  reconstructor () {
    return `new NotLeft(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.premiseFormulaIndex}, ${this.conclusionFormulaIndex})`
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

  reconstructor () {
    return `new NotRight(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.premiseFormulaIndex}, ${this.conclusionFormulaIndex})`
  }
}

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

    if (deepEqual(f2.one.subst(f2.v, t), f1)) {
      this.premiseFormulaIndex = premiseFormulaIndex
      this.conclusionFormulaIndex = conclusionFormulaIndex
      this.t = t
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }

  reconstructor () {
    return `new ForallLeft(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.premiseFormulaIndex}, ${this.conclusionFormulaIndex}, ${this.t.reconstructor()})`
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

    if (deepEqual(f2.one.subst(f2.v, y), f1)) {
      this.premiseFormulaIndex = premiseFormulaIndex
      this.conclusionFormulaIndex = conclusionFormulaIndex
      this.y = y
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }

  reconstructor () {
    return `new ForallRight(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.premiseFormulaIndex}, ${this.conclusionFormulaIndex}, ${this.y.reconstructor()})`
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

    if (deepEqual(f2.one.subst(f2.v, y), f1)) {
      this.premiseFormulaIndex = premiseFormulaIndex
      this.conclusionFormulaIndex = conclusionFormulaIndex
      this.y = y
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }

  reconstructor () {
    return `new ExistsLeft(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.premiseFormulaIndex}, ${this.conclusionFormulaIndex}, ${this.y.reconstructor()})`
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

    if (deepEqual(f2.one.subst(f2.v, t), f1)) {
      this.premiseFormulaIndex = premiseFormulaIndex
      this.conclusionFormulaIndex = conclusionFormulaIndex
      this.t = t
    } else {
      throw new TypeError('Not the right kind of formula at index')
    }
  }

  reconstructor () {
    return `new ExistsRight(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.premiseFormulaIndex}, ${this.conclusionFormulaIndex}, ${this.t.reconstructor()})`
  }
}

class Cut extends LKProofTree {
  constructor (premise1, premise2, conclusion) {
    super([premise1, premise2], conclusion)
    this.unicodeName = 'Cut'
    this.latexName = '\\textrm{Cut}'
  }

  reconstructor () {
    return `new Cut(${this.premises[0].reconstructor()}, ${this.premises[1].reconstructor()}, ${this.conclusion.reconstructor()})`
  }
}

/*
  Γ ⊢ Δ
  −−−−−−−−− W_L
  Γ, F ⊢ Δ
*/
class WeakeningLeft extends LKProofTree {
  constructor (premise, conclusion, conclusionFormulaIndex) {
    super([premise], conclusion)
    this.unicodeName = 'Weak-L'
    this.latexName = '\\textrm{Weak}_L'

    if (conclusion.precedents[conclusionFormulaIndex] instanceof Formula) {
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not an LK formula at index')
    }
  }

  reconstructor () {
    return `new WeakeningLeft(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.conclusionFormulaIndex})`
  }
}

/*
  Γ ⊢ Δ
  −−−−−−−−− W_R
  Γ ⊢ Δ, F
*/
class WeakeningRight extends LKProofTree {
  constructor (premise, conclusion, conclusionFormulaIndex) {
    super([premise], conclusion)
    this.unicodeName = 'Weak-R'
    this.latexName = '\\textrm{Weak}_R'

    if (conclusion.antecedents[conclusionFormulaIndex] instanceof Formula) {
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not an LK formula at index')
    }
  }

  reconstructor () {
    return `new WeakeningRight(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.conclusionFormulaIndex})`
  }
}

/*
  −−−−−−−−−-- C_L
  Γ, F, F ⊢ Δ
  Γ, F ⊢ Δ
*/
class ContractionLeft extends LKProofTree {
  constructor (premise, conclusion, conclusionFormulaIndex) {
    super([premise], conclusion)
    this.unicodeName = 'Cont-L'
    this.latexName = '\\textrm{Cont}_L'

    if (conclusion.precedents[conclusionFormulaIndex] instanceof Formula) {
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not an LK formula at index')
    }
  }

  reconstructor () {
    return `new ContractionLeft(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.conclusionFormulaIndex})`
  }
}

/*
  Γ ⊢ Δ, F, F
  −−−−−−−−−-- C_R
  Γ ⊢ Δ, F
*/
class ContractionRight extends LKProofTree {
  constructor (premise, conclusion, conclusionFormulaIndex) {
    super([premise], conclusion)
    this.unicodeName = 'Cont-L'
    this.latexName = '\\textrm{Cont}_L'

    if (conclusion.antecedents[conclusionFormulaIndex] instanceof Formula) {
      this.conclusionFormulaIndex = conclusionFormulaIndex
    } else {
      throw new TypeError('Not an LK formula at index')
    }
  }

  reconstructor () {
    return `new ContractionRight(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()}, ${this.conclusionFormulaIndex})`
  }
}


class Z3Rule extends LKProofTree {
  constructor (conclusion) {
    super([], conclusion)
    this.conclusion = conclusion
    this.isLeft = false
    this.isRight = false
    this.connective = null
    this.unicodeName = 'Z3'
    this.latexName = 'Z3'
    this.z3Response = "checking"

    checkWithZ3(conclusion, result => {
      this.z3Response = result
      if(!result) {
        console.log(result);
        modalWarning("Z3 says no!")
        // throw new TypeError('Z3 does not accept this sequent!')
      }

      // FIXME
      canvas.forEachObject(function (obj) {
        canvas.remove(obj)
      })
      proofs.map(p => p.proof.draw())

    })
  }

  reconstructor () {
    return `new Z3Rule(${this.conclusion.reconstructor()})`
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

  reconstructor () {
    if (this.completer) {
      return this.completer.reconstructor()
    } else {
      return `new LKIncomplete(${this.conclusion.reconstructor()})`
    }
  }
}

// End of LK rules

class AddTerms extends TermFun {
  constructor (first, second) {
    // parent constructor will throw error if arguments are not terms
    super('+', [first, second])
    this.first = first
    this.second = second
    this.primitive = true
  }

  subst (v, term) {
    return new AddTerms(
      this.first.subst(v, term),
      this.second.subst(v, term))
  }

  unicode () { return `${this.first.punicode()} + ${this.second.punicode()}` }
  latex () { return `${this.first.platex()} + ${this.second.platex()}` }
  reconstructor () {
    return `new AddTerms(${this.first.reconstructor()}, ${this.second.reconstructor()})`
  }
}

class SubtractTerms extends TermFun {
  constructor (first, second) {
    // parent constructor will throw error if arguments are not terms
    super('-', [first, second])
    this.first = first
    this.second = second
    this.primitive = true
  }

  subst (v, term) {
    return new SubtractTerms(
      this.first.subst(v, term),
      this.second.subst(v, term))
  }

  unicode () { return `${this.first.punicode()} - ${this.second.punicode()}` }
  latex () { return `${this.first.platex()} - ${this.second.platex()}` }
  reconstructor () {
    return `new SubtractTerms(${this.first.reconstructor()}, ${this.second.reconstructor()})`
  }
}

class MultiplyTerms extends TermFun {
  constructor (first, second) {
    // parent constructor will throw error if arguments are not terms
    super('*', [first, second])
    this.first = first
    this.second = second
    this.primitive = true
  }

  subst (v, term) {
    return new MultiplyTerms(
      this.first.subst(v, term),
      this.second.subst(v, term))
  }

  unicode () { return `${this.first.punicode()} * ${this.second.punicode()}` }
  latex () { return `${this.first.platex()} * ${this.second.platex()}` }
  reconstructor () {
    return `new MultiplyTerms(${this.first.reconstructor()}, ${this.second.reconstructor()})`
  }
}

class DivideTerms extends TermFun {
  constructor (first, second) {
    // parent constructor will throw error if arguments are not terms
    super('/', [first, second])
    this.first = first
    this.second = second
    this.primitive = true
  }

  subst (v, term) {
    return new DivideTerms(
      this.first.subst(v, term),
      this.second.subst(v, term))
  }

  unicode () { return `${this.first.punicode()} / ${this.second.punicode()}` }
  latex () { return `${this.first.platex()} / ${this.second.platex()}` }
  reconstructor () {
    return `new DivideTerms(${this.first.reconstructor()}, ${this.second.reconstructor()})`
  }
}

class LessThan extends Relation {
  constructor (lhs, rhs) {
    // parent constructor will throw error if arguments are not terms
    super('<', [lhs, rhs])
    this.lhs = lhs
    this.rhs = rhs
    this.primitive = true
  }

  subst (v, term) {
    return new LessThan(
      this.lhs.subst(v, term),
      this.rhs.subst(v, term))
  }

  unicode () { return `${this.lhs.unicode()} < ${this.rhs.unicode()}` }
  latex () { return `${this.lhs.latex()} < ${this.rhs.latex()}` }
  reconstructor () {
    return `new LessThan(${this.lhs.reconstructor()}, ${this.rhs.reconstructor()})`
  }
}

class GreaterThan extends Relation {
  constructor (lhs, rhs) {
    // parent constructor will throw error if arguments are not terms
    super('>', [lhs, rhs])
    this.lhs = lhs
    this.rhs = rhs
    this.primitive = true
  }

  subst (v, term) {
    return new GreaterThan(
      this.lhs.subst(v, term),
      this.rhs.subst(v, term))
  }

  unicode () { return `${this.lhs.unicode()} > ${this.rhs.unicode()}` }
  latex () { return `${this.lhs.latex()} > ${this.rhs.latex()}` }
  reconstructor () {
    return `new GreaterThan(${this.lhs.reconstructor()}, ${this.rhs.reconstructor()})`
  }
}

class LeqThan extends Relation {
  constructor (lhs, rhs) {
    // parent constructor will throw error if arguments are not terms
    super('<=', [lhs, rhs])
    this.lhs = lhs
    this.rhs = rhs
    this.primitive = true
  }

  subst (v, term) {
    return new LeqThan(
      this.lhs.subst(v, term),
      this.rhs.subst(v, term))
  }

  unicode () { return `${this.lhs.unicode()} ≤ ${this.rhs.unicode()}` }
  latex () { return `${this.lhs.latex()} \\leq ${this.rhs.latex()}` }
  reconstructor () {
    return `new LeqThan(${this.lhs.reconstructor()}, ${this.rhs.reconstructor()})`
  }
}

class GeqThan extends Relation {
  constructor (lhs, rhs) {
    // parent constructor will throw error if arguments are not terms
    super('>=', [lhs, rhs])
    this.lhs = lhs
    this.rhs = rhs
    this.primitive = true
  }

  subst (v, term) {
    return new GeqThan(
      this.lhs.subst(v, term),
      this.rhs.subst(v, term))
  }

  unicode () { return `${this.lhs.unicode()} ≥ ${this.rhs.unicode()}` }
  latex () { return `${this.lhs.latex()} \\geq ${this.rhs.latex()}` }
  reconstructor () {
    return `new GeqThan(${this.lhs.reconstructor()}, ${this.rhs.reconstructor()})`
  }
}

class Equal extends Relation {
  constructor (lhs, rhs) {
    // parent constructor will throw error if arguments are not terms
    super('=', [lhs, rhs])
    this.lhs = lhs
    this.rhs = rhs
    this.primitive = true
  }

  subst (v, term) {
    return new Equal(
      this.lhs.subst(v, term),
      this.rhs.subst(v, term))
  }

  unicode () { return `${this.lhs.unicode()} = ${this.rhs.unicode()}` }
  latex () { return `${this.lhs.latex()} = ${this.rhs.latex()}` }
  reconstructor () {
    return `new Equal(${this.lhs.reconstructor()}, ${this.rhs.reconstructor()})`
  }
}

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
  reconstructor () {
    return `new CmdAssign(${this.v.reconstructor()}, ${this.t.reconstructor()})`
  }
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
  reconstructor () {
    return `new CmdSeq(${this.first.reconstructor()}, ${this.second.reconstructor()})`
  }
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
  reconstructor () {
    return `new CmdIf(${this.condition.reconstructor()}, ${this.btrue.reconstructor()}, ${this.bfalse.reconstructor()})`
  }
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
  reconstructor () {
    return `new CmdWhile(${this.condition.reconstructor()}, ${this.body.reconstructor()})`
  }
}

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
    return `\\vdash \\{${this.pre.latex()}\\} \\; ${this.command.latex()} \\; \\{${this.post.latex()}\\}`
  }

  reconstructor () {
    return `new HoareTriple(${this.pre.reconstructor()}, ${this.command.reconstructor()}, ${this.post.reconstructor()})`
  }
}

class HoareProofTree extends ProofTree {
  constructor (premises, conclusion) {
    super()
    if (premises.length === 0 && conclusion == null) {
      this.premises = []
      this.conclusion = null
    } else if (arrayOf(premises, ProofTree) && conclusion instanceof HoareTriple) {
      this.premises = premises
      this.conclusion = conclusion
    } else {
      throw new TypeError('HoareProofTree must have proof trees and a Hoare triple')
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
\\UnaryInfC{$${this.conclusion.latex()}$}`
      case 2:
        return `${this.premises[0].latex()}
${this.premises[1].latex()}
${rule}
\\BinaryInfC{$${this.conclusion.latex()}$}`
      case 3:
        return `${this.premises[0].latex()}
${this.premises[1].latex()}
${this.premises[2].latex()}
${rule}
\\TrinaryInfC{$${this.conclusion.latex()}$}`
      default:
        throw new TypeError(`Don't know how to typeset a judgment with ${this.premises.length} premises`)
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

  reconstructor () {
    return `new Assignment(${this.conclusion.reconstructor()})`
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

  reconstructor () {
    return `new Sequencing(${this.premises[0].reconstructor()}, ${this.premises[1].reconstructor()}, ${this.conclusion.reconstructor()})`
  }
}

/*
  F ⊢ F'    ⊢ {F'} S {G'}    G' ⊢ G
  −−−−−−−−−−−−---------------------- CONS
            ⊢ {F} S {G}
*/
class Consequence extends HoareProofTree {
  constructor (premise1, premise2, premise3, conclusion) {
    super([premise1, premise2, premise3], conclusion)
    if (arrayOf([premise1, premise3], LKProofTree)) {
      this.command = conclusion.command
      this.unicodeName = 'CONS'
      this.latexName = 'CONS'
    } else {
      throw new TypeError('First and last premise must be LK proof trees')
    }

    // checks for the consequence rule
    if (!(deepEqual(premise2.conclusion.command, conclusion.command) &&
          premise1.conclusion.precedents.length === 1 &&
          premise1.conclusion.antecedents.length === 1 &&
          premise3.conclusion.precedents.length === 1 &&
          premise3.conclusion.antecedents.length === 1 &&
          deepEqual(premise1.conclusion.precedents[0], conclusion.pre) &&
          deepEqual(premise3.conclusion.antecedents[0], conclusion.post) &&
          deepEqual(premise1.conclusion.antecedents[0], premise2.conclusion.pre) &&
          deepEqual(premise3.conclusion.precedents[0], premise2.conclusion.post))) {
      throw new TypeError("Commands and conditions don't match up")
    }
  }

  reconstructor () {
    return `new Consequence(${this.premises[0].reconstructor()}, ${this.premises[1].reconstructor()}, ${this.premises[2].reconstructor()}, ${this.conclusion.reconstructor()})`
  }
}

/*
  ⊢ {F} S {G'}     G' ⊢ G
  −−−−−−−−−−−−----------- CONS*1
        ⊢ {F} S {G}
*/
class ConsequenceNoPre extends HoareProofTree {
  constructor (premise2, premise3, conclusion) {
    super([premise2, premise3], conclusion)
    if (arrayOf([premise3], LKProofTree)) {
      this.command = conclusion.command
      this.unicodeName = 'CONS*'
      this.latexName = 'CONS*'
    } else {
      throw new TypeError('The last premise must be an LK proof tree')
    }

    // checks for the consequence rule
    if (!(deepEqual(premise2.conclusion.command, conclusion.command) &&
          premise3.conclusion.precedents.length === 1 &&
          premise3.conclusion.antecedents.length === 1 &&
          deepEqual(premise2.conclusion.pre, conclusion.pre) && // shortened
          deepEqual(premise3.conclusion.antecedents[0], conclusion.post) &&
          deepEqual(premise3.conclusion.precedents[0], premise2.conclusion.post))) {
      throw new TypeError("Commands and conditions don't match up")
    }
  }

  reconstructor () {
    return `new ConsequenceNoPre(${this.premises[0].reconstructor()}, ${this.premises[1].reconstructor()}, ${this.conclusion.reconstructor()})`
  }
}

/*
  F ⊢ F'     ⊢ {F'} S {G}
  −−−−−−−−−−−−----------- CONS*2
      ⊢ {F} S {G}
*/
class ConsequenceNoPost extends HoareProofTree {
  constructor (premise1, premise2, conclusion) {
    super([premise1, premise2], conclusion)
    if (arrayOf([premise1], LKProofTree)) {
      this.command = conclusion.command
      this.unicodeName = 'CONS*'
      this.latexName = 'CONS*'
    } else {
      throw new TypeError('The first premise must be an LK proof tree')
    }

    if (!(deepEqual(premise2.conclusion.command, conclusion.command) &&
          premise1.conclusion.precedents.length === 1 &&
          premise1.conclusion.antecedents.length === 1 &&
          deepEqual(premise2.conclusion.post, conclusion.post) && // shortened
          deepEqual(premise1.conclusion.precedents[0], conclusion.pre) &&
          deepEqual(premise1.conclusion.antecedents[0], premise2.conclusion.pre))) {
      throw new TypeError("Commands and conditions don't match up")
    }
  }

  reconstructor () {
    return `new ConsequenceNoPost(${this.premises[0].reconstructor()}, ${this.premises[1].reconstructor()}, ${this.conclusion.reconstructor()})`
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

  reconstructor () {
    return `new Conditional(${this.premises[0].reconstructor()}, ${this.premises[1].reconstructor()}, ${this.conclusion.reconstructor()})`
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

  reconstructor () {
    return `new Loop(${this.premises[0].reconstructor()}, ${this.conclusion.reconstructor()})`
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

  reconstructor () {
    if (this.completer) {
      return this.completer.reconstructor()
    } else {
      return `new HoareIncomplete(${this.conclusion.reconstructor()})`
    }
  }
}

// If a tree is set as toDelete, delete the tree and its premises
// If an incomplete tree has a completer, remove the incomplete tree
const reorganizeTree = (tree) => {
  if (!tree instanceof ProofTree) {
    throw new TypeError(`Can't reorganize non-tree structures`)
  } else if (tree.toDelete && tree instanceof LKProofTree) {
    return new LKIncomplete(tree.conclusion)
  } else if (tree.toDelete && tree instanceof HoareProofTree) {
    return new HoareIncomplete(tree.conclusion)
  } else if (tree.completer && (tree instanceof LKIncomplete || tree instanceof HoareIncomplete)) {
    return reorganizeTree(tree.completer)
  } else {
    tree.premises = tree.premises.map(reorganizeTree)
    return tree
  }
}

const fillIncompleteByIndex = (tree, toComplete, i) => {
  const aux = (tree, toComplete, i) => {
    if (!tree instanceof ProofTree) {
      throw new TypeError(`Can't reorganize non-tree structures`)
    } else if (tree instanceof LKIncomplete || tree instanceof HoareIncomplete) {
      if (tree.completer || !deepEqual(tree.conclusion, toComplete.conclusion)) {
        return { t: tree, i: i }
      } else {
        return { t: (i === 0) ? toComplete : tree, i: i - 1 }
      }
    } else {
      let j = i
      tree.premises = tree.premises.map(p => { let o = aux(p, toComplete, j); j = o.i; return o.t})
      return { t: tree, i: j }
    }
  }
  return aux(tree, toComplete, i).t
}

const connectives = {
  "AndLeft": "∧",
  "OrLeft": "∨",
  "NotLeft": "¬",
  "ImpliesLeft": "⇒",
  "FalsityLeft": "⊥",
  "ForallLeft": "∀",
  "ExistsLeft": "∃",
  "AndRight": "∧",
  "OrRight": "∨",
  "NotRight": "¬",
  "ImpliesRight": "⇒",
  "TruthRight": "⊤",
  "ForallRight": "∀",
  "ExistsRight": "∃"
}
const commands = {
  "CmdAssign": "assignment",
  "CmdSeq": "sequencing",
  "CmdIf": "conditional",
  "CmdWhile": "loop"
}
