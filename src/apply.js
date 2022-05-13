/* `uservar` is a field used for the cut rule and forall and exists quantifier rules.
   In the former case it is a `Formula`; in the latter it is a `TermVar` that we use in 
   the application of the rule. */
const applyLK = async (sequent, rule, uservar, strict=true) => {
  let lhs = sequent.precedents
  let rhs = sequent.antecedents

  if (rule === Cut) {
    if (!(uservar instanceof Formula)) throw new TypeError('Cut rule needs a Formula')
    let premise1 = new LKIncomplete(new Sequent(lhs, [uservar, ...rhs]))
    let premise2 = new LKIncomplete(new Sequent([...lhs, uservar], rhs))
    return new Cut(premise1, premise2, sequent)
  }
  if (rule === WeakeningLeft) {
    if (!(lhs[uservar] instanceof Formula)) throw new TypeError('WeakeningLeft rule needs a Formula')
    const newLhs = lhs.filter((p, i) => i !== uservar)
    let premise = new LKIncomplete(new Sequent(newLhs, rhs))
    return new WeakeningLeft(premise, sequent, uservar)
  }
  if (rule === WeakeningRight) {
    if (!(rhs[uservar] instanceof Formula)) throw new TypeError('WeakeningRight rule needs a Formula')
    const newRhs = rhs.filter((p, i) => i !== uservar)
    let premise = new LKIncomplete(new Sequent(lhs, newRhs))
    return new WeakeningRight(premise, sequent, uservar)
  }
  if (rule === ContractionLeft) {
    if (!(lhs[uservar] instanceof Formula)) throw new TypeError('ContractionLeft rule needs a Formula')
    const newLhs = lhs.filter((p, i) => i <= uservar).concat([lhs[uservar]]).concat(lhs.filter((p, i) => i > uservar))
    let premise = new LKIncomplete(new Sequent(newLhs, rhs))
    return new ContractionLeft(premise, sequent, uservar)
  }
  if (rule === ContractionRight) {
    if (!(rhs[uservar] instanceof Formula)) throw new TypeError('ContractionRight rule needs a Formula')
    const newRhs = rhs.filter((p, i) => i <= uservar).concat([rhs[uservar]]).concat(rhs.filter((p, i) => i > uservar))
    let premise = new LKIncomplete(new Sequent(lhs, newRhs))
    return new ContractionRight(premise, sequent, uservar)
  }

  // what kind of formula are we looking for
  let formula = Formula
  if (rule === NotLeft || rule === NotRight) {
    formula = Not
  } else if (rule === OrLeft || rule === OrRight) {
    formula = Or
  } else if (rule === AndLeft || rule === AndRight) {
    formula = And
  } else if (rule === ImpliesLeft || rule === ImpliesRight) {
    formula = Implies
  } else if (rule === TruthRight) {
    formula = Truth
  } else if (rule === FalsityLeft) {
    formula = Falsity
  } else if (rule === ForallLeft || rule === ForallRight) {
    formula = Forall
  } else if (rule === ExistsLeft || rule === ExistsRight) {
    formula = Exists
  }

  // if dealing with Left rules
  // or, and, implies, not, falsity, forall, exists
  if (rule.name.includes('Left')) {
    // get all applicable indices
    let indices = []
    for (let i = 0; i < lhs.length; i++) {
      if (lhs[i] instanceof formula) { indices.push(i) }
    }

    // if none, then can't apply rule
    if (indices.length == 0) {
      throw new Error(`There is no formula with the ${connectives[rule.name]} connective on the left hand side.`)
    }

    let idx
    // if more than one, ambiguous
    if (indices.length > 1 && strict) {
      let options = indices.map(index => lhs[index].unicode())
      const i = await modalRadio(`There are multiple formulas this rule could apply to. Please choose which one you mean.`, options) 
      idx = indices[i]
    } else {
      // this is the index
      idx = indices[0]
    }

    // CASE: FALSITY LEFT
    if (rule === FalsityLeft) {
      return new FalsityLeft(sequent, idx)

    // CASE: NOT
    } else if (rule === NotLeft) {
      // original NOT formula
      let og = lhs[idx]
      let inner = og.one
      // make shallow copies
      let plhs = lhs.slice()
      let prhs = rhs.slice()
      // remove NOT from lhs
      plhs.splice(idx, 1)
      // add formula to rhs
      prhs.unshift(inner)
      let premise = new LKIncomplete(new Sequent(plhs, prhs))
      return new NotLeft(premise, sequent, 0, idx)

    // CASE: OR
    } else if (rule === OrLeft) {
      // original OR formula
      let og = lhs[idx]
      // subformulas
      let left = og.left
      let right = og.right

      // make premise1
      let plhs1 = lhs.slice()
      delete plhs1[idx]
      plhs1[idx] = left
      let premise1 = new LKIncomplete(new Sequent(plhs1, rhs.slice()))

      // make premise2
      let plhs2 = lhs.slice()
      delete plhs2[idx]
      plhs2[idx] = right
      let premise2 = new LKIncomplete(new Sequent(plhs2, rhs.slice()))

      return new OrLeft(premise1, premise2, sequent, idx, idx, idx)

    // CASE: AND
    } else if (rule === AndLeft) {
      // original AND formula
      let og = lhs[idx]
      // subformulas
      let left = og.left
      let right = og.right

      // make premise
      let plhs = lhs.slice()
      //delete plhs[idx]
      plhs[idx] = right
      plhs.splice(idx, 0, left)
      let premise = new LKIncomplete(new Sequent(plhs, rhs.slice()))

      return new AndLeft(premise, sequent, idx, idx + 1, idx)
    } else if (rule === ImpliesLeft) {
      // original OR formula
      let og = lhs[idx]
      // subformulas
      let left = og.left
      let right = og.right

      // make premise1
      let plhs1 = lhs.slice()
      plhs1.splice(idx, 1)
      let prhs = rhs.slice()
      prhs.unshift(left)
      let premise1 = new LKIncomplete(new Sequent(plhs1, prhs))

      // make premise2
      let plhs2 = lhs.slice()
      delete plhs2[idx]
      plhs2[idx] = right
      let premise2 = new LKIncomplete(new Sequent(plhs2, rhs.slice()))

      return new ImpliesLeft(premise1, premise2, sequent, 0, idx, idx)
    } else if (rule === ForallLeft) {
      // original Forall formula
      let og = lhs[idx]
      // subformulas
      let v = og.v
      let body = og.one
      let newbody = body.subst(v, uservar)

      // make premise
      let plhs = lhs.slice()
      delete plhs[idx]
      plhs[idx] = newbody
      let premise = new LKIncomplete(new Sequent(plhs, rhs.slice()))

      return new ForallLeft(premise, sequent, idx, idx, uservar)
    } else if (rule === ExistsLeft) {
      if (sequent.getFreeTermVars().some(v => deepEqual(v, uservar))) {
        modalAlert(`${uservar.v} is not a free variable!`)
        return null
      }
      // original Exists formula
      let og = lhs[idx]
      // subformulas
      let v = og.v
      let body = og.one
      let newbody = body.subst(v, uservar)

      // make premise
      let plhs = lhs.slice()
      delete plhs[idx]
      plhs[idx] = newbody
      let premise = new LKIncomplete(new Sequent(plhs, rhs.slice()))

      return new ExistsLeft(premise, sequent, idx, idx, uservar)
    }
  }

  // if dealing with Right rules
  // or, and, implies, not, truth
  if (rule.name.includes('Right')) {
    // get all applicable indices
    let indices = []
    for (i = 0; i < rhs.length; i++) {
      if (rhs[i] instanceof formula) { indices.push(i) }
    }

    // if none, then can't apply rule
    if (indices.length == 0) {
      throw new Error(`There is no formula with the ${connectives[rule.name]} connective on the right hand side.`)
    }

    let idx
    // if more than one, ambiguous
    if (indices.length > 1 && strict) {
      let options = indices.map(index => rhs[index].unicode())
      const i = await modalRadio(`There are multiple formulas this rule could apply to. Please choose which one you mean.`, options) 
      idx = indices[i]
    } else {
      // this is the index
      idx = indices[0]
    }

    // CASE: TRUTH
    if (rule === TruthRight) {
      return new TruthRight(sequent, idx)

    // CASE: NOT
    } else if (rule === NotRight) {
      // original NOT formula
      let og = rhs[idx]
      let inner = og.one
      // make shallow copies
      let plhs = lhs.slice()
      let prhs = rhs.slice()
      // remove NOT from lhs
      prhs.splice(idx, 1)
      // add formula to rhs
      plhs.push(inner)
      let premise = new LKIncomplete(new Sequent(plhs, prhs))
      return new NotRight(premise, sequent, plhs.length - 1, idx)

    // CASE: OR
    } else if (rule === OrRight) {
      // original OR formula
      let og = rhs[idx]
      // subformulas
      let left = og.left
      let right = og.right

      // make premise
      let prhs = rhs.slice()
      //delete prhs[idx]
      prhs[idx] = right
      prhs.splice(idx, 0, left)
      let premise = new LKIncomplete(new Sequent(lhs.slice(), prhs))

      return new OrRight(premise, sequent, idx, idx + 1, idx)

    // CASE: AND
    } else if (rule === AndRight) {
      // original AND formula
      let og = rhs[idx]
      // subformulas
      let left = og.left
      let right = og.right

      // make premise1
      let prhs1 = rhs.slice()
      delete prhs1[idx]
      prhs1[idx] = left
      let premise1 = new LKIncomplete(new Sequent(lhs.slice(), prhs1))

      // make premise2
      let prhs2 = rhs.slice()
      delete prhs2[idx]
      prhs2[idx] = right
      premise2 = new LKIncomplete(new Sequent(lhs.slice(), prhs2))

      return new AndRight(premise1, premise2, sequent, idx, idx, idx)

    } else if (rule === ImpliesRight) {
      // original OR formula
      let og = rhs[idx]
      // subformulas
      let left = og.left
      let right = og.right

      // make premise1
      let plhs = lhs.slice()
      plhs.push(left)
      let prhs = rhs.slice()
      delete prhs[idx]
      prhs[idx] = right
      let premise = new LKIncomplete(new Sequent(plhs, prhs))

      return new ImpliesRight(premise, sequent, plhs.length - 1, idx, idx)

    } else if (rule === ForallRight) {
      if (sequent.getFreeTermVars().some(v => deepEqual(v, uservar))) {
        modalAlert(`${uservar.v} is not a free variable!`)
        return null
      }
      // original Forall formula
      let og = rhs[idx]
      // subformulas
      let v = og.v
      let body = og.one
      let newbody = body.subst(v, uservar)

      // make premise
      let prhs = rhs.slice()
      delete prhs[idx]
      prhs[idx] = newbody
      let premise = new LKIncomplete(new Sequent(lhs.slice(), prhs))

      return new ForallRight(premise, sequent, idx, idx, uservar)

    } else if (rule === ExistsRight) {
      // original Exists formula
      let og = rhs[idx]
      // subformulas
      let v = og.v
      let body = og.one
      let newbody = body.subst(v, uservar)

      // make premise
      let prhs = rhs.slice()
      delete prhs[idx]
      prhs[idx] = newbody
      let premise = new LKIncomplete(new Sequent(lhs.slice(), prhs))

      return new ExistsRight(premise, sequent, idx, idx, uservar)
    }
  }

  // if dealing with both sides
  // identity
  if(rule === Identity) {
    // at least one of the things on the right should be on the left
    let l = 0
    let r = 0
    const found = lhs.find((left, i) => {
      l = i
      return rhs.find((right, j) => {
        r = j
        return deepEqual(left, right)
      })
    })

    if(found) {
      return new Identity(sequent, l, r)
    } else {
      throw new Error('Rule not applicable.')
    }
  }

  if(rule === Z3Rule) {
    return new Z3Rule(sequent)
  }

  throw new Error('no such rule so far')
}

const applyHoare = (triple, rule, uservar, uservar2) => {
  let pre = triple.pre
  let command = triple.command
  let post = triple.post

  if (rule === Assignment) {
    let v = command.v
    let term = command.t

    if (!(command instanceof CmdAssign) ||
      !deepEqual(post.subst(v, term), pre)) {
      throw new Error('Rule not applicable.')
    }

    return new Assignment(triple)

  } else if (rule === Sequencing) {
    if (!(command instanceof CmdSeq)) {
      throw new Error('Rule not applicable.')
    }

    let first = command.first
    let second = command.second

    let premise1 = new HoareIncomplete(new HoareTriple(pre, first, uservar))
    let premise2 = new HoareIncomplete(new HoareTriple(uservar, second, post))

    return new Sequencing(premise1, premise2, triple)

  } else if (rule === Consequence) {
    let premise1 = new LKIncomplete(new Sequent([pre], [uservar]))
    let premise2 = new HoareIncomplete(new HoareTriple(uservar, command, uservar2))
    let premise3 = new LKIncomplete(new Sequent([uservar2], [post]))

    if(deepEqual(pre, uservar)) {
      return new ConsequenceNoPre(premise2, premise3, triple)
    } else if(deepEqual(uservar2, post)) {
      return new ConsequenceNoPost(premise1, premise2, triple)
    } else {
      return new Consequence(premise1, premise2, premise3, triple)
    }

  } else if (rule === Conditional) {
    if (!(command instanceof CmdIf)) {
      throw new Error('Rule not applicable.')
    }
    let c = command.condition
    let btrue = command.btrue
    let bfalse = command.bfalse

    let p1 = new And(pre, c)
    let p2 = new And(pre, new Not(c))

    let premise1 = new HoareIncomplete(new HoareTriple(p1, btrue, post))
    let premise2 = new HoareIncomplete(new HoareTriple(p2, bfalse, post))

    return new Conditional(premise1, premise2, triple)

  } else if (rule === Loop) {
    let c = command.condition
    let body = command.body

    if (!(command instanceof CmdWhile) &&
      !deepEqual(pre, new And(pre, new Not(c)))) {
      throw new Error('Rule not applicable.')
    }

    let p1 = new And(pre, c)
    let p2 = new And(pre, new Not(c))

    let premise = new HoareIncomplete(new HoareTriple(p1, body, pre))

    return new Loop(premise, triple)
  }

  throw new Error('No rule specified or rule does not exist.')
}
