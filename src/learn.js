// hint which rules are applicable (sequent calculus)

function LKapplicable (sequent) {
  let arr = []

  let lhs = sequent.precedents
  let rhs = sequent.antecedents

  // left rules: falsity, or, and, implies, not
  for (i = 0; i < lhs.length; i++) {
    // get formula
    let f = lhs[i]
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
    } else if (f instanceof Forall) {
      arr.push(ForallLeft)
    } else if (f instanceof Exists) {
      arr.push(ExistsLeft)
    }
  }

  // right rules: truth, or, and, implies, not
  for (i = 0; i < rhs.length; i++) {
    // get formula
    let f = rhs[i]
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
    } else if (f instanceof Forall) {
      arr.push(ForallRight)
    } else if (f instanceof Exists) {
      arr.push(ExistsRight)
    }
  }

  // other: identity
  for (i = 0; i < rhs.length; i++) {
    let formula = rhs[i]
    let found = false
    // if we find match, stop looking
    for (j = 0; j < lhs.length; j++) {
      if (deepEqual(formula, lhs[j])) {
        found = true
        break
      }
    }
    // if match found, can apply identity
    if (found) {
      arr.push(Identity)
    }
  }

  return arr
}
