// hint which rules are applicable (sequent calculus)

const applicableLK = (sequent) => {
  let arr = []

  let lhs = sequent.precedents
  let rhs = sequent.antecedents

  // left rules: falsity, or, and, implies, not
  for (i = 0; i < lhs.length; i++) {
    // get formula
    let f = lhs[i]
    // add rule to list
    if (f instanceof Truth) {
      arr.push({name: "'WeakL'"})
    } else if (f instanceof Falsity) {
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
    } else if (f instanceof Falsity) {
      arr.push({name: "'WeakR'"})
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

  // Can always apply cut rule
  arr.push(Cut)

  return arr
}

const applicableHoare = (hoareTriple) => {
  let arr = []
  if (hoareTriple.command instanceof CmdAssign) {
    arr.push(Assignment)
  } else if (hoareTriple.command instanceof CmdSeq) {
    arr.push(Sequencing)
  } else if (hoareTriple.command instanceof CmdIf) {
    arr.push(Conditional)
  } else if (hoareTriple.command instanceof CmdWhile) {
    arr.push(Loop)
  }

  // Can always apply cut rule
  arr.push(Consequence)
  return arr
}

/*

Color code rules in decreasing order of safety

(1) Rules that immediately solve the goal

  Assumption


    ———————— Identity
    Γ, A ⊢ A

  Truth values

     
    ———————— FalsityLeft
    Γ, ⊥ ⊢ Δ


    ———————— TruthRight
    Γ ⊢ T, Δ

(2) Invertible rules that produce 1 subgoal

  Truth values

     Γ ⊢ Δ
    ———————— WeakL
    Γ, T ⊢ Δ

     Γ ⊢ Δ
    ———————— WeakR
    Γ ⊢ ⊥, Δ

  Negation

     Γ ⊢ A, Δ
    —————————— NotLeft
    Γ, ¬ A ⊢ Δ

     Γ, A ⊢ Δ
    —————————— NotRight
    Γ, ⊢ ¬ A, Δ

  Conjunction

    Γ, A, B ⊢ Δ
    ———————————— AndLeft
    Γ, A ∧ B ⊢ Δ

  Disjunction

    Γ ⊢ Δ, A, B
    ———————————— OrRight
    Γ ⊢ Δ, A ∨ B

  Implication

    Γ, A ⊢ B, Δ
    ———————————— ImpliesRight
    Γ ⊢ A → B, Δ

  Forall

    Γ ⊢ P[y/x], Δ
    ————————————— (y fresh) ForallRight
    Γ ⊢ ∀ x. P, Δ

  Exists

    Γ, P[y/x] ⊢ Δ
    ————————————— (y fresh) ExistsLeft
    Γ, ∃ x. P ⊢ Δ

(2) Invertible rules that produce 2 subgoals

  Conjunction

    Γ ⊢ A, Δ    Γ ⊢ B, Δ
    ———————————————————— AndRight
       Γ ⊢ A ∧ B, Δ

  Disjunction

    Γ, A ⊢ Δ    Γ, B ⊢ Δ
    ———————————————————— OrLeft
       Γ, A ∨ B ⊢ Δ

*/
