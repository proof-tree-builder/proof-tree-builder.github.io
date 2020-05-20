const genFresh = (sequent) => {
  let letters = 'abcdefghijklmnopqrstuvwxyz'.split('').reverse()
  let free_vars = sequent.getFreeTermVars().map(x => x.v)
  for (let i = -1; true; ++i) {
    for (let x of letters) {
      let y = x + (i >= 0 ? i.toString() : '')
      if (!free_vars.includes(y))
        return new TermVar(y)
    }
  }
}

const auto = (tree) => {
  let applicable = LKapplicable(tree.conclusion)
  let invertible = [
    // 0 subgoals
    Identity, FalsityLeft, TruthRight, 
    // 1 subgoal
    NotLeft, NotRight,
    AndLeft, OrRight, ImpliesRight,
    ForallRight, ExistsLeft,
    // 2 subgoals
    AndRight, OrLeft,
  ]
  for (let r of invertible) {
    if (applicable.includes(r)) {
      let fresh_var = [ForallRight, ExistsLeft].includes(r) ? genFresh(tree.conclusion) : null
      let new_tree = applyLK(tree.conclusion, r, fresh_var, false)
      new_tree.premises = new_tree.premises.map(auto)
      return new_tree
    }
  }
  return tree
}

