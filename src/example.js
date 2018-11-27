var p = new Var("p")

// Proving that p ⊢ p
var proofpp = new Identity(new Sequent([p],[p]), 0, 0)

var q = new Var("q")
var pq = new And(p, q)
var qp = new And(q, p)
var pq2qp = new Implies(pq, qp)

// Proving that p,q ⊢ q
var pf1 = new Identity(new Sequent([p, q], [q]), 1, 0)
// Proving that p,q ⊢ p
var pf2 = new Identity(new Sequent([p, q], [p]), 0, 0)
// Proving that p,q ⊢ q ∧ p
var pf3 = new AndRight(pf1, pf2, new Sequent([p, q], [qp]), 0, 0, 0)
// Proving that p ∧ q ⊢ q ∧ p
var pf4 = new AndLeft(pf3, new Sequent([pq], [qp]), 0, 1, 0)
// Proving that ⊢ (p ∧ q) ⇒ (q ∧ p)
var pf5 = new ImpliesRight(pf4, new Sequent([], [pq2qp]), 0, 0, 0)

pf5.draw()
