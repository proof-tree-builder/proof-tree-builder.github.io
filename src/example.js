let p = new Var("p")

// Proving that p ⊢ p
let proofpp = new Identity(new Sequent([p],[p]), 0, 0)

let q = new Var("q")
let pq = new And(p, q)
let qp = new And(q, p)
let pq2qp = new Implies(pq, qp)

// let incomplete1 = new LKIncomplete(new Sequent([],[pq2qp]))
// incomplete1.draw()

// Proving that p,q ⊢ q
let pf1 = new Identity(new Sequent([p, q], [q]), 1, 0)
// Proving that p,q ⊢ p
let pf2 = new Identity(new Sequent([p, q], [p]), 0, 0)
// Proving that p,q ⊢ q ∧ p
let pf3 = new AndRight(pf1, pf2, new Sequent([p, q], [qp]), 0, 0, 0)
// Proving that p ∧ q ⊢ q ∧ p
let pf4 = new AndLeft(pf3, new Sequent([pq], [qp]), 0, 1, 0)
// Proving that ⊢ (p ∧ q) ⇒ (q ∧ p)
let pf5 = new ImpliesRight(pf4, new Sequent([], [pq2qp]), 0, 0, 0)

let pf5incomplete = new ImpliesRight(new LKIncomplete(new Sequent([pq], [qp])), new Sequent([], [pq2qp]), 0, 0, 0)

// addProof(pf5incomplete)
// pf5incomplete.draw()

let np = new Not(p)
let nnp = new Not(np)

let weakLEM = new Sequent([], [new Or(np, nnp)])

let pfWeakLEM =
  new OrRight(
    new NotRight(
      new Identity(new Sequent([np], [np]), 0, 0),
    new Sequent([], [np, nnp]), 0, 1),
  weakLEM, 0,1,0)

// automation tests

let pnp1 = new Sequent([p, np], [])
let pnp2 = new Sequent([], [p, np])
// pnp1.prove()

let forallx = peg.parse("forall x. f(x) |- f(1)", {startRule: "Sequent"})
let forallxi = new LKIncomplete(forallx)
// addProof(forallxi)

let existsx = peg.parse("exists x. g(x) |- exists y. g(y)", {startRule: "Sequent"})
let existsxi = new LKIncomplete(existsx)
addProof(existsxi)


let peirce = peg.parse("|- ((p -> q) -> p) -> p", {startRule: "Sequent"})
let peircei = new LKIncomplete(peirce)
// addProof(peircei)

let negh = peg.parse("{true} if x < 0 then x := -1 * x else x := x {x >= 0}", {startRule: "HoareTriple"})
let neghi = new HoareIncomplete(negh)
// addProof(neghi)


let mult = peg.parse("p && q, r && s |- p && s", {startRule: "Sequent"})
let multi = new LKIncomplete(mult)
// addProof(multi)
