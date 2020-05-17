const generateSmtlib = sequent => {
  let s = new Set()
  sequent.getFreePropVars().forEach(fv => {
    s.add(`(declare-const ${fv.v} Bool)`)
  })
  sequent.getFreeTermVars().forEach(fv => {
    s.add(`(declare-const ${fv.v} Int)`)
  })
  sequent.getRelations().forEach(rel => {
    s.add(`(declare-fun ${rel.name}_${rel.args.length} () Bool)`)
  })
  sequent.getFunctions().forEach(fun => {
    s.add(`(declare-fun ${fun.name}_${fun.args.length} () Int)`)
  })
  return [...s, 
         `(assert (not ${sequent.smtlib()}))`,
         `(check-sat)`,
         `(exit)`
         ].join('\n')
}

const checkWithZ3 = sequent => {
  let s = generateSmtlib(sequent)
  // TODO
  return
}
