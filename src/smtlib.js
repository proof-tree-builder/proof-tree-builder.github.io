const generateSmtlib = sequent => {
  let s = new Set()
  sequent.getFreePropVars().forEach(fv => {
    s.add(`(declare-const ${fv.v} Bool)`)
  })
  sequent.getFreeTermVars().forEach(fv => {
    s.add(`(declare-const ${fv.v} Int)`)
  })
  sequent.getRelations().forEach(rel => {
    if(rel.primitive) { return }
    const args = Array(rel.args.length).fill('Int').join(' ')
    s.add(`(declare-fun ${rel.name}_${rel.args.length} (${args}) Bool)`)
  })
  sequent.getFunctions().forEach(fun => {
    if(fun.primitive) { return }
    const args = Array(fun.args.length).fill('Int').join(' ')
    s.add(`(declare-fun ${fun.name}_${fun.args.length} (${args}) Int)`)
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
