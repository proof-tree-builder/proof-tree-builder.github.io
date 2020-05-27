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

let lastResult = ``
let isLoaded = false
const checkWithZ3 = (sequent, cb) => {
  lastResult = ``
  isLoaded = false
  let input = generateSmtlib(sequent)
  console.log(input);
  let args = ['-smt2']
  verification_start = window.performance.now();
  postZ3Message(queries.VERIFY, { args: args, input: input });

  let wait = setInterval(() => { 
    if (isLoaded) { 
      clearInterval(wait) 
      if((/Failed to verify/).test(lastResult)) {
        modalAlert(`<strong>Bug in the Z3 build:</strong> ${lastResult}`)
        return
      }
      cb((/unsat/).test(lastResult))
    } 
  }, 100)
}


// Worker stuff

let worker

const postZ3Message = (query, payload) => {
  // console.info("[Window] -> Z3 (" + query + "):", payload)
  worker.postMessage({ kind: query, payload: payload })
}

const verifyCurrentInput = () => {
}

const logOutput = (message) => {
  lastResult += message
}

const onZ3Message = (event) => {
  // console.info("Z3 -> [Window]:", event);
  var kind = event.data.kind;
  var payload = event.data.payload;
  switch (kind) {
  case responses.PROGRESS:
      setLoading()
      break;
  case responses.READY:
      unsetLoading()
      break;
  case responses.STDOUT:
      setLoading()
      logOutput(payload);
      break;
  case responses.STDERR:
      setLoading()
      logOutput(payload)
      break;
  case responses.VERIFICATION_COMPLETE:
      isLoaded = true
      unsetLoading()
      // var elapsed = Math.round(window.performance.now() - verification_start);
      // logOutput ("\n-- Verification complete (" + elapsed + "ms)");
      break;
  }
}

const setupZ3Worker = () => {
  worker = new window.Worker("worker.js");
  worker.onmessage = onZ3Message;
}
