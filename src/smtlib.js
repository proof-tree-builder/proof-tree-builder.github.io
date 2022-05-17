const generateSmtlib = (sequent, hasBogus) => {
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
  return [`(reset)`,
          `(set-option :produce-models true)`,
          ...s, 
          `(assert (not ${sequent.smtlib()}))`,
  // the 2 lines below are based on a hack described in
  // https://github.com/cpitclaudel/z3.wasm/issues/2#issuecomment-832659189
  // don't know why this works
          hasBogus ? `(declare-fun __FORBIDDEN__ () Int)` : ``,
          hasBogus ? `(assert-soft (= __FORBIDDEN__ 10))` : ``,
          `(check-sat)`,
          `(get-model)`,
          `(exit)`
         ].join('\n')
}

let lastResult = ``
let isLoaded = false
const checkWithZ3 = (sequent, cb, hasBogus = false) => {
  lastResult = ``
  isLoaded = false
  let input = generateSmtlib(sequent, hasBogus)
  console.log(input);
  let args = ['-smt2', '-nw']
  verification_start = window.performance.now();
  postZ3Message(queries.VERIFY, { args: args, input: input });

  let wait = setInterval(() => { 
    if (isLoaded) { 
      clearInterval(wait) 
      if((/Failed to verify/).test(lastResult)) {
        if (hasBogus) {
          modalWarning(`<strong>Bug in the Z3 build:</strong> ${lastResult}`)
        } else {
          // HACK: run Z3 without the bogus assertion first, 
          // try again with it if you get an error
          checkWithZ3(sequent, cb, true) 
        }
        return
      }
      if((/sat\(model/).test(lastResult)) {
        let s = lastResult.substring(lastResult.indexOf("("))
        let p = parseSexpr(s).filter(x => x instanceof Array && !x.includes("__FORBIDDEN__"))
        console.log(lastResult);
        cb(false, p)
        return
      }
      cb((/unsat/).test(lastResult), [])
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
      setLoading(isLoaded ? "Getting data..." : "Downloading Z3...")
      break;
  case responses.READY:
      unsetLoading()
      break;
  case responses.STDOUT:
      setLoading("Getting output from Z3...")
      logOutput(payload);
      break;
  case responses.STDERR:
      setLoading("Encountered Z3 error...")
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
  worker = new window.Worker("/src/worker.js");
  worker.onmessage = onZ3Message;
}

// from https://rosettacode.org/wiki/S-expressions
const parseSexpr = function(arg) {
	var t = arg.match(/\s*("[^"]*"|\(|\)|"|[^\s()"]+)/g)
	for (var o, c=0, i=t.length-1; i>=0; i--) {
		var n, ti = t[i].trim()
		if (ti == '"') return
		else if (ti == '(') t[i]='[', c+=1
		else if (ti == ')') t[i]=']', c-=1
		else if ((n=+ti) == ti) t[i]=n
		else t[i] = '\'' + ti.replace('\'', '\\\'') + '\''
		if (i>0 && ti!=']' && t[i-1].trim()!='(' ) t.splice(i,0, ',')
		if (!c) if (!o) o=true; else return
	}
	return c ? undefined : eval(t.join(''))
}
