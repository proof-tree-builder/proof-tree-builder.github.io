/*
Copyright (c) 2018 Clément Pit-Claudel

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

const makeWorker = (self, console, queries, responses, performance) => {
  let INPUT_FNAME = "input.smt2"

  let solver
  let ready = false

  const postMessage = (kind, payload) => {
    // console.info("Z3 -> Window (" + kind + "):", payload)
    self.postMessage({ kind: kind, payload: payload })
  }

  const runSolver = (input, args) => {
    if (!ready) {
      console.error("Cannot run SMT solver yet.")
      postMessage(responses.DONE, false)
c
    }

    args.push(INPUT_FNAME)
    // console.log("Running SMT solver with", args)
    solver.FS.writeFile(INPUT_FNAME, input, { encoding: "utf8" })
    solver.callMain(args)
    postMessage(responses.VERIFICATION_COMPLETE, true)
  }

  const progress = (message) => {
    postMessage(responses.PROGRESS, message)
    // console.info("Worker:", message, performance.now())
  }

  const onRuntimeInitialized = () => {
    ready = true
    progress("Done initializing SMT solver.")
    postMessage(responses.READY)
  }

  let STUB_MSG = "Calling stub instead of signal()"

  const postOutput = (channel, output) => {
    output = output.replace(STUB_MSG, "")
    if (output != "") {
      postMessage(channel, output)
    }
  }

  const loadSolver = () => {
    progress("Downloading SMT solver...")
    self.importScripts("z3w.js")
    progress("Initializing SMT solver...")
    solver = Z3({ ENVIRONMENT: "WORKER",
                  onRuntimeInitialized: onRuntimeInitialized,
                  print: function(message) { postOutput(responses.STDOUT, message) },
                  printErr: function(message) { postOutput(responses.STDERR, message) } })
  }

  const onMessage = (event) => {
    // console.info("Window -> Z3:", event)
    let kind = event.data.kind
    let payload = event.data.payload
    switch (kind) {
      case queries.VERIFY:
        runSolver(payload.input, payload.args)
        break
    }
  }

  const init = () => {
    loadSolver()
    self.onmessage = onMessage
  }

  return { init: init }
}

importScripts("./protocol.js")
makeWorker(self, console, queries, responses, performance).init()
