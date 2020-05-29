let proofs = []

let canvas = this.__canvas = new fabric.Canvas('c', { selection: false })
fabric.Object.prototype.transparentCorners = false
canvas.setWidth(window.innerWidth)
canvas.setHeight(window.innerHeight)

let incompleteColor = '#FFA500'
let successColor = '#00CC84'
let failureColor = '#FF2500'
let goodColor = 'black'

const isLearnMode = () => document.getElementById('mode').checked
const isAutomateMode = () => !document.getElementById('mode').checked

const toNodes = (html) => new DOMParser().parseFromString(html, 'text/html').body.childNodes

const setLoading = (msg) => {
  document.getElementById("loading").style = "display: inline"
  document.getElementById("loadingMsg").innerHTML = msg
  document.getElementById("loadingMsg").style = "display: inline"
}
const unsetLoading = () => {
  document.getElementById("loading").style = "display: none"
  document.getElementById("loadingMsg").style = "display: none"
}
const promptTrim = (s) => {
  let x = prompt(s)
  if (x === null) {
    return null
  } else {
    return x.trim()
  }
}

// Panning with ALT + drag
canvas.on('mouse:down', function (opt) {
  document.querySelectorAll('.ruleSelection').forEach(e => e.remove())

  let evt = opt.e
  if (evt.altKey === true) {
    this.isDragging = true
    this.selection = false
    this.lastPosX = evt.clientX
    this.lastPosY = evt.clientY
  }
})
canvas.on('mouse:move', function (opt) {
  if (this.isDragging) {
    let e = opt.e
    this.viewportTransform[4] += e.clientX - this.lastPosX
    this.viewportTransform[5] += e.clientY - this.lastPosY
    this.requestRenderAll()
    this.lastPosX = e.clientX
    this.lastPosY = e.clientY
  }
})
canvas.on('mouse:up', function (opt) {
  this.isDragging = false
  this.selection = true
})

// Zooming to the cursor
canvas.on('mouse:wheel', function (opt) {
  let delta = opt.e.deltaY
  let pointer = canvas.getPointer(opt.e)
  let zoom = canvas.getZoom()
  zoom = zoom + delta / 200
  if (zoom > 20) zoom = 20
  if (zoom < 0.01) zoom = 0.01
  canvas.zoomToPoint({ x: opt.e.offsetX, y: opt.e.offsetY }, zoom)
  opt.e.preventDefault()
  opt.e.stopPropagation()
})

canvas.on('object:moving', function (opt) {
  if(opt.transform.action === "drag") {
    opt.target.opacity = 0.5
    opt.target.setCoords()
    proofs.forEach((entry, i) => {
      entry.incompletes.forEach(inc => {
        if (opt.target.root == entry.proof) { return }
        let collision = opt.target.intersectsWithObject(entry.image)
        if(collision) {
          opt.target.opacity = 0.8
          opt.target.set({ borderColor: incompleteColor })
          opt.target.set({ borderScaleFactor: 5 })
        } else {
          opt.target.set({ borderColor: 'black' })
          opt.target.set({ borderScaleFactor: 1 })
        }
      })
    })
  }
})
canvas.on('object:modified', function (opt) {
  opt.target.opacity = 1
  if(opt.transform.action === "drag") {
    opt.target.set({ borderColor: 'black' })
    opt.target.set({ borderScaleFactor: 1 })
    opt.target.setCoords()
    proofs.forEach(async (entry, i) => {
      if (opt.target.root == entry.proof) { return }
      const collision = opt.target.intersectsWithObject(entry.image)
      if (!collision) { return }
      console.log(`Found collision with ${opt.target.root.conclusion.unicode()}`)

      let choices = []
      entry.incompletes.forEach((inc, j) => {
        if(deepEqual(inc.tree.conclusion, opt.target.root.conclusion)) {
          choices.push(j)
        }
      })

      let toAttach
      if(choices.length === 1) {
        if (await modalConfirm(`Do you want to attach the proof tree you dragged to the incomplete goal of the tree you dragged it over?`, `Attach`, `Don't attach`)) {
          toAttach = 0
        }
      } else if(collision && choices.length > 1) {
        const choiceTexts = choices.map(j => entry.incompletes[j].tree.conclusion.unicode())

        toAttach = await modalRadio(`Do you want to attach the proof tree you dragged to the one of the incomplete goals of the tree you dragged it over? Please choose which one you want to attach to, ordered below left to right with respect to their places in the proof tree.`, choiceTexts, `Attach`, `Don't attach`)
      }

      if(Number.isInteger(toAttach)) {
        proofs[i].proof = fillIncompleteByIndex(proofs[i].proof, opt.target.root, toAttach)
        proofs.forEach((entry, k) => {
          if (opt.target.root == entry.proof) {
            removeProof(k)
            refreshList()
            redrawAll()
          }
        })
      }
    })
  }
})

const copyToClipboard = str => {
  const el = document.createElement('textarea')
  el.value = str
  document.body.appendChild(el)
  el.select()
  document.execCommand('copy')
  document.body.removeChild(el)
}

const giveLatex = i => {
  let pf = proofs[i].proof
  let code = pf.latex()
  copyToClipboard(code)
  modalAlert(`LaTeX output for the ${pf.conclusion.unicode()} proof tree is copied to the clipboard!`)
}

const removeProof = i => {
  let pf = proofs[i].proof
  canvas.forEachObject(obj => {
    if (!obj.root) return
    if (obj.root == pf) canvas.remove(obj)
  })
  proofs.splice(i, 1)
  refreshList()
}

const saveProof = i => {
  const goal = proofs[i].proof.conclusion.unicode().trim()
  const text = `/* Proof for ${goal} */\n${proofs[i].proof.reconstructor()}`
  var pom = document.createElement('a')
  pom.setAttribute('href', 'data:text/plain;charset=utf-8,' + encodeURIComponent(text))
  pom.setAttribute('download', `${goal}.proof`)
  pom.click()
};

const refreshList = () => {
  let ol = document.querySelector('#left-bar ol')
  ol.innerHTML = ''
  proofs.forEach((entry, i) => {
    ol.innerHTML += `<li value="${i}">
                        ${entry.proof.conclusion.unicode()}
                        <br>
                        <button onclick="javascript:giveLatex(${i})">LaTeX</button>
                        <button onclick="javascript:removeProof(${i})">✖ Delete</button>
                        <button onclick="javascript:saveProof(${i})">💾 Save</button>
                     </li>`
  })
}

const addProof = (pf) => {
  proofs.push({ proof: pf, x: null, y: null, incompletes: [] })
  pf.draw()
  refreshList()
}

const redrawAll = () => {
  canvas.forEachObject(obj => (canvas.remove(obj)))
  proofs.forEach(pf => { pf.proof.draw() })
}

const refreshAll = () => {
  proofs.forEach(pf => { pf.proof = reorganizeTree(pf.proof) })
  redrawAll()
}

document.getElementById('addLKGoal').addEventListener('click', async () => {
  addProof(new LKIncomplete(await modalSequentPrompt('Enter an LK goal sequent:')))
})

document.getElementById('addHoareGoal').addEventListener('click', async () => {
  addProof(new HoareIncomplete(await modalHoarePrompt('Enter a Hoare triple:')))
})

document.getElementById('loadProof').addEventListener('click', async () => {
  // eval is evil, but what can you do sometimes
  addProof(eval(await modalFilePrompt('Select the proof file you want to load into the proof assistant:')))
})

const help = () => {
  modalTextWindow(
  `
  <h2>What is this?</h2>
  <p>
    <strong>Proof Tree Builder</strong> is a web-based graphical proof assistant for sequent calculus (LK) and Hoare logic.
  </p>
  <br>
  <h2>Sequent calculus</h2>
  <p>
    You can click the "Add LK goal" button to add a new sequent calculus goal.
  </p>
  <p>
    You can use <code>&&</code> for conjunction, <code>||</code> for disjunction, <code>=></code> for implication, <code>!</code> for negation. <code>exists</code> and <code>forall</code> for quantification.
  </p>
  <p>
    Relations are written <code>P(x, y)</code>, where <code>P</code> is the relation name and <code>x</code> and <code>y</code> are the terms in the relation. There are some primitive relations such as <code>=</code>, <code>&lt;</code>, <code>&gt;</code>, <code>&le;</code> and <code>&ge;</code>. Primitive relations are written <code>x &lt; y</code>.
  </p>
  <p>
    Functions are written <code>f(x, y)</code>, where <code>f</code> is the function name and <code>x</code> and <code>y</code> are the terms in the function. There are some primitive functions such as <code>+</code>, <code>-</code>, <code>*</code> and <code>/</code>. Primitive functions are written <code>x + y</code>.
  </p>
  <p>
    Term variables like <code>x</code> and integers like <code>5</code> or <code>-5</code> are also terms. However <code>-x</code> is not parseable, it should be written as <code>-1 * x</code>.
  </p>
  <p>
    Any sequent pretty printed by the app can also be parsed back in. Here are some example sequents:
  </p>
  <p>
    <ul class="help-examples">
    <li><code>|- p => q => r => p && q && r</code></li>
    <li><code>exists x. P(x) |- exists y. P(y)</code></li>
    <li><code>exists x. P(k, x) |- exists y. P(k, y)</code></li>
    <li><code>|- ((p => q) => p) -> p</code></li>
    <li><code>x > 1 |- x > 0</code></li>
    <li><code>|- (P(0) && (forall x. (P(x) => P(x + 1)))) => P(3)</code></li>
    </ul>
  </p>
  <p><button id="showLKRules">Show LK rules</button></p>
  <div id="LKRules" style="display: none">
    <p><img src="./rules/propositional.png"></p>
    <p><img src="./rules/firstOrder.png"></p>
  </div>
  <br>
  <h2>Hoare logic</h2>
  <p>
    You can click the "Add Hoare logic goal" button to add a new Hoare triple, such as
  </p>
  <p>
    <ul class="help-examples">
      <li><code>{true} if true then x := 3 else x := 5 {x = 3}</code></li>
      <li><code>{true} if x < 0 then x := -1 * x else x := x {x >= 0}</code></li>
      <li><code>{0 <= n} (r := 0; i := 0); while i < n do (r := r+2; i := i+1) {r = 2*n}</code></li>
    </ul>
  </p>
  <br>
  <p>
    Our Hoare triples are based on a simple imperative language (SIL). 
    SIL has only 4 kinds of statements: 
    <ul class="help-list">
    <li>assignments <code>x := t</code> where <code>t</code> is a term</li>
    <li>conditionals <code>if c then s1 else s2</code> where <code>c</code> is a formula and <code>s1</code> and <code>s2</code> are statements</li>
    <li>loops <code>while c do s</code> where <code>c</code> is a formula and <code>s</code> is a statement</li>
    <li>and sequences <code>s1 ; s2</code> where <code>s1</code> and <code>s2</code> are statements.</li>
    </ul>
  </p>
  <p><button id="showHoareRules">Show Hoare logic rules</button></p>
  <div id="HoareRules" style="display: none">
    <p><img src="./rules/hoare.png"></p>
  </div>
  <br>
  <h2>General usage</h2>
  <p>
    You can click on the <span style="color: ${incompleteColor}">orange</span> plus buttons next to incomplete proof trees, then choose a proof rules to apply. 
  </p>
  <p>
    You can click on the <span style="color: ${failureColor}">red</span> minus button to unapply proof rules that are already applied.
  </p>
  <p>
You can click on the <span style="color: ${incompleteColor}">orange</span> scissors button (✄) to <strong>detach</strong> a proof, i.e. to create a separate proof tree with the current branch and changing the original one into an incomplete one. You can also <strong>attach</strong> a separate proof on another one by <strong>dragging</strong> the subtree and <strong>dropping</strong> on the main one.
  </p>
  <p>
    As you work on the proof, you can click on the buttons on the left bar to either copy the LaTeX output for a given proof, or to save that proof onto your computer as a file. You can later reload the proof file into the proof assistant by clicking the "Load proof file" button on the top bar.
  </p>
  <br>
  <h3>Modes of usage</h3>
  <p>
  The proof assistant has two modes: <strong>automate</strong> and <strong>learn</strong> mode. Automate mode is the default, but you can switch to learn mode by click on the button on the top right corner. Automate mode hides most rules that obviously cannot be applied, and enables the Auto button for LK. Auto button runs a non-backtracking algorithm to automatically apply a bunch of proof rules, you might be surprised that it can make a lot of progress in your LK proofs.
  </p>
  <p>
    Learn mode shows all the rule buttons, but you have to figure out which rule you can apply. We think the learn mode is useful for students who are just getting into LK and Hoare logic, because they have to think more about why they are applying which rules, while the automate mode is useful for when you want to finish the proof faster.
  </p>
  <br>
  <h3>Z3 support</h3>
  <p>
    The proof assistant currently cannot evaluate functions or relations. For example, if there is a term <code>1 + 1</code>, it will get stuck, it will not evaluate to <code>2</code>. Therefore you cannot prove <code>P(1 + 1) |- P(2)</code> by normal proof rules. For these cases, you can use the <strong>Z3</strong> pseudo-rule. This rule runs the Z3 theorem prover in the background to check if the goal is valid. You can also use this rule for other logical goals you do not want to write the full proof for, but still want to check. 
  </p>
  <p>
    If Z3 finds the goal to be valid, it will draw a <span style="color: ${successColor}">green</span> line over it. If Z3 finds the goal to be not valid, it will draw a <span style="color: ${failureColor}">red</span> line over it.
  </p>
  <p>
    Remember that while our proof assistant does not assume the law of excluded middle (P ∨ ¬ P), Z3 does! So there might be goals that our proof assistant cannot prove on purpose, but Z3 will say yes to them.
  </p>
  <br>
  <p>
    Happy proof hacking!
  </p>
  <br>
  <small>
    The source code of the Proof Tree Builder can be found <a href="https://github.com/joom/proof-tree-builder" target="_blank">here</a>.<br>
    Proof Tree Builder is developed by Joomy Korkut, Anastasiya Kravchuk-Kirilyuk and John Li. 2018-2020.
  </small>`)
  let ex = document.querySelectorAll('ul.help-examples')
  Array.from(ex[0].children).forEach(li => {
    let but = toNodes(`<button>Try this!</button>`)[0]
    but.addEventListener('click', e => { 
      addProof(new LKIncomplete(peg.parse(li.children[0].innerText, { startRule: "Sequent" }) ))
      but.style.background = successColor
      but.innerText = "✓"
      but.disabled = true
      setTimeout(() => { document.querySelector('.modal').remove() }, 500)
    })
    li.appendChild(but)
  })
  Array.from(ex[1].children).forEach(li => {
    let but = toNodes(`<button>Try this!</button>`)[0]
    but.addEventListener('click', e => { 
      addProof(new HoareIncomplete(peg.parse(li.children[0].innerText, { startRule: "HoareTriple" }) ))
      but.style.background = successColor
      but.innerText = "✓"
      but.disabled = true
      setTimeout(() => { document.querySelector('.modal').remove() }, 500)
    })
    li.appendChild(but)
  })
  document.querySelector('#showLKRules').onclick = e => {
    let x = document.querySelector('#LKRules')
    x.style.display = x.style.display !== "none" ? "none" : "block"
  }
  document.querySelector('#showHoareRules').onclick = e => {
    let x = document.querySelector('#HoareRules')
    x.style.display = x.style.display !== "none" ? "none" : "block"
  }
}
document.getElementById('help').addEventListener('click', help)

ProofTree.prototype.image = function (root) {
  let premiseImages = this.premises.map(p => p.image(root))

  if (this.completer) {
    return this.completer.image(root)
  }
  let isIncomplete = this instanceof LKIncomplete || this instanceof HoareIncomplete

  
  premiseImages.forEach((image, i) => {
    if (i === 0) return

    let prev = premiseImages[i - 1]
    image.setPositionByOrigin(
      (new fabric.Point(80, 0)).add(prev.getPointByOrigin('right', 'bottom')), 'left', 'bottom')
    premiseImages[i] = image
  })

  let opt = { subTargetCheck: true }
  let premiseGroup = this.premises ? new fabric.Group(premiseImages, opt) : new fabric.Group([], opt)

  let text = new fabric.Text(this.conclusion.unicode(), {
    fontFamily: 'Helvetica',
    fontSize: 30
  })
  let newTextPt = (new fabric.Point(0, 30)).add(premiseGroup.getPointByOrigin('center', 'bottom'))
  text.setPositionByOrigin(newTextPt)


  let color = goodColor
  if(isIncomplete) {
    color = incompleteColor
  }
  if(this instanceof Z3Rule) {
    if(this.z3Response === true) {
      color = successColor
    } else if(this.z3Response === false) {
      color = failureColor
    } else {
      color = incompleteColor
    }
  }

  // line length should be the max of premise image conclusion text width and conclusion width
  let premiseTexts = premiseImages.map(g => {
    let l = g.getObjects()
    let o = l[l.length - 1]
    let point = { x: -o.width/2, y: o.height/2 };
    let pointOnCanvas = fabric.util.transformPoint(point, o.calcTransformMatrix())
    return {left: pointOnCanvas.x, right: pointOnCanvas.x + o.width}
  })
  let x1 = Math.min.apply(Math, premiseTexts.map(t => t.left))
  let x2 = Math.max.apply(Math, premiseTexts.map(t => t.right))
  let p1 = (new fabric.Point(0, 0)).add(text.getPointByOrigin('left', 'top'))
  let p2 = (new fabric.Point(0, 0)).add(text.getPointByOrigin('right', 'top'))

  let linex1
  let linex2
  if(x2 - x1 > p2.x - p1.x) {
    // if the premises are wider than the conclusion text
    linex1 = x1
    linex2 = x2
  } else {
    // if the conclusion text is wider than the premises
    linex1 = p1.x
    linex2 = p2.x
  }

  let line = new fabric.Line([ linex1, p1.y - 5, linex2, p2.y - 5], {
    fill: color,
    stroke: color,
    strokeWidth: 2,
    selectable: false
  })

  // TODO for centering the text along the rule line:
  let newTextPt2 = (new fabric.Point(0, 20)).add(line.getPointByOrigin('center', 'bottom'))
  text.setPositionByOrigin(newTextPt2)

  let ruleLabel = null
  let deleteLabel = null
  let detachLabel = null
  if (isIncomplete) {
    ruleLabel = new fabric.Text(' + ', {
      fontFamily: 'Helvetica',
      fontSize: 11,
      stroke: 'white',
      backgroundColor: incompleteColor
    })

    ruleLabel.on('mousedown', (e) => {
      let box
      if (this instanceof LKIncomplete) {
        box = toNodes(`<div id="lkRuleSelection" class="ruleSelection">
                         <p>Left connective rules:</p>
                         <p>
                           <button value="AndLeft">∧</button>
                           <button value="OrLeft">∨</button>
                           <button value="NotLeft">¬</button>
                           <button value="ImpliesLeft">⇒</button>
                           <button value="FalsityLeft">⊥</button>
                           <button value="ForallLeft">∀</button>
                           <button value="ExistsLeft">∃</button>
                         </p>
                         <p>Right connective rules:</p>
                         <p>
                           <button value="AndRight">∧</button>
                           <button value="OrRight">∨</button>
                           <button value="NotRight">¬</button>
                           <button value="ImpliesRight">⇒</button>
                           <button value="TruthRight">⊤</button>
                           <button value="ForallRight">∀</button>
                           <button value="ExistsRight">∃</button>
                         </p>
                         <p>Structural rules:</p>
                         <p class="text-rules">
                           <button value="WeakeningLeft">Weak-L</button>
                           <button value="WeakeningRight">Weak-R</button>
                           <button value="ContractionLeft">Cont-L</button>
                           <button value="ContractionRight">Cont-R</button>
                         </p>
                         <p>Other rules:</p>
                         <p class="text-rules">
                           <button value="Identity">Id</button>
                           <button value="Cut">Cut</button>
                           <button value="Z3Rule" class="solver">Z3</button>
                           <button value="'Auto'" class="solver">Auto</button>
                         </p>
                       </div>`)[0]

        if (isAutomateMode()) {
          let applicables = applicableLK(this.conclusion).map(x => x.name)
          box.querySelectorAll('button').forEach(but => {
            if (but.value === "Z3Rule") { return }
            if (but.value === "WeakeningLeft") { return }
            if (but.value === "WeakeningRight") { return }
            if (but.value === "ContractionLeft") { return }
            if (but.value === "ContractionRight") { return }
            if (but.value === "'Auto'") { return }
            if (!applicables.includes(but.value)) { but.remove() }
          })
        } else {
          box.querySelectorAll('button').forEach(but => {
            if (but.value === "'Auto'") { but.remove() }
          })
        }
      } else if (this instanceof HoareIncomplete) {
        box = toNodes(`<div class="ruleSelection">
                         <p>Command rules:</p>
                         <p class="text-rules">
                           <button value="Assignment">Assn</button>
                           <button value="Sequencing">Seq</button>
                           <button value="Conditional">Cond</button>
                           <button value="Loop">Loop</button>
                         </p>
                         <p>Logical rules:</p>
                         <p class="text-rules">
                           <button value="Consequence">Cons</button>
                         </p>
                       </div>`)[0]
        if (isAutomateMode()) {
          let applicables = applicableHoare(this.conclusion).map(x => x.name)
          box.querySelectorAll('button').forEach(but => {
            if (!applicables.includes(but.value)) { but.remove() }
          })
        }
      }
      box.style.top = `${e.pointer.y}px`
      box.style.left = `${e.pointer.x}px`
      box.style.visibility = 'visible'
      box.querySelectorAll('button').forEach(but => {
        but.addEventListener('click', async e => {
          console.log(`${but.value} application for ${this.conclusion.unicode()}`)
          box.remove()
          try {
            let rule = eval(but.value)
            let updated
            if (this instanceof LKIncomplete) {
              if (rule === 'Auto') {
                updated = await auto(this)
                if(updated === this) { return }
              } else if (rule === WeakeningLeft) {
                const i = await modalRadio('For weakening, select a formula from the left side to drop:', this.conclusion.precedents.map(x => x.unicode()))
                updated = await applyLK(this.conclusion, rule, i)
              } else if (rule === WeakeningRight) {
                const i = await modalRadio('For weakening, select a formula from the right side to drop:', this.conclusion.antecedents.map(x => x.unicode()))
                updated = await applyLK(this.conclusion, rule, i)
              } else if (rule === ContractionLeft) {
                const i = await modalRadio('For contraction, select a formula from the left side to repeat:', this.conclusion.precedents.map(x => x.unicode()))
                updated = await applyLK(this.conclusion, rule, i)
              } else if (rule === ContractionRight) {
                const i = await modalRadio('For contraction, select a formula from the right side to repeat:', this.conclusion.antecedents.map(x => x.unicode()))
                updated = await applyLK(this.conclusion, rule, i)
              } else if (rule === Cut) {
                const parsed = await modalFormulaPrompt('Enter the formula to prove:')
                updated = await applyLK(this.conclusion, rule, parsed)
              } else if (rule === ForallLeft || rule === ExistsRight) {
                const parsed = await modalTermPrompt('Enter the term to substitute for the variable:')
                updated = await applyLK(this.conclusion, rule, parsed)
              } else if (rule === ForallRight || rule === ExistsLeft) {
                const parsed = await modalNamePrompt('Enter a fresh variable to substitute for the variable:')
                updated = await applyLK(this.conclusion, rule, new TermVar(parsed))
              } else {
                updated = await applyLK(this.conclusion, rule)
              }
            } else if (this instanceof HoareIncomplete) {
              if (rule === Consequence) {
                const parsed1 = await modalFormulaPromptDefault(
                    `Enter the first middle formula for the consequence rule: <br>
                    (leave it blank if it is the same as the precondition ${this.conclusion.pre.unicode()})`, this.conclusion.pre)
                const parsed2 = await modalFormulaPromptDefault(
                    `Enter the second middle formula for the consequence rule: <br>
                    (leave it blank if it is the same as the postcondition ${this.conclusion.post.unicode()})`, this.conclusion.post)
                updated = applyHoare(this.conclusion, rule, parsed1, parsed2)
              } else if (rule === Sequencing) {
                const parsed = await modalFormulaPrompt('Enter the middle formula to prove:')
                updated = applyHoare(this.conclusion, rule, parsed1)
              } else {
                updated = applyHoare(this.conclusion, rule)
              }
            }
            if (updated !== null) this.completer = updated

            let entry = proofs.find(entry => root == entry.proof)
            canvas.forEachObject(obj => {
              if (!obj.root) return
              if (obj.root == root) canvas.remove(obj)
            })
            entry.proof.draw()
          } catch(err) {
            modalAlert(`Rule not applicable!`)
            // TODO better error messages
            console.log(err.message);
            console.log(err);
          }
        })
      })
      document.body.appendChild(box)
    })
  } else {
    ruleLabel = new fabric.Text(this.unicodeName, {
      fontFamily: 'Helvetica',
      fontSize: 10,
      stroke: color
    })

    deleteLabel = new fabric.Text(' - ', {
      fontFamily: 'Helvetica',
      fontSize: 11,
      stroke: 'white',
      backgroundColor: failureColor
    })

    detachLabel = new fabric.Text('✄', {
      fontFamily: 'Helvetica',
      fontSize: 11,
      stroke: 'white',
      backgroundColor: incompleteColor
    })

    deleteLabel.on('mousedown', async (e) => {
      const msg = `Are you sure you want to <strong>unapply</strong> the ${this.unicodeName} rule
                   for the conclusion <br>${this.conclusion.unicode()}<br> and the rules applied after/above?`
      if(await modalConfirm(msg)) {
        this.toDelete = true
        refreshAll()
      }
    })

    detachLabel.on('mousedown', async (e) => {
      const msg = `Are you sure you want to <strong>detach</strong> the proof at the ${this.unicodeName} rule
                   for the conclusion <br>${this.conclusion.unicode()} ?<br>
                   This will unapply the ${this.unicodeName} rule in the current proof tree, and also will create an extra proof tree with the ${this.unicodeName} rule at the bottom, followed by the rest of this branch of the proof tree.`
      if(await modalConfirm(msg)) {
        let deepCopy = eval(this.reconstructor())
        addProof(deepCopy)
        this.toDelete = true
        refreshAll()
      }
    })
  }

  ruleLabel.setPositionByOrigin(
    (new fabric.Point(15, 0)).add(line.getPointByOrigin('right', 'top'), 'left', 'top'))

  let groupImages
  if(deleteLabel && detachLabel) {
    deleteLabel.setPositionByOrigin(
      (new fabric.Point(15, 5)).add(ruleLabel.getPointByOrigin('right', 'top'), 'left', 'top'))
    detachLabel.setPositionByOrigin(
      (new fabric.Point(30, 5)).add(ruleLabel.getPointByOrigin('right', 'top'), 'left', 'top'))
    groupImages = [premiseGroup, line, ruleLabel, deleteLabel, detachLabel, text]
  } else {
    groupImages = [premiseGroup, line, ruleLabel, text]
  }
  let group = new fabric.Group(groupImages, { selectable: true, subTargetCheck: true })

  group.lockRotation = true
  group.lockScalingX = true
  group.lockScalingY = true
  group.hasControls = false
  group.set({ borderColor: 'black' })
  group.root = root
  if (this == root) {
    group.on('moved', e => {
      proofs.forEach((entry, i) => {
        if (root == entry.proof) {
          proofs[i].x = e.target.aCoords.bl.x
          proofs[i].y = e.target.aCoords.bl.y
        }
      })
    })
  }

  if(isIncomplete) {
    proofs.forEach((entry, i) => {
      if (root == entry.proof) {
        proofs[i].incompletes.push({ image: group, tree: this })
      }
    })
  }
  return group
}

ProofTree.prototype.draw = function () {
  proofs.forEach((entry, i) => { if (this == entry.proof) proofs[i].incompletes = [] })
  let im = this.image(this)
  proofs.forEach((entry, i) => {
    if (this == entry.proof) {
      if(entry.x == null || entry.y == null) {
        proofs[i].x = (window.innerWidth - im.width) / 2
        proofs[i].y = (window.innerHeight + im.height) / 2
      }
      im.setPositionByOrigin(new fabric.Point(proofs[i].x, proofs[i].y), 'left', 'bottom')
      proofs[i].image = im
    }
  })
  im.setCoords()
  canvas.add(im)
  return im
}
