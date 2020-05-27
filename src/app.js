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
  canvas.forEachObject(function (obj) {
    if (!obj.root) return
    if (obj.root == pf) canvas.remove(obj)
  })
  proofs.splice(i, 1)
  refreshList()
}

const refreshList = () => {
  let ol = document.querySelector('#left-bar ol')
  ol.innerHTML = ''
  proofs.forEach((entry, i) => {
    ol.innerHTML += `<li value="${i}">
                        ${entry.proof.conclusion.unicode()}
                        <br>
                        <button onclick="javascript:giveLatex(${i})">LaTeX</button>
                        <button onclick="javascript:removeProof(${i})">Delete</button>
                     </li>`
  })
}

const addProof = (pf) => {
  proofs.push({ proof: pf, x: window.innerWidth / 2 - 100, y: window.innerHeight / 2 })
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

document.getElementById('help').addEventListener('click', () => {
  modalTextWindow(
  `<p>
    <strong>Proof Tree Builder</strong> is a web-based graphical interactive proof assistant for sequent calculus (LK) and Hoare logic.
  </p>
  <br>
  <p>
    You can click the "Add LK goal" button to add a new sequent calculus goal to prove. 
  </p>
  <p>
    You can use <code>&&</code> for conjunction, <code>||</code> for disjunction, <code>=></code> for implication, <code>!</code> for negation. <code>exists</code> and <code>forall</code> for quantification.
  </p>
  <p>
    For relations, use the syntax <code>P(x, y)</code>, where <code>P</code> is the relation and <code>x</code> and <code>y</code> are the terms in the relation. There are some primitive relations such as <code>=</code>, <code>&lt;</code>, <code>&gt;</code>, <code>&le;</code> and <code>&ge;</code>.
  </p>
  <p>
    For functions, use the syntax <code>f(x, y)</code>, where <code>f</code> is the function and <code>x</code> and <code>y</code> are the terms in the function. There are some primitive functions such as <code>+</code>, <code>-</code>, <code>*</code> and <code>/</code>.
  </p>
  <p>
    Other kinds of terms are term variables and integers. However <code>-x</code> is not an integer, it should be written as <code>-1 * x</code>.
  </p>
  <p>
    Any sequent pretty printed by the app can also be parsed back in. Here are some examples of how to write sequents for the app:
  </p>
  <p>
    <ul class="help-examples">
    <li><code>|- p => q => r => p && q && r</code></li>
    <li><code>exists x. g(x) |- exists y. g(y)</code></li>
    <li><code>exists x. g(k,x) |- exists y. g(k,y)</code></li>
    <li><code>|- ((p => q) => p) -> p</code></li>
    <li><code>x > 1 |- x > 0</code></li>
    <li><code>|- (P(0) && (forall x. (P(x) => P(x + 1)))) => P(3)</code></li>
    </ul>
  </p>
  <br>
  <p>
    Or you can click the "Add Hoare logic goal" button to add a new Hoare triple, such as
  </p>
  <p>
    <ul class="help-examples">
      <li><code>{true} if true then x := 3 else x := 5 {x = 3}</code></li>
      <li><code>{true} if x < 0 then x := -1 * x else x := x {x >= 0}</code></li>
      <li><code>|- {0 <= n} (r := 0 ; i := 0) ; while i < n do (r := r + 2 ; i := i + 1) {r = 2 * n}</code></li>
    </ul>
  </p>
  <p>
    Our Hoare triples are based on a simple imperative language (SIL). 
    SIL has only 4 kinds of statements: 
    assignments <code>x := t</code> where <code>t</code> is a term, 
    conditionals <code>if c then s1 else s2</code> where <code>c</code> is a formula and <code>s1</code> and <code>s2</code> are statements,
    loops <code>while c do s</code> where <code>c</code> is a formula and <code>s</code> is a statement,
    and sequences <code>s1;s2</code> where <code>s1</code> and <code>s2</code> are statements.
  </p>
  <br>
  <p>
    You can click on the orange plus button to apply proof rules to incomplete proof trees, and click on the red minus button to unapply proof rules.
  </p>
  <br>
  <p>
    The proof assistant has two modes: automate and learn modes. Automate mode is the default, but you can switch to learn mode by click on the button on the top right corner. Automate mode hides most rules that obviously cannot be applied, and enables the Auto button for LK. Auto button runs a non-backtracking algorithm to automatically apply a bunch of proof rules, you might be surprised that it can make a lot of progress in your LK proofs. Learn mode shows all the rule buttons, but you have to figure out which rule you can apply. We think the learn mode is useful for students who are just getting into LK and Hoare logic, because they have to think more about why they are applying which rules, while the automate mode is useful for when you want to finish the proof faster.
  </p>
  <br>
  <p>
    The source code of the Proof Tree Builder can be found <a href="https://github.com/joom/proof-tree-builder" target="_blank">here</a>. Happy proof hacking!
  </p>`)
  document.querySelector('.modal-content').style = "font-size: 0.85em"
  let ex = document.querySelectorAll('ul.help-examples')
  Array.from(ex[0].children).forEach(li => {
    let but = toNodes(`<button>Try this!</button>`)[0]
    but.addEventListener('click', e => { 
      addProof(new LKIncomplete(peg.parse(li.children[0].innerText, { startRule: "Sequent" }) ))
      but.style.background = successColor
      but.innerText = "✓"
      but.disabled = true
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
    })
    li.appendChild(but)
  })
})

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
            canvas.forEachObject(function (obj) {
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

    deleteLabel.on('mousedown', async (e) => {
      const msg = `Are you sure you want to unapply the ${this.unicodeName} rule 
                   for the conclusion ${this.conclusion.unicode()} and the rules applied after/above?`
      if(await modalConfirm(msg)) {
        this.toDelete = true
        refreshAll()
      }
    })
  }

  ruleLabel.setPositionByOrigin(
    (new fabric.Point(15, 0)).add(line.getPointByOrigin('right', 'top'), 'left', 'top'))

  let groupImages
  if(deleteLabel) {
    deleteLabel.setPositionByOrigin(
      (new fabric.Point(15, 5)).add(ruleLabel.getPointByOrigin('right', 'top'), 'left', 'top'))
    groupImages = [premiseGroup, line, ruleLabel, deleteLabel, text]
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
  group.on('moved', e => {
    proofs.forEach((entry, i) => {
      if (root == entry.proof) {
        proofs[i].x = e.target.aCoords.bl.x
        proofs[i].y = e.target.aCoords.bl.y
      }
    })
  })
  return group
}

ProofTree.prototype.draw = function () {
  let i = this.image(this)
  canvas.add(i)
  proofs.forEach((entry) => {
    if (this == entry.proof) {
      i.setPositionByOrigin(new fabric.Point(entry.x, entry.y), 'left', 'bottom')
    } 
  })
  // i.center()
  i.setCoords()
  return i
}
