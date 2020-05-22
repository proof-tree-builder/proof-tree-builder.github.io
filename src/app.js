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

const setLoading = () => { document.getElementById("loading").style = "display: inline" }
const unsetLoading = () => { document.getElementById("loading").style = "display: none" }

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
  alert(`LaTeX output for the ${pf.conclusion.unicode()} proof tree is copied to the clipboard!`)
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

document.getElementById('addLKGoal').addEventListener('click', function () {
  let input = prompt('Enter a LK goal sequent:')
  if (input === null) { return }
  let parsed = peg.parse(input.trim(), { startRule: 'Sequent' })
  let tree = new LKIncomplete(parsed)
  addProof(tree)
})

document.getElementById('addHoareGoal').addEventListener('click', function () {
  let input = prompt('Enter a Hoare triple:')
  if (input === null) { return }
  let parsed = peg.parse(input.trim(), { startRule: 'HoareTriple' })
  let tree = new HoareIncomplete(parsed)
  addProof(tree)
})

ProofTree.prototype.image = function (root) {
  let premiseImages = this.premises.map(p => p.image(root))

  if (this.completer) {
    return this.completer.image(root)
  }
  let isIncomplete = this instanceof LKIncomplete || this instanceof HoareIncomplete

  
  let maxHeight = Math.max.apply(Math, premiseImages.map(image => image.height))
  premiseImages.forEach((image, i) => {
    // get max height of all premiseImages, 
    // then shift image to the bottom by the difference
    // also shift each to the right a bit for spacing
    if (i === 0) return

    let prev = premiseImages[i - 1]

    image.setPositionByOrigin(
      (new fabric.Point(80, maxHeight - image.height)).add(prev.getPointByOrigin('right', 'top')), 'left', 'top')
    premiseImages[i] = image
  })

  /* We have to do this separately afterwards because the way our rendering
     algorithm works makes every premise image depend on the previous one. */
  if(premiseImages.length > 0) {
    let diff = maxHeight - premiseImages[0].height
    premiseImages[0].setPositionByOrigin(
      premiseImages[0]
        .getPointByOrigin('left','top')
        .add(new fabric.Point(0, diff)), 'left', 'top')
  }

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

  // let newTextPt2 = (new fabric.Point(0, 20)).add(line.getPointByOrigin('center', 'bottom'))
  // text.setPositionByOrigin(newTextPt2)

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
                         <p>Left rules:</p>
                         <p>
                           <button value="AndLeft" class="invertible1">∧</button>
                           <button value="OrLeft" class="invertible2">∨</button>
                           <button value="NotLeft" class="invertible1">¬</button>
                           <button value="ImpliesLeft">⇒</button>
                           <button value="FalsityLeft" class="invertible0">⊥</button>
                           <button value="ForallLeft">∀</button>
                           <button value="ExistsLeft" class="invertible1">∃</button>
                         </p>
                         <p>Right rules:</p>
                         <p>
                           <button value="AndRight" class="invertible2">∧</button>
                           <button value="OrRight" class="invertible1">∨</button>
                           <button value="NotRight" class="invertible1">¬</button>
                           <button value="ImpliesRight" class="invertible1">⇒</button>
                           <button value="TruthRight" class="invertible0">⊤</button>
                           <button value="ForallRight" class="invertible1">∀</button>
                           <button value="ExistsRight">∃</button>
                         </p>
                         <p>Other rules:</p>
                         <p>
                           <button value="Identity" class="invertible0">Id</button>
                           <button value="Cut">Cut</button>
                           <button value="'WeakL'">WeakL</button>
                           <button value="'WeakR'">WeakR</button>
                           <button value="Z3Rule" class="solver">Z3</button>
                           <button value="'Auto'" class="solver">Auto</button>
                         </p>
                       </div>`)[0]

        if (isAutomateMode()) {
          let applicables = LKapplicable(this.conclusion).map(x => x.name)
          box.querySelectorAll('button').forEach(but => {
            if (but.value === "Z3Rule") { return }
            if (but.value === "'Auto'") { return }
            if (!applicables.includes(but.value)) { but.remove() }
          })
        }
      } else if (this instanceof HoareIncomplete) {
        box = toNodes(`<div id="hoareRuleSelection" class="ruleSelection">
                         <p>Rules:</p>
                         <p>
                           <button value="Assignment">Assn</button>
                           <button value="Sequencing">Seq</button>
                           <button value="Consequence">Cons</button>
                           <button value="Conditional">Cond</button>
                           <button value="Loop">Loop</button>
                         </p>
                       </div>`)[0]
      }
      box.style.top = `${e.pointer.y}px`
      box.style.left = `${e.pointer.x}px`
      box.style.visibility = 'visible'
      box.querySelectorAll('button').forEach(but => {
        but.addEventListener('click', e => {
          console.log(`${but.value} application for ${this.conclusion.unicode()}`)
          box.remove()
          let rule = eval(but.value)
          let updated
          if (this instanceof LKIncomplete) {
            if (rule === 'Auto') {
              updated = auto(this)
              if(updated === this) { return }
            } else if (rule === 'WeakL') {
              let t = prompt('Select a formula to drop:')
              if (t === null) { return }
              let parsed = peg.parse(t, { startRule: 'Formula' })
              this.conclusion.precedents = this.conclusion.precedents.filter(p => !deepEqual(p, parsed))
            } else if (rule === 'WeakR') {
              let t = prompt('Select a formula to drop:')
              if (t === null) { return }
              let parsed = peg.parse(t, { startRule: 'Formula' })
              this.conclusion.antecedents = this.conclusion.antecedents.filter(p => !deepEqual(p, parsed))
            } else if (rule === Cut) {
              let t = prompt('Enter the formula to prove:')
              if (t === null) { return }
              let parsed = peg.parse(t, { startRule: 'Formula' })
              updated = applyLK(this.conclusion, rule, parsed)
            } else if (rule === ForallLeft || rule === ExistsRight) {
              let t = prompt('Enter the term to substitute for the variable:')
              if (t === null) { return }
              let parsed = peg.parse(t, { startRule: 'Term' })
              updated = applyLK(this.conclusion, rule, parsed)
            } else if (rule === ForallRight || rule === ExistsLeft) {
              let t = prompt('Enter a fresh variable to substitute for the variable:')
              if (t === null) { return }
              let parsed = peg.parse(t, { startRule: 'Name' })
              updated = applyLK(this.conclusion, rule, new TermVar(parsed))
            } else {
              updated = applyLK(this.conclusion, rule)
            }
          } else if (this instanceof HoareIncomplete) {
            if (rule === Consequence) {
              let t1 = prompt('Enter the first middle formula for the consequence rule:')
              if (t1 === null) { return }
              let parsed1 = peg.parse(t1, { startRule: 'Formula' })
              let t2 = prompt('Enter the second middle formula for the consequence rule:')
              if (t2 === null) { return }
              let parsed2 = peg.parse(t2, { startRule: 'Formula' })
              updated = applyHoare(this.conclusion, rule, parsed1, parsed2)
            } else if (rule === Sequencing) {
              let t1 = prompt('Enter the middle formula for the sequencing rule:')
              if (t1 === null) { return }
              let parsed1 = peg.parse(t1, { startRule: 'Formula' })
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

    deleteLabel.on('mousedown', (e) => {
      if(confirm("Are you sure you want to unapply this rule and the rules applied after/above?")) {
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
