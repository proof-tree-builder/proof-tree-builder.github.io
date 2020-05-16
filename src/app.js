let proofs = []

let canvas = this.__canvas = new fabric.Canvas('c', { selection: false })
fabric.Object.prototype.transparentCorners = false
canvas.setWidth(window.innerWidth)
canvas.setHeight(window.innerHeight)

let incompleteColor = '#FFA500'
let goodColor = 'black'

const isLearnMode = () => document.getElementById('mode').checked
const isAutomateMode = () => !document.getElementById('mode').checked

const toNodes = (html) => new DOMParser().parseFromString(html, 'text/html').body.childNodes

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
  // proofs.push(pf)
  proofs.push({ proof: pf })
  pf.draw()
  refreshList()
}

// const redrawAll = () => {
//   proofs.forEach
// }

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

  let opt = { subTargetCheck: true }
  let premiseGroup = this.premises ? new fabric.Group(premiseImages, opt) : new fabric.Group([], opt)

  let text = new fabric.Text(this.conclusion.unicode(), {
    fontFamily: 'Helvetica',
    fontSize: 30
  })
  let newTextPt = (new fabric.Point(0, 40)).add(premiseGroup.getPointByOrigin('center', 'bottom'))
  text.setPositionByOrigin(newTextPt)

  let p1 = (new fabric.Point(0, 0)).add(text.getPointByOrigin('left', 'top'))
  let p2 = (new fabric.Point(0, 0)).add(text.getPointByOrigin('right', 'top'))
  let line = new fabric.Line([ p1.x, p1.y, p2.x, p2.y ], {
    fill: isIncomplete ? incompleteColor : goodColor,
    stroke: isIncomplete ? incompleteColor : goodColor,
    strokeWidth: 2,
    selectable: false
  })

  let ruleLabel
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
                           <button value="AndLeft">∧</button>
                           <button value="OrLeft">∨</button>
                           <button value="ImpliesLeft">⇒</button>
                           <button value="FalsityLeft">⊥</button>
                           <button value="ForallLeft">∀</button>
                           <button value="ExistsLeft">∃</button>
                         </p>
                         <p>Right rules:</p>
                         <p>
                           <button value="AndRight">∧</button>
                           <button value="OrRight">∨</button>
                           <button value="ImpliesRight">⇒</button>
                           <button value="TruthRight">⊤</button>
                           <button value="ForallRight">∀</button>
                           <button value="ExistsRight">∃</button>
                         </p>
                         <p>Other rules:</p>
                         <p>
                           <button value="Identity">Id</button>
                           <button value="CutOne">Cut</button>
                           <button value="'Weaken'">Weak</button>
                         </p>
                       </div>`)[0]

        if (isAutomateMode()) {
          let applicables = LKapplicable(this.conclusion).map(x => x.name)
          box.querySelectorAll('button').forEach(but => {
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
            if (rule === 'Weaken') {
              let t = prompt('Select a formula to drop:')
              if (t === null) { return }
              let parsed = peg.parse(t, { startRule: 'Formula' })
              this.conclusion.precedents = this.conclusion.precedents.filter(p => !deepEqual(p, parsed))
            } else if (rule === CutOne) {
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
            updated = applyHoare(this.conclusion, rule)
          }
          this.completer = updated

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
      stroke: goodColor
    })
  }

  ruleLabel.setPositionByOrigin(
    (new fabric.Point(15, 0)).add(line.getPointByOrigin('right', 'top'), 'left', 'top'))

  let group = new fabric.Group([premiseGroup, line, ruleLabel, text], { selectable: true, subTargetCheck: true })

  group.lockRotation = true
  group.lockScalingX = true
  group.lockScalingY = true
  group.hasControls = false
  group.set({ borderColor: 'black' })
  group.root = root
  return group
}

ProofTree.prototype.draw = function () {
  let i = this.image(this)
  canvas.add(i)
  i.center()
  return i
}
