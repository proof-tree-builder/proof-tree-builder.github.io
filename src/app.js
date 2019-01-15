var proofs = []

var canvas = this.__canvas = new fabric.Canvas('c', {selection: false});
fabric.Object.prototype.transparentCorners = false;
canvas.setWidth(window.innerWidth)
canvas.setHeight(window.innerHeight)

var incompleteColor = '#FFA500'
var goodColor = 'black'

const toNodes = (html) => new DOMParser().parseFromString(html, 'text/html').body.childNodes

// Panning with ALT + drag
canvas.on('mouse:down', function(opt) {
  document.querySelectorAll('.ruleSelection').forEach(e => e.remove())

  var evt = opt.e;
  if (evt.altKey === true) {
    this.isDragging = true;
    this.selection = false;
    this.lastPosX = evt.clientX;
    this.lastPosY = evt.clientY;
  }
});
canvas.on('mouse:move', function(opt) {
  if (this.isDragging) {
    var e = opt.e;
    this.viewportTransform[4] += e.clientX - this.lastPosX;
    this.viewportTransform[5] += e.clientY - this.lastPosY;
    this.requestRenderAll();
    this.lastPosX = e.clientX;
    this.lastPosY = e.clientY;
  }
});
canvas.on('mouse:up', function(opt) {
  this.isDragging = false;
  this.selection = true;
});

// Zooming to the cursor
canvas.on('mouse:wheel', function(opt) {
  var delta = opt.e.deltaY;
  var pointer = canvas.getPointer(opt.e);
  var zoom = canvas.getZoom();
  zoom = zoom + delta/200;
  if (zoom > 20) zoom = 20;
  if (zoom < 0.01) zoom = 0.01;
  canvas.zoomToPoint({ x: opt.e.offsetX, y: opt.e.offsetY }, zoom);
  opt.e.preventDefault();
  opt.e.stopPropagation();
});

const refreshList = () => {
  var ol = document.querySelector("#left-bar ol")
  ol.innerHTML = ""
  proofs.forEach((entry, i) => {
    ol.innerHTML += `<li value="${i}">${entry.proof.conclusion.unicode()}</li>`
  })
}

const addProof = (pf) => {
  // proofs.push(pf)
  proofs.push({proof: pf})
  pf.draw()
  refreshList()
}

// const redrawAll = () => {
//   proofs.forEach
// }

document.getElementById('addLKGoal').addEventListener("click", function() {
  var input = prompt("Enter a LK goal sequent:")
  var parsed = peg.parse(input, {startRule: "Sequent"})
  var tree = new LKIncomplete(parsed)
  addProof(tree)
})

document.getElementById('addHoareGoal').addEventListener("click", function() {
  var input = prompt("Enter a Hoare logic goal sequent:")
  var parsed = peg.parse(input, {startRule: "HoareTriple"})
  var tree = new HoareIncomplete(parsed)
  addProof(tree)
})


ProofTree.prototype.image = function(root) {
  var premiseImages = this.premises.map(p => p.image(root))

  if (this.completer) {
    return this.completer.image(root)
  }
  var isIncomplete = this instanceof LKIncomplete

  premiseImages.forEach((image, i) => {
    if (i === 0) return;

    var prev = premiseImages[i - 1]

    image.setPositionByOrigin(
      (new fabric.Point(80, 0)).add(prev.getPointByOrigin("right", "top")), "left", "top")
    premiseImages[i] = image
  })

  var opt = {subTargetCheck: true}
  var premiseGroup = this.premises ? new fabric.Group(premiseImages, opt) : new fabric.Group([], opt)

  var text = new fabric.Text(this.conclusion.unicode(), {
    fontFamily: 'Helvetica',
    fontSize: 30
  });
  var newTextPt = (new fabric.Point(0, 40)).add(premiseGroup.getPointByOrigin("center", "bottom"))
  text.setPositionByOrigin(newTextPt)

  var p1 = (new fabric.Point(0, 0)).add(text.getPointByOrigin("left", "top"))
  var p2 = (new fabric.Point(0, 0)).add(text.getPointByOrigin("right", "top"))
  var line = new fabric.Line([ p1.x, p1.y, p2.x, p2.y ], {
                                fill: isIncomplete ? incompleteColor : goodColor,
                                stroke: isIncomplete ? incompleteColor : goodColor,
                                strokeWidth: 2,
                                selectable: false,
                              })

  var ruleLabel
  if (isIncomplete) {
    ruleLabel = new fabric.Text(" + ", {
      fontFamily: 'Helvetica',
      fontSize: 11,
      stroke: 'white',
      backgroundColor: incompleteColor
    });

    ruleLabel.on('mousedown', (e) => {
      var box = toNodes(`<div id="lkRuleSelection" class="ruleSelection">
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
                          </p>
                        </div>`)[0]
      box.style.top = `${e.pointer.y}px`
      box.style.left = `${e.pointer.x}px`
      box.style.visibility = 'visible'
      box.querySelectorAll('button').forEach(but => {
        but.addEventListener('click', e => {
          console.log(`${but.value} application for ${this.conclusion.unicode()}`);
          box.remove()
          var rule = eval(but.value)
          var updated = applyLK(this.conclusion, rule)
          this.completer = updated

          var entry = proofs.find(entry => root == entry.proof)
          canvas.forEachObject(function(obj){
            if(!obj.root) return
            if(obj.root == root) canvas.remove(obj)
          });
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
    });
  }




  ruleLabel.setPositionByOrigin(
    (new fabric.Point(15, 0)).add(line.getPointByOrigin("right", "top"), "left", "top"))

  var group = new fabric.Group([premiseGroup, line, ruleLabel, text], {selectable: true, subTargetCheck: true});

  // group.on('selected', () => {
  //   console.log(ruleLabel);
  //   canvas.setActiveObject(group);
  // })


  group.lockRotation = true;
  group.lockScalingX = true;
  group.lockScalingY = true;
  group.hasControls = false;
  group.set({borderColor: 'black'})
  group.root = root
  return group;
}

ProofTree.prototype.draw = function() {
  i = this.image(this)
  canvas.add(i)
  i.center();
  return i
}
