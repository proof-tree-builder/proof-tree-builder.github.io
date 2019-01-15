var proofs = []

var canvas = this.__canvas = new fabric.Canvas('c', {selection: false});
var ruleSelection = document.querySelector('#lkRuleSelection') //TODO
fabric.Object.prototype.transparentCorners = false;
canvas.setWidth(window.innerWidth)
canvas.setHeight(window.innerHeight)

var incompleteColor = '#FFA500'
var goodColor = 'black'

// Panning with ALT + drag
canvas.on('mouse:down', function(opt) {
  ruleSelection.style.visibility = 'hidden'
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
  proofs.forEach(pf => {
    ol.innerHTML += `<li>${pf.conclusion.unicode()}</li>`
  })
}

const addProof = (pf) => {
  proofs.push(pf)
  refreshList()
}

document.getElementById('addGoal').addEventListener("click", function() {
  var input = prompt("Enter a goal sequent:")
  var parsed = peg.parse(input, {startRule: "Sequent"})
  addProof(new LKIncomplete(parsed))
  proofs[proofs.length - 1].draw()
})


ProofTree.prototype.image = function() {
  var premiseImages = this.premises.map(p => p.image())

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
  } else {
    ruleLabel = new fabric.Text(this.unicodeName, {
      fontFamily: 'Helvetica',
      fontSize: 10,
      stroke: goodColor
    });
  }


  ruleLabel.on('mousedown', (e) => {
    console.log(e);
    ruleSelection.style.top = `${e.absolutePointer.y}px`
    ruleSelection.style.left = `${e.absolutePointer.x}px`
    ruleSelection.style.visibility = 'visible'
  })

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
  return group;
}

ProofTree.prototype.draw = function() {
  i = this.image()
  canvas.add(i)
  i.center();
}
