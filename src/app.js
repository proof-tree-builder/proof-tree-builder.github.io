var canvas = this.__canvas = new fabric.Canvas('c');
fabric.Object.prototype.transparentCorners = false;
canvas.setWidth(window.innerWidth)
canvas.setHeight(window.innerHeight)

// Panning with ALT + drag
canvas.on('mouse:down', function(opt) {
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


Judgment.prototype.image = function() {
  var premiseImages = this.premises.map(p => p.image())

  premiseImages.forEach((image, i) => {
    if (i === 0) return;

    var prev = premiseImages[i - 1]

    image.setPositionByOrigin(
      (new fabric.Point(80, 0)).add(prev.getPointByOrigin("right", "top")), "left", "top")
    premiseImages[i] = image
  })

  var premiseGroup = new fabric.Group(premiseImages)

  var text = new fabric.Text(this.conclusion.unicode(), {
    fontFamily: 'Helvetica',
    fontSize: 30
  });
  var newTextPt = (new fabric.Point(0, 40)).add(premiseGroup.getPointByOrigin("center", "bottom"))
  text.setPositionByOrigin(newTextPt)

  var p1 = (new fabric.Point(0, 0)).add(text.getPointByOrigin("left", "top"))
  var p2 = (new fabric.Point(0, 0)).add(text.getPointByOrigin("right", "top"))
  var line = new fabric.Line([ p1.x, p1.y, p2.x, p2.y ], {
                                fill: 'black',
                                stroke: 'black',
                                strokeWidth: 2,
                                selectable: false,
                              })

  var ruleLabel = new fabric.Text(this.unicodeName, {
    fontFamily: 'Helvetica',
    fontSize: 10
  });
  ruleLabel.setPositionByOrigin(
    (new fabric.Point(15, 0)).add(line.getPointByOrigin("right", "top"), "left", "top"))

  var group = new fabric.Group([premiseGroup, line, ruleLabel, text]);
  group.lockRotation = true;
  group.lockScalingX = true;
  group.lockScalingY = true;
  return group;
}

Judgment.prototype.draw = function() {
  i = this.image()
  canvas.add(i)
  i.center();
}
