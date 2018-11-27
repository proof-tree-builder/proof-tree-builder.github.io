import katex from 'https://cdn.jsdelivr.net/npm/katex@0.10.0/dist/katex.mjs';

var zoom = d3.zoom()
  .scaleExtent([0.5, 5])
  .on("zoom", function () {
    svg.attr("transform", d3.event.transform)
  })

var svg = d3.select("body")
  .append("svg")
  .attr("width", "100%")
  .attr("height", "100%")
  .call(zoom)
  .append("g")


svg.append("text")
  .attr("x", document.body.clientWidth / 2)
  .attr("y", document.body.clientHeight / 2)
	.attr("width", 100)
	.attr("height", 100)
  .text("Γ ⊢ Δ");

const drawJudgment = (judgment) => {
}

// update(katex.renderToString("\\Gamma \\vdash \\Delta"))
