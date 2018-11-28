Sequent.prototype.prove = function() {
  if (!this.isQuantifierFree()) {
    throw new TypeError("The sequent is not quantifier-free, therefore Wang's algorithm doesn't apply")
  }

  // Check if TruthRight is applicable
  var anteIndex = this.antecedents.findIndex(q => q instanceof Truth)
  if (anteIndex > -1) {
    return new TruthRight(this, anteIndex)
  }

  // Check if FalsityLeft is applicable
  var precIndex = this.precedents.findIndex(q => q instanceof Falsity)
  if (precIndex > -1) {
    return new FalsityLeft(this, precIndex)
  }

  // Check if Identity is applicable

  // if any of the precedents is in the antecedents,
  // conclude with the Identity rule,
  // and add the indices of the relevant formulas.
  var precIndices = this.precedents.map(p => this.antecedents.findIndex(q => deepEqual(p, q)))
  var precIndex = precIndices.findIndex(x => x > -1)

  if (precIndex > -1) {
    var anteIndex = precIndices.find(x => x > -1)
    return new Identity(this, precIndex, anteIndex)
  }

  // TODO the rest of Wang's algorithm
}
