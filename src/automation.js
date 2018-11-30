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

  // Check if NotLeft is applicable

  var precIndex = this.precedents.findIndex(p => p instanceof Not)
  var precElem = this.precedents.find(p => p instanceof Not)
  if (precIndex > -1) {
    var newPrecedents = this.precedents
    newPrecedents.splice(precIndex, 1)
    var seq = new Sequent(newPrecedents, this.antecedents.concat([precElem.one]))
    console.log(seq.unicode());

    return new NotLeft(seq.prove(), this, this.antecedents.length, precIndex)
  }

  // Check if NotRight is applicable

  var anteIndex = this.antecedents.findIndex(p => p instanceof Not)
  var anteElem = this.antecedents.find(p => p instanceof Not)
  if (anteIndex > -1) {
    var newAntecedents = this.antecedents
    newAntecedents.splice(anteIndex, 1)
    var seq = new Sequent(this.precedents.concat([anteElem.one]), newAntecedents)
    console.log(seq.unicode());

    return new NotRight(seq.prove(), this, this.precedents.length, anteIndex)
  }


  // TODO the rest of Wang's algorithm
}
