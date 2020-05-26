// from https://www.w3schools.com/howto/howto_js_draggable.asp
const dragModal = () => {
  let elmnt = document.querySelector('.modal-inner')
  let pos1 = 0, pos2 = 0, pos3 = 0, pos4 = 0

  const dragMouseDown = (e) => {
    e = e || window.event
    e.preventDefault()
    // get the mouse cursor position at startup:
    pos3 = e.clientX
    pos4 = e.clientY
    document.onmouseup = closeDragElement
    // call a function whenever the cursor moves:
    document.onmousemove = elementDrag
  }

  const elementDrag = (e) => {
    e = e || window.event
    e.preventDefault()
    // calculate the new cursor position:
    pos1 = pos3 - e.clientX
    pos2 = pos4 - e.clientY
    pos3 = e.clientX
    pos4 = e.clientY
    // set the element's new position:
    elmnt.style.top = (elmnt.offsetTop - pos2) + "px"
    elmnt.style.left = (elmnt.offsetLeft - pos1) + "px"
  }

  const closeDragElement = () => {
    // stop moving when mouse button is released:
    document.onmouseup = null
    document.onmousemove = null
  }

  document.querySelector('.modal-header').onmousedown = dragMouseDown
}

const modalWindow = s => {
  return `<div class="modal">
            <div class="modal-inner">
              <div class="modal-header">
                <span class="close">&times;</span>
              </div>
              <div class="modal-content">
                ${s}
              </div>
            </div>
          </div>`
}

const modalPromptBinds = html => {
  let node = toNodes(modalWindow(html))[0]
  document.body.appendChild(node)
  dragModal()
  node.style.display = "block"
  document.querySelector('.modal-content textarea').focus()

  return new Promise((resolve, reject) => {
    document.querySelector('button.ok').onclick = e => {
      let answer = document.querySelector('.modal-content textarea').value.trim()
      document.querySelector('.modal').remove()
      resolve(answer)
    }
    document.querySelector(".close").onclick = e => {
      document.querySelector('.modal').remove()
      reject(new Error("Cancelled prompt"))
    }
    document.querySelector('button.cancel').onclick = e => {
      document.querySelector('.modal').remove()
      reject(new Error("Cancelled prompt"))
    }
    window.onclick = e => {
      if (e.target == document.querySelector('.modal')) {
        document.querySelector('.modal').remove()
        reject(new Error("Cancelled prompt"))
      }
    } 
  })
}

const modalPrompt = s => {
  let html = `<p>${s}</p>
              <p><textarea></textarea></p>
              <p>
                <button class="ok">OK</button>
                <button class="cancel">Cancel</button>
              </p>`

  let p = modalPromptBinds(html)
  return p
}

const waitAfterInput = action => e => {
  // initially borrowed from https://stackoverflow.com/a/6217551/2016295
  let callCount = 0

  const delayAction = (action, time) => {
    let expected = callCount
    setTimeout(() => { if(callCount === expected) action() }, time)
  }

  return (eventtrigger) => {
    callCount++
    delayAction(action, 800)
  }
}

const modalParsePrompt = (prettyName, parserRuleName, s, disable = true, toString) => {
  let emptyMsg = `The parsed ${prettyName} will appear here as you type.`
  let html = `<p>${s}</p>
              <p><textarea></textarea></p>
              <p><small>${emptyMsg}</small></p>
              <p>
                <button class="ok" ${disable ? "disabled" : ""}>OK</button>
                <button class="cancel">Cancel</button>
              </p>`

  let p = modalPromptBinds(html)

  document.querySelector('.modal-content textarea').onkeyup = 
    waitAfterInput(() => { 
      if (document.querySelector('.modal') === null) { return }
      let answer = document.querySelector('.modal-content textarea').value.trim()
      let toShow = document.querySelector('.modal-content p small')
      let okButton = document.querySelector('.modal-content button.ok')
      
      if (answer === "") {
        toShow.innerHTML = emptyMsg
        if(disable) { okButton.disabled = true }
        return
      }

      try {
        let parsed = peg.parse(answer, { startRule: parserRuleName })
        if(disable) { okButton.disabled = false }
        let str
        if(toString) {
          str = toString(parsed)
        } else {
          str = parsed.unicode() // default
        }
        toShow.innerHTML = `<span style="color: ${successColor}"><strong>✓:</strong> ${str}</span>`
      } catch(err) {
        if(disable) { okButton.disabled = false }
        toShow.innerHTML = `<span style="color: ${failureColor}"><strong>&times;:</strong> ${err.message}</span>`
      }
    })()

  return p
}

const modalFormulaPrompt = async s => peg.parse(await modalParsePrompt("formula", "Formula", s), { startRule: "Formula" }) 
const modalSequentPrompt = async s => peg.parse(await modalParsePrompt("sequent", "Sequent", s), { startRule: "Sequent" }) 
const modalHoarePrompt = async s => peg.parse(await modalParsePrompt("Hoare triple", "HoareTriple", s), { startRule: "HoareTriple" }) 
const modalNamePrompt = async s => peg.parse(await modalParsePrompt("variable name", "Name", s, true, x => x), { startRule: "Name" }) 
const modalTermPrompt = async s => peg.parse(await modalParsePrompt("term", "Term", s), { startRule: "Term" }) 

const modalFormulaPromptDefault = async (s, def) => {
  const input = await modalParsePrompt("formula", "Formula", s, false)
  if (input === "") {
    return def
  } else {
    return peg.parse(input, { startRule: "Formula" }) 
  }
}

const modalRadioBinds = html => {
  let node = toNodes(modalWindow(html))[0]
  document.body.appendChild(node)
  dragModal()
  node.style.display = "block"

  return new Promise((resolve, reject) => {
    document.querySelector('button.ok').onclick = e => {
      let answer = document.querySelector('input[name=choice]:checked').value
      document.querySelector('.modal').remove()
      resolve(parseInt(answer))
    }
    document.querySelector(".close").onclick = e => {
      document.querySelector('.modal').remove()
      reject(new Error("Cancelled multiple choice"))
    }
    document.querySelector('button.cancel').onclick = e => {
      document.querySelector('.modal').remove()
      reject(new Error("Cancelled multiple choice"))
    }
    window.onclick = e => {
      if (e.target == document.querySelector('.modal')) {
        document.querySelector('.modal').remove()
        reject(new Error("Cancelled multiple choice"))
      }
    } 
  })
}

const modalRadio = (s, options) => {
  let labels = ``
  options.forEach((opt, i) => {
    labels += `<p><label><input type="radio" name="choice" value="${i}" /> ${opt}</label></p>`
  })

  let html = `<p>${s}</p>
              ${labels}
              <p>
                <button class="ok" disabled>OK</button>
                <button class="cancel">Cancel</button>
              </p>`

  let p = modalRadioBinds(html)

  document.querySelectorAll('.modal-content input[name="choice"]').forEach(radio => {
    radio.onclick = e => { document.querySelector('.modal-content button.ok').disabled = false }
  })

  return p
}
