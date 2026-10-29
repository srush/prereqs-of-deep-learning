// Inserted inside Verso's hover initializer by tools/compact_verso.py.
// Only the proof state being inspected is parsed into live DOM nodes.
const proofRequests = new Map();
function proofHTML(path) {
  if (!proofRequests.has(path)) {
    const request = fetch(path).then(response => {
      if (!response.ok) throw new Error(`Proof state: HTTP ${response.status}`);
      return response.text();
    }).catch(error => {
      proofRequests.delete(path);
      throw error;
    });
    proofRequests.set(path, request);
    if (proofRequests.size > 64) proofRequests.delete(proofRequests.keys().next().value);
  }
  return proofRequests.get(path);
}
async function fillProofState(state) {
  const request = {};
  state.proofRequest = request;
  try {
    const html = await proofHTML(state.dataset.proofState);
    if (state.proofRequest === request) state.innerHTML = html;
  } catch (error) {
    if (state.proofRequest === request) {
      state.textContent = 'Could not load this proof state. Close and reopen it to retry.';
    }
    console.error(error);
  }
}

// Create tooltips on interaction instead of allocating one per token on load.
// Existing Verso content, themes, and closed-tactic rules remain in effect.
function showLeanHover(event) {
  if (!(event.target instanceof Element)) return;
  let element = event.target.closest('[data-verso-hover], .has-info, .tactic');
  if (!element || !element.closest('.hl.lean')) return;
  if (!element.classList.contains('tactic') && blockedByTactic(element)) {
    element = element.closest('.tactic');
  }
  if (!element) return;
  if (event.relatedTarget instanceof Node && element.contains(event.relatedTarget)) return;
  if (!element._tippy) {
    const theme = element.classList.contains('tactic') ? 'tactic'
      : element.classList.contains('error') ? 'error message'
      : element.classList.contains('warning') ? 'warning message'
      : element.classList.contains('information') ? 'info message' : 'lean';
    tippy(element, {
      ...defaultTippyProps,
      theme,
      onHidden(instance) {
        defaultTippyProps.onHidden(instance);
        instance.destroy();
      },
    });
  }
  element._tippy.show();
}
document.addEventListener('mouseover', showLeanHover);
document.addEventListener('focusin', showLeanHover);
document.addEventListener('change', event => {
  const toggle = event.target;
  if (!(toggle instanceof HTMLInputElement) || !toggle.matches('.tactic-toggle')) return;
  const tactic = toggle.parentElement;
  const state = tactic.querySelector(':scope > .tactic-state');
  tactic._tippy?.hide();
  if (!state?.dataset.proofState) return;
  if (toggle.checked) {
    state.textContent = 'Loading proof state…';
    fillProofState(state);
  } else {
    // Invalidate an in-flight request and release the expanded state's DOM.
    state.proofRequest = null;
    state.replaceChildren();
    bindingCache.clear();
  }
});
