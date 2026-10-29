// A reading view for the Baby Rudin note. Keep definitions and theorem statements
// visible, and retain Verso's original highlighted proof nodes inside disclosures.
function foldRudinProofs() {
  document.body.classList.add('rudin-note');

  document.querySelectorAll('.code-box > code.hl.lean.block').forEach(code => {
    const theorem = code.querySelector('[data-binding^="kw-occ-Lean.Parser.Command.theorem-"]');
    const assignment = code.querySelector('[data-binding^="kw-occ-Lean.Parser.Command.declValSimple-"]');
    if (!theorem || !assignment || code.dataset.proofFolded) return;

    // Some Verso tactic ranges wrap the declaration's statement as well as its
    // proof. Unwrap just those crossing the boundary; keep inner tactics intact.
    while (assignment.parentElement !== code) {
      const tactic = assignment.closest('.tactic');
      const label = tactic?.querySelector(':scope > label');
      if (!tactic || !code.contains(tactic) || !label?.contains(assignment)) return;
      tactic.replaceWith(...label.childNodes);
    }

    const name = code.querySelector('.const.token[id]')?.textContent || 'theorem';
    const disclosure = document.createElement('details');
    disclosure.className = 'lean-proof';
    const summary = document.createElement('summary');
    summary.setAttribute('aria-label', `Proof of ${name}`);
    // The visible caption is CSS-generated so Verso's textContent-based copy
    // button still copies exactly the Lean source, without a stray "Proof" word.
    const proof = document.createElement('code');
    proof.className = code.className;
    proof.dataset.leanContext = code.dataset.leanContext || 'lean';
    while (assignment.nextSibling) proof.append(assignment.nextSibling);
    disclosure.append(summary, proof);
    code.dataset.proofFolded = 'true';
    code.after(disclosure);
  });

  // Declaration links stay on the visible statement. Links into a proof open it.
  function revealLinkedProof() {
    let id;
    try { id = decodeURIComponent(location.hash.slice(1)); } catch { return; }
    const target = document.getElementById(id);
    const proof = target?.closest('details.lean-proof');
    if (proof) {
      proof.open = true;
      target.scrollIntoView({block: 'center'});
    }
  }
  window.addEventListener('hashchange', revealLinkedProof);
  revealLinkedProof();
}

if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', foldRudinProofs, {once: true});
} else {
  foldRudinProofs();
}
