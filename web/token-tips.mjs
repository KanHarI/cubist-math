// A macro's expansion shows as soon as its token is hovered or focused, not
// after the browser's delay for a title. A token carries its tip in data-tip;
// one shared element shows it next to the token.
let tip = null, enabled = false;

function show(target) {
  if (!tip) {
    tip = document.createElement("div");
    tip.className = "token-tip";
    tip.id = "token-tip";
    tip.setAttribute("role", "tooltip");
  }
  if (!tip.isConnected) document.body.append(tip);
  tip.textContent = target.dataset.tip;
  tip.hidden = false;
  target.setAttribute("aria-describedby", tip.id);
  // Below the token when it fits, otherwise above; always inside the viewport.
  const box = target.getBoundingClientRect(), gap = 6;
  const left = Math.max(8, Math.min(box.left, innerWidth - tip.offsetWidth - 8));
  const top = box.bottom + gap + tip.offsetHeight <= innerHeight ? box.bottom + gap : box.top - gap - tip.offsetHeight;
  tip.style.left = `${left}px`;
  tip.style.top = `${Math.max(8, top)}px`;
}

function hide() {
  if (tip) tip.hidden = true;
}

export function enableTokenTips() {
  if (enabled) return;
  enabled = true;
  const tipped = node => node instanceof Element ? node.closest("[data-tip]") : null;
  document.addEventListener("pointerover", ({ target }) => { const token = tipped(target); if (token) show(token); });
  document.addEventListener("pointerout", ({ target, relatedTarget }) => {
    const token = tipped(target);
    if (token && !(relatedTarget instanceof Node && token.contains(relatedTarget))) hide();
  });
  document.addEventListener("focusin", ({ target }) => { const token = tipped(target); if (token) show(token); });
  document.addEventListener("focusout", hide);
  // Scrolling the page or a code block moves the token away from its tip.
  addEventListener("scroll", hide, true);
}
