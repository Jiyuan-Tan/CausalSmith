/**
 * The landing/paper page disclosures: the Cite panel and the AI-score fold.
 *
 * DELEGATED, deliberately. The landing page reorders its list by MOVING the
 * `<section>` nodes with `appendChild`; a listener bound to a button inside one
 * of them would survive that (the node is moved, not recreated), but a listener
 * bound per button is also one listener per paper per control, and any future
 * re-render would silently drop them all. A single document-level handler
 * cannot be lost by a reorder, and costs one listener for the whole page.
 *
 * Both panels are in the DOM from the first paint, `hidden`; opening flips
 * `hidden` and `aria-expanded`. Nothing is built client-side, so the panels
 * work identically with JavaScript disabled up to the point of being closed.
 */

const OPEN_MARK = "▾"; // ▾
const SHUT_MARK = "▸"; // ▸

function panelOf(btn: Element): HTMLElement | null {
  const id = btn.getAttribute("aria-controls");
  return id ? btn.ownerDocument.getElementById(id) : null;
}

function setExpanded(btn: Element, open: boolean): void {
  btn.setAttribute("aria-expanded", open ? "true" : "false");
  const mark = btn.querySelector("[data-fold-mark]");
  if (mark) mark.textContent = open ? OPEN_MARK : SHUT_MARK;
}

/** Opens/closes one disclosure. Exported for tests and for deep-link handling. */
export function toggleFold(btn: Element, force?: boolean): void {
  const panel = panelOf(btn);
  if (!panel) return;
  const open = force ?? panel.hasAttribute("data-collapsed");
  if (open) panel.removeAttribute("data-collapsed");
  else panel.setAttribute("data-collapsed", "");
  setExpanded(btn, open);
}

/**
 * Switches a Cite panel between its BibTeX and plain-text bodies.
 *
 * Roving tabindex: exactly one tab is in the page's tab order at a time, which
 * is the standard tabs pattern — arrows move between tabs, Tab leaves the
 * widget. `focus` moves the caret only when the change came from the keyboard.
 */
export function selectCiteTab(panel: HTMLElement, tab: string, focus = false): void {
  for (const b of Array.from(panel.querySelectorAll<HTMLElement>("[data-cite-tab]"))) {
    const on = b.getAttribute("data-cite-tab") === tab;
    b.setAttribute("aria-selected", on ? "true" : "false");
    b.tabIndex = on ? 0 : -1;
    if (on && focus) b.focus();
  }
  for (const body of Array.from(panel.querySelectorAll<HTMLElement>("[data-cite-body]"))) {
    if (body.getAttribute("data-cite-body") === tab) body.removeAttribute("data-collapsed");
    else body.setAttribute("data-collapsed", "");
  }
}

/** The body the reader is currently looking at (what Copy must copy). */
function visibleBody(panel: HTMLElement): HTMLElement | null {
  return panel.querySelector<HTMLElement>("[data-cite-body]:not([data-collapsed])");
}

/**
 * Copy, with the selection fallback. `navigator.clipboard` is absent over
 * plain http and rejects without a user gesture in some browsers, so a failure
 * must leave the reader able to finish the job by hand rather than with a
 * button that silently did nothing.
 */
function copyCitation(btn: HTMLElement, panel: HTMLElement): void {
  const body = visibleBody(panel);
  if (!body) return;
  const text = body.textContent ?? "";
  const label = btn.getAttribute("data-copy-label") ?? btn.textContent ?? "Copy";
  btn.setAttribute("data-copy-label", label);
  const done = () => {
    btn.textContent = "Copied";
    setTimeout(() => {
      btn.textContent = label;
    }, 1400);
  };
  const fallback = () => {
    const doc = panel.ownerDocument;
    const sel = doc.defaultView?.getSelection?.();
    if (sel) {
      const range = doc.createRange();
      range.selectNodeContents(body);
      sel.removeAllRanges();
      sel.addRange(range);
    }
    btn.textContent = "Selected — press Ctrl/⌘-C";
  };
  const clip = (navigator as Navigator | undefined)?.clipboard;
  if (!clip?.writeText) {
    fallback();
    return;
  }
  void clip.writeText(text).then(done, fallback);
}

/** Documents already wired. A second `initDisclosures()` on the same document —
 *  two page scripts, a re-run after a client-side navigation — would otherwise
 *  install a second handler and every click would toggle twice, i.e. do nothing. */
const wired = new WeakSet<Document>();

/** Wires the delegated handler. Safe to call on a page with no disclosures,
 *  and safe to call more than once. */
export function initDisclosures(doc: Document = document): void {
  // Enhancement, not construction: the markup ships OPEN so it is readable
  // without a script, and the collapsed state is applied here. This half is
  // idempotent and runs on every call, so a re-render cannot leave the page
  // marked as scripted while its panels are still in their served state.
  // `js` is set in the head for a flash-free first paint; `js-ready` says the
  // controller that can REOPEN a collapsed panel is actually here. The head's
  // watchdog withdraws `js` if this never runs (audit r3).
  doc.documentElement.classList.add("js");
  doc.documentElement.classList.add("js-ready");
  for (const panel of Array.from(doc.querySelectorAll<HTMLElement>("[data-cite-panel]"))) {
    const selected = panel.querySelector<HTMLElement>('[data-cite-tab][aria-selected="true"]');
    selectCiteTab(panel, selected?.getAttribute("data-cite-tab") ?? "bibtex");
  }
  // The delegated listener, on the other hand, must be installed exactly once.
  if (wired.has(doc)) return;
  wired.add(doc);
  doc.addEventListener("click", (ev) => {
    const target = ev.target as Element | null;
    if (!target || typeof target.closest !== "function") return;

    const tab = target.closest<HTMLElement>("[data-cite-tab]");
    if (tab) {
      const panel = tab.closest<HTMLElement>("[data-cite-panel]");
      if (panel) selectCiteTab(panel, tab.getAttribute("data-cite-tab") ?? "bibtex");
      return;
    }
    const copy = target.closest<HTMLElement>("[data-cite-copy]");
    if (copy) {
      const panel = copy.closest<HTMLElement>("[data-cite-panel]");
      if (panel) copyCitation(copy, panel);
      return;
    }
    const fold = target.closest<HTMLElement>("[data-fold-toggle]");
    if (fold) {
      toggleFold(fold);
      return;
    }
  });

  // Arrow/Home/End across the citation tabs. Without this a keyboard user who
  // lands on BibTeX cannot reach Plain text the way every other tab widget on
  // the web works (audit, 2026-09-21).
  doc.addEventListener("keydown", (ev) => {
    const key = (ev as KeyboardEvent).key;
    if (!["ArrowLeft", "ArrowRight", "Home", "End"].includes(key)) return;
    const target = ev.target as Element | null;
    const tab = target?.closest?.<HTMLElement>("[data-cite-tab]");
    if (!tab) return;
    const panel = tab.closest<HTMLElement>("[data-cite-panel]");
    if (!panel) return;
    const tabs = Array.from(panel.querySelectorAll<HTMLElement>("[data-cite-tab]"));
    const here = tabs.indexOf(tab);
    if (here < 0) return;
    const next =
      key === "Home"
        ? 0
        : key === "End"
          ? tabs.length - 1
          : (here + (key === "ArrowRight" ? 1 : -1) + tabs.length) % tabs.length;
    ev.preventDefault();
    selectCiteTab(panel, tabs[next].getAttribute("data-cite-tab") ?? "bibtex", true);
  });
}
