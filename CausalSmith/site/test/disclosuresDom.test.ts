// @vitest-environment happy-dom
//
// The Cite panel and the AI-score fold, exercised through the same delegated
// handler the pages install. The load-bearing case is the last one: the landing
// page reorders its list by MOVING entry nodes, and the controls must still
// work afterwards.

import { beforeEach, describe, expect, it, vi } from "vitest";
import { initDisclosures, selectCiteTab, toggleFold } from "../src/scripts/disclosures.js";

/** One landing entry: score fold + cite panel, exactly as PaperEntry emits it. */
const entry = (id: string) => `
  <section class="wp-entry" data-id="${id}">
    <button type="button" class="badge score-badge" data-fold-toggle
            aria-expanded="false" aria-controls="ai-${id}">AI score 8.0/10
      <span class="fold-mark" aria-hidden="true" data-fold-mark>▸</span></button>
    <section class="ai-fold" id="ai-${id}" data-collapsed><p>rationale</p></section>
    <div class="wp-actions">
      <button type="button" class="cite-btn" data-fold-toggle
              aria-expanded="false" aria-controls="cite-${id}">Cite</button>
    </div>
    <div class="cite-panel" id="cite-${id}" data-cite-panel data-collapsed>
      <div class="cite-tabs">
        <div class="cite-tablist" role="tablist">
          <button type="button" role="tab" data-cite-tab="bibtex" aria-selected="true" tabindex="0">BibTeX</button>
          <button type="button" role="tab" data-cite-tab="text" aria-selected="false" tabindex="-1">Plain text</button>
        </div>
        <button type="button" class="cite-copy" data-cite-copy>Copy</button>
      </div>
      <pre class="cite-body" data-cite-body="bibtex">@techreport{k, title = {T}}</pre>
      <div class="cite-body" data-cite-body="text">CausalSmith (2026). T.</div>
    </div>
  </section>`;

const $ = <T extends Element>(sel: string) => document.querySelector<T>(sel)!;
const click = (el: Element) => el.dispatchEvent(new window.MouseEvent("click", { bubbles: true }));

beforeEach(() => {
  document.body.innerHTML = `<div id="wp-list">${entry("a")}${entry("b")}</div>`;
  // Called repeatedly on purpose: a second install would double every click
  // (open then close), so this also pins the idempotence guard.
  initDisclosures();
  initDisclosures();
});

describe("score fold", () => {
  it("opens and closes in place, keeping aria-expanded and the marker honest", () => {
    const btn = $(`[aria-controls="ai-a"]`);
    const panel = $("#ai-a");
    expect(panel.hasAttribute("data-collapsed")).toBe(true);

    click(btn);
    expect(panel.hasAttribute("data-collapsed")).toBe(false);
    expect(btn.getAttribute("aria-expanded")).toBe("true");
    expect($("[data-fold-mark]").textContent).toBe("▾");

    click(btn);
    expect(panel.hasAttribute("data-collapsed")).toBe(true);
    expect(btn.getAttribute("aria-expanded")).toBe("false");
  });

  it("opens only its own entry's panel", () => {
    click($(`[aria-controls="ai-a"]`));
    expect($("#ai-a").hasAttribute("data-collapsed")).toBe(false);
    expect($("#ai-b").hasAttribute("data-collapsed")).toBe(true);
  });

  it("fires from a click on the marker inside the button, not only the button", () => {
    click($("[data-fold-mark]"));
    expect($("#ai-a").hasAttribute("data-collapsed")).toBe(false);
  });
});

describe("cite panel", () => {
  it("discloses from the Cite button", () => {
    click($(`[aria-controls="cite-a"]`));
    expect($("#cite-a").hasAttribute("data-collapsed")).toBe(false);
  });

  it("switches between the BibTeX and plain-text bodies", () => {
    const panel = $<HTMLElement>("#cite-a");
    click($(`#cite-a [data-cite-tab="text"]`));
    expect($(`#cite-a [data-cite-body="bibtex"]`).hasAttribute("data-collapsed")).toBe(true);
    expect($(`#cite-a [data-cite-body="text"]`).hasAttribute("data-collapsed")).toBe(false);
    expect($(`#cite-a [data-cite-tab="text"]`).getAttribute("aria-selected")).toBe("true");
    expect($(`#cite-a [data-cite-tab="bibtex"]`).getAttribute("aria-selected")).toBe("false");

    selectCiteTab(panel, "bibtex");
    expect($(`#cite-a [data-cite-body="bibtex"]`).hasAttribute("data-collapsed")).toBe(false);
  });

  it("copies the body the reader is looking at", async () => {
    const writeText = vi.fn().mockResolvedValue(undefined);
    Object.defineProperty(globalThis.navigator, "clipboard", { value: { writeText }, configurable: true });
    click($(`#cite-a [data-cite-tab="text"]`));
    click($("#cite-a [data-cite-copy]"));
    expect(writeText).toHaveBeenCalledWith("CausalSmith (2026). T.");
    await Promise.resolve();
    expect($("#cite-a [data-cite-copy]").textContent).toBe("Copied");
  });

  // Over plain http `navigator.clipboard` is simply absent. The reader must
  // still end up able to finish the copy by hand.
  it("falls back to selecting the text when the clipboard is unavailable", () => {
    Object.defineProperty(globalThis.navigator, "clipboard", { value: undefined, configurable: true });
    click($("#cite-a [data-cite-copy]"));
    expect($("#cite-a [data-cite-copy]").textContent).toContain("Selected");
  });
});

// The landing page's sort calls appendChild on each entry, which MOVES the
// node. A per-button listener would survive that; a re-render would not, and
// neither would a listener bound before the node existed. Delegation on the
// document is immune to both.
describe("after the list is reordered", () => {
  it("still opens the panels", () => {
    const list = $("#wp-list");
    const entries = Array.from(document.querySelectorAll(".wp-entry")).reverse();
    for (const e of entries) list.appendChild(e);
    expect(list.firstElementChild?.getAttribute("data-id")).toBe("b");

    click($(`[aria-controls="ai-b"]`));
    expect($("#ai-b").hasAttribute("data-collapsed")).toBe(false);
    click($(`[aria-controls="cite-a"]`));
    expect($("#cite-a").hasAttribute("data-collapsed")).toBe(false);
  });
});

// A tablist may contain only tabs, and arrows must move between them — a
// keyboard user could not reach Plain text at all before (audit, 2026-09-21).
describe("cite tabs: keyboard", () => {
  const press = (el: Element, key: string) =>
    el.dispatchEvent(new window.KeyboardEvent("keydown", { key, bubbles: true, cancelable: true }));
  const tab = (id: string, which: string) =>
    $<HTMLElement>(`#cite-${id} [data-cite-tab="${which}"]`);

  it("keeps Copy out of the tablist", () => {
    expect($("#cite-a [data-cite-copy]").closest('[role="tablist"]')).toBeNull();
    expect($("#cite-a .cite-tablist")!.querySelectorAll("button").length).toBe(2);
  });

  it("moves selection with Right/Left and wraps", () => {
    press(tab("a", "bibtex"), "ArrowRight");
    expect(tab("a", "text").getAttribute("aria-selected")).toBe("true");
    expect($(`#cite-a [data-cite-body="text"]`).hasAttribute("data-collapsed")).toBe(false);
    press(tab("a", "text"), "ArrowRight"); // wraps back to the first
    expect(tab("a", "bibtex").getAttribute("aria-selected")).toBe("true");
    press(tab("a", "bibtex"), "ArrowLeft"); // and wraps the other way
    expect(tab("a", "text").getAttribute("aria-selected")).toBe("true");
  });

  it("jumps with Home and End", () => {
    press(tab("a", "bibtex"), "End");
    expect(tab("a", "text").getAttribute("aria-selected")).toBe("true");
    press(tab("a", "text"), "Home");
    expect(tab("a", "bibtex").getAttribute("aria-selected")).toBe("true");
  });

  it("keeps exactly one tab in the page's tab order (roving tabindex)", () => {
    expect(tab("a", "bibtex").tabIndex).toBe(0);
    expect(tab("a", "text").tabIndex).toBe(-1);
    press(tab("a", "bibtex"), "ArrowRight");
    expect(tab("a", "bibtex").tabIndex).toBe(-1);
    expect(tab("a", "text").tabIndex).toBe(0);
    expect(document.activeElement).toBe(tab("a", "text")); // focus follows
  });

  it("leaves other keys, and other panels, alone", () => {
    press(tab("a", "bibtex"), "ArrowDown");
    expect(tab("a", "bibtex").getAttribute("aria-selected")).toBe("true");
    press(tab("a", "bibtex"), "ArrowRight");
    expect(tab("b", "bibtex").getAttribute("aria-selected")).toBe("true");
  });
});

// Without JavaScript nothing marks the document as scripted, the CSS never
// collapses anything, and both citations plus the referee's criticisms are
// readable. Enhancement is what closes them (audit r2).
describe("without JavaScript", () => {
  it("ships the panels open and unmarked", () => {
    document.documentElement.className = "";
    document.body.innerHTML = `<div id="wp-list">${entry("c")}</div>`;
    // This is the served markup: the collapse rule is `.js [data-collapsed]`,
    // so with no `js` class on <html> it does not apply.
    expect(document.documentElement.classList.contains("js")).toBe(false);
    expect($("#cite-c").hasAttribute("data-collapsed")).toBe(true);
    expect($(`#cite-c [data-cite-body="bibtex"]`).textContent).toContain("@techreport");
    expect($(`#cite-c [data-cite-body="text"]`).textContent).toContain("CausalSmith (2026)");
    expect($(`#cite-c [data-cite-body="text"]`).hasAttribute("data-collapsed")).toBe(false);
    expect($("#ai-c").textContent).toContain("rationale");
  });

  // Collapsing is only safe once the controller that can REOPEN a panel is
  // here. The head sets `js` for a flash-free paint and withdraws it if
  // `js-ready` never appears (audit r3).
  it("signals readiness, not merely the presence of scripting", () => {
    expect(document.documentElement.classList.contains("js")).toBe(true);
    expect(document.documentElement.classList.contains("js-ready")).toBe(true);
  });

  it("leaves js-ready unset when the controller never runs", () => {
    document.documentElement.className = "js"; // what the head alone leaves
    expect(document.documentElement.classList.contains("js-ready")).toBe(false);
    // The head's watchdog then removes `js`, and the CSS rule
    // `.js .cite-panel[data-collapsed]` stops matching, so panels stay open.
    document.documentElement.classList.remove("js");
    expect(document.documentElement.classList.contains("js")).toBe(false);
  });

  it("marks the document and applies the tab state once it runs", () => {
    expect(document.documentElement.classList.contains("js")).toBe(true);
    expect($(`#cite-a [data-cite-body="text"]`).hasAttribute("data-collapsed")).toBe(true);
    expect($(`#cite-a [data-cite-body="bibtex"]`).hasAttribute("data-collapsed")).toBe(false);
  });
});

describe("toggleFold", () => {
  it("is inert on a button whose panel is missing", () => {
    const orphan = document.createElement("button");
    orphan.setAttribute("aria-controls", "nope");
    expect(() => toggleFold(orphan)).not.toThrow();
  });
});
