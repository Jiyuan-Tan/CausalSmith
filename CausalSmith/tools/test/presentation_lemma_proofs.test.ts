import { describe, expect, it } from "vitest";
import { parseProofRender, insertLemmaProofs, insertProofPointers } from "../src/presentation/stages/p2_draft.js";

// Object ids contain ':' (e.g. prop:overlap-envelope) — the marker/env regexes
// must handle the colon, or the whole lemma-proof batch fails to parse (real P2 incident 2026-06-25).
const proofA = "\\begin{proof}[Proof of Lemma~\\ref{obj:lem:witness-membership}]\nStep. % lean: witness_membership\n\\end{proof}";
const proofB = "\\begin{proof}[Proof of Lemma~\\ref{obj:prop:overlap-envelope}]\nOther. % lean: overlap_envelope\n\\end{proof}";

describe("parseProofRender", () => {
  it("attributes a lemma proof to its colon-bearing object id", () => {
    expect(parseProofRender(proofA, "lem:witness-membership"))
      .toContain(String.raw`\begin{proof}[Proof of \cref{obj:lem:witness-membership}]`);
  });

  it("rejects an UNCLEAR response even if it echoes a prior proof", () => {
    expect(parseProofRender(`UNCLEAR: route missing\n${proofA}`, "lem:witness-membership")).toBeNull();
  });

  it("rejects absent or incomplete proof envelopes for a targeted retry", () => {
    expect(parseProofRender("No proof emitted", "lem:a")).toBeNull();
    expect(parseProofRender(String.raw`\begin{proof}Unfinished`, "lem:a")).toBeNull();
  });

  it("preserves a nested claim proof and discards surrounding chatter", () => {
    const nested = String.raw`\begin{proof}Outer. \begin{proof}[Claim]Inner.\end{proof} Conclusion.\end{proof}`;
    const parsed = parseProofRender(`chatter\n${nested}\nchatter`, "lem:a");
    expect(parsed).toContain(String.raw`\begin{proof}[Claim]Inner.\end{proof} Conclusion.\end{proof}`);
    expect(parsed).not.toContain("chatter");
  });
});

describe("insertLemmaProofs", () => {
  const tex = [
    "intro prose",
    "\\begin{lemmav}{lem:witness-membership}[Title]\nbody\n\\end{lemmav}",
    "remark prose",
    "\\begin{lemmav}{lem:clip-bias}\nbody9\n\\end{lemmav}",
    "tail",
  ].join("\n\n");

  it("inserts each proof directly after its lemma env, leaving others alone", () => {
    const out = insertLemmaProofs(tex, new Map([["lem:witness-membership", proofA]]));
    expect(out).toContain(`\\end{lemmav}\n\n${proofA}\n\nremark prose`);
    expect(out).toContain("\\begin{lemmav}{lem:clip-bias}\nbody9\n\\end{lemmav}\n\ntail");
    expect(out.match(/\\begin\{proof\}/g)?.length).toBe(1);
  });

  it("is a no-op with no proofs", () => {
    expect(insertLemmaProofs(tex, new Map())).toBe(tex);
  });
});

describe("insertProofPointers", () => {
  const tex = [
    "intro prose",
    "\\begin{lemmav}{lem:witness-membership}[Title]\nbody\n\\end{lemmav}",
    "remark prose",
    "\\begin{lemmav}{lem:clip-bias}\nbody9\n\\end{lemmav}",
    "tail",
  ].join("\n\n");

  it("adds a deferral pointer only after the listed (body) lemmas", () => {
    const out = insertProofPointers(tex, new Set(["lem:witness-membership"]), "sec:deferred-proofs");
    // body lemma gets the pointer to the proofs appendix (clickable section ref, not an obj ref).
    // The pointer is a bare \cref: the manuscript's target-typed reference convention has the
    // TARGET supply its own kind, and tex_anchors' xref lint explicitly rejects a manually
    // chosen kind ("Appendix~\ref{…}" / "Appendix~\cref{…}") as duplicating it.
    expect(out).toContain("\\end{lemmav}\n\nThe proof is deferred to \\cref{sec:deferred-proofs}.");
    // the other lemma (appendix-placed; not in the set) is untouched — no pointer, no proof inline
    expect(out).toContain("\\begin{lemmav}{lem:clip-bias}\nbody9\n\\end{lemmav}\n\ntail");
    expect(out.match(/deferred to \\cref/g)?.length).toBe(1);
    // never a manually chosen kind in front of the ref — that is what the lint flags
    expect(out).not.toMatch(/Appendix~?\\c?ref\{/);
    // the pointer uses a section ref (sec:), never an obj ref — so xref lints don't flag it
    expect(out).not.toContain("\\ref{obj:");
  });

  it("is a no-op when no lemma ids are given", () => {
    expect(insertProofPointers(tex, new Set(), "sec:deferred-proofs")).toBe(tex);
  });
});
