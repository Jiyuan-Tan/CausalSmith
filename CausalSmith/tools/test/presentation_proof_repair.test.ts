import { describe, expect, it } from "vitest";
import { parseProofRepair } from "../src/presentation/stages/p2_draft.js";

const prior = String.raw`\begin{proof}[Proof of \cref{obj:lem:x}]
For the canonical tuning, the half-width is 1024 times the scale.
% lean: canonicalTuning
If the center is nonnegative, the radius is at most the half-width.
% lean: radiusBound
\end{proof}`;
const before = "If the center is nonnegative, the radius is at most the half-width.";
const after = "If the center is at most the half-width, the radius is at most the half-width; otherwise they are equal.";
const reply = (replacements: unknown) => JSON.stringify({ replacements });

describe("P2 exact proof repairs", () => {
  it("repairs the radius argument without regenerating the corrected tuning attribution", () => {
    expect(parseProofRepair(reply([{ before, after }]), prior))
      .toBe(prior.replace(before, after));
  });

  it("does not normalize untouched references as a side effect of a local repair", () => {
    const input = prior.replace("For the canonical", String.raw`See \ref{obj:other}. For the canonical`);
    expect(parseProofRepair(reply([{ before, after }]), input)).toBe(input.replace(before, after));
  });

  it("applies several disjoint patches while retaining all unselected text", () => {
    const patches = [{ before: "canonical tuning", after: "chosen canonical tuning" }, { before, after }];
    expect(parseProofRepair(reply(patches), prior))
      .toBe(prior.replace(patches[0].before, patches[0].after).replace(before, after));
  });

  it("requires unique matches in the current text after earlier edits", () => {
    const input = prior.replace(before, "old A and old B");
    const patches = [{ before: "old A", after: "old B" }, { before: "old B", after: "new B" }];
    expect(parseProofRepair(reply(patches), input)).toBeNull();
    expect(parseProofRepair(reply([...patches].reverse()), input)).toBe(input.replace("old A and old B", "old B and new B"));
  });

  it("rejects the entire repair when any location is missing or ambiguous", () => {
    for (const bad of ["absent sentence", "half-width"]) {
      expect(parseProofRepair(reply([{ before, after }, { before: bad, after: "new" }]), prior))
        .toBeNull();
    }
  });

  it("accepts ordered dependent edits but rejects stale or ambiguous matches", () => {
    expect(parseProofRepair(reply([{ before, after }, { before: "center is nonnegative", after: "center is small" }]), prior))
      .toBeNull();
    expect(parseProofRepair(reply([{ before, after }, { before: after, after: "another rewrite" }]), prior))
      .toBe(prior.replace(before, "another rewrite"));
    expect(parseProofRepair(reply([{ before: "aa", after: "b" }]), prior.replace(before, "aaa")))
      .toBeNull();
  });

  it("rejects whole-proof output and edits to proof wrappers", () => {
    expect(parseProofRepair(prior, prior)).toBeNull();
    expect(parseProofRepair(reply([{ before: "obj:lem:x", after: "obj:lem:y" }]), prior)).toBeNull();
    expect(parseProofRepair(reply([{ before: prior, after: prior }]), prior)).toBeNull();
    expect(parseProofRepair(reply([{ before, after: String.raw`\end{proof}` }]), prior)).toBeNull();
  });

  it("uses the shared TeX-aware decoder for raw math escapes in repair JSON", () => {
    const payload = String.raw`{"replacements":[{"before":"If the center is nonnegative, the radius is at most the half-width.","after":"For \(K=1\), use \frac{1}{K} and \tau."}]}`;
    expect(parseProofRepair(payload, prior)).toBe(prior.replace(before, String.raw`For \(K=1\), use \frac{1}{K} and \tau.`));
  });

  it("preserves genuine line breaks and refuses truncated or multiple JSON objects", () => {
    const after = "A displayed identity:\n\\[\n\\tau=1\n\\]";
    const payload = reply([{ before, after }]);
    expect(parseProofRepair(payload, prior)).toBe(prior.replace(before, after));
    expect(parseProofRepair(payload.slice(0, -1), prior)).toBeNull();
    expect(parseProofRepair(payload + payload, prior)).toBeNull();
  });

  it("rejects malformed patches without throwing", () => {
    for (const replacements of [null, {}, [null], [{ before: 3, after }], [{ before, after: false }], [{ before: "", after }]]) {
      expect(parseProofRepair(reply(replacements), prior)).toBeNull();
    }
  });

  it("returns an unchanged proof for an empty repair so the loop stops", () => {
    expect(parseProofRepair(reply([]), prior)).toBe(prior);
    expect(parseProofRepair(reply([{ before, after: before }]), prior)).toBe(prior);
  });
});

import { proofAuditPaperContext } from "../src/presentation/audit.js";
import type { AnchoredEnv } from "../src/presentation/tex_anchors.js";

describe("P2 audit statement excerpts", () => {
  const env = (obj_id: string, body: string): AnchoredEnv =>
    ({ obj_id, body, title: obj_id, env: "lemmav", order: 0 });
  const envs = [
    env("target", String.raw`Target uses \cref{obj:definition}.`),
    env("definition", String.raw`A defined object using \ref{obj:target}.`),
    env("helper", "The helper's exact bound."),
    env("unrelated", "This unrelated body must stay out of the initial excerpt."),
  ];

  it("includes the target and the statements the proof itself cites, one hop, ignoring comments", () => {
    const context = proofAuditPaperContext(envs, "target", String.raw`Use \Cref{obj:helper, obj:unknown}.
% \cref{obj:unrelated}`);
    expect(context).toContain(envs[0].body);
    expect(context).not.toContain(envs[1].body); // cited by the target statement, not by the proof
    expect(context).toContain(envs[2].body);
    expect(context).not.toContain(envs[3].body);
    expect(context).not.toContain("unrelated | unrelated"); // no object catalogue
    expect(context.match(/--- target /g)).toHaveLength(1);
  });

  it("selects references from the current repaired proof rather than the old draft", () => {
    expect(proofAuditPaperContext(envs, "target", "First draft.")).not.toContain(envs[2].body);
    expect(proofAuditPaperContext(envs, "target", String.raw`Now cite \cref{obj:helper}.`)).toContain(envs[2].body);
  });
});
