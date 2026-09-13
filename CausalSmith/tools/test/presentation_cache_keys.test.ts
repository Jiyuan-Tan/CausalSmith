import { describe, it, expect } from "vitest";
import { PROOF_AUDIT_STANDARD, equivalenceAuditKey, proofAuditCacheKey, proofAuditSemanticNotation } from "../src/presentation/audit.js";
import { RUBRIC_STANDARD } from "../src/presentation/stages/p3_gates.js";
import { SLIDES_STANDARD } from "../src/presentation/stages/p6_slides.js";
import { P1_RENDER_STANDARD, P1_NOTATION_STANDARD, P1_SYNTH_STANDARD } from "../src/presentation/stages/p1_plan.js";
import { sectionCacheKey, proofRenderCacheKey, frontMatterCacheKey } from "../src/presentation/stages/p2_draft.js";
import { hashEnvBody } from "../src/presentation/tex_anchors.js";
import { PRESENTATION_PROSE_POLICY_VERSION } from "../src/presentation/prompt_io.js";

// BYTE-STABILITY PINS. Every persisted cache on every existing run dir is keyed by
// these formulas; an accidental change to any component order, separator, or version
// token silently colds ALL run-dir caches (P1 alone is ~30 codex audits). A failing
// pin means either an unintended formula change (fix the code) or an INTENTIONAL
// invalidation (update the pinned hex here and say why in the commit).
describe("cache key formulas are byte-stable", () => {
  it("equivalenceAuditKey (equivalence_cache.json)", () => {
    expect(
      equivalenceAuditKey({
        envBody: "BODY", mapping: "F.lean:decl:3", leanStatement: "STMT",
        refDefs: "DEFS", citedDependencies: "CITED",
      }),
    ).toBe("48b289c8f51566fc0672af2bcf131f5cff0219d663d983d679afded933b3c22e");
  });

  it("sectionCacheKey (sections/_cache_keys.json)", () => {
    // Hex updated 2026-08-21: env bodies REMOVED from the key — an INTENTIONAL one-time
    // section-cache miss per bundle (use `--from P2` on a live bundle to skip
    // it), after which re-rendered env bodies no longer re-draft the prose that places them.
    expect(sectionCacheKey("Intro", ["a", "b"], "brief", "k1, k2", "rev"))
      .toBe("1f2779cca5fd936dea8d744426bc2c2a5f84b9483e6340966f65a31d67c0cbb2");
  });

  it("proofRenderCacheKey (proofs/_cache_keys.json)", () => {
    // Hex updated 2026-08-16: `informalDerivation` added as a render input (the D-stage
    // derivation now reaches the proof prompt) — an INTENTIONAL whole-proof-cache
    // invalidation so existing thin proofs re-render with the derivation as context.
    expect(
      proofRenderCacheKey({
        modelKey: "m", objId: "T-1", envTex: "ENV", leanPath: "/p/F.lean", leanDecl: "d",
        exactDecl: "DECL", helperContext: [{ obj_id: "L-1", tex: "H" }], notation: "N",
        revisionBrief: "R", citedDependencies: "C", informalDerivation: "I",
      }),
    ).toBe("815026c7518308bfe534e8dff916b6f7f57bfb0e6ffac5f01d4f04bc1cf36d15");
  });

  it("frontMatterCacheKey (sections/_cache_keys.json `_front`)", () => {
    expect(frontMatterCacheKey("mk", "body", "fb", "brief", "keys"))
      .toBe("427acaaefb490a8e85a5c8143f715e9593b9fe46a30667d1d1ee93cc2ad3be27");
  });

  // proofAuditCacheKey embeds PRESENTATION_PROSE_POLICY_VERSION, whose bumps are
  // INTENTIONAL whole-cache invalidations — so pin the composition, not raw hex.
  it("proofAuditCacheKey (proof_audit_cache.json) — layout pin", () => {
    // Layout changed 2026-09-09: `targetStatement` dropped (the closure-keyed formalContext carries
    // the target) — rows under the old layout are honoured and re-stamped by runProofAudit.
    // Layout changed 2026-09-12: the prompt fingerprint slot became the hand-bumped
    // PROOF_AUDIT_STANDARD, initialised to that same fingerprint so the key bytes are unchanged.
    const parts = { proofTex: "P", leanPointer: "L", leanProofCacheSource: "S", notationTable: "| a | b | c | d |", formalContext: "C" };
    expect(proofAuditCacheKey(parts)).toBe(
      hashEnvBody(`${PRESENTATION_PROSE_POLICY_VERSION}|${PROOF_AUDIT_STANDARD}|C|P|L|S|${proofAuditSemanticNotation(parts.notationTable)}`),
    );
  });

  // The P3 rubric and P6 slides keys hash these tokens in the slot that used to hold a prompt
  // fingerprint; both are frozen at that fingerprint's 2026-09-12 value so existing caches stay warm.
  // P1's three model keys hash these tokens in the slot that used to hold a prompt fingerprint;
  // each is frozen at that call's 2026-09-12 fingerprint so existing p1_cache.json rows stay warm.
  it("P1 render / notation / synthesis standards are pinned", () => {
    expect(P1_RENDER_STANDARD).toBe("43fd68ad7f448930e385855cbf35d92052547b7011acbca428d017628a306959");
    expect(P1_NOTATION_STANDARD).toBe("ad823da5e4844c7a4b763abca1763a7b9c51cfecf3e9c0a49b23a10526a1bbdc");
    expect(P1_SYNTH_STANDARD).toBe("5bd102991da5885a907c409dfec19d0458cffb5643bbca9f0198ca79aa76c5da");
  });

  it("P3 rubric / P6 slides standards are pinned", () => {
    expect(RUBRIC_STANDARD).toBe("3625b12a1967d679399c6cd20ba43f04cadbb7d077aa6483b343657c66a6d501");
    expect(SLIDES_STANDARD).toBe("55c0b01b56ba5cfc1c463b44b904263d5f596dd0d2c47deb6c5f2ea653e6dc17");
  });
});
