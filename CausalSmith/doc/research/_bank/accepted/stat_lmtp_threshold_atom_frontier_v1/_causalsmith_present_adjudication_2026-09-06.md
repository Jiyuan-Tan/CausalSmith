# Presentation adjudication — 2026-09-06

## P1 citation namespace repair

The two verified cited gates used graph source slugs (`kallenberg2002-foundations-thm6-3` and `hoeffding1963-thm2`) that did not resolve to the P0 bibliography's CamelCase keys. The existing verified bibliography entries were re-keyed to those exact graph slugs in the presentation bundle. No source, title, locator, or claim was changed.

After the P2 promotion reload regenerated the bibliography from its verified P0 sources, the derived re-keying was lost and citation erasure recurred. The persistent repair is therefore in `graph.json`: the two cited-gate source fields now use the canonical verified keys `Kallenberg2002Foundations` and `Hoeffding1963`. The bibliography and P0 verification records themselves are unchanged.

## P1 notation homes

The notation reviewer found six Lean-realized symbols without an editable frozen environment. Three Lean-backed definition nodes were added to `graph.json`:

- `def:clamp-functional`, mapped to `clampFunctional`, defines the exact unsmoothed observed clamp functional together with `q_x(δ)` and the retained mean.
- `def:local-design-notation`, mapped to `interceptWeight`, exposes the definitions it unfolds (`v_ℓ`, the reference moment matrix, `Ω_x`, and `w_ix`).
- `def:causal-clamp-mean`, mapped to `causalClampMean`, defines `ψ_δ(P^F)`.

These are presentation homes for existing Lean declarations, not new mathematical claims. The exact-modulus constant remains explicitly an open question in `oeq:sharp-constant`; no optimality or exact-constant conclusion was added.

## P1 checkpoint review

The outline has a conventional journal progression (question and contribution, early related work, setup, procedures, results, causal interpretation, continuity-only extension, limitations/open question, proofs). No frozen theorem or lemma is standard-literature motivation ballast; the two imported standard results remain hidden cited dependencies.

Two ordering advisories were fixed in `outline.md`: the projection definition `synth_6` now precedes the fixed-split interval `synth_12`, and `def:exact-modulus-handle` now precedes `synth_14`. Five cross-reference advisories were accepted because the new `statement-uses` edges were added to establish notation-home dependency and order; the audited theorem bodies already state the relevant targets and rates explicitly, and no mathematical dependency is being hidden. The sharp-constant environment was checked to remain interrogative throughout and to assert no exact constant, honesty, nondegeneracy, or optimality result.

The P2 ballast gate identified three terminal results and their three supporting continuity definitions. All six were acknowledged in `ballast_review.json`: the one-cell calibration is an explicit exponent benchmark, the causal-frontier lift and continuity-only frontier are delivered headline results, and the three continuity definitions are the rate, estimator, and interval used by that headline. None is motivation-only standard material.
