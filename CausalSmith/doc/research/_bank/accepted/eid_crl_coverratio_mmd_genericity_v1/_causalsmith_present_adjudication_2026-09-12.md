# P2 proof-audit adjudication — 2026-09-12

Operator decisions (user-approved in session), run through P4 only; P5 was not rerun.
- `lem:analytic-edge-perturbation`: remaining findings overruled, marked `faithful` in
  `proof_audit_cache.json` (verdict flipped, key recomputed for the final proof text).
- `thm:exact-ratio-decoder`: promotion round 2 granted (`--promote-again`, run from P1 because a
  P2 reassemble entry never promotes). It added three Lean-backed lemmas, all judged faithful at P1:
  `lem:ratio-nonancestor-zero` (`ratio_nonancestor_zero`), `lem:predecessor-score-homeomorphism`
  (`predecessorScoreHomeomorph`), `lem:exact-ratio-decoder-continuous-rank-clauses`
  (`exactRatioDecoder_continuousRankClauses`). The retried audit then asked the new lemmas for
  further helpers (five more for the rank-clauses lemma). No third round was granted: that is the
  non-converging cascade, and the derivations are given in prose. Remaining genuine rendering defects
  were fixed by hand (a control character corrupting `\ell` in a support clause, a duplicated
  identity, the measure space of the observed laws, a mis-attributed assumption, the `v^{(w)}`
  parent-locality reduction, Lean-flavoured compatibility/carrier wording), then the decoder and
  the two unconverged new lemmas were marked `faithful` (keys recomputed). Overruled: provenance-tag
  granularity, the sign-compatibility remark (Lean uses the same sign vector for both worlds, as
  the prose says), and the further `[missing-step]` requests.

## Compile fixes during the P4 emit
- `lem:analytic-edge-perturbation`: the fixed-sign display wrote `s_\ell\Bigg` with no delimiter; now `\Bigg(`.
- `lem:exact-ratio-decoder-continuous-rank-clauses` statement: a stray `\]` after the last item broke
  the itemize. Removed from every stored copy (formal_layer.json/.tex, the appendix section, paper.tex,
  p1_cache.json, and nl.frozen_body in graph.json). Because proof-audit keys include the formal
  statements a proof relies on, the lemma's proof and the decoder proof were re-keyed as `faithful`
  under the corrected statement; the decoder proof was restored to the adjudicated text after an
  unwanted repair rewrite (the rejected rewrite is kept in the session scratchpad).
- Final emit: `stopped:P4`, paper compiles (71 pages), index check clean, no P5 calls.

## Why these proofs were re-audited
Commits `197008afb` and `ee0002d5e` (2026-09-12) edited `prompts/proof_audit.txt`, which under
the then-current key scheme rekeyed every cached proof verdict; the coordinate-name migration
also changed Lean helper sources behind three proofs. The re-audit flagged six of nine proofs;
four were repaired by the pipeline and accepted, two remained.

## Fixed by hand before adjudication
- `thm:exact-ratio-decoder`: step-1 coherence display (stray `a=`, identical sides) rewritten
  to compare the rank coordinates of the two compatible worlds; step-13 relabeling direction
  stated consistently as sigma = pi-tilde after pi-inverse (matches
  `W.targetPerm.symm.trans W'.targetPerm`); "shared mixing map" corrected to W'-specific.
- `lem:analytic-edge-perturbation`: step 1 now states the needed conclusion (open convex
  O ⊇ [0,1], positivity, analyticity) and presents the m/2 set as one admissible construction;
  step 3 no longer cites `def:cancellation-witness` for the auxiliary primitive H; step 5
  neighborhood phrasing aligned with the ambient neighborhood filter; `p_l(v)` notation defined.

## Why the Sept 10 audit passed without these lemmas
Promotion round 1 already ran on Sept 10 (added the equation-ten/eleven lemmas). The helpers now
named by the judge (`predecessorScoreHomeomorph`, `exactRankCondIndepCharacterization`,
`componentwiseC2Equivalent_of_common_rank_and_aligned_edges`,
`ratioGraph_reconstruction_order_and_predecessors`, and the analytic-edge helpers) exist only in the
later uncommitted Lean refactor; before it the Lean proof derived these steps inline.

## Findings overruled (not mathematical errors)
- `lem:analytic-edge-perturbation`: provenance-only findings (the prose derives the scalar
  inequality, analyticity, and stratum preservation that Lean delegates to
  `affinePathContrast_one_ne_zero`, `affinePathContrastIntegral_analyticOnNhd`,
  `affinePathExtension_eventually_modelStratum`). These are short technical steps of one lemma and
  not independently interesting; promotion cannot close `[rendering]` findings anyway.

The pre-adjudication proofs and cache are backed up in the session scratchpad
(`crl_manual_patch_backup/`). A future full re-presentation may revisit lemma promotion.
