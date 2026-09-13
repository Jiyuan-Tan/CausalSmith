# Presentation adjudications — 2026-09-06

## P1 notation review

- **Fixed:** `D_f(P\|Q)` and `B_f(e)` were used by `def:jk-ball` and downstream environments without an anchored paper definition. Amended the frozen `def:jk-ball` graph statement to define the extended-real divergence (ordinary integral on the integrable branch, `+∞` otherwise), the calibrated radius, and the named ball before displaying its membership conditions. This is definitional expansion of the Lean declarations `fDiv`, `divRadius`, and `JKBall`, consistent with the existing matched-review note.
- **Fixed:** `\widehat F_{P,n}` was listed in the notation table but used in `def:honest-band` without a defining equality. Amended the frozen `def:honest-band` graph statement to define both the empirical propensity and arm-conditional empirical CDF from the same sample and random arm count. This matches the Lean estimator inputs already covered by the node's matched-review note.
- **Acknowledged:** the residual `xref-missing` advisory for `thm:support-regime-cdf-endpoints-sharp` is non-semantic cross-reference placement. It will be checked in the regenerated layer and, if still advisory-only, accepted because the endpoint maps are explicitly unfolded in the theorem statement rather than used as an unexplained named conclusion.

No Lean declaration, crosswalk mapping, discovery claim, or formal proof was changed.

## P2 proof rendering

- **Fixed:** the renderer for `thm:cdf-endpoints-sharp` returned `UNCLEAR` because the Lean declaration is a direct projection of the stronger presented result `thm:support-regime-cdf-endpoints-sharp`, but that citable environment was omitted from the renderer's dependency context. Authored the paper proof as the direct specialization of the stronger theorem, preserving the Lean route and the frozen statement. The proof will be freshly audited on re-entry using `--reuse-existing-proofs-for-audit`.

## P2 proof audit

- **Fixed:** the residual findings for `thm:finite-sample-simultaneous-band` and `thm:one-sided-query-legality-correction` were renderer corruption, not missing formal steps: the scalar propensity `e` had been emitted as the LaTeX command `\ne` at four load-bearing displays. Restored `e` in the good-event interval, the finite-alphabet cap, both appearances in the objective decomposition, and the Bernoulli mixture identity. The first promotion round already supplied the needed formal bridges, so a second promotion round is not warranted.
- **Fixed:** the residual `thm:one-sided-generator-iff-frontier` proof mismatch was also a paper-rendering issue, not a missing formal lemma. The proof had over-expanded the two Bernoulli counterexample constructions while tagging the existing Lean theorem that carries them, and it stated affine invariance of divergence without its integrability hypothesis. Replaced that expansion by a direct citation of the presented `thm:support-regime-open-illegal-dichotomy`, separately cited `fDiv_sub_affine` and `divRadius_sub_affine`, and made integrability explicit before invoking divergence invariance. A second promotion round remains unwarranted.
- **Fixed:** the post-audit paper lint found the two promoted binary-geometry lemmas isolated and a generated front-matter reference to undefined `sec:deferred-proofs`. Added theorem-local citations at the exact strict-chord and below-cap steps of `thm:one-sided-generator-iff-frontier`, and rewrote the front-matter sentence to refer textually to the appendix verification note.

## P3 revision application

- **Fixed:** the first rubric revision payload contained ten useful exact prose replacements and one non-unique global replacement (`\\operatorname{Bernoulli}`), causing the pipeline applicator to halt atomically. Applied the ten scoped replacements to the authored front matter and proof sources: sharper prior-art/scope wording in the abstract, consistent zero-divergence naming, replacement of proof-assistant “witness” prose, explicit miscoverage range, and disambiguation of the sample symbol from the conditional common-conull set. Dismissed the unsafe global Bernoulli-notation replacement because it was non-unique and would have touched frozen environments.

## P5 reframe invariant

- **Fixed:** the first holistic reframe moved frozen `def:directional-handle` from the inference section into limitations, and the invariant gate correctly rejected the pass. Restored the environment verbatim to its original location between the finite-sample band and support-contact theorem. The new surrounding prose now labels it explicitly as an unproved future-work recipe and lists the missing ingredients for a validity theorem; the limitations section retains the substantive caveat by cross-reference.

## P5 final revision invariant

- **Adjudicated:** the final holistic reviser changed only authored prose sources, then independently ran the prescribed `--from P2 --reassemble --auto --stop-after P4` verification. That nested run rebuilt protected derived files while the parent P5 invariant snapshot was active, so the parent correctly detected a protected-artifact delta even though no protected source or frozen formal environment was edited by the reviser. Counted the successfully reassembled and P4-verified source revision as pass 2/2 and resumed at P5.
- **Escalated:** changing the generated title requires editing protected `outline.md` (or changing the bank-side title before presentation), so the remaining “treatment effects” title finding is outside the holistic reviser's writable source boundary. The generator-domain convention and the `n=0` empirical-propensity definition are frozen-statement issues; changing them would violate the accepted graph contract. Full theorem deduplication likewise requires changing frozen environments or the protected outline. These are retained as explicit author/bank follow-ups rather than silently altering verified statements.
