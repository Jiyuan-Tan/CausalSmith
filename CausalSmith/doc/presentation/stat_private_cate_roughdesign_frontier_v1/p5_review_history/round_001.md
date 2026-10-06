# Referee review

**Recommendation:** minor_revision
**Overall score:** 7.6/10 — The submission delivers a substantive and carefully scoped private minimax characterization, with faithful claims and strong positioning, while its organization and several presentation details need refinement.

The paper characterizes pure-private pointwise estimation and honest connected-interval length in a precisely specified binary causal model with rough nuisance functions and an unknown bounded positive design density. Its main contributions are the occupancy-weighted pair construction and matching privacy-sensitive lower bounds; the verification contract supports the stated mathematical conclusions. The literature comparison is unusually careful about differences in experiments and assumptions. Publication is warranted after an editorial revision that foregrounds these contributions, reduces repetition, and clarifies the branch-specific interval presentation.

## Strengths
- The estimation and interval claims preserve the verified model restrictions, privacy definition, decision criteria, and constant-factor meaning of optimality.
- Shared occupancy weights provide a concrete attainment argument across the entire admissible measurable-density class, including boundary arm means.
- The interval converse addresses honest expected length directly through simultaneous containment and connectedness.
- The dedicated early related-work section engages competitors' rates, assumptions, privacy requirements, and estimands.
- The limitations section clearly explains the displayed interval's full-range behavior at the certified constants and distinguishes mathematical guarantees from implementation certification.

## Findings
- **[minor·structure] Observation model, identification, and decision criteria** — The model presentation fragments elementary notation into separate environments for the outcome coordinate, treatment coordinate, covariate coordinate, probability laws, and interval coding. Their ordering makes readers reconstruct the record structure before reaching the statistical class and decision problems.
  - *Fix:* Introduce the full causal record and observed marginal together in the main text, retain a compact statement of the model restrictions and decision criteria, and relocate the individual coordinate definitions, probability-space conventions, and detailed interval coding to an appendix while preserving their anchored environments.
- **[minor·structure] Introduction; Related work; Discussion and limitations** — The comparison with Kennedy and coauthors is developed at substantial length in both the introduction and related work, while the benchmark, public tuning, occupancy explanation, and consistency conclusion recur throughout the discussion and appendices. This repetition dilutes the paper's conceptual contribution.
  - *Fix:* Reduce the introduction's literature comparison to a concise novelty paragraph, retain the detailed conditions in Related work, and make the discussion interpret the findings rather than repeat the construction. Concentrate the main-text explanation on shared occupancy weighting, the two privacy scales, and the direct expected-length converse.
- **[minor·prose] A private release based on within-cell pairs** — The sentence "The coverage theorem and the asymptotic order statement remain valid, but these explicit constants make the displayed interval uninformative throughout that finite-sample range" places a genuine limitation outside the explicitly titled limitations subsection. The same interpretation already appears there.
  - *Fix:* Keep the affirmative mathematical conclusion here: for the stated sample-size range, the procedure returns the full target interval with uniform coverage. Consolidate the interpretation of practical width in Limitations and future work.
- **[minor·statement] Optimal estimation and honest confidence intervals** — Within \cref{obj:thm:sharp-interval-frontier}, the local tuning parameters are introduced for the branch with benchmark below one eighth, but the subsequent sentence "Using the clipped pair-ratio estimator ... the tuned interval is" presents the local centered-interval formula without repeating that branch condition. The fallback interval has already been specified separately, so the display's domain should be explicit.
  - *Fix:* Preface the occupancy-envelope definitions and centered-interval display with "On this local branch" or the exact benchmark condition, and retain the full-range fallback formula for the complementary branch.
- **[minor·prose] Introduction** — The choice of nuisance smoothness one tenth is motivated as a transparent higher-order regime, but the substantive interpretation of a Lipschitz contrast alongside much rougher arm means and treatment selection remains brief. Explaining this relationship would strengthen the contribution's significance for econometric readers.
  - *Fix:* Add a short affirmative explanation of how common rough variation in the treatment-arm means can coexist with a smoother difference, and describe the scalar binary experiment as a concrete setting in which privacy and nuisance roughness interact. Keep the numerical smoothness specialization explicit.
- **[nit·prose] Lower-bound experiments and component coupling** — The component-mark definition wraps its cross-reference in inline mathematics: "from \(\cref{obj:def:cosine-family}\)." A reader-facing cross-reference belongs in ordinary text.
  - *Fix:* Remove the inline-math delimiters around \cref{obj:def:cosine-family}.
- **[nit·prose] abstract** — The first-use gloss "For n≥2, the sample size, and 0<ε≤1, the pure replacement privacy budget" attaches the appositives awkwardly to inequalities.
  - *Fix:* Write "For sample size n≥2 and pure replacement privacy budget 0<ε≤1" using the existing mathematical notation.

## Questions for authors
- Which feature should readers regard as the principal reusable methodological contribution: occupancy-weighted attainment under measurable design densities, the shared-sign privacy comparison, or their combination?
- Can the discussion distinguish more explicitly the interval frontier's theoretical value from the full-range output of the displayed procedure throughout the stated finite-sample range?

