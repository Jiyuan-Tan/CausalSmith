# Referee review

**Recommendation:** major_revision
**Overall score:** 6.8/10 — The paper delivers a potentially important and formally verified variance characterization, phase frontier, software identity, and impossibility result, but central notation and theorem presentation require substantial repair before the contribution is journal-ready.

The submission characterizes exact and asymptotic variance under homogeneous random group formation using Johnson–Kneser geometry, identifies the probability target of equal-group CR2, and establishes a positive-density one-realization lower bound. The verified results are strong and the manuscript generally represents their scope faithfully. Publication nevertheless requires clearer reader-facing corollaries, consistent population indexing, an explicit probability space for the lower bound, and a more precise verification-scope statement.

## Strengths
- The exact Kneser covariance and PAME variance identities give a coherent finite-population account of dependence from disjoint group formation.
- The dense expansion isolates an interpretable degree-one correction and yields an exact ratio-consistency criterion for the scalar CR2 statistic.
- The zero-density result clearly distinguishes the variance-estimation rate N_n/n from the stronger whole-tuple condition discussed in the closest comparator.
- The versioned software identity and eight-unit witness connect the abstract variance geometry to an applied regression calculation.
- The Rademacher construction supports a substantively valuable minimax obstruction over the bounded positive-density schedule class.
- The related-work section appears early and engages the closest group-formation, cluster-robust, interference, and variance-nonidentification literatures.

## Findings
- **[major·structure] Dense and sparse variance behavior** — The principal asymptotic theorems repeatedly present the Johnson decomposition and Kneser spectrum as long theorem hypotheses even though the manuscript later proves that the canonical projections satisfy them automatically. This obscures the substantive assumptions and makes the main contribution appear conditional on reader-supplied spectral structure.
  - *Fix:* Retain the gate-form verified results in the appendix, but add machine-checked corollaries for the canonical Johnson projections whose hypotheses contain only feasibility, group growth, stable treatment fraction, sampling fraction, boundedness, and—where needed—the scaled-variance floor. Use those corollaries as the main-text phase-frontier and sparse results.
- **[major·statement] Setup and assumptions** — The population labeling is internally inconsistent. The feasible schedule definition uses units in {0,…,n_r−1}, while the random-partition, slice, and Johnson definitions use {1,…,n}. As written, the schedule domain and the groups in Ω_{n,M} are not literally the same finite set.
  - *Fix:* Choose one labeling convention globally and rewrite every occurrence of the unit universe, membership subtype, and Ω_{n,M} accordingly. A brief statement that all finite populations are identified with [n] would eliminate the mismatch.
- **[major·statement] One-realization lower bound** — The central mixture display writes E_{H_n}E_{Z_n}{φ(O_n)} even though O_n also contains the random group tuple A_n. The lower-bound theorem then writes a supremum over Y in C_dense while its construction begins from a fixed design skeleton A; the domain of the statistic and the quantities held fixed in this supremum are therefore unclear to the reader.
  - *Fix:* Define one joint design expectation that explicitly integrates over both the random group tuple and treatment allocation, and use it throughout the mixture argument. State whether the minimax supremum ranges over schedules compatible with the fixed population/group-count skeleton or over complete arrays with varying skeletons, and define the statistic family on that exact observation space.
- **[major·prose] Proofs and auxiliary lemmas** — The verification note states, “Every theorem, proposition, and assumption displayed in this paper … is machine-checked … with no unproved hypotheses.” Assumptions are formalized conditions rather than established facts, and the software proposition depends on two externally sourced implementation contracts. The later qualifications improve the account but leave the opening sentence materially overbroad.
  - *Fix:* State that the internal Lean declarations and derivations are sorry-free, that displayed assumptions are formally encoded, and that the software identity is verified conditional on the two versioned source contracts identified in its formalization-scope footnote.
- **[minor·prose] global** — The manuscript repeatedly calls a fixed-count complete assignment “balanced,” including designs with p converging to any interior value rather than one half. This can be read as equal allocation, which is imposed only in the eight-unit witness.
  - *Fix:* Use “complete fixed-count group assignment” or “fixed-arm-count assignment” in the general theory, reserving “balanced” for G_{1n}=G_{0n}.
- **[minor·statement] Software identity and finite witness** — The displayed definition of the eight-unit witness introduces only a “balanced sign vector” and supplies its actual coordinates several paragraphs later, after discussion of the software proposition. The formal object is therefore incomplete at its point of definition for a reader.
  - *Fix:* Put a_i=+1 for i≤4 and a_i=−1 for i≥5 directly inside the witness definition, and place the definition immediately before the witness proposition.
- **[minor·prose] Related work** — The sentence “its subject is the variance object itself … and Section … records what a complete inference theory would still require” frames the comparison partly through an absent inferential deliverable outside the designated limitations subsection. The later phrase “quantify the resulting gap rather than repairing the adjustment” uses the same contrastive framing.
  - *Fix:* Describe the delivered scope affirmatively—for example, exact variance characterization, CR2 probability limits, and the variance-ratio frontier—and keep discussion of Gaussian approximation and studentized inference in the existing Limitations and future work subsection.
- **[minor·prose] abstract** — The lower-bound formula first uses p in 1/[Mp(1−p)]−2ρ/M without identifying it in plain words, contrary to the first-use gloss rule. The sentence also makes the fixed treatment-fraction parameter less visible than M, ρ, B, and c_σ.
  - *Fix:* Introduce p as the limiting treated-group fraction when it first appears and list it among the fixed lower-bound parameters.
- **[minor·citation] Related work** — The closest-comparator discussion gives the locator as prose—“their Section 3 and Theorems 1–2”—rather than attaching it to the citation command, weakening precise source attribution.
  - *Fix:* Use a locator-bearing citation such as \citet[Section 3, Theorems 1--2]{FuSamiiWang2026} and apply the same convention to other theorem-level external comparisons.
- **[nit·structure] Proofs and auxiliary lemmas** — The appendix begins with an unnumbered “Appendices” heading immediately followed by the numbered section “Proofs and auxiliary lemmas,” and it repeats the slice, norm, and Johnson–Kneser apparatus already defined in the setup.
  - *Fix:* Remove the redundant heading and consolidate repeated definitions into a short notation recap that points back to the setup.

## Questions for authors
- In the Rademacher mixture proposition, is the inner expectation intended to integrate over the full random-partition design or only treatment assignment conditional on a realized partition?
- For the final minimax risk, which design-skeleton quantities are fixed across the supremum, and which components of the triangular array may vary?

