# Referee review

**Recommendation:** major_revision
**Overall score:** 7.4/10 — The verified characterization makes a substantial theoretical contribution with careful scope control, but extensive repetition and formal bookkeeping require substantial editorial restructuring for journal publication.

The paper establishes the sharp pointwise CATE minimax absolute-error rate for independent labeled and outcome-free covariate-treatment samples under known uniform design, fixed overlap, and public Hölder regularity. Its principal contribution is the unequal-sample characterization, supported by an attaining rectangular estimator and an original-record lower bound, together with acquisition thresholds. The substantive prose generally represents the verified results faithfully and distinguishes the supervised numerical comparison from a source-model statistical guarantee. The main publication obstacle is an unnecessarily sprawling presentation that repeatedly states the same results and obscures their statistical contribution.

## Strengths
- The characterization covers every admissible sample imbalance and clearly separates the labeled-sample floor from the product-of-counts regime.
- The estimator guarantee applies throughout the specified primitive class with public tuning and explicit guarding and clipping.
- The original-record mixture construction supplies a lower bound for the actual known-uniform experiment, with its occupancy condition stated explicitly.
- The paper carefully distinguishes strict asymptotic improvement from attainment of the supplied-propensity order.
- The early related-work section engages competitors' targets, information structures, rates, and attainment conditions without transporting their guarantees to the present model.
- The acquisition interpretation preserves independent sampling when an auxiliary record is selected for labeling independently of its contents.

## Findings
- **[major·structure] Global; estimation; sharp precision; appendices** — The manuscript repeatedly defines identical rates and decisions, restates parameter lists and rate branches, and explains arguments before presenting them again in deferred proofs. The acquisition proposition reproduces much of the sharp-frontier theorem, while the appendix separates supporting arguments from main proofs with an intervening verification note. Extensive constant construction and elementary bookkeeping make the statistical ideas difficult to locate.
  - *Fix:* Restructure the exposition around one model definition, one estimator construction, the sharp characterization, and the acquisition consequences. Introduce the rate branches before the detailed estimator machinery. Retain each verified statement in one location, use cross-references elsewhere, and group each main proof with its supporting results. Move representation details and lengthy constant bookkeeping to a technical supplement while preserving every verified condition and conclusion.
- **[minor·prose] Sharp precision and sample requirements** — The sentence “This is a known-design polynomial evaluation average, not an empirical local least-squares fit” uses ordinary negative framing outside the limitations section.
  - *Fix:* Replace it with an affirmative description, such as: “This known-design smoother averages inverse-propensity pseudo-outcomes using the polynomial evaluation kernel determined by the uniform localization measure.”
- **[minor·citation] Setup and assumptions** — Several external attributions omit the required source locators, including the citations following uniform design, exchangeability, overlap, and the three smoothness discussions. The phrase “considered by \citep{KennedyBalakrishnanRobinsWasserman2024}” also produces an awkward parenthetical author attribution.
  - *Fix:* Identify the relevant source sections, assumptions, or theorem statements and attach accurate locators to these citations. Use \citet for grammatical author attributions, or rewrite the sentence so that a parenthetical citation follows a complete clause.
- **[minor·structure] Acquisition consequences and supervised comparison; verification note** — The acquisition proposition embeds a numerical identity at n=0 with negative powers of zero assigned value zero, despite the statistical experiment using n≥2. The coarse-basis definition likewise foregrounds division at h=0. These valid representation conventions interrupt the statistical exposition and invite readers to interpret implementation conventions as sample-size or bandwidth conclusions.
  - *Fix:* Present statistical consequences on their stated admissible domains and place the totalized conventions in the representation discussion or supplement. Preserve the complete checked identities there and provide a brief cross-reference where necessary.
- **[nit·prose] Related work** — The acronym CATE first appears in “supervised pointwise CATE estimation” without an explicit acronym expansion.
  - *Fix:* Introduce “conditional average treatment effect (CATE)” at its first occurrence and use the acronym consistently thereafter.

## Questions for authors
- Which aspects of the rectangular construction and original-record converse should readers regard as the principal methodological advance beyond the supervised projection architecture?
- Can the estimator exposition briefly explain how cellwise kernel support permits evaluation of the rectangular correction without explicitly enumerating every cross-role record pair?

