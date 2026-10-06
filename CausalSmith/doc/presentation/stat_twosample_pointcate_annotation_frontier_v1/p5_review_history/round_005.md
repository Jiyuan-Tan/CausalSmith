# Referee review

**Recommendation:** major_revision
**Overall score:** 7.4/10 — The verified minimax characterization provides a substantial theoretical contribution, but extensive repetition and several presentation and sampling-interpretation issues require revision for journal publication.

The paper establishes a sharp pointwise CATE absolute-error rate for independent labeled and outcome-free treatment records under known uniform design, fixed overlap, and public Hölder regularity. Its estimator, original-record converse, and acquisition thresholds deliver the advertised contribution, and the supervised comparison carefully respects differences between model classes. The principal revision concerns turning an extensively repetitive exposition into a focused statistical argument, with smaller repairs to acquisition interpretation and formal presentation.

## Strengths
- The unequal-sample minimax characterization covers every auxiliary count and distinguishes strict improvement from attainment of the supplied-propensity order.
- The explicit guarded estimator supplies finite-sample attainment under primitive-model conditions.
- The original-record mixture construction establishes the lower bound within the stipulated known-uniform class.
- The discussion of the closest supervised comparator distinguishes numerical rate agreement from source-model statistical guarantees.
- The acquisition consequences and numerical example accurately preserve parameter-dependent comparison constants and the stated smoothness regimes.

## Findings
- **[major·structure] Global organization, setup, estimation, and appendices** — Repeated definitions, parameter lists, rate displays, and proof roadmaps obscure the contribution. The role split appears twice in full; the sharp rate and its branches recur throughout the manuscript; the acquisition proposition repeats the minimax sandwich and supervised comparison; and the upper-bound appendix gives extended explanatory accounts before the full proofs appear again in the final appendix. Routine constant bookkeeping occupies substantial space relative to the statistical mechanisms.
  - *Fix:* Consolidate the public domain and rate notation, specify the role split once, and make subsequent objects refer to those definitions. Present the acquisition proposition around its sequence and target-error consequences. Organize each proof beside its supporting lemmas, retaining the approximation, cancellation, variance, and occupancy arguments while compressing repeated formulas and elementary constant comparisons. Preserve exact theorem conditions and the artifact crosswalk.
- **[minor·prose] Introduction and discussion and limitations** — The claim that “prespecifying the record, or selecting it independently of its observed covariates and treatment, preserves the stated sampling law” leaves the selection mechanism insufficiently specified. Independence from the candidate's covariates and treatment alone does not explicitly establish exogeneity with respect to its latent response or the joint record collection.
  - *Fix:* State a sufficient mechanism precisely: convert a fixed auxiliary index, or choose an index using randomization independent of the full record collection, with the conversion count fixed in advance. Tie the sampling-law preservation claim to that mechanism in both locations.
- **[minor·prose] Sharp precision and sample requirements** — The sentence “this is a known-design polynomial evaluation average, not an empirical local least-squares fit” uses explanatory negation outside the designated limitations subsection, contrary to the affirmative prose contract.
  - *Fix:* Replace it with an affirmative description, such as: “This known-design polynomial evaluation average uses the population design normalization and extends to bandwidths in (0,1].”
- **[minor·prose] Original-record lower bounds** — The closing sentence announces that “the rate and attaining decision are collected in the following ordered pair,” but the next paragraph and section contain no such pair. The handle appears later in the verification note.
  - *Fix:* Replace the announcement with a direct reference to \cref{obj:def:frontier-handle}, or remove the announcement and retain the existing references to the statistical results.
- **[minor·statement] Acquisition consequences and supervised comparison** — The annotation proposition breaks existential and eventual universal quantifiers onto separate alignment rows, making the scope of the equivalence chain difficult to parse. Its strict-benefit condition similarly separates the conjunction from the auxiliary-ratio limit.
  - *Fix:* Render eventual region membership as one complete clause, for example “there exists a finite ζ≥1 such that (n,m_n) belongs to the annotation region eventually.” Keep each equivalence operand and the complete strict-benefit conjunction visually grouped.
- **[minor·structure] Acquisition consequences and verification note** — The statistical acquisition proposition includes the representation convention assigning negative powers of zero the value zero, and its proof devotes a separate discussion to sample sizes zero and one. This distracts from the statistical domain n≥2 and duplicates the explanation already provided in the verification note.
  - *Fix:* Present the supervised comparison for n≥2 in the statistical exposition and retain the broader totalized identity as a clearly separated representation clause in the verification note or an artifact-facing supplement.

## Questions for authors
- What precise exogenous selection mechanism is intended when an existing auxiliary record is converted into a labeled record?

