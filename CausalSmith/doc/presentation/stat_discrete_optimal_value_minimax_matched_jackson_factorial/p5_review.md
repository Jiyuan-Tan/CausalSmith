# Referee review

**Recommendation:** major_revision
**Overall score:** 7.2/10 — The paper delivers a significant matched minimax characterization with a carefully specified estimator, but central verification claims and artifact metadata require correction before publication.

The paper establishes the finite-sample minimax squared-risk frontier for estimating the scalar unrestricted optimal-treatment value with binary treatment and outcome, growing discrete covariate support, and fixed overlap. Its principal contribution is a mathematically specified Jackson-factorial estimator paired with lower bounds obtained through an exact two-sample L1 embedding and moment matching. The verified statements support the headline rate, consistency boundary, parametric boundary, and causal-completion equivalence, but the manuscript currently overstates the status of its printed proofs and identifies an obsolete verification commit.

## Strengths
- The matched all-regime rate is a clear and potentially important contribution at the intersection of treatment choice, nonregular estimation, and large-alphabet functional estimation.
- The observed-law target, causal completion class, overlap conditions, and equality of observed and causal minimax risks are stated precisely.
- The paper engages the closest large-alphabet comparisons directly, including rate-level comparisons with two-sample L1 estimation and high-dimensional discrete causal adjustment.
- The estimator construction addresses unknown arm denominators, unequal propensities, null cells, boundary means, and treatment-effect ties within one uniform result.
- The theorem-local disclosures accurately identify the two published inputs on which the lower-bound certification depends.

## Findings
- **[major·other] Verification note** — The artifact metadata are stale: the manuscript identifies commit 603f7dc86a4e2a3229b27f104bedc7ca63e062a6, whereas the current verification contract is for commit 881a4d27aaf42f02b1f71128db9f0c6d2184c790. This prevents the reader from matching the submitted statements and audit receipts to the cited artifact.
  - *Fix:* Regenerate the verification appendix from the current artifact, cite commit 881a4d27aaf42f02b1f71128db9f0c6d2184c790, and recheck every accompanying toolchain, Mathlib-revision, source-scan, and axiom-audit claim against that commit.
- **[major·prose] global** — The author footnote says, "The displayed formal statements and proofs are Lean-verified," but the verification appendix correctly explains that the printed proofs are prose renderings and are not themselves kernel-checked objects. The current front-matter wording materially overstates the certification scope.
  - *Fix:* Replace the sentence with an exact account: the displayed formal statements correspond to Lean declarations whose underlying proofs are kernel-checked, while the printed proofs are audited prose renderings; retain the theorem-local disclosures for published inputs.
- **[minor·prose] Introduction** — The claims that the estimator is "written out in closed form" and that every ingredient yields a "complete statistical specification" blur mathematical definition and computational evaluation. The construction still requires extracting coefficients from a tensor convolution and evaluating an exact Rao--Blackwell expectation over auxiliary randomization.
  - *Fix:* Describe the result as a fully specified decision-theoretic estimator rather than a closed-form computational procedure. If practical computability is intended as part of the contribution, supply coefficient-extraction and finite Rao--Blackwell evaluation pseudocode with a complexity discussion.
- **[minor·prose] Related work** — The sentence "This paper inherits their converse and nothing else" violates the affirmative contribution-framing contract and is unnecessarily categorical given the acknowledged shared approximation and factorial-moment lineage.
  - *Fix:* Rewrite affirmatively, for example: "The present lower bound transfers their converse through the equal-propensity embedding, while the upper bound constructs a pilot-adaptive four-coordinate estimator for the observational cell table."
- **[minor·statement] Discussion and limitations** — The first clause of the parent-reduction proposition is titled "Matched frontier" even though its displayed predecessor bounds do not match. The following paragraph must then explain that the title does not mean what readers naturally infer.
  - *Fix:* Rename the clause "Implied predecessor bracket" or "Recovery of the predecessor bounds," and rename the proposition accordingly if appropriate. State positively that the matched theorem implies this earlier bracket.
- **[minor·citation] Related work** — The rate-level descriptions of Jiao--Han--Weissman and Zeng et al. lack pinpoint locators. In particular, the Jiao--Han--Weissman paragraph presents the d/[n log(en)] obstruction without stating the sampling and regime gates recorded for the published input.
  - *Fix:* Verify the cited results and add theorem, equation, or section locators to both rate comparisons. State the Poissonized sample convention and applicable large-alphabet gates for the Jiao--Han--Weissman lower bound, while distinguishing those source conditions from the additional arguments that produce this paper's all-regime theorem.
- **[minor·statement] Main results** — The equal-propensity reduction is introduced with arbitrary objects P0 and mu_n whose sampling relation is unrelated to the embedded law subsequently denoted by P. Although the verified implication is true, these unused reader-facing arguments obscure the experiment comparison.
  - *Fix:* Present a clean corollary under the standing canonical product-sampling convention, or add an explicit sentence explaining that P0 and mu_n serve only to instantiate the global sampling interface and play no role in the embedding.
- **[minor·structure] global** — The manuscript contains several duplicated or elementary displayed definitions, notably the two versions of the L1 embedding and the separate repetitions of the Jackson kernel, good-pilot event, and basic risk notation. Together with full-length renderings of highly mechanical proofs, this obscures the main econometric argument.
  - *Fix:* Consolidate duplicate definitions, move elementary notation into running prose, and place the most mechanical verification-oriented derivations in a clearly identified supplemental appendix while retaining the estimator logic and substantive lower-bound argument in the paper.

## Questions for authors
- Do the authors intend the Jackson-factorial estimator as a computationally implementable procedure, or solely as an explicit decision-theoretic construction?
- Will the deposited Lean artifact and the final manuscript be pinned to the same current commit, toolchain, and Mathlib revision?
- Can the authors state precisely which regimes of the cited two-sample L1 theorem are used directly and which regimes are supplied by their own dense and two-point arguments?

