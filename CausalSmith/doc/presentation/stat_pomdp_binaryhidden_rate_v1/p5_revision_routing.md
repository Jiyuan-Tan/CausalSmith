# Revision routing plan (minor_revision)

## fix by hand in the authored sources (prose/structure rewrite)
- [minor·prose·rewrite] (Main results — paragraph preceding the minimax risk definition) The sentence 'The supremum ranges over the binary experiment class ... with those supplied inputs' suggests that the supremum fixes the behavior and target policies. Elsewhere, the class allows both policies to vary, with each experiment supplying its own pair to an indexed estimator. These are different decision problems.
- [minor·structure·rewrite] (Main results — fixed binary minimax rate; Discussion; appendices) The central theorem combines the binary risk bound, extensive testing-witness details, and a lengthy externally sourced cardinality comparison. Repeated explanations of the seven moments, contraction mechanism, testing pair, and candidate counts across subsequent sections dilute the main statistical contribution.
- [minor·prose·rewrite] (Introduction) The sentence 'this is a candidate-count statement, not a runtime bound' explains the contribution through an absent deliverable outside the limitations section, contrary to the affirmative framing contract.

## escalate — out of causalsmith scope (bank/causalsmith)
- [minor·statement·rewrite] (Appendix — pair-polynomial identity and value modulus) The lemma calls all six vectors, including the reward vectors, 'real row vectors,' while the setup and neighboring exposition use rewards as columns in scalar matrix products. The coordinate-sum interpretation resolves the mathematics but leaves conflicting orientation instructions.

→ revise by hand at the level that owns each finding; formal statements remain frozen; then rescore once
