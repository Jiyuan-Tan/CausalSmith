# Revision routing plan (major_revision)

## escalate — out of causalsmith scope (bank/causalsmith)
- [major·structure·new_theorem] (Dense and sparse variance behavior) The principal asymptotic theorems repeatedly present the Johnson decomposition and Kneser spectrum as long theorem hypotheses even though the manuscript later proves that the canonical projections satisfy them automatically. This obscures the substantive assumptions and makes the main contribution appear conditional on reader-supplied spectral structure.
- [major·statement·rewrite] (Setup and assumptions) The population labeling is internally inconsistent. The feasible schedule definition uses units in {0,…,n_r−1}, while the random-partition, slice, and Johnson definitions use {1,…,n}. As written, the schedule domain and the groups in Ω_{n,M} are not literally the same finite set.
- [major·statement·rewrite] (One-realization lower bound) The central mixture display writes E_{H_n}E_{Z_n}{φ(O_n)} even though O_n also contains the random group tuple A_n. The lower-bound theorem then writes a supremum over Y in C_dense while its construction begins from a fixed design skeleton A; the domain of the statistic and the quantities held fixed in this supremum are therefore unclear to the reader.
- [minor·statement·rewrite] (Software identity and finite witness) The displayed definition of the eight-unit witness introduces only a “balanced sign vector” and supplies its actual coordinates several paragraphs later, after discussion of the software proposition. The formal object is therefore incomplete at its point of definition for a reader.

## fix by hand in the authored sources (prose/structure rewrite)
- [major·prose·rewrite] (Proofs and auxiliary lemmas) The verification note states, “Every theorem, proposition, and assumption displayed in this paper … is machine-checked … with no unproved hypotheses.” Assumptions are formalized conditions rather than established facts, and the software proposition depends on two externally sourced implementation contracts. The later qualifications improve the account but leave the opening sentence materially overbroad.
- [minor·prose·rewrite] (global) The manuscript repeatedly calls a fixed-count complete assignment “balanced,” including designs with p converging to any interior value rather than one half. This can be read as equal allocation, which is imposed only in the eight-unit witness.
- [minor·prose·rewrite] (Related work) The sentence “its subject is the variance object itself … and Section … records what a complete inference theory would still require” frames the comparison partly through an absent inferential deliverable outside the designated limitations subsection. The later phrase “quantify the resulting gap rather than repairing the adjustment” uses the same contrastive framing.
- [minor·prose·rewrite] (abstract) The lower-bound formula first uses p in 1/[Mp(1−p)]−2ρ/M without identifying it in plain words, contrary to the first-use gloss rule. The sentence also makes the fixed treatment-fraction parameter less visible than M, ρ, B, and c_σ.
- [nit·structure·rewrite] (Proofs and auxiliary lemmas) The appendix begins with an unnumbered “Appendices” heading immediately followed by the numbered section “Proofs and auxiliary lemmas,” and it repeats the slice, norm, and Johnson–Kneser apparatus already defined in the setup.

## your call — orchestrator decides
- [minor·citation·rewrite] (Related work) The closest-comparator discussion gives the locator as prose—“their Section 3 and Theorems 1–2”—rather than attaching it to the citation command, weakening precise source attribution.

→ revise by hand at the level that owns each finding; formal statements remain frozen; then rescore once
