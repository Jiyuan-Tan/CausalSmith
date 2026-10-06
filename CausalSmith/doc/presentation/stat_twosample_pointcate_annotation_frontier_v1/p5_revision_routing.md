# Revision routing plan (major_revision)

## fix by hand in the authored sources (prose/structure rewrite)
- [major·structure·rewrite] (Global; estimation; sharp precision; appendices) The manuscript repeatedly defines identical rates and decisions, restates parameter lists and rate branches, and explains arguments before presenting them again in deferred proofs. The acquisition proposition reproduces much of the sharp-frontier theorem, while the appendix separates supporting arguments from main proofs with an intervening verification note. Extensive constant construction and elementary bookkeeping make the statistical ideas difficult to locate.
- [minor·prose·rewrite] (Sharp precision and sample requirements) The sentence “This is a known-design polynomial evaluation average, not an empirical local least-squares fit” uses ordinary negative framing outside the limitations section.
- [minor·structure·rewrite] (Acquisition consequences and supervised comparison; verification note) The acquisition proposition embeds a numerical identity at n=0 with negative powers of zero assigned value zero, despite the statistical experiment using n≥2. The coarse-basis definition likewise foregrounds division at h=0. These valid representation conventions interrupt the statistical exposition and invite readers to interpret implementation conventions as sample-size or bandwidth conclusions.
- [nit·prose·rewrite] (Related work) The acronym CATE first appears in “supervised pointwise CATE estimation” without an explicit acronym expansion.

## escalate — out of causalsmith scope (bank/causalsmith)
- [minor·citation·citation_research] (Setup and assumptions) Several external attributions omit the required source locators, including the citations following uniform design, exchangeability, overlap, and the three smoothness discussions. The phrase “considered by \citep{KennedyBalakrishnanRobinsWasserman2024}” also produces an awkward parenthetical author attribution.

→ revise by hand at the level that owns each finding; formal statements remain frozen; then rescore once
