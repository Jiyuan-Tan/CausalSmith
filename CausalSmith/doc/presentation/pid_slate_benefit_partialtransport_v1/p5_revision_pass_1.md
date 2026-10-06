# Holistic revision pass 1

- mode: reframe
- source digest before: `eecce1a572fdc11dfe5ad011dbcd531d8450b08bee7f906fc5310558a187de66`
- source digest after: `de2cb35daed48aeea05f878109d5421212ed343f37848d34233f7760041551c5`

## Reviser report

Implemented the P5 reframe pass in the authored sources.

**Changed**
- [front_matter.tex](<repo-root>/CausalSmith/doc/presentation/pid_slate_benefit_partialtransport_v1/.p5_revision_workspace/front_matter.tex): tightened abstract inference conditions and added the observed-law-to-transport roadmap.
- [sections/01_related_work.tex](<repo-root>/CausalSmith/doc/presentation/pid_slate_benefit_partialtransport_v1/.p5_revision_workspace/sections/01_related_work.tex): repaired contribution-by-negation wording.
- [sections/02_setup_and_assumptions.tex](<repo-root>/CausalSmith/doc/presentation/pid_slate_benefit_partialtransport_v1/.p5_revision_workspace/sections/02_setup_and_assumptions.tex): added a section roadmap around the fixed formal setup.
- [sections/03_sharp_benefit_bounds.tex](<repo-root>/CausalSmith/doc/presentation/pid_slate_benefit_partialtransport_v1/.p5_revision_workspace/sections/03_sharp_benefit_bounds.tex): reframed endpoint-attainment prose affirmatively.
- [sections/04_computation_and_witness.tex](<repo-root>/CausalSmith/doc/presentation/pid_slate_benefit_partialtransport_v1/.p5_revision_workspace/sections/04_computation_and_witness.tex): smoothed implementation framing.
- [sections/05_estimation_and_guarded_inference.tex](<repo-root>/CausalSmith/doc/presentation/pid_slate_benefit_partialtransport_v1/.p5_revision_workspace/sections/05_estimation_and_guarded_inference.tex): explicitly enumerated guard events, added \(|\mathcal E|=|\mathcal X|(4K+3)\), and separated implementable inputs from \(\delta_n\)’s proof role.
- [sections/07_appendix.tex](<repo-root>/CausalSmith/doc/presentation/pid_slate_benefit_partialtransport_v1/.p5_revision_workspace/sections/07_appendix.tex): replaced the generic appendix heading with a descriptive one.

**Findings**
Addressed: `guard-conditions-understated`, `negative-contribution-framing`, `duplicate-appendix-hierarchy`.

Partially repaired but declined the formal-body part: `guard-algorithm-oracle-mixing` and `formal-scaffolding-obscures-argument`. Moving \(\delta_n\) out of the anchored guarded-confidence-set environment, consolidating potential-outcome definitions, and moving formal cost/support objects to an appendix would change frozen formal environments or their fixed placement, so those pieces need upstream outline/formal-layer work.

Outside-scope residuals remain as routed: closest-competitor citation positioning, observable capacity contrast formulas, executable threshold-flow pseudocode/witness matrices, uniform-class definition, open-question calibration statement, direction-margin positivity, and observed-outcome encoding.

Verification: ran source grep checks for forbidden cross-reference forms and prose patterns; compiled a temporary TeX driver against the edited authored sources with `pdflatex` successfully. The temporary driver omitted the bibliography, so natbib citation warnings were expected; there were no fatal TeX errors.
