# Substrate requirement: finite-side-information-minimax-convergence

## Goal
Build axiom-clean reusable finite decision-theory substrate proving convergence from empirical finite side information to an exactly observed side-law vector.

## Provides (API contract)
- `finiteSideInfo_minimax_tendsto`: for a compact parameter space, finite labeled and nonempty side alphabets, continuous probability coordinates, and a continuous bounded real target, the bounded squared-loss minimax values based on labeled data plus `m` iid side observations tend as `m → ∞` to the benchmark minimax value based on the labeled data plus the exact side-law vector.
- A compact coordinate-simplex representation for probability mass functions on a finite type, with continuous atom coordinates and continuous finite product probabilities.
- Continuity and boundedness lemmas for finite squared risks.
- Specialization lemmas for a parameter space that is a closed subset of a finite simplex.

## Statement / milestones
Let `Theta` be compact, `X` a finite labeled alphabet, and `C` a finite nonempty side alphabet. Let `p : Theta → X → Real` and `q : Theta → C → Real` be continuous probability coordinates and let `tau : Theta → Real` be continuous and bounded. Define the bounded squared-loss minimax value when the procedure observes the labeled outcome together with `m` iid draws from `q theta`, and the benchmark value when it instead observes the exact vector `q theta`. Prove that the former tends along `Nat.atTop` to the latter.

The proof must supply the full reusable chain: exact-`q` simulation and squared-loss conditional averaging for the lower comparison; compact shrinking-fiber local-minimax convergence; finite-cover approximate decision selection measurable in the empirical side vector; a uniform finite-category empirical L1 tail from Hoeffding and a union bound; and the liminf/limsup assembly.

## Standard reference
Standard compact statistical decision theory: comparison of experiments, Rao–Blackwell conditional averaging under convex squared loss, compactness/finite-cover arguments, and finite-alphabet empirical concentration via Hoeffding. No paper-specific theorem may be assumed.

## Intended reuse
The immediate consumer is the known-marginal limiting theorem in `stat_semisupervised_discrete_ate_annotation_frontier/v1`. The shared declarations must remain paper-independent. The run-local specialization will encode its discrete-law coordinates, closed overlap-constrained model class, ATE continuity at null cells, finite-sum risks, and auxiliary empirical table.

## May assume / must derive
May assume compactness of `Theta`, finiteness/nonemptiness of the alphabets, continuity and probability-simplex validity of `p` and `q`, and continuity/boundedness of `tau`. Must derive the PMF simplex compactness/continuity API, risk continuity, shrinking-fiber minimax interchange, measurable finite-cover selector, exact-side comparison, empirical L1 concentration, and convergence theorem. All public results must have zero `sorry`, use no `admit`, and introduce no axioms.

## Non-goals (optional)
Do not import any `CausalSmith/*_Research` module. Do not encode the paper's `DiscreteLaw`, overlap inequalities, `ateFunctional`, `auxTableOf`, or annotation experiment; those are run-local prerequisites and specializations after promotion. Do not weaken the main result to a conditional gate or one-sided bound.

## Known building blocks (optional)
Search and reuse `Causalean.Stat.Minimax.FiniteSquaredLoss.Core`, `Causalean.Stat.Minimax.MinimaxValue`, `Causalean.Stat.Concentration.TailBounds.Hoeffding`, `Causalean.Stat.FiniteSquaredLoss.isCompact_procedureSet`, `Causalean.Stat.FiniteSquaredLoss.continuous_rawRisk`, `Causalean.Stat.Concentration.hoeffding_abs_ge`, `Mathlib.Probability.ProbabilityMassFunction.Constructions`, `Mathlib.Topology.MetricSpace.Compact`, and `Mathlib.MeasureTheory.Integral.Bochner.Basic`. Generic `ProbabilityTheory.minimaxRisk` and Hoeffding alone do not already provide the required compact-fiber minimax interchange.
