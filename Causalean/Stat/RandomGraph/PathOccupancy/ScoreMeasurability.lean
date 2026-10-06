module
public import Causalean.Stat.RandomGraph.PathOccupancy.Components
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Measurability and integrability of finite component scores

A random relation is encoded by finitely many Boolean edge indicators. Every
component statistic then factors through a finite measurable vector of edges,
cells, and marks. This proves measurability and integrability without restricting
how the relation depends on cells, marks, or additional randomness.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.RandomGraph.PathOccupancy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- [Measurable edge events](hyp:hR) of [a random finite relation](hyp:R)
give [a measurable component partition](goal).

Encode the relation by the Boolean vector `fun i j => decide (R ω i j)`.
Each coordinate is measurable by measurable_to_bool and hR; apply
measurable_pi_lambda twice. Any map from this finite discrete vector space to
the finite space of partitions is measurable. Decode each bit as equality to
true, then use propext to identify the decoded relation with R. No path-length
bound or extra measurable reachability hypothesis is necessary. -/
theorem measurable_components {n : ℕ} (R : Ω → Fin n → Fin n → Prop)
    (hR : ∀ i j, MeasurableSet {ω | R ω i j}) :
    Measurable (fun ω => components (R ω)) := by
  classical
  let edges : Ω → Fin n → Fin n → Bool := fun ω i j => decide (R ω i j)
  have hedges : Measurable edges := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    apply measurable_to_bool
    convert hR i j using 1
    ext ω
    simp [edges]
  have hdecode : ∀ ω, (fun i j => edges ω i j = true) = R ω := by
    intro ω
    funext i j
    apply propext
    simp [edges]
  have hpartition :=
    (measurable_of_finite (fun e : Fin n → Fin n → Bool =>
      components (fun i j => e i j = true))).comp hedges
  simpa only [Function.comp_def, hdecode] using hpartition

/-- [Measurable edge events and marks](hyp:hR,hB) on [a finite-measure
space](hyp:μ) make [the random single-component score integrable](goal),
for [the supplied relation and marking](hyp:R,B).

Factor through the measurable component partition and the measurable finite
mark vector. The resulting real score has finite range. It is bounded by the
maximum of the norms over that finite range; use Integrable.mono' with an
integrable constant, or SimpleFunc.integrable_of_isFiniteMeasure. There is no
locality or independence assumption in this analytic fact.
-/
theorem integrable_singleScore {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : Ω → Fin n → Fin n → Prop) (B : Fin n → Ω → Bool)
    (hR : ∀ i j, MeasurableSet {ω | R ω i j})
    (hB : ∀ i, Measurable (B i)) :
    Integrable (fun ω => singleScore (R ω) (fun i => B i ω)) μ := by
  classical
  let score : Finset (Finset (Fin n)) × (Fin n → Bool) → ℝ :=
    fun p => ∑ C ∈ p.1, singleWeight C p.2
  have hinput : Measurable (fun ω => (components (R ω), fun i => B i ω)) :=
    (measurable_components R hR).prodMk (measurable_pi_lambda _ hB)
  exact ((SimpleFunc.ofFinite score).comp _ hinput).integrable_of_isFiniteMeasure

/-- [Measurable edge events, cells, and marks](hyp:hR,hX,hB) on
[a finite-measure space](hyp:μ) make [the random paired-component score
integrable](goal), for [coarse count, relation, cells, and marks](hyp:M,R,X,B).

Factor through the component partition, the finite cell vector, and the finite
mark vector. Any real statistic of that finite discrete tuple is measurable and
bounded. This includes the shared-envelope indicator even when the random
relation depends on the marks. Reuse the finite-range argument of
integrable_singleScore rather than deriving any distributional formula.
-/
theorem integrable_pairedScore {n K : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (M : ℕ) (R : Ω → Fin n → Fin n → Prop)
    (X : Fin n → Ω → Fin K) (B : Fin n → Ω → Bool)
    (hR : ∀ i j, MeasurableSet {ω | R ω i j})
    (hX : ∀ i, Measurable (X i)) (hB : ∀ i, Measurable (B i)) :
    Integrable (fun ω => pairedScore M (R ω) (fun i => X i ω)
      (fun i => B i ω)) μ := by
  classical
  let score : Finset (Finset (Fin n)) × ((Fin n → Fin K) × (Fin n → Bool)) → ℝ :=
    fun p => (1 / 2 : ℝ) * ∑ C ∈ p.1,
      ∑ D ∈ p.1.erase C, pairWeight M C D p.2.1 p.2.2
  have hinput : Measurable (fun ω =>
      (components (R ω), (fun i => X i ω, fun i => B i ω))) :=
    (measurable_components R hR).prodMk
      ((measurable_pi_lambda _ hX).prodMk (measurable_pi_lambda _ hB))
  exact ((SimpleFunc.ofFinite score).comp _ hinput).integrable_of_isFiniteMeasure

end Causalean.Stat.RandomGraph.PathOccupancy
