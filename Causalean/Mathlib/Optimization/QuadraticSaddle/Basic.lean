module
public import Mathlib

/-!
# Finite parametric quadratic saddle problems

This module defines fixed compact polytopes, finite families of parameterized convex scalar
quadratics, their max-min value, and the maximum envelope.  It proves the Borel and pointwise
facts that support an exact measurable saddle-point selector.
-/

@[expose] public section

noncomputable section

namespace Causalean.Mathlib.Optimization.QuadraticSaddle

variable {Θ ι κ : Type*} [MeasurableSpace Θ] [Fintype ι] [Fintype κ]

/-- A [finite coordinate set](hyp:ι) and [finite equality-index set](hyp:κ) determine a
nonempty compact polytope of nonnegative weight vectors satisfying fixed linear equalities. -/
structure Polytope (ι κ : Type*) [Fintype ι] [Fintype κ] where
  A : κ → ι → ℝ
  b : κ → ℝ
  compact : IsCompact {α : EuclideanSpace ℝ ι |
    (∀ i, 0 ≤ α i) ∧ ∀ j, (∑ i, A j i * α i) = b j}
  nonempty : Set.Nonempty {α : EuclideanSpace ℝ ι |
    (∀ i, 0 ≤ α i) ∧ ∀ j, (∑ i, A j i * α i) = b j}

/-- A [fixed compact polytope](hyp:P) has a [feasible weight set](goal) consisting of its
nonnegative vectors that satisfy every defining linear equality. -/
def Polytope.weights (P : Polytope ι κ) : Set (EuclideanSpace ℝ ι) :=
  {α | (∀ i, 0 ≤ α i) ∧ ∀ j, (∑ i, P.A j i * α i) = P.b j}

/-- The [feasible weight set](goal) of a [fixed compact polytope](hyp:P) is Borel. -/
theorem Polytope.measurableSet_weights (P : Polytope ι κ) :
    MeasurableSet P.weights := by
  exact P.compact.measurableSet

/-- A [parameter space](hyp:Θ) and [finite coordinate set](hyp:ι) determine Borel
coefficient fields with nonnegative quadratic terms for one convex scalar quadratic per
coordinate. -/
structure Quadratics (Θ ι : Type*) [MeasurableSpace Θ] [Fintype ι] where
  a : ι → Θ → ℝ
  b : ι → Θ → ℝ
  c : ι → Θ → ℝ
  measurable_a : ∀ i : ι, Measurable (a i)
  measurable_b : ∀ i : ι, Measurable (b i)
  measurable_c : ∀ i : ι, Measurable (c i)
  nonneg_a : ∀ (θ : Θ) (i : ι), 0 ≤ a i θ

/-- A [quadratic family](hyp:Q), [parameter](hyp:θ), [weight vector](hyp:α), and [scalar
decision](hyp:t) determine the [finite weighted quadratic objective](goal): the sum over
coordinates of the weight times that coordinate's quadratic a·t² + b·t + c evaluated at the
parameter. -/
def Quadratics.objective (Q : Quadratics Θ ι)
    (θ : Θ) (α : EuclideanSpace ℝ ι) (t : ℝ) : ℝ :=
  ∑ i, α i * (Q.a i θ * t ^ 2 + Q.b i θ * t + Q.c i θ)

/-- A [quadratic family](hyp:Q) has a [jointly Borel quadratic objective](goal) in the
parameter, finite weight vector, and scalar decision. -/
theorem Quadratics.measurable_objective (Q : Quadratics Θ ι) :
    Measurable (fun x : Θ × (EuclideanSpace ℝ ι × ℝ) =>
      Q.objective x.1 x.2.1 x.2.2) := by
  unfold Quadratics.objective
  apply Finset.measurable_sum
  intro i hi
  have hθ : Measurable (fun x : Θ × (EuclideanSpace ℝ ι × ℝ) => x.1) :=
    measurable_fst
  have hα : Measurable (fun x : Θ × (EuclideanSpace ℝ ι × ℝ) => x.2.1 i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp
      (measurable_fst.comp measurable_snd)
  have ht : Measurable (fun x : Θ × (EuclideanSpace ℝ ι × ℝ) => x.2.2) :=
    measurable_snd.comp measurable_snd
  exact hα.mul (((((Q.measurable_a i).comp hθ).mul (ht.pow_const 2)).add
    (((Q.measurable_b i).comp hθ).mul ht)).add ((Q.measurable_c i).comp hθ))

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [parameter](hyp:θ), [weight
vector](hyp:α), and [scalar decision](hyp:t) [form a saddle pair](goal) when the weight is
feasible, the scalar globally minimizes its weighted quadratic, and the weight maximizes the
objective at that scalar. -/
def IsSaddle (P : Polytope ι κ) (Q : Quadratics Θ ι)
    (θ : Θ) (α : EuclideanSpace ℝ ι) (t : ℝ) : Prop :=
  α ∈ P.weights ∧
  (∀ u : ℝ, Q.objective θ α t ≤ Q.objective θ α u) ∧
  ∀ β ∈ P.weights, Q.objective θ β t ≤ Q.objective θ α t

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), and [parameter](hyp:θ) determine
the [real max-min value](goal), the supremum of all attained weighted-quadratic minima. -/
def value (P : Polytope ι κ) (Q : Quadratics Θ ι) (θ : Θ) : ℝ :=
  sSup {j : ℝ | ∃ α ∈ P.weights, ∃ t : ℝ,
    Q.objective θ α t = j ∧
    ∀ u : ℝ, Q.objective θ α t ≤ Q.objective θ α u}

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [parameter](hyp:θ), [weight
vector](hyp:α), and [scalar decision](hyp:t) whose [pair is a saddle](hyp:h) have an
[objective equal to the max-min value](goal). -/
theorem value_eq_of_isSaddle (P : Polytope ι κ) (Q : Quadratics Θ ι)
    (θ : Θ) (α : EuclideanSpace ℝ ι) (t : ℝ)
    (h : IsSaddle P Q θ α t) :
    value P Q θ = Q.objective θ α t := by
  let S : Set ℝ := {j : ℝ | ∃ β ∈ P.weights, ∃ u : ℝ,
    Q.objective θ β u = j ∧ ∀ v : ℝ, Q.objective θ β u ≤ Q.objective θ β v}
  have hmem : Q.objective θ α t ∈ S := ⟨α, h.1, t, rfl, h.2.1⟩
  have hub : ∀ j ∈ S, j ≤ Q.objective θ α t := by
    rintro j ⟨β, hβ, u, rfl, hu⟩
    exact (hu t).trans (h.2.2 β hβ)
  have hbdd : BddAbove S := ⟨Q.objective θ α t, hub⟩
  change sSup S = Q.objective θ α t
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup hbdd hmem)

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [parameter](hyp:θ), [weight
vector](hyp:α), and [scalar decision](hyp:t) whose [pair is a saddle](hyp:h) have a [real
max-min value equal to the extended-real max-min expression](goal), including unbounded-below
competitors. -/
theorem value_eq_extended_maxMin (P : Polytope ι κ) (Q : Quadratics Θ ι)
    (θ : Θ) (α : EuclideanSpace ℝ ι) (t : ℝ)
    (h : IsSaddle P Q θ α t) :
    (value P Q θ : EReal) =
      ⨆ (β : {β : EuclideanSpace ℝ ι // β ∈ P.weights}),
        ⨅ (u : ℝ), (Q.objective θ β.1 u : EReal) := by
  rw [value_eq_of_isSaddle P Q θ α t h]
  apply le_antisymm
  · calc
      (Q.objective θ α t : EReal) ≤
          ⨅ (u : ℝ), (Q.objective θ α u : EReal) :=
        le_iInf fun u => by exact_mod_cast h.2.1 u
      _ ≤ ⨆ (β : {β : EuclideanSpace ℝ ι // β ∈ P.weights}),
          ⨅ (u : ℝ), (Q.objective θ β.1 u : EReal) :=
        le_iSup (fun β : {β : EuclideanSpace ℝ ι // β ∈ P.weights} =>
          ⨅ (u : ℝ), (Q.objective θ β.1 u : EReal)) ⟨α, h.1⟩
  · refine iSup_le fun β => ?_
    calc
      (⨅ (u : ℝ), (Q.objective θ β.1 u : EReal)) ≤
          (Q.objective θ β.1 t : EReal) := iInf_le _ t
      _ ≤ (Q.objective θ α t : EReal) := by
        exact_mod_cast h.2.2 β.1 β.2

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [parameter](hyp:θ), and [scalar
decision](hyp:t) determine the [maximum envelope](goal) obtained by maximizing the objective
over feasible weights. -/
def Quadratics.envelope (P : Polytope ι κ) (Q : Quadratics Θ ι)
    (θ : Θ) (t : ℝ) : ℝ :=
  sSup ((fun β : EuclideanSpace ℝ ι => Q.objective θ β t) '' P.weights)

/-- A [fixed polytope](hyp:P) and [quadratic family](hyp:Q) have a [jointly Borel maximum
envelope](goal) in the parameter and scalar decision. -/
theorem Quadratics.measurable_envelope (P : Polytope ι κ)
    (Q : Quadratics Θ ι) :
    Measurable (fun x : Θ × ℝ => Q.envelope P x.1 x.2) := by
  classical
  letI : Nonempty P.weights := Set.nonempty_coe_sort.mpr P.nonempty
  let d : ℕ → P.weights := TopologicalSpace.denseSeq P.weights
  have hd : Dense (Set.range d) := by
    simpa only [DenseRange, d] using TopologicalSpace.denseRange_denseSeq P.weights
  have hn : Measurable (fun x : Θ × ℝ =>
      ⨆ n : ℕ, Q.objective x.1 (d n).1 x.2) := by
    apply Measurable.iSup
    intro n
    exact Q.measurable_objective.comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  convert hn using 1
  ext x
  change sSup ((fun β : EuclideanSpace ℝ ι => Q.objective x.1 β x.2) ''
    P.weights) = ⨆ n : ℕ, Q.objective x.1 (d n).1 x.2
  rw [sSup_image']
  have hc : Continuous (fun β : P.weights => Q.objective x.1 β.1 x.2) := by
    unfold Quadratics.objective
    fun_prop
  rw [← hd.ciSup' hc]
  have he : Function.Surjective
      (fun n : ℕ => (⟨d n, Set.mem_range_self n⟩ : Set.range d)) := by
    rintro ⟨z, n, rfl⟩
    exact ⟨n, rfl⟩
  exact (he.iSup_comp (fun s : Set.range d =>
    Q.objective x.1 s.1.1 x.2)).symm

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), and [parameter](hyp:θ) have a
[continuous maximum envelope as a function of the scalar decision](goal). -/
theorem Quadratics.continuous_envelope (P : Polytope ι κ)
    (Q : Quadratics Θ ι) (θ : Θ) : Continuous (Q.envelope P θ) := by
  apply P.compact.continuous_sSup
  change Continuous (fun p : ℝ × EuclideanSpace ℝ ι =>
    Q.objective θ p.2 p.1)
  unfold Quadratics.objective
  fun_prop

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [parameter](hyp:θ), [scalar
decision](hyp:t), and [feasible weight](hyp:β,hβ) have an [objective no larger than the maximum
envelope](goal). -/
theorem Quadratics.objective_le_envelope (P : Polytope ι κ) (Q : Quadratics Θ ι)
    (θ : Θ) (t : ℝ) (β : EuclideanSpace ℝ ι) (hβ : β ∈ P.weights) :
    Q.objective θ β t ≤ Q.envelope P θ t := by
  have hc : Continuous (fun γ : EuclideanSpace ℝ ι => Q.objective θ γ t) := by
    unfold Quadratics.objective
    fun_prop
  have hbdd : BddAbove ((fun γ : EuclideanSpace ℝ ι => Q.objective θ γ t) ''
      P.weights) := P.compact.bddAbove_image hc.continuousOn
  exact le_csSup hbdd ⟨β, hβ, rfl⟩

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [parameter](hyp:θ), [weight
vector](hyp:α), and [scalar decision](hyp:s) whose [pair is a saddle](hyp:hs) have a [maximum
envelope equal to their objective](goal). -/
theorem Quadratics.envelope_eq_of_isSaddle (P : Polytope ι κ)
    (Q : Quadratics Θ ι) (θ : Θ) (α : EuclideanSpace ℝ ι) (s : ℝ)
    (hs : IsSaddle P Q θ α s) :
    Q.envelope P θ s = Q.objective θ α s := by
  apply le_antisymm
  · apply csSup_le (P.nonempty.image _)
    rintro y ⟨β, hβ, rfl⟩
    exact hs.2.2 β hβ
  · exact Q.objective_le_envelope P θ s α hs.1

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [parameter](hyp:θ), [weight
vector](hyp:α), [known saddle decision](hyp:s), [new decision](hyp:t), [known saddle
certificate](hyp:hs), and [envelope comparison](hyp:hle) give a [saddle pair at the new
decision](goal). -/
theorem Quadratics.isSaddle_at_envelope_le (P : Polytope ι κ)
    (Q : Quadratics Θ ι) (θ : Θ) (α : EuclideanSpace ℝ ι) (s t : ℝ)
    (hs : IsSaddle P Q θ α s)
    (hle : Q.envelope P θ t ≤ Q.envelope P θ s) :
    IsSaddle P Q θ α t := by
  have hts : Q.objective θ α t ≤ Q.objective θ α s := by
    calc
      Q.objective θ α t ≤ Q.envelope P θ t :=
        Q.objective_le_envelope P θ t α hs.1
      _ ≤ Q.envelope P θ s := hle
      _ = Q.objective θ α s := Q.envelope_eq_of_isSaddle P θ α s hs
  have heq : Q.objective θ α t = Q.objective θ α s :=
    le_antisymm hts (hs.2.1 t)
  refine ⟨hs.1, ?_, ?_⟩
  · intro u
    rw [heq]
    exact hs.2.1 u
  · intro β hβ
    calc
      Q.objective θ β t ≤ Q.envelope P θ t :=
        Q.objective_le_envelope P θ t β hβ
      _ ≤ Q.objective θ α s := by
        rw [← Q.envelope_eq_of_isSaddle P θ α s hs]
        exact hle
      _ = Q.objective θ α t := heq.symm

end Causalean.Mathlib.Optimization.QuadraticSaddle
