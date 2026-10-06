module
public import Causalean.Mathlib.Optimization.CompactSaddleValue
public import Causalean.Mathlib.Optimization.QuadraticSaddle.Basic

/-!
# Continuity of finite quadratic saddle values

This module transfers local compact-saddle continuity to the existing finite quadratic max-min
value. It requires joint continuity of the quadratic objective only on an open neighborhood and a
common compact bound for locally attaining saddle scalar decisions.
-/

public section

noncomputable section

namespace Causalean.Mathlib.Optimization.QuadraticSaddle

open CompactSaddleValue

variable {Θ ι κ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ]
  [Fintype ι] [Fintype κ]

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [parameter](hyp:θ), [weight vector](hyp:α),
[scalar decision](hyp:t), and [saddle certificate](hyp:hs) give [the equality of the existing
quadratic max-min value with the unrestricted envelope minimum and the global minimality of that
scalar envelope value](goal). -/
theorem quadratic_value_eq_envelope_min_of_isSaddle
    (P : Polytope ι κ) (Q : Quadratics Θ ι) (θ : Θ)
    (α : EuclideanSpace ℝ ι) (t : ℝ) (hs : IsSaddle P Q θ α t) :
    value P Q θ =
      CompactSaddleValue.value P.weights Q.objective θ ∧
      ∀ u : ℝ, Q.envelope P θ t ≤ Q.envelope P θ u := by
  have hmin : ∀ u : ℝ, Q.envelope P θ t ≤ Q.envelope P θ u := by
    intro u
    calc
      Q.envelope P θ t = Q.objective θ α t :=
        Q.envelope_eq_of_isSaddle P θ α t hs
      _ ≤ Q.objective θ α u := hs.2.1 u
      _ ≤ Q.envelope P θ u := Q.objective_le_envelope P θ u α hs.1
  have hleast : IsLeast ((fun u : ℝ => Q.envelope P θ u) '' Set.univ)
      (Q.envelope P θ t) := by
    constructor
    · exact ⟨t, Set.mem_univ _, rfl⟩
    · rintro y ⟨u, -, rfl⟩
      exact hmin u
  have hgeneric : CompactSaddleValue.value P.weights Q.objective θ =
      Q.envelope P θ t := by
    exact hleast.csInf_eq
  constructor
  · exact (value_eq_of_isSaddle P Q θ α t hs).trans
      ((Q.envelope_eq_of_isSaddle P θ α t hs).symm.trans hgeneric.symm)
  · exact hmin

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [compact nonempty scalar set](hyp:K,hK,hKne),
[parameter](hyp:θ₀), [open parameter neighborhood](hyp:U,hUopen,hθU), [joint continuity of the
quadratic objective on that neighborhood](hyp:hobj), and [eventually attaining saddle pairs whose
scalar decisions lie in the compact set](hyp:hatt) give a [continuous existing quadratic max-min
value at the parameter](goal). -/
theorem continuousAt_quadratic_value
    (P : Polytope ι κ) (Q : Quadratics Θ ι) (K : Set ℝ)
    (hK : IsCompact K) (hKne : K.Nonempty) (θ₀ : Θ)
    (U : Set Θ) (hUopen : IsOpen U) (hθU : θ₀ ∈ U)
    (hobj : ContinuousOn
      (fun x : (Θ × ℝ) × EuclideanSpace ℝ ι =>
        Q.objective x.1.1 x.2 x.1.2) {x | x.1.1 ∈ U})
    (hatt : ∀ᶠ θ in nhds θ₀, ∃ α : EuclideanSpace ℝ ι,
      ∃ t ∈ K, IsSaddle P Q θ α t) :
    ContinuousAt (value P Q) θ₀ := by
  have hatt' : ∀ᶠ θ in nhds θ₀, ∃ t ∈ K,
      ∀ u : ℝ, envelope P.weights Q.objective θ t ≤
        envelope P.weights Q.objective θ u := by
    filter_upwards [hatt] with θ ⟨α, t, ht, hs⟩
    exact ⟨t, ht, (quadratic_value_eq_envelope_min_of_isSaddle P Q θ α t hs).2⟩
  have hcont := continuousAt_value_of_continuousOn P.weights P.compact P.nonempty
    Q.objective K hK hKne θ₀ U hUopen hθU hobj hatt'
  apply hcont.congr
  filter_upwards [hatt] with θ ⟨α, t, ht, hs⟩
  exact (quadratic_value_eq_envelope_min_of_isSaddle P Q θ α t hs).1.symm

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [compact nonempty scalar set](hyp:K,hK,hKne),
[parameter](hyp:θ₀), [open parameter neighborhood](hyp:U,hUopen,hθU), [joint continuity of the
quadratic objective on that neighborhood](hyp:hobj), [eventually attaining saddle pairs whose
scalar decisions lie in the compact set](hyp:hatt), and a [strictly positive existing quadratic
max-min value at the parameter](hyp:hpos) give a [continuous reciprocal quadratic max-min value
at that parameter](goal). -/
theorem continuousAt_inv_quadratic_value
    (P : Polytope ι κ) (Q : Quadratics Θ ι) (K : Set ℝ)
    (hK : IsCompact K) (hKne : K.Nonempty) (θ₀ : Θ)
    (U : Set Θ) (hUopen : IsOpen U) (hθU : θ₀ ∈ U)
    (hobj : ContinuousOn
      (fun x : (Θ × ℝ) × EuclideanSpace ℝ ι =>
        Q.objective x.1.1 x.2 x.1.2) {x | x.1.1 ∈ U})
    (hatt : ∀ᶠ θ in nhds θ₀, ∃ α : EuclideanSpace ℝ ι,
      ∃ t ∈ K, IsSaddle P Q θ α t)
    (hpos : 0 < value P Q θ₀) :
    ContinuousAt (fun θ =>
      (value P Q θ)⁻¹) θ₀ := by
  exact (continuousAt_quadratic_value P Q K hK hKne θ₀ U hUopen hθU hobj hatt).inv₀
    (ne_of_gt hpos)

end Causalean.Mathlib.Optimization.QuadraticSaddle
