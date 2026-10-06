module
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact

/-!
# Continuity of compact saddle values

A jointly continuous objective is maximized over a fixed compact action set and minimized over a
scalar decision. When the scalar minimum is attained in one fixed compact set near a parameter,
the value and, at a positive value, its reciprocal are continuous without continuity of a selected
optimizer.
-/

@[expose] public section

noncomputable section

namespace Causalean.Mathlib.Optimization.CompactSaddleValue

variable {Θ A : Type*} [TopologicalSpace Θ] [TopologicalSpace A]

/-- The [fixed action set](hyp:S), [objective family](hyp:f), [parameter](hyp:θ), and [scalar
decision](hyp:t) determine the [maximum envelope](goal), given by the supremum over the action
set [as its defining equation](step:1). -/
def envelope (S : Set A) (f : Θ → A → ℝ → ℝ) (θ : Θ) (t : ℝ) : ℝ :=
  sSup ((fun a : A => f θ a t) '' S)

/-- The [fixed action set](hyp:S), [objective family](hyp:f), and [parameter](hyp:θ) determine
the [max-inf saddle value](goal), given by the infimum of the maximum envelope over all scalar
decisions [as its defining equation](step:1). -/
def value (S : Set A) (f : Θ → A → ℝ → ℝ) (θ : Θ) : ℝ :=
  sInf ((fun t : ℝ => envelope S f θ t) '' Set.univ)

/-- The [fixed action set](hyp:S), [objective family](hyp:f), [compact scalar set](hyp:K), and
[parameter](hyp:θ) determine the [compact scalar minimum](goal), given by the infimum of the
maximum envelope over that scalar set [as its defining equation](step:1). -/
def compactMin (S : Set A) (f : Θ → A → ℝ → ℝ) (K : Set ℝ) (θ : Θ) : ℝ :=
  sInf ((fun t : ℝ => envelope S f θ t) '' K)

/-- A [compact action set](hyp:S,hS) and [jointly continuous objective](hyp:f,hf) give a
[jointly continuous maximum envelope](goal) in the parameter and scalar decision. -/
theorem continuous_envelope (S : Set A) (hS : IsCompact S)
    (f : Θ → A → ℝ → ℝ)
    (hf : Continuous (fun x : (Θ × ℝ) × A => f x.1.1 x.2 x.1.2)) :
    Continuous (fun x : Θ × ℝ => envelope S f x.1 x.2) := by
  exact hS.continuous_sSup hf

/-- A [compact action set](hyp:S,hS), [objective family](hyp:f), [compact scalar set](hyp:K,hK),
and [jointly continuous objective](hyp:hf) give a [continuous compact scalar minimum](goal). -/
theorem continuous_compactMin (S : Set A) (hS : IsCompact S)
    (f : Θ → A → ℝ → ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hf : Continuous (fun x : (Θ × ℝ) × A => f x.1.1 x.2 x.1.2)) :
    Continuous (compactMin S f K) := by
  exact hK.continuous_sInf (continuous_envelope S hS f hf)

/-- An [action set](hyp:S), [objective family](hyp:f), [compact scalar set](hyp:K),
[parameter](hyp:θ), and [scalar point belonging to that set](hyp:t,ht) whose [envelope value is
no larger than at every scalar point](hyp:hmin) give [equality of the unrestricted saddle value
and compact scalar minimum](goal). -/
theorem value_eq_compactMin_of_attained (S : Set A) (f : Θ → A → ℝ → ℝ)
    (K : Set ℝ) (θ : Θ) (t : ℝ) (ht : t ∈ K)
    (hmin : ∀ u : ℝ, envelope S f θ t ≤ envelope S f θ u) :
    value S f θ = compactMin S f K θ := by
  have hall : IsLeast ((fun u : ℝ => envelope S f θ u) '' Set.univ)
      (envelope S f θ t) := by
    constructor
    · exact ⟨t, Set.mem_univ _, rfl⟩
    · rintro y ⟨u, -, rfl⟩
      exact hmin u
  have hcompact : IsLeast ((fun u : ℝ => envelope S f θ u) '' K)
      (envelope S f θ t) := by
    constructor
    · exact ⟨t, ht, rfl⟩
    · rintro y ⟨u, -, rfl⟩
      exact hmin u
  exact (hall.csInf_eq).trans hcompact.csInf_eq.symm

/-- A [compact nonempty action set](hyp:S,hS,hSne), [objective family](hyp:f), [compact
nonempty scalar set](hyp:K,hK,hKne), [parameter](hyp:θ₀), [joint continuity of the objective](hyp:hf), and [eventual attainment of scalar envelope minima in the compact set](hyp:hatt) give
a [continuous max-inf saddle value at the parameter](goal). -/
theorem continuousAt_value (S : Set A) (hS : IsCompact S) (hSne : S.Nonempty)
    (f : Θ → A → ℝ → ℝ) (K : Set ℝ) (hK : IsCompact K) (hKne : K.Nonempty)
    (θ₀ : Θ)
    (hf : Continuous (fun x : (Θ × ℝ) × A => f x.1.1 x.2 x.1.2))
    (hatt : ∀ᶠ θ in nhds θ₀, ∃ t ∈ K,
      ∀ u : ℝ, envelope S f θ t ≤ envelope S f θ u) :
    ContinuousAt (value S f) θ₀ := by
  have _hSne : S.Nonempty := hSne
  have _hKne : K.Nonempty := hKne
  apply (continuous_compactMin S hS f K hK hf).continuousAt.congr
  filter_upwards [hatt] with θ ⟨t, ht, hmin⟩
  exact (value_eq_compactMin_of_attained S f K θ t ht hmin).symm

/-- A [compact nonempty action set](hyp:S,hS,hSne), [objective family](hyp:f), [compact
nonempty scalar set](hyp:K,hK,hKne), [parameter](hyp:θ₀), [joint continuity of the objective](hyp:hf), [eventual attainment of scalar envelope minima in the compact set](hyp:hatt), and a
[strictly positive saddle value at the parameter](hyp:hpos) give a [continuous reciprocal saddle
value at that parameter](goal). -/
theorem continuousAt_inv_value (S : Set A) (hS : IsCompact S) (hSne : S.Nonempty)
    (f : Θ → A → ℝ → ℝ) (K : Set ℝ) (hK : IsCompact K) (hKne : K.Nonempty)
    (θ₀ : Θ)
    (hf : Continuous (fun x : (Θ × ℝ) × A => f x.1.1 x.2 x.1.2))
    (hatt : ∀ᶠ θ in nhds θ₀, ∃ t ∈ K,
      ∀ u : ℝ, envelope S f θ t ≤ envelope S f θ u)
    (hpos : 0 < value S f θ₀) :
    ContinuousAt (fun θ => (value S f θ)⁻¹) θ₀ := by
  exact (continuousAt_value S hS hSne f K hK hKne θ₀ hf hatt).inv₀ (ne_of_gt hpos)

/-- A [compact nonempty action set](hyp:S,hS,hSne), [objective family](hyp:f), [compact
nonempty scalar set](hyp:K,hK,hKne), [parameter](hyp:θ₀), [parameter neighborhood](hyp:U), [openness of that neighborhood](hyp:hUopen), and [membership of the parameter](hyp:hθU), [joint continuity of the objective on that neighborhood](hyp:hf), and
[eventual attainment of scalar envelope minima in the compact set](hyp:hatt) give a [continuous
max-inf saddle value at the parameter](goal). -/
theorem continuousAt_value_of_continuousOn (S : Set A) (hS : IsCompact S)
    (hSne : S.Nonempty) (f : Θ → A → ℝ → ℝ) (K : Set ℝ)
    (hK : IsCompact K) (hKne : K.Nonempty) (θ₀ : Θ)
    (U : Set Θ) (hUopen : IsOpen U) (hθU : θ₀ ∈ U)
    (hf : ContinuousOn (fun x : (Θ × ℝ) × A => f x.1.1 x.2 x.1.2)
      {x | x.1.1 ∈ U})
    (hatt : ∀ᶠ θ in nhds θ₀, ∃ t ∈ K,
      ∀ u : ℝ, envelope S f θ t ≤ envelope S f θ u) :
    ContinuousAt (value S f) θ₀ := by
  let fU : U → A → ℝ → ℝ := fun θ a t => f θ.1 a t
  have hfU : Continuous (fun x : (U × ℝ) × A => fU x.1.1 x.2 x.1.2) := by
    apply continuous_iff_continuousAt.2
    intro x
    have hmap : ContinuousAt (fun y : (U × ℝ) × A =>
        ((y.1.1.1, y.1.2), y.2)) x := by
      fun_prop
    exact (hf.continuousAt ((hUopen.preimage
      (continuous_fst.comp continuous_fst)).mem_nhds x.1.1.2)).comp hmap
  have hattU : ∀ᶠ θ in nhds (⟨θ₀, hθU⟩ : U), ∃ t ∈ K,
      ∀ u : ℝ, envelope S fU θ t ≤ envelope S fU θ u := by
    filter_upwards [(continuous_subtype_val.continuousAt.eventually hatt)] with θ hθ
    exact hθ
  have hlocal := continuousAt_value S hS hSne fU K hK hKne
    (⟨θ₀, hθU⟩ : U) hfU hattU
  apply (continuousWithinAt_iff_continuousAt (hUopen.mem_nhds hθU)).mp
  exact (continuousWithinAt_iff_continuousAt_domRestrict (value S f) hθU).mpr hlocal

end Causalean.Mathlib.Optimization.CompactSaddleValue
