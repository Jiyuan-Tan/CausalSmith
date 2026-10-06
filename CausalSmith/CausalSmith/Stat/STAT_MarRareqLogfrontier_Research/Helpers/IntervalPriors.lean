module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Activation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! The finite interpolated reciprocal priors in equations (5) and (7) of the
connected-interval lower bound. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:π₀,π₁,t), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: intervalInterpolatedPrior
noncomputable def intervalInterpolatedPrior (π₀ π₁ : Measure ℝ) (t : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - t) • π₀ + ENNReal.ofReal t • π₁

/-- Given [the specified inputs and assumptions](hyp:H,π,hπ,f), [the stated mathematical conclusion holds](goal). -/
-- @node: finiteReciprocalPrior_integrable
lemma finiteReciprocalPrior_integrable {H : ℝ} {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior H π) (f : ℝ → ℝ) : Integrable f π := by
  let := hπ.1
  obtain ⟨s, hs, _⟩ := hπ.2
  have hae : ∀ᵐ z ∂π, z ∈ (s : Set ℝ) :=
    (ae_mem_iff_measure_eq s.measurableSet.nullMeasurableSet).2 (by simpa using hs)
  have hres : π.restrict (s : Set ℝ) = π := Measure.restrict_eq_self_of_ae_mem hae
  have hi : IntegrableOn f (s : Set ℝ) π := IntegrableOn.of_finite s.finite_toSet
  simpa only [IntegrableOn, hres] using hi

/-- Given [the specified inputs and assumptions](hyp:H,π₀,π₁,h₀,h₁,t,ht), [the stated mathematical conclusion holds](goal). -/
-- @node: finiteReciprocalPrior_interpolate
lemma finiteReciprocalPrior_interpolate {H : ℝ} {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior H π₀) (h₁ : FiniteReciprocalPrior H π₁)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    FiniteReciprocalPrior H (intervalInterpolatedPrior π₀ π₁ t) := by
  classical
  let := h₀.1
  let := h₁.1
  have hweights : ENNReal.ofReal (1 - t) + ENNReal.ofReal t = 1 := by
    rw [← ENNReal.ofReal_add (by linarith [ht.2]) ht.1]
    norm_num
  have hp : IsProbabilityMeasure (intervalInterpolatedPrior π₀ π₁ t) := by
    constructor
    simp only [intervalInterpolatedPrior, Measure.add_apply, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    exact hweights
  refine ⟨hp, ?_⟩
  obtain ⟨s₀, hs₀, hmem₀⟩ := h₀.2
  obtain ⟨s₁, hs₁, hmem₁⟩ := h₁.2
  have hmass₀ : π₀ (↑(s₀ ∪ s₁) : Set ℝ) = 1 := by
    apply le_antisymm (by simpa using (measure_mono (subset_univ _) :
      π₀ (↑(s₀ ∪ s₁) : Set ℝ) ≤ π₀ univ))
    rw [← hs₀]
    exact measure_mono (by simp only [Finset.coe_union]; exact subset_union_left)
  have hmass₁ : π₁ (↑(s₀ ∪ s₁) : Set ℝ) = 1 := by
    apply le_antisymm (by simpa using (measure_mono (subset_univ _) :
      π₁ (↑(s₀ ∪ s₁) : Set ℝ) ≤ π₁ univ))
    rw [← hs₁]
    exact measure_mono (by simp only [Finset.coe_union]; exact subset_union_right)
  refine ⟨s₀ ∪ s₁, ?_, ?_⟩
  · simp only [intervalInterpolatedPrior, Measure.add_apply, Measure.smul_apply,
      hmass₀, hmass₁, smul_eq_mul, mul_one]
    exact hweights
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hmem₀ z hz
    · exact hmem₁ z hz

/-- Given [the specified inputs and assumptions](hyp:H,π₀,π₁,h₀,h₁,t,ht,f), [the stated mathematical conclusion holds](goal). -/
-- @node: intervalInterpolatedPrior_integral
lemma intervalInterpolatedPrior_integral {H : ℝ} {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior H π₀) (h₁ : FiniteReciprocalPrior H π₁)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (f : ℝ → ℝ) :
    (∫ z, f z ∂intervalInterpolatedPrior π₀ π₁ t) =
      (1 - t) * (∫ z, f z ∂π₀) + t * (∫ z, f z ∂π₁) := by
  rw [intervalInterpolatedPrior, integral_add_measure
    ((finiteReciprocalPrior_integrable h₀ f).smul_measure (by simp))
    ((finiteReciprocalPrior_integrable h₁ f).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (show 0 ≤ 1 - t by linarith [ht.2]),
    ENNReal.toReal_ofReal ht.1, smul_eq_mul]

/-- Given [the specified inputs and assumptions](hyp:H,π₀,π₁,h₀,h₁,K,hm,t,ht,v,hv), [the stated mathematical conclusion holds](goal). -/
-- @node: intervalInterpolatedPrior_moments
lemma intervalInterpolatedPrior_moments {H : ℝ} {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior H π₀) (h₁ : FiniteReciprocalPrior H π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (v : ℕ) (hv : v ≤ K) :
    (∫ z, z ^ v ∂intervalInterpolatedPrior π₀ π₁ t) = ∫ z, z ^ v ∂π₀ := by
  rw [intervalInterpolatedPrior_integral h₀ h₁ ht, ← hm v hv]
  ring

/-- Given [the specified inputs and assumptions](hyp:H,π₀,π₁,h₀,h₁,K,hm,M,hM), [the stated mathematical conclusion holds](goal). -/
-- @node: intervalInterpolatedPrior_grid
lemma intervalInterpolatedPrior_grid {H : ℝ} {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior H π₀) (h₁ : FiniteReciprocalPrior H π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (M : ℕ) (hM : 1 ≤ M) :
    ∀ h : Fin (M + 1),
      FiniteReciprocalPrior H (intervalInterpolatedPrior π₀ π₁ ((h : ℝ) / M)) ∧
      (∀ h' : Fin (M + 1), ∀ v : ℕ, v ≤ K →
        (∫ z, z ^ v ∂intervalInterpolatedPrior π₀ π₁ ((h : ℝ) / M)) =
          ∫ z, z ^ v ∂intervalInterpolatedPrior π₀ π₁ ((h' : ℝ) / M)) ∧
      (∫ z, z⁻¹ ∂intervalInterpolatedPrior π₀ π₁ ((h : ℝ) / M)) =
        (∫ z, z⁻¹ ∂π₀) + (h : ℝ) *
          (((∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀) / M) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have ht (h : Fin (M + 1)) : (h : ℝ) / M ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, (div_le_one hMpos).mpr ?_⟩
    exact_mod_cast (by omega : h.val ≤ M)
  intro h
  refine ⟨finiteReciprocalPrior_interpolate h₀ h₁ (ht h), ?_, ?_⟩
  · intro h' v hv
    rw [intervalInterpolatedPrior_moments h₀ h₁ K hm (ht h) v hv,
      intervalInterpolatedPrior_moments h₀ h₁ K hm (ht h') v hv]
  · rw [intervalInterpolatedPrior_integral h₀ h₁ (ht h)]
    ring

/-- Given [the specified inputs and assumptions](hyp:H,π₀,π₁,h₀,h₁,M,h,hh), [the stated mathematical conclusion holds](goal). -/
-- @node: intervalInterpolatedPrior_reciprocal_spacing
lemma intervalInterpolatedPrior_reciprocal_spacing {H : ℝ} {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior H π₀) (h₁ : FiniteReciprocalPrior H π₁)
    (M h : ℕ) (hh : h < M) :
    |(∫ z, z⁻¹ ∂intervalInterpolatedPrior π₀ π₁ (((h : ℝ) + 1) / M)) -
      (∫ z, z⁻¹ ∂intervalInterpolatedPrior π₀ π₁ ((h : ℝ) / M))| =
        |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀| / M := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have ht : (h : ℝ) / M ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, (div_le_one hM).mpr ?_⟩
    exact_mod_cast (Nat.le_of_lt hh)
  have ht' : ((h : ℝ) + 1) / M ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, (div_le_one hM).mpr ?_⟩
    exact_mod_cast (by omega : h + 1 ≤ M)
  rw [intervalInterpolatedPrior_integral h₀ h₁ ht',
    intervalInterpolatedPrior_integral h₀ h₁ ht]
  have heq (a b : ℝ) :
      (1 - ((h : ℝ) + 1) / M) * a + (((h : ℝ) + 1) / M) * b -
        ((1 - (h : ℝ) / M) * a + ((h : ℝ) / M) * b) = (b - a) / M := by
    ring
  rw [heq, abs_div, abs_of_pos hM]

end CausalSmith.Stat.MarRareqLogfrontier
