module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.MinimaxLowerRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FrontierAlternatives
public import Causalean.Stat.Minimax.HonestConfidenceSet
public import Causalean.Stat.Minimax.Pinsker

/-! # Two-point converse for honest intervals

Coverage transfers from an alternative to the reference law through total
variation. Simultaneous coverage forces the interval to contain both targets.
An arbitrarily small interior amplitude gives the parametric converse at every
sample size, covering the subcritical regime and finite-sample patches.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Coverage at two targets forces expected nonnegative interval length at
least their separation times the simultaneous-coverage probability floor. -/
-- @node: twoPoint_interval_length_lower
lemma twoPoint_interval_length_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (lo hi : Ω → ℝ) (hlo : Measurable lo) (hhi : Measurable hi)
    (θ₀ θ₁ alpha eta : ℝ)
    (h₀ : 1 - alpha ≤ μ.real {s | lo s ≤ θ₀ ∧ θ₀ ≤ hi s})
    (h₁ : 1 - alpha ≤ ν.real {s | lo s ≤ θ₁ ∧ θ₁ ≤ hi s})
    (htv : Causalean.Stat.tvDist μ ν ≤ eta) :
    ENNReal.ofReal ((1 - 2 * alpha - eta) * |θ₁ - θ₀|) ≤
      ∫⁻ s, ENNReal.ofReal (hi s - lo s) ∂μ := by
  let E₀ := {s | lo s ≤ θ₀ ∧ θ₀ ≤ hi s}
  let E₁ := {s | lo s ≤ θ₁ ∧ θ₁ ≤ hi s}
  have hE₀ : MeasurableSet E₀ :=
    (measurableSet_le hlo measurable_const).inter (measurableSet_le measurable_const hhi)
  have hE₁ : MeasurableSet E₁ :=
    (measurableSet_le hlo measurable_const).inter (measurableSet_le measurable_const hhi)
  have hgap := (Causalean.Stat.measureReal_sub_le_tvDist
    (μ := μ) (ν := ν) hE₁).trans htv
  have hunion := measureReal_union_add_inter (μ := μ) (s := E₀) hE₁
  have hunion_le : μ.real (E₀ ∪ E₁) ≤ 1 := measureReal_le_one
  have hboth : 1 - 2 * alpha - eta ≤ μ.real (E₀ ∩ E₁) := by
    change 1 - alpha ≤ μ.real E₀ at h₀
    change 1 - alpha ≤ ν.real E₁ at h₁
    linarith
  let f := (E₀ ∩ E₁).indicator (fun _ : Ω => |θ₁ - θ₀|)
  have hf : Integrable f μ := (integrable_const _).indicator (hE₀.inter hE₁)
  have hflength : ∀ s, f s ≤ hi s - lo s ∨ hi s - lo s < 0 := by
    intro s
    by_cases hs : s ∈ E₀ ∩ E₁
    · left
      rw [show f s = |θ₁ - θ₀| from Set.indicator_of_mem hs _]
      rw [abs_le]
      constructor <;> linarith [hs.1.1, hs.1.2, hs.2.1, hs.2.2]
    · rw [show f s = 0 from Set.indicator_of_notMem hs _]
      exact le_or_gt 0 (hi s - lo s)
  have hpoint : ∀ s, f s ≤ max (hi s - lo s) 0 := by
    intro s
    rcases hflength s with h | h
    · exact h.trans (le_max_left _ _)
    · have hs : s ∉ E₀ ∩ E₁ := by
        intro hs
        linarith [hs.1.1, hs.1.2]
      rw [show f s = 0 from Set.indicator_of_notMem hs _]
      exact le_max_right _ _
  have hint : (∫ s, f s ∂μ) = μ.real (E₀ ∩ E₁) * |θ₁ - θ₀| := by
    simp only [f, integral_indicator (hE₀.inter hE₁), setIntegral_const,
      smul_eq_mul, measureReal_def]
  calc
    ENNReal.ofReal ((1 - 2 * alpha - eta) * |θ₁ - θ₀|) ≤
        ENNReal.ofReal (∫ s, f s ∂μ) := by
      rw [hint]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hboth (abs_nonneg _))
    _ ≤ ∫⁻ s, ENNReal.ofReal (max (hi s - lo s) 0) ∂μ :=
      Causalean.Stat.ofReal_integral_le_lintegral_ofReal_of_le hf hpoint
    _ = ∫⁻ s, ENNReal.ofReal (hi s - lo s) ∂μ := by
      simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (zero_le : (0 : ℝ≥0∞) ≤ _)]

/-- Finite sample KL gives a usable total-variation bound for two subject
models, with probability instances derived from the model construction. -/
-- @node: sampleLaw_tvDist_le_of_KL
lemma sampleLaw_tvDist_le_of_KL (P₀ P₁ : SubjectLaw) (n : ℕ)
    (K : ℝ) (hfin : InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw P₀ n) ≠ ⊤)
    (hbound : (InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw P₀ n)).toReal ≤ K) :
    Causalean.Stat.tvDist (sampleLaw P₀ n) (sampleLaw P₁ n) ≤ Real.sqrt (K / 2) := by
  let : IsProbabilityMeasure P₀.latent := ⟨P₀.prob⟩
  let : IsProbabilityMeasure P₁.latent := ⟨P₁.prob⟩
  let : IsProbabilityMeasure (observedLaw P₀) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (observedLaw P₁) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P₀ n) := by unfold sampleLaw; infer_instance
  let : IsProbabilityMeasure (sampleLaw P₁ n) := by unfold sampleLaw; infer_instance
  have hac : sampleLaw P₁ n ≪ sampleLaw P₀ n := by
    by_contra h
    exact hfin (InformationTheory.klDiv_of_not_ac h)
  rw [Causalean.Stat.tvDist_symm]
  exact (Causalean.Stat.pinskerBound_of_ac_of_ne_top _ _ hac hfin).trans
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hbound (by norm_num)))

/-- Shrinking a genuine interior perturbation makes its sample laws close
enough for any miscoverage below one half, at every sample size. -/
-- @node: honestInterval_parametric_lower
lemma honestInterval_parametric_lower (c : ClassConstants)
    (hNonempty : ∃ P : SubjectLaw, ModelClass c P)
    (alpha : ℝ) (hAlphaHalf : alpha < 1 / 2) :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 3 ≤ n →
      ∀ lo hi : (Fin n → ObsHistory) → ℝ,
        Measurable lo → Measurable hi →
        (∀ P : SubjectLaw, ModelClass c P →
          1 - alpha ≤ (sampleLaw P n).real
            {s | lo s ≤ causalTarget P ∧ causalTarget P ≤ hi s}) →
        ∃ P : SubjectLaw, ModelClass c P ∧
          ENNReal.ofReal (a * Real.sqrt ((n : ℝ)⁻¹)) ≤
            ∫⁻ s, ENNReal.ofReal (hi s - lo s) ∂sampleLaw P n := by
  obtain ⟨P, hP⟩ := hNonempty
  obtain ⟨cut₀⟩ := nonempty_cutoffData c
  let cut := interiorCutoffData c cut₀
  let eta := (1 - 2 * alpha) / 2
  have heta : 0 < eta := by dsimp [eta]; linarith
  let B := endpointBumpBound c cut
  let lambda0 := midpointLambda c
  have hB : 0 < B := endpointBumpBound_pos c cut
  have hlambda0 : 0 < lambda0 := c.lambdaMin_pos.trans (midpoint_strict_bounds c).1
  let threshold := eta ^ 2 * lambda0 / B ^ 2
  have hthreshold : 0 < threshold := by dsimp [threshold]; positivity
  let u := min (endpointModelRadius c cut) (Real.sqrt threshold)
  have hu : 0 < u := lt_min (endpointModelRadius_pos c cut)
    (Real.sqrt_pos.mpr hthreshold)
  have hur : u ≤ endpointModelRadius c cut := min_le_left _ _
  have husq : u ^ 2 ≤ threshold := by
    have h := (sq_le_sq₀ hu.le (Real.sqrt_nonneg threshold)).2 (min_le_right _ _)
    rwa [Real.sq_sqrt hthreshold.le] at h
  let K := u ^ 2 * B ^ 2 / lambda0
  have hK : K ≤ eta ^ 2 := by
    have h := mul_le_mul_of_nonneg_right husq (sq_nonneg B)
    have hden : B ^ 2 ≠ 0 := pow_ne_zero _ hB.ne'
    dsimp only [threshold] at h
    rw [div_mul_cancel₀ _ hden] at h
    exact (div_le_iff₀ hlambda0).2 h
  have hsqrt : Real.sqrt (K / 2) ≤ eta := by
    apply (Real.sqrt_le_iff).2
    refine ⟨heta.le, ?_⟩
    linarith [sq_nonneg eta]
  obtain ⟨δ, hδ, hfamily⟩ := interior_twoPoint_family c P hP cut u hu hur
  refine ⟨eta * δ, mul_pos heta hδ, ?_⟩
  intro n hn lo hi hlo hhi hcoverage
  obtain ⟨P₀, P₁, h₀, h₁, hfin, hbound, hsep⟩ := hfamily n hn
  let : IsProbabilityMeasure P₀.latent := ⟨P₀.prob⟩
  let : IsProbabilityMeasure P₁.latent := ⟨P₁.prob⟩
  let : IsProbabilityMeasure (observedLaw P₀) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (observedLaw P₁) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P₀ n) := by unfold sampleLaw; infer_instance
  let : IsProbabilityMeasure (sampleLaw P₁ n) := by unfold sampleLaw; infer_instance
  have htv := (sampleLaw_tvDist_le_of_KL P₀ P₁ n K hfin.ne hbound).trans hsqrt
  have hlower := twoPoint_interval_length_lower (sampleLaw P₀ n) (sampleLaw P₁ n)
    lo hi hlo hhi (causalTarget P₀) (causalTarget P₁) alpha eta
    (hcoverage P₀ h₀) (hcoverage P₁ h₁) htv
  have he : 1 - 2 * alpha - eta = eta := by dsimp [eta]; ring
  rw [he] at hlower
  refine ⟨P₀, h₀, le_trans ?_ hlower⟩
  apply ENNReal.ofReal_le_ofReal
  have hsep' := mul_le_mul_of_nonneg_left hsep heta.le
  simpa only [Real.sqrt_inv, ← div_eq_mul_inv, mul_div_assoc] using hsep'

/-- Amplitude tuning makes the genuine endpoint pair close enough to
transfer honest coverage while preserving the frontier target separation. -/
-- @node: honestInterval_eventual_lower_of_one_le_kappa
lemma honestInterval_eventual_lower_of_one_le_kappa (c : ClassConstants)
    (hNonempty : ∃ P : SubjectLaw, ModelClass c P) (hk : 1 ≤ c.kappa)
    (alpha : ℝ) (hAlphaHalf : alpha < 1 / 2) :
    ∃ b : ℝ, ∃ N : ℕ, 0 < b ∧ 3 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ lo hi : (Fin n → ObsHistory) → ℝ,
        Measurable lo → Measurable hi →
        (∀ P : SubjectLaw, ModelClass c P →
          1 - alpha ≤ (sampleLaw P n).real
            {s | lo s ≤ causalTarget P ∧ causalTarget P ≤ hi s}) →
        ∃ P : SubjectLaw, ModelClass c P ∧
          ENNReal.ofReal (b * Real.sqrt (riskScale c n)) ≤
            ∫⁻ s, ENNReal.ofReal (hi s - lo s) ∂sampleLaw P n := by
  obtain ⟨C, r, hC, hr, hfamily⟩ := frontier_twoPoint_family c hNonempty hk
  let eta := (1 - 2 * alpha) / 2
  have heta : 0 < eta := by dsimp [eta]; linarith
  let threshold := eta ^ 2 / C
  have hthreshold : 0 < threshold := by dsimp [threshold]; positivity
  let u := min r (Real.sqrt threshold)
  have hu : 0 < u := lt_min hr (Real.sqrt_pos.mpr hthreshold)
  have husq : u ^ 2 ≤ threshold := by
    have h := (sq_le_sq₀ hu.le (Real.sqrt_nonneg threshold)).2 (min_le_right _ _)
    rwa [Real.sq_sqrt hthreshold.le] at h
  have hK : C * u ^ 2 ≤ eta ^ 2 := by
    have h := mul_le_mul_of_nonneg_left husq hC.le
    dsimp only [threshold] at h
    rwa [mul_div_cancel₀ _ hC.ne'] at h
  have hsqrt : Real.sqrt (C * u ^ 2 / 2) ≤ eta := by
    apply (Real.sqrt_le_iff).2
    refine ⟨heta.le, ?_⟩
    linarith [sq_nonneg eta]
  obtain ⟨δ, N, hδ, hN, hw⟩ := hfamily u hu (min_le_left _ _)
  refine ⟨eta * δ, N, mul_pos heta hδ, hN, ?_⟩
  intro n hn lo hi hlo hhi hcoverage
  obtain ⟨P₀, P₁, h₀, h₁, hfin, hbound, hsep⟩ := hw n hn
  let : IsProbabilityMeasure P₀.latent := ⟨P₀.prob⟩
  let : IsProbabilityMeasure P₁.latent := ⟨P₁.prob⟩
  let : IsProbabilityMeasure (observedLaw P₀) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (observedLaw P₁) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P₀ n) := by unfold sampleLaw; infer_instance
  let : IsProbabilityMeasure (sampleLaw P₁ n) := by unfold sampleLaw; infer_instance
  have htv := (sampleLaw_tvDist_le_of_KL P₀ P₁ n (C * u ^ 2) hfin.ne hbound).trans hsqrt
  have hlower := twoPoint_interval_length_lower (sampleLaw P₀ n) (sampleLaw P₁ n)
    lo hi hlo hhi (causalTarget P₀) (causalTarget P₁) alpha eta
    (hcoverage P₀ h₀) (hcoverage P₁ h₁) htv
  have he : 1 - 2 * alpha - eta = eta := by dsimp [eta]; ring
  rw [he] at hlower
  refine ⟨P₀, h₀, le_trans ?_ hlower⟩
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsep heta.le

/-- An eventual frontier converse extends to every allowed sample size
using the genuine interior alternatives on the finite remaining set. -/
-- @node: honestInterval_lower_rate_of_eventual
lemma honestInterval_lower_rate_of_eventual (c : ClassConstants)
    (hNonempty : ∃ P : SubjectLaw, ModelClass c P)
    (alpha : ℝ) (hAlphaHalf : alpha < 1 / 2)
    (heventual : ∃ b : ℝ, ∃ N : ℕ, 0 < b ∧ 3 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ lo hi : (Fin n → ObsHistory) → ℝ,
        Measurable lo → Measurable hi →
        (∀ P : SubjectLaw, ModelClass c P →
          1 - alpha ≤ (sampleLaw P n).real
            {s | lo s ≤ causalTarget P ∧ causalTarget P ≤ hi s}) →
        ∃ P : SubjectLaw, ModelClass c P ∧
          ENNReal.ofReal (b * Real.sqrt (riskScale c n)) ≤
            ∫⁻ s, ENNReal.ofReal (hi s - lo s) ∂sampleLaw P n) :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 3 ≤ n →
      ∀ lo hi : (Fin n → ObsHistory) → ℝ,
        Measurable lo → Measurable hi →
        (∀ P : SubjectLaw, ModelClass c P →
          1 - alpha ≤ (sampleLaw P n).real
            {s | lo s ≤ causalTarget P ∧ causalTarget P ≤ hi s}) →
        ∃ P : SubjectLaw, ModelClass c P ∧
          ENNReal.ofReal (a * Real.sqrt (riskScale c n)) ≤
            ∫⁻ s, ENNReal.ofReal (hi s - lo s) ∂sampleLaw P n := by
  classical
  obtain ⟨a, ha, hparam⟩ := honestInterval_parametric_lower c hNonempty alpha hAlphaHalf
  obtain ⟨b, N, hb, hN, hevent⟩ := heventual
  let ratio := fun n : ℕ => a * Real.sqrt ((n : ℝ)⁻¹) / Real.sqrt (riskScale c n)
  have hratpos (n : ℕ) (hn : 3 ≤ n) : 0 < ratio n := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact div_pos (mul_pos ha (Real.sqrt_pos.mpr (inv_pos.mpr hnpos)))
      (Real.sqrt_pos.mpr (riskScale_pos c hn))
  have hne : (Finset.Icc 3 N).Nonempty := ⟨N, Finset.mem_Icc.mpr ⟨hN, le_rfl⟩⟩
  obtain ⟨i, hi, hmin⟩ := (Finset.Icc 3 N).exists_min_image ratio hne
  have hi3 := (Finset.mem_Icc.mp hi).1
  refine ⟨min b (ratio i), lt_min hb (hratpos i hi3), ?_⟩
  intro n hn lo hi hlo hhi hcoverage
  by_cases hnN : N ≤ n
  · obtain ⟨P, hP, hlength⟩ := hevent n hnN lo hi hlo hhi hcoverage
    refine ⟨P, hP, le_trans ?_ hlength⟩
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Real.sqrt_nonneg _))
  · obtain ⟨P, hP, hlength⟩ := hparam n hn lo hi hlo hhi hcoverage
    refine ⟨P, hP, le_trans ?_ hlength⟩
    apply ENNReal.ofReal_le_ofReal
    have hnmem : n ∈ Finset.Icc 3 N := Finset.mem_Icc.mpr ⟨hn, by omega⟩
    calc
      min b (ratio i) * Real.sqrt (riskScale c n) ≤
          ratio n * Real.sqrt (riskScale c n) :=
        mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (hmin n hnmem))
          (Real.sqrt_nonneg _)
      _ = a * Real.sqrt ((n : ℝ)⁻¹) :=
        div_mul_cancel₀ _ (Real.sqrt_pos.mpr (riskScale_pos c hn)).ne'

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
