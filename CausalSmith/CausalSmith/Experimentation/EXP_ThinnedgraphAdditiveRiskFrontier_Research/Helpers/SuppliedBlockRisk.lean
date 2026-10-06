module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.CompleteBlockDensity

/-!
# Supplied-block risk assembly

The translated full-record laws at the bounded testing amplitude give the
unrestricted randomized minimax converse through the two-prior testing inequality.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The roadmap amplitude, expressed using the square root of the risk scale. -/
-- @node: completeBlockLowerAmplitude
def completeBlockLowerAmplitude (n d : ℕ) : ℝ :=
  (100 * Real.pi)⁻¹ * Real.sqrt (min 1 (((d : ℝ) + 1) ^ 2 / n))

/-- The testing amplitude is positive, admissible, and has exactly the required squared scale.  [For the stated data and conditions](hyp:n,d,hn), [the stated conclusion holds](goal). -/
-- @node: completeBlockLowerAmplitude_properties
lemma completeBlockLowerAmplitude_properties (n d : ℕ) (hn : 0 < n) :
    0 < completeBlockLowerAmplitude n d ∧
    completeBlockLowerAmplitude n d ∈ Set.Icc 0 (1 / 4) ∧
    (completeBlockLowerAmplitude n d) ^ 2 =
      (10000 * Real.pi ^ 2)⁻¹ * min 1 (((d : ℝ) + 1) ^ 2 / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hs : 0 < min 1 (((d : ℝ) + 1) ^ 2 / n) := by positivity
  have hκ : 0 < (100 * Real.pi)⁻¹ := by positivity
  have hroot : Real.sqrt (min 1 (((d : ℝ) + 1) ^ 2 / n)) ≤ 1 := by
    exact (Real.sqrt_le_one).mpr (min_le_left _ _)
  have hκquarter : (100 * Real.pi)⁻¹ ≤ (1 / 4 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 100 * Real.pi)).mpr
    nlinarith [Real.two_le_pi]
  refine ⟨mul_pos hκ (Real.sqrt_pos.2 hs), ⟨(mul_pos hκ (Real.sqrt_pos.2 hs)).le, ?_⟩, ?_⟩
  · exact (mul_le_of_le_one_right hκ.le hroot).trans hκquarter
  · unfold completeBlockLowerAmplitude
    rw [mul_pow, Real.sq_sqrt hs.le]
    congr 1
    field_simp
    ring

/-- The genuine original-record distance at the roadmap amplitude is at most one fiftieth.  [For the stated data and conditions](hyp:n,d,hn,D,ha), [the stated conclusion holds](goal). -/
-- @node: completeBlock_testing_distance
lemma completeBlock_testing_distance (n d : ℕ) (hn : 0 < n)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (ha : AssignmentLaw D) :
    Causalean.Stat.tvDist
      (mixtureLaw D (blockBaselineLaw (n / (d + 1)))
        (completeBlockSchedule n d true (completeBlockLowerAmplitude n d)))
      (mixtureLaw D (blockBaselineLaw (n / (d + 1)))
        (completeBlockSchedule n d false (completeBlockLowerAmplitude n d))) ≤ 1 / 50 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hsq := (completeBlockLowerAmplitude_properties n d hn).2.2
  refine (completeBlock_mixture_tv_population_le n d _ D ha).trans ?_
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by norm_num, ?_⟩
  rw [hsq]
  have hmin := min_le_right (1 : ℝ) (((d : ℝ) + 1) ^ 2 / n)
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have he : 4 * Real.pi ^ 2 * ((10000 * Real.pi ^ 2)⁻¹ *
      min 1 (((d : ℝ) + 1) ^ 2 / n)) * n / ((d : ℝ) + 1) ^ 2 =
      min 1 (((d : ℝ) + 1) ^ 2 / n) * n / (2500 * ((d : ℝ) + 1) ^ 2) := by
    field_simp
    ring
  rw [he]
  apply (div_le_iff₀ (by positivity : 0 < 2500 * ((d : ℝ) + 1) ^ 2)).mpr
  have hm := (le_div_iff₀ hnR).mp hmin
  nlinarith

/-- Support, full-record testing distance, and coverage yield the supplied-block risk scale.  [For the stated data and conditions](hyp:n,d,q,hn,hd,hdu,hq), [the stated conclusion holds](goal). -/
-- @node: completeBlock_risk_lower_assembly
lemma completeBlock_risk_lower_assembly (n d : ℕ) (q : ℝ)
    (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n - 1) (hq : q ∈ Set.Icc 0 1) :
    ENNReal.ofReal ((160000 * Real.pi ^ 2)⁻¹ * min 1 (((d : ℝ) + 1) ^ 2 / n)) ≤
      minimaxRisk (thinnedDesign (Fin n) q) d := by
  let h := completeBlockLowerAmplitude n d
  let ρ : ℝ := (((n / (d + 1)) * (d + 1) : ℕ) : ℝ) / n
  have hprop := completeBlockLowerAmplitude_properties n d (by omega)
  have hcov : (1 / 2 : ℝ) ≤ ρ := completeBlock_coverage_ge_half n d hn hdu
  have hh : 0 < h := hprop.1
  have hΔ : 0 < ρ * h := mul_pos (by linarith) hh
  let := blockBaselineLaw_probability (n / (d + 1))
  have hs (σ : Bool) : ∀ᵐ U ∂(blockBaselineLaw (n / (d + 1))),
      ScheduleClass (completeBlockSchedule n d σ h U) d ∧
        tte (completeBlockSchedule n d σ h U) = signOf σ * (ρ * h) := by
    filter_upwards [completeBlock_support n d σ h hprop.2.1] with U hU
    refine ⟨hU.1, hU.2.trans ?_⟩
    dsimp [ρ]
    ring
  let : IsProbabilityMeasure (thinnedDesign (Fin n) q) := thinnedDesign_probabilityDesign q hq
  have ht := full_record_two_prior_risk n d q hn hd hdu hq
    (blockBaselineLaw (n / (d + 1))) (blockBaselineLaw (n / (d + 1)))
    (completeBlockSchedule n d true h) (completeBlockSchedule n d false h)
    (completeBlock_record_measurable n d true h) (completeBlock_record_measurable n d false h)
    (ρ * h) hΔ (by simpa [signOf] using hs true) (by simpa [signOf] using hs false)
  have htv := completeBlock_testing_distance n d (by omega) (thinnedDesign (Fin n) q)
    (thinnedDesign_assignment q hq)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) ht
  have hsep : h / 2 ≤ ρ * h := by nlinarith
  have hsqsep : h ^ 2 / 4 ≤ (ρ * h) ^ 2 := by nlinarith [sq_nonneg (ρ * h - h / 2)]
  have hscale : (160000 * Real.pi ^ 2)⁻¹ * min 1 (((d : ℝ) + 1) ^ 2 / n) =
      h ^ 2 / 16 := by
    rw [show h ^ 2 = _ from hprop.2.2]
    field_simp
    ring
  rw [hscale]
  change Causalean.Stat.tvDist
    (mixtureLaw (thinnedDesign (Fin n) q) (blockBaselineLaw (n / (d + 1)))
      (completeBlockSchedule n d true h))
    (mixtureLaw (thinnedDesign (Fin n) q) (blockBaselineLaw (n / (d + 1)))
      (completeBlockSchedule n d false h)) ≤ 1 / 50 at htv
  nlinarith [mul_nonneg (sq_nonneg (ρ * h))
    (show 0 ≤ 1 / 50 - Causalean.Stat.tvDist
      (mixtureLaw (thinnedDesign (Fin n) q) (blockBaselineLaw (n / (d + 1)))
        (completeBlockSchedule n d true h))
      (mixtureLaw (thinnedDesign (Fin n) q) (blockBaselineLaw (n / (d + 1)))
        (completeBlockSchedule n d false h)) from sub_nonneg.mpr htv)]

variable {V Ξ : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace Ξ]

/-- Hard-coding a graph makes a supplied-graph estimator a measurable original-record rule. -/
def hardcodeSuppliedEstimator (g : OffDiag V → Bool) (T : SuppliedEstimator V) : Estimator V :=
  ⟨fun x => T.1 ((x.1, g), x.2),
    T.2.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)⟩

/-- On a schedule with the hard-coded graph, the original and supplied squared risks agree.  [For the stated data and conditions](hyp:D,θ,g,T,hg), [the stated conclusion holds](goal). -/
lemma hardcodeSuppliedEstimator_sqLoss
    (D : Measure (Assign V × Audit V)) (θ : Schedule V)
    (g : OffDiag V → Bool) (T : SuppliedEstimator V)
    (hg : suppliedGraphOf θ = g) :
    sqLoss D θ (hardcodeSuppliedEstimator g T) = suppliedSqLoss D θ T := by
  have hr : Measurable (recordOf θ) := measurable_of_finite _
  have ho : Measurable (fun ω : (Assign V × Audit V) × ℝ => (recordOf θ ω.1, ω.2)) :=
    (hr.comp measurable_fst).prodMk measurable_snd
  have hs : Measurable (fun ω : (Assign V × Audit V) × ℝ =>
      (suppliedRecordOf θ ω.1, ω.2)) :=
    ((hr.comp measurable_fst).prodMk measurable_const).prodMk measurable_snd
  have hf : Measurable (fun x : Record V × ℝ =>
      ENNReal.ofReal (((hardcodeSuppliedEstimator g T).1 x - tte θ) ^ 2)) :=
    (((hardcodeSuppliedEstimator g T).2.sub measurable_const).pow_const 2).ennreal_ofReal
  have hfG : Measurable (fun x : SuppliedRecord V × ℝ =>
      ENNReal.ofReal ((T.1 x - tte θ) ^ 2)) :=
    ((T.2.sub measurable_const).pow_const 2).ennreal_ofReal
  unfold sqLoss recordLaw suppliedSqLoss suppliedRecordLaw
  rw [lintegral_map hf ho, lintegral_map hfG hs]
  simp only [hardcodeSuppliedEstimator, suppliedRecordOf, hg]

/-- A constant-target, fixed-graph prior's hard-coded risks are bounded by supplied worst risk.  [For the stated data and conditions](hyp:D,π,s,hm,d,a,g,hs,hg,T), [the stated conclusion holds](goal). -/
lemma mixture_seeded_risk_le_supplied_worst
    (D : Measure (Assign V × Audit V)) [IsProbabilityMeasure D]
    (π : Measure Ξ) [IsProbabilityMeasure π] (s : Ξ → Schedule V)
    (hm : Measurable (fun x : Ξ × (Assign V × Audit V) => recordOf (s x.1) x.2))
    (d : ℕ) (a : ℝ) (g : OffDiag V → Bool)
    (hs : ∀ᵐ u ∂π, ScheduleClass (s u) d ∧ tte (s u) = a)
    (hg : ∀ u, suppliedGraphOf (s u) = g) (T : SuppliedEstimator V) :
    (∫⁻ x, ENNReal.ofReal (((hardcodeSuppliedEstimator g T).1 x - a) ^ 2)
      ∂((mixtureLaw D π s).prod seedLaw)) ≤ suppliedWorstRisk D d T := by
  let : IsProbabilityMeasure seedLaw := ⟨by simp [seedLaw, Real.volume_Icc]⟩
  let T₀ := hardcodeSuppliedEstimator g T
  have hf : Measurable (fun x : Record V × ℝ => ENNReal.ofReal ((T₀.1 x - a) ^ 2)) :=
    ((T₀.2.sub measurable_const).pow_const 2).ennreal_ofReal
  rw [lintegral_prod _ hf.aemeasurable]
  unfold mixtureLaw
  rw [Measure.lintegral_bind (measurable_record_components D s hm).aemeasurable
    hf.lintegral_prod_right'.aemeasurable]
  calc
    _ ≤ ∫⁻ _ : Ξ, suppliedWorstRisk D d T ∂π := by
      apply lintegral_mono_ae
      filter_upwards [hs] with u hu
      have hr : Measurable (recordOf (s u)) :=
        hm.comp (measurable_const.prodMk measurable_id)
      rw [lintegral_map hf.lintegral_prod_right' hr]
      have heq : (∫⁻ ω, ∫⁻ v, ENNReal.ofReal ((T₀.1 (recordOf (s u) ω, v) - a) ^ 2)
          ∂seedLaw ∂D) = sqLoss D (s u) T₀ := by
        unfold sqLoss recordLaw
        rw [hu.2]
        have hmseed : Measurable (fun ω : (Assign V × Audit V) × ℝ =>
            (recordOf (s u) ω.1, ω.2)) :=
          (hr.comp measurable_fst).prodMk measurable_snd
        rw [lintegral_map hf hmseed]
        exact (lintegral_prod _ (hf.comp hmseed).aemeasurable).symm
      rw [heq, hardcodeSuppliedEstimator_sqLoss D (s u) g T (hg u)]
      exact le_iSup
        (fun θ : {θ : Schedule V // ScheduleClass θ d} => suppliedSqLoss D θ.1 T)
        ⟨s u, hu.1⟩
    _ = suppliedWorstRisk D d T := by simp

/-- The common deterministic complete-block graph allows testing against supplied worst risk.  [For the stated data and conditions](hyp:n,d,q,h,Δ,hq,hΔ,hs), [the stated conclusion holds](goal). -/
lemma completeBlock_supplied_two_prior
    (n d : ℕ) (q h Δ : ℝ) (hq : q ∈ Set.Icc 0 1) (hΔ : 0 < Δ)
    (hs : ∀ σ : Bool, ∀ᵐ U ∂(blockBaselineLaw (n / (d + 1))),
      ScheduleClass (completeBlockSchedule n d σ h U) d ∧
        tte (completeBlockSchedule n d σ h U) = signOf σ * Δ) :
    ENNReal.ofReal (Δ ^ 2 / 2 * (1 - Causalean.Stat.tvDist
      (mixtureLaw (thinnedDesign (Fin n) q) (blockBaselineLaw (n / (d + 1)))
        (completeBlockSchedule n d true h))
      (mixtureLaw (thinnedDesign (Fin n) q) (blockBaselineLaw (n / (d + 1)))
        (completeBlockSchedule n d false h)))) ≤
      suppliedMinimaxRisk (thinnedDesign (Fin n) q) d := by
  let D := thinnedDesign (Fin n) q
  let π := blockBaselineLaw (n / (d + 1))
  let g := suppliedGraphOf (completeBlockSchedule n d true 0 (fun _ => 0))
  let P := mixtureLaw D π (completeBlockSchedule n d true h)
  let M := mixtureLaw D π (completeBlockSchedule n d false h)
  let : IsProbabilityMeasure D := thinnedDesign_probabilityDesign q hq
  let : IsProbabilityMeasure π := blockBaselineLaw_probability _
  let : IsProbabilityMeasure seedLaw := ⟨by simp [seedLaw, Real.volume_Icc]⟩
  let : IsProbabilityMeasure P :=
    mixtureLaw_probability D π _ (completeBlock_record_measurable n d true h)
  let : IsProbabilityMeasure M :=
    mixtureLaw_probability D π _ (completeBlock_record_measurable n d false h)
  have hg (σ : Bool) (U : Fin (n / (d + 1)) → ℝ) :
      suppliedGraphOf (completeBlockSchedule n d σ h U) = g := rfl
  have htv : Causalean.Stat.tvDist (P.prod seedLaw) (M.prod seedLaw) =
      Causalean.Stat.tvDist P M := by
    simpa using Causalean.Stat.tvDist_compProd_eq P M (ProbabilityTheory.Kernel.const _ seedLaw)
  change _ ≤ ⨅ T : SuppliedEstimator (Fin n), suppliedWorstRisk D d T
  apply le_iInf
  intro T
  have hP := mixture_seeded_risk_le_supplied_worst D π _
    (completeBlock_record_measurable n d true h) d Δ g
    (by simpa [signOf] using hs true) (hg true) T
  have hM := mixture_seeded_risk_le_supplied_worst D π _
    (completeBlock_record_measurable n d false h) d (-Δ) g
    (by simpa [signOf] using hs false) (hg false) T
  have htest := two_prior_squared_testing (P.prod seedLaw) (M.prod seedLaw)
    (hardcodeSuppliedEstimator g T).1 (hardcodeSuppliedEstimator g T).2 Δ hΔ
    (suppliedWorstRisk D d T) hP hM
  rw [htv] at htest
  exact htest

/-- The unchanged support, distance, and algebra certify supplied-graph minimax risk.  [For the stated data and conditions](hyp:n,d,q,hn,hd,hdu,hq), [the stated conclusion holds](goal). -/
lemma completeBlock_supplied_risk_lower_assembly (n d : ℕ) (q : ℝ)
    (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n - 1) (hq : q ∈ Set.Icc 0 1) :
    ENNReal.ofReal ((160000 * Real.pi ^ 2)⁻¹ * min 1 (((d : ℝ) + 1) ^ 2 / n)) ≤
      suppliedMinimaxRisk (thinnedDesign (Fin n) q) d := by
  let h := completeBlockLowerAmplitude n d
  let ρ : ℝ := (((n / (d + 1)) * (d + 1) : ℕ) : ℝ) / n
  have hprop := completeBlockLowerAmplitude_properties n d (by omega)
  have hcov : (1 / 2 : ℝ) ≤ ρ := completeBlock_coverage_ge_half n d hn hdu
  have hh : 0 < h := hprop.1
  have hΔ : 0 < ρ * h := mul_pos (by linarith) hh
  let := blockBaselineLaw_probability (n / (d + 1))
  have hs (σ : Bool) : ∀ᵐ U ∂(blockBaselineLaw (n / (d + 1))),
      ScheduleClass (completeBlockSchedule n d σ h U) d ∧
        tte (completeBlockSchedule n d σ h U) = signOf σ * (ρ * h) := by
    filter_upwards [completeBlock_support n d σ h hprop.2.1] with U hU
    refine ⟨hU.1, hU.2.trans ?_⟩
    dsimp [ρ]
    ring
  let : IsProbabilityMeasure (thinnedDesign (Fin n) q) := thinnedDesign_probabilityDesign q hq
  have ht := completeBlock_supplied_two_prior n d q h (ρ * h) hq hΔ hs
  have htv := completeBlock_testing_distance n d (by omega) (thinnedDesign (Fin n) q)
    (thinnedDesign_assignment q hq)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) ht
  have hsep : h / 2 ≤ ρ * h := by nlinarith
  have hsqsep : h ^ 2 / 4 ≤ (ρ * h) ^ 2 := by nlinarith [sq_nonneg (ρ * h - h / 2)]
  have hscale : (160000 * Real.pi ^ 2)⁻¹ * min 1 (((d : ℝ) + 1) ^ 2 / n) =
      h ^ 2 / 16 := by
    rw [show h ^ 2 = _ from hprop.2.2]
    field_simp
    ring
  rw [hscale]
  change Causalean.Stat.tvDist
    (mixtureLaw (thinnedDesign (Fin n) q) (blockBaselineLaw (n / (d + 1)))
      (completeBlockSchedule n d true h))
    (mixtureLaw (thinnedDesign (Fin n) q) (blockBaselineLaw (n / (d + 1)))
      (completeBlockSchedule n d false h)) ≤ 1 / 50 at htv
  nlinarith [mul_nonneg (sq_nonneg (ρ * h))
    (show 0 ≤ 1 / 50 - Causalean.Stat.tvDist
      (mixtureLaw (thinnedDesign (Fin n) q) (blockBaselineLaw (n / (d + 1)))
        (completeBlockSchedule n d true h))
      (mixtureLaw (thinnedDesign (Fin n) q) (blockBaselineLaw (n / (d + 1)))
        (completeBlockSchedule n d false h)) from sub_nonneg.mpr htv)]

/-- The same lower bound holds for the entire original record and for that record with the
true graph additionally supplied. [For the stated data and conditions](hyp:n,d,q,D,hn,hd,hdu,hq,ha,hw,hi,supplied), [the stated conclusion holds](goal).

The optional observation selector defaults to the original-record inequality so that existing
consumers retain their statements and source proofs verbatim. Its other value certifies the
identical supplied-graph inequality. -/
-- @node: lem:supplied-block-record-lower
lemma supplied_block_record_lower (n d : ℕ) (q : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n)))
    (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n - 1) (hq : q ∈ Set.Icc 0 1)
    (ha : AssignmentLaw D) (hw : AuditLaw D q) (hi : DesignIndependent D)
    (supplied : Bool := false) :
    ENNReal.ofReal ((160000 * Real.pi ^ 2)⁻¹ * min 1 (((d : ℝ) + 1) ^ 2 / n)) ≤
      (if supplied then suppliedMinimaxRisk D d else minimaxRisk D d) := by
  rw [design_eq_thinnedDesign D q ha hw hi]
  cases supplied
  · exact completeBlock_risk_lower_assembly n d q hn hd hdu hq
  · exact completeBlock_supplied_risk_lower_assembly n d q hn hd hdu hq

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
