module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.ScoreMoments
public import Causalean.Mathlib.MeasureTheory.CondExpPreimage
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Tested conditional score identities

Bounded measurable score weights extend the tested conditional-mean and
exchangeability clauses, giving the population deleted-score objective.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped ENNReal

/-- A bounded almost everywhere measurable real function on a finite measure is integrable. -/
-- @node: score_bounded_integrable
lemma score_bounded_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (C : ℝ)
    (hf : AEMeasurable f μ) (hb : ∀ᵐ x ∂μ, |f x| ≤ C) : Integrable f μ := by
  exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (hb.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)

/-- Equality tested on score events extends to bounded score weights. -/
-- @node: score_tested_weighted_eq
lemma score_tested_weighted_eq {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (u v : Ω → ℝ) (hu : Integrable u μ) (hv : Integrable v μ)
    (htest : ∀ B : Set ℝ, MeasurableSet B →
      ∫ o in X ⁻¹' B, u o ∂μ = ∫ o in X ⁻¹' B, v o ∂μ)
    (w : ℝ → ℝ) (hw : AEMeasurable w (μ.map X))
    (C : ℝ) (hb : ∀ᵐ x ∂μ.map X, |w x| ≤ C) :
    ∫ o, w (X o) * u o ∂μ = ∫ o, w (X o) * v o ∂μ := by
  let m : MeasurableSpace Ω := MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)
  have hm : m ≤ mΩ := hX.comap_le
  letI : MeasurableSpace Ω := mΩ
  have hwX : AEStronglyMeasurable[m] (fun o => w (X o)) μ := by
    refine ⟨fun o => hw.mk w (X o), ?_, ?_⟩
    · exact hw.measurable_mk.stronglyMeasurable.comp_measurable (comap_measurable X)
    · exact ae_eq_comp hX.aemeasurable hw.ae_eq_mk
  have hbX : ∀ᵐ o ∂μ, ‖w (X o)‖ ≤ C := by
    have h := ae_of_ae_map hX.aemeasurable hb
    simpa [Real.norm_eq_abs] using h
  have hwu : Integrable (fun o => w (X o) * u o) μ :=
    hu.bdd_mul (hwX.mono hm) hbX
  have hwv : Integrable (fun o => w (X o) * v o) μ :=
    hv.bdd_mul (hwX.mono hm) hbX
  have hzero : μ[(fun o => u o-v o) | m] =ᵐ[μ] (fun _ => (0:ℝ)) := by
    apply Causalean.Mathlib.MeasureTheory.condExp_eq_of_integral_preimage_eq
      μ X hX (fun o => u o-v o) (fun _ => 0) (hu.sub hv) (integrable_const 0)
      aestronglyMeasurable_const
    intro B hB
    rw [integral_sub hu.integrableOn hv.integrableOn, htest B hB]
    simp
  have hpull := condExp_mul_of_aestronglyMeasurable_left hwX
    (hwu.sub hwv |>.congr (by filter_upwards with o; simp [mul_sub])) (hu.sub hv)
  have hprod : μ[(fun o => w (X o) * (u o-v o)) | m] =ᵐ[μ] (fun _ => (0:ℝ)) := by
    filter_upwards [hpull, hzero] with o ho hz
    change μ[(fun o => w (X o) * (u o-v o)) | m] o =
      w (X o) * μ[(fun o => u o-v o) | m] o at ho
    rw [hz, mul_zero] at ho
    exact ho
  have hi : (∫ o, w (X o) * (u o-v o) ∂μ) = 0 := by
    rw [← integral_condExp hm]
    exact (integral_congr_ae hprod).trans (by simp)
  have heq : (fun o => w (X o) * (u o-v o)) =
      (fun o => w (X o)*u o-w (X o)*v o) := by funext o; ring
  rw [heq, integral_sub hwu hwv] at hi
  exact sub_eq_zero.mp hi

/-- The conditional effect is measurable on the score marginal. -/
-- @node: score_tau_aemeasurable
lemma score_tau_aemeasurable (P : RowLaw) (hwf : WellFormed P) :
    AEMeasurable P.tau P.PX := by
  have hs : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0:ℝ) 1 :=
    (ae_map_iff fullRow_X_measurable.aemeasurable measurableSet_Icc).2
      (ae_iff.mpr hwf.2.1)
  have h := aemeasurable_restrict_of_measurable_subtype
    (μ := P.PX) measurableSet_Icc hwf.2.2.2.2.1
  rwa [Measure.restrict_eq_self_of_ae_mem hs] at h

/-- A Borel binary policy is measurable on the score marginal. -/
-- @node: score_policy_aemeasurable
lemma score_policy_aemeasurable (P : RowLaw) (hwf : WellFormed P)
    (π : ℝ → Bool) (hπ : π ∈ binaryPolicyClass) : AEMeasurable π P.PX := by
  have hs : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0:ℝ) 1 :=
    (ae_map_iff fullRow_X_measurable.aemeasurable measurableSet_Icc).2
      (ae_iff.mpr hwf.2.1)
  have h := aemeasurable_restrict_of_measurable_subtype
    (μ := P.PX) measurableSet_Icc hπ
  rwa [Measure.restrict_eq_self_of_ae_mem hs] at h

/-- The full-row coordinates are measurable for the concrete row sigma-algebra. -/
-- @node: score_full_coordinates_measurable
lemma score_full_coordinates_measurable :
    Measurable (fun o : FullRow => (o.X,o.A,o.Y,o.Y0,o.Y1)) := by
  exact comap_measurable _

/-- Conditional exchangeability with an arbitrary bounded measurable score weight. -/
-- @node: score_exchangeability_weighted
lemma score_exchangeability_weighted (P : RowLaw) (hwf : WellFormed P)
    (hbounded : BoundedPotentials P) (hex : Exchangeability P)
    (he : ∀ᵐ x ∂P.PX, 0 < P.logger x ∧ P.logger x < 1)
    (a : Bool) (w : ℝ → ℝ) (hw : AEMeasurable w P.PX)
    (C : ℝ) (hb : ∀ᵐ x ∂P.PX, |w x| ≤ C) :
    ∫ o, w o.X * (if o.A = a then (if a then o.Y1 else o.Y0) else 0) ∂P.full =
      ∫ o, w o.X * ((if a then P.logger o.X else 1-P.logger o.X) *
        (if a then o.Y1 else o.Y0)) ∂P.full := by
  letI : IsProbabilityMeasure P.full := hwf.1
  have hAm : Measurable (fun o : FullRow => o.A) :=
    (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ => t.2.1)).comp
      score_full_coordinates_measurable
  have hYm : Measurable (fun o : FullRow => (o.Y0,o.Y1)) :=
    (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ => (t.2.2.2.1,t.2.2.2.2))).comp
      score_full_coordinates_measurable
  let g : ℝ × ℝ → ℝ := fun y => max (-1) (min 1 (if a then y.2 else y.1))
  have hg : Measurable g := by cases a <;> dsimp [g] <;> fun_prop
  have hgBound : ∀ y, |g y| ≤ 1 := by
    intro y
    apply abs_le.mpr
    dsimp [g]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have heFull := ae_of_ae_map fullRow_X_measurable.aemeasurable he
  have hq : AEMeasurable (fun o : FullRow => if a then P.logger o.X else 1-P.logger o.X) P.full := by
    have hl := (logger_aemeasurable P hwf).comp_measurable fullRow_X_measurable
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hu : Integrable (fun o : FullRow => if o.A = a then g (o.Y0,o.Y1) else 0) P.full := by
    apply score_bounded_integrable 1
    · exact (Measurable.ite (hAm (measurableSet_singleton a)) (hg.comp hYm)
        measurable_const).aemeasurable
    · exact ae_of_all _ fun o => by by_cases h : o.A = a <;> simp [h, hgBound]
  have hv : Integrable (fun o : FullRow =>
      (if a then P.logger o.X else 1-P.logger o.X) * g (o.Y0,o.Y1)) P.full := by
    apply score_bounded_integrable 1 (hq.mul (hg.comp hYm).aemeasurable)
    filter_upwards [heFull] with o ho
    change |(if a then P.logger o.X else 1-P.logger o.X) * g (o.Y0,o.Y1)| ≤ 1
    rw [abs_mul]
    have hqb : |(if a then P.logger o.X else 1-P.logger o.X)| ≤ 1 := by
      cases a <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [abs_of_nonneg (by linarith [ho.2])]; linarith [ho.1]
      · rw [abs_of_nonneg ho.1.le]; exact ho.2.le
    exact (mul_le_mul hqb (hgBound _) (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have ht : ∀ B : Set ℝ, MeasurableSet B →
      ∫ o in FullRow.X ⁻¹' B, (if o.A = a then g (o.Y0,o.Y1) else 0) ∂P.full =
      ∫ o in FullRow.X ⁻¹' B,
        (if a then P.logger o.X else 1-P.logger o.X) * g (o.Y0,o.Y1) ∂P.full := by
    intro B hB
    have hA : MeasurableSet {o : FullRow | o.A = a} := hAm (measurableSet_singleton a)
    have hi : (fun o : FullRow => if o.A = a then g (o.Y0,o.Y1) else 0) =
        {o : FullRow | o.A = a}.indicator (fun o => g (o.Y0,o.Y1)) := by
      funext o; simp [Set.indicator]
    rw [hi]
    change (∫ o in FullRow.X ⁻¹' B, {o : FullRow | o.A = a}.indicator
      (fun o => g (o.Y0,o.Y1)) o ∂P.full) = _
    rw [setIntegral_indicator hA]
    have hs : FullRow.X ⁻¹' B ∩ {o : FullRow | o.A = a} =
        {o : FullRow | o.X ∈ B ∧ o.A = a} := rfl
    rw [hs]
    exact hex B hB g hg ⟨1, hgBound⟩ a
  have hid := score_tested_weighted_eq P.full FullRow.X fullRow_X_measurable
    _ _ hu hv ht w hw C hb
  have hgeq : ∀ᵐ o ∂P.full, g (o.Y0,o.Y1) = (if a then o.Y1 else o.Y0) := by
    filter_upwards [hbounded] with o ho
    cases a <;> simp only [g, Bool.false_eq_true, ↓reduceIte]
    · rw [min_eq_right ho.1.2, max_eq_right ho.1.1]
    · rw [min_eq_right ho.2.2, max_eq_right ho.2.1]
  calc
    _ = ∫ o, w o.X * (if o.A = a then g (o.Y0,o.Y1) else 0) ∂P.full := by
      apply integral_congr_ae
      filter_upwards [hgeq] with o ho
      rw [ho]
    _ = _ := hid
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hgeq] with o ho
      rw [ho]

/-- The deleted inverse-propensity contrast has the retained conditional effect. -/
-- @node: score_gamma_weighted_identity
lemma score_gamma_weighted_identity (P : RowLaw) (hwf : WellFormed P)
    (hbounded : BoundedPotentials P) (hc : Consistency P) (hex : Exchangeability P)
    (he : ∀ᵐ x ∂P.PX, 0 < P.logger x ∧ P.logger x < 1)
    (ht : ∀ᵐ x ∂P.PX, |P.tau x| ≤ 2)
    (a : ℝ) (ha : 0 < a) (w : ℝ → ℝ) (hw : AEMeasurable w P.PX)
    (hb : ∀ᵐ x ∂P.PX, |w x| ≤ 1) :
    ∫ o, w o.X * gammaScore a P.logger ⟨o.X,o.A,o.Y⟩ ∂P.full =
      ∫ x, w x * (if a ≤ overlap P x then P.tau x else 0) ∂P.PX := by
  letI : IsProbabilityMeasure P.full := hwf.1
  letI : IsFiniteMeasure P.PX := ⟨by
    rw [RowLaw.PX, Measure.map_apply fullRow_X_measurable MeasurableSet.univ]; simp⟩
  have hl := logger_aemeasurable P hwf
  have hret : NullMeasurableSet {x | a ≤ overlap P x} P.PX := by
    apply nullMeasurableSet_le aemeasurable_const
    change AEMeasurable (fun x => min (P.logger x) (1-P.logger x)) P.PX
    fun_prop
  let W : Bool → ℝ → ℝ := fun b x =>
    if a ≤ overlap P x then w x / (if b then P.logger x else 1-P.logger x) else 0
  have hW (b : Bool) : AEMeasurable (W b) P.PX := by
    have hq : AEMeasurable (fun x => if b then P.logger x else 1-P.logger x) P.PX := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
    convert (hw.div hq).indicator₀ hret using 1
    ext x; simp [W, Set.indicator]
  have hWb (b : Bool) : ∀ᵐ x ∂P.PX, |W b x| ≤ 1/a := by
    filter_upwards [he, hb] with x hx hwx
    dsimp [W]
    by_cases hr : a ≤ overlap P x
    · rw [if_pos hr]
      have hqa : a ≤ (if b then P.logger x else 1-P.logger x) := by
        cases b
        · exact hr.trans (min_le_right _ _)
        · exact hr.trans (min_le_left _ _)
      have hq : 0 < (if b then P.logger x else 1-P.logger x) := ha.trans_le hqa
      rw [abs_div, abs_of_pos hq]
      exact (div_le_div_of_nonneg_right hwx hq.le).trans
        (div_le_div_of_nonneg_left (by norm_num) ha hqa)
    · rw [if_neg hr, abs_zero]
      positivity
  have hAm : Measurable (fun o : FullRow => o.A) :=
    (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ => t.2.1)).comp
      score_full_coordinates_measurable
  have hY0 : Measurable (fun o : FullRow => o.Y0) :=
    (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ => t.2.2.2.1)).comp
      score_full_coordinates_measurable
  have hY1 : Measurable (fun o : FullRow => o.Y1) :=
    (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ => t.2.2.2.2)).comp
      score_full_coordinates_measurable
  have hleftInt (b : Bool) : Integrable (fun o : FullRow =>
      W b o.X * (if o.A = b then (if b then o.Y1 else o.Y0) else 0)) P.full := by
    apply score_bounded_integrable (1/a)
    · have hYm : Measurable (fun o : FullRow => if b then o.Y1 else o.Y0) := by
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> assumption
      exact ((hW b).comp_measurable fullRow_X_measurable).mul
        (Measurable.ite (hAm (measurableSet_singleton b)) hYm measurable_const).aemeasurable
    · filter_upwards [ae_of_ae_map fullRow_X_measurable.aemeasurable (hWb b), hbounded]
        with o ho hy
      rw [abs_mul]
      have hyb : |(if o.A = b then (if b then o.Y1 else o.Y0) else 0)| ≤ 1 := by
        split_ifs with hA hb
        · exact abs_le.mpr hy.2
        · exact abs_le.mpr hy.1
        · norm_num
      simpa using mul_le_mul ho hyb (abs_nonneg _) (by positivity : 0 ≤ 1/a)
  let wr : ℝ → ℝ := fun x => if a ≤ overlap P x then w x else 0
  have hwr : AEMeasurable wr P.PX := by
    convert hw.indicator₀ hret using 1
    ext x; simp [wr, Set.indicator]
  have hwrb : ∀ᵐ x ∂P.PX, |wr x| ≤ 1 := by
    filter_upwards [hb] with x hx
    dsimp [wr]; split_ifs <;> simp_all
  have hrightInt (b : Bool) : Integrable (fun o : FullRow =>
      wr o.X * (if b then o.Y1 else o.Y0)) P.full := by
    apply score_bounded_integrable 1
    · have hYm : Measurable (fun o : FullRow => if b then o.Y1 else o.Y0) := by
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> assumption
      exact ((hwr.comp_measurable fullRow_X_measurable).mul hYm.aemeasurable)
    · filter_upwards [ae_of_ae_map fullRow_X_measurable.aemeasurable hwrb, hbounded]
        with o ho hy
      rw [abs_mul]
      have hby : |(if b then o.Y1 else o.Y0)| ≤ 1 := by
        cases b; exact abs_le.mpr hy.1; exact abs_le.mpr hy.2
      simpa using mul_le_mul ho hby (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have harm (b : Bool) :
      ∫ o, W b o.X * (if o.A = b then (if b then o.Y1 else o.Y0) else 0) ∂P.full =
        ∫ o, wr o.X * (if b then o.Y1 else o.Y0) ∂P.full := by
    rw [score_exchangeability_weighted P hwf hbounded hex he b (W b) (hW b) (1/a) (hWb b)]
    apply integral_congr_ae
    filter_upwards [ae_of_ae_map fullRow_X_measurable.aemeasurable he] with o ho
    have hq : (if b then P.logger o.X else 1-P.logger o.X) ≠ 0 := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact ne_of_gt (by linarith [ho.2])
      · exact ne_of_gt ho.1
    dsimp [W, wr]
    by_cases hr : a ≤ overlap P o.X
    · rw [if_pos hr, if_pos hr]
      field_simp [hq]
    · simp only [if_neg hr, zero_mul]
  have hgamma : (fun o : FullRow => w o.X * gammaScore a P.logger ⟨o.X,o.A,o.Y⟩) =ᵐ[P.full]
      (fun o => W true o.X * (if o.A = true then o.Y1 else 0) -
        W false o.X * (if o.A = false then o.Y0 else 0)) := by
    filter_upwards [hc] with o ho
    dsimp [W, gammaScore, overlap]
    rw [ho]
    cases o.A <;> split_ifs <;> simp_all <;> ring
  have hYu : Integrable (fun o : FullRow => o.Y1-o.Y0) P.full := by
    apply score_bounded_integrable 2 (hY1.sub hY0).aemeasurable
    filter_upwards [hbounded] with o ho
    change |o.Y1-o.Y0| ≤ 2
    exact abs_le.mpr (by constructor <;> linarith [ho.1.1,ho.1.2,ho.2.1,ho.2.2])
  have htInt : Integrable (fun o : FullRow => P.tau o.X) P.full := by
    apply score_bounded_integrable 2 ((score_tau_aemeasurable P hwf).comp_measurable fullRow_X_measurable)
    exact ae_of_ae_map fullRow_X_measurable.aemeasurable ht
  have hmean := score_tested_weighted_eq P.full FullRow.X fullRow_X_measurable
    (fun o => o.Y1-o.Y0) (fun o => P.tau o.X) hYu htInt
    (by
      intro B hB
      rw [← setIntegral_map hB (score_tau_aemeasurable P hwf).aestronglyMeasurable
        fullRow_X_measurable.aemeasurable]
      exact hwf.2.2.2.2.2.2 B hB)
    wr hwr 1 hwrb
  calc
    _ = ∫ o, W true o.X * (if o.A = true then o.Y1 else 0) -
        W false o.X * (if o.A = false then o.Y0 else 0) ∂P.full := integral_congr_ae hgamma
    _ = (∫ o, W true o.X * (if o.A = true then o.Y1 else 0) ∂P.full) -
        ∫ o, W false o.X * (if o.A = false then o.Y0 else 0) ∂P.full :=
      integral_sub (hleftInt true) (hleftInt false)
    _ = (∫ o, wr o.X * o.Y1 ∂P.full) - ∫ o, wr o.X * o.Y0 ∂P.full := by
      simpa only [Bool.false_eq_true, ↓reduceIte] using congrArg₂ (· - ·) (harm true) (harm false)
    _ = ∫ o, wr o.X * (o.Y1-o.Y0) ∂P.full := by
      have hi1 : Integrable (fun o => wr o.X * o.Y1) P.full := hrightInt true
      have hi0 : Integrable (fun o => wr o.X * o.Y0) P.full := hrightInt false
      rw [← integral_sub hi1 hi0]
      congr 1; funext o; ring
    _ = ∫ o, wr o.X * P.tau o.X ∂P.full := hmean
    _ = ∫ x, wr x * P.tau x ∂P.PX :=
      (integral_map fullRow_X_measurable.aemeasurable
        (hwr.mul (score_tau_aemeasurable P hwf)).aestronglyMeasurable).symm
    _ = _ := by
      congr 1; funext x; dsimp [wr]; split_ifs <;> simp

/-- The observable projection of a full row is measurable. -/
-- @node: score_observation_map_measurable
lemma score_observation_map_measurable :
    Measurable (fun o : FullRow => (⟨o.X,o.A,o.Y⟩ : Observation)) := by
  apply measurable_comap_iff.mpr
  exact (by fun_prop : Measurable
    (fun t : ℝ × Bool × ℝ × ℝ × ℝ => (t.1,t.2.1,t.2.2.1))).comp
    score_full_coordinates_measurable

/-- The score coordinate of an observation is measurable. -/
-- @node: score_observation_X_measurable
lemma score_observation_X_measurable : Measurable (fun o : Observation => o.X) := by
  exact (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.1)).comp
    (comap_measurable _)

/-- The observable score marginal agrees with the full-row score marginal. -/
-- @node: score_observation_X_map
lemma score_observation_X_map (P : RowLaw) :
    P.obsLaw.map Observation.X = P.PX := by
  rw [RowLaw.obsLaw, RowLaw.PX,
    Measure.map_map score_observation_X_measurable score_observation_map_measurable]
  rfl

/-- The deleted contrast and offset are measurable on the observable law. -/
-- @node: score_z_aemeasurable
@[fun_prop] lemma score_z_aemeasurable (P : RowLaw) (hwf : WellFormed P) (a : ℝ) :
    AEMeasurable (zScore a P.logger) P.obsLaw := by
  have hl := logger_aemeasurable P hwf
  let elog := hl.mk P.logger
  have helog : Measurable elog := hl.measurable_mk
  have hret : MeasurableSet {o : Observation | a ≤ min (elog o.X) (1-elog o.X)} :=
    measurableSet_le measurable_const
      ((helog.comp score_observation_X_measurable).min
        (measurable_const.sub (helog.comp score_observation_X_measurable)))
  have hAm : Measurable (fun o : Observation => o.A) :=
    (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.2.1)).comp
      (comap_measurable _)
  have hYm : Measurable (fun o : Observation => o.Y) :=
    (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.2.2)).comp
      (comap_measurable _)
  have hz : Measurable (zScore a elog) := by
    have hg : Measurable (gammaScore a elog) := by
      apply Measurable.ite hret
      · exact Measurable.ite (hAm (measurableSet_singleton true))
          (hYm.div (helog.comp score_observation_X_measurable))
          ((hYm.div (measurable_const.sub (helog.comp score_observation_X_measurable))).neg)
      · exact measurable_const
    have ho : Measurable (fun o : Observation => offsetG a elog o.X) := by
      have hXm := score_observation_X_measurable
      unfold offsetG; fun_prop
    exact hg.add ho
  apply hz.aemeasurable.congr
  have hlobs : ∀ᵐ o ∂P.obsLaw, P.logger o.X = elog o.X := by
    refine ae_of_ae_map score_observation_X_measurable.aemeasurable
      (p := fun x => P.logger x = elog x) ?_
    rw [score_observation_X_map]
    exact hl.ae_eq_mk
  filter_upwards [hlobs] with o ho
  simp only [zScore, gammaScore, offsetG]
  rw [ho]

/-- The negative-action indicator of a measurable binary rule is measurable. -/
-- @node: score_negative_action_aemeasurable
lemma score_negative_action_aemeasurable {μ : Measure ℝ} (π : ℝ → Bool)
    (hπ : AEMeasurable π μ) :
    AEMeasurable (fun x => if π x then (0:ℝ) else 1) μ := by
  have hm : Measurable (fun x => if hπ.mk π x then (0:ℝ) else 1) :=
    Measurable.ite (hπ.measurable_mk (measurableSet_singleton true))
      measurable_const measurable_const
  apply hm.aemeasurable.congr
  filter_upwards [hπ.ae_eq_mk] with x hx
  rw [hx]

/-- The canonical tie convention gives a measurable binary rule. -/
-- @node: score_canonical_aemeasurable
@[fun_prop] lemma score_canonical_aemeasurable (P : RowLaw) (hwf : WellFormed P) :
    AEMeasurable (canonicalPolicy P) P.PX := by
  have ht := score_tau_aemeasurable P hwf
  have hm : Measurable (fun x => decide (0 ≤ ht.mk P.tau x)) := by
    have heq : (fun x => decide (0 ≤ ht.mk P.tau x)) =
        (fun x => if 0 ≤ ht.mk P.tau x then true else false) := by
      funext x; split_ifs <;> simp_all
    rw [heq]
    exact Measurable.ite (measurableSet_le measurable_const ht.measurable_mk)
      measurable_const measurable_const
  apply hm.aemeasurable.congr
  filter_upwards [ht.ae_eq_mk] with x hx
  simp only [canonicalPolicy, hx]

/-- The population objective is the negative-action weighted retained effect plus offset. -/
-- @node: score_popObjective_identity
lemma score_popObjective_identity (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hClass : LawClass α γ θ n P e)
    (a : ℝ) (ha : 0 < a ∧ a ≤ 1/4) (π : ℝ → Bool)
    (hπ : AEMeasurable π P.PX) :
    popObjective P a π = ∫ x, (if π x then (0:ℝ) else 1) *
      ((if a ≤ overlap P x then P.tau x else 0) + offsetG a P.logger x) ∂P.PX := by
  letI : IsProbabilityMeasure P.full := hClass.wf.1
  letI : IsProbabilityMeasure P.PX := hClass.score.1
  letI : IsFiniteMeasure P.obsLaw := ⟨by
    rw [RowLaw.obsLaw, Measure.map_apply score_observation_map_measurable MeasurableSet.univ]; simp⟩
  have hs : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0:ℝ) 1 := ae_iff.mpr hClass.score.2
  have he : ∀ᵐ x ∂P.PX, 0 < P.logger x ∧ P.logger x < 1 := by
    filter_upwards [hClass.positive, hs] with x hx hxs
    simpa only [hClass.known hxs] using hx
  have heSpace : ∀ x ∈ Set.Icc (0:ℝ) 1, P.logger x ∈ Set.Ioo (0:ℝ) 1 := by
    intro x hx
    simpa only [hClass.known hx] using hClass.loggerSpace x hx
  let w : ℝ → ℝ := fun x => if π x then 0 else 1
  have hw := score_negative_action_aemeasurable π hπ
  have hwb : ∀ᵐ x ∂P.PX, |w x| ≤ 1 := ae_of_all _ fun x => by
    dsimp [w]; cases π x <;> norm_num
  have hwobs : AEMeasurable (fun o : Observation => w o.X) P.obsLaw := by
    have hwmap : AEMeasurable w (P.obsLaw.map Observation.X) := by
      rw [score_observation_X_map]; exact hw
    exact hwmap.comp_measurable score_observation_X_measurable
  have hz := score_z_aemeasurable P hClass.wf a
  have hg : AEMeasurable (offsetG a P.logger) P.PX := by
    have hl := logger_aemeasurable P hClass.wf
    unfold offsetG; fun_prop
  have hgb : ∀ᵐ x ∂P.PX, |offsetG a P.logger x| ≤ 1 := by
    filter_upwards [he] with x hx
    have hp : 0 < min (P.logger x) (1-P.logger x) := lt_min hx.1 (by linarith [hx.2])
    have hg0 : 0 ≤ offsetG a P.logger x :=
      le_min (by norm_num) (div_nonneg ha.1.le hp.le)
    rw [abs_of_nonneg hg0]
    exact min_le_left _ _
  have hwg : Integrable (fun x => w x * offsetG a P.logger x) P.PX := by
    apply score_bounded_integrable 1 (hw.mul hg)
    filter_upwards [hwb, hgb] with x hx hy
    change |w x * offsetG a P.logger x| ≤ 1
    rw [abs_mul]
    simpa using mul_le_mul hx hy (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hwgFull : Integrable (fun o : FullRow => w o.X * offsetG a P.logger o.X) P.full :=
    (integrable_map_measure (hw.mul hg).aestronglyMeasurable fullRow_X_measurable.aemeasurable).mp hwg
  have hwzObs : Integrable (fun o : Observation => w o.X * zScore a P.logger o) P.obsLaw := by
    apply score_bounded_integrable (2/a) (hwobs.mul hz)
    have hwbObs : ∀ᵐ o ∂P.obsLaw, |w o.X| ≤ 1 := by
      refine ae_of_ae_map score_observation_X_measurable.aemeasurable
        (p := fun x => |w x| ≤ 1) ?_
      rw [score_observation_X_map]; exact hwb
    filter_upwards [hwbObs, zScore_abs_ae P a ha hClass.wf heSpace] with o hx hy
    change |w o.X * zScore a P.logger o| ≤ 2/a
    rw [abs_mul]
    simpa using mul_le_mul hx hy (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hwzFull : Integrable (fun o : FullRow => w o.X * zScore a P.logger ⟨o.X,o.A,o.Y⟩) P.full :=
    (integrable_map_measure (hwobs.mul hz).aestronglyMeasurable
      score_observation_map_measurable.aemeasurable).mp hwzObs
  have hwgamma : Integrable (fun o : FullRow => w o.X * gammaScore a P.logger ⟨o.X,o.A,o.Y⟩) P.full := by
    convert hwzFull.sub hwgFull using 1
    ext o; dsimp [zScore]; ring
  have hret : NullMeasurableSet {x | a ≤ overlap P x} P.PX := by
    apply nullMeasurableSet_le aemeasurable_const
    change AEMeasurable (fun x => min (P.logger x) (1-P.logger x)) P.PX
    have hl := logger_aemeasurable P hClass.wf
    fun_prop
  have hrt : AEMeasurable (fun x => if a ≤ overlap P x then P.tau x else 0) P.PX := by
    convert (score_tau_aemeasurable P hClass.wf).indicator₀ hret using 1
    ext x; simp [Set.indicator]
  have hwrt : Integrable (fun x => w x * (if a ≤ overlap P x then P.tau x else 0)) P.PX := by
    apply score_bounded_integrable 2 (hw.mul hrt)
    filter_upwards [hwb, hClass.effectBound] with x hx hy
    have hrb : |(if a ≤ overlap P x then P.tau x else 0)| ≤ 2 := by
      split_ifs <;> simp_all
    change |w x * (if a ≤ overlap P x then P.tau x else 0)| ≤ 2
    rw [abs_mul]
    simpa using mul_le_mul hx hrb (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  change (∫ o, w o.X * zScore a P.logger o ∂P.obsLaw) = _
  rw [RowLaw.obsLaw, integral_map (f := fun o : Observation => w o.X * zScore a P.logger o)
    score_observation_map_measurable.aemeasurable (hwobs.mul hz).aestronglyMeasurable]
  calc
    _ = (∫ o, w o.X * gammaScore a P.logger ⟨o.X,o.A,o.Y⟩ ∂P.full) +
        ∫ o, w o.X * offsetG a P.logger o.X ∂P.full := by
      rw [← integral_add hwgamma hwgFull]
      congr 1; funext o; dsimp [zScore]; ring
    _ = (∫ x, w x * (if a ≤ overlap P x then P.tau x else 0) ∂P.PX) +
        ∫ x, w x * offsetG a P.logger x ∂P.PX := by
      rw [score_gamma_weighted_identity P hClass.wf hClass.bounded hClass.consistent
        hClass.exchangeable he hClass.effectBound a ha.1 w hw hwb]
      rw [← integral_map (f := fun x => w x * offsetG a P.logger x)
        fullRow_X_measurable.aemeasurable (hw.mul hg).aestronglyMeasurable]
      rfl
    _ = _ := by
      rw [← integral_add hwrt hwg]
      congr 1; funext x; dsimp [w]; ring

end CausalSmith.Stat.ScorethresholdOverlapRegret
