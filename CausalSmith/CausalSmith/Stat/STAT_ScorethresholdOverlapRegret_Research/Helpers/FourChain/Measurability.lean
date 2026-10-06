module
public import Causalean.Stat.EmpiricalProcess.Countable
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.FourChain.MeasurabilityFamilies

/-! # Score-threshold overlap regret — atom-safe process measurability

On the supported observation space, the deleted score is integrable despite the
logger being specified only almost everywhere. An atom-safe countable reduction
then identifies the full localized process with the finite maximum of its two
cutoff orientations and the constant-false policy.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

private lemma ae_nonneg_of_locally_bounded_setIntegrals
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f)
    (hset : ∀ s : Set Ω, MeasurableSet s → IntegrableOn f s μ →
      0 ≤ ∫ x in s, f x ∂μ) :
    0 ≤ᵐ[μ] f := by
  let T : ℕ → Set Ω := fun k => {x | |f x| ≤ k}
  have hT (k : ℕ) : MeasurableSet (T k) :=
    measurableSet_le hf.norm measurable_const
  have hlocal (k : ℕ) : IntegrableOn f (T k) μ := by
    apply IntegrableOn.of_bound (measure_lt_top μ (T k))
      hf.aestronglyMeasurable.restrict (k : ℝ)
    filter_upwards [self_mem_ae_restrict (hT k)] with x hx
    change |f x| ≤ (k : ℝ)
    exact hx
  have hk (k : ℕ) : 0 ≤ᵐ[μ.restrict (T k)] f :=
    ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter (hlocal k)
      (fun s hs _ => hset (s ∩ T k) (hs.inter (hT k))
        ((hlocal k).mono_set Set.inter_subset_right))
  have hk' (k : ℕ) : ∀ᵐ x ∂μ, x ∈ T k → 0 ≤ f x :=
    (ae_restrict_iff' (hT k)).1 (hk k)
  have hall : ∀ᵐ x ∂μ, ∀ k : ℕ, x ∈ T k → 0 ≤ f x :=
    ae_all_iff.2 hk'
  filter_upwards [hall] with x hx
  obtain ⟨k, hkx⟩ := exists_nat_gt |f x|
  exact hx k hkx.le

private lemma logger_ae_mem_Icc (P : RowLaw) (hP : WellFormed P) :
    ∀ᵐ x ∂P.PX, P.logger x ∈ Set.Icc (0 : ℝ) 1 := by
  letI : IsProbabilityMeasure P.full := hP.1
  letI : IsProbabilityMeasure P.PX :=
    Measure.isProbabilityMeasure_map fullRow_X_measurable.aemeasurable
  have hl := logger_aemeasurable P hP
  let e : ℝ → ℝ := hl.mk P.logger
  have he : Measurable e := hl.measurable_mk
  have heq : P.logger =ᵐ[P.PX] e := hl.ae_eq_mk
  have he0 : 0 ≤ᵐ[P.PX] e := by
    apply ae_nonneg_of_locally_bounded_setIntegrals P.PX e he
    intro B hB _
    rw [integral_congr_ae (heq.symm.restrict)]
    rw [← hP.2.2.2.2.2.1 B hB]
    exact integral_nonneg_of_ae (ae_of_all _ fun o => by positivity)
  have he1 : 0 ≤ᵐ[P.PX] fun x => 1 - e x := by
    apply ae_nonneg_of_locally_bounded_setIntegrals P.PX (fun x => 1 - e x)
      (measurable_const.sub he)
    intro B hB hdiff
    have hX : MeasurableSet {o : FullRow | o.X ∈ B} :=
      fullRow_X_measurable hB
    have htreated : IntegrableOn
        (fun o : FullRow => if o.A then (1 : ℝ) else 0)
        {o | o.X ∈ B} P.full := by
      refine IntegrableOn.of_bound (measure_lt_top _ _) ?_ 1 ?_
      · have hA : Measurable (fun o : FullRow => o.A) := by
          have hc := score_full_coordinates_measurable
          exact (by fun_prop : Measurable
            (fun q : ℝ × Bool × ℝ × ℝ × ℝ => q.2.1)).comp hc
        exact (Measurable.ite (hA (measurableSet_singleton true))
          measurable_const measurable_const).aestronglyMeasurable.restrict
      · filter_upwards with o
        cases o.A <;> norm_num
    have hle : (∫ o in {o : FullRow | o.X ∈ B},
          (if o.A then (1 : ℝ) else 0) ∂P.full) ≤
        P.PX.real B := by
      have hm : (∫ o in {o : FullRow | o.X ∈ B},
          (if o.A then (1 : ℝ) else 0) ∂P.full) ≤
          ∫ _ in {o : FullRow | o.X ∈ B}, (1 : ℝ) ∂P.full := by
        apply setIntegral_mono_ae htreated integrableOn_const
        filter_upwards with o
        cases o.A <;> norm_num
      rw [setIntegral_one_eq_measureReal] at hm
      rw [RowLaw.PX, measureReal_def,
        Measure.map_apply fullRow_X_measurable hB]
      exact hm
    rw [integral_sub]
    · rw [setIntegral_one_eq_measureReal,
        integral_congr_ae (heq.symm.restrict), ← hP.2.2.2.2.2.1 B hB]
      exact sub_nonneg.mpr hle
    · exact integrableOn_const
    · change IntegrableOn e B P.PX
      have ht := (integrableOn_const (μ := P.PX) (C := (1 : ℝ))).sub hdiff
      apply ht.congr
      filter_upwards with x
      simp
  filter_upwards [heq, he0, he1] with x hx hx0 hx1
  exact ⟨by simpa [hx] using hx0, by simpa [hx] using sub_nonneg.mp hx1⟩

private lemma zScore_abs_le_of_logger_mem_Icc (a : ℝ) (e : ℝ → ℝ)
    (o : Observation) (ha : 0 < a) (he : e o.X ∈ Set.Icc (0 : ℝ) 1)
    (hY : o.Y ∈ Set.Icc (-1 : ℝ) 1) :
    |zScore a e o| ≤ 1 / a + 1 := by
  have hp : 0 ≤ min (e o.X) (1 - e o.X) :=
    le_min he.1 (by linarith [he.2])
  have hg : 0 ≤ offsetG a e o.X ∧ offsetG a e o.X ≤ 1 := by
    unfold offsetG
    exact ⟨le_min (by norm_num) (div_nonneg ha.le hp), min_le_left _ _⟩
  have hgamma : |gammaScore a e o| ≤ 1 / a := by
    unfold gammaScore
    split_ifs with hret hA
    · have hae : a ≤ e o.X := hret.trans (min_le_left _ _)
      rw [abs_div, abs_of_pos (ha.trans_le hae)]
      exact (div_le_div_of_nonneg_right (abs_le.mpr hY) (ha.trans_le hae).le).trans
        (div_le_div_of_nonneg_left (by norm_num) ha hae)
    · have hae : a ≤ 1 - e o.X := hret.trans (min_le_right _ _)
      rw [abs_neg, abs_div, abs_of_pos (ha.trans_le hae)]
      exact (div_le_div_of_nonneg_right (abs_le.mpr hY) (ha.trans_le hae).le).trans
        (div_le_div_of_nonneg_left (by norm_num) ha hae)
    · simp [ha.le]
  unfold zScore
  calc
    |gammaScore a e o + offsetG a e o.X| ≤
        |gammaScore a e o| + |offsetG a e o.X| := abs_add_le _ _
    _ ≤ 1 / a + 1 := by rw [abs_of_nonneg hg.1]; exact add_le_add hgamma hg.2

private lemma zScore_supported_integrable (P : RowLaw) (a : ℝ)
    (hP : WellFormed P) (ha : 0 < a) :
    Integrable (fun o : {o : Observation //
      o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} =>
      zScore a P.logger o.1)
      (Measure.comap (Subtype.val : {o : Observation //
        o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} → Observation)
        P.obsLaw) := by
  letI : IsProbabilityMeasure P.full := hP.1
  letI : IsFiniteMeasure P.obsLaw := ⟨by
    rw [RowLaw.obsLaw, Measure.map_apply score_observation_map_measurable MeasurableSet.univ]
    simp⟩
  let B : Set Observation := {o | o.X ∈ Set.Icc (0 : ℝ) 1 ∧
    o.Y ∈ Set.Icc (-1 : ℝ) 1}
  have hcoords : Measurable (fun o : Observation => (o.X, o.A, o.Y)) :=
    comap_measurable _
  have hB : MeasurableSet B :=
    (hcoords.fst measurableSet_Icc).inter (hcoords.snd.snd measurableSet_Icc)
  have hs : ∀ᵐ o ∂P.obsLaw, o ∈ B := by
    apply (ae_map_iff score_observation_map_measurable.aemeasurable hB).2
    exact (ae_iff.mpr hP.2.1).and (ae_iff.mpr hP.2.2.1)
  have hXlog : ∀ᵐ o ∂P.obsLaw, P.logger o.X ∈ Set.Icc (0 : ℝ) 1 := by
    have hh : ∀ᵐ x ∂(P.obsLaw.map Observation.X),
        P.logger x ∈ Set.Icc (0 : ℝ) 1 := by
      rw [score_observation_X_map]
      exact logger_ae_mem_Icc P hP
    exact ae_of_ae_map score_observation_X_measurable.aemeasurable hh
  have hi : IntegrableOn (fun o => zScore a P.logger o) B P.obsLaw := by
    apply Integrable.mono' (integrable_const (1 / a + 1))
      (score_z_aemeasurable P hP a).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_of_ae hXlog, self_mem_ae_restrict hB] with o hoX hoB
    simpa only [Real.norm_eq_abs] using
      zScore_abs_le_of_logger_mem_Icc a P.logger o ha hoX hoB.2
  exact (integrableOn_iff_comap_subtypeVal hB).1 hi

private lemma zScore_integrable (P : RowLaw) (a : ℝ)
    (hP : WellFormed P) (ha : 0 < a) :
    Integrable (fun o => zScore a P.logger o) P.obsLaw := by
  let B : Set Observation := {o | o.X ∈ Set.Icc (0 : ℝ) 1 ∧
    o.Y ∈ Set.Icc (-1 : ℝ) 1}
  have hcoords : Measurable (fun o : Observation => (o.X, o.A, o.Y)) :=
    comap_measurable _
  have hB : MeasurableSet B :=
    (hcoords.fst measurableSet_Icc).inter (hcoords.snd.snd measurableSet_Icc)
  have hs : ∀ᵐ o ∂P.obsLaw, o ∈ B := by
    apply (ae_map_iff score_observation_map_measurable.aemeasurable hB).2
    exact (ae_iff.mpr hP.2.1).and (ae_iff.mpr hP.2.2.1)
  have hi : IntegrableOn (fun o => zScore a P.logger o) B P.obsLaw :=
    (integrableOn_iff_comap_subtypeVal hB).2
      (zScore_supported_integrable P a hP ha)
  change Integrable (fun o => zScore a P.logger o) (P.obsLaw.restrict B) at hi
  rwa [Measure.restrict_eq_self_of_ae_mem hs] at hi

private lemma regularizedLoss_congr_on_support (P : RowLaw) (a : ℝ)
    (hP : WellFormed P) {π ψ : ℝ → Bool}
    (hπψ : Set.EqOn π ψ (Set.Icc (0 : ℝ) 1)) :
    regularizedLoss P a π = regularizedLoss P a ψ := by
  have hs : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0 : ℝ) 1 :=
    (ae_map_iff fullRow_X_measurable.aemeasurable measurableSet_Icc).2
      (ae_iff.mpr hP.2.1)
  have heq : π =ᵐ[P.PX] ψ := hs.mono fun x hx => hπψ hx
  have hw : rawWelfare P π = rawWelfare P ψ := by
    unfold rawWelfare
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  have hd : offsetDisagreement P a π = offsetDisagreement P a ψ := by
    unfold offsetDisagreement
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  unfold regularizedLoss rawRegret
  rw [hw, hd]

private lemma comparisonIntegrand_congr_on_support (P : RowLaw) (a : ℝ)
    {π ψ : ℝ → Bool} (hπψ : Set.EqOn π ψ (Set.Icc (0 : ℝ) 1))
    (o : Observation) (ho : o.X ∈ Set.Icc (0 : ℝ) 1) :
    comparisonIntegrand P a π o = comparisonIntegrand P a ψ o := by
  unfold comparisonIntegrand
  rw [hπψ ho]

private lemma centeredComparison_congr_on_support {n : ℕ} (P : RowLaw) (a : ℝ)
    (hP : WellFormed P) {π ψ : ℝ → Bool}
    (hπψ : Set.EqOn π ψ (Set.Icc (0 : ℝ) 1))
    (d : Fin n → {o : Observation //
      o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1}) :
    |empiricalAverage (comparisonIntegrand P a π) (fun i => (d i).1) -
        ∫ o, comparisonIntegrand P a π o ∂P.obsLaw| =
      |empiricalAverage (comparisonIntegrand P a ψ) (fun i => (d i).1) -
        ∫ o, comparisonIntegrand P a ψ o ∂P.obsLaw| := by
  have hs : ∀ᵐ o ∂P.obsLaw, o.X ∈ Set.Icc (0 : ℝ) 1 := by
    refine ae_of_ae_map score_observation_X_measurable.aemeasurable ?_
    rw [score_observation_X_map]
    exact (ae_map_iff fullRow_X_measurable.aemeasurable measurableSet_Icc).2
      (ae_iff.mpr hP.2.1)
  have hint : (∫ o, comparisonIntegrand P a π o ∂P.obsLaw) =
      ∫ o, comparisonIntegrand P a ψ o ∂P.obsLaw := by
    apply integral_congr_ae
    filter_upwards [hs] with o ho
    exact comparisonIntegrand_congr_on_support P a hπψ o ho
  have hemp : empiricalAverage (comparisonIntegrand P a π) (fun i => (d i).1) =
      empiricalAverage (comparisonIntegrand P a ψ) (fun i => (d i).1) := by
    unfold empiricalAverage
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact comparisonIntegrand_congr_on_support P a hπψ (d i).1 (d i).2.1
  rw [hemp, hint]

/-- The localized threshold supremum is measurable even with score atoms. -/
lemma localizedProcess_measurable {n : ℕ} (P : RowLaw) (a z : ℝ)
    (hP : WellFormed P) (ha : 0 < a) (hz : 0 < z) :
    Measurable (fun d : Fin n → {o : Observation //
        o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} =>
      localizedProcess (n := n) P a z (fun i => (d i).1)) := by
  classical
  let B : Set Observation := {o | o.X ∈ Set.Icc (0 : ℝ) 1 ∧
    o.Y ∈ Set.Icc (-1 : ℝ) 1}
  let Ω := B
  let μ : Measure Ω := Measure.comap Subtype.val P.obsLaw
  let score : Ω → ℝ := fun o => o.1.X
  let offset : Ω → ℝ := fun o =>
    (if canonicalPolicy P o.1.X then (1 : ℝ) else 0) * zScore a P.logger o.1
  let mark : Ω → ℝ := fun o => -zScore a P.logger o.1
  let leftLoss : ℝ → ℝ := fun t => regularizedLoss P a (leftThr t)
  let rightLoss : ℝ → ℝ := fun t => regularizedLoss P a (rightThr t)
  let leftProc : (Fin n → Ω) → ℝ :=
    Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup μ true
      score offset mark (Set.Icc 0 1) leftLoss z
  let rightProc : (Fin n → Ω) → ℝ :=
    Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup μ false
      score offset mark (Set.Icc 0 1) rightLoss z
  let falseProc : (Fin n → Ω) → ℝ := fun d =>
    if regularizedLoss P a (fun _ => false) ≤ z then
      |empiricalAverage (comparisonIntegrand P a (fun _ => false))
          (fun i => (d i).1) -
        ∫ o, comparisonIntegrand P a (fun _ => false) o ∂P.obsLaw|
    else 0
  have hscore : Measurable score := by
    exact score_observation_X_measurable.comp measurable_subtype_coe
  have hmark : Measurable mark := by
    exact (zScore_supported_measurable P a hP).neg
  have hoffset : Measurable offset := by
    exact (Measurable.ite
      (((canonicalPolicy_supported_measurable P hP).comp
        (hscore.subtype_mk (h := fun o : Ω => o.2.1)))
        (measurableSet_singleton true))
        measurable_const measurable_const).mul
      (zScore_supported_measurable P a hP)
  have hmarkInt : Integrable mark μ :=
    (zScore_supported_integrable P a hP ha).neg
  have hoffsetInt : Integrable offset μ := by
    apply Integrable.mono' (zScore_supported_integrable P a hP ha).abs
      hoffset.aestronglyMeasurable
    filter_upwards with o
    dsimp only [offset]
    cases canonicalPolicy P o.1.X <;> simp only [Bool.false_eq_true,
      ↓reduceIte, zero_mul, one_mul, Real.norm_eq_abs, abs_zero, le_refl,
      abs_nonneg]
  have hleft : Measurable leftProc := by
    exact Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup_measurable_of_integrable
      μ true score offset mark hscore hoffset hmark hoffsetInt hmarkInt
      (Set.Icc 0 1) leftLoss z n
  have hright : Measurable rightProc := by
    exact Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup_measurable_of_integrable
      μ false score offset mark hscore hoffset hmark hoffsetInt hmarkInt
      (Set.Icc 0 1) rightLoss z n
  have hfalse : Measurable falseProc := by
    dsimp only [falseProc]
    split_ifs
    · exact centeredComparison_supported_measurable P a hP (fun _ => false)
        (by simp [binaryPolicyClass])
    · exact measurable_const
  have hrepLeft (t : ℝ) (o : Ω) :
      Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction true
        score offset mark t o = comparisonIntegrand P a (leftThr t) o.1 := by
    simp only [Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction,
      score, offset, mark, ↓reduceIte, leftThr, comparisonIntegrand]
    by_cases ht : o.1.X ≤ t <;>
      by_cases hc : canonicalPolicy P o.1.X <;> simp [ht, hc]
  have hrepRight (t : ℝ) (o : Ω) :
      Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction false
        score offset mark t o = comparisonIntegrand P a (rightThr t) o.1 := by
    simp only [Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction,
      score, offset, mark, Bool.false_eq_true, ↓reduceIte, rightThr, comparisonIntegrand]
    by_cases ht : t ≤ o.1.X <;>
      by_cases hc : canonicalPolicy P o.1.X <;> simp [ht, hc]
  have hcoords : Measurable (fun o : Observation => (o.X, o.A, o.Y)) :=
    comap_measurable _
  have hB : MeasurableSet B :=
    (hcoords.fst measurableSet_Icc).inter (hcoords.snd.snd measurableSet_Icc)
  have hs : ∀ᵐ o ∂P.obsLaw, o ∈ B := by
    apply (ae_map_iff score_observation_map_measurable.aemeasurable hB).2
    exact (ae_iff.mpr hP.2.1).and (ae_iff.mpr hP.2.2.1)
  have hintLeft (t : ℝ) :
      (∫ o : Ω, Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
          true score offset mark t o ∂μ) =
        ∫ o, comparisonIntegrand P a (leftThr t) o ∂P.obsLaw := by
    rw [integral_congr_ae (ae_of_all _ (hrepLeft t))]
    have he : (∫ o, comparisonIntegrand P a (leftThr t) o ∂P.obsLaw) =
        ∫ o : Ω, comparisonIntegrand P a (leftThr t) o.1 ∂μ := by
      dsimp only [μ, Ω, B]
      rw [integral_subtype_comap (μ := P.obsLaw)
        (s := {o : Observation | o.X ∈ Set.Icc (0 : ℝ) 1 ∧
          o.Y ∈ Set.Icc (-1 : ℝ) 1}) hB,
        Measure.restrict_eq_self_of_ae_mem hs]
    exact he.symm
  have hintRight (t : ℝ) :
      (∫ o : Ω, Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
          false score offset mark t o ∂μ) =
        ∫ o, comparisonIntegrand P a (rightThr t) o ∂P.obsLaw := by
    rw [integral_congr_ae (ae_of_all _ (hrepRight t))]
    have he : (∫ o, comparisonIntegrand P a (rightThr t) o ∂P.obsLaw) =
        ∫ o : Ω, comparisonIntegrand P a (rightThr t) o.1 ∂μ := by
      dsimp only [μ, Ω, B]
      rw [integral_subtype_comap (μ := P.obsLaw)
        (s := {o : Observation | o.X ∈ Set.Icc (0 : ℝ) 1 ∧
          o.Y ∈ Set.Icc (-1 : ℝ) 1}) hB,
        Measure.restrict_eq_self_of_ae_mem hs]
    exact he.symm
  have hcenterLeft (t : ℝ) (d : Fin n → Ω) :
      |Causalean.Stat.Concentration.centeredEmpiricalAverage μ d
          (Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
            true score offset mark t)| =
      |empiricalAverage (comparisonIntegrand P a (leftThr t))
          (fun i => (d i).1) -
        ∫ o, comparisonIntegrand P a (leftThr t) o ∂P.obsLaw| := by
    unfold Causalean.Stat.Concentration.centeredEmpiricalAverage empiricalAverage
    rw [hintLeft t]
    congr 2
    apply congrArg
    apply Finset.sum_congr rfl
    intro i _
    exact hrepLeft t (d i)
  have hcenterRight (t : ℝ) (d : Fin n → Ω) :
      |Causalean.Stat.Concentration.centeredEmpiricalAverage μ d
          (Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
            false score offset mark t)| =
      |empiricalAverage (comparisonIntegrand P a (rightThr t))
          (fun i => (d i).1) -
        ∫ o, comparisonIntegrand P a (rightThr t) o ∂P.obsLaw| := by
    unfold Causalean.Stat.Concentration.centeredEmpiricalAverage empiricalAverage
    rw [hintRight t]
    congr 2
    apply congrArg
    apply Finset.sum_congr rfl
    intro i _
    exact hrepRight t (d i)
  have heq : (fun d : Fin n → Ω =>
      localizedProcess (n := n) P a z (fun i => (d i).1)) =
      fun d => max (falseProc d) (max (leftProc d) (rightProc d)) := by
    funext d
    let value : (ℝ → Bool) → ℝ := fun π =>
      |empiricalAverage (comparisonIntegrand P a π) (fun i => (d i).1) -
        ∫ o, comparisonIntegrand P a π o ∂P.obsLaw|
    let K : ℝ := |(n : ℝ)⁻¹| * ∑ i, |zScore a P.logger (d i).1| +
      ∫ o, |zScore a P.logger o| ∂P.obsLaw
    have hcomp (π : ℝ → Bool) (o : Observation) :
        |comparisonIntegrand P a π o| ≤ |zScore a P.logger o| := by
      unfold comparisonIntegrand
      cases π o.X <;> cases canonicalPolicy P o.X <;> simp
    have hvalue (π : ℝ → Bool) : value π ≤ K := by
      have hi : |∫ o, comparisonIntegrand P a π o ∂P.obsLaw| ≤
          ∫ o, |zScore a P.logger o| ∂P.obsLaw := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_of_norm_le
            (f := comparisonIntegrand P a π) (zScore_integrable P a hP ha).abs
            (ae_of_all _ (fun o => by
              simpa only [Real.norm_eq_abs] using hcomp π o))
      have hemp : |empiricalAverage (comparisonIntegrand P a π)
          (fun i => (d i).1)| ≤
          |(n : ℝ)⁻¹| * ∑ i, |zScore a P.logger (d i).1| := by
        unfold empiricalAverage
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => hcomp π (d i).1)) (abs_nonneg _)
      exact (abs_sub _ _).trans (by dsimp only [K]; linarith)
    have hbddAll : BddAbove (Set.range (fun π : {π : ℝ → Bool //
        π ∈ thresholdClass ∧ regularizedLoss P a π ≤ z} => value π.1)) :=
      ⟨K, by rintro _ ⟨π, rfl⟩; exact hvalue π.1⟩
    have hbddLeft : BddAbove (Set.range (fun t : {t : ℝ //
        t ∈ Set.Icc (0 : ℝ) 1 ∧ leftLoss t ≤ z} => value (leftThr t.1))) :=
      ⟨K, by rintro _ ⟨t, rfl⟩; exact hvalue (leftThr t.1)⟩
    have hbddRight : BddAbove (Set.range (fun t : {t : ℝ //
        t ∈ Set.Icc (0 : ℝ) 1 ∧ rightLoss t ≤ z} => value (rightThr t.1))) :=
      ⟨K, by rintro _ ⟨t, rfl⟩; exact hvalue (rightThr t.1)⟩
    have hbddLeftCentered : BddAbove (Set.range (fun t : {t : ℝ //
        t ∈ Set.Icc (0 : ℝ) 1 ∧ leftLoss t ≤ z} =>
        |Causalean.Stat.Concentration.centeredEmpiricalAverage μ d
          (Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
            true score offset mark t.1)|)) := by
      refine ⟨K, ?_⟩
      rintro _ ⟨t, rfl⟩
      change |Causalean.Stat.Concentration.centeredEmpiricalAverage μ d
        (Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
          true score offset mark t.1)| ≤ K
      rw [hcenterLeft t.1 d]
      exact hvalue (leftThr t.1)
    have hbddRightCentered : BddAbove (Set.range (fun t : {t : ℝ //
        t ∈ Set.Icc (0 : ℝ) 1 ∧ rightLoss t ≤ z} =>
        |Causalean.Stat.Concentration.centeredEmpiricalAverage μ d
          (Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
            false score offset mark t.1)|)) := by
      refine ⟨K, ?_⟩
      rintro _ ⟨t, rfl⟩
      change |Causalean.Stat.Concentration.centeredEmpiricalAverage μ d
        (Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
          false score offset mark t.1)| ≤ K
      rw [hcenterRight t.1 d]
      exact hvalue (rightThr t.1)
    change (⨆ π : {π : ℝ → Bool // π ∈ thresholdClass ∧
        regularizedLoss P a π ≤ z}, value π.1) = _
    rcases isEmpty_or_nonempty {π : ℝ → Bool // π ∈ thresholdClass ∧
      regularizedLoss P a π ≤ z} with hEmpty | hNonempty
    · have hfalseIneligible : ¬ regularizedLoss P a (fun _ => false) ≤ z := by
        intro hf
        exact isEmptyElim (⟨fun _ => false, Or.inl (fun _ _ => rfl), hf⟩ :
          {π : ℝ → Bool // π ∈ thresholdClass ∧ regularizedLoss P a π ≤ z})
      have hleftEmpty : IsEmpty {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1 ∧ leftLoss t ≤ z} :=
        ⟨fun t => isEmptyElim (⟨leftThr t.1,
          Or.inr (Or.inr (Or.inl ⟨t.1, t.2.1, fun _ _ => rfl⟩)), t.2.2⟩ :
          {π : ℝ → Bool // π ∈ thresholdClass ∧ regularizedLoss P a π ≤ z})⟩
      have hrightEmpty : IsEmpty {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1 ∧ rightLoss t ≤ z} :=
        ⟨fun t => isEmptyElim (⟨rightThr t.1,
          Or.inr (Or.inr (Or.inr ⟨t.1, t.2.1, fun _ _ => rfl⟩)), t.2.2⟩ :
          {π : ℝ → Bool // π ∈ thresholdClass ∧ regularizedLoss P a π ≤ z})⟩
      letI := hleftEmpty
      letI := hrightEmpty
      simp only [iSup_of_empty', leftProc, rightProc,
        Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup,
        Causalean.Stat.EmpiricalProcess.Countable.centeredSup, falseProc,
        if_neg hfalseIneligible, Real.sSup_empty]
      norm_num
    letI := hNonempty
    apply le_antisymm
    · apply ciSup_le
      intro π
      rcases π.2.1 with hfalseπ | hrest
      · have hv := centeredComparison_congr_on_support P a hP hfalseπ d
        dsimp only [falseProc]
        rw [if_pos ((regularizedLoss_congr_on_support P a hP hfalseπ).symm ▸ π.2.2)]
        dsimp only [value]
        rw [hv]
        exact le_max_left _ _
      · rcases hrest with htrueπ | hrest
        · have hright0 : Set.EqOn π.1 (rightThr 0) (Set.Icc (0 : ℝ) 1) := by
            intro x hx
            rw [htrueπ x hx]
            simp [rightThr, hx.1]
          have hloss : rightLoss 0 ≤ z := by
            dsimp only [rightLoss]
            rw [← regularizedLoss_congr_on_support P a hP hright0]
            exact π.2.2
          let hmem : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1 ∧ rightLoss t ≤ z} :=
            ⟨0, by exact ⟨by norm_num, hloss⟩⟩
          have hle : value (rightThr 0) ≤ rightProc d := by
            letI : Nonempty {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1 ∧ rightLoss t ≤ z} :=
              ⟨hmem⟩
            dsimp only [rightProc]
            unfold Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
              Causalean.Stat.EmpiricalProcess.Countable.centeredSup
            dsimp only [value]
            rw [← hcenterRight 0 d]
            exact le_ciSup hbddRightCentered hmem
          dsimp only [value]
          rw [centeredComparison_congr_on_support P a hP hright0 d]
          exact hle.trans (le_max_of_le_right (le_max_right _ _))
        · rcases hrest with hleftπ | hrightπ
          · obtain ⟨t, ht, heqπ⟩ := hleftπ
            have hloss : leftLoss t ≤ z := by
              dsimp only [leftLoss]
              rw [← regularizedLoss_congr_on_support P a hP heqπ]
              exact π.2.2
            let hmem : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1 ∧ leftLoss t ≤ z} :=
              ⟨t, ht, hloss⟩
            have hle : value (leftThr t) ≤ leftProc d := by
              letI : Nonempty {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1 ∧ leftLoss t ≤ z} :=
                ⟨hmem⟩
              dsimp only [leftProc]
              unfold Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
                Causalean.Stat.EmpiricalProcess.Countable.centeredSup
              dsimp only [value]
              rw [← hcenterLeft t d]
              exact le_ciSup hbddLeftCentered hmem
            dsimp only [value]
            rw [centeredComparison_congr_on_support P a hP heqπ d]
            exact hle.trans (le_max_of_le_right (le_max_left _ _))
          · obtain ⟨t, ht, heqπ⟩ := hrightπ
            have hloss : rightLoss t ≤ z := by
              dsimp only [rightLoss]
              rw [← regularizedLoss_congr_on_support P a hP heqπ]
              exact π.2.2
            let hmem : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1 ∧ rightLoss t ≤ z} :=
              ⟨t, ht, hloss⟩
            have hle : value (rightThr t) ≤ rightProc d := by
              letI : Nonempty {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1 ∧ rightLoss t ≤ z} :=
                ⟨hmem⟩
              dsimp only [rightProc]
              unfold Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
                Causalean.Stat.EmpiricalProcess.Countable.centeredSup
              dsimp only [value]
              rw [← hcenterRight t d]
              exact le_ciSup hbddRightCentered hmem
            dsimp only [value]
            rw [centeredComparison_congr_on_support P a hP heqπ d]
            exact hle.trans (le_max_of_le_right (le_max_right _ _))
    · apply max_le
      · dsimp only [falseProc]
        split_ifs with hf
        · exact le_ciSup hbddAll ⟨fun _ => false, by
            exact ⟨Or.inl (fun _ _ => rfl), hf⟩⟩
        · exact Real.iSup_nonneg (fun i => by
            dsimp only [value]
            exact abs_nonneg _)
      · apply max_le
        · dsimp only [leftProc]
          unfold Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
            Causalean.Stat.EmpiricalProcess.Countable.centeredSup
          rcases isEmpty_or_nonempty {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1 ∧
            leftLoss t ≤ z} with he | hn
          · letI := he
            simp only [iSup_of_empty']
            rw [Real.sSup_empty]
            exact Real.iSup_nonneg (fun i => by
              dsimp only [value]
              exact abs_nonneg _)
          · letI := hn
            apply ciSup_le
            intro t
            rw [hcenterLeft t.1 d]
            exact le_ciSup hbddAll ⟨leftThr t.1, by
              exact ⟨Or.inr (Or.inr (Or.inl ⟨t.1, t.2.1, fun _ _ => rfl⟩)), t.2.2⟩⟩
        · dsimp only [rightProc]
          unfold Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
            Causalean.Stat.EmpiricalProcess.Countable.centeredSup
          rcases isEmpty_or_nonempty {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1 ∧
            rightLoss t ≤ z} with he | hn
          · letI := he
            simp only [iSup_of_empty']
            rw [Real.sSup_empty]
            exact Real.iSup_nonneg (fun i => by
              dsimp only [value]
              exact abs_nonneg _)
          · letI := hn
            apply ciSup_le
            intro t
            rw [hcenterRight t.1 d]
            exact le_ciSup hbddAll ⟨rightThr t.1, by
              exact ⟨Or.inr (Or.inr (Or.inr ⟨t.1, t.2.1, fun _ _ => rfl⟩)), t.2.2⟩⟩
  change Measurable (fun d : Fin n → Ω =>
    localizedProcess (n := n) P a z (fun i => (d i).1))
  rw [heq]
  exact hfalse.max (hleft.max hright)

end CausalSmith.Stat.ScorethresholdOverlapRegret
