module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.SelectorMeasurability
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.UpperPeeling

/-! # Integrability bridges for the upper-bound assembly

Supported data and jointly Borel policy evaluation give integrable selector
losses. A deterministic deleted-score envelope makes every measurable
localized fourth power integrable, independently of its moment estimate.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators

/-- The valid observed-data subset is Borel. -/
-- @node: upperIntegrability_data_measurableSet
lemma upperIntegrability_data_measurableSet (n : ℕ) :
    MeasurableSet {d : Fin n → Observation | ∀ i,
      (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1} := by
  have hX : Measurable (fun o : Observation => o.X) := (comap_measurable _).fst
  have hY : Measurable (fun o : Observation => o.Y) := (comap_measurable _).snd.snd
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact ((hX.comp (measurable_pi_apply i)) measurableSet_Icc).inter
    ((hY.comp (measurable_pi_apply i)) measurableSet_Icc)

/-- Every sample from a legal law lies in the valid observed-data subset. -/
-- @node: upperIntegrability_data_support
lemma upperIntegrability_data_support (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e) :
    ∀ᵐ d ∂sampleLaw P n, ∀ i,
      (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1 := by
  have hX : Measurable (fun o : Observation => o.X) := (comap_measurable _).fst
  have hY : Measurable (fun o : Observation => o.Y) := (comap_measurable _).snd.snd
  have hrow : ∀ᵐ o ∂P.obsLaw,
      o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1 := by
    apply (ae_map_iff score_observation_map_measurable.aemeasurable
      ((hX measurableSet_Icc).inter (hY measurableSet_Icc))).2
    exact (ae_iff.mpr hP.wf.2.1).and (ae_iff.mpr hP.wf.2.2.1)
  haveI : IsProbabilityMeasure P.full := hP.wf.1
  haveI : IsProbabilityMeasure P.obsLaw :=
    Measure.isProbabilityMeasure_map score_observation_map_measurable.aemeasurable
  rw [ae_all_iff]
  intro i
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => P.obsLaw) (i := i)) hrow

/-- Offset disagreement is measurable for a jointly Borel policy family. -/
-- @node: upperIntegrability_offset_family_measurable
@[fun_prop] lemma upperIntegrability_offset_family_measurable
    {Ω : Type*} [MeasurableSpace Ω] (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a : ℝ) (ψ : Ω → ℝ → Bool)
    (hψ : Measurable (fun z : Ω × Set.Icc (0:ℝ) 1 => ψ z.1 z.2)) :
    Measurable (fun w => offsetDisagreement P a (ψ w)) := by
  haveI : IsProbabilityMeasure P.PX := scoreLaw_isProbability P hP.wf
  have hs : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0:ℝ) 1 := ae_iff.mpr hP.score.2
  have ht : Measurable (fun x : Set.Icc (0:ℝ) 1 => P.tau x) := hP.wf.2.2.2.2.1
  have he : Measurable (fun x : Set.Icc (0:ℝ) 1 => P.logger x) := hP.wf.2.2.2.1
  have hc : Measurable (fun x : Set.Icc (0:ℝ) 1 => canonicalPolicy P x) := by
    unfold canonicalPolicy
    apply measurable_to_bool
    simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
      (measurableSet_le measurable_const ht :
        MeasurableSet {x : Set.Icc (0:ℝ) 1 | 0 ≤ P.tau x})
  have hg : Measurable (fun x : Set.Icc (0:ℝ) 1 => offsetG a P.logger x) := by
    unfold offsetG
    fun_prop
  have hm : Measurable (fun z : Ω × Set.Icc (0:ℝ) 1 =>
      offsetG a P.logger z.2 * (if ψ z.1 z.2 = canonicalPolicy P z.2 then (0:ℝ) else 1)) := by
    exact (hg.comp measurable_snd).mul
      (Measurable.ite (measurableSet_eq_fun hψ (hc.comp measurable_snd))
        measurable_const measurable_const)
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν := Measure.comap Subtype.val P.PX)
  have heq (w : Ω) : offsetDisagreement P a (ψ w) =
      ∫ x : Set.Icc (0:ℝ) 1, offsetG a P.logger x *
        (if ψ w x = canonicalPolicy P x then (0:ℝ) else 1)
        ∂Measure.comap Subtype.val P.PX := by
    rw [integral_subtype_comap (μ := P.PX) measurableSet_Icc
      (fun x => offsetG a P.logger x * (if ψ w x = canonicalPolicy P x then (0:ℝ) else 1)),
      Measure.restrict_eq_self_of_ae_mem hs]
    rfl
  simp_rw [heq]
  exact hi.measurable

/-- The implemented selector's bounded regularized loss is integrable. -/
-- @node: upperIntegrability_selector_loss
@[fun_prop] lemma upperIntegrability_selector_loss (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a : ℝ) (ha : 0 < a) :
    Integrable (fun d => regularizedLoss P a (sortedSelector a e d)) (sampleLaw P n) := by
  haveI := sampleLaw_isProbability P n hP.wf
  have he : Measurable (fun x : Set.Icc (0:ℝ) 1 => e x) := by
    have heq : (fun x : Set.Icc (0:ℝ) 1 => e x) = fun x : Set.Icc (0:ℝ) 1 => P.logger x :=
      funext (fun x => hP.known x.2)
    rw [heq]
    exact hP.wf.2.2.2.1
  have hm : Measurable (fun d : {d : Fin n → Observation // ∀ i,
      (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1} =>
      regularizedLoss P a (sortedSelector a e d.1)) := by
    unfold regularizedLoss
    apply Measurable.add
    · exact rawRegret_family_measurable α γ θ n P e hP _ (sortedSelector_measurable a e he)
    · exact upperIntegrability_offset_family_measurable α γ θ n P e hP a _
        (sortedSelector_measurable a e he)
  have ham := aemeasurable_restrict_of_measurable_subtype (μ := sampleLaw P n)
    (f := fun d => regularizedLoss P a (sortedSelector a e d))
    (upperIntegrability_data_measurableSet n) hm
  rw [Measure.restrict_eq_self_of_ae_mem
    (s := {d : Fin n → Observation | ∀ i,
      (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1})
    (upperIntegrability_data_support α γ θ n P e hP)] at ham
  apply Integrable.of_bound ham.aestronglyMeasurable 3
  filter_upwards with d
  have hb := upperPeeling_regularizedLoss_bounds α γ θ n P e hP a ha _
    (firstScannedMinimizer_mem_thresholdClass a e d)
  change 0 ≤ regularizedLoss P a (sortedSelector a e d) ∧
    regularizedLoss P a (sortedSelector a e d) ≤ 3 at hb
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

/-- The localized process has a deterministic deleted-score envelope on valid data. -/
-- @node: upperIntegrability_process_bound
lemma upperIntegrability_process_bound (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a z : ℝ) (ha : 0 < a ∧ a ≤ 1/4) (hn : 0 < n)
    (d : Fin n → Observation) (hd : ∀ i,
      (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1) :
    0 ≤ localizedProcess P a z d ∧ localizedProcess P a z d ≤ 4/a := by
  have he : ∀ x ∈ Set.Icc (0:ℝ) 1, P.logger x ∈ Set.Ioo (0:ℝ) 1 := by
    intro x hx
    simpa only [hP.known hx] using hP.loggerSpace x hx
  haveI : IsProbabilityMeasure P.full := hP.wf.1
  haveI : IsProbabilityMeasure P.obsLaw :=
    Measure.isProbabilityMeasure_map score_observation_map_measurable.aemeasurable
  constructor
  · exact Real.iSup_nonneg (fun _ => abs_nonneg _)
  · unfold localizedProcess
    classical
    by_cases hne : Nonempty {π : ℝ → Bool // π ∈ thresholdClass ∧ regularizedLoss P a π ≤ z}
    · letI := hne
      apply ciSup_le
      intro π
      have hi : |∫ o, comparisonIntegrand P a π.1 o ∂P.obsLaw| ≤ 2/a := by
        have hb := norm_integral_le_of_norm_le_const (μ := P.obsLaw) (C := 2/a)
          (f := comparisonIntegrand P a π.1) (by
            filter_upwards [zScore_abs_ae P a ha hP.wf he] with o ho
            exact (upperComparison_abs_le_score P a π.1 o).trans ho)
        simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb
      have hemp : |empiricalAverage (comparisonIntegrand P a π.1) d| ≤ 2/a := by
        unfold empiricalAverage
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)⁻¹)]
        calc
          _ ≤ (n:ℝ)⁻¹ * ∑ i : Fin n, (2/a) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
              (upperComparison_abs_le_score P a π.1 (d i)).trans
                (zScore_abs_le a P.logger (d i) ha (he _ (hd i).1) (hd i).2))
          _ = 2/a := by simp [ne_of_gt (Nat.cast_pos.mpr hn)]
      exact (abs_sub _ _).trans (by convert add_le_add hemp hi using 1 <;> ring)
    · haveI := not_nonempty_iff.mp hne
      rw [iSup_of_empty', Real.sSup_empty]
      exact div_nonneg (by norm_num) ha.1.le

/-- A supported measurable localized process has an integrable fourth power;
this uses a deterministic envelope rather than its claimed moment bound. -/
-- @node: upperIntegrability_process_fourth
@[fun_prop] lemma upperIntegrability_process_fourth (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a z : ℝ) (ha : 0 < a ∧ a ≤ 1/4) (hn : 0 < n)
    (hm : Measurable (fun d : Fin n → {o : Observation //
        o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1} =>
      localizedProcess P a z (fun i => (d i).1))) :
    Integrable (fun d : Fin n → Observation => (localizedProcess P a z d)^4) (sampleLaw P n) := by
  haveI := sampleLaw_isProbability P n hP.wf
  have hsub : Measurable (fun d : {d : Fin n → Observation // ∀ i,
      (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1} =>
      (localizedProcess P a z d.1)^4) := by
    have hl := hm.comp (show Measurable (fun d : {d : Fin n → Observation // ∀ i,
        (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1} =>
        fun i => (⟨d.1 i, d.2 i⟩ : {o : Observation //
          o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1})) by
          apply measurable_pi_iff.mpr
          intro i
          apply Measurable.subtype_mk
          exact (measurable_pi_apply i).comp measurable_subtype_coe)
    exact hl.pow_const 4
  have ham := aemeasurable_restrict_of_measurable_subtype (μ := sampleLaw P n)
    (f := fun d => (localizedProcess P a z d)^4)
    (upperIntegrability_data_measurableSet n) hsub
  rw [Measure.restrict_eq_self_of_ae_mem
    (s := {d : Fin n → Observation | ∀ i,
      (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1})
    (upperIntegrability_data_support α γ θ n P e hP)] at ham
  apply Integrable.of_bound ham.aestronglyMeasurable ((4/a)^4)
  filter_upwards [upperIntegrability_data_support α γ θ n P e hP] with d hd
  have hb := upperIntegrability_process_bound α γ θ n P e hP a z ha hn d hd
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hb.1 4)]
  exact pow_le_pow_left₀ hb.1 hb.2 4

/-- Nonnegative offset disagreement lets the integrated selector regret be
bounded by its integrable regularized loss. -/
-- @node: upperIntegrability_selector_regret_le_loss
lemma upperIntegrability_selector_regret_le_loss (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a : ℝ) (ha : 0 < a) :
    (∫ d, regret (P.toWellFormedLaw hP.wf hP.bounded)
      (measurablePolicy (sortedSelector a e d)) ∂sampleLaw P n) ≤
      ∫ d, regularizedLoss P a (sortedSelector a e d) ∂sampleLaw P n := by
  have heq (d : Fin n → Observation) :
      regret (P.toWellFormedLaw hP.wf hP.bounded)
        (measurablePolicy (sortedSelector a e d)) =
        rawRegret P (sortedSelector a e d) := by
    have hπ := thresholdClass_mem_binaryPolicyClass (sortedSelector a e d)
      (firstScannedMinimizer_mem_thresholdClass a e d)
    simp [regret, RowLaw.toWellFormedLaw, measurablePolicy, hπ]
  simp_rw [heq]
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun d => (rawRegret_bounds α γ θ n P e hP _).1)
    (upperIntegrability_selector_loss α γ θ n P e hP a ha)
  filter_upwards with d
  have hg : 0 ≤ offsetDisagreement P a (sortedSelector a e d) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_iff.mpr hP.score.2] with x hx
    have he := hP.loggerSpace x hx
    rw [hP.known hx] at he
    have hp : 0 < min (P.logger x) (1-P.logger x) := lt_min he.1 (by linarith [he.2])
    apply mul_nonneg
    · exact le_min zero_le_one (div_nonneg ha.le hp.le)
    · positivity
  unfold regularizedLoss
  linarith

end CausalSmith.Stat.ScorethresholdOverlapRegret
