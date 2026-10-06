module
public import Causalean.Stat.RecurrentEvent.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Hazard survival to death density

The finite-horizon survival equation determines the death-time density on
the open administrative horizon. This is a primitive-law lemma, independent
of observation and recurrence.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace Causalean.Stat.RecurrentEvent

variable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]

/-- [A nonnegative hazard](hyp:h), [a terminal horizon](hyp:H), and [two
ordered times](hyp:a,b,ha,hab,hb) with [an integrable hazard over the
horizon](hyp:hh) give [survival-weighted hazard mass equal to the loss of
survival over the interval](goal). -/
theorem hazardSurvival_interval_integral (h : ℝ → ℝ≥0) (H a b : ℝ)
    (hh : IntervalIntegrable (fun t : ℝ => (h t : ℝ)) volume 0 H)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ H) :
    (∫ t in a..b, hazardSurvival h t * (h t : ℝ)) =
      hazardSurvival h a - hazardSurvival h b := by
  let G : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, (h u : ℝ)
  have h0H : 0 ≤ H := by linarith
  have hG : AbsolutelyContinuousOnInterval G 0 H :=
    hh.absolutelyContinuousOnInterval_intervalIntegral (by simp [h0H])
  have hsub : uIcc a b ⊆ uIcc (0 : ℝ) H := by
    rw [uIcc_of_le hab, uIcc_of_le h0H]
    exact Icc_subset_Icc ha hb
  have hG' : AbsolutelyContinuousOnInterval (fun t => -G t) a b :=
    (hG.mono hsub).fun_neg
  obtain ⟨C, hC⟩ := hG'.exists_bound
  have hmap : Set.MapsTo (fun t => -G t) (uIcc a b) (Icc (-C) C) := by
    intro x hx
    have hx' := hC x hx
    exact mem_Icc.mpr (abs_le.mp (by simpa only [Real.norm_eq_abs] using hx'))
  obtain ⟨K, hK⟩ : ∃ K, LipschitzOnWith K Real.exp (Icc (-C) C) :=
    ((Real.contDiff_exp (n := 1)).contDiffOn).exists_lipschitzOnWith
      (by norm_num) (convex_Icc _ _) isCompact_Icc
  have hS : AbsolutelyContinuousOnInterval (hazardSurvival h) a b := by
    change AbsolutelyContinuousOnInterval (fun t => Real.exp (-G t)) a b
    have hbound := hG'.const_mul (K : ℝ)
    unfold AbsolutelyContinuousOnInterval at hbound ⊢
    apply squeeze_zero' ?_ ?_ (by simpa using hbound)
    · exact Filter.Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
    · rw [eventually_inf_principal]
      filter_upwards with E hE
      apply Finset.sum_le_sum
      intro i hi
      have hi₁ := hmap (hE.1 i hi).1
      have hi₂ := hmap (hE.1 i hi).2
      calc
        _ ≤ (K : ℝ) * dist (-G (E.2 i).1) (-G (E.2 i).2) :=
          hK.dist_le_mul _ hi₁ _ hi₂
        _ = _ := by simp [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg K.coe_nonneg]
  have hderiv : ∀ᵐ x ∂volume.restrict (uIoc a b),
      deriv (hazardSurvival h) x = -(hazardSurvival h x * (h x : ℝ)) := by
    filter_upwards [ae_restrict_of_ae hh.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_uIoc] with x hx hmem
    have hx0H : x ∈ uIcc (0 : ℝ) H := hsub (uIoc_subset_uIcc hmem)
    have hD : HasDerivAt G (h x : ℝ) x := by
      simpa only [G] using hx hx0H 0 (by simp [h0H])
    have hD' : HasDerivAt (hazardSurvival h)
        (-(hazardSurvival h x * (h x : ℝ))) x := by
      convert (Real.hasDerivAt_exp (-G x)).comp x hD.neg using 1 <;>
        first | rfl | simp [hazardSurvival, G]
    exact hD'.deriv
  calc
    (∫ t in a..b, hazardSurvival h t * (h t : ℝ)) =
        ∫ t in a..b, -(deriv (hazardSurvival h) t) := by
          apply intervalIntegral.integral_congr_ae_restrict
          filter_upwards [hderiv] with x hx
          rw [hx, neg_neg]
    _ = hazardSurvival h a - hazardSurvival h b := by
      rw [intervalIntegral.integral_neg, hS.integral_deriv_eq_sub]
      ring

/-- [A recurrent-event model](hyp:M) and [an ordered subinterval inside its
administrative horizon](hyp:a,b,ha,hab,hb) give [death-time mass equal to
the decrease in hazard-generated survival](goal). -/
theorem Model.death_law_Ico_eq_survival_sub (M : Model A X) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.horizon) :
    M.deathLaw (Ico a b) =
      ENNReal.ofReal (hazardSurvival M.hazard a - hazardSurvival M.hazard b) := by
  /- Use `Ico a b = Ici a \ Ici b`, probability finiteness, and the two
  instances of `death_survival`. Convert the finite ENNReal subtraction to
  `ofReal` of the real survival difference. The case `a = b` is empty. -/
  letI := M.deathProb
  have hsub : Ici b ⊆ Ici a := Ici_subset_Ici.mpr hab
  have hdiff : Ico a b = Ici a \ Ici b := by ext x; simp
  rw [hdiff, measure_sdiff hsub measurableSet_Ici.nullMeasurableSet
    (measure_ne_top M.deathLaw (Ici b))]
  rw [M.death_survival a ⟨ha, le_trans hab hb⟩,
    M.death_survival b ⟨le_trans ha hab, hb⟩]
  exact (ENNReal.ofReal_sub _ (le_of_lt (Real.exp_pos _))).symm

/-- [A recurrent-event model](hyp:M) and [an ordered subinterval inside its
administrative horizon](hyp:a,b,ha,hab,hb) give [survival-weighted hazard
mass equal to the survival decrease](goal), including empty and
horizon-endpoint intervals. -/
theorem Model.survival_hazard_density_Ico (M : Model A X) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.horizon) :
    ((volume.restrict (Ico 0 M.horizon)).withDensity
      (fun t => ENNReal.ofReal (hazardSurvival M.hazard t) *
        (M.hazard t : ℝ≥0∞))) (Ico a b) =
      ENNReal.ofReal (hazardSurvival M.hazard a - hazardSurvival M.hazard b) := by
  /- Intersect nested `Ico` sets, use `withDensity_apply` and
  `ofReal_integral_eq_lintegral_ofReal`, and close the real integral with
  `hazardSurvival_interval_integral`. Establish integrability from
  `hazard_integrable` and bounded survival on `[0, horizon]`. -/
  let f : ℝ → ℝ := fun t => hazardSurvival M.hazard t * (M.hazard t : ℝ)
  have hsub : Icc a b ⊆ Icc (0 : ℝ) M.horizon := Icc_subset_Icc ha hb
  have hG := M.hazard_integrable.absolutelyContinuousOnInterval_intervalIntegral (c := 0)
    (by simp [M.horizon_nonneg])
  have hcont : ContinuousOn (hazardSurvival M.hazard) (Icc 0 M.horizon) := by
    change ContinuousOn (fun t => Real.exp (-(∫ u in (0 : ℝ)..t, (M.hazard u : ℝ)))) _
    have hc : ContinuousOn (fun t => -(∫ u in (0 : ℝ)..t, (M.hazard u : ℝ)))
        (Icc 0 M.horizon) := by
      simpa [uIcc_of_le M.horizon_nonneg] using hG.fun_neg.continuousOn
    simpa only [Function.comp_def] using Real.continuous_exp.continuousOn.comp hc
      (fun _ _ => Set.mem_univ _)
  have hbounds : ∀ t ∈ Icc a b, 0 ≤ hazardSurvival M.hazard t ∧
      hazardSurvival M.hazard t ≤ 1 := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans ha ht.1
    have hnonneg : 0 ≤ ∫ u in (0 : ℝ)..t, (M.hazard u : ℝ) :=
      intervalIntegral.integral_nonneg_of_forall ht0 (fun u => NNReal.coe_nonneg _)
    constructor
    · exact le_of_lt (Real.exp_pos _)
    · simpa [hazardSurvival] using Real.exp_le_one_iff.mpr (neg_nonpos.mpr hnonneg)
  have hh : IntervalIntegrable (fun t : ℝ => (M.hazard t : ℝ)) volume a b :=
    M.hazard_integrable.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le M.horizon_nonneg]
      exact hsub)
  have hf : IntegrableOn f (Ico a b) volume := by
    have hfm : AEStronglyMeasurable f (volume.restrict (Ico a b)) := by
      apply AEStronglyMeasurable.mul
      · exact (hcont.mono (fun x hx => hsub ⟨hx.1, hx.2.le⟩)).aestronglyMeasurable
          measurableSet_Ico
      · exact M.measurable_hazard.coe_nnreal_real.aestronglyMeasurable
    have hbound : (fun t => ‖f t‖) ≤ᵐ[volume.restrict (Ico a b)]
        (fun t => ‖(M.hazard t : ℝ)‖) := by
      filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      have hs := hbounds t ⟨ht.1, ht.2.le⟩
      simp only [f, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs.1,
        abs_of_nonneg (NNReal.coe_nonneg (M.hazard t))]
      exact mul_le_of_le_one_left (NNReal.coe_nonneg _) hs.2
    exact Integrable.mono
      (((intervalIntegrable_iff_integrableOn_Ico_of_le hab).mp hh) :
        Integrable (fun t : ℝ => (M.hazard t : ℝ)) (volume.restrict (Ico a b)))
      hfm hbound
  have hmeas : Ico a b ⊆ Ico 0 M.horizon := by
    intro t ht
    exact ⟨le_trans ha ht.1, lt_of_lt_of_le ht.2 hb⟩
  rw [withDensity_apply _ measurableSet_Ico]
  change (∫⁻ t, ENNReal.ofReal (hazardSurvival M.hazard t) *
    (M.hazard t : ℝ≥0∞) ∂((volume.restrict (Ico 0 M.horizon)).restrict (Ico a b))) = _
  rw [Measure.restrict_restrict_of_subset hmeas]
  have hnn : 0 ≤ᵐ[volume.restrict (Ico a b)] f := by
    filter_upwards [] with t
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (NNReal.coe_nonneg _)
  have heq : ∀ t, ENNReal.ofReal (f t) =
      ENNReal.ofReal (hazardSurvival M.hazard t) * (M.hazard t : ℝ≥0∞) := by
    intro t
    change ENNReal.ofReal (hazardSurvival M.hazard t * (M.hazard t : ℝ)) = _
    have hp : 0 ≤ hazardSurvival M.hazard t := by
      unfold hazardSurvival
      positivity
    rw [ENNReal.ofReal_mul hp]
    simp
  simp_rw [← heq]
  rw [← ofReal_integral_eq_lintegral_ofReal hf hnn]
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact congrArg ENNReal.ofReal
    (hazardSurvival_interval_integral M.hazard M.horizon a b
      M.hazard_integrable ha hab hb)

/-- [A recurrent-event model](hyp:M) has [a death-time law on its open
finite horizon with density equal to survival times hazard](goal) relative
to Lebesgue measure. -/
theorem Model.death_law_restrict_eq_withDensity (M : Model A X) :
    M.deathLaw.restrict (Ico 0 M.horizon) =
      (volume.restrict (Ico 0 M.horizon)).withDensity
        (fun t => ENNReal.ofReal (hazardSurvival M.hazard t) *
          (M.hazard t : ℝ≥0∞)) := by
  letI := M.deathProb
  let f : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (hazardSurvival M.hazard t) * (M.hazard t : ℝ≥0∞)
  let ν : Measure ℝ := (volume.restrict (Ico 0 M.horizon)).withDensity f
  have hν : ν = (volume.withDensity f).restrict (Ico 0 M.horizon) :=
    (restrict_withDensity measurableSet_Ico f).symm
  change M.deathLaw.restrict (Ico 0 M.horizon) = ν
  apply Measure.ext_of_Ico'
  · intro a b hab
    exact measure_ne_top _ _
  · intro a b hab
    let c := max a 0
    let d := min b M.horizon
    have hset : Ico a b ∩ Ico 0 M.horizon = Ico c d := Set.Ico_inter_Ico
    have hsub : Ico c d ⊆ Ico 0 M.horizon := by
      intro t ht
      exact ⟨le_trans (le_max_right _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
    have hleft : (M.deathLaw.restrict (Ico 0 M.horizon)) (Ico a b) =
        M.deathLaw (Ico c d) := by
      rw [Measure.restrict_apply measurableSet_Ico, hset]
    have hright : ν (Ico a b) = ν (Ico c d) := by
      calc
        ν (Ico a b) = (volume.withDensity f) (Ico c d) := by
          rw [hν, Measure.restrict_apply measurableSet_Ico, hset]
        _ = ν (Ico c d) := by
          rw [hν, Measure.restrict_apply measurableSet_Ico,
            Set.inter_eq_self_of_subset_left hsub]
    rw [hleft, hright]
    by_cases hcd : c ≤ d
    · have hc : 0 ≤ c := le_max_right _ _
      have hd : d ≤ M.horizon := min_le_right _ _
      change M.deathLaw (Ico c d) =
        ((volume.restrict (Ico 0 M.horizon)).withDensity f) (Ico c d)
      rw [M.death_law_Ico_eq_survival_sub c d hc hcd hd,
        M.survival_hazard_density_Ico c d hc hcd hd]
    · have hempty : Ico c d = ∅ := Set.Ico_eq_empty_of_le (le_of_not_ge hcd)
      simp [hempty]

end Causalean.Stat.RecurrentEvent
