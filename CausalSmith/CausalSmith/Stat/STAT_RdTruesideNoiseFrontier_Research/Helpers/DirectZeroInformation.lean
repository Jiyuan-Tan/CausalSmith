module

public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.DirectWitness
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.ObservedCellDensity

/-!
# Noiseless direct-witness information bound
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- At zero noise, a treated observed cell is exactly its latent score cell. Given [the displayed inputs and assumptions](hyp:β,h,s,y,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma direct_observed_treated_cell_zero
    (β h : ℝ) (s y : Bool) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) :
    observedCellMeasure (directAltLaw β h s hβ hh) 0 true y =
      treatedLatentCell (directProbability β h s) y := by
  have hp := directProbability_properties β h s hβ hh
  letI := uniformScore_probability
  let μ := uniformScore.restrict (Ici (0 : ℝ))
  haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hsupp : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 :=
    Measure.absolutelyContinuous_restrict.ae_le uniformScore_support
  have hden : (fun x : ℝ => ENNReal.ofReal
      (if y then directProbability β h s x else 1 - directProbability β h s x))
      ≤ᵐ[μ] (fun _ => 1) := by
    filter_upwards [hsupp] with x hx
    have hb := hp.2.2 x hx
    cases y <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      rw [ENNReal.ofReal_le_one] <;> linarith
  haveI : IsFiniteMeasure (treatedLatentCell (directProbability β h s) y) := by
    unfold treatedLatentCell
    exact isFiniteMeasure_of_le μ (by
      simpa [μ] using withDensity_mono hden)
  unfold directAltLaw
  rw [witness_observed_treated_cell_eq_conv
    (directProbability β h s) hp.1 hp.2.1 hp.2.2]
  have hmap : (gaussianReal 0 1).map (fun z => (0 : ℝ) * z) = Measure.dirac 0 := by
    rw [show (fun z : ℝ => (0 : ℝ) * z) = fun _ => (0 : ℝ) by funext z; simp,
      Measure.map_const]
    simp
  rw [hmap, MeasureTheory.Measure.conv_dirac_zero]

/-- At zero noise, either control observed cell is the common latent score cell. Given [the displayed inputs and assumptions](hyp:β,h,s,y,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma direct_observed_control_cell_zero
    (β h : ℝ) (s y : Bool) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) :
    observedCellMeasure (directAltLaw β h s hβ hh) 0 false y =
      controlLatentCell := by
  have hp := directProbability_properties β h s hβ hh
  letI := uniformScore_probability
  haveI : IsFiniteMeasure controlLatentCell := by
    unfold controlLatentCell
    let μ := uniformScore.restrict (Iio (0 : ℝ))
    haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
    exact isFiniteMeasure_of_le μ (by
      have hle := withDensity_mono (μ := μ) (by
        filter_upwards [] with x
        norm_num : (fun x : ℝ => ENNReal.ofReal (1 / 2 : ℝ)) ≤ᵐ[μ] (fun _ => 1))
      simpa [μ] using hle)
  unfold directAltLaw
  rw [witness_observed_control_cell_eq_conv
    (directProbability β h s) hp.1 hp.2.1 hp.2.2]
  have hmap : (gaussianReal 0 1).map (fun z => (0 : ℝ) * z) = Measure.dirac 0 := by
    rw [show (fun z : ℝ => (0 : ℝ) * z) = fun _ => (0 : ℝ) by funext z; simp,
      Measure.map_const]
    simp
  rw [hmap, MeasureTheory.Measure.conv_dirac_zero]

/-- Density of the noiseless observed direct alternative with respect to
Lebesgue measure on the score and counting measure on the two marks. Given [the displayed inputs and assumptions](hyp:β,h,s,o), [this definition specifies the stated object](goal). -/
@[no_expose]
def directZeroDensity (β h : ℝ) (s : Bool) (o : Obs) : ℝ :=
  if o.2.1 then
    if o.1 ∈ Icc (0 : ℝ) 1 then
      (1 / 2 : ℝ) * (if o.2.2 then directProbability β h s o.1
        else 1 - directProbability β h s o.1)
    else 0
  else if o.1 ∈ Ico (-1 : ℝ) 0 then 1 / 4 else 0

/-- Given [the displayed inputs and assumptions](hyp:β,h,s), [the stated mathematical conclusion holds](goal). -/
lemma directZeroDensity_measurable (β h : ℝ) (s : Bool) :
    Measurable (directZeroDensity β h s) := by
  have hp : Measurable (directProbability β h s) := by
    unfold directProbability directBump
    apply measurable_const.add
    apply measurable_const.mul
    apply Measurable.ite measurableSet_Iio measurable_const
    exact (measurable_const.sub (measurable_id.div_const h)).max measurable_const
  unfold directZeroDensity
  apply Measurable.ite
  · exact (measurableSet_singleton true).preimage
      (measurable_fst.comp measurable_snd)
  · apply Measurable.ite
    · exact measurableSet_Icc.preimage measurable_fst
    · exact measurable_const.mul (Measurable.ite
        ((measurableSet_singleton true).preimage
          (measurable_snd.comp measurable_snd))
        (hp.comp measurable_fst)
        (measurable_const.sub (hp.comp measurable_fst)))
    · exact measurable_const
  · apply Measurable.ite
    · exact measurableSet_Ico.preimage measurable_fst
    · exact measurable_const
    · exact measurable_const

/-- Given [the displayed inputs and assumptions](hyp:β,h,s,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma directAltLaw_observed_density_zero
    (β h : ℝ) (s : Bool) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) :
    Pobs (directAltLaw β h s hβ hh) 0 =
      observedReference.withDensity
        (fun o => ENNReal.ofReal (directZeroDensity β h s o)) := by
  let L := directAltLaw β h s hβ hh
  have hdens : Measurable (fun o : Obs => ENNReal.ofReal
      (directZeroDensity β h s o)) :=
    (directZeroDensity_measurable β h s).ennreal_ofReal
  ext A hA
  rw [measure_apply_eq_sum_observedCellMeasure L 0 A hA]
  unfold observedReference
  rw [withDensity_apply _ hA, ← lintegral_indicator hA]
  rw [lintegral_prod _ (hdens.indicator hA).aemeasurable]
  simp_rw [lintegral_count, tsum_fintype]
  rw [lintegral_finset_sum]
  swap
  · intro i _
    exact ((hdens.comp (measurable_id.prodMk measurable_const)).indicator
      (hA.preimage (measurable_id.prodMk measurable_const)))
  apply Finset.sum_congr rfl
  intro i _
  rcases i with ⟨d, y⟩
  change observedCellMeasure L 0 d y (observedCellEmbed d y ⁻¹' A) =
    ∫⁻ w : ℝ, (observedCellEmbed d y ⁻¹' A).indicator
      (fun w => ENNReal.ofReal
        (directZeroDensity β h s (observedCellEmbed d y w))) w
  have hcellA : MeasurableSet (observedCellEmbed d y ⁻¹' A) :=
    hA.preimage (measurable_id.prodMk (measurable_const.prodMk measurable_const))
  rw [lintegral_indicator hcellA]
  cases d
  · rw [direct_observed_control_cell_zero β h s y hβ hh,
      controlLatentCell_eq_withDensity, withDensity_apply _ hcellA]
    apply lintegral_congr
    intro w
    by_cases hw : w ∈ Ico (-1 : ℝ) 0
    · simp [directZeroDensity, observedCellEmbed, controlCellBaseDensity, hw]
    · simp [directZeroDensity, observedCellEmbed, controlCellBaseDensity, hw]
  · rw [direct_observed_treated_cell_zero β h s y hβ hh,
      treatedLatentCell_eq_withDensity _ _
        (directProbability_properties β h s hβ hh).1,
      withDensity_apply _ hcellA]
    apply lintegral_congr
    intro w
    by_cases hw : w ∈ Icc (0 : ℝ) 1
    · simp only [directZeroDensity, observedCellEmbed, if_true,
        treatedCellBaseDensity, Set.indicator_of_mem hw]
      have hb := (directProbability_properties β h s hβ hh).2.2 w
        ⟨by linarith [hw.1], by linarith [hw.2]⟩
      cases y <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
        rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))] <;>
        congr 1 <;> simp [hw]
    · simp [directZeroDensity, observedCellEmbed, treatedCellBaseDensity, hw]

/-- Likelihood ratio of the plus direct alternative against the minus direct
alternative on the common noiseless support. Given [the displayed inputs and assumptions](hyp:β,h,o), [this definition specifies the stated object](goal). -/
@[no_expose]
def directZeroLikelihoodRatio (β h : ℝ) (o : Obs) : ℝ :=
  if o.2.1 ∧ o.1 ∈ Icc (0 : ℝ) 1 then
    directZeroDensity β h true o / directZeroDensity β h false o
  else 1

/-- Given [the displayed inputs and assumptions](hyp:β,h), [the stated mathematical conclusion holds](goal). -/
lemma directZeroLikelihoodRatio_measurable (β h : ℝ) :
    Measurable (directZeroLikelihoodRatio β h) := by
  unfold directZeroLikelihoodRatio
  apply Measurable.ite
  · exact ((measurableSet_singleton true).preimage
      (measurable_fst.comp measurable_snd)).inter
      (measurableSet_Icc.preimage measurable_fst)
  · exact (directZeroDensity_measurable β h true).div
      (directZeroDensity_measurable β h false)
  · exact measurable_const

/-- Given [the displayed inputs and assumptions](hyp:β,h,s,hβ,hh,o), [the stated mathematical conclusion holds](goal). -/
lemma directZeroDensity_nonneg
    (β h : ℝ) (s : Bool) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) (o : Obs) :
    0 ≤ directZeroDensity β h s o := by
  unfold directZeroDensity
  split_ifs with hd hx hy hx
  · exact mul_nonneg (by norm_num)
      ((directProbability_properties β h s hβ hh).2.2 o.1
        ⟨by linarith [hx.1], by linarith [hx.2]⟩).1
  · exact mul_nonneg (by norm_num) (sub_nonneg.mpr
      ((directProbability_properties β h s hβ hh).2.2 o.1
        ⟨by linarith [hx.1], by linarith [hx.2]⟩).2)
  all_goals norm_num

/-- Given [the displayed inputs and assumptions](hyp:β,h,hβ,hh,o,ho,hx), [the stated mathematical conclusion holds](goal). -/
lemma directZeroDensity_false_pos
    (β h : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) (o : Obs)
    (ho : o.2.1 = true) (hx : o.1 ∈ Icc (0 : ℝ) 1) :
    0 < directZeroDensity β h false o := by
  unfold directZeroDensity
  rw [if_pos ho, if_pos hx]
  have hb := directProbability_mean_bounds β h false hβ hh o.1
  cases o.2.2 <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
    nlinarith [hb.1, hb.2]

/-- Given [the displayed inputs and assumptions](hyp:β,h,hβ,hh,o), [the stated mathematical conclusion holds](goal). -/
lemma directZeroDensity_mul_likelihoodRatio
    (β h : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) (o : Obs) :
    ENNReal.ofReal (directZeroDensity β h false o) *
        ENNReal.ofReal (directZeroLikelihoodRatio β h o) =
      ENNReal.ofReal (directZeroDensity β h true o) := by
  by_cases hs : o.2.1 = true ∧ o.1 ∈ Icc (0 : ℝ) 1
  · rw [directZeroLikelihoodRatio, if_pos hs]
    rw [ENNReal.ofReal_div_of_pos
      (directZeroDensity_false_pos β h hβ hh o hs.1 hs.2)]
    exact ENNReal.mul_div_cancel
      (by simp [directZeroDensity_false_pos β h hβ hh o hs.1 hs.2])
      ENNReal.ofReal_ne_top
  · rw [directZeroLikelihoodRatio, if_neg hs]
    simp only [ENNReal.ofReal_one, mul_one]
    unfold directZeroDensity
    by_cases hd : o.2.1 = true
    · have hx : o.1 ∉ Icc (0 : ℝ) 1 := fun hx => hs ⟨hd, hx⟩
      simp [hd, hx]
    · simp [hd]

/-- Given [the displayed inputs and assumptions](hyp:β,h,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma directAltLaw_plus_eq_minus_withDensity_zero
    (β h : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) :
    Pobs (directAltLaw β h true hβ hh) 0 =
      (Pobs (directAltLaw β h false hβ hh) 0).withDensity
        (fun o => ENNReal.ofReal (directZeroLikelihoodRatio β h o)) := by
  rw [directAltLaw_observed_density_zero β h true hβ hh,
    directAltLaw_observed_density_zero β h false hβ hh, ← withDensity_mul]
  · congr 1
    funext o
    exact (directZeroDensity_mul_likelihoodRatio β h hβ hh o).symm
  · exact (directZeroDensity_measurable β h false).ennreal_ofReal
  · exact (directZeroLikelihoodRatio_measurable β h).ennreal_ofReal

/-- Given [the displayed inputs and assumptions](hyp:β,h,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma directAltLaw_observed_rnDeriv_zero
    (β h : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) :
    (fun o => ((Pobs (directAltLaw β h true hβ hh) 0).rnDeriv
      (Pobs (directAltLaw β h false hβ hh) 0) o).toReal) =ᵐ[
        Pobs (directAltLaw β h false hβ hh) 0]
      directZeroLikelihoodRatio β h := by
  letI := (directAltLaw β h false hβ hh).prob
  letI : IsProbabilityMeasure (Pobs (directAltLaw β h false hβ hh) 0) :=
    Measure.isProbabilityMeasure_map (obs_measurable 0).aemeasurable
  rw [directAltLaw_plus_eq_minus_withDensity_zero β h hβ hh]
  filter_upwards [Measure.rnDeriv_withDensity
    (Pobs (directAltLaw β h false hβ hh) 0)
    (directZeroLikelihoodRatio_measurable β h).ennreal_ofReal] with o ho
  rw [ho, ENNReal.toReal_ofReal]
  unfold directZeroLikelihoodRatio
  split_ifs with hs
  · exact div_nonneg
      (directZeroDensity_nonneg β h true hβ hh o)
      (directZeroDensity_nonneg β h false hβ hh o)
  · norm_num

/-- Given [the displayed inputs and assumptions](hyp:β,h,hβ,hh,o), [the stated mathematical conclusion holds](goal). -/
lemma directZeroLikelihoodRatio_bounds
    (β h : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) (o : Obs) :
    0 ≤ directZeroLikelihoodRatio β h o ∧
      directZeroLikelihoodRatio β h o ≤ 3 := by
  unfold directZeroLikelihoodRatio
  split_ifs with hs
  · have hp := directProbability_mean_bounds β h true hβ hh o.1
    have hm := directProbability_mean_bounds β h false hβ hh o.1
    have hden := directZeroDensity_false_pos β h hβ hh o hs.1 hs.2
    unfold directZeroDensity
    rw [if_pos hs.1, if_pos hs.2, if_pos hs.1, if_pos hs.2]
    cases o.2.2 <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      constructor
    · exact div_nonneg (by nlinarith [hp.1, hp.2]) (by nlinarith [hm.1, hm.2])
    · have hden' : 0 < (1 / 2 : ℝ) *
          (1 - directProbability β h false o.1) := by nlinarith [hm.1, hm.2]
      apply (div_le_iff₀ hden').2
      nlinarith [hp.1, hp.2, hm.1, hm.2]
    · exact div_nonneg (by nlinarith [hp.1, hp.2]) (by nlinarith [hm.1, hm.2])
    · have hden' : 0 < (1 / 2 : ℝ) *
          directProbability β h false o.1 := by nlinarith [hm.1, hm.2]
      apply (div_le_iff₀ hden').2
      nlinarith [hp.1, hp.2, hm.1, hm.2]
  · norm_num

/-- Given [the displayed inputs and assumptions](hyp:β,h,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma directAltLaw_observed_likelihood_square_integrable_zero
    (β h : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun o => (((Pobs (directAltLaw β h true hβ hh) 0).rnDeriv
      (Pobs (directAltLaw β h false hβ hh) 0) o).toReal - 1)^2)
      (Pobs (directAltLaw β h false hβ hh) 0) := by
  letI := (directAltLaw β h false hβ hh).prob
  letI : IsProbabilityMeasure (Pobs (directAltLaw β h false hβ hh) 0) :=
    Measure.isProbabilityMeasure_map (obs_measurable 0).aemeasurable
  have hr := directAltLaw_observed_rnDeriv_zero β h hβ hh
  have hi : Integrable (fun o => (directZeroLikelihoodRatio β h o - 1)^2)
      (Pobs (directAltLaw β h false hβ hh) 0) := Integrable.of_bound
    (((directZeroLikelihoodRatio_measurable β h).sub measurable_const).pow_const 2).aestronglyMeasurable
    4 (Filter.Eventually.of_forall fun o => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb := directZeroLikelihoodRatio_bounds β h hβ hh o
      nlinarith [sq_nonneg (directZeroLikelihoodRatio β h o - 1)])
  apply hi.congr
  filter_upwards [hr] with o ho
  rw [ho]

/-- Given [the displayed inputs and assumptions](hyp:β,h,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma directAltLaw_observed_ac_zero
    (β h : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) :
    Pobs (directAltLaw β h true hβ hh) 0 ≪
      Pobs (directAltLaw β h false hβ hh) 0 := by
  rw [directAltLaw_plus_eq_minus_withDensity_zero β h hβ hh]
  exact withDensity_absolutelyContinuous _ _

/-- Given [the displayed inputs and assumptions](hyp:β,h,o), [this definition specifies the stated object](goal). -/
@[no_expose]
def directZeroChiIntegrand (β h : ℝ) (o : Obs) : ℝ :=
  directZeroDensity β h false o * (directZeroLikelihoodRatio β h o - 1)^2

/-- Given [the displayed inputs and assumptions](hyp:β,h,o), [this definition specifies the stated object](goal). -/
@[no_expose]
def directZeroChiMajorant (β h : ℝ) (o : Obs) : ℝ :=
  if o.2.1 ∧ o.1 ∈ Icc (0 : ℝ) 1 then
    8 * (kappa * h^β * directBump h o.1)^2
  else 0

/-- Given [the displayed inputs and assumptions](hyp:β,h), [the stated mathematical conclusion holds](goal). -/
lemma directZeroChiIntegrand_measurable (β h : ℝ) :
    Measurable (directZeroChiIntegrand β h) := by
  unfold directZeroChiIntegrand
  exact (directZeroDensity_measurable β h false).mul
    (((directZeroLikelihoodRatio_measurable β h).sub measurable_const).pow_const 2)

/-- Given [the displayed inputs and assumptions](hyp:β,h), [the stated mathematical conclusion holds](goal). -/
lemma directZeroChiMajorant_measurable (β h : ℝ) :
    Measurable (directZeroChiMajorant β h) := by
  have hb : Measurable (directBump h) := by
    unfold directBump
    apply Measurable.ite measurableSet_Iio measurable_const
    exact (measurable_const.sub (measurable_id.div_const h)).max measurable_const
  unfold directZeroChiMajorant
  apply Measurable.ite
  · exact ((measurableSet_singleton true).preimage
      (measurable_fst.comp measurable_snd)).inter
      (measurableSet_Icc.preimage measurable_fst)
  · exact measurable_const.mul
      ((measurable_const.mul (hb.comp measurable_fst)).pow_const 2)
  · exact measurable_const

/-- Given [the displayed inputs and assumptions](hyp:β,h,hβ,hh,o), [the stated mathematical conclusion holds](goal). -/
lemma directZeroChiIntegrand_le_majorant
    (β h : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) (o : Obs) :
    0 ≤ directZeroChiIntegrand β h o ∧
      directZeroChiIntegrand β h o ≤ directZeroChiMajorant β h o := by
  by_cases hs : o.2.1 = true ∧ o.1 ∈ Icc (0 : ℝ) 1
  · have hp := directProbability_mean_bounds β h true hβ hh o.1
    have hm := directProbability_mean_bounds β h false hβ hh o.1
    have hbump := directBump_mem h hh.1 o.1
    have hhpow : h^β ≤ 1 := Real.rpow_le_one hh.1.le hh.2 hβ.1.le
    have ha : 0 ≤ kappa * h^β * directBump h o.1 ∧
        kappa * h^β * directBump h o.1 ≤ 1 / 100 := by
      constructor
      · exact mul_nonneg (mul_nonneg (by norm_num [kappa])
          (Real.rpow_nonneg hh.1.le _)) hbump.1
      · change kappa * h^β * directBump h o.1 ≤ kappa
        calc
          _ ≤ kappa * (1 * 1) := by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
              (mul_le_mul hhpow hbump.2 hbump.1 (by norm_num))
              (by norm_num [kappa])
          _ = kappa := by ring
    unfold directZeroChiIntegrand directZeroChiMajorant directZeroLikelihoodRatio
    rw [if_pos hs, if_pos hs]
    unfold directZeroDensity directProbability
    rw [if_pos hs.1, if_pos hs.2, if_pos hs.1, if_pos hs.2]
    cases o.2.2 <;> simp only [Bool.false_eq_true, if_false, if_true, witnessSign,
      one_mul, neg_one_mul]
    · change 0 ≤ (1 / 2 : ℝ) *
          (1 - (1 / 2 + (-kappa) * h^β * directBump h o.1)) *
          (((1 / 2 : ℝ) * (1 - (1 / 2 + kappa * h^β * directBump h o.1))) /
            ((1 / 2 : ℝ) * (1 - (1 / 2 + (-kappa) * h^β * directBump h o.1))) - 1)^2 ∧
        (1 / 2 : ℝ) * (1 - (1 / 2 + (-kappa) * h^β * directBump h o.1)) *
          (((1 / 2 : ℝ) * (1 - (1 / 2 + kappa * h^β * directBump h o.1))) /
            ((1 / 2 : ℝ) * (1 - (1 / 2 + (-kappa) * h^β * directBump h o.1))) - 1)^2 ≤
          8 * (kappa * h^β * directBump h o.1)^2
      have hminus : (1 / 2 : ℝ) + (-kappa) * h^β * directBump h o.1 =
          1 / 2 - kappa * h^β * directBump h o.1 := by ring
      rw [hminus]
      have hd : 0 < (1 / 2 : ℝ) *
          (1 - (1 / 2 - kappa * h^β * directBump h o.1)) := by
        nlinarith [ha.1, ha.2]
      have hq : (1 / 8 : ℝ) ≤ (1 / 2 : ℝ) *
          (1 - (1 / 2 - kappa * h^β * directBump h o.1)) := by
        nlinarith [ha.1, ha.2]
      have hratio :
          (1 / 2 * (1 - (1 / 2 + kappa * h^β * directBump h o.1))) /
              (1 / 2 * (1 - (1 / 2 - kappa * h^β * directBump h o.1))) - 1 =
            -(kappa * h^β * directBump h o.1) /
              (1 / 2 * (1 - (1 / 2 - kappa * h^β * directBump h o.1))) := by
        rw [div_sub_one hd.ne']
        field_simp [hd.ne']
        ring
      constructor
      · exact mul_nonneg (by nlinarith [ha.1, ha.2]) (sq_nonneg _)
      · rw [hratio]
        have heq :
            (1 / 2 * (1 - (1 / 2 - kappa * h^β * directBump h o.1))) *
                (-(kappa * h^β * directBump h o.1) /
                  (1 / 2 * (1 - (1 / 2 - kappa * h^β * directBump h o.1))))^2 =
              (kappa * h^β * directBump h o.1)^2 /
                (1 / 2 * (1 - (1 / 2 - kappa * h^β * directBump h o.1))) := by
          field_simp [hd.ne']
        rw [heq]
        apply (div_le_iff₀ hd).2
        nlinarith [hq, sq_nonneg (kappa * h^β * directBump h o.1)]
    · change 0 ≤ (1 / 2 : ℝ) *
          (1 / 2 + (-kappa) * h^β * directBump h o.1) *
          (((1 / 2 : ℝ) * (1 / 2 + kappa * h^β * directBump h o.1)) /
            ((1 / 2 : ℝ) * (1 / 2 + (-kappa) * h^β * directBump h o.1)) - 1)^2 ∧
        (1 / 2 : ℝ) * (1 / 2 + (-kappa) * h^β * directBump h o.1) *
          (((1 / 2 : ℝ) * (1 / 2 + kappa * h^β * directBump h o.1)) /
            ((1 / 2 : ℝ) * (1 / 2 + (-kappa) * h^β * directBump h o.1)) - 1)^2 ≤
          8 * (kappa * h^β * directBump h o.1)^2
      have hminus : (1 / 2 : ℝ) + (-kappa) * h^β * directBump h o.1 =
          1 / 2 - kappa * h^β * directBump h o.1 := by ring
      rw [hminus]
      have hd : 0 < (1 / 2 : ℝ) *
          (1 / 2 - kappa * h^β * directBump h o.1) := by
        nlinarith [ha.1, ha.2]
      have hq : (1 / 8 : ℝ) ≤ (1 / 2 : ℝ) *
          (1 / 2 - kappa * h^β * directBump h o.1) := by
        nlinarith [ha.1, ha.2]
      have hratio :
          (1 / 2 * (1 / 2 + kappa * h^β * directBump h o.1)) /
              (1 / 2 * (1 / 2 - kappa * h^β * directBump h o.1)) - 1 =
            (kappa * h^β * directBump h o.1) /
              (1 / 2 * (1 / 2 - kappa * h^β * directBump h o.1)) := by
        rw [div_sub_one hd.ne']
        field_simp [hd.ne']
        ring
      constructor
      · exact mul_nonneg (by nlinarith [ha.1, ha.2]) (sq_nonneg _)
      · rw [hratio]
        have heq :
            (1 / 2 * (1 / 2 - kappa * h^β * directBump h o.1)) *
                ((kappa * h^β * directBump h o.1) /
                  (1 / 2 * (1 / 2 - kappa * h^β * directBump h o.1)))^2 =
              (kappa * h^β * directBump h o.1)^2 /
                (1 / 2 * (1 / 2 - kappa * h^β * directBump h o.1)) := by
          field_simp [hd.ne']
        rw [heq]
        apply (div_le_iff₀ hd).2
        nlinarith [hq, sq_nonneg (kappa * h^β * directBump h o.1)]
  · have hr : directZeroLikelihoodRatio β h o = 1 := by
      unfold directZeroLikelihoodRatio
      rw [if_neg hs]
    have hm : directZeroChiMajorant β h o = 0 := by
      unfold directZeroChiMajorant
      rw [if_neg hs]
    rw [hm]
    simp [directZeroChiIntegrand, hr]

/-- Given [the displayed inputs and assumptions](hyp:β,h,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma directZeroChiMajorant_integrable
    (β h : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) :
    Integrable (directZeroChiMajorant β h) observedReference := by
  unfold observedReference
  refine (integrable_prod_iff
    (directZeroChiMajorant_measurable β h).aestronglyMeasurable).2
    ⟨Filter.Eventually.of_forall (fun w => Integrable.of_finite), ?_⟩
  have hc : Continuous (fun w : ℝ =>
      16 * (kappa * h^β * directBump h w)^2) := by
    exact continuous_const.mul
      ((continuous_const.mul (directBump_continuous h hh.1)).pow 2)
  have hi : Integrable ((Icc (0 : ℝ) 1).indicator
      (fun w => 16 * (kappa * h^β * directBump h w)^2)) volume :=
    hc.integrableOn_Icc.integrable_indicator measurableSet_Icc
  apply hi.congr
  filter_upwards [] with w
  rw [integral_count]
  simp only [Real.norm_eq_abs, Fintype.sum_prod_type, Fintype.sum_bool]
  by_cases hw : w ∈ Icc (0 : ℝ) 1
  · simp [directZeroChiMajorant, hw]
    have ha : |kappa| * |h^β| * |directBump h w| =
        |kappa * h^β * directBump h w| := by rw [abs_mul, abs_mul]
    rw [ha, sq_abs]
    ring
  · simp [directZeroChiMajorant, hw]

/-- Given [the displayed inputs and assumptions](hyp:β,h,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma directZeroChiMajorant_integral
    (β h : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) :
    (∫ o, directZeroChiMajorant β h o ∂observedReference) =
      (16 / 3 : ℝ) * kappa^2 * h^(2*β+1) := by
  unfold observedReference
  rw [integral_prod _ (directZeroChiMajorant_integrable β h hβ hh)]
  have heq : (fun w : ℝ => ∫ z : Bool × Bool,
      directZeroChiMajorant β h (w, z) ∂Measure.count) =
      fun w => (Icc (0 : ℝ) 1).indicator
        (fun w => 16 * (kappa * h^β * directBump h w)^2) w := by
    funext w
    rw [integral_count]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    by_cases hw : w ∈ Icc (0 : ℝ) 1
    · simp [directZeroChiMajorant, hw]
      ring
    · simp [directZeroChiMajorant, hw]
  rw [heq, integral_indicator measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [show (∫ x in (0 : ℝ)..1,
      16 * (kappa * h^β * directBump h x)^2) =
      16 * (kappa * h^β)^2 *
        ∫ x in (0 : ℝ)..1, (directBump h x)^2 by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring]
  rw [directBump_sq_integral_arm h hh]
  rw [show h^(2*β+1) = (h^β)^2 * h by
    rw [show 2 * β + 1 = β * 2 + 1 by ring, Real.rpow_add hh.1,
      Real.rpow_mul hh.1.le]
    norm_num]
  ring

/-- The noiseless direct alternatives have one-observation chi-squared
divergence of the boundary-bump order `h^(2*beta+1)`. Given [the displayed inputs and assumptions](hyp:β,h,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma directAltLaw_observed_chiSqDiv_zero_le
    (β h : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) :
    Causalean.Stat.chiSqDiv
      (Pobs (directAltLaw β h true hβ hh) 0)
      (Pobs (directAltLaw β h false hβ hh) 0) ≤
        (16 / 3 : ℝ) * kappa^2 * h^(2*β+1) := by
  let P := directAltLaw β h true hβ hh
  let Q := directAltLaw β h false hβ hh
  letI := P.prob
  letI := Q.prob
  letI : IsProbabilityMeasure (Pobs P 0) :=
    Measure.isProbabilityMeasure_map (obs_measurable 0).aemeasurable
  letI : IsProbabilityMeasure (Pobs Q 0) :=
    Measure.isProbabilityMeasure_map (obs_measurable 0).aemeasurable
  have hmaj := directZeroChiMajorant_integrable β h hβ hh
  have hint : Integrable (directZeroChiIntegrand β h) observedReference := by
    apply hmaj.mono' (directZeroChiIntegrand_measurable β h).aestronglyMeasurable
    filter_upwards [] with o
    have hb := directZeroChiIntegrand_le_majorant β h hβ hh o
    simpa [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
  rw [Causalean.Stat.chiSqDiv]
  calc
    (∫ o, (((Pobs P 0).rnDeriv (Pobs Q 0) o).toReal - 1)^2 ∂Pobs Q 0) =
        ∫ o, (directZeroLikelihoodRatio β h o - 1)^2 ∂Pobs Q 0 := by
      apply integral_congr_ae
      filter_upwards [directAltLaw_observed_rnDeriv_zero β h hβ hh] with o ho
      rw [ho]
    _ = ∫ o, directZeroChiIntegrand β h o ∂observedReference := by
      dsimp [Q]
      rw [directAltLaw_observed_density_zero β h false hβ hh]
      rw [integral_withDensity_eq_integral_toReal_smul
        (directZeroDensity_measurable β h false).ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp_rw [ENNReal.toReal_ofReal
        (directZeroDensity_nonneg β h false hβ hh _)]
      simp only [smul_eq_mul]
      rfl
    _ ≤ ∫ o, directZeroChiMajorant β h o ∂observedReference := by
      exact integral_mono hint hmaj (fun o =>
        (directZeroChiIntegrand_le_majorant β h hβ hh o).2)
    _ = _ := directZeroChiMajorant_integral β h hβ hh

end CausalSmith.Stat.RdTruesideNoiseFrontier
