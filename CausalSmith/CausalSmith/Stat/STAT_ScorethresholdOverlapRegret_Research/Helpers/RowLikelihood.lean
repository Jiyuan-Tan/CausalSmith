module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.BlockConstruction
public import Causalean.Stat.Minimax.ChiSquared

/-! # Binary-outcome likelihood calculation

The uniform-coin construction gives the two Rademacher masses explicitly.
Changing the sign of its mean is a bounded likelihood change, whose squared
centered density integrates to the one-channel chi-square formula.
-/

@[expose] public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- Every test of a binary outcome is integrable, since it takes just two values. -/
-- @node: binaryOutcome_test_integrable
lemma binaryOutcome_test_integrable (μ : ℝ) (f : ℝ → ℝ) :
    Integrable (fun u => f (binaryOutcome μ u)) uniformRandomizer := by
  have := uniformRandomizer_probability
  have hm : Measurable (fun u => f (binaryOutcome μ u)) := by
    simp only [binaryOutcome, apply_ite]
    apply Measurable.ite (measurableSet_le measurable_id measurable_const) <;> fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable (max |f 1| |f (-1)|)
  apply Filter.Eventually.of_forall
  intro u
  simp only [Real.norm_eq_abs, binaryOutcome]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- A test of a feasible binary outcome is the weighted sum of its two values. -/
-- @node: binaryOutcome_test_integral
lemma binaryOutcome_test_integral (μ : ℝ) (hμ : -1 ≤ μ) (hμ1 : μ ≤ 1)
    (f : ℝ → ℝ) :
    (∫ u, f (binaryOutcome μ u) ∂uniformRandomizer) =
      (1+μ)/2 * f 1 + (1-μ)/2 * f (-1) := by
  have := uniformRandomizer_probability
  have hi := binaryOutcome_test_integrable μ (fun y => if y = 1 then (1:ℝ) else 0)
  have heq : (fun u => if binaryOutcome μ u = 1 then (1:ℝ) else 0) =
      (fun u => if u ≤ (1+μ)/2 then (1:ℝ) else 0) := by
    funext u
    by_cases hu : u ≤ (1+μ)/2 <;> norm_num [binaryOutcome, hu]
  rw [heq] at hi
  calc
    _ = ∫ u, (f 1 - f (-1)) * (if u ≤ (1+μ)/2 then (1:ℝ) else 0) +
        f (-1) ∂uniformRandomizer := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      by_cases hu : u ≤ (1+μ)/2 <;> norm_num [binaryOutcome, hu] <;> ring
    _ = (f 1 - f (-1)) * ((1+μ)/2) + f (-1) := by
      rw [integral_add (hi.const_mul _) (integrable_const _), integral_const_mul,
        uniformRandomizer_coin_integral _ (by linarith) (by linarith)]
      simp
    _ = _ := by ring

/-- Likelihood of the positive-mean binary outcome relative to the negative-mean one. -/
-- @node: binarySignLikelihood
noncomputable def binarySignLikelihood (h y : ℝ) : ℝ :=
  if y = 1 then (1+h)/(1-h) else (1-h)/(1+h)

/-- The likelihood exactly changes the sign of the mean for every binary-outcome test. -/
-- @node: binaryOutcome_sign_change
lemma binaryOutcome_sign_change (h : ℝ) (hh : -1 < h) (hh1 : h < 1)
    (f : ℝ → ℝ) :
    (∫ u, binarySignLikelihood h (binaryOutcome (-h) u) *
      f (binaryOutcome (-h) u) ∂uniformRandomizer) =
    ∫ u, f (binaryOutcome h u) ∂uniformRandomizer := by
  rw [binaryOutcome_test_integral (-h) (by linarith) (by linarith)
    (fun y => binarySignLikelihood h y * f y),
    binaryOutcome_test_integral h hh.le hh1.le f]
  norm_num [binarySignLikelihood]
  have hm : 1-h ≠ 0 := ne_of_gt (by linarith)
  have hp : 1+h ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- Direct integration of the squared centered binary likelihood gives the
Rademacher chi-square value in the paper's one-row calculation. -/
-- @node: binaryOutcome_sign_chi_integral
lemma binaryOutcome_sign_chi_integral (h : ℝ) (hh : -1 < h) (hh1 : h < 1) :
    (∫ u, (binarySignLikelihood h (binaryOutcome (-h) u) - 1)^2
      ∂uniformRandomizer) = 4*h^2/(1-h^2) := by
  rw [binaryOutcome_test_integral (-h) (by linarith) (by linarith)
    (fun y => (binarySignLikelihood h y - 1)^2)]
  norm_num [binarySignLikelihood]
  have hm : 1-h ≠ 0 := ne_of_gt (by linarith)
  have hp : 1+h ≠ 0 := ne_of_gt (by linarith)
  have hd : 1-h^2 ≠ 0 := by
    have : 0 < (1-h)*(1+h) := mul_pos (by linarith) (by linarith)
    nlinarith
  field_simp
  ring

/-- In the half-mean window the one-channel information is at most eight times
its squared effect, as required before multiplying by the rare-event mass. -/
-- @node: binaryOutcome_sign_chi_bound
lemma binaryOutcome_sign_chi_bound (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) :
    (∫ u, (binarySignLikelihood h (binaryOutcome (-h) u) - 1)^2
      ∂uniformRandomizer) ≤ 8*h^2 := by
  rw [binaryOutcome_sign_chi_integral h (by linarith) (by linarith)]
  have hs : h^2 ≤ 1/4 := by nlinarith
  apply (div_le_iff₀ (by nlinarith : 0 < 1-h^2)).2
  nlinarith [sq_nonneg h]

/-- An independent binary channel contributes information only on its outer event,
so its squared likelihood deviation is multiplied by the event probability. -/
-- @node: binaryOutcome_rare_event_chi_integral
lemma binaryOutcome_rare_event_chi_integral {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (S : Set Ω) (hS : MeasurableSet S)
    (h : ℝ) (hh : -1 < h) (hh1 : h < 1) :
    (∫ z : Ω × ℝ, ((if z.1 ∈ S then
        binarySignLikelihood h (binaryOutcome (-h) z.2) else 1) - 1)^2
      ∂ν.prod uniformRandomizer) = ν.real S * (4*h^2/(1-h^2)) := by
  have := uniformRandomizer_probability
  calc
    _ = ∫ z : Ω × ℝ, S.indicator (fun _ => (1:ℝ)) z.1 *
        (binarySignLikelihood h (binaryOutcome (-h) z.2) - 1)^2
        ∂ν.prod uniformRandomizer := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      by_cases hz : z.1 ∈ S <;> simp [hz]
    _ = _ := by
      rw [integral_prod_mul (S.indicator (fun _ => (1:ℝ)))
        (fun u => (binarySignLikelihood h (binaryOutcome (-h) u) - 1)^2),
        binaryOutcome_sign_chi_integral h hh hh1,
        integral_indicator hS, setIntegral_const]
      simp

/-- The scarce block and weak treatment coin multiply their masses, giving the
one-row information integral before passing to the observable pushforward. -/
-- @node: blockChannel_chi_integral
lemma blockChannel_chi_integral (m q h : ℝ)
    (hm : 0 ≤ m) (hm1 : m ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hh : -1 < h) (hh1 : h < 1) :
    (∫ z : (ℝ × ℝ) × ℝ, ((if z.1.1 ≤ m ∧ z.1.2 ≤ q then
        binarySignLikelihood h (binaryOutcome (-h) z.2) else 1) - 1)^2
      ∂(uniformRandomizer.prod uniformRandomizer).prod uniformRandomizer) =
      m*q*(4*h^2/(1-h^2)) := by
  have := uniformRandomizer_probability
  calc
    _ = ∫ z : (ℝ × ℝ) × ℝ,
        ((if z.1.1 ≤ m then (1:ℝ) else 0) *
          (if z.1.2 ≤ q then (1:ℝ) else 0)) *
        (binarySignLikelihood h (binaryOutcome (-h) z.2) - 1)^2
        ∂(uniformRandomizer.prod uniformRandomizer).prod uniformRandomizer := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      by_cases hx : z.1.1 ≤ m <;> by_cases ha : z.1.2 ≤ q <;> simp [hx, ha]
    _ = _ := by
      rw [integral_prod_mul
        (fun v : ℝ × ℝ => (if v.1 ≤ m then (1:ℝ) else 0) *
          (if v.2 ≤ q then (1:ℝ) else 0))
        (fun u => (binarySignLikelihood h (binaryOutcome (-h) u) - 1)^2),
        integral_prod_mul (fun x => if x ≤ m then (1:ℝ) else 0)
          (fun u => if u ≤ q then (1:ℝ) else 0),
        uniformRandomizer_coin_integral m hm hm1,
        uniformRandomizer_coin_integral q hq hq1,
        binaryOutcome_sign_chi_integral h hh hh1]

/-- The three-coin information integral obeys the rare-block row budget. -/
-- @node: blockChannel_chi_bound
lemma blockChannel_chi_bound (m q h : ℝ)
    (hm : 0 ≤ m) (hm1 : m ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) :
    (∫ z : (ℝ × ℝ) × ℝ, ((if z.1.1 ≤ m ∧ z.1.2 ≤ q then
        binarySignLikelihood h (binaryOutcome (-h) z.2) else 1) - 1)^2
      ∂(uniformRandomizer.prod uniformRandomizer).prod uniformRandomizer) ≤
      8*m*q*h^2 := by
  rw [blockChannel_chi_integral m q h hm hm1 hq hq1 (by linarith) (by linarith)]
  have hb := binaryOutcome_sign_chi_bound h hh hh1
  rw [binaryOutcome_sign_chi_integral h (by linarith) (by linarith)] at hb
  calc
    _ ≤ m*q*(8*h^2) := mul_le_mul_of_nonneg_left hb (mul_nonneg hm hq)
    _ = _ := by ring

/-- The two coin regions have their explicit ENNReal masses. -/
-- @node: uniformRandomizer_coin_masses
lemma uniformRandomizer_coin_masses (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    uniformRandomizer (Set.Iic q) = ENNReal.ofReal q ∧
    uniformRandomizer (Set.Iic q)ᶜ = ENNReal.ofReal (1-q) := by
  constructor
  · rw [uniformRandomizer, Measure.restrict_apply measurableSet_Iic]
    have hs : Set.Iic q ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 q := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · tauto
      · intro hu
        exact ⟨hu.2, hu.1, hu.2.trans hq1⟩
    rw [hs, Real.volume_Icc, sub_zero]
  · rw [uniformRandomizer, Measure.restrict_apply measurableSet_Iic.compl]
    have hs : (Set.Iic q)ᶜ ∩ Set.Icc (0:ℝ) 1 = Set.Ioc q 1 := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Iic, Set.mem_Icc,
        Set.mem_Ioc, not_le]
      constructor
      · tauto
      · intro hu
        exact ⟨hu.1, hq.trans hu.1.le, hu.2⟩
    rw [hs, Real.volume_Ioc]

/-- Nonnegative tests of a binary channel have the same two-mass formula,
including unbounded tests; this identifies the channel as a measure. -/
-- @node: binaryOutcome_test_lintegral
lemma binaryOutcome_test_lintegral (μ : ℝ) (hμ : -1 ≤ μ) (hμ1 : μ ≤ 1)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ u, f (binaryOutcome μ u) ∂uniformRandomizer) =
      ENNReal.ofReal ((1+μ)/2) * f 1 + ENNReal.ofReal ((1-μ)/2) * f (-1) := by
  have hm := uniformRandomizer_coin_masses ((1+μ)/2) (by linarith) (by linarith)
  have heq : (fun u => f (binaryOutcome μ u)) =
      (Set.Iic ((1+μ)/2)).piecewise (fun _ => f 1) (fun _ => f (-1)) := by
    funext u
    by_cases hu : u ≤ (1+μ)/2 <;> simp [binaryOutcome, Set.piecewise, hu]
  rw [heq]
  rw [lintegral_piecewise measurableSet_Iic, setLIntegral_const, setLIntegral_const,
    hm.1, hm.2]
  have he : 1 - (1+μ)/2 = (1-μ)/2 := by ring
  rw [he]
  ac_rfl

/-- The observable binary outcome law is its explicit two-atom distribution. -/
-- @node: binaryOutcome_map_eq
lemma binaryOutcome_map_eq (μ : ℝ) (hμ : -1 ≤ μ) (hμ1 : μ ≤ 1) :
    uniformRandomizer.map (binaryOutcome μ) =
      ENNReal.ofReal ((1+μ)/2) • Measure.dirac 1 +
      ENNReal.ofReal ((1-μ)/2) • Measure.dirac (-1) := by
  have hb : Measurable (binaryOutcome μ) := by fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hb, binaryOutcome_test_lintegral μ hμ hμ1 f,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac' _ hf, lintegral_dirac' _ hf]
  rfl

/-- The sign likelihood is a positive bounded Borel density when both binary
outcome probabilities are positive. -/
-- @node: binarySignLikelihood_positive
lemma binarySignLikelihood_positive (h : ℝ) (hh : -1 < h) (hh1 : h < 1)
    (y : ℝ) : 0 < binarySignLikelihood h y := by
  unfold binarySignLikelihood
  split_ifs <;> exact div_pos (by linarith) (by linarith)

/-- The positive binary law is the negative law tilted by the explicit sign
likelihood, identifying the Radon–Nikodym density at the channel level. -/
-- @node: binaryOutcome_sign_withDensity
lemma binaryOutcome_sign_withDensity (h : ℝ) (hh : -1 < h) (hh1 : h < 1) :
    (uniformRandomizer.map (binaryOutcome (-h))).withDensity
      (fun y => ENNReal.ofReal (binarySignLikelihood h y)) =
      uniformRandomizer.map (binaryOutcome h) := by
  rw [binaryOutcome_map_eq (-h) (by linarith) (by linarith),
    binaryOutcome_map_eq h hh.le hh1.le, withDensity_add_measure,
    withDensity_smul_measure, withDensity_smul_measure,
    dirac_withDensity, dirac_withDensity, smul_smul, smul_smul]
  have hm : 1-h ≠ 0 := ne_of_gt (by linarith)
  have hp : 1+h ≠ 0 := ne_of_gt (by linarith)
  norm_num only [binarySignLikelihood, if_pos, if_neg, neg_ne_self.mpr (by norm_num : (1:ℝ) ≠ 0)]
  rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ (1 + -h)/2),
    ← ENNReal.ofReal_mul (by linarith : 0 ≤ (1 - -h)/2)]
  have ep : ((1 + -h)/2) * ((1+h)/(1-h)) = (1+h)/2 := by
    field_simp [hm, hp]
    <;> ring
  have en : ((1 - -h)/2) * ((1-h)/(1+h)) = (1-h)/2 := by
    field_simp [hm, hp]
    <;> ring
  rw [ep, en]

/-- The sign likelihood is a Borel step function of the binary observation. -/
@[fun_prop]
-- @node: binarySignLikelihood_measurable
lemma binarySignLikelihood_measurable (h : ℝ) : Measurable (binarySignLikelihood h) := by
  unfold binarySignLikelihood
  exact Measurable.ite (measurableSet_singleton (1:ℝ)) measurable_const measurable_const

/-- The sign-change density proves absolute continuity of the binary channel. -/
-- @node: binaryOutcome_sign_absolutelyContinuous
lemma binaryOutcome_sign_absolutelyContinuous (h : ℝ) (hh : -1 < h) (hh1 : h < 1) :
    uniformRandomizer.map (binaryOutcome h) ≪
      uniformRandomizer.map (binaryOutcome (-h)) := by
  rw [← binaryOutcome_sign_withDensity h hh hh1]
  exact withDensity_absolutelyContinuous _ _

/-- The real Radon–Nikodym derivative is the explicit binary sign likelihood. -/
-- @node: binaryOutcome_sign_rnDeriv
lemma binaryOutcome_sign_rnDeriv (h : ℝ) (hh : -1 < h) (hh1 : h < 1) :
    (fun y => ((uniformRandomizer.map (binaryOutcome h)).rnDeriv
      (uniformRandomizer.map (binaryOutcome (-h))) y).toReal) =ᵐ[
        uniformRandomizer.map (binaryOutcome (-h))] binarySignLikelihood h := by
  haveI := uniformRandomizer_probability
  have hb : Measurable (binaryOutcome (-h)) := by fun_prop
  haveI : IsProbabilityMeasure (uniformRandomizer.map (binaryOutcome (-h))) :=
    Measure.isProbabilityMeasure_map hb.aemeasurable
  have hd : Measurable (fun y => ENNReal.ofReal (binarySignLikelihood h y)) := by
    fun_prop
  have hr := Measure.rnDeriv_withDensity
    (uniformRandomizer.map (binaryOutcome (-h))) hd
  rw [binaryOutcome_sign_withDensity h hh hh1] at hr
  filter_upwards [hr] with y hy
  rw [hy, ENNReal.toReal_ofReal (binarySignLikelihood_positive h hh hh1 y).le]

/-- The channel's actual chi-square divergence equals the direct likelihood
calculation, rather than merely an integral of a candidate density. -/
-- @node: binaryOutcome_sign_chiSqDiv
lemma binaryOutcome_sign_chiSqDiv (h : ℝ) (hh : -1 < h) (hh1 : h < 1) :
    Causalean.Stat.chiSqDiv (uniformRandomizer.map (binaryOutcome h))
      (uniformRandomizer.map (binaryOutcome (-h))) = 4*h^2/(1-h^2) := by
  unfold Causalean.Stat.chiSqDiv
  calc
    _ = ∫ y, (binarySignLikelihood h y - 1)^2
        ∂uniformRandomizer.map (binaryOutcome (-h)) := by
      apply integral_congr_ae
      filter_upwards [binaryOutcome_sign_rnDeriv h hh hh1] with y hy
      rw [hy]
    _ = _ := by
      have hb : Measurable (binaryOutcome (-h)) := by fun_prop
      have hd : Measurable (fun y => (binarySignLikelihood h y - 1)^2) := by
        fun_prop
      rw [integral_map hb.aemeasurable hd.aestronglyMeasurable]
      exact binaryOutcome_sign_chi_integral h hh hh1

/-- The squared density deviation is integrable under the negative channel,
providing the regularity input for chi-square tensorization. -/
-- @node: binaryOutcome_sign_sq_integrable
lemma binaryOutcome_sign_sq_integrable (h : ℝ) (hh : -1 < h) (hh1 : h < 1) :
    Integrable (fun y => (((uniformRandomizer.map (binaryOutcome h)).rnDeriv
      (uniformRandomizer.map (binaryOutcome (-h))) y).toReal - 1)^2)
      (uniformRandomizer.map (binaryOutcome (-h))) := by
  have hb : Measurable (binaryOutcome (-h)) := by fun_prop
  have hd : Measurable (fun y => (binarySignLikelihood h y - 1)^2) := by fun_prop
  have hi : Integrable (fun y => (binarySignLikelihood h y - 1)^2)
      (uniformRandomizer.map (binaryOutcome (-h))) :=
    (integrable_map_measure hd.aestronglyMeasurable hb.aemeasurable).2
      (binaryOutcome_test_integrable (-h) (fun y => (binarySignLikelihood h y - 1)^2))
  apply hi.congr
  filter_upwards [binaryOutcome_sign_rnDeriv h hh hh1] with y hy
  rw [hy]

/-- The channel chi-square divergence has the paper's eight-times-effect bound. -/
-- @node: binaryOutcome_sign_chiSqDiv_bound
lemma binaryOutcome_sign_chiSqDiv_bound (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1/2) :
    Causalean.Stat.chiSqDiv (uniformRandomizer.map (binaryOutcome h))
      (uniformRandomizer.map (binaryOutcome (-h))) ≤ 8*h^2 := by
  rw [binaryOutcome_sign_chiSqDiv h (by linarith) (by linarith)]
  rw [← binaryOutcome_sign_chi_integral h (by linarith) (by linarith)]
  exact binaryOutcome_sign_chi_bound h hh hh1

/-- Nonnegative measurable channel tests also obey the exact likelihood change. -/
-- @node: binaryOutcome_sign_change_lintegral
lemma binaryOutcome_sign_change_lintegral (h : ℝ) (hh : -1 < h) (hh1 : h < 1)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u, ENNReal.ofReal (binarySignLikelihood h (binaryOutcome (-h) u)) *
      f (binaryOutcome (-h) u) ∂uniformRandomizer) =
    ∫⁻ u, f (binaryOutcome h u) ∂uniformRandomizer := by
  have hb : Measurable (binaryOutcome (-h)) := by fun_prop
  have hd : Measurable (fun y => ENNReal.ofReal (binarySignLikelihood h y)) := by
    fun_prop
  change (∫⁻ u, ((fun y => ENNReal.ofReal (binarySignLikelihood h y)) * f)
    (binaryOutcome (-h) u) ∂uniformRandomizer) = _
  rw [← lintegral_map (hd.mul hf) hb,
    ← lintegral_withDensity_eq_lintegral_mul _ hd hf,
    binaryOutcome_sign_withDensity h hh hh1]
  exact lintegral_map hf (by fun_prop)

/-- The four-coin observable map drops the unobserved potential outcomes. -/
-- @node: blockObservationMap
noncomputable def blockObservationMap (m q h : ℝ) (σ : Bool)
    (v : (((ℝ × ℝ) × ℝ) × ℝ)) : Observation :=
  ⟨v.1.1.1, decide (v.1.1.2 ≤ blockLogger m q v.1.1.1),
    if decide (v.1.1.2 ≤ blockLogger m q v.1.1.1) then
      binaryOutcome (blockMeanOne m h σ v.1.1.1) v.2
    else binaryOutcome (blockMeanZero m v.1.1.1) v.1.2⟩

/-- The observable map inherits measurability from the full-row construction. -/
@[fun_prop]
-- @node: blockObservationMap_measurable
lemma blockObservationMap_measurable (m q h : ℝ) (σ : Bool) :
    Measurable (blockObservationMap m q h σ) := by
  have hp : Measurable (fun o : FullRow => (⟨o.X, o.A, o.Y⟩ : Observation)) := by
    apply measurable_comap_iff.mpr
    have hc : Measurable (fun o : FullRow => (o.X, o.A, o.Y, o.Y0, o.Y1)) :=
      comap_measurable _
    exact hc.fst.prodMk (hc.snd.fst.prodMk hc.snd.snd.fst)
  exact hp.comp (blockFull_map_measurable m q h σ)

/-- The observable law is the pushforward of the four uniforms by the observable map. -/
-- @node: blockPair_obsLaw_map
lemma blockPair_obsLaw_map (m q h : ℝ) (σ : Bool) :
    (blockPair m q h σ).obsLaw = fourUniform.map (blockObservationMap m q h σ) := by
  have hp : Measurable (fun o : FullRow => (⟨o.X, o.A, o.Y⟩ : Observation)) := by
    apply measurable_comap_iff.mpr
    have hc : Measurable (fun o : FullRow => (o.X, o.A, o.Y, o.Y0, o.Y1)) :=
      comap_measurable _
    exact hc.fst.prodMk (hc.snd.fst.prodMk hc.snd.snd.fst)
  exact Measure.map_map hp (blockFull_map_measurable m q h σ)

/-- The observable likelihood changes only treated outcomes on the rare score block. -/
-- @node: blockObservationLikelihood
noncomputable def blockObservationLikelihood (m h : ℝ) (o : Observation) : ℝ :=
  if o.X ≤ m ∧ o.A = true then binarySignLikelihood h o.Y else 1

/-- The row likelihood is measurable in the observed coordinates. -/
@[fun_prop]
-- @node: blockObservationLikelihood_measurable
lemma blockObservationLikelihood_measurable (m h : ℝ) :
    Measurable (blockObservationLikelihood m h) := by
  have hc : Measurable (fun o : Observation => (o.X, o.A, o.Y)) :=
    comap_measurable _
  exact Measurable.ite
    ((measurableSet_le hc.fst measurable_const).inter
      (hc.snd.fst (measurableSet_singleton true)))
    ((binarySignLikelihood_measurable h).comp hc.snd.snd) measurable_const

/-- The row likelihood is strictly positive in the feasible effect window. -/
-- @node: blockObservationLikelihood_positive
lemma blockObservationLikelihood_positive (m h : ℝ) (hh : -1 < h) (hh1 : h < 1)
    (o : Observation) : 0 < blockObservationLikelihood m h o := by
  unfold blockObservationLikelihood
  split_ifs
  · exact binarySignLikelihood_positive h hh hh1 o.Y
  · norm_num

/-- Integrating the treated coin lifts the channel density to the entire observable law. -/
-- @node: blockPair_obsLaw_sign_withDensity
lemma blockPair_obsLaw_sign_withDensity (m q h : ℝ) (hh : -1 < h) (hh1 : h < 1) :
    (blockPair m q h false).obsLaw.withDensity
      (fun o => ENNReal.ofReal (blockObservationLikelihood m h o)) =
    (blockPair m q h true).obsLaw := by
  haveI := uniformRandomizer_probability
  apply Measure.ext_of_lintegral
  intro f hf
  have hd : Measurable (fun o => ENNReal.ofReal (blockObservationLikelihood m h o)) := by
    fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hf,
    blockPair_obsLaw_map, blockPair_obsLaw_map,
    lintegral_map (hd.mul hf) (blockObservationMap_measurable m q h false),
    lintegral_map hf (blockObservationMap_measurable m q h true)]
  simp only [Pi.mul_apply]
  unfold fourUniform
  rw [lintegral_prod (fun v => ENNReal.ofReal (blockObservationLikelihood m h
    (blockObservationMap m q h false v)) * f (blockObservationMap m q h false v))
    (((hd.mul hf).comp
    (blockObservationMap_measurable m q h false)).aemeasurable)]
  conv_rhs => rw [lintegral_prod (fun v => f (blockObservationMap m q h true v)) ((hf.comp
    (blockObservationMap_measurable m q h true)).aemeasurable)]
  apply lintegral_congr
  intro v
  by_cases hx : v.1.1 ≤ m
  · by_cases ha : v.1.2 ≤ q
    · simp only [Pi.mul_apply, blockObservationMap, blockObservationLikelihood,
        blockLogger, blockMeanOne, hx, ha, ↓reduceIte, decide_true, Bool.true_eq,
        and_self, blockMeanZero, Bool.false_eq_true, ite_false]
      apply binaryOutcome_sign_change_lintegral h hh hh1
        (fun y => f (⟨v.1.1, true, y⟩ : Observation))
      apply hf.comp
      apply measurable_comap_iff.mpr
      exact measurable_const.prodMk (measurable_const.prodMk measurable_id)
    · simp [Pi.mul_apply, blockObservationMap, blockObservationLikelihood,
        blockLogger, blockMeanOne, hx, ha]
  · simp [Pi.mul_apply, blockObservationMap, blockObservationLikelihood,
      blockLogger, blockMeanOne, hx]

end CausalSmith.Stat.ScorethresholdOverlapRegret
