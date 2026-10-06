module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RoleMeans
public import Causalean.Mathlib.MeasureTheory.SetIntegralRecovery

/-! Observed arm–covariate transport from the rectangle specification.
These identities connect the observable residual means to the uniform-design calculations
in equation (21), with all density regularity supplied by the observed-law structure. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Marginalizing the outcome in an observed rectangle leaves its arm propensity. -/
-- @node: observed_arm_covariate_mass
lemma observed_arm_covariate_mass (P : ObsLaw) (a : Bool)
    (B : Set ℝ) (hB : MeasurableSet B) :
    P.law.real {o | X o ∈ B ∧ A o = a} = ∫ x in B, pi P a x ∂unitVolume := by
  have h := P.rectangles B Set.univ hB MeasurableSet.univ a
  simp only [Set.mem_univ, and_true, Measure.restrict_univ] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hB).2 (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact fun _ => hx)] with x hx
  rw [P.eta_normalized a x hx, mul_one]
  rfl

/-- The supplied propensity version makes either arm probability measurable. -/
-- @node: measurable_pi_design
@[fun_prop] lemma measurable_pi_design (P : ObsLaw) (a : Bool) :
    Measurable (pi P a) := by
  cases a
  · change Measurable (fun x => 1 - P.e x)
    exact measurable_const.sub P.e_measurable
  · change Measurable P.e
    exact P.e_measurable

/-- Arm propensities are integrable under the uniform design without model overlap. -/
-- @node: integrable_pi_design
@[fun_prop] lemma integrable_pi_design (P : ObsLaw) (a : Bool) :
    Integrable (pi P a) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have he := P.e_range x hx
  cases a <;> simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte,
    Real.norm_eq_abs] <;> exact abs_le.mpr ⟨by linarith [he.1, he.2], by linarith [he.1, he.2]⟩

/-- Restricting to one arm and mapping the covariate gives the propensity-weighted design law. -/
-- @node: observed_arm_covariate_law
lemma observed_arm_covariate_law (P : ObsLaw) (a : Bool) :
    (P.law.restrict {o | A o = a}).map X =
      unitVolume.withDensity (fun x => ENNReal.ofReal (pi P a x)) := by
  apply Causalean.Mathlib.MeasureTheory.measure_eq_withDensity_of_toReal_setIntegral
    (integrable_pi_design P a)
  intro B hB
  rw [Measure.map_apply (show Measurable X from measurable_fst) hB,
    Measure.restrict_apply (hB.preimage (show Measurable X from measurable_fst))]
  change P.law.real {o | X o ∈ B ∧ A o = a} = _
  exact observed_arm_covariate_mass P a B hB

/-- Any measurable covariate statistic in one arm integrates against the propensity weight. -/
-- @node: integral_observed_arm_covariate
lemma integral_observed_arm_covariate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : ObsLaw) (a : Bool) (f : ℝ → E)
    (hf : Measurable f) :
    (∫ o in {o | A o = a}, f (X o) ∂P.law) =
      ∫ x, pi P a x • f x ∂unitVolume := by
  rw [← integral_map (show AEMeasurable X _ from measurable_fst.aemeasurable)
    hf.aestronglyMeasurable,
    observed_arm_covariate_law]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have he := P.e_range x hx
  have hp : 0 ≤ pi P a x := by
    cases a <;> simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte] <;>
      linarith [he.1, he.2]
  rw [ENNReal.toReal_ofReal hp]

/-- Inverse pilot propensities are globally bounded by four by clipping. -/
-- @node: pilotPi_inv_abs_le
lemma pilotPi_inv_abs_le {m : ℕ} (train : Fin m → Omega) (mx : ℕ)
    (a : Bool) (x : ℝ) : |(pilotPi train mx a x)⁻¹| ≤ 4 := by
  have h := pilotPi_mem_Icc train mx a x
  have hp : 0 < pilotPi train mx a x := by linarith [h.1]
  rw [abs_of_pos (inv_pos.mpr hp), ← one_div]
  apply (div_le_iff₀ hp).2
  linarith [h.1]

/-- Observable treatment residuals tested against bounded covariate functions have the
relative propensity-error design mean used in the independent role calculations. -/
-- @node: integral_Rres_covariate_test
lemma integral_Rres_covariate_test {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx : ℕ) (a : Bool) (f : ℝ → E)
    (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ o, Rres train mx a o • f (X o) ∂P.law) =
      ∫ x, uerr P train mx a x • f x ∂unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let g : ℝ → E := fun x => (pilotPi train mx a x)⁻¹ • f x
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hgC : ∀ x, ‖g x‖ ≤ 4 * C := by
    intro x
    dsimp only [g]
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (pilotPi_inv_abs_le train mx a x) (hC x) (norm_nonneg _)
      (by norm_num)
  have hX : Measurable X := measurable_fst
  have hA : MeasurableSet {o : Omega | A o = a} := by
    change MeasurableSet ((fun o : Omega => o.2.1) ⁻¹' {a})
    exact (measurableSet_singleton a).preimage (by fun_prop)
  have hgi : Integrable (fun o => g (X o)) P.law :=
    Integrable.of_bound (hg.comp hX).aestronglyMeasurable (4 * C)
      (Filter.Eventually.of_forall (fun o => hgC (X o)))
  have hfi : Integrable (fun o => f (X o)) P.law :=
    Integrable.of_bound (hf.comp hX).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun o => hC (X o)))
  have he (o : Omega) : Rres train mx a o • f (X o) =
      {o : Omega | A o = a}.indicator (fun o => g (X o)) o - f (X o) := by
    have hp : pilotPi train mx a (X o) ≠ 0 := by
      linarith [(pilotPi_mem_Icc train mx a (X o)).1]
    by_cases ha : A o = a
    · simp only [Rres, ha, ↓reduceIte, Set.indicator, Set.mem_ofPred_eq, g]
      rw [sub_div, div_self hp, div_eq_mul_inv, one_mul, sub_smul, one_smul]
    · simp only [Rres, ha, ↓reduceIte, Set.indicator, Set.mem_ofPred_eq, zero_sub, g]
      rw [neg_div, div_self hp, neg_smul, one_smul]
  simp_rw [he]
  rw [integral_sub (hgi.indicator hA) hfi, integral_indicator hA,
    integral_observed_arm_covariate P a g hg]
  have hdesign : (∫ o, f (X o) ∂P.law) = ∫ x, f x ∂unitVolume := by
    rw [← integral_map hX.aemeasurable hf.aestronglyMeasurable, hModel.design]
  rw [hdesign]
  have hpi : Integrable (fun x => pi P a x • g x) unitVolume := by
    -- Integrability transfers along the arm map and its recovered density law.
    have hgmap : Integrable g ((P.law.restrict {o | A o = a}).map X) :=
      (integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable).2
      hgi.integrableOn
    rw [observed_arm_covariate_law] at hgmap
    have hi := (integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))).1 hgmap
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have he0 := (P.e_range x hx).1
    have he1 := (P.e_range x hx).2
    have hp : 0 ≤ pi P a x := by
      cases a <;> simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte] <;>
        linarith [he0, he1]
    rw [ENNReal.toReal_ofReal hp]
  rw [← integral_sub hpi (Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC))]
  apply integral_congr_ae
  filter_upwards [] with x
  have hp : pilotPi train mx a x ≠ 0 := by
    linarith [(pilotPi_mem_Icc train mx a x).1]
  dsimp only [g]
  rw [smul_smul, uerr, sub_div, div_self hp, div_eq_mul_inv, sub_smul, one_smul]

/-- The observed treatment residual has its uniform-design relative-error mean. -/
-- @node: integral_Rres_eq_integral_uerr
lemma integral_Rres_eq_integral_uerr (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx : ℕ) (a : Bool) :
    (∫ o, Rres train mx a o ∂P.law) = ∫ x, uerr P train mx a x ∂unitVolume := by
  simpa only [smul_eq_mul, mul_one] using
    integral_Rres_covariate_test P hModel train mx a (fun _ => (1 : ℝ))
      measurable_const 1 (fun _ => by norm_num)

/-- Integrating the first observed kernel role gives the propensity-error correction-cell mean. -/
-- @node: integral_Rres_covariateKernel
lemma integral_Rres_covariateKernel (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx k : ℕ) (a : Bool) (z : ℝ) :
    (∫ o, Rres train mx a o * covariateKernel k (X o) z ∂P.law) =
      cellAverage k (uerr P train mx a) z := by
  have hm : Measurable (fun x => covariateKernel k x z) := by fun_prop
  have hb : ∀ x, ‖covariateKernel k x z‖ ≤ (k : ℝ) := by
    intro x
    unfold covariateKernel
    split_ifs <;> simp
  rw [show (∫ o, Rres train mx a o * covariateKernel k (X o) z ∂P.law) =
      ∫ x, uerr P train mx a x * covariateKernel k x z ∂unitVolume from
    integral_Rres_covariate_test P hModel train mx a _ hm k hb]
  unfold cellAverage
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [covariateKernel, smul_eq_mul]
  by_cases h : cell k x = cell k z
  · rw [if_pos h, if_pos h.symm, mul_comm]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero, zero_mul]

/-- Conditional outcome-bin probabilities are measurable functions of the covariate. -/
-- @node: measurable_eta_bin_probability
@[fun_prop] lemma measurable_eta_bin_probability (P : ObsLaw) (a : Bool) (D : Set ℝ) :
    Measurable (fun x => ∫ y in D, P.eta a x y ∂unitVolume) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  exact (P.eta_measurable a).stronglyMeasurable.integral_prod_right'.measurable

/-- Normalization bounds each conditional outcome-bin probability between zero and one. -/
-- @node: eta_bin_probability_mem_Icc
lemma eta_bin_probability_mem_Icc (P : ObsLaw) (a : Bool) (D : Set ℝ)
    (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    (∫ y in D, P.eta a x y ∂unitVolume) ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : ∀ᵐ y ∂unitVolume, 0 ≤ P.eta a x y := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact P.eta_nonneg a x y hx hy
  constructor
  · exact integral_nonneg_of_ae (ae_restrict_of_ae hn)
  · rw [← P.eta_normalized a x hx]
    exact setIntegral_le_integral (P.eta_integrable a x hx) hn

/-- The joint arm/outcome-bin weight is integrable under the uniform covariate law. -/
-- @node: integrable_pi_eta_bin_probability
lemma integrable_pi_eta_bin_probability (P : ObsLaw) (a : Bool) (D : Set ℝ) :
    Integrable (fun x => pi P a x * ∫ y in D, P.eta a x y ∂unitVolume)
      unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hd := eta_bin_probability_mem_Icc P a D x hx
  have he := P.e_range x hx
  have hp : pi P a x ∈ Set.Icc (0 : ℝ) 1 := by
    cases a <;> simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte,
      Set.mem_Icc] <;> constructor <;> linarith [he.1, he.2]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp.1 hd.1)]
  exact (mul_le_mul hp.2 hd.2 hd.1 (by norm_num)).trans_eq (by norm_num)

/-- Selecting one arm and an outcome bin and then mapping the covariate recovers the
propensity times conditional bin-probability density from the rectangle specification. -/
-- @node: observed_arm_outcome_bin_covariate_law
lemma observed_arm_outcome_bin_covariate_law (P : ObsLaw) (a : Bool)
    (D : Set ℝ) (hD : MeasurableSet D) :
    (P.law.restrict {o | A o = a ∧ Y o ∈ D}).map X =
      unitVolume.withDensity
        (fun x => ENNReal.ofReal (pi P a x * ∫ y in D, P.eta a x y ∂unitVolume)) := by
  apply Causalean.Mathlib.MeasureTheory.measure_eq_withDensity_of_toReal_setIntegral
    (integrable_pi_eta_bin_probability P a D)
  intro B hB
  rw [Measure.map_apply (show Measurable X from measurable_fst) hB,
    Measure.restrict_apply (hB.preimage (show Measurable X from measurable_fst))]
  change P.law.real {o | X o ∈ B ∧ (A o = a ∧ Y o ∈ D)} = _
  simpa only [and_assoc, pi] using P.rectangles B D hB hD a

/-- A measurable covariate test restricted to an arm and outcome bin transports to the
uniform design with its propensity and conditional-bin-probability weights. -/
-- @node: integral_observed_arm_outcome_bin_covariate
lemma integral_observed_arm_outcome_bin_covariate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : ObsLaw) (a : Bool) (D : Set ℝ)
    (hD : MeasurableSet D) (f : ℝ → E) (hf : Measurable f) :
    (∫ o in {o | A o = a ∧ Y o ∈ D}, f (X o) ∂P.law) =
      ∫ x, (pi P a x * ∫ y in D, P.eta a x y ∂unitVolume) • f x ∂unitVolume := by
  rw [← integral_map (show AEMeasurable X _ from measurable_fst.aemeasurable)
    hf.aestronglyMeasurable, observed_arm_outcome_bin_covariate_law P a D hD]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have he := P.e_range x hx
  have hp : 0 ≤ pi P a x := by
    cases a <;> simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte] <;>
      linarith [he.1, he.2]
  rw [ENNReal.toReal_ofReal (mul_nonneg hp (eta_bin_probability_mem_Icc P a D x hx).1)]

/-- Inverse-propensity-weighted outcome-bin tests have the relative propensity factor
required for the observable outcome representer mean. -/
-- @node: integral_observed_weighted_outcome_bin
lemma integral_observed_weighted_outcome_bin {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : ObsLaw) {m : ℕ} (train : Fin m → Omega)
    (mx : ℕ) (a : Bool) (D : Set ℝ) (hD : MeasurableSet D)
    (f : ℝ → E) (hf : Measurable f) :
    (∫ o in {o | A o = a ∧ Y o ∈ D},
      (pilotPi train mx a (X o))⁻¹ • f (X o) ∂P.law) =
      ∫ x, ((1 + uerr P train mx a x) *
        ∫ y in D, P.eta a x y ∂unitVolume) • f x ∂unitVolume := by
  rw [integral_observed_arm_outcome_bin_covariate P a D hD
    (fun x => (pilotPi train mx a x)⁻¹ • f x) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with x
  have hp : pilotPi train mx a x ≠ 0 := by
    linarith [(pilotPi_mem_Icc train mx a x).1]
  have hu : 1 + uerr P train mx a x = pi P a x / pilotPi train mx a x := by
    unfold uerr
    rw [sub_div, div_self hp]
    ring
  rw [smul_smul, hu, div_eq_mul_inv]
  congr 1
  ring

/-- Each observable inverse-weighted histogram coordinate has the conditional-density
coefficient mean required by the outcome-residual transport step. -/
-- @node: integral_observed_weighted_phi_coordinate
lemma integral_observed_weighted_phi_coordinate (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx J : ℕ) (a : Bool) (i : Fin J) :
    (∫ o in {o | A o = a},
      (pilotPi train mx a (X o))⁻¹ * phiCoefficients J (Y o) i ∂P.law) =
      ∫ x, (1 + uerr P train mx a x) * coefficients J (P.eta a x) i ∂unitVolume := by
  let D : Set ℝ := {y | cell J y = i.val + 1}
  have hD : MeasurableSet D :=
    (measurable_histogram_cell J) (measurableSet_singleton _)
  have hY : Measurable Y := measurable_snd.comp measurable_snd
  have heq : (fun o : Omega => (pilotPi train mx a (X o))⁻¹ *
      phiCoefficients J (Y o) i) =
      (Y ⁻¹' D).indicator (fun o => (pilotPi train mx a (X o))⁻¹ * Real.sqrt J) := by
    funext o
    by_cases hy : Y o ∈ D <;> simp [phiCoefficients, D, Set.indicator, hy] at *
  rw [heq, integral_indicator (hD.preimage hY)]
  have hset : Y ⁻¹' D ∩ {o : Omega | A o = a} = {o | A o = a ∧ Y o ∈ D} := by
    ext o
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    exact and_comm
  rw [Measure.restrict_restrict (hD.preimage hY), hset]
  rw [show (∫ o in {o | A o = a ∧ Y o ∈ D},
      (pilotPi train mx a (X o))⁻¹ * Real.sqrt J ∂P.law) =
      ∫ x, ((1 + uerr P train mx a x) *
        ∫ y in D, P.eta a x y ∂unitVolume) * Real.sqrt J ∂unitVolume from
    integral_observed_weighted_outcome_bin P train mx a D hD
      (fun _ => Real.sqrt J) measurable_const]
  apply integral_congr_ae
  filter_upwards [] with x
  have hbin : (∫ y in D, P.eta a x y ∂unitVolume) =
      ∫ y in histogramCell J (i.val + 1), P.eta a x y ∂unitVolume := by
    apply setIntegral_congr_set
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    apply propext
    change (cell J y = i.val + 1) ↔ (y ∈ Set.Icc 0 1 ∧ cell J y = i.val + 1)
    simp only [hy, true_and]
  rw [hbin]
  change _ = (1 + uerr P train mx a x) *
    (Real.sqrt J * ∫ y in histogramCell J (i.val + 1), P.eta a x y ∂unitVolume)
  ring

/-- The inverse-weighted conditional-density coefficient vector is integrable by
normalization and the clipped propensity bound. -/
-- @node: integrable_weighted_eta_coefficients_design
lemma integrable_weighted_eta_coefficients_design (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx J : ℕ) (a : Bool) :
    Integrable (fun x => (1 + uerr P train mx a x) • coefficients J (P.eta a x))
      unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_eval_piLp
  intro i
  have hu (x : ℝ) : 1 + uerr P train mx a x =
      pi P a x * (pilotPi train mx a x)⁻¹ := by
    have hp : pilotPi train mx a x ≠ 0 := by
      linarith [(pilotPi_mem_Icc train mx a x).1]
    unfold uerr
    field_simp
    ring
  simp only [PiLp.smul_apply, smul_eq_mul, hu]
  change Integrable (fun x => (pi P a x * (pilotPi train mx a x)⁻¹) *
    (Real.sqrt J * ∫ y in histogramCell J (i.val + 1), P.eta a x y ∂unitVolume)) _
  apply Integrable.of_bound (by fun_prop) (4 * Real.sqrt J)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hb := eta_bin_probability_mem_Icc P a (histogramCell J (i.val + 1)) x hx
  have he := P.e_range x hx
  have hp : |pi P a x| ≤ 1 := by
    cases a <;> simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte] <;>
      exact abs_le.mpr ⟨by linarith [he.1, he.2], by linarith [he.1, he.2]⟩
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hb.1]
  calc
    _ ≤ (1 * 4) * (Real.sqrt J * 1) :=
      mul_le_mul (mul_le_mul hp (pilotPi_inv_abs_le train mx a x) (abs_nonneg _)
        (by norm_num)) (mul_le_mul_of_nonneg_left hb.2 (Real.sqrt_nonneg _))
        (mul_nonneg (Real.sqrt_nonneg _) hb.1) (by norm_num)
    _ = _ := by ring

/-- Coordinate transport assembles the observable inverse-weighted outcome
representer mean into its conditional-density coefficient vector. -/
-- @node: integral_observed_weighted_phi_vector
lemma integral_observed_weighted_phi_vector (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx J : ℕ) (a : Bool) :
    (∫ o in {o | A o = a},
      (pilotPi train mx a (X o))⁻¹ • phiCoefficients J (Y o) ∂P.law) =
      ∫ x, (1 + uerr P train mx a x) • coefficients J (P.eta a x) ∂unitVolume := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  have hi : Integrable (fun o : Omega =>
      (pilotPi train mx a (X o))⁻¹ • phiCoefficients J (Y o)) P.law := by
    apply integrable_of_measurable_finite_range _ _ (by unfold X Y; fun_prop)
    exact chain_finite_range_binary
      (chain_finite_range_comp (chain_finite_range_precomp
        (finite_range_pilotPi train mx a) X) (g := fun r : ℝ => r⁻¹))
      (chain_finite_range_precomp (finite_range_phiCoefficients J) Y) (· • ·)
  have hj := integrable_weighted_eta_coefficients_design P train mx J a
  ext i
  rw [eval_integral_piLp (fun j => hi.integrableOn.eval_piLp j),
    eval_integral_piLp (fun j => hj.eval_piLp j)]
  simpa only [PiLp.smul_apply, smul_eq_mul] using
    integral_observed_weighted_phi_coordinate P train mx J a i

/-- The observable outcome residual has the uniform-design weighted density-error
mean in equation (21), with regularity supplied by clipping and normalization. -/
-- @node: integral_Vres_eq_integral_verr_coefficients
lemma integral_Vres_eq_integral_verr_coefficients (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my J : ℕ) (a : Bool) :
    (∫ o, Vres train mx my J a o ∂P.law) =
      ∫ x, coefficients J (verr P train mx my a x) ∂unitVolume := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let S : Set Omega := {o | A o = a}
  have hS : MeasurableSet S := by
    exact (measurableSet_singleton a).preimage (show Measurable A by unfold A; fun_prop)
  let f : Omega → Hj J := fun o =>
    (pilotPi train mx a (X o))⁻¹ • phiCoefficients J (Y o)
  let g : ℝ → Hj J := fun x =>
    (pilotPi train mx a x)⁻¹ • pilotCoefficients train mx my J a x
  have hgf : (Set.range g).Finite :=
    chain_finite_range_binary
      (chain_finite_range_comp (finite_range_pilotPi train mx a)
        (g := fun r : ℝ => r⁻¹))
      (finite_range_pilotCoefficients train mx my J a) (· • ·)
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hgi : Integrable (fun o => g (X o)) P.law :=
    integrable_of_measurable_finite_range _ _ (hgm.comp measurable_fst)
      (chain_finite_range_precomp hgf X)
  have hfi : Integrable f P.law := by
    apply integrable_of_measurable_finite_range _ _ (by dsimp [f]; unfold X Y; fun_prop)
    exact chain_finite_range_binary
      (chain_finite_range_comp (chain_finite_range_precomp
        (finite_range_pilotPi train mx a) X) (g := fun r : ℝ => r⁻¹))
      (chain_finite_range_precomp (finite_range_phiCoefficients J) Y) (· • ·)
  have he : Vres train mx my J a = S.indicator f -
      S.indicator (fun o => g (X o)) := by
    funext o
    by_cases ha : A o = a <;>
      simp [Vres, S, Set.indicator, ha, f, g, smul_sub, one_div]
  rw [he]
  simp only [Pi.sub_apply]
  rw [integral_sub (hfi.indicator hS) (hgi.indicator hS),
    integral_indicator hS, integral_indicator hS,
    integral_observed_weighted_phi_vector P train mx J a,
    integral_observed_arm_covariate P a g hgm]
  obtain ⟨C, hC⟩ := hgf.isBounded.exists_norm_le
  have hpi : Integrable (fun x => pi P a x • g x) unitVolume := by
    apply Integrable.of_bound (by fun_prop) C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have heRange := P.e_range x hx
    have hp : |pi P a x| ≤ 1 := by
      cases a <;> simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte] <;>
        exact abs_le.mpr ⟨by linarith [heRange.1, heRange.2], by linarith [heRange.1, heRange.2]⟩
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
      (by simpa using hC (g x) ⟨x, rfl⟩)
  rw [← integral_sub (integrable_weighted_eta_coefficients_design P train mx J a) hpi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hp : pilotPi train mx a x ≠ 0 := by
    linarith [(pilotPi_mem_Icc train mx a x).1]
  have hu : 1 + uerr P train mx a x = pi P a x * (pilotPi train mx a x)⁻¹ := by
    unfold uerr
    field_simp
    ring
  change _ = coefficients J (fun y => (1 + uerr P train mx a x) *
    (P.eta a x y - densityPilot train mx my a x y))
  rw [coefficients_const_mul_sub J _ _ _ (P.eta_integrable a x hx)
    (densityPilot_integrable train mx my a x), smul_sub]
  dsimp [g, pilotCoefficients]
  rw [smul_smul, hu]

/-- Positive-size first-role averages have the exact projected density-error mean. -/
-- @node: integral_Uone_eq_integral_verr_coefficients
lemma integral_Uone_eq_integral_verr_coefficients (P : ObsLaw) {m : ℕ} (hm : 0 < m)
    (train : Fin m → Omega) (mx my J : ℕ) (b : Fin 2) (a : Bool) :
    (∫ eval, Uone train mx my J eval b a ∂evalLaw P m) =
      ∫ x, coefficients J (verr P train mx my a x) ∂unitVolume := by
  rw [integral_Uone_eq_integral_Vres P hm train mx my J b a,
    integral_Vres_eq_integral_verr_coefficients]

end CausalSmith.Stat.DensityEffectRoughNull
