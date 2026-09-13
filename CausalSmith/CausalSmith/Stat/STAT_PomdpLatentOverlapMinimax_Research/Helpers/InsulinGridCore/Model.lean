import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FiniteEncoding
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.Kernels
import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Basic
import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Operations
import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Exponential
import Causalean.Mathlib.Probability.StdNormalCDF
import Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.Main

set_option linter.style.longLine false

/-! # Refreshed finite insulin-policy application -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure

/-- The five-point glucose grid decoded from the observed-state index. -/
noncomputable def glucoseGridValue (x : Fin 90) : ℝ :=
  match x.val / 18 with
  | 0 => 50 | 1 => 100 | 2 => 150 | 3 => 200 | _ => 250

/-- The four bounded reward values used by the application. -/
noncomputable def insulinRewardValue (r : Fin 4) : ℝ :=
  match r.val with
  | 0 => -1 | 1 => -(2 / 3) | 2 => -(1 / 3) | _ => 0

/-- The normalized Gaussian distribution function used in rounded transitions. -/
noncomputable def gaussianCDF (z : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x in Set.Iic z, Real.exp (-(x ^ 2) / 2)

/-- Behavior-policy action weight: insulin is injected with probability `3/10`. -/
noncomputable def insulinBehaviourWeight (a : Bool) : ℝ := if a then 3 / 10 else 7 / 10

/-- Target-policy action weight: inject exactly at glucose at least 125. -/
noncomputable def insulinTargetWeight (x : Fin 90) (a : Bool) : ℝ :=
  if a = decide (125 ≤ glucoseGridValue x) then 1 else 0

/-- Decode one activity category as the stated levels `0`, `31`, and `850`. -/
noncomputable def insulinActivityValue (i : Nat) : ℝ :=
  if i = 0 then 0 else if i = 1 then 31 else 850

/-- The autoregressive glucose mean decoded from the finite memory state. -/
noncomputable def insulinMean (s : JointState 90 4) (a : Bool) : ℝ :=
  10 + 0.9 * glucoseGridValue s.1 + 0.1 * (if s.2.val / 2 = 0 then 0 else 78) +
    0.1 * (if s.2.val % 2 = 0 then 0 else 78) -
    0.01 * insulinActivityValue (s.1.val / 6 % 3) -
    0.01 * insulinActivityValue (s.1.val / 2 % 3) -
    2 * (if a then 1 else 0) - 4 * (s.1.val % 2 : Nat)

/-- Gaussian rounded-grid mass for the next observed glucose cell. -/
noncomputable def roundedGlucoseWeight (s : JointState 90 4) (a : Bool) (x' : Fin 90) : ℝ :=
  let i := x'.val / 18
  if i = 0 then gaussianCDF ((75 - insulinMean s a) / 5)
  else if i = 4 then 1 - gaussianCDF ((225 - insulinMean s a) / 5)
  else gaussianCDF ((75 + 50 * i - insulinMean s a) / 5) -
    gaussianCDF ((75 + 50 * (i - 1) - insulinMean s a) / 5)

/-- Non-refresh transition weight, including memory shifts and exogenous diet/activity draws. -/
noncomputable def insulinDynamicWeight (s : JointState 90 4) (a : Bool)
    (s' : JointState 90 4) : ℝ :=
  roundedGlucoseWeight s a s'.1 *
    (if s'.2.val / 2 = 0 then 4 / 5 else 1 / 5) *
    (if s'.1.val / 6 % 3 = 0 then 2 / 5
      else if s'.1.val / 6 % 3 = 1 then 2 / 5 else 1 / 5) *
    (if s'.2.val % 2 = s.2.val / 2 then 1 else 0) *
    (if s'.1.val / 2 % 3 = s.1.val / 6 % 3 then 1 else 0) *
    (if decide (s'.1.val % 2 = 1) = a then 1 else 0)

/-- Refreshed state transition weight: half uniform, half dynamic. -/
noncomputable def insulinStateWeight (s : JointState 90 4) (a : Bool)
    (s' : JointState 90 4) : ℝ :=
  1 / 720 + (1 / 2) * insulinDynamicWeight s a s'

/-- Deterministic reward symbol selected from the current glucose cell. -/
noncomputable def insulinRewardSymbol (x : Fin 90) : Fin 4 :=
  if glucoseGridValue x ≤ 70 then 0
  else if 150 < glucoseGridValue x then 1
  else if glucoseGridValue x ≤ 80 ∨ (120 < glucoseGridValue x ∧ glucoseGridValue x ≤ 150)
    then 2 else 3

/-- The finite 360-state refreshed insulin model. -/
noncomputable def insulinGridFinite (T : Nat) : FiniteRewardModel T 90 4 4 :=
  let K : JointState 90 4 → Bool → PMF (Fin 4 × JointState 90 4) :=
    fun s a ↦ pmfOfRealWeight fun p ↦
      (if p.1 = insulinRewardSymbol s.1 then 1 else 0) * insulinStateWeight s a p.2
  let init : PMF (JointState 90 4) := pmfOfRealWeight fun _ ↦ 1 / 360
  let b : Fin 90 → PMF Bool := fun _ ↦
    @pmfOfRealWeight Bool inferInstance inferInstance insulinBehaviourWeight
  let e : Fin 90 → PMF Bool := fun x ↦
    @pmfOfRealWeight Bool inferInstance inferInstance (insulinTargetWeight x)
  { kernel := K
    rew := insulinRewardValue
    rew_mem := by
      intro r
      fin_cases r <;> norm_num [insulinRewardValue]
    init := init
    b := b
    e := e
    law := finitePathPMF K init b
    law_generated := finitePathPMF_apply K init b }

-- @env: S4
variable (T : Nat)

-- @node: def:insulin-grid
/-- The refreshed finite insulin model embedded into the real-reward POMDP world. -/
noncomputable def insulinGrid (T : Nat) : RawPomdpExperiment T 90 4 :=
  embed (insulinGridFinite T)
  -- @realizes \(\mathcal I_{\mathrm{grid}}\)(360-state refreshed insulin POMDP)

/-- The stationary immediate-weighting bias in the insulin witness. -/
noncomputable def immediateWeightBias (T : Nat) : ℝ :=
  (∑ s, stationaryLaw (policyKernel (insulinGrid T) (insulinGrid T).b) s *
    ∑ a : Bool, (insulinGrid T).b s.1 a * ratio (insulinGrid T).b (insulinGrid T).e s.1 a *
      ∫ p, p.1 ∂((insulinGrid T).K s a)) - targetValue (insulinGrid T)
  -- @realizes \(\Delta_{\mathrm{imm}}\)(immediate-weighting stationary bias)

/-- [the gaussian CDF eq std Normal CDF assertion holds](goal). -/
lemma gaussianCDF_eq_stdNormalCDF (z : ℝ) :
    gaussianCDF z = Causalean.Mathlib.stdNormalCDF z := by
  rw [Causalean.Mathlib.stdNormalCDF, ProbabilityTheory.cdf_eq_real,
    MeasureTheory.measureReal_def]
  rw [ProbabilityTheory.gaussianReal_apply_eq_integral 0 (by norm_num) (Set.Iic z)]
  rw [ENNReal.toReal_ofReal]
  · unfold gaussianCDF ProbabilityTheory.gaussianPDFReal
    simp only [NNReal.coe_one, sub_zero, one_mul]
    rw [MeasureTheory.integral_const_mul]
    norm_num
  · exact integral_nonneg fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x

/-- [the gaussian CDF nonneg assertion holds](goal). -/
lemma gaussianCDF_nonneg (z : ℝ) : 0 ≤ gaussianCDF z := by
  rw [gaussianCDF_eq_stdNormalCDF]
  exact Causalean.Mathlib.stdNormalCDF_nonneg z

/-- [the gaussian CDF le one assertion holds](goal). -/
lemma gaussianCDF_le_one (z : ℝ) : gaussianCDF z ≤ 1 := by
  rw [gaussianCDF_eq_stdNormalCDF]
  exact Causalean.Mathlib.stdNormalCDF_le_one z

/-- [the gaussian CDF monotone assertion holds](goal). -/
lemma gaussianCDF_monotone : Monotone gaussianCDF := by
  intro x y hxy
  rw [gaussianCDF_eq_stdNormalCDF, gaussianCDF_eq_stdNormalCDF]
  exact Causalean.Mathlib.stdNormalCDF_monotone hxy

/-- [this defines the insulin Bool Equiv Fin object](goal). [defining clause 1](step:1); and [defining clause 2](step:2); and [defining clause 3](step:3); and [defining clause 4](step:4). -/
def insulinBoolEquivFin : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := i = 1
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- [this defines the insulin Obs Equiv object](goal). -/
noncomputable def insulinObsEquiv :
    Fin 5 × (Fin 3 × (Fin 3 × Bool)) ≃ Fin 90 :=
  ((Equiv.refl (Fin 5)).prodCongr
      ((Equiv.refl (Fin 3)).prodCongr
        ((Equiv.refl (Fin 3)).prodCongr insulinBoolEquivFin))).trans
    (((Equiv.refl (Fin 5)).prodCongr
      ((Equiv.refl (Fin 3)).prodCongr (@finProdFinEquiv 3 2))).trans
    (((Equiv.refl (Fin 5)).prodCongr (@finProdFinEquiv 3 6)).trans
      (@finProdFinEquiv 5 18)))

/-- [this defines the insulin Latent Equiv object](goal). -/
noncomputable def insulinLatentEquiv : Fin 2 × Fin 2 ≃ Fin 4 :=
  finProdFinEquiv

/-- [the insulin Obs Equiv val assertion holds](goal). -/
@[simp] lemma insulinObsEquiv_val (g : Fin 5) (u v : Fin 3) (a : Bool) :
    (insulinObsEquiv (g, (u, (v, a)))).val =
      g.val * 18 + u.val * 6 + v.val * 2 + Bool.toNat a := by
  cases a <;> simp [insulinObsEquiv, finProdFinEquiv, insulinBoolEquivFin] <;> ring

/-- [the insulin Latent Equiv val assertion holds](goal). -/
@[simp] lemma insulinLatentEquiv_val (d₀ d₁ : Fin 2) :
    (insulinLatentEquiv (d₀, d₁)).val = d₀.val * 2 + d₁.val := by
  simp [insulinLatentEquiv, finProdFinEquiv] <;> ring

/-- [the rounded Glucose Weight encode assertion holds](goal). -/
lemma roundedGlucoseWeight_encode (s : JointState 90 4) (a : Bool)
    (g : Fin 5) (u v : Fin 3) (a' : Bool) :
    roundedGlucoseWeight s a (insulinObsEquiv (g, (u, (v, a')))) =
      roundedGlucoseWeight s a (insulinObsEquiv (g, (0, (0, false)))) := by
  unfold roundedGlucoseWeight
  simp only [insulinObsEquiv_val]
  have hg (u : Fin 3) (v : Fin 3) (a' : Bool) :
      (g.val * 18 + u.val * 6 + v.val * 2 + Bool.toNat a') / 18 = g.val := by
    cases a' <;> simp [Bool.toNat] <;> omega
  rw [hg, hg]

/-- [the insulin Dynamic Weight encode assertion holds](goal). -/
lemma insulinDynamicWeight_encode (s : JointState 90 4) (a : Bool)
    (g : Fin 5) (u v : Fin 3) (a' : Bool) (d₀ d₁ : Fin 2) :
    insulinDynamicWeight s a
        (insulinObsEquiv (g, (u, (v, a'))), insulinLatentEquiv (d₀, d₁)) =
      roundedGlucoseWeight s a (insulinObsEquiv (g, (0, (0, false)))) *
        (if d₀.val = 0 then 4 / 5 else 1 / 5) *
        (if u.val = 0 then 2 / 5 else if u.val = 1 then 2 / 5 else 1 / 5) *
        (if d₁.val = s.2.val / 2 then 1 else 0) *
        (if v.val = s.1.val / 6 % 3 then 1 else 0) *
        (if a' = a then 1 else 0) := by
  rw [insulinDynamicWeight, roundedGlucoseWeight_encode]
  simp only [insulinObsEquiv_val, insulinLatentEquiv_val]
  have hd₀ : (d₀.val * 2 + d₁.val) / 2 = d₀.val := by omega
  have hd₁ : (d₀.val * 2 + d₁.val) % 2 = d₁.val := by omega
  have hu : (g.val * 18 + u.val * 6 + v.val * 2 + Bool.toNat a') / 6 % 3 =
      u.val := by cases a' <;> simp [Bool.toNat] <;> omega
  have hv : (g.val * 18 + u.val * 6 + v.val * 2 + Bool.toNat a') / 2 % 3 =
      v.val := by cases a' <;> simp [Bool.toNat] <;> omega
  have ha : decide
      ((g.val * 18 + u.val * 6 + v.val * 2 + Bool.toNat a') % 2 = 1) = a' := by
    cases a' <;> simp [Bool.toNat] <;> omega
  rw [hd₀, hd₁, hu, hv, ha]

/-- [the sum rounded Glucose Weight assertion holds](goal). -/
lemma sum_roundedGlucoseWeight (s : JointState 90 4) (a : Bool) :
    ∑ g : Fin 5, roundedGlucoseWeight s a
      (insulinObsEquiv (g, (0, (0, false)))) = 1 := by
  simp [roundedGlucoseWeight, insulinObsEquiv_val, Fin.sum_univ_succ]
  ring_nf

/-- [the sum insulin Dynamic Weight fiber assertion holds](goal). -/
lemma sum_insulinDynamicWeight_fiber (s : JointState 90 4) (a : Bool)
    (g : Fin 5) :
    ∑ u : Fin 3, ∑ v : Fin 3, ∑ a' : Bool, ∑ d₀ : Fin 2, ∑ d₁ : Fin 2,
      insulinDynamicWeight s a
        (insulinObsEquiv (g, (u, (v, a'))), insulinLatentEquiv (d₀, d₁)) =
      roundedGlucoseWeight s a (insulinObsEquiv (g, (0, (0, false)))) := by
  simp_rw [insulinDynamicWeight_encode]
  simp [Fin.sum_univ_succ]
  split_ifs <;> try omega
  all_goals ring

/-- [the sum insulin Dynamic Weight assertion holds](goal). -/
lemma sum_insulinDynamicWeight (s : JointState 90 4) (a : Bool) :
    ∑ s' : JointState 90 4, insulinDynamicWeight s a s' = 1 := by
  rw [Fintype.sum_prod_type]
  calc
    ∑ x : Fin 90, ∑ h : Fin 4, insulinDynamicWeight s a (x, h) =
        ∑ z : Fin 5 × (Fin 3 × (Fin 3 × Bool)), ∑ h : Fin 4,
          insulinDynamicWeight s a (insulinObsEquiv z, h) := by
      symm
      exact Fintype.sum_equiv insulinObsEquiv _ _ (fun _ ↦ rfl)
    _ = ∑ z : Fin 5 × (Fin 3 × (Fin 3 × Bool)), ∑ d : Fin 2 × Fin 2,
          insulinDynamicWeight s a (insulinObsEquiv z, insulinLatentEquiv d) := by
      apply Finset.sum_congr rfl
      intro z _
      symm
      exact Fintype.sum_equiv insulinLatentEquiv _ _ (fun _ ↦ rfl)
    _ = 1 := by
      simp_rw [Fintype.sum_prod_type]
      simp_rw [sum_insulinDynamicWeight_fiber]
      exact sum_roundedGlucoseWeight s a

/-- [the rounded Glucose Weight nonneg assertion holds](goal). -/
lemma roundedGlucoseWeight_nonneg (s : JointState 90 4) (a : Bool) (x : Fin 90) :
    0 ≤ roundedGlucoseWeight s a x := by
  obtain ⟨z, rfl⟩ := insulinObsEquiv.surjective x
  rcases z with ⟨g, u, v, a'⟩
  rw [roundedGlucoseWeight_encode]
  fin_cases g
  · simpa [roundedGlucoseWeight, insulinObsEquiv_val] using
      gaussianCDF_nonneg ((75 - insulinMean s a) / 5)
  · simp only [roundedGlucoseWeight, insulinObsEquiv_val]
    exact sub_nonneg.mpr (gaussianCDF_monotone (by linarith))
  · simp only [roundedGlucoseWeight, insulinObsEquiv_val]
    exact sub_nonneg.mpr (gaussianCDF_monotone (by linarith))
  · simp only [roundedGlucoseWeight, insulinObsEquiv_val]
    exact sub_nonneg.mpr (gaussianCDF_monotone (by linarith))
  · simpa [roundedGlucoseWeight, insulinObsEquiv_val] using
      sub_nonneg.mpr (gaussianCDF_le_one ((225 - insulinMean s a) / 5))

/-- [the insulin Dynamic Weight nonneg assertion holds](goal). -/
lemma insulinDynamicWeight_nonneg (s : JointState 90 4) (a : Bool)
    (s' : JointState 90 4) : 0 ≤ insulinDynamicWeight s a s' := by
  unfold insulinDynamicWeight
  have := roundedGlucoseWeight_nonneg s a s'.1
  positivity

/-- [the insulin State Weight nonneg assertion holds](goal). -/
lemma insulinStateWeight_nonneg (s : JointState 90 4) (a : Bool)
    (s' : JointState 90 4) : 0 ≤ insulinStateWeight s a s' := by
  unfold insulinStateWeight
  have := insulinDynamicWeight_nonneg s a s'
  positivity

/-- [the sum insulin State Weight assertion holds](goal). -/
lemma sum_insulinStateWeight (s : JointState 90 4) (a : Bool) :
    ∑ s' : JointState 90 4, insulinStateWeight s a s' = 1 := by
  simp_rw [insulinStateWeight, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_insulinDynamicWeight]
  norm_num [Fintype.card_prod]

/-- [the insulin Kernel Weight nonneg assertion holds](goal). -/
lemma insulinKernelWeight_nonneg (s : JointState 90 4) (a : Bool)
    (p : Fin 4 × JointState 90 4) :
    0 ≤ (if p.1 = insulinRewardSymbol s.1 then 1 else 0) *
      insulinStateWeight s a p.2 := by
  have := insulinStateWeight_nonneg s a p.2
  positivity

/-- [the sum insulin Kernel Weight assertion holds](goal). -/
lemma sum_insulinKernelWeight (s : JointState 90 4) (a : Bool) :
    ∑ p : Fin 4 × JointState 90 4,
      (if p.1 = insulinRewardSymbol s.1 then 1 else 0) *
        insulinStateWeight s a p.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp
  exact sum_insulinStateWeight s a

/-- [the insulin Kernel state Marginal assertion holds](goal). -/
lemma insulinKernel_stateMarginal (T : Nat) (s : JointState 90 4) (a : Bool)
    (s' : JointState 90 4) :
    ∑ r : Fin 4, ((insulinGridFinite T).kernel s a (r, s')).toReal =
      insulinStateWeight s a s' := by
  change ∑ r : Fin 4, (pmfOfRealWeight (fun p : Fin 4 × JointState 90 4 ↦
    (if p.1 = insulinRewardSymbol s.1 then 1 else 0) *
      insulinStateWeight s a p.2) (r, s')).toReal = _
  simp_rw [pmfOfRealWeight_apply_of_nonneg_sum_one _
    (insulinKernelWeight_nonneg s a) (sum_insulinKernelWeight s a)]
  have hto (r : Fin 4) :
      (ENNReal.ofReal ((if r = insulinRewardSymbol s.1 then 1 else 0) *
        insulinStateWeight s a s')).toReal =
        (if r = insulinRewardSymbol s.1 then 1 else 0) * insulinStateWeight s a s' :=
    ENNReal.toReal_ofReal (insulinKernelWeight_nonneg s a (r, s'))
  simp_rw [hto]
  simp

/-- [the insulin Kernel state Marginal' assertion holds](goal). -/
lemma insulinKernel_stateMarginal' (T : Nat) (s : JointState 90 4) (a : Bool)
    (s' : JointState 90 4) :
    (∑ r : Fin 4, (insulinGridFinite T).kernel s a (r, s')).toReal =
      insulinStateWeight s a s' := by
  rw [ENNReal.toReal_sum]
  · exact insulinKernel_stateMarginal T s a s'
  · intro r _
    exact PMF.apply_ne_top ((insulinGridFinite T).kernel s a) (r, s')

/-- [the insulin Finite Policy Kernel eq assertion holds](goal). -/
lemma insulinFinitePolicyKernel_eq (T : Nat) (p : Fin 90 → PMF Bool) :
    finitePolicyKernel (insulinGridFinite T) p = fun s s' ↦
      1 / 720 + (1 / 2) * ∑ a : Bool, (p s.1 a).toReal * insulinDynamicWeight s a s' := by
  funext s s'
  unfold finitePolicyKernel
  simp_rw [insulinKernel_stateMarginal', insulinStateWeight, mul_add,
    Finset.sum_add_distrib]
  rw [← Finset.sum_mul, sum_pmf_toReal_eq_one]
  simp only [one_mul]
  rw [Finset.mul_sum]
  apply congrArg (fun z ↦ 1 / 720 + z)
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- [the insulin Residual probability Vector assertion holds](goal). -/
lemma insulinResidual_probabilityVector (p : Fin 90 → PMF Bool)
    (s : JointState 90 4) :
    ProbabilityVector (fun s' ↦ ∑ a : Bool,
      (p s.1 a).toReal * insulinDynamicWeight s a s') := by
  constructor
  · intro s'
    exact Finset.sum_nonneg fun a _ ↦
      mul_nonneg ENNReal.toReal_nonneg (insulinDynamicWeight_nonneg s a s')
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_insulinDynamicWeight, mul_one]
    exact sum_pmf_toReal_eq_one _

/-- [the insulin Policy contraction assertion holds](goal). -/
lemma insulinPolicy_contraction (T : Nat) (p : Fin 90 → PMF Bool) :
    ∀ nu nu', ProbabilityVector nu → ProbabilityVector nu' →
      tvNorm (applyKernel nu (finitePolicyKernel (insulinGridFinite T) p) -
        applyKernel nu' (finitePolicyKernel (insulinGridFinite T) p)) ≤
        (1 / 2) * tvNorm (nu - nu') := by
  rw [insulinFinitePolicyKernel_eq]
  convert tvNorm_contraction_of_refresh (1 / 2) (by norm_num)
    (fun _ : JointState 90 4 ↦ (1 / 360 : ℝ))
    (fun s s' ↦ ∑ a : Bool,
      (p s.1 a).toReal * insulinDynamicWeight s a s')
    (insulinResidual_probabilityVector p) using 1 <;> norm_num

/-- The application has exactly 360 joint states. [the stated conclusion](goal). -/
lemma insulinGrid_card : Fintype.card (JointState 90 4) = 360 := by
  norm_num [Fintype.card_prod]

/-- Both induced kernels have Dobrushin contraction coefficient at most one half. [the stated conclusion](goal). -/
lemma insulinGrid_contraction (T : Nat) :
    UniformContraction (1 / 2) (insulinGrid T) := by
  intro p hp nu nu' hnu hnu'
  rcases hp with rfl | rfl
  · rw [show policyKernel (insulinGrid T) (insulinGrid T).b =
        finitePolicyKernel (insulinGridFinite T) (insulinGridFinite T).b by
      exact embed_policyKernel_eq _ _]
    exact insulinPolicy_contraction T _ nu nu' hnu hnu'
  · rw [show policyKernel (insulinGrid T) (insulinGrid T).e =
        finitePolicyKernel (insulinGridFinite T) (insulinGridFinite T).e by
      exact embed_policyKernel_eq _ _]
    exact insulinPolicy_contraction T _ nu nu' hnu hnu'

/-- The target-to-behavior action ratio is at most `10/3`. [the stated conclusion](goal). -/
lemma insulinGrid_policyOverlap (T : Nat) :
    PolicyOverlap (10 / 3) (insulinGrid T) := by
  have hb (a : Bool) :
      ((@pmfOfRealWeight Bool inferInstance inferInstance insulinBehaviourWeight) a).toReal =
        if a then 3 / 10 else 7 / 10 := by
    have hsum : ∑' a : Bool, ENNReal.ofReal (insulinBehaviourWeight a) = 1 := by
      rw [tsum_bool]
      simp only [insulinBehaviourWeight, Bool.false_eq_true, ↓reduceIte]
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 7 / 10)
        (by norm_num : (0 : ℝ) ≤ 3 / 10)]
      norm_num
    rw [pmfOfRealWeight, dif_neg (by rw [hsum]; norm_num), PMF.normalize_apply, hsum]
    cases a <;> norm_num [insulinBehaviourWeight]
  unfold PolicyOverlap PolicyVector
  constructor
  · intro x
    constructor
    · intro a
      exact ENNReal.toReal_nonneg
    · change ∑ a : Bool, ((insulinGridFinite T).e x a).toReal = 1
      have hsum : ∑ a : Bool, (insulinGridFinite T).e x a = 1 := by
        simpa only [tsum_fintype] using ((insulinGridFinite T).e x).tsum_coe
      rw [← ENNReal.toReal_sum
        (fun a _ ↦ ((insulinGridFinite T).e x).apply_ne_top a), hsum]
      simp
  · intro x a
    simp only [insulinGrid, embed]
    have hbval : (((insulinGridFinite T).b x) a).toReal =
        if a then 3 / 10 else 7 / 10 := by
      unfold insulinGridFinite
      exact hb a
    rw [hbval]
    have he_le : (((insulinGridFinite T).e x) a).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top
        (((insulinGridFinite T).e x).coe_le_one a)
    cases a <;> norm_num at hb ⊢ <;> linarith

/-- [the insulin Policy Kernel minoration assertion holds](goal). -/
lemma insulinPolicyKernel_minoration (T : Nat) (p : Fin 90 → PMF Bool)
    (s s' : JointState 90 4) :
    1 / 720 ≤ finitePolicyKernel (insulinGridFinite T) p s s' := by
  rw [insulinFinitePolicyKernel_eq]
  apply le_add_of_nonneg_right
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ ↦
    mul_nonneg ENNReal.toReal_nonneg (insulinDynamicWeight_nonneg s a s'))

/-- [the insulin Embedded Init probability Vector assertion holds](goal). -/
lemma insulinEmbeddedInit_probabilityVector (T : Nat) :
    ProbabilityVector (insulinGrid T).init := by
  constructor
  · intro s
    exact ENNReal.toReal_nonneg
  · change ∑ s : JointState 90 4, ((insulinGridFinite T).init s).toReal = 1
    exact sum_pmf_toReal_eq_one _

/-- Assuming [the hp condition](hyp:hp), [the hc condition](hyp:hc), [the insulin Stationary Law is Stationary assertion holds](goal). -/
lemma insulinStationaryLaw_isStationary (T : Nat) (p : Policy 90)
    (hp : PolicyVector p)
    (hc : ∀ nu nu', ProbabilityVector nu → ProbabilityVector nu' →
      tvNorm (applyKernel nu (policyKernel (insulinGrid T) p) -
        applyKernel nu' (policyKernel (insulinGrid T) p)) ≤
        (1 / 2) * tvNorm (nu - nu')) :
    IsStationary (policyKernel (insulinGrid T) p)
      (stationaryLaw (policyKernel (insulinGrid T) p)) := by
  apply stationaryLaw_isStationary_of_exists
  apply exists_stationary_of_contraction
    (P := policyKernel (insulinGrid T) p)
    (p0 := (insulinGrid T).init) (alpha := (1 / 2 : ℝ))
  · exact policyKernel_probabilityVector _ (embed_pomdpKernelLaw _) p hp
  · exact insulinEmbeddedInit_probabilityVector T
  · norm_num
  · norm_num
  · exact hc

/-- Assuming [the hd condition](hyp:hd), [the hminor condition](hyp:hminor), [the stationary ge minorization assertion holds](goal). -/
lemma stationary_ge_minorization {S : Type*} [Fintype S]
    (P : S → S → ℝ) (d : S → ℝ) (c : ℝ)
    (hd : IsStationary P d) (hminor : ∀ s s', c ≤ P s s') (s' : S) :
    c ≤ d s' := by
  rw [← hd.2 s', ← mul_one c, ← hd.1.2, Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ ↦
    by simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hminor s s') (hd.1.1 s)

/-- Assuming [the hd condition](hyp:hd), [the probability Vector le one assertion holds](goal). -/
lemma probabilityVector_le_one {S : Type*} [Fintype S]
    (d : S → ℝ) (hd : ProbabilityVector d) (s : S) : d s ≤ 1 := by
  rw [← hd.2]
  exact Finset.single_le_sum (fun i _ ↦ hd.1 i) (Finset.mem_univ s)

/-- The target stationary law is pointwise at most 720 times the behavior law. [the stated conclusion](goal). -/
lemma insulinGrid_stationaryOverlap (T : Nat) :
    LatentStationaryOverlap 720 (insulinGrid T) := by
  constructor
  · norm_num
  · intro s'
    have hbv : PolicyVector (insulinGrid T).b :=
      (embed_sequentialIgnorability (insulinGridFinite T)).1
    have hev : PolicyVector (insulinGrid T).e := (insulinGrid_policyOverlap T).1
    have hcb := insulinGrid_contraction T (insulinGrid T).b (Or.inl rfl)
    have hce := insulinGrid_contraction T (insulinGrid T).e (Or.inr rfl)
    have hb := insulinStationaryLaw_isStationary T _ hbv hcb
    have he := insulinStationaryLaw_isStationary T _ hev hce
    have hbmin : (1 / 720 : ℝ) ≤
        stationaryLaw (policyKernel (insulinGrid T) (insulinGrid T).b) s' := by
      apply stationary_ge_minorization _ _ (1 / 720) hb
      intro s z
      rw [show policyKernel (insulinGrid T) (insulinGrid T).b =
          finitePolicyKernel (insulinGridFinite T) (insulinGridFinite T).b by
        exact embed_policyKernel_eq _ _]
      exact insulinPolicyKernel_minoration T _ s z
    have heone : stationaryLaw
        (policyKernel (insulinGrid T) (insulinGrid T).e) s' ≤ 1 :=
      probabilityVector_le_one _ he.1 s'
    nlinarith

end CausalSmith.Stat.PomdpLatentOverlapMinimax
