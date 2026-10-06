module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ObservableOdds
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.TwoPointLength
public import Causalean.Stat.Minimax.ChiSquared
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Constant-logit Bernoulli comparison experiment

The null has four equiprobable labels; the alternative changes only the treated
outcome risk. Both retain the public uniform covariate design and zero nuisance
logits, as in the parametric-floor proof roadmap.
-/
@[expose] public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Constant conditional cells with fair treatment and control outcome. -/
-- @node: parametricCells
def parametricCells (t : ℝ) (a y : Bool) (_x : Covariate) : ℝ :=
  (1/2) * (if y then logistic (if a then t else 0) else 1-logistic (if a then t else 0))

/-- All four cells are continuous, interior, and normalized for every effect. [the stated conclusion](goal) holds. -/
-- @node: parametricCells_valid
lemma parametricCells_valid (t : ℝ) : ValidCells (parametricCells t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a y
    unfold parametricCells
    fun_prop
  · intro a y x
    have hp := Real.sigmoid_pos (if a then t else 0)
    have hq := Real.sigmoid_lt_one (if a then t else 0)
    cases y <;> simp only [parametricCells, Bool.false_eq_true, ↓reduceIte, logistic]
    all_goals constructor <;> linarith
  · intro x
    simp only [Fintype.sum_bool, parametricCells, Bool.false_eq_true, ↓reduceIte]
    ring

/-- The actual observed-law carrier of the constant-nuisance subexperiment. -/
-- @node: parametricLaw
def parametricLaw (t : ℝ) : ObservedLaw := lawFromCells (parametricCells t) (parametricCells_valid t)

/-- The comparison laws retain the uniform design. [the stated conclusion](goal) holds. -/
-- @node: parametricLaw_uniform
lemma parametricLaw_uniform (t : ℝ) : UniformDesign (parametricLaw t) :=
  jointLaw_uniform _ (parametricCells_valid t)

/-- The conditional treatment probability is exactly one half. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: parametricLaw_propensity
lemma parametricLaw_propensity (t : ℝ) (x : Covariate) : propensity (parametricLaw t) x = 1/2 := by
  simp only [propensity, parametricLaw, lawFromCells, parametricCells, Bool.false_eq_true, ↓reduceIte]
  ring

/-- [Conditional outcome risks are the prescribed Bernoulli probabilities.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: parametricLaw_armRisk
lemma parametricLaw_armRisk (t : ℝ) (a : Bool) (x : Covariate) :
    armRisk (parametricLaw t) a x = logistic (if a then t else 0) := by
  simp only [armRisk, parametricLaw, lawFromCells, parametricCells, Bool.false_eq_true, ↓reduceIte]
  have hd : (1/2 : ℝ)*(1-logistic (if a then t else 0)) +
      (1/2)*logistic (if a then t else 0) = 1/2 := by ring
  rw [hd]
  ring

/-- [Both native nuisance logits vanish, and the homogeneous effect is t. [the stated conclusion](goal) holds. -/
-- @node: parametricLaw_logits
lemma parametricLaw_logits (t : ℝ) :
    (∀ x, propensityLogit (parametricLaw t) x = 0) ∧
    (∀ x, prognosisLogit (parametricLaw t) x = 0) ∧ effect (parametricLaw t) = t := by
  have hg (x : Covariate) : propensityLogit (parametricLaw t) x = 0 := by
    rw [propensityLogit, parametricLaw_propensity]
    norm_num [logit]
  have hv (x : Covariate) : prognosisLogit (parametricLaw t) x = 0 := by
    rw [prognosisLogit, parametricLaw_armRisk]
    simpa using logit_logistic 0
  refine ⟨hg, hv, ?_⟩
  rw [effect, parametricLaw_armRisk, hv, sub_zero]
  exact logit_logistic t

/-- Constant zero nuisance logits satisfy every Hölder radius. [the stated conclusion](goal) holds. -/
-- @node: holderSeminorm_zero
lemma holderSeminorm_zero (γ : ℝ) : holderSeminorm γ (fun _ => 0) = 0 := by
  simp [holderSeminorm]

/-- Legal model membership follows from the effect envelope alone. Under the stated assumptions. [The stated hypotheses](hyp:ht) hold, and [the stated conclusion follows](goal). -/
-- @node: parametricLaw_model
lemma parametricLaw_model (α β t : ℝ) (ht : |t| ≤ 1/2) : Model α β (parametricLaw t) := by
  obtain ⟨hg, hv, he⟩ := parametricLaw_logits t
  refine ⟨parametricLaw_uniform t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [parametricLaw_armRisk, hv, he, zero_add, ↓reduceIte]
  · simpa only [EffectEnvelope, he] using ht
  · intro x
    rw [hg]
    norm_num
  · intro x
    rw [hv]
    norm_num
  · change holderSeminorm α (propensityLogit (parametricLaw t)) ≤ 2
    rw [show propensityLogit (parametricLaw t) = (fun _ => 0) from funext hg, holderSeminorm_zero]
    norm_num
  · change holderSeminorm β (prognosisLogit (parametricLaw t)) ≤ 2
    rw [show prognosisLogit (parametricLaw t) = (fun _ => 0) from funext hv, holderSeminorm_zero]
    norm_num

/-- [The null is legal in every nonnegative radius slice, including radius zero.](goal) Under [the stated assumptions](hyp:hr). -/
-- @node: parametricLaw_null_radius
lemma parametricLaw_null_radius (α β r : ℝ) (hr : 0 ≤ r) : RadiusModel α β r (parametricLaw 0) := by
  refine ⟨parametricLaw_model α β 0 (by norm_num), ?_⟩
  rw [EvaluationRadius, (parametricLaw_logits 0).2.2]
  simpa using hr

/-- [The one-record likelihood ratio relative to the four-label fair null. -/
-- @node: parametricDensity
def parametricDensity (t : ℝ) (o : Record) : ℝ := 4 * parametricCells t o.2.1 o.2.2 o.1

/-- The likelihood ratio is continuous, since it depends only on discrete labels. [the stated conclusion](goal) holds. -/
-- @node: parametricDensity_continuous
lemma parametricDensity_continuous (t : ℝ) : Continuous (parametricDensity t) := by
  change Continuous ((fun b : Bool × Bool =>
    4 * ((1/2) * (if b.2 then logistic (if b.1 then t else 0)
      else 1-logistic (if b.1 then t else 0)))) ∘ Prod.snd)
  exact continuous_of_discreteTopology.comp continuous_snd

/-- The density is nonnegative at every record. [the stated conclusion](goal) holds. -/
-- @node: parametricDensity_nonneg
lemma parametricDensity_nonneg (t : ℝ) (o : Record) : 0 ≤ parametricDensity t o := by
  exact mul_nonneg (by norm_num) ((parametricCells_valid t).2.1 _ _ _).1.le

/-- Direct finite cell summation identifies the likelihood ratio, without an abstract model gate. [the stated conclusion](goal) holds. -/
-- @node: parametricLaw_withDensity
lemma parametricLaw_withDensity (t : ℝ) :
    (parametricLaw t).measure = (parametricLaw 0).measure.withDensity
      (fun o => ENNReal.ofReal (parametricDensity t o)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hd := (parametricDensity_continuous t).measurable.ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hf]
  change (∫⁻ o, f o ∂jointLaw uniformLaw (parametricLaw t).cells) =
    ∫⁻ o, ENNReal.ofReal (parametricDensity t o) * f o
      ∂jointLaw uniformLaw (parametricLaw 0).cells
  rw [lintegral_jointLaw_cells (parametricLaw t) f hf,
    lintegral_jointLaw_cells (parametricLaw 0)
      (fun o => ENNReal.ofReal (parametricDensity t o) * f o) (hd.mul hf)]
  apply lintegral_congr
  intro x
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro y hy
  have hnull : (parametricLaw 0).cells a y x = 1/4 := by
    cases a <;> cases y <;> norm_num [parametricLaw, lawFromCells, parametricCells, logistic, Real.sigmoid_zero]
  have hp : 0 ≤ parametricCells t a y x := ((parametricCells_valid t).2.1 a y x).1.le
  rw [hnull]
  change ENNReal.ofReal (parametricCells t a y x) * f (x,a,y) =
    ENNReal.ofReal (1/4) * (ENNReal.ofReal (4 * parametricCells t a y x) * f (x,a,y))
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/4)]
  congr 2
  ring

/-- The real Radon--Nikodym derivative is the explicit bounded label density. [the stated conclusion](goal) holds. -/
-- @node: parametricLaw_rnDeriv
lemma parametricLaw_rnDeriv (t : ℝ) :
    (fun o => (((parametricLaw t).measure.rnDeriv (parametricLaw 0).measure) o).toReal)
      =ᵐ[(parametricLaw 0).measure] parametricDensity t := by
  have h := Measure.rnDeriv_withDensity (parametricLaw 0).measure
    (parametricDensity_continuous t).measurable.ennreal_ofReal
  rw [← parametricLaw_withDensity] at h
  filter_upwards [h] with o ho
  rw [ho, ENNReal.toReal_ofReal (parametricDensity_nonneg t o)]

/-- The squared likelihood deviation is integrable on the actual null law. [the stated conclusion](goal) holds. -/
-- @node: parametricLaw_density_integrable
lemma parametricLaw_density_integrable (t : ℝ) :
    Integrable (fun o => ((((parametricLaw t).measure.rnDeriv
      (parametricLaw 0).measure) o).toReal-1)^2) (parametricLaw 0).measure := by
  have hc : Continuous (fun o => (parametricDensity t o-1)^2) :=
    ((parametricDensity_continuous t).sub continuous_const).pow 2
  have hi : Integrable (fun o => (parametricDensity t o-1)^2) (parametricLaw 0).measure :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply hi.congr
  filter_upwards [parametricLaw_rnDeriv t] with o ho
  rw [ho]

/-- Direct summation gives the exact one-record chi-square value. [the stated conclusion](goal) holds. -/
-- @node: parametricLaw_chiSq
lemma parametricLaw_chiSq (t : ℝ) :
    Causalean.Stat.chiSqDiv (parametricLaw t).measure (parametricLaw 0).measure =
      2*(logistic t-1/2)^2 := by
  unfold Causalean.Stat.chiSqDiv
  rw [integral_congr_ae (show
    (fun o => ((((parametricLaw t).measure.rnDeriv (parametricLaw 0).measure) o).toReal-1)^2)
      =ᵐ[(parametricLaw 0).measure] (fun o => (parametricDensity t o-1)^2) from
        (parametricLaw_rnDeriv t).fun_comp (fun z => (z-1)^2))]
  have hc : Continuous (fun o => (parametricDensity t o-1)^2) :=
    ((parametricDensity_continuous t).sub continuous_const).pow 2
  rw [integral_observed_cells _ (parametricLaw_uniform 0) _ hc]
  norm_num [Fintype.sum_bool, parametricLaw, lawFromCells, parametricDensity,
    parametricCells, logistic, Real.sigmoid_zero]
  ring

/-- The sigmoid derivative is bounded by a quarter on the whole real line. [the stated conclusion](goal) holds. -/
-- @node: logistic_quarter_bound
lemma logistic_quarter_bound (t : ℝ) : |logistic t-1/2| ≤ |t|/4 := by
  have hderiv (x : ℝ) : ‖deriv Real.sigmoid x‖ ≤ (1/4 : ℝ) := by
    rw [Real.deriv_sigmoid, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sigmoid_pos x).le (by linarith [Real.sigmoid_lt_one x]))]
    nlinarith [sq_nonneg (Real.sigmoid x-1/2)]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (f := Real.sigmoid)
    (fun x _ => (Real.hasDerivAt_sigmoid x).differentiableAt)
    (fun x _ => hderiv x) (convex_univ) (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  simpa [logistic, Real.sigmoid_zero, Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using h

/-- The roadmap's one-record information bound follows from the derivative estimate. [the stated conclusion](goal) holds. -/
-- @node: parametricLaw_chiSq_le
lemma parametricLaw_chiSq_le (t : ℝ) :
    Causalean.Stat.chiSqDiv (parametricLaw t).measure (parametricLaw 0).measure ≤ t^2/8 := by
  rw [parametricLaw_chiSq]
  have h := logistic_quarter_bound t
  have hs : |logistic t-1/2|^2 ≤ (|t|/4)^2 :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 h
  rw [sq_abs] at hs
  nlinarith [sq_abs t]

/-- The public root-n scalar effect used in the two-point comparison. -/
-- @node: parametricAmplitude
def parametricAmplitude (n : ℕ) : ℝ := (1/4)*(n : ℝ)^(-(1/2 : ℝ))

/-- The comparison effect lies in the model envelope at every positive sample size. Under the stated assumptions. [The stated hypotheses](hyp:hn) hold, and [the stated conclusion follows](goal). -/
-- @node: parametricAmplitude_bounds
lemma parametricAmplitude_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ parametricAmplitude n ∧ parametricAmplitude n ≤ 1/4 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨by unfold parametricAmplitude; positivity, ?_⟩
  unfold parametricAmplitude
  have hpow : (n : ℝ)^(-(1/2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn' (by norm_num)
  linarith

/-- [The effect and sample-size factors cancel in the information budget.](goal) Under [the stated assumptions](hyp:hn). -/
-- @node: parametricAmplitude_budget
lemma parametricAmplitude_budget (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (parametricAmplitude n)^2/8 = 1/128 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : ((n : ℝ)^(-(1/2 : ℝ)))^2 = (n : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le]
    norm_num [Real.rpow_neg_one]
  unfold parametricAmplitude
  rw [mul_pow, hp]
  field_simp
  <;> ring

/-- [The iid original-record laws have total variation at most one twentieth.](goal) Under [the stated assumptions](hyp:hn). -/
-- @node: parametricLaw_iid_tv
lemma parametricLaw_iid_tv (n : ℕ) (hn : 1 ≤ n) :
    Causalean.Stat.tvDist
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (parametricLaw 0).measure n)
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (parametricLaw (parametricAmplitude n)).measure n)
      ≤ 1/20 := by
  let t := parametricAmplitude n
  let μ := (parametricLaw t).measure
  let ν := (parametricLaw 0).measure
  have hac : μ ≪ ν := by
    dsimp only [μ, ν]
    rw [parametricLaw_withDensity]
    exact withDensity_absolutelyContinuous _ _
  have hint := parametricLaw_density_integrable t
  have hbudget : (n : ℝ)*Causalean.Stat.chiSqDiv μ ν ≤ 1/128 := by
    have h := mul_le_mul_of_nonneg_left (parametricLaw_chiSq_le t) (by positivity : (0 : ℝ) ≤ n)
    dsimp only [μ, ν, t] at *
    nlinarith [parametricAmplitude_budget n hn]
  have hpowexp : (1+Causalean.Stat.chiSqDiv μ ν)^n ≤
      Real.exp ((n : ℝ)*Causalean.Stat.chiSqDiv μ ν) := by
    calc
      _ ≤ (Real.exp (Causalean.Stat.chiSqDiv μ ν))^n :=
        pow_le_pow_left₀ (by linarith [Causalean.Stat.chiSqDiv_nonneg (μ := μ) (ν := ν)])
          (by simpa [add_comm] using Real.add_one_le_exp (Causalean.Stat.chiSqDiv μ ν)) n
      _ = _ := by rw [← Real.exp_nat_mul]
  have hexp : Real.exp ((n : ℝ)*Causalean.Stat.chiSqDiv μ ν) ≤ 128/127 := by
    calc
      _ ≤ Real.exp (1/128 : ℝ) := Real.exp_le_exp.mpr hbudget
      _ ≤ 1/(1-(1/128 : ℝ)) :=
        Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have htensor := Causalean.Stat.one_add_chiSqDiv_pi_iid_general μ ν hac hint n
  have hchi : Causalean.Stat.chiSqDiv (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun _ : Fin n => ν)) ≤ 1/127 := by
    rw [← htensor] at hpowexp
    linarith [hpowexp.trans hexp]
  have htv := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv
    (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => ν))
    (Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous μ ν hac n)
    (Causalean.Stat.pi_iid_integrable_sq_dev μ ν hac hint n)
  have hsqrt : Real.sqrt (1/127 : ℝ) ≤ 1/10 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num
  rw [Causalean.Stat.tvDist_symm]
  change Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => μ))
    (Measure.pi (fun _ : Fin n => ν)) ≤ 1/20
  calc
    _ ≤ (1/2)*Real.sqrt (Causalean.Stat.chiSqDiv
      (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => ν))) := htv
    _ ≤ (1/2)*Real.sqrt (1/127 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hchi) (by norm_num)
    _ ≤ 1/20 := by linarith

/-- [Tensoring the same independent uniform seed preserves the testing comparison.](goal) Under [the stated assumptions](hyp:hn). -/
-- @node: parametricLaw_experiment_tv
lemma parametricLaw_experiment_tv (n : ℕ) (hn : 1 ≤ n) :
    Causalean.Stat.tvDist (experimentLaw (parametricLaw 0) n)
      (experimentLaw (parametricLaw (parametricAmplitude n)) n) ≤ 1/20 := by
  unfold experimentLaw Causalean.Stat.UStatistic.LocalizedVariance.iidLaw
  rw [← Measure.compProd_const, ← Measure.compProd_const,
    Causalean.Stat.tvDist_compProd_eq]
  exact parametricLaw_iid_tv n hn

/-- [Two concrete legal laws discharge the full parametric comparison obligation.](goal) Under [the stated assumptions](hyp:hn,hr). -/
-- @node: parametric_comparison
lemma parametric_comparison (α β r : ℝ) (n : ℕ) (hn : 1 ≤ n) (hr : 0 ≤ r) :
    ∃ P₀ P₁ : ObservedLaw,
      RadiusModel α β r P₀ ∧ Model α β P₁ ∧ effect P₀ = 0 ∧
      effect P₁ = (1/4 : ℝ)*(n : ℝ)^(-(1/2 : ℝ)) ∧
      Causalean.Stat.tvDist (experimentLaw P₀ n) (experimentLaw P₁ n) ≤ 1/20 := by
  refine ⟨parametricLaw 0, parametricLaw (parametricAmplitude n),
    parametricLaw_null_radius α β r hr, ?_, (parametricLaw_logits 0).2.2,
    (parametricLaw_logits _).2.2, parametricLaw_experiment_tv n hn⟩
  apply parametricLaw_model
  obtain ⟨hpos, hle⟩ := parametricAmplitude_bounds n hn
  rw [abs_of_nonneg hpos]
  linarith
end CausalSmith.Stat.LogoddsLowsmoothFrontier
