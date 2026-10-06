module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.LowerBanditKernel

/-! # Finite observed law of the contextual bandit

The singleton hidden coordinate and independent uniform redraw identify a full
path with its observed word and its final context. Marginalizing that last
context gives the independent observation weights used in equation (44).
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- A fully observed finite path contains only one extra terminal context. -/
-- @node: lowerBanditPathEquiv
def lowerBanditPathEquiv (T d : Nat) :
    FiniteTrajectory T d 1 2 ≃ FiniteObsView T d 2 × Fin d where
  toFun tau := (finObsProj tau, (tau.1 (Fin.last T)).1)
  invFun w := (Fin.lastCases (w.2, 0) (fun t ↦ ((w.1 t).1, 0)),
    fun t ↦ (w.1 t).2)
  left_inv tau := by
    apply Prod.ext
    · funext t
      refine Fin.lastCases ?_ (fun i ↦ ?_) t
      · simp; exact Prod.ext rfl (Subsingleton.elim _ _)
      · simp [finObsProj]; exact Prod.ext rfl (Subsingleton.elim _ _)
    · rfl
  right_inv w := by
    apply Prod.ext
    · funext t; simp [finObsProj]
    · simp

/-- One observed-symbol weight is the uniform context, fair action, and reward. -/
-- @node: lowerBanditSymbolWeight
noncomputable def lowerBanditSymbolWeight {d : Nat} (word : Fin d → Bool)
    (gamma : ℝ) (w : Fin d × Bool × Fin 2) : ℝ :=
  (d : ℝ)⁻¹ * (1 / 2) * lowerBanditRewardWeight gamma (word w.1) w.2.1 w.2.2

/-- The actual full path factors into the observed weights and final context. For
[the time horizon](hyp:T), [the code dimension](hyp:d), [the code dimension assumption](hyp:hd),
[the word](hyp:word), [the target](hyp:target), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the g0 assumption](hyp:hg0), [the g1 assumption](hyp:hg1), and
[the tau](hyp:tau), this establishes [the lower bandit path factorization result](goal). -/
-- @node: lower_bandit_path_factorization
lemma lower_bandit_path_factorization {T d : Nat} (hd : 0 < d)
    (word target : Fin d → Bool) (gamma eta : ℝ) (hg0 : 0 ≤ gamma)
    (hg1 : gamma ≤ 1 / 16) (tau : FiniteTrajectory T d 1 2) :
    ((lowerBanditFinite hd word target gamma eta).law tau).toReal =
      (d : ℝ)⁻¹ * ∏ t : Fin T,
        lowerBanditSymbolWeight word gamma (finObsProj tau t) := by
  rw [(lowerBanditFinite hd word target gamma eta).law_generated,
    ENNReal.toReal_mul, ENNReal.toReal_prod]
  have hi : ((lowerBanditFinite (T := T) hd word target gamma eta).init
      (tau.1 0)).toReal = (d : ℝ)⁻¹ := by
    letI : NeZero d := ⟨hd.ne'⟩
    change (pmfOfRealWeight (lowerBanditStateWeight d) _).toReal = _
    rw [pmfOfRealWeight_apply_of_nonneg_sum_one _
      (lower_bandit_state_probability hd).1 (lower_bandit_state_probability hd).2,
      ENNReal.toReal_ofReal ((lower_bandit_state_probability hd).1 _)]
    rfl
  rw [hi]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  rw [ENNReal.toReal_mul]
  change (pmfOfRealWeight (fun _ : Bool ↦ (1 / 2 : ℝ)) _).toReal *
    (lowerBanditKernel hd word gamma _ _ _).toReal = _
  rw [lower_bandit_behavior_pmf_toReal, lower_bandit_kernel_toReal hd word gamma hg0 hg1]
  simp only [lowerBanditStateWeight, lowerBanditSymbolWeight, finObsProj]
  ring

/-- Summing the unused terminal context leaves the independent word weights. For
[the time horizon](hyp:T), [the code dimension](hyp:d), [the code dimension assumption](hyp:hd),
[the word](hyp:word), [the target](hyp:target), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the g0 assumption](hyp:hg0), [the g1 assumption](hyp:hg1), and
[the observed word](hyp:w), this establishes
[the lower bandit observed probability mass function to real result](goal). -/
-- @node: lower_bandit_observed_pmf_toReal
lemma lower_bandit_observed_pmf_toReal {T d : Nat} (hd : 0 < d)
    (word target : Fin d → Bool) (gamma eta : ℝ) (hg0 : 0 ≤ gamma)
    (hg1 : gamma ≤ 1 / 16) (w : FiniteObsView T d 2) :
    ((lowerBanditFinite hd word target gamma eta).obsPMF w).toReal =
      ∏ t : Fin T, lowerBanditSymbolWeight word gamma (w t) := by
  classical
  let F := lowerBanditFinite (T := T) hd word target gamma eta
  let e := lowerBanditPathEquiv T d
  change ((F.law.map finObsProj) w).toReal = _
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum
    (fun tau _ ↦ by split_ifs <;> simp [PMF.apply_ne_top])]
  simp only [apply_ite ENNReal.toReal, ENNReal.toReal_zero]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have hproj (q : FiniteObsView T d 2 × Fin d) : finObsProj (e.symm q) = q.1 :=
    congrArg Prod.fst (e.apply_symm_apply q)
  dsimp only [F]
  simp_rw [lower_bandit_path_factorization hd word target gamma eta hg0 hg1, hproj]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp [hd.ne', mul_comm]

/-- Every observed-symbol weight is nonnegative. For [the code dimension](hyp:d),
[the word](hyp:word), [the rate parameter](hyp:gamma), [the g0 assumption](hyp:hg0),
[the g1 assumption](hyp:hg1), and [the observed word](hyp:w), this establishes
[the lower bandit symbol nonnegativity result](goal). -/
-- @node: lower_bandit_symbol_nonneg
lemma lower_bandit_symbol_nonneg {d : Nat} (word : Fin d → Bool)
    (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1 / 16)
    (w : Fin d × Bool × Fin 2) : 0 ≤ lowerBanditSymbolWeight word gamma w := by
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg d)) (by norm_num))
    (lower_bandit_reward_weight_nonneg gamma hg0 hg1 _ _ _)

/-- The one-step observed weights normalize without exposing a hidden state. For
[the code dimension](hyp:d), [the code dimension assumption](hyp:hd), [the word](hyp:word), and
[the rate parameter](hyp:gamma), this establishes [the lower bandit symbol sum result](goal). -/
-- @node: lower_bandit_symbol_sum
lemma lower_bandit_symbol_sum {d : Nat} (hd : 0 < d)
    (word : Fin d → Bool) (gamma : ℝ) :
    ∑ w : Fin d × Bool × Fin 2, lowerBanditSymbolWeight word gamma w = 1 := by
  simp only [Fintype.sum_prod_type, lowerBanditSymbolWeight, ← Finset.mul_sum,
    lower_bandit_reward_weight_sum, mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Fintype.card_bool]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  norm_num

/-- The normalized one-step finite observation law. -/
-- @node: lowerBanditSymbolPMF
noncomputable def lowerBanditSymbolPMF {d : Nat} (hd : 0 < d)
    (word : Fin d → Bool) (gamma : ℝ) : PMF (Fin d × Bool × Fin 2) := by
  letI : NeZero d := ⟨hd.ne'⟩
  exact pmfOfRealWeight (lowerBanditSymbolWeight word gamma)

/-- Normalization preserves the explicit one-step observation mass. For
[the code dimension](hyp:d), [the code dimension assumption](hyp:hd), [the word](hyp:word),
[the rate parameter](hyp:gamma), [the g0 assumption](hyp:hg0), [the g1 assumption](hyp:hg1), and
[the observed word](hyp:w), this establishes
[the lower bandit symbol probability mass function to real result](goal). -/
-- @node: lower_bandit_symbol_pmf_toReal
lemma lower_bandit_symbol_pmf_toReal {d : Nat} (hd : 0 < d)
    (word : Fin d → Bool) (gamma : ℝ) (hg0 : 0 ≤ gamma)
    (hg1 : gamma ≤ 1 / 16) (w : Fin d × Bool × Fin 2) :
    (lowerBanditSymbolPMF hd word gamma w).toReal = lowerBanditSymbolWeight word gamma w := by
  letI : NeZero d := ⟨hd.ne'⟩
  change (pmfOfRealWeight _ w).toReal = _
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one _
    (lower_bandit_symbol_nonneg word gamma hg0 hg1)
    (lower_bandit_symbol_sum hd word gamma),
    ENNReal.toReal_ofReal (lower_bandit_symbol_nonneg word gamma hg0 hg1 w)]

/-- The actual finite observed word has the independent product law. For
[the time horizon](hyp:T), [the code dimension](hyp:d), [the code dimension assumption](hyp:hd),
[the word](hyp:word), [the target](hyp:target), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the g0 assumption](hyp:hg0), and [the g1 assumption](hyp:hg1),
this establishes [the lower bandit observed product law result](goal). -/
-- @node: lower_bandit_observed_product_law
lemma lower_bandit_observed_product_law {T d : Nat} (hd : 0 < d)
    (word target : Fin d → Bool) (gamma eta : ℝ) (hg0 : 0 ≤ gamma)
    (hg1 : gamma ≤ 1 / 16) :
    (lowerBanditFinite (T := T) hd word target gamma eta).obsPMF.toMeasure =
      Measure.pi (fun _ : Fin T ↦ (lowerBanditSymbolPMF hd word gamma).toMeasure) := by
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.pi_singleton]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
    (ENNReal.prod_ne_top fun t _ ↦ PMF.apply_ne_top _ _)).mp
  rw [lower_bandit_observed_pmf_toReal hd word target gamma eta hg0 hg1,
    ENNReal.toReal_prod]
  simp_rw [lower_bandit_symbol_pmf_toReal hd word gamma hg0 hg1]

/-- Reward decoding transports the independent word law to the actual observations. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the code dimension assumption](hyp:hd), [the candidate-policy count assumption](hyp:hM),
[the binary code](hyp:code), [the codeword index](hyp:v), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the g0 assumption](hyp:hg0), and [the g1 assumption](hyp:hg1),
this establishes [the lower bandit actual observed product law result](goal). -/
-- @node: lower_bandit_actual_observed_product_law
lemma lower_bandit_actual_observed_product_law (T M d : Nat) (hd : 0 < d)
    (hM : 2 ≤ M) (code : Fin M → Fin d → Bool) (v : Fin M)
    (gamma eta : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1 / 16) :
    obsLaw (lowerBanditExperiment T M d hd hM code v gamma eta).Mx.toRawB =
      (Measure.pi (fun _ : Fin T ↦ (lowerBanditSymbolPMF hd (code v) gamma).toMeasure)).map
        (fun w t ↦ ((w t).1, (w t).2.1, if (w t).2.2 = 0 then (0 : ℝ) else 1)) := by
  change obsLaw (embed (lowerBanditFinite (T := T) hd (code v) (code v) gamma eta)) = _
  rw [embed_obsLaw_eq, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    lower_bandit_observed_product_law hd (code v) (code v) gamma eta hg0 hg1]
  rfl

/-- All alternatives expose the same alphabet, behavior, and target list to a selector. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the code dimension assumption](hyp:hd), [the candidate-policy count assumption](hyp:hM),
[the binary code](hyp:code), [the codeword index](hyp:v), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the observable selector](hyp:sel), and
[the observed word](hyp:w), this establishes
[the lower bandit selector common rule result](goal). -/
-- @node: lower_bandit_selector_common_rule
lemma lower_bandit_selector_common_rule (T M d : Nat) (hd : 0 < d)
    (hM : 2 ≤ M) (code : Fin M → Fin d → Bool) (v : Fin M)
    (gamma eta : ℝ) (sel : ObservableSelector T M) (w : ObsView T d) :
    sel.1 (lowerBanditExperiment T M d hd hM code v gamma eta).nX
      (lowerBanditExperiment T M d hd hM code v gamma eta).Mx.b
      (lowerBanditExperiment T M d hd hM code v gamma eta).Mx.E w =
    sel.1 d (fun _ a ↦ (pmfOfRealWeight (fun _ : Bool ↦ (1 / 2 : ℝ)) a).toReal)
      (fun j x a ↦ (pmfOfRealWeight (lowerBanditPolicyWeight eta (code j) x) a).toReal) w := by
  rfl

end CausalSmith.Stat.PomdpPolicyclassRegret
