import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmScheduleKernel
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmVanTreesAssembly
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmSmoothKernel
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmFinitePosterior
import Causalean.Stat.Minimax.FinitePosteriorBayesRisk

/-! Finite effect-count and posterior compatibility algebra for the smooth two-arm prior. -/

open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

open Causalean.Experimentation.DesignBased

/-- The effect triple 1 space carries the discrete measurable structure. -/
noncomputable local instance (n : ℕ) : MeasurableSpace (EffectTriple n) := ⊤
/-- [every singleton in the effect triple 1 space is measurable](goal). -/
noncomputable local instance (n : ℕ) : MeasurableSingletonClass (EffectTriple n) :=
  ⟨fun _ => MeasurableSet.of_discrete⟩
/-- [the effect triple collection is nonempty](goal). -/
noncomputable local instance (n : ℕ) : Nonempty (EffectTriple n) :=
  ⟨⟨⟨⟨0, Nat.zero_lt_succ n⟩,
      ⟨⟨0, Nat.zero_lt_succ n⟩, ⟨n, Nat.lt_succ_self n⟩⟩⟩, by simp⟩⟩

/-- [The signed-score average depends only on the retained success count.](goal) -/
-- @node: twoArmScoreAverage_eq_count
lemma twoArmScoreAverage_eq_count {n : ℕ} (s : Unit n → Bool) :
    twoArmScoreAverage s =
      (n : ℝ)⁻¹ * (2 * (scoreCount s : ℕ) - n) := by
  unfold twoArmScoreAverage scoreCount
  congr 1
  rw [show (∑ i, if s i then (1 : ℝ) else -1) =
      ∑ i, (2 * (if s i then (1 : ℝ) else 0) - 1) by
    apply Finset.sum_congr rfl
    intro i _
    cases s i <;> norm_num]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  simp

-- @node: twoArmPosteriorCompat_sum_prod_mul_apply
/-- [the two arm posterior compat sums prod times evaluation](goal). -/
lemma twoArmPosteriorCompat_sum_prod_mul_apply {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] (q : I → X → ℝ) (h : X → ℝ) (i : I) :
    ∑ r : I → X, (∏ j, q j (r j)) * h (r i) =
      (∑ t, q i t * h t) * ∏ j ∈ Finset.univ.erase i, ∑ t, q j t := by
  rw [show (∑ r : I → X, (∏ j, q j (r j)) * h (r i)) =
      ∑ r : I → X, ∏ j, if j = i then q j (r j) * h (r j) else q j (r j) by
    apply Finset.sum_congr rfl
    intro r _
    calc
      (∏ j, q j (r j)) * h (r i) =
          (∏ j, q j (r j)) * ∏ j, (if j = i then h (r j) else 1) := by
            simp [Finset.prod_ite_eq']
      _ = ∏ j, q j (r j) * (if j = i then h (r j) else 1) := by
            rw [Finset.prod_mul_distrib]
      _ = _ := by
            apply Finset.prod_congr rfl
            intro j _
            split <;> simp_all]
  let q' : I → X → ℝ := fun j t => if j = i then q j t * h t else q j t
  change (∑ r : I → X, ∏ j, q' j (r j)) = _
  rw [← Fintype.prod_sum]
  dsimp [q']
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [if_pos]
  congr 1
  rw [Finset.sdiff_singleton_eq_erase]
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by simpa using hj
  simp [hji]

-- @node: twoArmPosteriorCompat_marginal
/-- [the second arm count satisfies its stated condition](hyp:ha1), [the parameter lies in the stated interior interval](hyp:hθ), [the two arm posterior compat marginal property holds](goal). -/
lemma twoArmPosteriorCompat_marginal {n : ℕ} (a θ : ℝ) (ha1 : a ≤ 1)
    (hθ : |θ| ≤ a / 2) (s : Unit n → Bool) :
    ∑ r : Unit n → Bool × Bool,
        (∏ i, (twoArmSmoothResponseTypeDesign a θ ha1
          (hθ.trans (by nlinarith [abs_nonneg θ]))).p (r i)) *
          (if (fun i => (r i).1) = s then 1 else 0) =
      twoArmBernoulliLikelihood θ s := by
  rw [show (∑ r : Unit n → Bool × Bool,
      (∏ i, (twoArmSmoothResponseTypeDesign a θ ha1
        (hθ.trans (by nlinarith [abs_nonneg θ]))).p (r i)) *
        (if (fun i => (r i).1) = s then 1 else 0)) =
      ∑ r : Unit n → Bool × Bool,
        ∏ i, ((twoArmSmoothResponseTypeDesign a θ ha1
          (hθ.trans (by nlinarith [abs_nonneg θ]))).p (r i) *
            (if (r i).1 = s i then 1 else 0)) by
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : (fun i => (r i).1) = s
    · simp [hr, congrFun hr]
    · have hi : ∃ i, (r i).1 ≠ s i := by
        simpa only [Function.ne_iff] using hr
      obtain ⟨i, hi⟩ := hi
      simp only [hr, if_false, mul_zero]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]]
  let q : Unit n → (Bool × Bool) → ℝ := fun i t =>
    (twoArmSmoothResponseTypeDesign a θ ha1
      (hθ.trans (by nlinarith [abs_nonneg θ]))).p t *
        (if t.1 = s i then 1 else 0)
  change (∑ r : Unit n → Bool × Bool, ∏ i, q i (r i)) = _
  rw [← Fintype.prod_sum]
  unfold twoArmBernoulliLikelihood
  apply Finset.prod_congr rfl
  intro i _
  rw [show (∑ t : Bool × Bool,
      (twoArmSmoothResponseTypeDesign a θ ha1
        (hθ.trans (by nlinarith [abs_nonneg θ]))).p t *
          (if t.1 = s i then 1 else 0)) =
      ((twoArmSmoothResponseTypeDesign a θ ha1
        (hθ.trans (by nlinarith [abs_nonneg θ]))).map
          (twoArmObservedScore 0)).p (s i) by
    simp [FiniteDesign.map_p, twoArmObservedScore]]
  rw [twoArmSmoothResponseType_score_mass]
  simp [twoArmBernoulliUnitDesign]

-- @node: twoArmPosteriorCompat_effectTarget
/-- [the two arm posterior compat effect target property holds](goal). -/
lemma twoArmPosteriorCompat_effectTarget {n : ℕ} (r : Unit n → Bool × Bool) :
    effectTarget (responseVectorEffectTriple r) =
      (n : ℝ)⁻¹ * ∑ i, twoArmResponseEffect (r i) := by
  rw [effectTarget_responseVectorEffectTriple]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, twoArmResponseEffect]
  push_cast
  rw [div_eq_mul_inv, sub_mul, Finset.sum_mul, Finset.sum_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  funext i
  cases (r i).1 <;> cases (r i).2 <;> norm_num

-- @node: twoArmPosteriorCompat_mean_unit_posterior
/-- [the population size is positive](hyp:hn), [the parameter lies in the stated interval](hyp:ha), [the parameter lies in the stated interior interval](hyp:hθ), [the two arm posterior compat mean unit posterior property holds](goal). -/
lemma twoArmPosteriorCompat_mean_unit_posterior {n : ℕ} (hn : 0 < n) {a θ : ℝ}
    (ha : a ≤ 1 / 2) (hθ : |θ| ≤ a / 2) (s : Unit n → Bool) :
    (n : ℝ)⁻¹ * ∑ i, (if s i then (a + θ) / (1 + θ)
      else -(a - θ) / (1 - θ)) = twoArmPosteriorTarget a θ s := by
  have hp : 1 + θ ≠ 0 := by
    have := (abs_le.mp hθ).1
    linarith
  have hm : 1 - θ ≠ 0 := by
    have := (abs_le.mp hθ).2
    linarith
  have hden : 1 - θ ^ 2 ≠ 0 := by
    rw [show 1 - θ ^ 2 = (1 + θ) * (1 - θ) by ring]
    exact mul_ne_zero hp hm
  unfold twoArmPosteriorTarget twoArmPosteriorWeight
  rw [twoArmScoreAverage_eq_count]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hfalse : (Finset.univ.filter fun i => ¬s i).card =
      n - (scoreCount s : ℕ) := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Unit n))) (p := fun i => s i)
    simp only [Finset.card_univ, Fintype.card_fin] at hpart
    change _ = n - (Finset.univ.filter fun i => s i).card
    omega
  rw [hfalse]
  have htrue : (Finset.univ.filter fun i => s i).card = (scoreCount s : ℕ) := rfl
  rw [htrue]
  have hk : (scoreCount s : ℕ) ≤ n := by
    exact Nat.le_of_lt_succ (scoreCount s).isLt
  push_cast [Nat.cast_sub hk]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hp, hm, hden, hnR]
  ring

-- @node: twoArmPosteriorCompat_first_moment
/-- [the population size is positive](hyp:hn), [the parameter lies in the stated interval](hyp:ha), [the parameter lies in the stated interior interval](hyp:hθ), [the two arm posterior compat first moment property holds](goal). -/
lemma twoArmPosteriorCompat_first_moment {n : ℕ} (hn : 0 < n) (a θ : ℝ)
    (ha : a ≤ 1 / 2) (hθ : |θ| ≤ a / 2) (s : Unit n → Bool) :
    ∑ r : Unit n → Bool × Bool,
        (∏ i, (twoArmSmoothResponseTypeDesign a θ (by linarith)
          (hθ.trans (by nlinarith [abs_nonneg θ]))).p (r i)) *
          (if (fun i => (r i).1) = s then 1 else 0) *
          effectTarget (responseVectorEffectTriple r) =
      twoArmBernoulliLikelihood θ s * twoArmPosteriorTarget a θ s := by
  have ha1 : a ≤ 1 := by linarith
  let P := twoArmSmoothResponseTypeDesign a θ ha1
    (hθ.trans (by nlinarith [abs_nonneg θ]))
  let q : Unit n → (Bool × Bool) → ℝ := fun i t =>
    P.p t * (if t.1 = s i then 1 else 0)
  have hrewrite (r : Unit n → Bool × Bool) :
      (∏ i, P.p (r i)) * (if (fun i => (r i).1) = s then 1 else 0) =
        ∏ i, q i (r i) := by
    dsimp [q]
    by_cases hr : (fun i => (r i).1) = s
    · simp [congrFun hr]
    · have hi : ∃ i, (r i).1 ≠ s i := by
        simpa only [Function.ne_iff] using hr
      obtain ⟨i, hi⟩ := hi
      simp only [hr, if_false, mul_zero]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  simp_rw [show twoArmSmoothResponseTypeDesign a θ ha1
      (hθ.trans (by nlinarith [abs_nonneg θ])) = P by rfl]
  simp_rw [hrewrite, twoArmPosteriorCompat_effectTarget]
  rw [show (∑ r : Unit n → Bool × Bool,
      (∏ i, q i (r i)) * ((n : ℝ)⁻¹ * ∑ i, twoArmResponseEffect (r i))) =
      (n : ℝ)⁻¹ * ∑ i, ∑ r : Unit n → Bool × Bool,
        (∏ j, q j (r j)) * twoArmResponseEffect (r i) by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    ring]
  simp_rw [twoArmPosteriorCompat_sum_prod_mul_apply]
  have hunit (i : Unit n) :
      (∑ t, q i t * twoArmResponseEffect t) =
        (twoArmBernoulliUnitDesign θ
          (hθ.trans (by nlinarith))).p (s i) *
          (if s i then (a + θ) / (1 + θ) else -(a - θ) / (1 - θ)) := by
    rw [← twoArmSmoothResponseType_effect_score_mass a θ ha1 hθ 0 (s i)]
    apply Finset.sum_congr rfl
    intro t _
    dsimp [q, P]
    simp [twoArmObservedScore]
  have hmarg (i : Unit n) :
      ∑ t, q i t = (twoArmBernoulliUnitDesign θ
        (hθ.trans (by nlinarith))).p (s i) := by
    change ∑ t, P.p t * (if t.1 = s i then 1 else 0) = _
    rw [show (∑ t, P.p t * (if t.1 = s i then 1 else 0)) =
        (P.map (twoArmObservedScore 0)).p (s i) by
      simp [FiniteDesign.map_p, twoArmObservedScore]]
    exact twoArmSmoothResponseType_score_mass a θ ha1
      (hθ.trans (by nlinarith [abs_nonneg θ])) 0 (s i)
  simp_rw [hunit, hmarg]
  have hprod (i : Unit n) :
      (twoArmBernoulliUnitDesign θ (hθ.trans (by nlinarith))).p (s i) *
          (if s i then (a + θ) / (1 + θ) else -(a - θ) / (1 - θ)) *
          ∏ j ∈ Finset.univ.erase i,
            (twoArmBernoulliUnitDesign θ (hθ.trans (by nlinarith))).p (s j) =
        twoArmBernoulliLikelihood θ s *
          (if s i then (a + θ) / (1 + θ) else -(a - θ) / (1 - θ)) := by
    rw [twoArmBernoulliLikelihood]
    have hbern (j : Unit n) :
        (if s j then (1 + θ) / 2 else (1 - θ) / 2) =
          (twoArmBernoulliUnitDesign θ (hθ.trans (by nlinarith))).p (s j) := by
      cases s j <;> simp [twoArmBernoulliUnitDesign]
    simp_rw [hbern]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => (twoArmBernoulliUnitDesign θ
        (hθ.trans (by nlinarith))).p (s j)) (Finset.mem_univ i)]
    ring
  simp_rw [hprod]
  rw [← Finset.mul_sum]
  calc
    (n : ℝ)⁻¹ * (twoArmBernoulliLikelihood θ s *
        ∑ i, (if s i then (a + θ) / (1 + θ) else -(a - θ) / (1 - θ))) =
      twoArmBernoulliLikelihood θ s * ((n : ℝ)⁻¹ *
        ∑ i, (if s i then (a + θ) / (1 + θ) else -(a - θ) / (1 - θ))) := by ring
    _ = _ := by rw [twoArmPosteriorCompat_mean_unit_posterior hn ha hθ]

-- @node: twoArmPosteriorCompat_square_completion
/-- [the population size is positive](hyp:hn), [the parameter lies in the stated interval](hyp:ha), [the parameter lies in the stated interior interval](hyp:hθ), [the two arm posterior compat square completion property holds](goal). -/
lemma twoArmPosteriorCompat_square_completion {n : ℕ} (hn : 0 < n) (a θ : ℝ)
    (ha : a ≤ 1 / 2) (hθ : |θ| ≤ a / 2)
    (T : Fin (n + 1) → ℝ) (s : Unit n → Bool) :
    twoArmBernoulliLikelihood θ s *
        (T (scoreCount s) - twoArmPosteriorTarget a θ s) ^ 2 ≤
      ∑ r : Unit n → Bool × Bool,
        ((∏ i, (twoArmSmoothResponseTypeDesign a θ (by linarith)
          (hθ.trans (by nlinarith [abs_nonneg θ]))).p (r i)) *
          (if (fun i => (r i).1) = s then 1 else 0)) *
          (T (scoreCount s) - effectTarget (responseVectorEffectTriple r)) ^ 2 := by
  let P := twoArmSmoothResponseTypeDesign a θ (by linarith : a ≤ 1)
    (hθ.trans (by nlinarith [abs_nonneg θ]))
  let w : (Unit n → Bool × Bool) → ℝ := fun r =>
    (∏ i, P.p (r i)) * (if (fun i => (r i).1) = s then 1 else 0)
  have hw0 (r : Unit n → Bool × Bool) : 0 ≤ w r := by
    dsimp [w]
    exact mul_nonneg (Finset.prod_nonneg fun i _ => P.p_nonneg (r i)) (by positivity)
  have hmarg : ∑ r, w r = twoArmBernoulliLikelihood θ s := by
    dsimp [w, P]
    exact twoArmPosteriorCompat_marginal a θ (by linarith) hθ s
  have hfirst : ∑ r, w r * effectTarget (responseVectorEffectTriple r) =
      twoArmBernoulliLikelihood θ s * twoArmPosteriorTarget a θ s := by
    dsimp [w, P]
    simpa only [mul_assoc] using twoArmPosteriorCompat_first_moment hn a θ ha hθ s
  have hcenter : ∑ r, w r * (twoArmPosteriorTarget a θ s -
      effectTarget (responseVectorEffectTriple r)) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmarg, hfirst]
    ring
  have hid : (∑ r, w r *
      (T (scoreCount s) - effectTarget (responseVectorEffectTriple r)) ^ 2) =
      twoArmBernoulliLikelihood θ s *
          (T (scoreCount s) - twoArmPosteriorTarget a θ s) ^ 2 +
        ∑ r, w r *
          (twoArmPosteriorTarget a θ s -
            effectTarget (responseVectorEffectTriple r)) ^ 2 := by
    simp_rw [show ∀ r : Unit n → Bool × Bool,
        w r * (T (scoreCount s) - effectTarget (responseVectorEffectTriple r)) ^ 2 =
          w r * (T (scoreCount s) - twoArmPosteriorTarget a θ s) ^ 2 +
          w r * (twoArmPosteriorTarget a θ s -
            effectTarget (responseVectorEffectTriple r)) ^ 2 +
          2 * (T (scoreCount s) - twoArmPosteriorTarget a θ s) *
            (w r * (twoArmPosteriorTarget a θ s -
              effectTarget (responseVectorEffectTriple r))) by intro r; ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hmarg]
    rw [← Finset.mul_sum, hcenter]
    ring
  rw [hid]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun r _ =>
    mul_nonneg (hw0 r) (sq_nonneg _))

-- @node: twoArmPosteriorCompat_product_formula
/-- [the second arm count satisfies its stated condition](hyp:ha1), [the parameter lies in the stated interior interval](hyp:hθ), [the two arm posterior compat product formula property holds](goal). -/
lemma twoArmPosteriorCompat_product_formula {n : ℕ} (a θ : ℝ) (ha1 : a ≤ 1)
    (hθ : |θ| ≤ a) (r : Unit n → Bool × Bool) :
    ∏ i, (twoArmSmoothResponseTypeDesign a θ ha1 hθ).p (r i) =
      ((a + θ) / 2) ^ (Finset.univ.filter fun i => (r i).1 && !(r i).2).card *
      ((a - θ) / 2) ^ (Finset.univ.filter fun i => !((r i).1) && (r i).2).card *
      ((1 - a) / 2) ^ (Finset.univ.filter fun i => (r i).1 = (r i).2).card := by
  rw [show (∏ i, (twoArmSmoothResponseTypeDesign a θ ha1 hθ).p (r i)) =
      ∏ i, if (r i).1 && !(r i).2 then (a + θ) / 2
        else if !((r i).1) && (r i).2 then (a - θ) / 2 else (1 - a) / 2 by
    apply Finset.prod_congr rfl
    intro i _
    cases h0 : (r i).1 <;> cases h1 : (r i).2 <;>
      simp [h0, h1, twoArmSmoothResponseTypeDesign]]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Finset.card_filter, nsmul_eq_mul]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hneg : (Finset.univ.filter fun i => ¬((r i).1 && !(r i).2)).filter
      (fun i => !((r i).1) && (r i).2) =
      Finset.univ.filter (fun i => !((r i).1) && (r i).2) := by
    ext i
    cases h0 : (r i).1 <;> cases h1 : (r i).2 <;> simp [h0, h1]
  have hzero : (Finset.univ.filter fun i => ¬((r i).1 && !(r i).2)).filter
      (fun i => ¬(!((r i).1) && (r i).2)) =
      Finset.univ.filter (fun i => (r i).1 = (r i).2) := by
    ext i
    cases h0 : (r i).1 <;> cases h1 : (r i).2 <;> simp [h0, h1]
  rw [hneg, hzero]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  ring

-- @node: twoArmPosteriorCompat_responseSchedule
/-- The two arm posterior compat response schedule property holds. -/
def twoArmPosteriorCompat_responseSchedule {n : ℕ} (r : Unit n → Bool × Bool) : Schedule 2 n :=
  fun i arm => if arm = 0 then (r i).1 else (r i).2

-- @node: twoArmPosteriorCompat_scheduleResponse
/-- The two arm posterior compat schedule response property holds. -/
def twoArmPosteriorCompat_scheduleResponse {n : ℕ} (z : Schedule 2 n) : Unit n → Bool × Bool :=
  fun i => (z i 0, z i 1)

-- @node: twoArmPosteriorCompat_responseScheduleEquiv
/-- The two arm posterior compat response schedule equiv property holds. -/
def twoArmPosteriorCompat_responseScheduleEquiv (n : ℕ) :
    (Unit n → Bool × Bool) ≃ Schedule 2 n where
  toFun := twoArmPosteriorCompat_responseSchedule
  invFun := twoArmPosteriorCompat_scheduleResponse
  left_inv r := by
    funext i
    simp [twoArmPosteriorCompat_responseSchedule, twoArmPosteriorCompat_scheduleResponse]
  right_inv z := by
    funext i arm
    fin_cases arm <;> simp [twoArmPosteriorCompat_responseSchedule, twoArmPosteriorCompat_scheduleResponse]

-- @node: twoArmPosteriorCompat_hasEffectTriple_iff
/-- [the two arm posterior compat has effect triple if and only if property holds](goal). -/
lemma twoArmPosteriorCompat_hasEffectTriple_iff {n : ℕ} (e : EffectTriple n)
    (r : Unit n → Bool × Bool) :
    hasEffectTriple e (twoArmPosteriorCompat_responseSchedule r) ↔ responseVectorEffectTriple r = e := by
  constructor
  · intro h
    simp only [hasEffectTriple, twoArmPosteriorCompat_responseSchedule] at h
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact h.1
    · apply Prod.ext
      · apply Fin.ext
        exact h.2.1
      · apply Fin.ext
        exact h.2.2
  · intro h
    subst e
    exact ⟨rfl, rfl, rfl⟩

-- @node: twoArmPosteriorCompat_product_eq_of_effectTriple_eq
/-- [the second arm count satisfies its stated condition](hyp:ha1), [the parameter lies in the stated interior interval](hyp:hθ), [the stated side condition holds](hyp:h), [the two arm posterior compat product equals when effect triple equals](goal). -/
lemma twoArmPosteriorCompat_product_eq_of_effectTriple_eq {n : ℕ} (a θ : ℝ) (ha1 : a ≤ 1)
    (hθ : |θ| ≤ a) {r t : Unit n → Bool × Bool}
    (h : responseVectorEffectTriple r = responseVectorEffectTriple t) :
    ∏ i, (twoArmSmoothResponseTypeDesign a θ ha1 hθ).p (r i) =
      ∏ i, (twoArmSmoothResponseTypeDesign a θ ha1 hθ).p (t i) := by
  rw [twoArmPosteriorCompat_product_formula a θ ha1 hθ r, twoArmPosteriorCompat_product_formula a θ ha1 hθ t]
  have hp := congrArg (fun e : EffectTriple n => (e.1.1 : ℕ)) h
  have hm := congrArg (fun e : EffectTriple n => (e.1.2.1 : ℕ)) h
  have hz := congrArg (fun e : EffectTriple n => (e.1.2.2 : ℕ)) h
  change (Finset.univ.filter fun i => (r i).1 && !(r i).2).card =
    (Finset.univ.filter fun i => (t i).1 && !(t i).2).card at hp
  change (Finset.univ.filter fun i => !((r i).1) && (r i).2).card =
    (Finset.univ.filter fun i => !((t i).1) && (t i).2).card at hm
  change (Finset.univ.filter fun i => (r i).1 = (r i).2).card =
    (Finset.univ.filter fun i => (t i).1 = (t i).2).card at hz
  rw [hp, hm, hz]

-- @node: twoArmPosteriorCompat_smoothEffect_canonical_mixture
/-- [the first arm count satisfies its stated condition](hyp:ha0), [the second arm count satisfies its stated condition](hyp:ha1), [the parameter lies in the stated interior interval](hyp:hθ), [the two arm posterior compat smooth effect canonical mixture property holds](goal). -/
lemma twoArmPosteriorCompat_smoothEffect_canonical_mixture {n : ℕ} (a θ : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hθ : |θ| ≤ a / 2)
    (z : Schedule 2 n) :
    ∑ e : EffectTriple n, (twoArmSmoothEffectDesign n a θ ha0 ha1).p e *
        canonicalScheduleKernel e z =
      ∏ i, (twoArmSmoothResponseTypeDesign a θ ha1
        (hθ.trans (by nlinarith [abs_nonneg θ]))).p (twoArmPosteriorCompat_scheduleResponse z i) := by
  classical
  let r0 := twoArmPosteriorCompat_scheduleResponse z
  let e0 := responseVectorEffectTriple r0
  let P := twoArmSmoothResponseTypeDesign a θ ha1
    (hθ.trans (by nlinarith [abs_nonneg θ]))
  have hrz : twoArmPosteriorCompat_responseSchedule r0 = z := by
    exact (twoArmPosteriorCompat_responseScheduleEquiv n).right_inv z
  have hz0 : hasEffectTriple e0 z := by
    rw [← hrz, twoArmPosteriorCompat_hasEffectTriple_iff]
  rw [Finset.sum_eq_single e0]
  · unfold twoArmSmoothEffectDesign
    rw [FiniteDesign.map_p]
    simp only [Causalean.Experimentation.DesignBased.prodDesign_p]
    simp only [twoArmClampedParameter_eq hθ]
    rw [Finset.sum_mul]
    calc
      (∑ r : Unit n → Bool × Bool,
          (if responseVectorEffectTriple r = e0 then ∏ i, P.p (r i) else 0) *
            canonicalScheduleKernel e0 z) =
          ∑ r : Unit n → Bool × Bool, (∏ i, P.p (r0 i)) *
              canonicalScheduleKernel e0 (twoArmPosteriorCompat_responseSchedule r) := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases hr : responseVectorEffectTriple r = e0
        · rw [if_pos hr]
          have hmass : (∏ i, P.p (r i)) = ∏ i, P.p (r0 i) := by
            apply twoArmPosteriorCompat_product_eq_of_effectTriple_eq a θ ha1
              (hθ.trans (by nlinarith [abs_nonneg θ]))
            simpa [e0] using hr
          rw [hmass]
          have hzr : hasEffectTriple e0 (twoArmPosteriorCompat_responseSchedule r) :=
            (twoArmPosteriorCompat_hasEffectTriple_iff e0 r).2 hr
          simp [canonicalScheduleKernel, hz0, hzr]
        · rw [if_neg hr]
          have hzr : ¬hasEffectTriple e0 (twoArmPosteriorCompat_responseSchedule r) := by
            simpa [twoArmPosteriorCompat_hasEffectTriple_iff] using hr
          simp [canonicalScheduleKernel, hzr]
      _ = (∏ i, P.p (r0 i)) *
            ∑ r : Unit n → Bool × Bool,
              canonicalScheduleKernel e0 (twoArmPosteriorCompat_responseSchedule r) := by
        rw [Finset.mul_sum]
      _ = ∏ i, P.p (r0 i) := by
        rw [Fintype.sum_equiv (twoArmPosteriorCompat_responseScheduleEquiv n)
          (fun r => canonicalScheduleKernel e0 (twoArmPosteriorCompat_responseSchedule r))
          (fun z => canonicalScheduleKernel e0 z) (fun _ => rfl)]
        rw [canonicalScheduleKernel_sum, mul_one]
      _ = _ := by rfl
  · intro e _ he
    have hne : ¬hasEffectTriple e z := by
      intro hez
      have h1 := (twoArmPosteriorCompat_hasEffectTriple_iff e r0).1 (by simpa [hrz] using hez)
      have h0 := (twoArmPosteriorCompat_hasEffectTriple_iff e0 r0).1 (by simpa [hrz] using hz0)
      exact he (h1.symm.trans h0)
    simp [canonicalScheduleKernel, hne]
  · intro h
    exact (h (Finset.mem_univ e0)).elim

-- @node: twoArmPosteriorCompat_zeroAssignDesign
/-- The two arm posterior compat zero assign design property holds. -/
noncomputable def twoArmPosteriorCompat_zeroAssignDesign (n : ℕ) : FiniteDesign (Assign 2 n) where
  p A := if A = (fun _ => 0) then 1 else 0
  p_nonneg A := by split_ifs <;> positivity
  p_sum := by simp

-- @node: twoArmPosteriorCompat_zeroAssign_labeledRisk
/-- [the two arm posterior compat zero assign labeled risk property holds](goal). -/
lemma twoArmPosteriorCompat_zeroAssign_labeledRisk {n : ℕ} (f : ℕ → ℝ) (z : Schedule 2 n) :
    labeledRisk twoArmContrast
      (twoArmPosteriorCompat_zeroAssignDesign n, scalarClippedEstimator f) z =
      (clip twoArmContrast (f (scoreCount (fun i => z i 0))) -
        tauC twoArmContrast z) ^ 2 := by
  unfold labeledRisk FiniteDesign.mse FiniteDesign.E twoArmPosteriorCompat_zeroAssignDesign
  rw [Finset.sum_eq_single (fun _ => 0)]
  · simp [scalarClippedEstimator, observedScore, obsOutcome, potentialOutcome,
      scoreCount, twoArmContrast, clip]
  · intro A _ hA
    simp [hA]
  · simp

-- @node: twoArmPosteriorCompat_effectRisk_eq_responseRisk
/-- [the first arm count satisfies its stated condition](hyp:ha0), [the parameter lies in the stated interval](hyp:ha), [the parameter lies in the stated interior interval](hyp:hθ), [the two arm posterior compat effect risk equals response risk](goal). -/
lemma twoArmPosteriorCompat_effectRisk_eq_responseRisk {n : ℕ} (a θ : ℝ)
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hθ : |θ| ≤ a / 2) (f : ℕ → ℝ) :
    (twoArmSmoothEffectDesign n a θ ha0 (by linarith)).E
        (Causalean.Stat.statewiseSquaredLoss (twoArmCountKernel (twoArmPosteriorCompat_zeroAssignDesign n))
          (fun e _ => effectTarget e)
          (fun x => clip twoArmContrast (f x))) =
      ∑ r : Unit n → Bool × Bool,
        (∏ i, (twoArmSmoothResponseTypeDesign a θ (by linarith)
          (hθ.trans (by nlinarith [abs_nonneg θ]))).p (r i)) *
          (clip twoArmContrast (f (scoreCount (fun i => (r i).1))) -
            effectTarget (responseVectorEffectTriple r)) ^ 2 := by
  rw [show (twoArmSmoothEffectDesign n a θ ha0 (by linarith)).E
      (Causalean.Stat.statewiseSquaredLoss (twoArmCountKernel (twoArmPosteriorCompat_zeroAssignDesign n))
        (fun e _ => effectTarget e) (fun x => clip twoArmContrast (f x))) =
      (twoArmSmoothEffectDesign n a θ ha0 (by linarith)).E
        (fun e => (twoArmScoreExperiment (twoArmPosteriorCompat_zeroAssignDesign n)).statisticRisk
          effectTarget (fun x => clip twoArmContrast (f x)) e) by
    apply Finset.sum_congr rfl
    intro e _
    rw [twoArmCount_statewiseSquaredLoss_eq_statisticRisk]]
  simp_rw [← clippedFullRisk_eq_statisticRisk]
  simp_rw [twoArmScoreExperiment_fullRisk_eq_labeled]
  unfold FiniteDesign.E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ z : Schedule 2 n, ∑ e : EffectTriple n,
        (twoArmSmoothEffectDesign n a θ ha0 (by linarith)).p e *
          (canonicalScheduleKernel e z *
            labeledRisk twoArmContrast
              (twoArmPosteriorCompat_zeroAssignDesign n, scalarClippedEstimator f) z)) =
      ∑ z : Schedule 2 n,
        (∏ i, (twoArmSmoothResponseTypeDesign a θ (by linarith)
          (hθ.trans (by nlinarith [abs_nonneg θ]))).p
            (twoArmPosteriorCompat_scheduleResponse z i)) *
          labeledRisk twoArmContrast
            (twoArmPosteriorCompat_zeroAssignDesign n, scalarClippedEstimator f) z := by
      apply Finset.sum_congr rfl
      intro z _
      rw [show (∑ e : EffectTriple n,
          (twoArmSmoothEffectDesign n a θ ha0 (by linarith)).p e *
            (canonicalScheduleKernel e z *
              labeledRisk twoArmContrast
                (twoArmPosteriorCompat_zeroAssignDesign n, scalarClippedEstimator f) z)) =
          (∑ e : EffectTriple n,
            (twoArmSmoothEffectDesign n a θ ha0 (by linarith)).p e *
              canonicalScheduleKernel e z) *
              labeledRisk twoArmContrast
                (twoArmPosteriorCompat_zeroAssignDesign n, scalarClippedEstimator f) z by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _
        ring]
      rw [twoArmPosteriorCompat_smoothEffect_canonical_mixture (n := n) a θ ha0 (by linarith) hθ z]
    _ = _ := by
      apply Fintype.sum_equiv (twoArmPosteriorCompat_responseScheduleEquiv n).symm _ _
      intro z
      rw [twoArmPosteriorCompat_zeroAssign_labeledRisk]
      let r := twoArmPosteriorCompat_scheduleResponse z
      have heff : tauC twoArmContrast (twoArmPosteriorCompat_responseSchedule r) =
          effectTarget (responseVectorEffectTriple r) :=
        twoArmTau_eq_effectTriple ((twoArmPosteriorCompat_hasEffectTriple_iff _ r).2 rfl)
      have hrz : twoArmPosteriorCompat_responseSchedule r = z := (twoArmPosteriorCompat_responseScheduleEquiv n).right_inv z
      rw [← hrz, heff]
      have hsym : (twoArmPosteriorCompat_responseScheduleEquiv n).symm (twoArmPosteriorCompat_responseSchedule r) = r := by
        exact (twoArmPosteriorCompat_responseScheduleEquiv n).symm_apply_apply r
      rw [hsym]
      simp [r, twoArmPosteriorCompat_scheduleResponse, twoArmPosteriorCompat_responseSchedule, scoreCount]

-- @node: twoArmPosteriorCompat_error_le_effectRisk
/-- [the population size is positive](hyp:hn), [the first arm count satisfies its stated condition](hyp:ha0), [the parameter lies in the stated interval](hyp:ha), [the parameter lies in the stated interior interval](hyp:hθ), [the two arm posterior compat error is at most effect risk](goal). -/
lemma twoArmPosteriorCompat_error_le_effectRisk {n : ℕ} (hn : 0 < n) (a θ : ℝ)
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hθ : |θ| ≤ a / 2) (f : ℕ → ℝ) :
    ∑ s : Unit n → Bool, twoArmBernoulliLikelihood θ s *
        (clip twoArmContrast (f (scoreCount s)) - twoArmPosteriorTarget a θ s) ^ 2 ≤
      (twoArmSmoothEffectDesign n a θ ha0 (by linarith)).E
        (Causalean.Stat.statewiseSquaredLoss (twoArmCountKernel (twoArmPosteriorCompat_zeroAssignDesign n))
          (fun e _ => effectTarget e) (fun x => clip twoArmContrast (f x))) := by
  rw [twoArmPosteriorCompat_effectRisk_eq_responseRisk a θ ha0 ha hθ f]
  calc
    _ ≤ ∑ s : Unit n → Bool, ∑ r : Unit n → Bool × Bool,
        ((∏ i, (twoArmSmoothResponseTypeDesign a θ (by linarith)
          (hθ.trans (by nlinarith [abs_nonneg θ]))).p (r i)) *
          (if (fun i => (r i).1) = s then 1 else 0)) *
          (clip twoArmContrast (f (scoreCount s)) -
            effectTarget (responseVectorEffectTriple r)) ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      exact twoArmPosteriorCompat_square_completion hn a θ ha hθ
        (fun x => clip twoArmContrast (f x)) s
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_eq_single (fun i => (r i).1)]
      · simp
      · intro s _ hs
        simp [Ne.symm hs]
      · simp

-- @node: twoArmPosteriorCompat_smoothPriorMeasure
/-- The smooth two-arm prior measure has the stated density on the parameter interval and is pushed forward to effect-count triples. -/
noncomputable def twoArmPosteriorCompat_smoothPriorMeasure (a : ℝ) : Measure ℝ :=
  (Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
    (-1 / 2) (1 / 2)).withDensity
      (fun θ => ENNReal.ofReal
        (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior 0 (a / 2) θ))

-- @node: twoArmPosteriorCompat_smoothPriorMeasure_isProbability
/-- [the parameter lies in the stated interval](hyp:ha), [the second arm count satisfies its stated condition](hyp:ha1), [the two arm posterior compat smooth prior measure is probability property holds](goal). -/
lemma twoArmPosteriorCompat_smoothPriorMeasure_isProbability (a : ℝ) (ha : 0 < a)
    (ha1 : a ≤ 1) : IsProbabilityMeasure (twoArmPosteriorCompat_smoothPriorMeasure a) := by
  apply IsProbabilityMeasure.mk
  unfold twoArmPosteriorCompat_smoothPriorMeasure
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_integrable_parameterMeasure
      (by positivity : 0 < a / 2))
    (Filter.Eventually.of_forall
      (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_nonneg
        (by positivity : 0 < a / 2)))]
  rw [Causalean.Stat.Limit.ObservationDependentVanTrees.integral_smoothPrior_parameterMeasure
    (by positivity : 0 < a / 2) (by linarith) (by linarith)]
  simp

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
