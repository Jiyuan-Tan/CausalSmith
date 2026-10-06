module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TentLowerConstruction

/-! Cross-sign paired-tent geometry and the finite full-record likelihood exponent. -/
public section
set_option linter.style.whitespace false
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Disjoint paired bumps remove every off-diagonal term in a two-field product. [This is the stated conclusion](goal). -/
-- @node: coarseTent_mul_sum
lemma coarseTent_mul_sum (M : ℕ) (σ τ : Fin (M/2) → Bool) (x : ℝ) :
    coarseTent M σ x * coarseTent M τ x =
      ∑ j : Fin (M/2), signVal (σ j) * signVal (τ j) *
        ((tentBase ((M:ℝ)*x-2*j.val))^2 +
          (tentBase ((M:ℝ)*x-(2*j.val+1)))^2) := by
  classical
  let f (j : Fin (M/2)) :=
    tentBase ((M:ℝ)*x-2*j.val)-tentBase ((M:ℝ)*x-(2*j.val+1))
  have hp (j : Fin (M/2)) : f j^2 =
      (tentBase ((M:ℝ)*x-2*j.val))^2 +
        (tentBase ((M:ℝ)*x-(2*j.val+1)))^2 := by
    have hz := tentBase_adjacent_mul_zero ((M:ℝ)*x-2*j.val)
    rw [show (M:ℝ)*x-2*j.val-1 = (M:ℝ)*x-(2*j.val+1) by ring] at hz
    dsimp [f]
    nlinarith
  simp_rw [← hp]
  by_cases hn : ∃ j, f j ≠ 0
  · obtain ⟨j, hj⟩ := hn
    have hz (k : Fin (M/2)) (hk : k ≠ j) : f k = 0 := by
      by_contra h
      exact hk (paired_bump_unique M x k j h hj)
    have he (s : Fin (M/2) → Bool) : coarseTent M s x = signVal (s j)*f j := by
      unfold coarseTent
      apply Finset.sum_eq_single j
      · intro k _ hk
        change signVal (s k)*f k = 0
        rw [hz k hk, mul_zero]
      · simp
    rw [he σ, he τ]
    rw [Finset.sum_eq_single j]
    · ring
    · intro k _ hk
      rw [hz k hk]
      ring
    · simp
  · have hz : ∀ j, f j = 0 := by simpa using hn
    have he (s : Fin (M/2) → Bool) : coarseTent M s x = 0 := by
      unfold coarseTent
      apply Finset.sum_eq_zero
      intro j _
      change signVal (s j)*f j = 0
      rw [hz j, mul_zero]
    simp [he, hz]

/-- The full interval overlap is the signed sum of equal paired-cell squared areas. This statement assumes [the hM condition](hyp:hM). [This is the stated conclusion](goal). -/
-- @node: coarseTent_interval_overlap
lemma coarseTent_interval_overlap (M : ℕ) (hM : 0 < M)
    (σ τ : Fin (M/2) → Bool) :
    (∫ x in (0:ℝ)..1, coarseTent M σ x * coarseTent M τ x) =
      (2 / (3*(M:ℝ))) * ∑ j : Fin (M/2), signVal (σ j)*signVal (τ j) := by
  have hidx (j : Fin (M/2)) : 2*j.val < M ∧ 2*j.val+1 < M := by omega
  simp_rw [coarseTent_mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · have hp (j : Fin (M/2)) :
        (∫ x in (0:ℝ)..1, signVal (σ j)*signVal (τ j)*
          ((tentBase ((M:ℝ)*x-2*j.val))^2 +
            (tentBase ((M:ℝ)*x-(2*j.val+1)))^2)) =
          (2/(3*(M:ℝ)))*(signVal (σ j)*signVal (τ j)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add
          (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop)]
      norm_cast
      rw [(scaled_tent_integrals M (2*j.val) hM (hidx j).1).2,
        (scaled_tent_integrals M (2*j.val+1) hM (hidx j).2).2]
      push_cast
      ring
    simp_rw [hp]
    rw [Finset.mul_sum]
  · intro j _
    apply Continuous.intervalIntegrable
    fun_prop

/-- The normalized original design preserves the exact cross-sign overlap. This statement assumes [the hM condition](hyp:hM). [This is the stated conclusion](goal). -/
-- @node: coarseTent_design_overlap
lemma coarseTent_design_overlap (M : ℕ) (hM : 0 < M)
    (σ τ : Fin (M/2) → Bool) :
    (∫ x : unitInterval, coarseTent M σ x * coarseTent M τ x ∂design) =
      (2/(3*(M:ℝ))) * Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign σ τ := by
  rw [integral_design_eq_interval (fun x => coarseTent M σ x * coarseTent M τ x),
    coarseTent_interval_overlap M hM]
  rfl

/-- A normalized inner-sign product stays in the unit interval. [This is the stated conclusion](goal). -/
-- @node: innerSign_abs_le_rank
lemma innerSign_abs_le_rank (k : ℕ) (σ τ : Fin k → Bool) :
    |Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign σ τ| ≤ (k:ℝ) := by
  unfold Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign
  calc
    _ ≤ ∑ j : Fin k, |(if σ j then (1:ℝ) else -1)*(if τ j then (1:ℝ) else -1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      have he (j : Fin k) :
          |(if σ j then (1:ℝ) else -1)*(if τ j then (1:ℝ) else -1)| = 1 := by
        cases σ j <;> cases τ j <;> norm_num
      simp_rw [he]
      simp

/-- The full-record overlap bases remain positive for every pair of sign fields. This statement assumes [the hk condition](hyp:hk), [the hρ condition](hyp:hρ). [This is the stated conclusion](goal). -/
-- @node: paired_sign_overlap_base_nonneg
lemma paired_sign_overlap_base_nonneg (k : ℕ) (hk : 0 < k) (ρ : ℝ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (σ τ : Fin k → Bool) :
    0 ≤ 1 + ρ*Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign σ τ/(k:ℝ) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hi := (abs_le.mp (innerSign_abs_le_rank k σ τ)).1
  have hm := mul_le_mul_of_nonneg_left hi hρ.1
  have hd : -ρ ≤ ρ*Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign σ τ/(k:ℝ) := by
    apply (le_div_iff₀ hkR).2
    nlinarith
  linarith [hρ.2]

/-- Uniform signs and iid overlap powers give the roadmap's Gaussian exponent. This statement assumes [the hk condition](hyp:hk), [the hρ condition](hyp:hρ). [This is the stated conclusion](goal). -/
-- @node: paired_sign_overlap_average_le
lemma paired_sign_overlap_average_le (k n : ℕ) (hk : 0 < k) (ρ : ℝ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    (∑ σ : Fin k → Bool, ∑ τ : Fin k → Bool,
      (1+ρ*Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign σ τ/(k:ℝ))^n) /
        (Fintype.card (Fin k → Bool):ℝ)^2 ≤ Real.exp (((n:ℝ)*ρ)^2/(2*(k:ℝ))) := by
  haveI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  simpa using Causalean.Stat.Minimax.Mixture.SignOverlap.uniform_sign_twoPower_le_exp
    k n 0 ρ 0 (paired_sign_overlap_base_nonneg k hk ρ hρ) (by intro σ τ; simp)

/-- The prescribed rarity and paired rank bound the finite-sign likelihood average. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tent_sign_overlap_average_le
lemma tent_sign_overlap_average_le (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    (∑ σ : Fin (tentRank n v/2) → Bool, ∑ τ : Fin (tentRank n v/2) → Bool,
      (1+(tentRarity n v*kappa0^2/6)*
        Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign σ τ/(tentRank n v/2:ℕ))^n) /
        (Fintype.card (Fin (tentRank n v/2) → Bool):ℝ)^2 ≤ Real.exp (kappa0^4/36) := by
  have hk : 0 < tentRank n v/2 := by have := (tentRank_bounds v hv n hn).1; omega
  have hρ : 0 ≤ tentRarity n v*kappa0^2/6 ∧ tentRarity n v*kappa0^2/6 ≤ 1 := by
    have hε := (tent_mark_parameters v hv n hn).1
    norm_num [kappa0] at *
    constructor <;> linarith
  apply (paired_sign_overlap_average_le _ n hk _ hρ).trans
  apply Real.exp_le_exp.mpr
  have heven : 2*(tentRank n v/2) = tentRank n v := by unfold tentRank; omega
  have hkR : (0:ℝ) < ((tentRank n v/2 : ℕ):ℝ) := by exact_mod_cast hk
  have hN : (tentRank n v:ℝ) = 2*(tentRank n v/2:ℕ) := by exact_mod_cast heven.symm
  have hh := tent_likelihood_exponent_bound v hv n hn
  have hid : ((n:ℝ)*(tentRarity n v*kappa0^2/6))^2/(2*(tentRank n v/2:ℕ)) =
      (kappa0^4/36)*((n:ℝ)^2*tentRarity n v^2*tentH n v) := by
    unfold tentH
    rw [hN]
    field_simp
    <;> ring
  rw [hid]
  exact mul_le_of_le_one_right (by positivity) hh

end CausalSmith.Stat.FinitepHomogeneityDensegamma
