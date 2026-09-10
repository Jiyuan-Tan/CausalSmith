import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TMechanismLoss
import Mathlib.Probability.ProbabilityMassFunction.Binomial

/-! # Cluster-count penalty of Bernoulli labels -/

open scoped BigOperators
open Set

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

-- @node: endpoint_power_lower
/-- The two endpoint masses of a Bernoulli sum are minimized at one half. -/
theorem endpoint_power_lower (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    2 ^ (1 - (n : ℤ)) ≤ x ^ n + (1 - x) ^ n := by
  have h := add_pow_le hx0 (sub_nonneg.mpr hx1) n
  norm_num at h
  have hp : 0 < (2 : ℝ) ^ (n - 1) := by positivity
  rw [show (2 : ℝ) ^ (1 - (n : ℤ)) = ((2 : ℝ) ^ (n - 1))⁻¹ by
    rw [show 1 - (n : ℤ) = -((n - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]]
  rw [← one_div]
  exact (div_le_iff₀ hp).2 (by simpa [mul_comm] using h)

-- @node: maximum_active_column_mass_le_endpoint_bound
/-- A proper menu of interior counts misses both binomial endpoint events. -/
lemma maximum_active_column_mass_le_endpoint_bound {n K : ℕ} [NeZero n] [NeZero K]
    (A : Finset (Fin K)) (m : Fin K → ℕ) (p : Fin K → ℝ)
    (hmenu : WellFormedMenu n K m) :
    maximumActiveColumnMass A (hitMatrix n m p).1 ≤ 1 - 2 ^ (1 - (n : ℤ)) := by
  let f := fun (l : Fin K) (i : ℕ) => (Nat.choose n i : ℝ) *
    saturation n m l ^ i * (1 - saturation n m l) ^ (n - i)
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hm : ∀ k, 1 ≤ m k ∧ m k ≤ n - 1 := hmenu.2.2.2.1
  have hpi : ∀ l, saturation n m l ∈ Icc (0 : ℝ) 1 := by
    intro l
    constructor
    · exact div_nonneg (by positivity) (by positivity)
    · rw [saturation, div_le_one (by positivity)]
      have hmn : m l ≤ n := (hm l).2.trans (Nat.sub_le n 1)
      exact_mod_cast hmn
  have hcol : ∀ l, ∑ k ∈ A, (hitMatrix n m p).1 k l ≤
      1 - 2 ^ (1 - (n : ℤ)) := by
    intro l
    let target := A.image m
    let interior := ((Finset.range (n + 1)).erase 0).erase n
    have hinj : Set.InjOn m (A : Set (Fin K)) := hmenu.2.2.2.2.injective.injOn
    have htarget : target ⊆ interior := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
      simp only [interior, Finset.mem_erase, Finset.mem_range]
      have hmk := hm k
      exact ⟨by omega, by omega, by omega⟩
    have hf_nonneg : ∀ i ∈ interior, i ∉ target → 0 ≤ f l i := by
      intro i hi hnot
      dsimp [f]
      exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (hpi l).1 _))
        (pow_nonneg (sub_nonneg.mpr (hpi l).2) _)
    have hsum_le : ∑ i ∈ target, f l i ≤ ∑ i ∈ interior, f l i :=
      Finset.sum_le_sum_of_subset_of_nonneg htarget hf_nonneg
    have htarget_sum : ∑ k ∈ A, (hitMatrix n m p).1 k l = ∑ i ∈ target, f l i := by
      rw [Finset.sum_image hinj]
      rfl
    have hzero : 0 ∈ Finset.range (n + 1) := by simp
    have hnmem : n ∈ (Finset.range (n + 1)).erase 0 := by simp [Nat.ne_of_gt hn]
    have hfull : ∑ i ∈ Finset.range (n + 1), f l i = 1 := by
      have hadd := add_pow (saturation n m l) (1 - saturation n m l) n
      norm_num at hadd
      simpa [f, mul_assoc, mul_left_comm, mul_comm] using hadd.symm
    have hsplit : ∑ i ∈ Finset.range (n + 1), f l i =
        f l 0 + f l n + ∑ i ∈ interior, f l i := by
      have hz := Finset.sum_erase_add (Finset.range (n + 1)) (f l) hzero
      have hN := Finset.sum_erase_add ((Finset.range (n + 1)).erase 0) (f l) hnmem
      dsimp [interior]
      linarith
    have hend : 2 ^ (1 - (n : ℤ)) ≤ f l 0 + f l n := by
      simpa [f, Nat.choose_self, Nat.choose_zero_right, add_comm] using
        endpoint_power_lower n hn (saturation n m l) (hpi l).1 (hpi l).2
    rw [htarget_sum]
    linarith
  unfold maximumActiveColumnMass
  apply Finset.sup'_le
  intro l hl
  exact hcol l

-- @node: prop:mechanism-cluster-count
/-- Matching the exact-count leading regret forces the displayed cluster-count
inflation, with the universal exact-hit column bound. -/
theorem mechanism_cluster_count {n K : ℕ} [NeZero n] [NeZero K]
    (A : Finset (Fin K)) (m : Fin K → ℕ) (v p : Fin K → ℝ)
    (CB CCR : ℝ) (hmenu : WellFormedMenu n K m) (hA : 2 ≤ A.card)
    (hv : ∀ k ∈ A, 0 < v k) (hp : InSimplex p) :
    let B := (hitMatrix n m p).1
    let RB := (faceMechanismValues B A v).1
    let RCR := (faceMechanismValues B A v).2
    let sMax := maximumActiveColumnMass A B
    0 < CB → 0 < CCR → 0 < RCR →
    RB / Real.sqrt CB ≤ RCR / Real.sqrt CCR →
    CB / CCR ≥ (RB / RCR) ^ 2 ∧
      (RB / RCR) ^ 2 ≥ 1 / sMax ∧
      1 / sMax ≥ 1 / (1 - 2 ^ (1 - (n : ℤ))) ∧
      ((RB / RCR) ^ 2 = 1 / sMax ↔
        ∃ pStar, InSimplex pStar ∧
          (∀ l, pStar l > 0 → ∑ k ∈ A, B k l = sMax) ∧
          gaussianGlobalValueReal A v (normalizedActiveHits A B pStar) = RCR) := by
  dsimp
  intro hCB hCCR hRCR hbudget
  rcases mechanism_loss A m v p hmenu hA hv hp with
    ⟨hscale, hmass, hmass_le, hsmax_lt, hratio, hpower, heq⟩
  have hsmax : 0 < maximumActiveColumnMass A (hitMatrix n m p).1 :=
    hmass.trans_le hmass_le
  have hRB_ratio : 0 < (faceMechanismValues (hitMatrix n m p).1 A v).1 /
      (faceMechanismValues (hitMatrix n m p).1 A v).2 :=
    lt_of_lt_of_le (lt_trans (by norm_num) hpower) hratio
  have hRB : 0 < (faceMechanismValues (hitMatrix n m p).1 A v).1 :=
    ((div_pos_iff.mp hRB_ratio).resolve_right fun hneg => (not_lt_of_ge hRCR.le) hneg.2).1
  have hsCB : 0 < Real.sqrt CB := Real.sqrt_pos.2 hCB
  have hsCCR : 0 < Real.sqrt CCR := Real.sqrt_pos.2 hCCR
  have hcross : (faceMechanismValues (hitMatrix n m p).1 A v).1 * Real.sqrt CCR ≤
      (faceMechanismValues (hitMatrix n m p).1 A v).2 * Real.sqrt CB :=
    (div_le_div_iff₀ hsCB hsCCR).mp hbudget
  have hcross_sq := (sq_le_sq₀ (mul_nonneg hRB.le hsCCR.le)
    (mul_nonneg hRCR.le hsCB.le)).2 hcross
  have hbudget_sq : ((faceMechanismValues (hitMatrix n m p).1 A v).1 /
      (faceMechanismValues (hitMatrix n m p).1 A v).2) ^ 2 ≤ CB / CCR := by
    rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hRCR) hCCR]
    simpa [mul_pow, Real.sq_sqrt hCB.le, Real.sq_sqrt hCCR.le,
      mul_comm, mul_left_comm, mul_assoc] using hcross_sq
  have hrpow_sq : (maximumActiveColumnMass A (hitMatrix n m p).1 ^ (-1 / 2 : ℝ)) ^ 2 =
      1 / maximumActiveColumnMass A (hitMatrix n m p).1 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hsmax.le]
    norm_num [Real.rpow_neg_one, one_div]
  have hmechanism_sq : 1 / maximumActiveColumnMass A (hitMatrix n m p).1 ≤
      ((faceMechanismValues (hitMatrix n m p).1 A v).1 /
        (faceMechanismValues (hitMatrix n m p).1 A v).2) ^ 2 := by
    rw [← hrpow_sq]
    exact (sq_le_sq₀ (by positivity) hRB_ratio.le).2 hratio
  have hsmax_bound := maximum_active_column_mass_le_endpoint_bound A m p hmenu
  have hendpoint_pos : (0 : ℝ) < 1 - (2 : ℝ) ^ (1 - (n : ℤ)) := by
    exact hsmax.trans_le hsmax_bound
  have hrecip : (1 : ℝ) / (1 - (2 : ℝ) ^ (1 - (n : ℤ))) ≤
      1 / maximumActiveColumnMass A (hitMatrix n m p).1 :=
    one_div_le_one_div_of_le hsmax hsmax_bound
  refine ⟨hbudget_sq, hmechanism_sq, hrecip, ?_⟩
  rw [← hrpow_sq]
  constructor
  · intro hsquares
    apply heq.mp
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp hsquares |>.resolve_right (by
      intro hneg
      have := hRB_ratio
      rw [hneg] at this
      linarith [hpower])
  · intro hcrit
    rw [heq.mpr hcrit]
-- @realizes C_B(positive Bernoulli-label cluster budget)
-- @realizes C_{CR}(positive exact-count cluster budget)

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
