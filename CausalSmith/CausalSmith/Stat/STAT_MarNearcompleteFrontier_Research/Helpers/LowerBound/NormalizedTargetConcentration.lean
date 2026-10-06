module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.NormalizedLagrange
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.NormalizedScale
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.NormalizedTarget
public import Causalean.Mathlib.Algebra.BigOperators.FiniteProductMoments
public import Causalean.Stat.Concentration.Chebyshev

/-! # Target concentration leaves for the normalized paired prior -/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open Causalean.Mathlib.Algebra.BigOperators

open MeasureTheory
open Polynomial
open ProbabilityTheory
open scoped ENNReal

-- @node: lagrangeAtZero_sum_one
/-- The cardinal Lagrange coefficients at zero sum to one. Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma lagrangeAtZero_sum_one (n : ℕ) :
    (∑ i : Fin (priorK n), lagrangeAtZero n i) = 1 := by
  have hinj : Set.InjOn (interpolationNode n)
      (Finset.univ : Finset (Fin (priorK n))) := by
    intro i _ j _ hij
    exact interpolationNode_injective n hij
  have hdegree : ((1 : ℝ[X]).degree <
      ((Finset.univ : Finset (Fin (priorK n))).card : WithBot ℕ)) := by
    simp
    exact lt_of_lt_of_le (by omega) (priorK_ge_two n)
  have hinterp := Lagrange.eq_interpolate (f := (1 : ℝ[X])) hinj hdegree
  have heval := congrArg (fun p : ℝ[X] => p.eval 0) hinterp
  simpa [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    lagrangeAtZero] using heval.symm

-- @node: signedNodeWeight_sum
/-- The normalized signed interpolation coefficients retain total mass
`1 / lagrangeNorm`. Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma signedNodeWeight_sum (n : ℕ) :
    (∑ i : Fin (priorK n), signedNodeWeight n i) = 1 / lagrangeNorm n := by
  simp_rw [signedNodeWeight, ← Finset.sum_div]
  rw [lagrangeAtZero_sum_one]

-- @node: signedNodeWeight_abs_sum
/-- The absolute normalized interpolation coefficients have total mass one. Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma signedNodeWeight_abs_sum (n : ℕ) :
    (∑ i : Fin (priorK n), |signedNodeWeight n i|) = 1 := by
  have hnorm : 0 ≤ lagrangeNorm n := by
    unfold lagrangeNorm
    positivity
  have hnorm_ne : lagrangeNorm n ≠ 0 := by
    intro hz
    have hsum := lagrangeAtZero_sum_one n
    have habs : |∑ i : Fin (priorK n), lagrangeAtZero n i| ≤
        ∑ i : Fin (priorK n), |lagrangeAtZero n i| := Finset.abs_sum_le_sum_abs _ _
    rw [hsum, abs_one] at habs
    have : (1 : ℝ) ≤ lagrangeNorm n := by simpa [lagrangeNorm] using habs
    rw [hz] at this
    norm_num at this
  simp only [signedNodeWeight, abs_div, abs_of_nonneg hnorm, ← Finset.sum_div]
  rw [show (∑ i : Fin (priorK n), |lagrangeAtZero n i|) = lagrangeNorm n by rfl]
  exact div_self hnorm_ne

-- @node: latentWeightedSign_mean
/-- The one-pair signed mass has the exact mean used in equation (18). Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma latentWeightedSign_mean (n : ℕ) :
    (∑ z : Latent n, latentWeight n z * (latentP n z * latentZ n z)) =
      priorH n * priorB n / lagrangeNorm n := by
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, latentWeight, latentP, latentZ, zero_mul,
    mul_zero, add_zero]
  calc
    (∑ i : Fin (priorK n),
        priorH n * |signedNodeWeight n i| / interpolationNode n i *
          (priorB n * interpolationNode n i *
            if 0 ≤ signedNodeWeight n i then 1 else -1)) =
        ∑ i : Fin (priorK n),
          priorH n * priorB n * signedNodeWeight n i := by
      apply Finset.sum_congr rfl
      intro i _
      have hnode : interpolationNode n i ≠ 0 :=
        ne_of_gt (latentWeight_node_pos n i)
      by_cases hw : 0 ≤ signedNodeWeight n i
      · simp only [if_pos hw, abs_of_nonneg hw]
        field_simp [hnode]
      · have hw' : signedNodeWeight n i ≤ 0 := le_of_not_ge hw
        simp only [if_neg hw, abs_of_nonpos hw']
        field_simp [hnode]
    _ = priorH n * priorB n *
        (∑ i : Fin (priorK n), signedNodeWeight n i) := by
      rw [Finset.mul_sum]
    _ = priorH n * priorB n / lagrangeNorm n := by
      rw [signedNodeWeight_sum]
      ring

-- @node: interpolationNode_le_one_target
/-- Every interpolation node is at most the right endpoint one. Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `i`](hyp:i). -/
lemma interpolationNode_le_one_target (n : ℕ) (i : Fin (priorK n)) :
    interpolationNode n i ≤ 1 := by
  have hh := priorH_le_one_for_normalization n
  have hc := Real.cos_le_one
    ((i : ℝ) * Real.pi / ((priorK n - 1 : ℕ) : ℝ))
  unfold interpolationNode
  nlinarith

-- @node: latentWeightedSign_second_moment_le
/-- The one-pair signed latent mass has the scale-squared second-moment bound. Given [the specified input `n`](hyp:n), [the specified input `hn`](hyp:hn), [the stated mathematical conclusion holds](goal). -/
lemma latentWeightedSign_second_moment_le (n : ℕ) (hn : 1 ≤ n) :
    (∑ z : Latent n,
      latentWeight n z * (latentP n z * latentZ n z) ^ 2) ≤
        1 / (1024 ^ 2 * (n : ℝ) ^ 2) := by
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, latentWeight, latentP, latentZ, zero_mul,
    mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  calc
    (∑ i : Fin (priorK n),
        priorH n * |signedNodeWeight n i| / interpolationNode n i *
          (priorB n * interpolationNode n i *
            (if 0 ≤ signedNodeWeight n i then 1 else -1)) ^ 2) =
        ∑ i : Fin (priorK n), priorH n * priorB n ^ 2 *
          |signedNodeWeight n i| * interpolationNode n i := by
      apply Finset.sum_congr rfl
      intro i _
      have hnode : interpolationNode n i ≠ 0 :=
        ne_of_gt (latentWeight_node_pos n i)
      split_ifs <;> field_simp [hnode] <;> ring
    _ ≤ ∑ i : Fin (priorK n),
        priorH n * priorB n ^ 2 * |signedNodeWeight n i| := by
      apply Finset.sum_le_sum
      intro i _
      have hh : 0 ≤ priorH n := by
        unfold priorH
        positivity
      have hcoef : 0 ≤ priorH n * priorB n ^ 2 *
          |signedNodeWeight n i| :=
        mul_nonneg (mul_nonneg hh (sq_nonneg _)) (abs_nonneg _)
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (interpolationNode_le_one_target n i) hcoef
    _ = priorH n * priorB n ^ 2 := by
      rw [← Finset.mul_sum, signedNodeWeight_abs_sum]
      ring
    _ = 1 / (1024 ^ 2 * (n : ℝ) ^ 2) := by
      have hk : (priorK n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by omega) (priorK_ge_two n)))
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      unfold priorH priorB
      field_simp [hk, hn0]

-- @node: latentMass_mean
/-- The one-pair latent mass has mean `priorH * priorB`. Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma latentMass_mean (n : ℕ) :
    (∑ z : Latent n, latentWeight n z * latentP n z) =
      priorH n * priorB n := by
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, latentWeight, latentP, mul_zero, add_zero]
  calc
    (∑ i : Fin (priorK n),
        priorH n * |signedNodeWeight n i| / interpolationNode n i *
          (priorB n * interpolationNode n i)) =
        ∑ i : Fin (priorK n),
          priorH n * priorB n * |signedNodeWeight n i| := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [ne_of_gt (latentWeight_node_pos n i)]
    _ = priorH n * priorB n := by
      rw [← Finset.mul_sum, signedNodeWeight_abs_sum]
      ring

-- @node: latentMass_second_moment_le
/-- The one-pair latent mass has the same scale-squared second-moment envelope. Given [the specified input `n`](hyp:n), [the specified input `hn`](hyp:hn), [the stated mathematical conclusion holds](goal). -/
lemma latentMass_second_moment_le (n : ℕ) (hn : 1 ≤ n) :
    (∑ z : Latent n, latentWeight n z * latentP n z ^ 2) ≤
      1 / (1024 ^ 2 * (n : ℝ) ^ 2) := by
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, latentWeight, latentP, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, add_zero]
  calc
    (∑ i : Fin (priorK n),
        priorH n * |signedNodeWeight n i| / interpolationNode n i *
          (priorB n * interpolationNode n i) ^ 2) =
        ∑ i : Fin (priorK n), priorH n * priorB n ^ 2 *
          |signedNodeWeight n i| * interpolationNode n i := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [ne_of_gt (latentWeight_node_pos n i)]
    _ ≤ ∑ i : Fin (priorK n),
        priorH n * priorB n ^ 2 * |signedNodeWeight n i| := by
      apply Finset.sum_le_sum
      intro i _
      have hh : 0 ≤ priorH n := by unfold priorH; positivity
      have hcoef : 0 ≤ priorH n * priorB n ^ 2 * |signedNodeWeight n i| :=
        mul_nonneg (mul_nonneg hh (sq_nonneg _)) (abs_nonneg _)
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (interpolationNode_le_one_target n i) hcoef
    _ = priorH n * priorB n ^ 2 := by
      rw [← Finset.mul_sum, signedNodeWeight_abs_sum]
      ring
    _ = 1 / (1024 ^ 2 * (n : ℝ) ^ 2) := by
      have hk : (priorK n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by omega) (priorK_ge_two n)))
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      unfold priorH priorB
      field_simp [hk, hn0]

-- @node: latentWeight_nonneg_target
/-- Every scalar latent weight is nonnegative. Given [the specified input `n`](hyp:n), [the specified input `z`](hyp:z), [the stated mathematical conclusion holds](goal). -/
lemma latentWeight_nonneg_target (n : ℕ) (z : Latent n) :
    0 ≤ latentWeight n z := by
  cases z with
  | inl i =>
      exact div_nonneg
        (mul_nonneg (by unfold priorH; positivity) (abs_nonneg _))
        (le_of_lt (latentWeight_node_pos n i))
  | inr _ =>
      simp only [latentWeight]
      apply sub_nonneg.mpr
      calc
        (∑ i : Fin (priorK n),
            priorH n * |signedNodeWeight n i| / interpolationNode n i) ≤
            ∑ i : Fin (priorK n), |signedNodeWeight n i| := by
          apply Finset.sum_le_sum
          intro i _
          apply (div_le_iff₀ (latentWeight_node_pos n i)).mpr
          nlinarith [latentWeight_node_lower n i,
            abs_nonneg (signedNodeWeight n i)]
        _ = 1 := signedNodeWeight_abs_sum n

-- @node: oneLatentLaw_toReal
/-- The real mass function of the scalar latent PMF is `latentWeight`. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `z`](hyp:z), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma oneLatentLaw_toReal (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (z : Latent n) :
    (oneLatentLaw n d q hn hd hq z).toReal = latentWeight n z := by
  rw [oneLatentLaw, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (latentWeight_nonneg_target n z)]

/-- For [a sample size](hyp:n), [every singleton latent state is measurable](goal). -/
instance latentMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (Latent n) where
  measurableSet_singleton z := by
    cases z with
    | inl i =>
        simpa only [Set.image_singleton] using
          (measurableSet_singleton i).inl_image (β := Unit)
    | inr u =>
        simpa only [Set.image_singleton] using
          (measurableSet_singleton u).inr_image (α := Fin (priorK n))

-- @node: thetaLaw_integral_fst
/-- Integrating a statistic of the latent coordinates under `thetaLaw`
reduces to the corresponding finite product-weighted sum. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `f`](hyp:f). -/
lemma thetaLaw_integral_fst (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (f : (Fin (pairCount n d) → Latent n) → ℝ) :
    (∫ θ, f θ.1 ∂(thetaLaw n d q hn hd hq).toMeasure) =
      ∑ u : Fin (pairCount n d) → Latent n,
        (∏ j : Fin (pairCount n d), latentWeight n (u j)) * f u := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, thetaLaw, PMF.ofFintype_apply, thetaWeight,
    ENNReal.toReal_prod, ENNReal.toReal_mul, oneLatentLaw_toReal,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsign : (∑ _s : Fin (pairCount n d) → Bool,
      (1 / 2 : ℝ≥0∞).toReal ^ pairCount n d) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow]
    norm_num
    rw [← mul_pow]
    simp
  calc
    (∑ _s : Fin (pairCount n d) → Bool,
        (∏ x, latentWeight n (u x)) *
          (1 / 2 : ℝ≥0∞).toReal ^ pairCount n d * f u) =
        (∑ _s : Fin (pairCount n d) → Bool,
          (1 / 2 : ℝ≥0∞).toReal ^ pairCount n d) *
            ((∏ x, latentWeight n (u x)) * f u) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by rw [hsign]; ring



-- @node: pairedFullLaw_tau_separated
/-- A lower bound on the normalized signed latent mass gives the two pointwise
target inequalities for the opposite prior signs. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `c`](hyp:c), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `θ`](hyp:θ). Given [the specified input `hq`](hyp:hq), [the specified input `hshift`](hyp:hshift). -/
lemma pairedFullLaw_tau_separated (n d : ℕ) (q c : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (θ : Theta n d)
    (hshift : c * gScale n d q ≤
      delta q / (16 * q) * pairedWeightedSign n d θ /
        normalizationJ n d θ) :
    tau (pairedFullLaw n d q (-1) hn hd hq (by norm_num) θ) ≤
        baseMean q - c * gScale n d q ∧
      baseMean q + c * gScale n d q ≤
        tau (pairedFullLaw n d q 1 hn hd hq (by norm_num) θ) := by
  have hminus := pairedFullLaw_tau_exact n d q (-1) hn hd hq (Or.inl rfl) θ
  have hplus := pairedFullLaw_tau_exact n d q 1 hn hd hq (Or.inr rfl) θ
  constructor
  · rw [hminus]
    have h := sub_le_sub_left hshift (baseMean q)
    convert h using 1 <;> ring
  · rw [hplus]
    norm_num
    linarith

-- @node: pairedWeightedSign_mean
/-- Equation (18), first part: the signed latent mass has the displayed mean. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma pairedWeightedSign_mean (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    ∫ θ, pairedWeightedSign n d θ ∂(thetaLaw n d q hn hd hq).toMeasure =
      (pairCount n d : ℝ) * priorH n * priorB n / lagrangeNorm n := by
  let w : Latent n → ℝ := latentWeight n
  let X : Latent n → ℝ := fun z => latentP n z * latentZ n z
  have hwsum : ∑ z : Latent n, w z = 1 := by
    simp only [w, Fintype.sum_sum_type, Fintype.sum_unique, latentWeight]
    ring
  have hμ : ∑ z : Latent n, w z * X z =
      priorH n * priorB n / lagrangeNorm n := by
    simpa only [w, X] using latentWeightedSign_mean n
  have hmarg (j : Fin (pairCount n d)) :
      ∑ u : Fin (pairCount n d) → Latent n,
        (∏ k : Fin (pairCount n d), w (u k)) * X (u j) =
          ∑ z : Latent n, w z * X z := by
    have hfactor (u : Fin (pairCount n d) → Latent n) :
        (∏ k : Fin (pairCount n d), w (u k)) * X (u j) =
          ∏ k : Fin (pairCount n d),
            if k = j then w (u k) * X (u k) else w (u k) := by
      calc
        _ = (∏ k : Fin (pairCount n d), w (u k)) *
            ∏ k : Fin (pairCount n d), if k = j then X (u k) else 1 := by
          simp
        _ = ∏ k : Fin (pairCount n d),
            w (u k) * (if k = j then X (u k) else 1) := by
          rw [Finset.prod_mul_distrib]
        _ = _ := by simp
    calc
      _ = ∑ u : Fin (pairCount n d) → Latent n,
          ∏ k : Fin (pairCount n d),
            if k = j then w (u k) * X (u k) else w (u k) := by
        apply Finset.sum_congr rfl
        intro u _
        exact hfactor u
      _ = ∏ k : Fin (pairCount n d),
          ∑ z : Latent n, if k = j then w z * X z else w z := by
        exact (Fintype.prod_sum (fun k : Fin (pairCount n d) => fun z : Latent n =>
          if k = j then w z * X z else w z)).symm
      _ = ∑ z : Latent n, w z * X z := by
        simp [hwsum, Finset.prod_ite_eq']
  rw [show (fun θ : Theta n d => pairedWeightedSign n d θ) =
      (fun θ => ∑ j : Fin (pairCount n d),
        latentP n (θ.1 j) * latentZ n (θ.1 j)) by
    funext θ
    exact pairedWeightedSign_apply n d θ]
  rw [thetaLaw_integral_fst n d q hn hd hq
    (fun u => ∑ j : Fin (pairCount n d), latentP n (u j) * latentZ n (u j))]
  calc
    (∑ u : Fin (pairCount n d) → Latent n,
        (∏ j : Fin (pairCount n d), latentWeight n (u j)) *
          ∑ j : Fin (pairCount n d), latentP n (u j) * latentZ n (u j)) =
      ∑ j : Fin (pairCount n d),
        ∑ u : Fin (pairCount n d) → Latent n,
          (∏ k : Fin (pairCount n d), w (u k)) * X (u j) := by
        simp only [w, X, Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = ∑ _j : Fin (pairCount n d),
        (priorH n * priorB n / lagrangeNorm n) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hmarg j, hμ]
    _ = (pairCount n d : ℝ) * priorH n * priorB n / lagrangeNorm n := by
      simp
      ring

-- @node: pairedWeightedSign_variance_bound
/-- Equation (18), second part: the signed latent mass has the required variance bound. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma pairedWeightedSign_variance_bound (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    ∫ θ, (pairedWeightedSign n d θ -
      (pairCount n d : ℝ) * priorH n * priorB n / lagrangeNorm n) ^ 2
        ∂(thetaLaw n d q hn hd hq).toMeasure ≤
      (pairCount n d : ℝ) / (1024 ^ 2 * (n : ℝ) ^ 2) := by
  let w : Latent n → ℝ := latentWeight n
  let X : Latent n → ℝ := fun z => latentP n z * latentZ n z
  let μ : ℝ := priorH n * priorB n / lagrangeNorm n
  let c : Latent n → ℝ := fun z => X z - μ
  have hwsum : ∑ z : Latent n, w z = 1 := by
    simp only [w, Fintype.sum_sum_type, Fintype.sum_unique, latentWeight]
    ring
  have hμ : ∑ z : Latent n, w z * X z = μ := by
    simpa only [w, X, μ] using latentWeightedSign_mean n
  have hcenter : ∑ z : Latent n, w z * c z = 0 := by
    simp only [c, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hμ, hwsum]
    ring
  have hcell : ∑ z : Latent n, w z * c z ^ 2 ≤
      1 / (1024 ^ 2 * (n : ℝ) ^ 2) := by
    have hpoint (z : Latent n) :
        w z * c z ^ 2 = w z * X z ^ 2 -
          2 * μ * (w z * X z) + μ ^ 2 * w z := by
      dsimp [c]
      ring
    calc
      _ = (∑ z : Latent n, w z * X z ^ 2) - 2 * μ ^ 2 + μ ^ 2 := by
        simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
        rw [hμ, hwsum]
        ring
      _ ≤ ∑ z : Latent n, w z * X z ^ 2 := by
        nlinarith [sq_nonneg μ]
      _ ≤ 1 / (1024 ^ 2 * (n : ℝ) ^ 2) := by
        simpa only [w, X] using latentWeightedSign_second_moment_le n hn
  rw [show (fun θ : Theta n d =>
      (pairedWeightedSign n d θ -
        (pairCount n d : ℝ) * priorH n * priorB n / lagrangeNorm n) ^ 2) =
      (fun θ => (∑ j : Fin (pairCount n d), c (θ.1 j)) ^ 2) by
    funext θ
    rw [pairedWeightedSign_apply]
    simp only [c, X, μ, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring]
  rw [thetaLaw_integral_fst n d q hn hd hq
    (fun u => (∑ j : Fin (pairCount n d), c (u j)) ^ 2)]
  rw [finiteProduct_centered_sum_sq w c hwsum hcenter]
  have hmul := mul_le_mul_of_nonneg_left hcell
    (show 0 ≤ (pairCount n d : ℝ) by positivity)
  simpa only [Fintype.card_fin, div_eq_mul_inv, one_mul] using hmul

-- @node: normalizationJ_moments
/-- Equation (19): the random normalizer has mean one and controlled variance. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma normalizationJ_moments (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∫ θ, normalizationJ n d θ ∂(thetaLaw n d q hn hd hq).toMeasure) = 1 ∧
    (∫ θ, (normalizationJ n d θ - 1) ^ 2
      ∂(thetaLaw n d q hn hd hq).toMeasure) ≤
        4 * (pairCount n d : ℝ) / (1024 ^ 2 * (n : ℝ) ^ 2) := by
  let w : Latent n → ℝ := latentWeight n
  let X : Latent n → ℝ := latentP n
  let μ : ℝ := priorH n * priorB n
  let c : Latent n → ℝ := fun z => X z - μ
  have hwsum : ∑ z : Latent n, w z = 1 := by
    simp only [w, Fintype.sum_sum_type, Fintype.sum_unique, latentWeight]
    ring
  have hμ : ∑ z : Latent n, w z * X z = μ := by
    simpa only [w, X, μ] using latentMass_mean n
  have hcenter : ∑ z : Latent n, w z * c z = 0 := by
    simp only [c, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hμ, hwsum]
    ring
  have hcell : ∑ z : Latent n, w z * c z ^ 2 ≤
      1 / (1024 ^ 2 * (n : ℝ) ^ 2) := by
    have hpoint (z : Latent n) :
        w z * c z ^ 2 = w z * X z ^ 2 -
          2 * μ * (w z * X z) + μ ^ 2 * w z := by
      dsimp [c]
      ring
    calc
      _ = (∑ z : Latent n, w z * X z ^ 2) - 2 * μ ^ 2 + μ ^ 2 := by
        simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
        rw [hμ, hwsum]
        ring
      _ ≤ ∑ z : Latent n, w z * X z ^ 2 := by
        nlinarith [sq_nonneg μ]
      _ ≤ 1 / (1024 ^ 2 * (n : ℝ) ^ 2) := by
        simpa only [w, X] using latentMass_second_moment_le n hn
  have hJfun : (fun θ : Theta n d => normalizationJ n d θ) =
      (fun θ => 1 + 2 * ∑ j : Fin (pairCount n d), c (θ.1 j)) := by
    funext θ
    unfold normalizationJ fillerMass
    simp only [c, X, μ, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  constructor
  · rw [hJfun]
    rw [thetaLaw_integral_fst n d q hn hd hq
      (fun u => 1 + 2 * ∑ j : Fin (pairCount n d), c (u j))]
    have hprod : (∑ u : Fin (pairCount n d) → Latent n,
        ∏ j : Fin (pairCount n d), w (u j)) = 1 := by
      calc
        _ = ∏ _j : Fin (pairCount n d), ∑ z : Latent n, w z := by
          exact (Fintype.prod_sum (fun _j : Fin (pairCount n d) => w)).symm
        _ = 1 := by simp [hwsum]
    have hsum := finiteProduct_sum_mean (I := Fin (pairCount n d))
      (A := Latent n) w c hwsum
    simp only [Fintype.card_fin, hcenter, mul_zero] at hsum
    calc
      (∑ u : Fin (pairCount n d) → Latent n,
          (∏ j : Fin (pairCount n d), latentWeight n (u j)) *
            (1 + 2 * ∑ j : Fin (pairCount n d), c (u j))) =
          (∑ u : Fin (pairCount n d) → Latent n,
            ∏ j : Fin (pairCount n d), w (u j)) +
          2 * ∑ u : Fin (pairCount n d) → Latent n,
            (∏ j : Fin (pairCount n d), w (u j)) *
              ∑ j : Fin (pairCount n d), c (u j) := by
        calc
          _ = ∑ u : Fin (pairCount n d) → Latent n,
              ((∏ j : Fin (pairCount n d), w (u j)) +
                2 * ((∏ j : Fin (pairCount n d), w (u j)) *
                  ∑ j : Fin (pairCount n d), c (u j))) := by
            apply Finset.sum_congr rfl
            intro u _
            simp only [w]
            ring
          _ = (∑ u : Fin (pairCount n d) → Latent n,
                ∏ j : Fin (pairCount n d), w (u j)) +
              ∑ u : Fin (pairCount n d) → Latent n,
                2 * ((∏ j : Fin (pairCount n d), w (u j)) *
                  ∑ j : Fin (pairCount n d), c (u j)) := by
            rw [Finset.sum_add_distrib]
          _ = _ := by rw [Finset.mul_sum]
      _ = 1 := by rw [hprod, hsum]; ring
  · rw [show (fun θ : Theta n d => (normalizationJ n d θ - 1) ^ 2) =
        (fun θ => (2 * ∑ j : Fin (pairCount n d), c (θ.1 j)) ^ 2) by
      funext θ
      rw [congrFun hJfun θ]
      ring]
    rw [thetaLaw_integral_fst n d q hn hd hq
      (fun u => (2 * ∑ j : Fin (pairCount n d), c (u j)) ^ 2)]
    calc
      (∑ u : Fin (pairCount n d) → Latent n,
          (∏ j : Fin (pairCount n d), latentWeight n (u j)) *
            (2 * ∑ j : Fin (pairCount n d), c (u j)) ^ 2) =
          4 * ∑ u : Fin (pairCount n d) → Latent n,
            (∏ j : Fin (pairCount n d), w (u j)) *
              (∑ j : Fin (pairCount n d), c (u j)) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        simp only [w]
        ring
      _ = 4 * (pairCount n d : ℝ) *
          (∑ z : Latent n, w z * c z ^ 2) := by
        rw [finiteProduct_centered_sum_sq w c hwsum hcenter]
        simp only [Fintype.card_fin]
        ring
      _ ≤ 4 * (pairCount n d : ℝ) *
          (1 / (1024 ^ 2 * (n : ℝ) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hcell
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      _ = 4 * (pairCount n d : ℝ) /
          (1024 ^ 2 * (n : ℝ) ^ 2) := by ring

-- @node: lagrangeNorm_ge_one
/-- Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma lagrangeNorm_ge_one (n : ℕ) : 1 ≤ lagrangeNorm n := by
  have habs : |∑ i : Fin (priorK n), lagrangeAtZero n i| ≤
      ∑ i : Fin (priorK n), |lagrangeAtZero n i| := Finset.abs_sum_le_sum_abs _ _
  rw [lagrangeAtZero_sum_one, abs_one] at habs
  simpa [lagrangeNorm] using habs

-- @node: pairedMean_scale_lower
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `hreg`](hyp:hreg). -/
lemma pairedMean_scale_lower (n d : ℕ) (q : ℝ)
    (hn : 2 ≤ n) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hreg : gScale n d q ^ 2 ≥ 1 / (n : ℝ)) :
    (1 / (36 * 1024 * Real.cosh 2) : ℝ) *
        min 1 ((d : ℝ) / ((n : ℝ) * ell n)) ≤
      (pairCount n d : ℝ) * priorH n * priorB n / lagrangeNorm n := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hkNat := priorK_ge_two n
  have hkpos : (0 : ℝ) < priorK n := by exact_mod_cast (show 0 < priorK n by omega)
  have hL1 := lagrangeNorm_ge_one n
  have hLpos : 0 < lagrangeNorm n := lt_of_lt_of_le zero_lt_one hL1
  have hCpos : 0 < Real.cosh 2 := Real.cosh_pos 2
  have hLC := lagrangeNorm_le_cosh_two n
  have hm0 : (0 : ℝ) ≤ pairCount n d := Nat.cast_nonneg _
  have hp := pairCount_scale_lower n d q hn hq hreg
  have hHB : priorH n * priorB n =
      1 / (1024 * (n : ℝ) * (priorK n : ℝ)) := by
    unfold priorH priorB
    field_simp [hnpos.ne', hkpos.ne']
  rw [show (pairCount n d : ℝ) * priorH n * priorB n =
    (pairCount n d : ℝ) * (priorH n * priorB n) by ring, hHB]
  calc
    (1 / (36 * 1024 * Real.cosh 2) : ℝ) *
        min 1 ((d : ℝ) / ((n : ℝ) * ell n)) =
        ((1 / 36 : ℝ) * min 1 ((d : ℝ) / ((n : ℝ) * ell n))) /
          (1024 * Real.cosh 2) := by ring
    _ ≤ ((pairCount n d : ℝ) / ((n : ℝ) * (priorK n : ℝ))) /
          (1024 * Real.cosh 2) := by gcongr
    _ ≤ ((pairCount n d : ℝ) / ((n : ℝ) * (priorK n : ℝ))) /
          (1024 * lagrangeNorm n) := by
      gcongr
    _ = (pairCount n d : ℝ) * (1 / (1024 * (n : ℝ) * (priorK n : ℝ))) /
          lagrangeNorm n := by ring


-- @node: finite_memLp
/-- Given [the specified input `Q`](hyp:Q), [the specified input `F`](hyp:F), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α). -/
lemma finite_memLp {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (Q : Measure α) [IsFiniteMeasure Q]
    (F : α → ℝ) : MemLp F 2 Q := by
  apply MemLp.of_bound (measurable_of_finite F).aestronglyMeasurable
    (∑ x : α, |F x|)
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun y _ => abs_nonneg (F y)) (Finset.mem_univ x)

-- @node: pairedWeightedSign_tail_eventual
/-- [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β), [the specified input `hβ`](hyp:hβ). -/
lemma pairedWeightedSign_tail_eventual (β : ℝ) (hβ : 0 < β) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (n d : ℕ) (q : ℝ), N ≤ n →
      ∀ (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1),
      gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
      (thetaLaw n d q hn hd hq).toMeasure.real
        {θ | ((pairCount n d : ℝ) * priorH n * priorB n / lagrangeNorm n) / 2 <
          |pairedWeightedSign n d θ -
            (pairCount n d : ℝ) * priorH n * priorB n / lagrangeNorm n|} ≤
        β / 2 := by
  let C := Real.cosh 2
  have hC : 0 < C := Real.cosh_pos 2
  obtain ⟨N0, hN02, hN0⟩ := eventually_priorK_sq_div_pairCount_le
    (β / (8 * C ^ 2)) (by positivity)
  refine ⟨N0, hN02, ?_⟩
  intro n d q hnN hn hd hq hreg
  let Q := (thetaLaw n d q hn hd hq).toMeasure
  let W : Theta n d → ℝ := pairedWeightedSign n d
  let μ := (pairCount n d : ℝ) * priorH n * priorB n / lagrangeNorm n
  let v := (pairCount n d : ℝ) / (1024 ^ 2 * (n : ℝ) ^ 2)
  have hn2 : 2 ≤ n := le_trans hN02 hnN
  have hnpos : (0 : ℝ) < n := by positivity
  have hkNat := priorK_ge_two n
  have hkpos : (0 : ℝ) < priorK n := by
    exact_mod_cast (show 0 < priorK n by omega)
  have hL1 := lagrangeNorm_ge_one n
  have hLpos : 0 < lagrangeNorm n := lt_of_lt_of_le zero_lt_one hL1
  have hmratio := hN0 n d q hnN hq hreg
  have hr2 := regime_min_scale_sq_lower n d q hn hq hreg
  have hrpos : 0 < min 1 ((d : ℝ) / ((n : ℝ) * ell n)) := by
    have hfour : 0 < (4 : ℝ) / (n : ℝ) := div_pos (by norm_num) hnpos
    have hspos := lt_of_lt_of_le hfour hr2
    have hellpos : 0 < ell n := lt_of_lt_of_le zero_lt_one (one_le_ell_scale n)
    have hr0 : 0 ≤ min 1 ((d : ℝ) / ((n : ℝ) * ell n)) :=
      le_min (by norm_num) (div_nonneg (Nat.cast_nonneg _) (mul_pos hnpos hellpos).le)
    nlinarith
  have hp := pairCount_scale_lower n d q hn2 hq hreg
  have hquotpos : 0 < (pairCount n d : ℝ) /
      ((n : ℝ) * (priorK n : ℝ)) :=
    lt_of_lt_of_le (mul_pos (by norm_num) hrpos) hp
  have hmpos : 0 < (pairCount n d : ℝ) := by
    by_contra hm
    have hmzero : (pairCount n d : ℝ) = 0 :=
      le_antisymm (not_lt.mp hm) (Nat.cast_nonneg _)
    rw [hmzero] at hquotpos
    simp at hquotpos
  have hmulower := pairedMean_scale_lower n d q hn2 hq hreg
  have hμpos : 0 < μ := by
    dsimp [μ]
    exact lt_of_lt_of_le (mul_pos (by positivity) hrpos) hmulower
  have hmem : MemLp W 2 Q := finite_memLp Q W
  have hmean : (∫ θ, W θ ∂Q) = μ := by
    exact pairedWeightedSign_mean n d q hn hd hq
  have hvar : variance W Q ≤ v := by
    rw [variance_eq_integral hmem.1.aemeasurable, hmean]
    exact pairedWeightedSign_variance_bound n d q hn hd hq
  have hcheb := Causalean.Stat.Concentration.probability_abs_sub_mean_gt_le
    Q W μ v (μ / 2) hmem (by positivity) hmean hvar
  have hratio : v / (μ / 2) ^ 2 =
      4 * (priorK n : ℝ) ^ 2 * lagrangeNorm n ^ 2 /
        (pairCount n d : ℝ) := by
    dsimp [v, μ]
    unfold priorH priorB
    field_simp [hnpos.ne', hkpos.ne', hLpos.ne', hmpos.ne']
    ring
  rw [hratio] at hcheb
  calc
    Q.real {θ | μ / 2 < |W θ - μ|} ≤
        4 * (priorK n : ℝ) ^ 2 * lagrangeNorm n ^ 2 /
          (pairCount n d : ℝ) := hcheb
    _ ≤ 4 * C ^ 2 * ((priorK n : ℝ) ^ 2 / (pairCount n d : ℝ)) := by
      have hLC := lagrangeNorm_le_cosh_two n
      have hLsq : lagrangeNorm n ^ 2 ≤ C ^ 2 := by
        dsimp [C]
        nlinarith [sq_nonneg (Real.cosh 2 - lagrangeNorm n)]
      field_simp [hmpos.ne']
      nlinarith [mul_nonneg (sq_nonneg (priorK n : ℝ))
        (sub_nonneg.mpr hLsq)]
    _ ≤ 4 * C ^ 2 * (β / (8 * C ^ 2)) :=
      mul_le_mul_of_nonneg_left hmratio (by positivity)
    _ = β / 2 := by field_simp [hC.ne']; ring


-- @node: normalizationJ_tail_eventual
/-- [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β), [the specified input `hβ`](hyp:hβ). -/
lemma normalizationJ_tail_eventual (β : ℝ) (hβ : 0 < β) :
    ∃ N : ℕ, ∀ (n d : ℕ) (q : ℝ), N ≤ n →
      ∀ (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1),
      (thetaLaw n d q hn hd hq).toMeasure.real
        {θ | (1 / 2 : ℝ) < |normalizationJ n d θ - 1|} ≤ β / 2 := by
  obtain ⟨N0, hN0⟩ := eventually_ell_sq_le
    (β * 1024 ^ 2 / 32) (by positivity)
  refine ⟨N0, ?_⟩
  intro n d q hnN hn hd hq
  let Q := (thetaLaw n d q hn hd hq).toMeasure
  let J : Theta n d → ℝ := normalizationJ n d
  let v := 4 * (pairCount n d : ℝ) / (1024 ^ 2 * (n : ℝ) ^ 2)
  have hnpos : (0 : ℝ) < n := by positivity
  have hmem : MemLp J 2 Q := finite_memLp Q J
  have hmom := normalizationJ_moments n d q hn hd hq
  have hmean : (∫ θ, J θ ∂Q) = 1 := hmom.1
  have hvar : variance J Q ≤ v := by
    rw [variance_eq_integral hmem.1.aemeasurable, hmean]
    exact hmom.2
  have hcheb := Causalean.Stat.Concentration.probability_abs_sub_mean_gt_le
    Q J 1 v (1 / 2) hmem (by norm_num) hmean hvar
  have hratio : v / (1 / 2) ^ 2 =
      16 * (pairCount n d : ℝ) / (1024 ^ 2 * (n : ℝ) ^ 2) := by
    dsimp [v]
    ring
  rw [hratio] at hcheb
  have hmNat : pairCount n d ≤ Nat.floor ((n : ℝ) * ell n) := by
    exact min_le_right _ _
  have hmcast : (pairCount n d : ℝ) ≤
      (Nat.floor ((n : ℝ) * ell n) : ℕ) := by exact_mod_cast hmNat
  have hfloor := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n)
    (le_trans (by norm_num) (one_le_ell_scale n)))
  have hmle : (pairCount n d : ℝ) ≤ (n : ℝ) * ell n :=
    le_trans hmcast hfloor
  have hell := one_le_ell_scale n
  have heps := hN0 n hnN
  calc
    Q.real {θ | (1 / 2 : ℝ) < |J θ - 1|} ≤
        16 * (pairCount n d : ℝ) / (1024 ^ 2 * (n : ℝ) ^ 2) := hcheb
    _ ≤ 16 * ((n : ℝ) * ell n) / (1024 ^ 2 * (n : ℝ) ^ 2) := by
      gcongr
    _ = 16 * ell n / (1024 ^ 2 * (n : ℝ)) := by
      field_simp [hnpos.ne']
    _ ≤ 16 * ell n ^ 2 / (1024 ^ 2 * (n : ℝ)) := by
      gcongr
      nlinarith
    _ ≤ β / 2 := by
      have hden : 0 < (1024 : ℝ) ^ 2 * (n : ℝ) := by positivity
      apply (div_le_iff₀ hden).2
      nlinarith



-- @node: paired_target_good_event_eventual
/-- Equations (20)--(24): beyond a tolerance-dependent threshold, the
normalized signed latent mass dominates a universal multiple of `gScale` with
prior probability at least `1-β`. [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β), [the specified input `hβ`](hyp:hβ). -/
lemma paired_target_good_event_eventual (β : ℝ) (hβ : 0 < β) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (n d : ℕ) (q : ℝ), ∀ (hnN : N ≤ n) (hn : 1 ≤ n) (hd : 1 ≤ d)
        (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1),
        gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
        1 - β ≤ (thetaLaw n d q hn hd hq).toMeasure.real
          {θ | c * gScale n d q ≤
            delta q / (16 * q) * pairedWeightedSign n d θ /
              normalizationJ n d θ} := by
  obtain ⟨NW, hNW2, hWtail⟩ := pairedWeightedSign_tail_eventual β hβ
  obtain ⟨NJ, hJtail⟩ := normalizationJ_tail_eventual β hβ
  let C := Real.cosh 2
  let c : ℝ := 1 / (36 * 1024 * C * 48)
  refine ⟨max NW NJ, le_trans hNW2 (le_max_left _ _), c, ?_, ?_⟩
  · dsimp [c, C]
    positivity
  intro n d q hnN hn hd hq hreg
  have hnW : NW ≤ n := le_trans (le_max_left _ _) hnN
  have hnJ : NJ ≤ n := le_trans (le_max_right _ _) hnN
  have hn2 : 2 ≤ n := le_trans hNW2 hnW
  let Q := (thetaLaw n d q hn hd hq).toMeasure
  let W : Theta n d → ℝ := pairedWeightedSign n d
  let J : Theta n d → ℝ := normalizationJ n d
  let μ := (pairCount n d : ℝ) * priorH n * priorB n / lagrangeNorm n
  let G : Set (Theta n d) := {θ | |W θ - μ| ≤ μ / 2 ∧ |J θ - 1| ≤ 1 / 2}
  let BW : Set (Theta n d) := {θ | μ / 2 < |W θ - μ|}
  let BJ : Set (Theta n d) := {θ | (1 / 2 : ℝ) < |J θ - 1|}
  have hWt : Q.real BW ≤ β / 2 := hWtail n d q hnW hn hd hq hreg
  have hJt : Q.real BJ ≤ β / 2 := hJtail n d q hnJ hn hd hq
  have hsubcomp : Gᶜ ⊆ BW ∪ BJ := by
    intro θ hθ
    simp only [G, BW, BJ, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_union] at hθ ⊢
    by_cases h1 : |W θ - μ| ≤ μ / 2
    · right
      exact lt_of_not_ge (fun h2 => hθ ⟨h1, h2⟩)
    · left
      exact lt_of_not_ge h1
  have hGmeas : MeasurableSet G := Set.Finite.measurableSet (Set.toFinite G)
  have hGcomp : Q.real Gᶜ ≤ β := by
    calc
      Q.real Gᶜ ≤ Q.real (BW ∪ BJ) := measureReal_mono hsubcomp
      _ ≤ Q.real BW + Q.real BJ := measureReal_union_le BW BJ
      _ ≤ β := by linarith
  have hGprob : 1 - β ≤ Q.real G := by
    rw [measureReal_compl hGmeas, probReal_univ] at hGcomp
    linarith
  apply le_trans hGprob
  refine measureReal_mono ?_ (by finiteness)
  intro θ hθ
  simp only [G, Set.mem_setOf_eq] at hθ ⊢
  have hnpos : (0 : ℝ) < n := by positivity
  have hr2 := regime_min_scale_sq_lower n d q hn hq hreg
  have hrpos : 0 < min 1 ((d : ℝ) / ((n : ℝ) * ell n)) := by
    have hfour : 0 < (4 : ℝ) / (n : ℝ) := div_pos (by norm_num) hnpos
    have hspos := lt_of_lt_of_le hfour hr2
    have hellpos : 0 < ell n := lt_of_lt_of_le zero_lt_one (one_le_ell_scale n)
    have hr0 : 0 ≤ min 1 ((d : ℝ) / ((n : ℝ) * ell n)) :=
      le_min (by norm_num) (div_nonneg (Nat.cast_nonneg _) (mul_pos hnpos hellpos).le)
    nlinarith
  have hmulower := pairedMean_scale_lower n d q hn2 hq hreg
  have hμpos : 0 < μ := by
    dsimp [μ]
    exact lt_of_lt_of_le (mul_pos (by positivity) hrpos) hmulower
  have hWlower : μ / 2 ≤ W θ := by
    have habs := (abs_le.mp hθ.1).1
    linarith
  have hJupper : J θ ≤ 3 / 2 := by
    have habs := (abs_le.mp hθ.2).2
    linarith
  have hJpos : 0 < J θ := normalizationJ_pos n d q hn hd hq θ
  have hratio : μ / 3 ≤ W θ / J θ := by
    apply (le_div_iff₀ hJpos).2
    have hμ0 : 0 ≤ μ := hμpos.le
    nlinarith [mul_nonneg hμ0 (sub_nonneg.mpr hJupper)]
  have hδ0 : 0 ≤ delta q := by unfold delta; linarith [hq.2]
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq.1
  have hratio0 : 0 ≤ W θ / J θ := le_trans (by positivity : 0 ≤ μ / 3) hratio
  have hcoef : delta q * μ / 48 ≤
      delta q / (16 * q) * W θ / J θ := by
    calc
      delta q * μ / 48 = (delta q / 16) * (μ / 3) := by ring
      _ ≤ (delta q / 16) * (W θ / J θ) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ (delta q / (16 * q)) * (W θ / J θ) := by
        apply mul_le_mul_of_nonneg_right _ hratio0
        apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 16)
          (mul_pos (by norm_num) hqpos)).2
        nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hq.2)]
      _ = delta q / (16 * q) * W θ / J θ := by ring
  calc
    c * gScale n d q =
        (delta q / 48) *
          ((1 / (36 * 1024 * C)) *
            min 1 ((d : ℝ) / ((n : ℝ) * ell n))) := by
      dsimp [c]
      simp only [gScale]
      ring
    _ ≤ (delta q / 48) * μ :=
      mul_le_mul_of_nonneg_left hmulower (by positivity)
    _ = delta q * μ / 48 := by ring
    _ ≤ _ := hcoef

end CausalSmith.Stat.MarNearcompleteFrontier
