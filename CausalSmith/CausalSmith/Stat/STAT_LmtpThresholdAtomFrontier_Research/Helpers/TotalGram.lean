/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.Bandwidth
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.Design
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.SampleBlocks
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ShiftedPowerCoercivity
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.LocalWindowGram
import Causalean.Stat.Nonparametric.LocalPolynomial.GramCoercivity
import Causalean.Stat.Concentration.TailBounds.BinomialCount
import Causalean.Stat.Concentration.Matrix.LocalizedGram

/-!
# Uniform total-Gram stabilization

This file isolates the note's main realized-design bottleneck. Constants are
quantified before laws, sample sizes, thresholds, blocks, and strata.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set
open scoped BigOperators

noncomputable section

private lemma measurable_clampObs_X {J : ℕ} :
    Measurable (fun o : ClampObs J => o.X) := by
  exact measurable_fst.comp (Measurable.of_comap_le le_rfl)

private lemma measurable_clampObs_A {J : ℕ} :
    Measurable (fun o : ClampObs J => o.A) := by
  exact measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))

private lemma infoBandwidth_pos_le {n : ℕ} {delta beta kappa deltaBar : ℝ}
    (hbeta : 0 < beta) (hkappa : 0 ≤ kappa)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (hdeltaBar : 0 < deltaBar ∧ deltaBar < 1) :
    0 < infoBandwidth n delta beta kappa deltaBar ∧
      infoBandwidth n delta beta kappa deltaBar ≤ 1 - deltaBar := by
  have hH : 0 < 1 - deltaBar := sub_pos.mpr hdeltaBar.2
  by_cases hS : (bandwidthCrossingSet n delta beta kappa deltaBar).Nonempty
  · have hSnonempty := hS
    obtain ⟨y, hy⟩ := hSnonempty
    have hn : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      simp only [bandwidthCrossingSet, Set.mem_setOf_eq] at hy
      rw [hn0] at hy
      norm_num at hy
    let b : ℝ := (n : ℝ) ^ (-1 / (2 * beta + 1))
    have hp : 0 < 2 * beta + 1 := by linarith
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hb : 0 < b := Real.rpow_pos_of_pos hnR _
    have hlower : ∀ z ∈ bandwidthCrossingSet n delta beta kappa deltaBar, b ≤ z := by
      intro z hz
      simp only [bandwidthCrossingSet, Set.mem_setOf_eq] at hz
      have hdz : delta + z ≤ 1 := by linarith [hdelta.2, hz.2.1]
      have hpow : (delta + z) ^ kappa ≤ 1 :=
        Real.rpow_le_one (by linarith [hdelta.1, hz.1]) hdz hkappa
      have hone : 1 ≤ (n : ℝ) * z ^ (2 * beta + 1) := by
        calc
          1 ≤ (n : ℝ) * z ^ (2 * beta + 1) * (delta + z) ^ kappa := hz.2.2
          _ ≤ (n : ℝ) * z ^ (2 * beta + 1) * 1 := by
            exact mul_le_mul_of_nonneg_left hpow
              (mul_nonneg hnR.le (Real.rpow_nonneg hz.1.le _))
          _ = _ := mul_one _
      rw [← Real.rpow_le_rpow_iff hb.le hz.1.le hp]
      dsimp [b]
      rw [← Real.rpow_mul hnR.le]
      have hexp : (-1 / (2 * beta + 1)) * (2 * beta + 1) = -1 := by
        field_simp
      rw [hexp, Real.rpow_neg_one]
      have hinv : (1 : ℝ) / (n : ℝ) ≤ z ^ (2 * beta + 1) :=
        (div_le_iff₀ hnR).2 (by simpa [mul_comm] using hone)
      simpa [one_div] using hinv
    have hbelow : BddBelow (bandwidthCrossingSet n delta beta kappa deltaBar) :=
      ⟨b, hlower⟩
    have hle : sInf (bandwidthCrossingSet n delta beta kappa deltaBar) ≤ y :=
      csInf_le hbelow hy
    have hlow : b ≤ sInf (bandwidthCrossingSet n delta beta kappa deltaBar) :=
      le_csInf hS hlower
    simpa only [infoBandwidth, hS, if_pos] using
      And.intro (hb.trans_le hlow) (hle.trans hy.2.1)
  · simp [infoBandwidth, hS, hH]

private lemma iid_block_product_law {J n : ℕ} (P : ClampLaw J)
    (hsampling : IidSampling P n) (I : Finset (Fin n)) :
    (iidProduct P n).map (fun z => fun j : Fin I.card =>
      z ((I.orderIsoOfFin rfl) j)) =
      Measure.pi (fun _ : Fin I.card => P.dataMeasure) := by
  let _ : IsProbabilityMeasure P.dataMeasure := hsampling.1
  simpa [iidProduct] using block_reindexed_law_eq P.dataMeasure I

private lemma coerciveMatrix_isUnit {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    {a : ℝ} (ha : 0 < a)
    (hA : ∀ v : Fin d → ℝ,
      a * ∑ i, (v i) ^ 2 ≤ matrixQuadratic A v) : IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have hzero : A.mulVec (u - v) = 0 := by
    simpa [Matrix.mulVec_sub] using sub_eq_zero.mpr huv
  have hquad : matrixQuadratic A (u - v) = 0 := by
    rw [show matrixQuadratic A (u - v) =
      dotProduct (u - v) (A.mulVec (u - v)) by
        simp [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
        ring_nf,
      hzero]
    simp
  have hsum : ∑ i, ((u - v) i) ^ 2 = 0 := by
    have hs : 0 ≤ ∑ i, ((u - v) i) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith [hA (u - v)]
  funext i
  have hi : ((u - v) i) ^ 2 = 0 := by
    exact le_antisymm
      (hsum ▸ Finset.single_le_sum (fun j _ => sq_nonneg ((u - v) j))
        (Finset.mem_univ i)) (sq_nonneg _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)

private lemma coerciveMatrix_inv_mulVec_euclidean_le {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℝ} {a : ℝ} (ha : 0 < a)
    (hA : ∀ v : Fin d → ℝ,
      a * ∑ i, (v i) ^ 2 ≤ matrixQuadratic A v)
    (s : Fin d → ℝ) :
    Real.sqrt (∑ k, (A⁻¹.mulVec s k) ^ 2) ≤
      a⁻¹ * Real.sqrt (∑ k, (s k) ^ 2) := by
  let z := A⁻¹.mulVec s
  have hu : IsUnit A := coerciveMatrix_isUnit ha hA
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hu
  have hAz : A.mulVec z = s := by
    change A.mulVec (A⁻¹.mulVec s) = s
    calc
      _ = (A * A⁻¹).mulVec s := Matrix.mulVec_mulVec s A A⁻¹
      _ = s := by rw [Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  have hlower : a * ∑ k, (z k) ^ 2 ≤ ∑ k, z k * s k := by
    have hz := hA z
    rw [show matrixQuadratic A z = dotProduct z (A.mulVec z) by
      simp [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
      ring_nf,
      hAz] at hz
    simpa [dotProduct] using hz
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ z s
  have hsquares : a * (Real.sqrt (∑ k, (z k) ^ 2)) ^ 2 ≤
      Real.sqrt (∑ k, (z k) ^ 2) * Real.sqrt (∑ k, (s k) ^ 2) := by
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg (z _))]
    exact hlower.trans hcs
  have hznonneg := Real.sqrt_nonneg (∑ k, (z k) ^ 2)
  by_cases hz : Real.sqrt (∑ k, (z k) ^ 2) = 0
  · simp [z, hz]
    positivity
  · have hzpos : 0 < Real.sqrt (∑ k, (z k) ^ 2) :=
      lt_of_le_of_ne hznonneg (Ne.symm hz)
    change Real.sqrt (∑ k, (z k) ^ 2) ≤ _
    have hai : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
    have hax : a * Real.sqrt (∑ k, (z k) ^ 2) ≤
        Real.sqrt (∑ k, (s k) ^ 2) := by
      nlinarith
    calc
      Real.sqrt (∑ k, (z k) ^ 2) =
          a⁻¹ * (a * Real.sqrt (∑ k, (z k) ^ 2)) := by
            rw [← mul_assoc, hai, one_mul]
      _ ≤ a⁻¹ * Real.sqrt (∑ k, (s k) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hax (inv_nonneg.mpr ha.le)

/-- If [the reference eigenvalue is positive](hyp:hlambda) and [the realized Gram matrix is good](hyp:hgood), [the intercept weights reproduce every polynomial basis coordinate](goal). -/
lemma goodGram_reproduction {J n ell : ℕ}
    (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (kappa cminus cplus delta h : ℝ)
    (hlambda : 0 < lambdaStar ell kappa cminus cplus)
    (hgood : GoodGramEvent B z x ell kappa cminus cplus delta h) :
    ∀ j : Fin (ell + 1),
      (∑ i ∈ B.I2,
        interceptWeight B z x ell kappa cminus cplus delta h i *
          (scaledDose delta h (z i)) ^ (j : ℕ)) =
        if j = 0 then 1 else 0 := by
  classical
  let A := localGram B z x ell delta h
  let N : ℝ := localCount B z x delta h
  let a := lambdaStar ell kappa cminus cplus * N / 2
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hgood.1
  have ha : 0 < a := by dsimp [a]; positivity
  have hunit : IsUnit A := coerciveMatrix_isUnit ha hgood.2
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunit
  let U : Fin n → ℝ := fun i => scaledDose delta h (z i)
  let W : Fin n → ℝ := localKernelWeight B z x delta h
  have hdet' : IsUnit
      (Causalean.Stat.Nonparametric.designMatrix ell U W).det := by
    simpa [A, U, W, localGram] using hdet
  intro j
  have hrep := Causalean.Stat.Nonparametric.equivKernelWeight_reproduces hdet'
      (j : ℕ) (Nat.le_of_lt_succ j.isLt)
  calc
    (∑ i ∈ B.I2,
        interceptWeight B z x ell kappa cminus cplus delta h i * U i ^ (j : ℕ)) =
        ∑ i ∈ B.I2,
          Causalean.Stat.Nonparametric.equivKernelWeight ell U W i * U i ^ (j : ℕ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [interceptWeight_eq_equivKernel_of_good
              B z x ell kappa cminus cplus delta h hgood i]
    _ = ∑ i,
          Causalean.Stat.Nonparametric.equivKernelWeight ell U W i * U i ^ (j : ℕ) := by
            apply Finset.sum_subset (Finset.subset_univ B.I2)
            intro i _ hi
            have hw : W i = 0 := by
              simp [W, localKernelWeight, hi]
            simp [Causalean.Stat.Nonparametric.equivKernelWeight, hw]
    _ = if j = 0 then 1 else 0 := by
      simpa [U] using hrep

-- @node: scaledDose_mem_iff
private lemma scaledDose_mem_iff {J : ℕ} {delta h : ℝ} (hh : 0 < h)
    (o : ClampObs J) :
    scaledDose delta h o ∈ Set.Icc (0 : ℝ) 1 ↔
      o.A ∈ Set.Icc delta (delta + h) := by
  simp only [scaledDose, Set.mem_Icc]
  constructor
  · intro hu
    constructor
    · exact sub_nonneg.mp (((div_nonneg_iff).mp hu.1 |>.resolve_right
        (fun hneg => (not_lt_of_ge hneg.2 hh))).1)
    · have := (div_le_iff₀ hh).mp hu.2
      linarith
  · intro ha
    constructor
    · exact div_nonneg (sub_nonneg.mpr ha.1) hh.le
    · exact (div_le_iff₀ hh).mpr (by linarith)

-- @node: local_active_count_eq
private lemma local_active_count_eq {J n : ℕ} (B : SplitBlocks n)
    (z : Fin n → ClampObs J) (x : Fin J) (delta h : ℝ) (hh : 0 < h) :
    (∑ i ∈ B.I2, if (z i).X = x ∧
        scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1 then (1 : ℝ) else 0) =
      (localCount B z x delta h : ℝ) := by
  rw [localCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  by_cases hx : (z i).X = x
  · simp [hx, scaledDose_mem_iff hh]
  · simp [hx]

-- @node: block_orderIso_sum_eq
/-- Summing over the canonical enumeration of a finite set agrees with summing directly over that set. -/
lemma block_orderIso_sum_eq {n : ℕ} (I : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ j : Fin I.card, f ((I.orderIsoOfFin rfl) j)) = ∑ i ∈ I, f i := by
  calc
    _ = ∑ i : I, f i := (I.orderIsoOfFin rfl).toEquiv.sum_comp (fun i : I => f i)
    _ = _ := Finset.sum_attach I f

-- @node: localizedGramGood_iff_goodGramEvent
private lemma localizedGramGood_iff_goodGramEvent {J n ell : ℕ}
    (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (kappa cminus cplus delta h : ℝ) (hh : 0 < h) :
    Causalean.Stat.Concentration.LocalizedGramGood
        (lambdaStar ell kappa cminus cplus) (localWindowWeight x delta h)
        (localWindowFeature (J := J) (ell := ell) delta h)
        (fun j : Fin B.I2.card => z ((B.I2.orderIsoOfFin rfl) j)) ↔
      GoodGramEvent B z x ell kappa cminus cplus delta h := by
  classical
  have hcount : Causalean.Stat.Concentration.localCount
      (localWindowWeight x delta h)
      (fun j : Fin B.I2.card => z ((B.I2.orderIsoOfFin rfl) j)) =
      (localCount B z x delta h : ℝ) := by
    unfold Causalean.Stat.Concentration.localCount
    change (∑ i : Fin B.I2.card,
      localWindowWeight x delta h (z ((B.I2.orderIsoOfFin rfl) i))) = _
    calc
      _ = ∑ i ∈ B.I2, localWindowWeight x delta h (z i) :=
        block_orderIso_sum_eq B.I2 (fun i => localWindowWeight x delta h (z i))
      _ = _ := by simpa [localWindowWeight, scaledDose_mem_iff hh] using
        local_active_count_eq B z x delta h hh
  have hentry (j k : Fin (ell + 1)) :
      Causalean.Stat.Concentration.localGramEntry (localWindowWeight x delta h)
        (localWindowFeature (J := J) (ell := ell) delta h)
        (fun r : Fin B.I2.card => z ((B.I2.orderIsoOfFin rfl) r)) j k =
      localGram B z x ell delta h j k := by
    unfold Causalean.Stat.Concentration.localGramEntry
    change (∑ i : Fin B.I2.card,
      localWindowWeight x delta h (z ((B.I2.orderIsoOfFin rfl) i)) *
        localWindowFeature delta h j (z ((B.I2.orderIsoOfFin rfl) i)) *
        localWindowFeature delta h k (z ((B.I2.orderIsoOfFin rfl) i))) = _
    calc
      _ = ∑ i ∈ B.I2, localWindowWeight x delta h (z i) *
          localWindowFeature delta h j (z i) * localWindowFeature delta h k (z i) :=
        block_orderIso_sum_eq B.I2 (fun i => localWindowWeight x delta h (z i) *
          localWindowFeature delta h j (z i) * localWindowFeature delta h k (z i))
      _ = ∑ i ∈ B.I2, if (z i).X = x ∧
        scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1 then
          monomialVec ell (scaledDose delta h (z i)) j *
            monomialVec ell (scaledDose delta h (z i)) k else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hu : scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1
        · by_cases hx : (z i).X = x <;>
            simp [localWindowWeight, localWindowFeature, hu, hx]
        · simp [localWindowWeight, localWindowFeature, hu]
      _ = localGram B z x ell delta h j k :=
        (localGram_apply B z x ell delta h j k).symm
  have hquad (v : Fin (ell + 1) → ℝ) :
      Causalean.Stat.Concentration.localGramQuadratic (localWindowWeight x delta h)
        (localWindowFeature (J := J) (ell := ell) delta h)
        (fun r : Fin B.I2.card => z ((B.I2.orderIsoOfFin rfl) r)) v =
      matrixQuadratic (localGram B z x ell delta h) v := by
    unfold Causalean.Stat.Concentration.localGramQuadratic matrixQuadratic
    simp_rw [hentry]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  unfold Causalean.Stat.Concentration.LocalizedGramGood GoodGramEvent
  rw [hcount]
  constructor
  · rintro ⟨hN, hg⟩
    refine ⟨by exact_mod_cast hN, ?_⟩
    intro v
    have hv := hg v
    rw [hquad v] at hv
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hv
  · rintro ⟨hN, hg⟩
    refine ⟨by exact_mod_cast hN, ?_⟩
    intro v
    rw [hquad]
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hg v

/-- On a good Gram event, every active intercept weight has the inverse-count
scale dictated by coercivity. The result uses [the `hlambda` condition](hyp:hlambda), [the `hgood` condition](hyp:hgood). [This is the stated conclusion](goal).
-/
-- @node: goodGram_interceptWeight_pointwise
lemma goodGram_interceptWeight_pointwise {J n ell : ℕ}
    (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (kappa cminus cplus delta h : ℝ)
    (hlambda : 0 < lambdaStar ell kappa cminus cplus)
    (hgood : GoodGramEvent B z x ell kappa cminus cplus delta h) (i : Fin n) :
    |interceptWeight B z x ell kappa cminus cplus delta h i| ≤
      (lambdaStar ell kappa cminus cplus * (localCount B z x delta h : ℝ) / 2)⁻¹ *
        Real.sqrt (ell + 1 : ℝ) := by
  classical
  by_cases hi : i ∈ B.I2 ∧ (z i).X = x ∧
      scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1
  · let A := localGram B z x ell delta h
    let a := lambdaStar ell kappa cminus cplus * (localCount B z x delta h : ℝ) / 2
    let s := monomialVec ell (scaledDose delta h (z i))
    have hN : 0 < (localCount B z x delta h : ℝ) := by exact_mod_cast hgood.1
    have ha : 0 < a := by dsimp [a]; positivity
    have hinv := coerciveMatrix_inv_mulVec_euclidean_le ha hgood.2 s
    have hcoord : |A⁻¹.mulVec s 0| ≤ Real.sqrt (∑ k, (A⁻¹.mulVec s k) ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (Finset.single_le_sum
        (fun j _ => sq_nonneg (A⁻¹.mulVec s j)) (Finset.mem_univ 0))
    have hs : Real.sqrt (∑ k, (s k) ^ 2) ≤ Real.sqrt (ell + 1 : ℝ) := by
      apply Real.sqrt_le_sqrt
      calc
        ∑ k, (s k) ^ 2 ≤ ∑ _k : Fin (ell + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          dsimp [s, monomialVec]
          have hu := hi.2.2
          have hp0 : 0 ≤ scaledDose delta h (z i) ^ (k : ℕ) := pow_nonneg hu.1 _
          have hp1 : scaledDose delta h (z i) ^ (k : ℕ) ≤ 1 := pow_le_one₀ hu.1 hu.2
          nlinarith
        _ = ell + 1 := by simp
    rw [interceptWeight_eq_mulVec B z x ell kappa cminus cplus delta h i
      hgood hi.1 hi.2.1 hi.2.2]
    simpa only [A, a, s] using
      hcoord.trans (hinv.trans
        (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr ha.le)))
  · rw [interceptWeight_eq_zero_of_inactive
      B z x ell kappa cminus cplus delta h i hgood hi, abs_zero]
    have hN : 0 < (localCount B z x delta h : ℝ) := by exact_mod_cast hgood.1
    positivity

/-- On a good Gram event, the exact weights reproduce every basis monomial and
obey explicit count-normalized `l1` and squared-`l2` bounds. The result uses [the `hh` condition](hyp:hh), [the `hlambda` condition](hyp:hlambda), [the `hgood` condition](hyp:hgood). [This is the stated conclusion](goal).
-/
-- @node: goodGram_weight_controls
lemma goodGram_weight_controls {J n ell : ℕ}
    (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (kappa cminus cplus delta h : ℝ)
    (hh : 0 < h)
    (hlambda : 0 < lambdaStar ell kappa cminus cplus)
    (hgood : GoodGramEvent B z x ell kappa cminus cplus delta h) :
    (∀ j : Fin (ell + 1),
      (∑ i ∈ B.I2,
        interceptWeight B z x ell kappa cminus cplus delta h i *
          (scaledDose delta h (z i)) ^ (j : ℕ)) =
        if j = 0 then 1 else 0) ∧
    (∑ i ∈ B.I2,
      |interceptWeight B z x ell kappa cminus cplus delta h i|) ≤
        2 * Real.sqrt (ell + 1 : ℝ) /
          lambdaStar ell kappa cminus cplus ∧
    (∑ i ∈ B.I2,
      (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2) ≤
        (4 * (ell + 1 : ℝ) / lambdaStar ell kappa cminus cplus ^ 2) /
          (localCount B z x delta h : ℝ) := by
  classical
  let lam := lambdaStar ell kappa cminus cplus
  let N := localCount B z x delta h
  have hNnat : 0 < N := hgood.1
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hpoint (i : Fin n) :
      |interceptWeight B z x ell kappa cminus cplus delta h i| ≤
        if i ∈ B.I2 ∧ (z i).X = x ∧
            scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1 then
          (lam * (N : ℝ) / 2)⁻¹ * Real.sqrt (ell + 1 : ℝ)
        else 0 := by
    by_cases hi : i ∈ B.I2 ∧ (z i).X = x ∧
        scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1
    · rw [if_pos hi]
      exact goodGram_interceptWeight_pointwise B z x kappa cminus cplus delta h
        hlambda hgood i
    · rw [if_neg hi, interceptWeight_eq_zero_of_inactive
        B z x ell kappa cminus cplus delta h i hgood hi, abs_zero]
  have hcount :
      (∑ i ∈ B.I2, if (z i).X = x ∧
          scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1 then (1 : ℝ) else 0) = N := by
    simpa only [N] using local_active_count_eq B z x delta h hh
  refine ⟨goodGram_reproduction B z x kappa cminus cplus delta h hlambda hgood, ?_, ?_⟩
  · calc
      (∑ i ∈ B.I2,
          |interceptWeight B z x ell kappa cminus cplus delta h i|) ≤
          ∑ i ∈ B.I2, if (z i).X = x ∧
              scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1 then
            (lam * (N : ℝ) / 2)⁻¹ * Real.sqrt (ell + 1 : ℝ) else 0 := by
              apply Finset.sum_le_sum
              intro i hi
              simpa [hi] using hpoint i
      _ = N * ((lam * (N : ℝ) / 2)⁻¹ * Real.sqrt (ell + 1 : ℝ)) := by
            rw [← hcount]
            simp_rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            by_cases ha : (z i).X = x ∧
                scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1 <;> simp [ha]
      _ = 2 * Real.sqrt (ell + 1 : ℝ) / lam := by
            field_simp [ne_of_gt hlambda, ne_of_gt hN]
            <;> ring
  · have hsqpoint (i : Fin n) :
        (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2 ≤
          if i ∈ B.I2 ∧ (z i).X = x ∧
              scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1 then
            ((lam * (N : ℝ) / 2)⁻¹ * Real.sqrt (ell + 1 : ℝ)) ^ 2
          else 0 := by
      have habs := hpoint i
      by_cases hi : i ∈ B.I2 ∧ (z i).X = x ∧
          scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1
      · rw [if_pos hi] at habs ⊢
        rw [← sq_abs]
        gcongr
      · rw [if_neg hi] at habs ⊢
        have hz : interceptWeight B z x ell kappa cminus cplus delta h i = 0 := by
          exact interceptWeight_eq_zero_of_inactive
            B z x ell kappa cminus cplus delta h i hgood hi
        simp [hz]
    calc
      (∑ i ∈ B.I2,
          (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2) ≤
          ∑ i ∈ B.I2, if (z i).X = x ∧
              scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1 then
            ((lam * (N : ℝ) / 2)⁻¹ * Real.sqrt (ell + 1 : ℝ)) ^ 2 else 0 := by
              apply Finset.sum_le_sum
              intro i hi
              simpa [hi] using hsqpoint i
      _ = N * ((lam * (N : ℝ) / 2)⁻¹ * Real.sqrt (ell + 1 : ℝ)) ^ 2 := by
            rw [← hcount]
            simp_rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            by_cases ha : (z i).X = x ∧
                scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1 <;> simp [ha]
      _ = (4 * (ell + 1 : ℝ) / lam ^ 2) / N := by
            simp only [mul_pow]
            rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ell + 1)]
            field_simp [ne_of_gt hlambda, ne_of_gt hN]
            <;> ring

/-- The population constant used by total-Gram stabilization is positive under
the standing regime constraints. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: totalGram_lambdaStar_pos
lemma totalGram_lambdaStar_pos
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    0 < lambdaStar (ellOf beta) kappa cminus cplus := by
  simp only [RegimeConstants] at hreg
  rcases hreg with
    ⟨_hJ, _hbeta, hkappa, _hL, hcminus, _hcminus_le, hkappa_le_cplus,
      _hpmin, _hpmin_le, _hdeltaBar, _hdeltaBar_lt, _halpha, _halpha_lt⟩
  exact lambdaStar_pos (ellOf beta) hkappa hcminus (by linarith)

/-- Uniform positivity, singular-design tail, exact reproduction, and `l1`/`l2`
weight control follow from [admissible regime constants](hyp:hreg). [The constants are uniform over laws, samples, thresholds, and strata](goal). -/
-- @node: lem:total-gram
lemma total_gram_stabilization
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      0 < lambdaStar (ellOf beta) kappa cminus cplus ∧
      ∀ (P : ClampLaw J), ClampModel P beta kappa L cminus cplus pmin →
      ∀ (n : ℕ), IidSampling P n →
      ∀ (B : SplitBlocks n) (delta : ℝ), delta ∈ Set.Icc (0 : ℝ) deltaBar →
      ∀ x : Fin J,
        let h := infoBandwidth n delta beta kappa deltaBar
        (iidProduct P n).real {z |
            ¬ GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h} ≤
          C * Real.exp (-c * (n : ℝ) * h * (delta + h) ^ kappa) ∧
        ∀ z : Fin n → ClampObs J,
          GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h →
          (∀ j : Fin (ellOf beta + 1),
            (∑ i ∈ B.I2,
              interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
                (scaledDose delta h (z i)) ^ (j : ℕ)) =
              if j = 0 then 1 else 0) ∧
          (∑ i ∈ B.I2,
              |interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i|) ≤ C ∧
          (∑ i ∈ B.I2,
              (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2) ≤
            C / (localCount B z x delta h : ℝ) := by
  have _hlambda : 0 < lambdaStar (ellOf beta) kappa cminus cplus :=
    totalGram_lambdaStar_pos J beta kappa L cminus cplus pmin deltaBar alpha hreg
  classical
  simp only [RegimeConstants] at hreg
  rcases hreg with
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus_lower,
      hpmin, hpmin_le, hdeltaBar, hdeltaBar_lt, halpha, halpha_lt⟩
  let ell := ellOf beta
  let lam := lambdaStar ell kappa cminus cplus
  let d : ℝ := ell + 1
  let r := Causalean.Stat.Concentration.localizedGramRate (Fin (ell + 1)) lam 1
  let K := pmin * cminus / (2 * (2 : ℝ) ^ kappa)
  let c := r * K / 8
  let A := 2 * (1 + d * d)
  let C := A * Real.exp (8 * c) + 2 * Real.sqrt d / lam + 4 * d / lam ^ 2 + 1
  have hlam : 0 < lam := by simpa [ell, lam] using _hlambda
  have hd : 0 < d := by dsimp [d]; positivity
  have hr : 0 < r := by
    dsimp [r]
    unfold Causalean.Stat.Concentration.localizedGramRate
    apply lt_min (by norm_num)
    positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hA : 1 ≤ A := by dsimp [A, d]; nlinarith [sq_nonneg (ell + 1 : ℝ)]
  have hC : 0 < C := by dsimp [C]; positivity
  have hCtail : A * Real.exp (8 * c) ≤ C := by
    dsimp [C]
    have h1 : 0 ≤ 2 * Real.sqrt d / lam := by positivity
    have h2 : 0 ≤ 4 * d / lam ^ 2 := by positivity
    linarith
  have hCA : A ≤ C := by
    calc
      A = A * 1 := by ring
      _ ≤ A * Real.exp (8 * c) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) (by linarith [hA])
      _ ≤ C := hCtail
  have hCl1 : 2 * Real.sqrt d / lam ≤ C := by
    dsimp [C]
    have h0 : 0 ≤ A * Real.exp (8 * c) := by positivity
    have h2 : 0 ≤ 4 * d / lam ^ 2 := by positivity
    linarith
  have hCl2 : 4 * d / lam ^ 2 ≤ C := by
    dsimp [C]
    have h0 : 0 ≤ A * Real.exp (8 * c) := by positivity
    have h1 : 0 ≤ 2 * Real.sqrt d / lam := by positivity
    linarith
  refine ⟨C, c, hC, hc, _hlambda, ?_⟩
  intro P hmodel n hsampling B delta hdelta x
  dsimp only
  let h := infoBandwidth n delta beta kappa deltaBar
  have hhgeom := infoBandwidth_pos_le (n := n) hbeta hkappa hdelta
    ⟨hdeltaBar, hdeltaBar_lt⟩
  have hh : 0 < h := by simpa [h] using hhgeom.1
  have hupper : delta + h ≤ 1 := by
    have := hhgeom.2
    linarith [hdelta.2]
  let q := localWindowWeight x delta h
  let phi : Fin (ell + 1) → ClampObs J → ℝ := localWindowFeature delta h
  let p := ∫ o, q o ∂P.dataMeasure
  let F : (Fin n → ClampObs J) → (Fin B.I2.card → ClampObs J) :=
    fun z j => z ((B.I2.orderIsoOfFin rfl) j)
  haveI : IsProbabilityMeasure P.dataMeasure := hmodel.probability
  have hp0 : 0 ≤ p := by
    dsimp [p, q]
    exact integral_nonneg_of_ae (ae_of_all _ fun o => (localWindowWeight_mem_unit x delta h o).1)
  have hpLower : K * h * (delta + h) ^ kappa ≤ p := by
    have hl := localWindowWeight_integral_lower P hmodel hkappa hcminus
      (by linarith : 0 ≤ cplus) hpmin x hdelta.1 hh hupper
    have hwpos : 0 < delta + h := by linarith [hdelta.1]
    have htwo : (0 : ℝ) < 2 := by norm_num
    have hrpow : ((delta + h) / 2) ^ kappa =
        (delta + h) ^ kappa / (2 : ℝ) ^ kappa := by
      rw [Real.div_rpow hwpos.le htwo.le]
    rw [hrpow] at hl
    calc
      K * h * (delta + h) ^ kappa =
          pmin * (cminus * ((delta + h) ^ kappa / (2 : ℝ) ^ kappa) * (h / 2)) := by
            dsimp [K]
            ring
      _ ≤ p := by simpa [p, q] using hl
  have hqmeas : Measurable q := measurable_localWindowWeight x delta h
  have hphimeas : ∀ j, Measurable (phi j) := measurable_localWindowFeature delta h
  have hq : ∀ᵐ o ∂P.dataMeasure, 0 ≤ q o ∧ q o ≤ 1 :=
    ae_of_all _ (localWindowWeight_mem_unit x delta h)
  have hphi : ∀ j, ∀ᵐ o ∂P.dataMeasure, |phi j o| ≤ 1 :=
    fun j => ae_of_all _ (abs_localWindowFeature_le_one delta h j)
  have hcoercive : ∀ v : Fin (ell + 1) → ℝ,
      lam * p * (∑ j, (v j) ^ 2) ≤
        ∑ j, ∑ k, v j * v k * ∫ o, q o * phi j o * phi k o ∂P.dataMeasure := by
    intro v
    simpa [ell, lam, p, q, phi] using
      localWindow_populationGram_coercive P hmodel hkappa hcminus
        (by linarith : 0 < cplus) hpmin x hdelta.1 hh hupper v
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  have hsum (f : Fin n → ℝ) :
      (∑ j : Fin B.I2.card, f ((B.I2.orderIsoOfFin rfl) j)) = ∑ i ∈ B.I2, f i := by
    calc
      _ = ∑ i : B.I2, f i := Equiv.sum_comp (B.I2.orderIsoOfFin rfl).toEquiv
        (fun i : B.I2 => f i)
      _ = _ := (Finset.sum_subtype B.I2 (fun _ => Iff.rfl) f).symm
  have hgood (z : Fin n → ClampObs J) :
      Causalean.Stat.Concentration.LocalizedGramGood lam q phi (F z) ↔
        GoodGramEvent B z x ell kappa cminus cplus delta h := by
    simp only [Causalean.Stat.Concentration.LocalizedGramGood, GoodGramEvent]
    have hcount : Causalean.Stat.Concentration.localCount q (F z) =
        (localCount B z x delta h : ℝ) := by
      unfold Causalean.Stat.Concentration.localCount
      change (∑ j : Fin B.I2.card, q (z ((B.I2.orderIsoOfFin rfl) j))) = _
      rw [show (∑ j : Fin B.I2.card, q (z ((B.I2.orderIsoOfFin rfl) j))) =
          ∑ i ∈ B.I2, q (z i) by exact hsum (fun i => q (z i))]
      calc
        (∑ i ∈ B.I2, q (z i)) =
            ∑ i ∈ B.I2, if (z i).X = x ∧
              scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1 then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro i hi
                simp [q, localWindowWeight]
        _ = (localCount B z x delta h : ℝ) := local_active_count_eq B z x delta h hh
    have hentry (j k : Fin (ell + 1)) :
        Causalean.Stat.Concentration.localGramEntry q phi (F z) j k =
          localGram B z x ell delta h j k := by
      unfold Causalean.Stat.Concentration.localGramEntry
      change (∑ a : Fin B.I2.card, q (z ((B.I2.orderIsoOfFin rfl) a)) *
        phi j (z ((B.I2.orderIsoOfFin rfl) a)) *
        phi k (z ((B.I2.orderIsoOfFin rfl) a))) = _
      rw [show (∑ a : Fin B.I2.card, q (z ((B.I2.orderIsoOfFin rfl) a)) *
          phi j (z ((B.I2.orderIsoOfFin rfl) a)) *
          phi k (z ((B.I2.orderIsoOfFin rfl) a))) =
          ∑ i ∈ B.I2, q (z i) * phi j (z i) * phi k (z i) by
            exact hsum (fun i => q (z i) * phi j (z i) * phi k (z i))]
      rw [localGram_apply]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases ha : (z i).X = x ∧ scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1
      · simp [q, phi, localWindowWeight, localWindowFeature, monomialVec, ha]
      · by_cases hu : scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1
        · have hx : (z i).X ≠ x := fun hx => ha ⟨hx, hu⟩
          simp [q, phi, localWindowWeight, localWindowFeature, monomialVec, ha, hx, hu]
        · simp [q, phi, localWindowWeight, localWindowFeature, monomialVec, ha, hu]
    have hquad (v : Fin (ell + 1) → ℝ) :
        Causalean.Stat.Concentration.localGramQuadratic q phi (F z) v =
          matrixQuadratic (localGram B z x ell delta h) v := by
      unfold Causalean.Stat.Concentration.localGramQuadratic matrixQuadratic
      simp_rw [hentry]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hcount]
    constructor
    · rintro ⟨hN, hg⟩
      refine ⟨by exact_mod_cast hN, ?_⟩
      intro v
      have hv := hg v
      rw [hquad] at hv
      dsimp [lam, ell] at hv ⊢
      ring_nf at hv ⊢
      exact hv
    · rintro ⟨hN, hg⟩
      refine ⟨by exact_mod_cast hN, ?_⟩
      intro v
      have hv := hg v
      rw [← hquad] at hv
      dsimp [lam, ell] at hv ⊢
      ring_nf at hv ⊢
      exact hv
  have hprob : (iidProduct P n).real {z |
      ¬ GoodGramEvent B z x ell kappa cminus cplus delta h} ≤ 1 := measureReal_le_one
  by_cases hlarge : 8 ≤ n
  · have hN : 0 < B.I2.card := lt_of_lt_of_le (by omega) B.card_I2
    have hp : 0 < p := lt_of_lt_of_le
      (mul_pos (mul_pos hK hh) (Real.rpow_pos_of_pos (by linarith [hdelta.1]) kappa))
      hpLower
    have hlocal := Causalean.Stat.Concentration.localized_empiricalGram_coercive_of_pos
      P.dataMeasure q phi hqmeas hphimeas hN hp hlam (by norm_num)
      hq hphi rfl hcoercive
    have htail : (iidProduct P n).real {z |
        ¬ GoodGramEvent B z x ell kappa cminus cplus delta h} ≤
        A * Real.exp (-(B.I2.card : ℝ) * p * r) := by
      let E : Set (Fin B.I2.card → ClampObs J) := {omega |
        ¬ Causalean.Stat.Concentration.LocalizedGramGood lam q phi omega}
      have hset : {z : Fin n → ClampObs J |
          ¬ GoodGramEvent B z x ell kappa cminus cplus delta h} = F ⁻¹' E := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        exact not_congr (hgood z).symm
      have hle : (iidProduct P n) (F ⁻¹' E) ≤
          ((iidProduct P n).map F) E := Measure.le_map_apply (by fun_prop) E
      have hreal : (iidProduct P n).real (F ⁻¹' E) ≤
          ((iidProduct P n).map F).real E := by
        exact ENNReal.toReal_mono (measure_ne_top _ _) hle
      rw [hset]
      rw [iid_block_product_law P hsampling B.I2] at hreal
      exact hreal.trans (by simpa [E, A, d, r] using hlocal)
    have hcard : (n : ℝ) / 8 ≤ B.I2.card := by
      have hqcard := B.card_I2
      have hncard : n ≤ 8 * B.I2.card := by omega
      have hncardR : (n : ℝ) ≤ 8 * (B.I2.card : ℝ) := by exact_mod_cast hncard
      linarith
    have hexp : c * (n : ℝ) * h * (delta + h) ^ kappa ≤
        (B.I2.card : ℝ) * p * r := by
      have ht : 0 ≤ h * (delta + h) ^ kappa :=
        mul_nonneg hh.le (Real.rpow_nonneg (by linarith [hdelta.1]) kappa)
      have hcn : c * (n : ℝ) ≤ r * K * (B.I2.card : ℝ) := by
        dsimp [c]
        nlinarith [mul_pos hr hK]
      calc
        c * (n : ℝ) * h * (delta + h) ^ kappa =
            (c * (n : ℝ)) * (h * (delta + h) ^ kappa) := by ring
        _ ≤ (r * K * (B.I2.card : ℝ)) *
            (h * (delta + h) ^ kappa) := mul_le_mul_of_nonneg_right hcn ht
        _ = (B.I2.card : ℝ) * (K * h * (delta + h) ^ kappa) * r := by ring
        _ ≤ (B.I2.card : ℝ) * p * r := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpLower (Nat.cast_nonneg _)) hr.le
    refine ⟨htail.trans ?_, ?_⟩
    · simpa [h] using mul_le_mul hCA (Real.exp_le_exp.mpr (neg_le_neg hexp))
        (Real.exp_pos _).le (by linarith [hA])
    · intro z hz
      have hw := goodGram_weight_controls B z x kappa cminus cplus delta h hh hlam hz
      refine ⟨hw.1, hw.2.1.trans ?_, hw.2.2.trans ?_⟩
      · simpa [d, lam] using hCl1
      · exact div_le_div_of_nonneg_right (by simpa [d, lam] using hCl2)
          (Nat.cast_nonneg _)
  · have heff : (n : ℝ) * h * (delta + h) ^ kappa ≤ 8 := by
      have hn : (n : ℝ) ≤ 8 := by exact_mod_cast (by omega : n ≤ 8)
      have hh1 : h ≤ 1 := hhgeom.2.trans (by linarith)
      have hw1 : (delta + h) ^ kappa ≤ 1 :=
        Real.rpow_le_one (by linarith [hdelta.1]) hupper hkappa
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have hw0 : 0 ≤ (delta + h) ^ kappa :=
        Real.rpow_nonneg (by linarith [hdelta.1, hh]) _
      calc
        (n : ℝ) * h * (delta + h) ^ kappa ≤
            8 * 1 * 1 := by
              exact mul_le_mul (mul_le_mul hn hh1 hh.le (by norm_num)) hw1 hw0 (by norm_num)
        _ = 8 := by norm_num
    refine ⟨hprob.trans ?_, ?_⟩
    · have hbase : 1 ≤ A * Real.exp (8 * c) *
          Real.exp (-c * (n : ℝ) * h * (delta + h) ^ kappa) := by
        rw [mul_assoc, ← Real.exp_add]
        have : 0 ≤ 8 * c + (-c * (n : ℝ) * h * (delta + h) ^ kappa) := by
          nlinarith [hc]
        calc
          1 ≤ A := hA
          _ = A * 1 := by ring
          _ ≤ A * Real.exp (8 * c + -c * (n : ℝ) * h * (delta + h) ^ kappa) :=
            mul_le_mul_of_nonneg_left (Real.one_le_exp this) (by linarith [hA])
      have := hbase.trans (mul_le_mul_of_nonneg_right hCtail (Real.exp_pos _).le)
      simpa [h] using this
    · intro z hz
      have hw := goodGram_weight_controls B z x kappa cminus cplus delta h hh hlam hz
      refine ⟨hw.1, hw.2.1.trans ?_, hw.2.2.trans ?_⟩
      · simpa [d, lam] using hCl1
      · exact div_le_div_of_nonneg_right (by simpa [d, lam] using hCl2)
          (Nat.cast_nonneg _)

end


end CausalSmith.Stat.LmtpThresholdAtomFrontier
