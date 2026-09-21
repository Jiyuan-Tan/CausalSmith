/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Stat.Concentration.EntropyMethod.BousquetDifferential
public import Causalean.Stat.Concentration.EntropyMethod.FiniteEmpiricalDeletion

/-!
# Bousquet entropy comparison for finite empirical suprema

This file sums the conditional Boucheron--Lugosi--Massart slice estimates along the recursive
deletion family. The head--tail product integrals are then transported back to the ordinary
finite product law.
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace Causalean.Stat.Concentration.EntropyMethod

universe u v

private lemma integrable_of_measurable_abs_le'''
    {S : Type*} [MeasurableSpace S] {nu : Measure S} [IsFiniteMeasure nu]
    {f : S → ℝ} {C : ℝ} (hf : Measurable f) (hC : ∀ x, |f x| ≤ C) :
    Integrable f nu := by
  refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

private lemma blmFactor_nonneg {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ blmPhi (-lam) / (1 - Real.exp (-lam) / 2) := by
  have hphi : 0 ≤ blmPhi (-lam) := by
    dsimp [blmPhi]
    linarith [Real.add_one_le_exp (-lam)]
  have hexp : Real.exp (-lam) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hlam)
  have hden : 0 < 1 - Real.exp (-lam) / 2 := by linarith
  exact div_nonneg hphi hden.le

private lemma abs_sliceIncrement_le'''
    {X : Type u} {I : Type v} [Fintype I] [Nonempty I]
    (g : I → X → ℝ) {B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1)
    (n : ℕ) (offset : I → ℝ) (rest : Fin n → X) (x : X) :
    |finiteEmpiricalSliceIncrement I g n offset rest x| ≤ max B 1 := by
  have hwBound : -B ≤ finiteEmpiricalSliceWitness I g n offset rest x :=
    neg_le_of_abs_le (hbound _ x)
  have hlower := finiteEmpiricalSliceWitness_le_increment g n offset rest x
  have hupper' := finiteEmpiricalSliceIncrement_le_one g hupper n offset rest x
  rw [abs_le]
  exact ⟨(neg_le_neg (le_max_left B 1)).trans (hwBound.trans hlower),
    hupper'.trans (le_max_right B 1)⟩

/-- **Finite-class global form of BLM Lemma 12.8.** Under [an i.i.d. probability law
mu](hyp:mu), a [nonempty finite measurable score class g](hyp:I,g,hg) with [nonnegative
offset and score bounds](hyp:hA,hB), [bounded offsets](hyp:hoffset), [scores bounded in absolute
value and above by one](hyp:hbound,hupper), [centered scores](hyp:hmean), and [second moments at
most the nonnegative proxy sigma2](hyp:hsigma,hsecond), the [recursive sum of tilted Bennett
deletion costs](goal) is at most the BLM factor times the expected tilted recursive deletion
budget at every [nonnegative tilt lam](hyp:hlam) and [coordinate count n](hyp:n). -/
theorem finiteEmpiricalDeletionPhiSum_le
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    {A B sigma2 lam : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1)
    (hmean : ∀ i, ∫ x, g i x ∂mu = 0)
    (hsigma : 0 ≤ sigma2) (hsecond : ∀ i, (∫ x, (g i x) ^ 2 ∂mu) ≤ sigma2)
    (hlam : 0 ≤ lam) (n : ℕ) (offset : I → ℝ)
    (hoffset : ∀ i, |offset i| ≤ A) :
    exponentialDeletionPhiSum (fun _ => mu) n lam
        (finiteEmpiricalSupremum I g n offset)
        (finiteEmpiricalDeletionFamily I g n offset) ≤
      (blmPhi (-lam) / (1 - Real.exp (-lam) / 2)) *
        ∫ s, Real.exp (lam * finiteEmpiricalSupremum I g n offset s) *
          (finiteEmpiricalDeletionIncrementSum I g n offset s +
            (n : ℝ) * sigma2 / 2)
          ∂Measure.pi (fun _ : Fin n => mu) := by
  induction n generalizing A offset with
  | zero =>
      simp [exponentialDeletionPhiSum, finiteEmpiricalDeletionFamily,
        finiteEmpiricalDeletionIncrementSum]
  | succ n ih =>
      let theta := blmPhi (-lam) / (1 - Real.exp (-lam) / 2)
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let nu : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => mu)
      let updated : X → I → ℝ := fun x i => offset i + g i x
      let Z : (Fin (n + 1) → X) → ℝ :=
        finiteEmpiricalSupremum I g (n + 1) offset
      let headPart : X × (Fin n → X) → ℝ := fun q =>
        Real.exp (lam * Z (e.symm q)) *
          (finiteEmpiricalSliceIncrement I g n offset q.2 q.1 + sigma2 / 2)
      let tailPart : X × (Fin n → X) → ℝ := fun q =>
        Real.exp (lam * Z (e.symm q)) *
          (finiteEmpiricalDeletionIncrementSum I g n (updated q.1) q.2 +
            (n : ℝ) * sigma2 / 2)
      have hupdatedBound : ∀ x i, |updated x i| ≤ A + B := by
        intro x i
        exact (abs_add_le _ _).trans (add_le_add (hoffset i) (hbound i x))
      have hHeadPoint : ∀ rest,
          (∫ x, Real.exp (lam * Z (e.symm (x, rest))) *
              blmPhi (-lam * (Z (e.symm (x, rest)) -
                finiteEmpiricalSupremum I g n offset rest)) ∂mu) ≤
            theta * ∫ x, headPart (x, rest) ∂mu := by
        intro rest
        have hslice := finiteEmpiricalSlice_phi_cost_le mu g hg hA hB hbound hupper
          hmean hsigma hsecond hlam n offset hoffset rest
        simpa [theta, Z, headPart, e, finiteEmpiricalSupremum_succ,
          finiteEmpiricalSliceIncrement] using hslice
      have hreg := finiteEmpiricalDeletionLogSobolevRegularity
        (fun _ => mu) g hg hA hB hbound hupper lam (n + 1) offset hoffset
      change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hreg
      rcases hreg with ⟨_hHeadExp, _hTailReg, _hHeadEntropyInt,
        hHeadCostInt, _hTailEntropyInt, hTailCostInt⟩
      have hHeadPartJoint : Integrable headPart (mu.prod nu) := by
        apply integrable_of_measurable_abs_le''' (by
          have hZmeas : Measurable (fun q : X × (Fin n → X) => Z (e.symm q)) :=
            (measurable_finiteEmpiricalSupremum g hg (n + 1) offset).comp
              e.symm.measurable
          let newOffset : X → I → ℝ := fun x i => offset i + g i x
          have hnew : Measurable (fun q : X × (Fin n → X) =>
              finiteEmpiricalSupremum I g n (newOffset q.1) q.2) :=
            measurable_finiteEmpiricalSupremum_param g hg n newOffset
              (fun i => by dsimp [newOffset]; fun_prop)
          have hold : Measurable (fun q : X × (Fin n → X) =>
              finiteEmpiricalSupremum I g n offset q.2) :=
            (measurable_finiteEmpiricalSupremum g hg n offset).comp measurable_snd
          dsimp [headPart]
          exact (measurable_const.mul hZmeas).exp.mul
            ((hnew.sub hold).add measurable_const))
          (C := Real.exp (|lam| * (A + ((n : ℝ) + 1) * B)) *
            (max B 1 + sigma2 / 2))
        intro q
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have hZ := abs_finiteEmpiricalSupremum_le g hbound (n + 1)
          offset hoffset (e.symm q)
        have hDelta := abs_sliceIncrement_le''' g hbound hupper n offset q.2 q.1
        have he : Real.exp (lam * Z (e.symm q)) ≤
            Real.exp (|lam| * (A + ((n : ℝ) + 1) * B)) := by
          apply Real.exp_le_exp.mpr
          calc
            _ ≤ |lam * Z (e.symm q)| := le_abs_self _
            _ = |lam| * |Z (e.symm q)| := abs_mul _ _
            _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [Z] using hZ)
              (abs_nonneg lam)
        have ha : |finiteEmpiricalSliceIncrement I g n offset q.2 q.1 +
            sigma2 / 2| ≤ max B 1 + sigma2 / 2 := by
          calc
            _ ≤ |finiteEmpiricalSliceIncrement I g n offset q.2 q.1| +
                |sigma2 / 2| := abs_add_le _ _
            _ ≤ _ := by
              rw [abs_of_nonneg (by positivity : 0 ≤ sigma2 / 2)]
              exact add_le_add hDelta le_rfl
        exact mul_le_mul he ha (abs_nonneg _) (Real.exp_pos _).le
      have hHeadPartInt : Integrable (fun rest => ∫ x, headPart (x, rest) ∂mu) nu :=
        hHeadPartJoint.integral_prod_right
      have hHead :
          (∫ rest, ∫ x, Real.exp (lam * Z (e.symm (x, rest))) *
              blmPhi (-lam * (Z (e.symm (x, rest)) -
                finiteEmpiricalSupremum I g n offset rest)) ∂mu ∂nu) ≤
            theta * ∫ rest, ∫ x, headPart (x, rest) ∂mu ∂nu := by
        rw [← integral_const_mul]
        exact integral_mono hHeadCostInt (hHeadPartInt.const_mul theta) hHeadPoint
      have hTailPoint : ∀ x,
          exponentialDeletionPhiSum (fun _ => mu) n lam
              (finiteEmpiricalSupremum I g n (updated x))
              (finiteEmpiricalDeletionFamily I g n (updated x)) ≤
            theta * ∫ rest, tailPart (x, rest) ∂nu := by
        intro x
        simpa [theta, tailPart, Z, e, updated, finiteEmpiricalSupremum_succ] using
          ih (A := A + B) (by positivity) (updated x) (hupdatedBound x)
      have hTailPartJoint : Integrable tailPart (mu.prod nu) := by
        apply integrable_of_measurable_abs_le''' (by
          have hZmeas : Measurable (fun q : X × (Fin n → X) => Z (e.symm q)) :=
            (measurable_finiteEmpiricalSupremum g hg (n + 1) offset).comp
              e.symm.measurable
          have hsumMeas : Measurable (fun q : X × (Fin n → X) =>
              finiteEmpiricalDeletionIncrementSum I g n (updated q.1) q.2) :=
            measurable_finiteEmpiricalDeletionIncrementSum_param g hg n updated
              (fun i => by dsimp [updated]; fun_prop)
          dsimp [tailPart]
          exact (measurable_const.mul hZmeas).exp.mul
            (hsumMeas.add measurable_const))
          (C := Real.exp (|lam| * (A + ((n : ℝ) + 1) * B)) *
            ((n : ℝ) * max B 1 + (n : ℝ) * sigma2 / 2))
        intro q
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have hZ := abs_finiteEmpiricalSupremum_le g hbound (n + 1)
          offset hoffset (e.symm q)
        have hsum := abs_finiteEmpiricalDeletionIncrementSum_le g hbound hupper
          n (updated q.1) q.2
        have he : Real.exp (lam * Z (e.symm q)) ≤
            Real.exp (|lam| * (A + ((n : ℝ) + 1) * B)) := by
          apply Real.exp_le_exp.mpr
          calc
            _ ≤ |lam * Z (e.symm q)| := le_abs_self _
            _ = |lam| * |Z (e.symm q)| := abs_mul _ _
            _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [Z] using hZ)
              (abs_nonneg lam)
        have ha : |finiteEmpiricalDeletionIncrementSum I g n (updated q.1) q.2 +
            (n : ℝ) * sigma2 / 2| ≤
            (n : ℝ) * max B 1 + (n : ℝ) * sigma2 / 2 := by
          calc
            _ ≤ |finiteEmpiricalDeletionIncrementSum I g n (updated q.1) q.2| +
                |(n : ℝ) * sigma2 / 2| := abs_add_le _ _
            _ ≤ _ := by
              rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) * sigma2 / 2)]
              exact add_le_add hsum le_rfl
        exact mul_le_mul he ha (abs_nonneg _) (Real.exp_pos _).le
      have hTailPartInt : Integrable (fun x => ∫ rest, tailPart (x, rest) ∂nu) mu :=
        hTailPartJoint.integral_prod_left
      have hTail :
          (∫ x, exponentialDeletionPhiSum (fun _ => mu) n lam
              (finiteEmpiricalSupremum I g n (updated x))
              (finiteEmpiricalDeletionFamily I g n (updated x)) ∂mu) ≤
            theta * ∫ x, ∫ rest, tailPart (x, rest) ∂nu ∂mu := by
        have hTailCostInt' : Integrable (fun x =>
            exponentialDeletionPhiSum (fun _ => mu) n lam
              (finiteEmpiricalSupremum I g n (updated x))
              (finiteEmpiricalDeletionFamily I g n (updated x))) mu := by
          simpa [updated, e, finiteEmpiricalSupremum_succ] using hTailCostInt
        rw [← integral_const_mul]
        exact integral_mono hTailCostInt' (hTailPartInt.const_mul theta) hTailPoint
      have hsplit : MeasurePreserving e
          (Measure.pi (fun _ : Fin (n + 1) => mu)) (mu.prod nu) := by
        simpa [e, nu] using
          (MeasureTheory.measurePreserving_piFinSuccAbove
            (μ := fun _ : Fin (n + 1) => mu) 0)
      have hBudget :
          (∫ rest, ∫ x, headPart (x, rest) ∂mu ∂nu) +
              (∫ x, ∫ rest, tailPart (x, rest) ∂nu ∂mu) =
            ∫ s, Real.exp (lam * finiteEmpiricalSupremum I g (n + 1) offset s) *
              (finiteEmpiricalDeletionIncrementSum I g (n + 1) offset s +
                ((n + 1 : ℕ) : ℝ) * sigma2 / 2)
              ∂Measure.pi (fun _ : Fin (n + 1) => mu) := by
        have hheadSwap : (∫ rest, ∫ x, headPart (x, rest) ∂mu ∂nu) =
            ∫ p, headPart p ∂(mu.prod nu) :=
          (integral_prod_symm headPart hHeadPartJoint).symm
        have htailProd : (∫ x, ∫ rest, tailPart (x, rest) ∂nu ∂mu) =
            ∫ p, tailPart p ∂(mu.prod nu) :=
          (integral_prod tailPart hTailPartJoint).symm
        rw [hheadSwap, htailProd, ← integral_add hHeadPartJoint hTailPartJoint]
        let budget : (Fin (n + 1) → X) → ℝ := fun s =>
          Real.exp (lam * finiteEmpiricalSupremum I g (n + 1) offset s) *
            (finiteEmpiricalDeletionIncrementSum I g (n + 1) offset s +
              ((n + 1 : ℕ) : ℝ) * sigma2 / 2)
        have htransport := hsplit.integral_comp' (headPart + tailPart)
        have hpoint : (headPart + tailPart) ∘ e = budget := by
          funext s
          dsimp [headPart, tailPart, budget, Z, updated]
          rw [e.symm_apply_apply]
          change Real.exp _ * (_ + sigma2 / 2) +
              Real.exp _ * (_ + (n : ℝ) * sigma2 / 2) =
            Real.exp _ * (_ + ((n + 1 : ℕ) : ℝ) * sigma2 / 2)
          rw [finiteEmpiricalDeletionIncrementSum]
          dsimp [e]
          push_cast
          ring
        calc
          (∫ p, headPart p + tailPart p ∂(mu.prod nu)) =
              ∫ s, (headPart + tailPart) (e s)
                ∂Measure.pi (fun _ : Fin (n + 1) => mu) := htransport.symm
          _ = ∫ s, budget s ∂Measure.pi (fun _ : Fin (n + 1) => mu) := by
            apply integral_congr_ae
            filter_upwards with s
            exact congrFun hpoint s
          _ = _ := rfl
      have htotal :
          (∫ rest, ∫ x, Real.exp (lam * Z (e.symm (x, rest))) *
              blmPhi (-lam * (Z (e.symm (x, rest)) -
                finiteEmpiricalSupremum I g n offset rest)) ∂mu ∂nu) +
            (∫ x, exponentialDeletionPhiSum (fun _ => mu) n lam
              (finiteEmpiricalSupremum I g n (updated x))
              (finiteEmpiricalDeletionFamily I g n (updated x)) ∂mu) ≤
          theta * ∫ s,
            Real.exp (lam * finiteEmpiricalSupremum I g (n + 1) offset s) *
              (finiteEmpiricalDeletionIncrementSum I g (n + 1) offset s +
                ((n + 1 : ℕ) : ℝ) * sigma2 / 2)
              ∂Measure.pi (fun _ : Fin (n + 1) => mu) := by
        calc
        _ ≤ theta * (∫ rest, ∫ x, headPart (x, rest) ∂mu ∂nu) +
            theta * (∫ x, ∫ rest, tailPart (x, rest) ∂nu ∂mu) :=
          add_le_add hHead hTail
        _ = theta * ((∫ rest, ∫ x, headPart (x, rest) ∂mu ∂nu) +
            (∫ x, ∫ rest, tailPart (x, rest) ∂nu ∂mu)) := by ring
        _ = _ := by rw [hBudget]
      simpa [exponentialDeletionPhiSum, finiteEmpiricalDeletionFamily, theta, Z, e, nu,
        updated, finiteEmpiricalSupremum_succ] using htotal

/-- **Finite-class entropy form of BLM Lemma 12.8.** Under [an i.i.d. probability law
mu](hyp:mu), a [nonempty finite measurable centered score class g](hyp:I,g,hg,hmean) whose
scores are [bounded in absolute value by the nonnegative constant B](hyp:hB,hbound), [at most
one](hyp:hupper), and have [second moments at most the nonnegative proxy sigma2](hyp:hsigma,hsecond), the [entropy of the exponentially tilted zero-offset empirical supremum is bounded by
the BLM factor times its tilted affine variance budget](goal) at every [nonnegative tilt
lam](hyp:hlam) and [coordinate count n](hyp:n). -/
theorem entropy_exp_finiteEmpiricalSupremum_le
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    {B sigma2 lam : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1)
    (hmean : ∀ i, ∫ x, g i x ∂mu = 0)
    (hsigma : 0 ≤ sigma2) (hsecond : ∀ i, (∫ x, (g i x) ^ 2 ∂mu) ≤ sigma2)
    (hlam : 0 ≤ lam) (n : ℕ) :
    entropy (Measure.pi (fun _ : Fin n => mu))
        (fun s => Real.exp
          (lam * finiteEmpiricalSupremum I g n (fun _ => 0) s)) ≤
      (blmPhi (-lam) / (1 - Real.exp (-lam) / 2)) *
        ∫ s, Real.exp (lam * finiteEmpiricalSupremum I g n (fun _ => 0) s) *
          (finiteEmpiricalSupremum I g n (fun _ => 0) s +
            (n : ℝ) * sigma2 / 2)
          ∂Measure.pi (fun _ : Fin n => mu) := by
  let productMeasure : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => mu)
  let Z := finiteEmpiricalSupremum I g n (fun _ => 0)
  let D := finiteEmpiricalDeletionIncrementSum I g n (fun _ => 0)
  let theta := blmPhi (-lam) / (1 - Real.exp (-lam) / 2)
  have hEntropy := entropy_exp_finiteEmpiricalSupremum_le_deletion
    (fun _ => mu) g hg (A := 0) (B := B) (by norm_num) hB hbound hupper
    lam n (fun _ => 0) (fun _ => by simp)
  have hCost := finiteEmpiricalDeletionPhiSum_le mu g hg
    (A := 0) (B := B) (sigma2 := sigma2) (lam := lam) (by norm_num) hB
    hbound hupper hmean hsigma hsecond hlam n (fun _ => 0) (fun _ => by simp)
  have hDInt : Integrable (fun s =>
      Real.exp (lam * Z s) * (D s + (n : ℝ) * sigma2 / 2)) productMeasure := by
    apply integrable_of_measurable_abs_le''' (by
      dsimp [Z, D]
      fun_prop)
      (C := Real.exp (|lam| * ((n : ℝ) * B)) *
        ((n : ℝ) * max B 1 + (n : ℝ) * sigma2 / 2))
    intro s
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hZ := abs_finiteEmpiricalSupremum_le g (A := 0) (B := B) hbound n
      (fun _ => 0) (fun _ => by simp) s
    have hD := abs_finiteEmpiricalDeletionIncrementSum_le g hbound hupper n
      (fun _ => 0) s
    have he : Real.exp (lam * Z s) ≤ Real.exp (|lam| * ((n : ℝ) * B)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ |lam * Z s| := le_abs_self _
        _ = |lam| * |Z s| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [Z] using hZ) (abs_nonneg lam)
    have ha : |D s + (n : ℝ) * sigma2 / 2| ≤
        (n : ℝ) * max B 1 + (n : ℝ) * sigma2 / 2 := by
      calc
        _ ≤ |D s| + |(n : ℝ) * sigma2 / 2| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) * sigma2 / 2)]
          exact add_le_add (by simpa [D] using hD) le_rfl
    exact mul_le_mul he ha (abs_nonneg _) (Real.exp_pos _).le
  have hZInt : Integrable (fun s =>
      Real.exp (lam * Z s) * (Z s + (n : ℝ) * sigma2 / 2)) productMeasure := by
    apply integrable_of_measurable_abs_le''' (by
      dsimp [Z]
      fun_prop)
      (C := Real.exp (|lam| * ((n : ℝ) * B)) *
        ((n : ℝ) * B + (n : ℝ) * sigma2 / 2))
    intro s
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hZ := abs_finiteEmpiricalSupremum_le g (A := 0) (B := B) hbound n
      (fun _ => 0) (fun _ => by simp) s
    have he : Real.exp (lam * Z s) ≤ Real.exp (|lam| * ((n : ℝ) * B)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ |lam * Z s| := le_abs_self _
        _ = |lam| * |Z s| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [Z] using hZ) (abs_nonneg lam)
    have ha : |Z s + (n : ℝ) * sigma2 / 2| ≤
        (n : ℝ) * B + (n : ℝ) * sigma2 / 2 := by
      calc
        _ ≤ |Z s| + |(n : ℝ) * sigma2 / 2| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) * sigma2 / 2)]
          exact add_le_add (by simpa [Z] using hZ) le_rfl
    exact mul_le_mul he ha (abs_nonneg _) (Real.exp_pos _).le
  have hIntegral :
      (∫ s, Real.exp (lam * Z s) * (D s + (n : ℝ) * sigma2 / 2)
          ∂productMeasure) ≤
        ∫ s, Real.exp (lam * Z s) * (Z s + (n : ℝ) * sigma2 / 2)
          ∂productMeasure := by
    apply integral_mono hDInt hZInt
    intro s
    exact mul_le_mul_of_nonneg_left
      (by
        dsimp [D, Z]
        exact add_le_add (finiteEmpiricalDeletionIncrementSum_le_supremum g n s) le_rfl)
      (Real.exp_pos _).le
  calc
    _ ≤ exponentialDeletionPhiSum (fun _ => mu) n lam Z
        (finiteEmpiricalDeletionFamily I g n (fun _ => 0)) := by
      simpa [Z, productMeasure] using hEntropy
    _ ≤ theta * ∫ s, Real.exp (lam * Z s) *
        (D s + (n : ℝ) * sigma2 / 2) ∂productMeasure := by
      simpa [theta, Z, D, productMeasure] using hCost
    _ ≤ theta * ∫ s, Real.exp (lam * Z s) *
        (Z s + (n : ℝ) * sigma2 / 2) ∂productMeasure :=
      mul_le_mul_of_nonneg_left hIntegral (blmFactor_nonneg hlam)

/-- **Finite-class centered MGF bound, with conservative constants.** Under [an i.i.d.
probability law mu](hyp:mu), a [nonempty finite measurable centered score class
g](hyp:I,g,hg,hmean) whose scores are [bounded in absolute value by the nonnegative constant
B](hyp:hB,hbound), [at most one](hyp:hupper), and have [second moments at most the nonnegative
proxy sigma2](hyp:hsigma,hsecond), the [centered MGF of the zero-offset n-coordinate empirical
supremum](goal) obeys the displayed BLM bound at [a nonnegative tilt below one half](hyp:hlam,hlam_half). -/
theorem finiteEmpiricalSupremum_mgf_centered_le
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    {B sigma2 : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1)
    (hmean : ∀ i, ∫ x, g i x ∂mu = 0)
    (hsigma : 0 ≤ sigma2) (hsecond : ∀ i, (∫ x, (g i x) ^ 2 ∂mu) ≤ sigma2)
    (n : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) (hlam_half : 2 * lam < 1) :
    mgf
        (fun s => finiteEmpiricalSupremum I g n (fun _ => 0) s -
          ∫ r, finiteEmpiricalSupremum I g n (fun _ => 0) r
            ∂Measure.pi (fun _ : Fin n => mu))
        (Measure.pi (fun _ : Fin n => mu)) lam ≤
      Real.exp
        ((2 * (∫ s, finiteEmpiricalSupremum I g n (fun _ => 0) s
            ∂Measure.pi (fun _ : Fin n => mu)) + (n : ℝ) * sigma2) * lam ^ 2 /
          (1 - 2 * lam)) := by
  let productMeasure : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => mu)
  let Z := finiteEmpiricalSupremum I g n (fun _ => 0)
  have hExp : ∀ t : ℝ, Integrable (fun s => Real.exp (t * Z s)) productMeasure := by
    intro t
    simpa [Z, productMeasure] using
      integrable_exp_finiteEmpiricalSupremum mu g hg hbound n t
  have hEnt : ∀ t : ℝ, 0 < t → 2 * t < 1 →
      entropy productMeasure (fun s => Real.exp (t * Z s)) ≤
        (blmPhi (-t) / (1 - Real.exp (-t) / 2)) *
          ∫ s, Real.exp (t * Z s) * (Z s + (n : ℝ) * sigma2 / 2)
            ∂productMeasure := by
    intro t ht _htHalf
    simpa [Z, productMeasure] using
      entropy_exp_finiteEmpiricalSupremum_le mu g hg hB hbound hupper
        hmean hsigma hsecond ht.le n
  have hZMean : 0 ≤ ∫ s, Z s ∂productMeasure := by
    simpa [Z, productMeasure] using
      integral_finiteEmpiricalSupremum_nonneg mu g hg hbound hmean n
  have hmgf := blm_mgf_centered_le (Z := Z) (c := (n : ℝ) * sigma2 / 2)
    (by positivity) hExp hEnt hZMean hlam hlam_half
  dsimp [Z, productMeasure] at hmgf ⊢
  convert hmgf using 1 <;> ring

/-- **Finite-class Bousquet upper tail, with conservative constants.** Under [an i.i.d.
probability law mu](hyp:mu), a [nonempty finite measurable centered score class
g](hyp:I,g,hg,hmean) whose scores are [bounded in absolute value by the nonnegative constant
B](hyp:hB,hbound), [at most one](hyp:hupper), and have [second moments at most the nonnegative
proxy sigma2](hyp:hsigma,hsecond), every [positive deviation t](hyp:ht) [obeys the stated
variance-sensitive upper tail](goal) for the [zero-offset n-coordinate empirical supremum](hyp:n),
provided its [mean plus half the total variance proxy is positive](hyp:hscale). The denominator
is the explicit conservative value 8 E Z + 4 n sigma2 + 4 t. -/
theorem finiteEmpiricalSupremum_upper_tail
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    {B sigma2 : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1)
    (hmean : ∀ i, ∫ x, g i x ∂mu = 0)
    (hsigma : 0 ≤ sigma2) (hsecond : ∀ i, (∫ x, (g i x) ^ 2 ∂mu) ≤ sigma2)
    (n : ℕ)
    (hscale : 0 < (∫ s, finiteEmpiricalSupremum I g n (fun _ => 0) s
        ∂Measure.pi (fun _ : Fin n => mu)) + (n : ℝ) * sigma2 / 2)
    {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin n => mu)).real
        {s | t ≤ finiteEmpiricalSupremum I g n (fun _ => 0) s -
          ∫ r, finiteEmpiricalSupremum I g n (fun _ => 0) r
            ∂Measure.pi (fun _ : Fin n => mu)} ≤
      Real.exp (-t ^ 2 /
        (8 * ((∫ s, finiteEmpiricalSupremum I g n (fun _ => 0) s
          ∂Measure.pi (fun _ : Fin n => mu)) + (n : ℝ) * sigma2 / 2) + 4 * t)) := by
  let productMeasure : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => mu)
  let Z := finiteEmpiricalSupremum I g n (fun _ => 0)
  have hExp : ∀ lam : ℝ, Integrable (fun s => Real.exp (lam * Z s)) productMeasure := by
    intro lam
    simpa [Z, productMeasure] using
      integrable_exp_finiteEmpiricalSupremum mu g hg hbound n lam
  have hEnt : ∀ lam : ℝ, 0 < lam → 2 * lam < 1 →
      entropy productMeasure (fun s => Real.exp (lam * Z s)) ≤
        (blmPhi (-lam) / (1 - Real.exp (-lam) / 2)) *
          ∫ s, Real.exp (lam * Z s) *
            (Z s + (n : ℝ) * sigma2 / 2) ∂productMeasure := by
    intro lam hlam _hlamHalf
    simpa [Z, productMeasure] using
      entropy_exp_finiteEmpiricalSupremum_le mu g hg hB hbound hupper
        hmean hsigma hsecond hlam.le n
  have hZMean : 0 ≤ ∫ s, Z s ∂productMeasure := by
    simpa [Z, productMeasure] using
      integral_finiteEmpiricalSupremum_nonneg mu g hg hbound hmean n
  simpa [Z, productMeasure] using
    blm_upper_tail (Z := Z) (c := (n : ℝ) * sigma2 / 2)
      (by positivity) hExp hEnt hZMean (by simpa [Z, productMeasure] using hscale) ht

end Causalean.Stat.Concentration.EntropyMethod
