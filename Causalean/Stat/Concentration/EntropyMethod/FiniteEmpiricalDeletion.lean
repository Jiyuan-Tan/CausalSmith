/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Stat.Concentration.EntropyMethod.FiniteEmpiricalEntropy

/-!
# Regularity of finite empirical deletion costs

This file proves the parameter-measurability and boundedness induction needed to integrate the
recursive deletion cost for a finite empirical supremum.  It is the remaining Fubini component
of the deletion-coordinate modified logarithmic-Sobolev assembly.
-/

public section

open MeasureTheory Real

namespace Causalean.Stat.Concentration.EntropyMethod

universe u v

private lemma abs_sliceIncrement_le'
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

private lemma integrable_of_measurable_abs_le''
    {S : Type*} [MeasurableSpace S] {nu : Measure S} [IsFiniteMeasure nu]
    {f : S → ℝ} {C : ℝ} (hf : Measurable f) (hC : ∀ x, |f x| ≤ C) :
    Integrable f nu := by
  refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

private theorem measurable_bounded_finiteEmpiricalDeletionPhiSum_param
    {X P : Type u} {I : Type v} [MeasurableSpace X] [MeasurableSpace P]
    [Fintype I] [Nonempty I]
    (mu : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (mu i)]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1)
    (lam : ℝ) (n : ℕ) (offset : P → I → ℝ)
    (hoffsetMeas : ∀ i, Measurable (fun p => offset p i))
    (hoffsetBound : ∀ p i, |offset p i| ≤ A) :
    Measurable (fun p => exponentialDeletionPhiSum mu n lam
        (finiteEmpiricalSupremum I g n (offset p))
        (finiteEmpiricalDeletionFamily I g n (offset p))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p,
        |exponentialDeletionPhiSum mu n lam
          (finiteEmpiricalSupremum I g n (offset p))
          (finiteEmpiricalDeletionFamily I g n (offset p))| ≤ C := by
  induction n generalizing P mu A with
  | zero =>
      constructor
      · simp [exponentialDeletionPhiSum, finiteEmpiricalDeletionFamily]
      · exact ⟨0, le_rfl, by simp [exponentialDeletionPhiSum,
          finiteEmpiricalDeletionFamily]⟩
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let nu : Measure (Fin n → X) := Measure.pi (fun j : Fin n => mu (j.val + 1))
      let updated : (P × X) → I → ℝ := fun q i => offset q.1 i + g i q.2
      have hupdatedMeas : ∀ i, Measurable (fun q => updated q i) := by
        intro i
        dsimp [updated]
        fun_prop
      have hupdatedBound : ∀ q i, |updated q i| ≤ A + B := by
        intro q i
        exact (abs_add_le _ _).trans
          (add_le_add (hoffsetBound q.1 i) (hbound i q.2))
      have htail := ih (P := P × X) (mu := fun i => mu (i + 1))
        (A := A + B) (by positivity) updated hupdatedMeas hupdatedBound
      rcases htail.2 with ⟨Ctail, hCtail, htailBound⟩
      let headJoint : X × ((Fin n → X) × P) → ℝ := fun q =>
        Real.exp (lam * finiteEmpiricalSupremum I g n
          (fun i => offset q.2.2 i + g i q.1) q.2.1) *
        blmPhi (-lam * (finiteEmpiricalSupremum I g n
          (fun i => offset q.2.2 i + g i q.1) q.2.1 -
          finiteEmpiricalSupremum I g n (offset q.2.2) q.2.1))
      have hfullMeas : Measurable (fun q : X × ((Fin n → X) × P) =>
          finiteEmpiricalSupremum I g n
            (fun i => offset q.2.2 i + g i q.1) q.2.1) := by
        have hparam := measurable_finiteEmpiricalSupremum_param g hg n updated hupdatedMeas
        exact hparam.comp (((measurable_snd.comp measurable_snd).prodMk measurable_fst).prodMk
          (measurable_fst.comp measurable_snd))
      have hdeletedMeas : Measurable (fun q : X × ((Fin n → X) × P) =>
          finiteEmpiricalSupremum I g n (offset q.2.2) q.2.1) := by
        have hparam := measurable_finiteEmpiricalSupremum_param g hg n offset hoffsetMeas
        exact hparam.comp ((measurable_snd.comp measurable_snd).prodMk
          (measurable_fst.comp measurable_snd))
      have hheadJoint : Measurable headJoint := by
        dsimp [headJoint, blmPhi]
        fun_prop
      have hinner : Measurable (fun q : (Fin n → X) × P =>
          ∫ x, headJoint (x, q) ∂mu 0) :=
        hheadJoint.stronglyMeasurable.integral_prod_left'.measurable
      have hhead : Measurable (fun p => ∫ rest, ∫ x,
          headJoint (x, (rest, p)) ∂mu 0 ∂nu) :=
        hinner.stronglyMeasurable.integral_prod_left'.measurable
      have htailMeas : Measurable (fun p => ∫ x,
          exponentialDeletionPhiSum (fun i => mu (i + 1)) n lam
            (fun rest => finiteEmpiricalSupremum I g n (updated (p, x)) rest)
            (finiteEmpiricalDeletionFamily I g n (updated (p, x))) ∂mu 0) := by
        have hswap : Measurable (fun q : X × P =>
            exponentialDeletionPhiSum (fun i => mu (i + 1)) n lam
              (fun rest => finiteEmpiricalSupremum I g n (updated (q.2, q.1)) rest)
              (finiteEmpiricalDeletionFamily I g n (updated (q.2, q.1)))) :=
          by
            convert htail.1.comp measurable_swap using 1
            funext q
            congr 1
        exact hswap.stronglyMeasurable.integral_prod_left'.measurable
      constructor
      · simp only [exponentialDeletionPhiSum, finiteEmpiricalDeletionFamily]
        simp_rw [finiteEmpiricalSupremum_succ]
        change Measurable ((fun p => ∫ rest, ∫ x,
          headJoint (x, (rest, p)) ∂mu 0 ∂nu) +
          fun p => ∫ x, exponentialDeletionPhiSum (fun i => mu (i + 1)) n lam
            (fun rest => finiteEmpiricalSupremum I g n (updated (p, x)) rest)
            (finiteEmpiricalDeletionFamily I g n (updated (p, x))) ∂mu 0)
        exact hhead.add htailMeas
      · let K := A + ((n : ℝ) + 1) * B
        let D := max B 1
        let H := Real.exp (|lam| * K) *
          (Real.exp (|lam| * D) + |lam| * D + 1)
        have hK : 0 ≤ K := by dsimp [K]; positivity
        have hD : 0 ≤ D := le_trans hB (le_max_left B 1)
        have hH : 0 ≤ H := by dsimp [H]; positivity
        refine ⟨H + Ctail, add_nonneg hH hCtail, ?_⟩
        intro p
        have hheadPoint : ∀ x rest, |headJoint (x, (rest, p))| ≤ H := by
          intro x rest
          have hZ := abs_finiteEmpiricalSupremum_le g hbound (n + 1)
            (offset p) (hoffsetBound p) (e.symm (x, rest))
          have hDelta := abs_sliceIncrement_le' g hbound hupper n (offset p) rest x
          have hZeq : finiteEmpiricalSupremum I g (n + 1) (offset p)
              (e.symm (x, rest)) = finiteEmpiricalSupremum I g n
                (fun i => offset p i + g i x) rest := by
            simpa [e] using finiteEmpiricalSupremum_succ g n (offset p)
              (e.symm (x, rest))
          rw [hZeq] at hZ
          have harg : |-lam * (finiteEmpiricalSupremum I g n
              (fun i => offset p i + g i x) rest -
                finiteEmpiricalSupremum I g n (offset p) rest)| ≤
              |lam| * D := by
            change |-lam * finiteEmpiricalSliceIncrement I g n (offset p) rest x| ≤ _
            rw [abs_mul, abs_neg]
            exact mul_le_mul_of_nonneg_left hDelta (abs_nonneg lam)
          have hexp : Real.exp (lam * finiteEmpiricalSupremum I g n
              (fun i => offset p i + g i x) rest) ≤ Real.exp (|lam| * K) := by
            apply Real.exp_le_exp.mpr
            calc
              _ ≤ |lam * finiteEmpiricalSupremum I g n
                    (fun i => offset p i + g i x) rest| := le_abs_self _
              _ = |lam| * |finiteEmpiricalSupremum I g n
                    (fun i => offset p i + g i x) rest| := abs_mul _ _
              _ ≤ |lam| * K := mul_le_mul_of_nonneg_left (by simpa [K] using hZ)
                (abs_nonneg lam)
          have hphi : |blmPhi (-lam *
              (finiteEmpiricalSupremum I g n (fun i => offset p i + g i x) rest -
                finiteEmpiricalSupremum I g n (offset p) rest))| ≤
              Real.exp (|lam| * D) + |lam| * D + 1 := by
            let r := -lam *
              (finiteEmpiricalSupremum I g n (fun i => offset p i + g i x) rest -
                finiteEmpiricalSupremum I g n (offset p) rest)
            dsimp [blmPhi]
            change |Real.exp r - r - 1| ≤ _
            calc
              |Real.exp r - r - 1| ≤ |Real.exp r - r| + |(1 : ℝ)| := abs_sub _ _
              _ ≤ (|Real.exp r| + |r|) + 1 := by
                simpa using add_le_add_right (abs_sub (Real.exp r) r) 1
              _ = Real.exp r + |r| + 1 := by rw [abs_of_pos (Real.exp_pos _)]
              _ ≤ Real.exp (|lam| * D) + |lam| * D + 1 := by
                have her : Real.exp r ≤ Real.exp (|lam| * D) :=
                  Real.exp_le_exp.mpr ((le_abs_self r).trans (by simpa [r] using harg))
                have hr : |r| ≤ |lam| * D := by simpa [r] using harg
                linarith
          change |Real.exp _ * blmPhi _| ≤ H
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul hexp hphi (abs_nonneg _) (Real.exp_pos _).le
        have hheadBound : |∫ rest, ∫ x, headJoint (x, (rest, p)) ∂mu 0 ∂nu| ≤ H := by
          have hinnerBound : ∀ rest,
              |∫ x, headJoint (x, (rest, p)) ∂mu 0| ≤ H := by
            intro rest
            rw [← Real.norm_eq_abs]
            simpa using norm_integral_le_of_norm_le_const
              (μ := mu 0) (C := H) (f := fun x => headJoint (x, (rest, p)))
              (ae_of_all _ fun x => by
                simpa [Real.norm_eq_abs] using hheadPoint x rest)
          rw [← Real.norm_eq_abs]
          simpa using norm_integral_le_of_norm_le_const
            (μ := nu) (C := H)
            (f := fun rest => ∫ x, headJoint (x, (rest, p)) ∂mu 0)
            (ae_of_all _ fun rest => by
              simpa [Real.norm_eq_abs] using hinnerBound rest)
        have htailIntegral : |∫ x,
            exponentialDeletionPhiSum (fun i => mu (i + 1)) n lam
              (finiteEmpiricalSupremum I g n (updated (p, x)))
              (finiteEmpiricalDeletionFamily I g n (updated (p, x))) ∂mu 0| ≤ Ctail := by
          rw [← Real.norm_eq_abs]
          simpa using norm_integral_le_of_norm_le_const
            (μ := mu 0) (C := Ctail)
            (f := fun x => exponentialDeletionPhiSum (fun i => mu (i + 1)) n lam
              (finiteEmpiricalSupremum I g n (updated (p, x)))
              (finiteEmpiricalDeletionFamily I g n (updated (p, x))))
            (ae_of_all _ fun x => by
              simpa [Real.norm_eq_abs] using htailBound (p, x))
        have hadd : |(∫ rest, ∫ x, headJoint (x, (rest, p)) ∂mu 0 ∂nu) +
          ∫ x, exponentialDeletionPhiSum (fun i => mu (i + 1)) n lam
            (finiteEmpiricalSupremum I g n (updated (p, x)))
            (finiteEmpiricalDeletionFamily I g n (updated (p, x))) ∂mu 0| ≤
            H + Ctail :=
          (abs_add_le _ _).trans (add_le_add hheadBound htailIntegral)
        simpa [exponentialDeletionPhiSum, finiteEmpiricalDeletionFamily, headJoint,
          updated, e, nu, finiteEmpiricalSupremum_succ] using hadd

/-- Under [coordinate probability laws `mu`](hyp:mu,hprob), a [nonempty finite measurable score
class `g`](hyp:I,g,hg) whose scores are [bounded by `B`](hyp:hbound) and [at most one](hyp:hupper),
and [offsets bounded by the nonnegative constant `A`](hyp:hA,hoffset), the [recursive empirical
supremum and its deletion family satisfy every deletion log-Sobolev regularity condition](goal)
at [tilt `lam`](hyp:lam) and [coordinate count `n`](hyp:n), provided [the score bound is
nonnegative](hyp:hB). -/
theorem finiteEmpiricalDeletionLogSobolevRegularity
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (mu : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (mu i)]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1)
    (lam : ℝ) (n : ℕ) (offset : I → ℝ) (hoffset : ∀ i, |offset i| ≤ A) :
    DeletionLogSobolevRegularity mu n lam
      (finiteEmpiricalSupremum I g n offset)
      (finiteEmpiricalDeletionFamily I g n offset) := by
  induction n generalizing mu A offset with
  | zero => trivial
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let nu : Measure (Fin n → X) := Measure.pi (fun j : Fin n => mu (j.val + 1))
      let K := A + ((n : ℝ) + 1) * B
      let D := max B 1
      let E := Real.exp (|lam| * K)
      let P := Real.exp (|lam| * D) + |lam| * D + 1
      have hK : 0 ≤ K := by dsimp [K]; positivity
      have hD : 0 ≤ D := hB.trans (le_max_left B 1)
      have hZBound : ∀ s, |finiteEmpiricalSupremum I g (n + 1) offset s| ≤ K := by
        intro s
        simpa [K] using abs_finiteEmpiricalSupremum_le g hbound (n + 1)
          offset hoffset s
      have hZMeas : Measurable (finiteEmpiricalSupremum I g (n + 1) offset) :=
        measurable_finiteEmpiricalSupremum g hg (n + 1) offset
      have hsectionMeas (rest : Fin n → X) : Measurable (fun x =>
          finiteEmpiricalSupremum I g (n + 1) offset (e.symm (x, rest))) :=
        hZMeas.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have hExpBound (rest : Fin n → X) (x : X) :
          Real.exp (lam * finiteEmpiricalSupremum I g (n + 1) offset
            (e.symm (x, rest))) ≤ E := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ |lam * finiteEmpiricalSupremum I g (n + 1) offset
                (e.symm (x, rest))| := le_abs_self _
          _ = |lam| * |finiteEmpiricalSupremum I g (n + 1) offset
                (e.symm (x, rest))| := abs_mul _ _
          _ ≤ |lam| * K := mul_le_mul_of_nonneg_left (hZBound _) (abs_nonneg lam)
      have hHeadExp : ∀ rest, Integrable (fun x => Real.exp
          (lam * finiteEmpiricalSupremum I g (n + 1) offset
            (e.symm (x, rest)))) (mu 0) ∧
          Integrable (fun x => Real.exp
            (lam * finiteEmpiricalSupremum I g (n + 1) offset
              (e.symm (x, rest))) *
            (lam * finiteEmpiricalSupremum I g (n + 1) offset
              (e.symm (x, rest)))) (mu 0) := by
        intro rest
        constructor
        · apply integrable_of_measurable_abs_le'' (by fun_prop) (C := E)
          intro x
          rw [abs_of_pos (Real.exp_pos _)]
          exact hExpBound rest x
        · apply integrable_of_measurable_abs_le'' (by fun_prop)
            (C := E * (|lam| * K))
          intro x
          rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
          have hzlam : |lam| * |finiteEmpiricalSupremum I g (n + 1) offset
              (e.symm (x, rest))| ≤ |lam| * K :=
            mul_le_mul_of_nonneg_left (hZBound _) (abs_nonneg lam)
          calc
            Real.exp _ * (|lam| * |finiteEmpiricalSupremum I g (n + 1) offset
                (e.symm (x, rest))|) ≤ Real.exp _ * (|lam| * K) :=
              mul_le_mul_of_nonneg_left hzlam (Real.exp_pos _).le
            _ ≤ E * (|lam| * K) :=
              mul_le_mul_of_nonneg_right (hExpBound rest x)
                (mul_nonneg (abs_nonneg lam) hK)
      let updated : X → I → ℝ := fun x i => offset i + g i x
      have hupdatedBound : ∀ x i, |updated x i| ≤ A + B := by
        intro x i
        exact (abs_add_le _ _).trans (add_le_add (hoffset i) (hbound i x))
      have hTail : ∀ x, DeletionLogSobolevRegularity (fun i => mu (i + 1)) n lam
          (finiteEmpiricalSupremum I g n (updated x))
          (finiteEmpiricalDeletionFamily I g n (updated x)) := by
        intro x
        exact ih (fun i => mu (i + 1)) (A := A + B) (by positivity)
          (updated x) (hupdatedBound x)
      let tiltJoint : X × (Fin n → X) → ℝ := fun q => Real.exp
        (lam * finiteEmpiricalSupremum I g (n + 1) offset (e.symm q))
      have htiltJoint : Measurable tiltJoint := by
        dsimp [tiltJoint]
        fun_prop
      have htiltLower : ∀ q, Real.exp (-|lam| * K) ≤ tiltJoint q := by
        intro q
        apply Real.exp_le_exp.mpr
        have hz := hZBound (e.symm q)
        have hprod : |lam * finiteEmpiricalSupremum I g (n + 1) offset
            (e.symm q)| ≤ |lam| * K := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hz (abs_nonneg lam)
        calc
          -|lam| * K = -(|lam| * K) := by ring
          _ ≤ -|lam * finiteEmpiricalSupremum I g (n + 1) offset (e.symm q)| :=
            neg_le_neg hprod
          _ ≤ _ := neg_abs_le _
      have htiltUpper : ∀ q, tiltJoint q ≤ E := fun q => hExpBound q.2 q.1
      have hHeadEntropyMeas : Measurable (fun rest => entropy (mu 0)
          (fun x => Real.exp (lam * finiteEmpiricalSupremum I g (n + 1) offset
            (e.symm (x, rest))))) :=
        measurable_entropy_section_of_bounded_positive (mu 0) (f := tiltJoint) htiltJoint
          (Real.exp_pos _) htiltLower htiltUpper
      have hHeadEntropyInt : Integrable (fun rest => entropy (mu 0)
          (fun x => Real.exp (lam * finiteEmpiricalSupremum I g (n + 1) offset
            (e.symm (x, rest))))) nu := by
        apply integrable_of_measurable_abs_le'' hHeadEntropyMeas
        intro rest
        exact abs_entropy_section_le (mu 0) (f := tiltJoint) htiltJoint
          (Real.exp_pos _) htiltLower htiltUpper rest
      let headCostJoint : X × (Fin n → X) → ℝ := fun q =>
        Real.exp (lam * finiteEmpiricalSupremum I g (n + 1) offset (e.symm q)) *
          blmPhi (-lam * (finiteEmpiricalSupremum I g (n + 1) offset (e.symm q) -
            finiteEmpiricalSupremum I g n offset q.2))
      have hheadCostJoint : Measurable headCostJoint := by
        dsimp [headCostJoint, blmPhi]
        fun_prop
      have hHeadCostMeas : Measurable (fun rest => ∫ x,
          headCostJoint (x, rest) ∂mu 0) :=
        hheadCostJoint.stronglyMeasurable.integral_prod_left'.measurable
      have hHeadCostBound : ∀ rest, |∫ x, headCostJoint (x, rest) ∂mu 0| ≤ E * P := by
        intro rest
        rw [← Real.norm_eq_abs]
        simpa using norm_integral_le_of_norm_le_const
          (μ := mu 0) (C := E * P) (f := fun x => headCostJoint (x, rest))
          (ae_of_all _ fun x => by
            have hDelta := abs_sliceIncrement_le' g hbound hupper n offset rest x
            have hZeq : finiteEmpiricalSupremum I g (n + 1) offset
                (e.symm (x, rest)) = finiteEmpiricalSupremum I g n
                  (updated x) rest := by
              simpa [e, updated] using finiteEmpiricalSupremum_succ g n offset
                (e.symm (x, rest))
            have harg : |-lam * (finiteEmpiricalSupremum I g (n + 1) offset
                (e.symm (x, rest)) - finiteEmpiricalSupremum I g n offset rest)| ≤
                |lam| * D := by
              rw [hZeq]
              change |-lam * finiteEmpiricalSliceIncrement I g n offset rest x| ≤ _
              rw [abs_mul, abs_neg]
              exact mul_le_mul_of_nonneg_left hDelta (abs_nonneg lam)
            have hphi : |blmPhi (-lam *
                (finiteEmpiricalSupremum I g (n + 1) offset (e.symm (x, rest)) -
                  finiteEmpiricalSupremum I g n offset rest))| ≤ P := by
              let r := -lam *
                (finiteEmpiricalSupremum I g (n + 1) offset (e.symm (x, rest)) -
                  finiteEmpiricalSupremum I g n offset rest)
              dsimp [blmPhi, P]
              change |Real.exp r - r - 1| ≤ _
              calc
                |Real.exp r - r - 1| ≤ |Real.exp r - r| + |(1 : ℝ)| := abs_sub _ _
                _ ≤ (|Real.exp r| + |r|) + 1 := by
                  simpa using add_le_add_right (abs_sub (Real.exp r) r) 1
                _ = Real.exp r + |r| + 1 := by rw [abs_of_pos (Real.exp_pos _)]
                _ ≤ Real.exp (|lam| * D) + |lam| * D + 1 := by
                  have hr : |r| ≤ |lam| * D := by simpa [r] using harg
                  linarith [Real.exp_le_exp.mpr ((le_abs_self r).trans hr)]
            change ‖Real.exp _ * blmPhi _‖ ≤ E * P
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul (hExpBound rest x) hphi (abs_nonneg _) (Real.exp_pos _).le)
      have hHeadCostInt : Integrable (fun rest => ∫ x,
          headCostJoint (x, rest) ∂mu 0) nu :=
        integrable_of_measurable_abs_le'' hHeadCostMeas hHeadCostBound
      have hTensor := finiteEmpiricalTensorizationRegularity mu g hg hA hB hbound
        (n + 1) offset hoffset lam
      have hTailEntropyInt : Integrable (fun x =>
          coordinateEntropySum (fun i => mu (i + 1)) n
            (fun rest => Real.exp (lam * finiteEmpiricalSupremum I g (n + 1) offset
              (e.symm (x, rest))))) (mu 0) := by
        exact hTensor.2.2.2
      have hTailCostData := measurable_bounded_finiteEmpiricalDeletionPhiSum_param
        (P := X) (fun i => mu (i + 1)) g hg (A := A + B) (by positivity) hB
        hbound hupper lam n updated (fun i => by dsimp [updated]; fun_prop) hupdatedBound
      rcases hTailCostData.2 with ⟨Ctail, _hCtail, hTailCostBound⟩
      have hTailCostInt : Integrable (fun x =>
          exponentialDeletionPhiSum (fun i => mu (i + 1)) n lam
            (finiteEmpiricalSupremum I g n (updated x))
            (finiteEmpiricalDeletionFamily I g n (updated x))) (mu 0) :=
        integrable_of_measurable_abs_le'' hTailCostData.1 hTailCostBound
      change (∀ rest, Integrable (fun x => Real.exp
            (lam * finiteEmpiricalSupremum I g (n + 1) offset (e.symm (x, rest))))
            (mu 0) ∧ Integrable (fun x => Real.exp
              (lam * finiteEmpiricalSupremum I g (n + 1) offset (e.symm (x, rest))) *
              (lam * finiteEmpiricalSupremum I g (n + 1) offset (e.symm (x, rest))))
              (mu 0)) ∧
        (∀ x, DeletionLogSobolevRegularity (fun i => mu (i + 1)) n lam
          (fun rest => finiteEmpiricalSupremum I g (n + 1) offset (e.symm (x, rest)))
          (finiteEmpiricalDeletionFamily I g n (updated x))) ∧ _
      refine ⟨hHeadExp, ?_, hHeadEntropyInt, ?_, hTailEntropyInt, ?_⟩
      · intro x
        simpa [updated, e, finiteEmpiricalSupremum_succ] using hTail x
      · simpa [headCostJoint, e, nu] using hHeadCostInt
      · simpa [updated, e, finiteEmpiricalSupremum_succ] using hTailCostInt

/-- Under [coordinate probability laws `mu`](hyp:mu,hprob), a [nonempty finite measurable score
class `g`](hyp:I,g,hg) whose scores are [bounded by `B`](hyp:hbound) and [at most one](hyp:hupper),
and [offsets bounded by the nonnegative constant `A`](hyp:hA,hoffset), the [entropy of the
exponential finite empirical supremum is at most its recursive sum of deletion-coordinate
Bennett costs](goal) at [tilt `lam`](hyp:lam) and [coordinate count `n`](hyp:n), provided [the
score bound is nonnegative](hyp:hB). -/
theorem entropy_exp_finiteEmpiricalSupremum_le_deletion
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (mu : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (mu i)]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1)
    (lam : ℝ) (n : ℕ) (offset : I → ℝ) (hoffset : ∀ i, |offset i| ≤ A) :
    entropy (Measure.pi (fun i : Fin n => mu i.val))
        (fun s => Real.exp (lam * finiteEmpiricalSupremum I g n offset s)) ≤
      exponentialDeletionPhiSum mu n lam
        (finiteEmpiricalSupremum I g n offset)
        (finiteEmpiricalDeletionFamily I g n offset) := by
  apply deletionModifiedLogSobolev_pi mu n lam
    (finiteEmpiricalSupremum I g n offset)
    (finiteEmpiricalDeletionFamily I g n offset)
  · exact finiteEmpiricalTensorizationRegularity mu g hg hA hB hbound
      n offset hoffset lam
  · exact finiteEmpiricalDeletionLogSobolevRegularity mu g hg hA hB
      hbound hupper lam n offset hoffset

end Causalean.Stat.Concentration.EntropyMethod
