/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Stat.Concentration.EntropyMethod.Bousquet
public import Causalean.Stat.Concentration.EntropyMethod.FiniteTensorization

/-!
# Deletion-coordinate modified logarithmic-Sobolev inequality

This file derives the deletion-coordinate form of the modified logarithmic-Sobolev
inequality directly from finite entropy tensorization.  A recursive family records one
comparison value for each coordinate while making its independence of the deleted coordinate
true by construction.  The resulting bound is the entropy input used in Bousquet's inequality.
-/

@[expose] public section

open MeasureTheory Real

namespace Causalean.Stat.Concentration.EntropyMethod

universe u

/-- Given [a probability law `mu`](hyp:mu), [a real function `g`](hyp:g), [a scalar comparison
value `c`](hyp:c), [integrability of its exponential](hyp:hExp), and [integrability of its
exponentially weighted value](hyp:hExpG), [the entropy of `exp(g)` is at most the expected
Bennett entropy cost `exp(g) * phi(c-g)`](goal). -/
theorem entropy_exp_le_phi_comparison
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (g : X → ℝ) (c : ℝ)
    (hExp : Integrable (fun x => Real.exp (g x)) mu)
    (hExpG : Integrable (fun x => Real.exp (g x) * g x) mu) :
    entropy mu (fun x => Real.exp (g x)) ≤
      ∫ x, Real.exp (g x) * blmPhi (c - g x) ∂mu := by
  let m := ∫ x, Real.exp (g x) ∂mu
  have hm : 0 < m := integral_exp_pos hExp
  have hmean : c * m + m - Real.exp c ≤ m * Real.log m := by
    have hlog := Real.log_le_sub_one_of_pos
      (div_pos (Real.exp_pos c) hm)
    rw [Real.log_div (Real.exp_ne_zero c) hm.ne', Real.log_exp] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hm.le
    have hratio : m * (Real.exp c / m) = Real.exp c := by
      field_simp [hm.ne']
    nlinarith [hmul, hratio]
  have hEq : (fun x => Real.exp (g x) * blmPhi (c - g x)) =
      fun x => Real.exp (g x) * g x - c * Real.exp (g x) -
        Real.exp (g x) + Real.exp c := by
    funext x
    simp only [blmPhi]
    rw [show c - g x = c + -g x by ring, Real.exp_add, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    ring
  have hLeftLog :
      (∫ x, Real.exp (g x) * Real.log (Real.exp (g x)) ∂mu) =
        ∫ x, Real.exp (g x) * g x ∂mu := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.log_exp]
  have hExpConst : Integrable (fun _ : X => Real.exp c) mu := integrable_const _
  have hRightInt : Integrable (fun x =>
      Real.exp (g x) * g x - c * Real.exp (g x) - Real.exp (g x)) mu :=
    ((hExpG.sub (hExp.const_mul c)).sub hExp)
  have hRight :
      (∫ x, Real.exp (g x) * g x - c * Real.exp (g x) -
          Real.exp (g x) + Real.exp c ∂mu) =
        (∫ x, Real.exp (g x) * g x ∂mu) -
          c * (∫ x, Real.exp (g x) ∂mu) -
          (∫ x, Real.exp (g x) ∂mu) + Real.exp c := by
    integral_linearity
    simp
  rw [entropy, hLeftLog, hEq, hRight]
  dsimp [m] at hmean
  linarith

/-- For [a sample type `X`](hyp:X) and a coordinate count `n` (the family's index), a
[recursive family of deletion-coordinate comparison values](goal) is either [empty at zero
coordinates](step:1) or [a head comparison depending only on the tail together with recursive
tail comparisons after fixing the head](step:2). -/
inductive DeletionCoordinateFamily (X : Type u) : (n : ℕ) → Type u where
  | nil : DeletionCoordinateFamily X 0
  | cons {n : ℕ} (head : (Fin n → X) → ℝ)
      (tail : X → DeletionCoordinateFamily X n) : DeletionCoordinateFamily X (n + 1)

/-- Given [coordinate laws `mu`](hyp:mu), [a coordinate count `n`](hyp:n), a tilt
`lam`, a statistic `Z`, and deletion-coordinate comparisons `D`,
the [sum of expected tilted Bennett deletion costs](goal) is [zero with no coordinates](step:1),
while [at a positive coordinate count it adds the head-coordinate cost and the recursively
averaged tail-coordinate costs](step:2). -/
noncomputable def exponentialDeletionPhiSum {X : Type u} [MeasurableSpace X]
    (mu : ℕ → Measure X) :
    (n : ℕ) → ℝ → ((Fin n → X) → ℝ) → DeletionCoordinateFamily X n → ℝ
  | 0, _, _, .nil => 0
  | n + 1, lam, Z, .cons head tail =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let nu := Measure.pi (fun j : Fin n => mu (j.val + 1))
      (∫ rest, ∫ x,
        Real.exp (lam * Z (e.symm (x, rest))) *
          blmPhi (-lam * (Z (e.symm (x, rest)) - head rest))
        ∂mu 0 ∂nu) +
      ∫ x, exponentialDeletionPhiSum (fun i => mu (i + 1)) n lam
        (fun rest => Z (e.symm (x, rest))) (tail x) ∂mu 0

/-- Given [coordinate laws `mu`](hyp:mu), [a coordinate count `n`](hyp:n), a tilt
`lam`, a statistic `Z`, and deletion-coordinate comparisons `D`,
the [regularity conditions for deletion-coordinate tensorization](goal) are [automatic with no
coordinates](step:1), while [at a positive coordinate count they require exponential slice
integrability, recursive tail regularity, and the four Fubini integrability conditions used to
average the head and tail comparisons](step:2). -/
def DeletionLogSobolevRegularity {X : Type u} [MeasurableSpace X]
    (mu : ℕ → Measure X) :
    (n : ℕ) → ℝ → ((Fin n → X) → ℝ) → DeletionCoordinateFamily X n → Prop
  | 0, _, _, .nil => True
  | n + 1, lam, Z, .cons head tail =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let nu := Measure.pi (fun j : Fin n => mu (j.val + 1))
      (∀ rest, Integrable (fun x => Real.exp (lam * Z (e.symm (x, rest)))) (mu 0) ∧
        Integrable (fun x => Real.exp (lam * Z (e.symm (x, rest))) *
          (lam * Z (e.symm (x, rest)))) (mu 0)) ∧
      (∀ x, DeletionLogSobolevRegularity (fun i => mu (i + 1)) n lam
        (fun rest => Z (e.symm (x, rest))) (tail x)) ∧
      Integrable (fun rest => entropy (mu 0)
        (fun x => Real.exp (lam * Z (e.symm (x, rest))))) nu ∧
      Integrable (fun rest => ∫ x,
        Real.exp (lam * Z (e.symm (x, rest))) *
          blmPhi (-lam * (Z (e.symm (x, rest)) - head rest)) ∂mu 0) nu ∧
      Integrable (fun x => coordinateEntropySum (fun i => mu (i + 1)) n
        (fun rest => Real.exp (lam * Z (e.symm (x, rest))))) (mu 0) ∧
      Integrable (fun x => exponentialDeletionPhiSum (fun i => mu (i + 1)) n lam
        (fun rest => Z (e.symm (x, rest))) (tail x)) (mu 0)

/-- If [the coordinate laws `mu` are probability laws](hyp:hprob), [the product has `n`
coordinates](hyp:n), [the tilt is `lam`](hyp:lam), [the statistic is `Z`](hyp:Z), [the
deletion-coordinate comparisons are `D`](hyp:D), and [the recursive slice and Fubini regularity
conditions hold](hyp:h), then [the finite sum of one-coordinate entropies is at most the sum of
expected tilted Bennett deletion costs](goal). -/
theorem coordinateEntropySum_exp_le_deletion
    {X : Type u} [MeasurableSpace X]
    (mu : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (mu i)]
    (n : ℕ) (lam : ℝ) (Z : (Fin n → X) → ℝ) (D : DeletionCoordinateFamily X n)
    (h : DeletionLogSobolevRegularity mu n lam Z D) :
    coordinateEntropySum mu n (fun s => Real.exp (lam * Z s)) ≤
      exponentialDeletionPhiSum mu n lam Z D := by
  induction n generalizing mu with
  | zero =>
      cases D
      simp [coordinateEntropySum, exponentialDeletionPhiSum]
  | succ n ih =>
      cases D with
      | cons head tail =>
          let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
          let nu : Measure (Fin n → X) := Measure.pi (fun j : Fin n => mu (j.val + 1))
          change
            (∀ rest, Integrable (fun x => Real.exp (lam * Z (e.symm (x, rest)))) (mu 0) ∧
              Integrable (fun x => Real.exp (lam * Z (e.symm (x, rest))) *
                (lam * Z (e.symm (x, rest)))) (mu 0)) ∧
            (∀ x, DeletionLogSobolevRegularity (fun i => mu (i + 1)) n lam
              (fun rest => Z (e.symm (x, rest))) (tail x)) ∧
            Integrable (fun rest => entropy (mu 0)
              (fun x => Real.exp (lam * Z (e.symm (x, rest))))) nu ∧
            Integrable (fun rest => ∫ x,
              Real.exp (lam * Z (e.symm (x, rest))) *
                blmPhi (-lam * (Z (e.symm (x, rest)) - head rest)) ∂mu 0) nu ∧
            Integrable (fun x => coordinateEntropySum (fun i => mu (i + 1)) n
              (fun rest => Real.exp (lam * Z (e.symm (x, rest))))) (mu 0) ∧
            Integrable (fun x => exponentialDeletionPhiSum (fun i => mu (i + 1)) n lam
              (fun rest => Z (e.symm (x, rest))) (tail x)) (mu 0) at h
          rcases h with ⟨hHead, hTail, hHeadEntInt, hHeadBoundInt,
            hTailEntInt, hTailBoundInt⟩
          let headEnt : (Fin n → X) → ℝ := fun rest => entropy (mu 0)
            (fun x => Real.exp (lam * Z (e.symm (x, rest))))
          let headBound : (Fin n → X) → ℝ := fun rest => ∫ x,
            Real.exp (lam * Z (e.symm (x, rest))) *
              blmPhi (-lam * (Z (e.symm (x, rest)) - head rest)) ∂mu 0
          let tailEnt : X → ℝ := fun x =>
            coordinateEntropySum (fun i => mu (i + 1)) n
              (fun rest => Real.exp (lam * Z (e.symm (x, rest))))
          let tailBound : X → ℝ := fun x =>
            exponentialDeletionPhiSum (fun i => mu (i + 1)) n lam
              (fun rest => Z (e.symm (x, rest))) (tail x)
          have hHeadPoint : headEnt ≤ᵐ[nu] headBound := by
            filter_upwards with rest
            have hOne := entropy_exp_le_phi_comparison (mu 0)
              (fun x => lam * Z (e.symm (x, rest))) (lam * head rest)
              (hHead rest).1 (hHead rest).2
            change entropy (mu 0) (fun x => Real.exp (lam * Z (e.symm (x, rest)))) ≤ _
            convert hOne using 1
            apply integral_congr_ae
            filter_upwards with x
            congr 2
            ring
          have hHeadIntegral : (∫ rest, headEnt rest ∂nu) ≤
              ∫ rest, headBound rest ∂nu :=
            integral_mono_ae hHeadEntInt hHeadBoundInt hHeadPoint
          have hTailPoint : tailEnt ≤ᵐ[mu 0] tailBound := by
            filter_upwards with x
            exact ih (fun i => mu (i + 1))
              (fun rest => Z (e.symm (x, rest))) (tail x) (hTail x)
          have hTailIntegral : (∫ x, tailEnt x ∂mu 0) ≤
              ∫ x, tailBound x ∂mu 0 :=
            integral_mono_ae hTailEntInt hTailBoundInt hTailPoint
          change (∫ rest, headEnt rest ∂nu) + (∫ x, tailEnt x ∂mu 0) ≤
            (∫ rest, headBound rest ∂nu) + ∫ x, tailBound x ∂mu 0
          exact add_le_add hHeadIntegral hTailIntegral

/-- If [the coordinate laws `mu` are probability laws](hyp:hprob), [the product has `n`
coordinates](hyp:n), [the tilt is `lam`](hyp:lam), [the statistic is `Z`](hyp:Z), [the
deletion-coordinate comparisons are `D`](hyp:D), [finite entropy tensorization applies to the
exponential tilt](hyp:hTensor), and [the deletion-coordinate slice regularity holds](hyp:hDeletion),
then [the entropy of the exponential tilt is at most the sum of expected costs
`exp(lam*Z) * phi(-lam*(Z-Z_i))`](goal). -/
theorem deletionModifiedLogSobolev_pi
    {X : Type u} [MeasurableSpace X]
    (mu : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (mu i)]
    (n : ℕ) (lam : ℝ) (Z : (Fin n → X) → ℝ) (D : DeletionCoordinateFamily X n)
    (hTensor : FiniteTensorizationRegularity mu n (fun s => Real.exp (lam * Z s)))
    (hDeletion : DeletionLogSobolevRegularity mu n lam Z D) :
    entropy (Measure.pi (fun i : Fin n => mu i.val))
        (fun s => Real.exp (lam * Z s)) ≤
      exponentialDeletionPhiSum mu n lam Z D :=
  (entropy_pi_le_coordinateEntropySum mu n _ hTensor).trans
    (coordinateEntropySum_exp_le_deletion mu n lam Z D hDeletion)

end Causalean.Stat.Concentration.EntropyMethod
