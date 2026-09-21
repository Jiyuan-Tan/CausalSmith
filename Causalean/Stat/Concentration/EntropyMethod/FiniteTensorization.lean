/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Stat.Concentration.EntropyMethod.Tensorization
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite-coordinate entropy tensorization

This file iterates binary entropy tensorization over a finite product of independent probability
laws.  The coordinate entropy sum is written recursively along Mathlib's measurable equivalence
between a `Fin (n + 1)`-indexed tuple and its head--tail product decomposition.

The regularity predicate contains the positivity, integrability, and Fubini conditions needed by
the real-valued binary theorem, together with the integrability needed to average the inductive
tail inequality.
-/

@[expose] public section

open MeasureTheory Real

namespace Causalean.Stat.Concentration.EntropyMethod

universe u

/-- Given [a sequence of coordinate laws `μ`](hyp:μ), [a number of coordinates `n`](hyp:n), and
a function `f` on the first `n` coordinates, the [finite sum of expected
one-coordinate entropies](goal) is [zero with no coordinates](step:1), while [at a positive number
of coordinates it averages the head-coordinate entropy over the tail and the recursively defined
tail-coordinate sum over the head](step:2). -/
noncomputable def coordinateEntropySum {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) :
    (n : ℕ) → ((Fin n → X) → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, f =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      (∫ tail, entropy (μ 0) (fun x => f (e.symm (x, tail)))
        ∂Measure.pi (fun j : Fin n => μ (j.val + 1))) +
      ∫ x, coordinateEntropySum (fun i => μ (i + 1)) n
          (fun tail => f (e.symm (x, tail))) ∂μ 0

/-- Given [coordinate laws `μ`](hyp:μ), [a finite coordinate count `n`](hyp:n), and a function
`f` on that product, the [regularity conditions for finite entropy
tensorization](goal) recursively require the binary positivity and integrability bundle, the
same conditions in every tail section, and integrability of both sides of the inductive tail
comparison: [the zero-coordinate condition is automatic](step:1), and [the positive-coordinate
condition contains the binary bundle, recursive tail regularity, and the two required
integrability clauses](step:2). -/
def FiniteTensorizationRegularity {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) :
    (n : ℕ) → ((Fin n → X) → ℝ) → Prop
  | 0, _ => True
  | n + 1, f =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      EntropyTensorizationIntegrable (μ 0)
          (Measure.pi (fun j : Fin n => μ (j.val + 1)))
          (fun p => f (e.symm p)) ∧
      (∀ x, FiniteTensorizationRegularity (fun i => μ (i + 1)) n
          (fun tail => f (e.symm (x, tail)))) ∧
      Integrable (fun x => entropy (Measure.pi (fun j : Fin n => μ (j.val + 1)))
          (fun tail => f (e.symm (x, tail)))) (μ 0) ∧
      Integrable (fun x => coordinateEntropySum (fun i => μ (i + 1)) n
          (fun tail => f (e.symm (x, tail)))) (μ 0)

private lemma entropy_comp_measurableEquiv
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} (e : A ≃ᵐ B)
    (h : MeasurePreserving e μ ν) (f : B → ℝ) :
    entropy μ (f ∘ e) = entropy ν f := by
  rw [entropy, entropy]
  simp only [Function.comp_apply]
  rw [h.integral_comp' (fun y => f y * Real.log (f y))]
  rw [h.integral_comp' f]

/-- If [the coordinate laws are probability laws](hyp:hprob), for [a number of
coordinates](hyp:n) and [a real-valued function of the whole coordinate vector](hyp:f) satisfying
[the recursive positivity and integrability conditions](hyp:h), then [the entropy under the
independent product law is at most the sum of the expected one-coordinate entropies](goal).

Positivity of the function is carried by the regularity bundle, not by the function itself; at
zero coordinates that bundle is vacuous, so the statement covers a function of any sign there. -/
theorem entropy_pi_le_coordinateEntropySum
    {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (f : (Fin n → X) → ℝ)
    (h : FiniteTensorizationRegularity μ n f) :
    entropy (Measure.pi (fun i : Fin n => μ i.val)) f ≤
      coordinateEntropySum μ n f := by
  induction n generalizing μ with
  | zero =>
      have hf : f = fun _ => f default := by
        funext x
        exact congrArg f (Subsingleton.elim x default)
      rw [hf, entropy]
      simp [coordinateEntropySum]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let ν : Measure (Fin n → X) := Measure.pi (fun j : Fin n => μ (j.val + 1))
      let g : X × (Fin n → X) → ℝ := fun p => f (e.symm p)
      have hsplit : MeasurePreserving e
          (Measure.pi (fun i : Fin (n + 1) => μ i.val)) ((μ 0).prod ν) := by
        simpa [e, ν] using
          (MeasureTheory.measurePreserving_piFinSuccAbove
            (μ := fun i : Fin (n + 1) => μ i.val) 0)
      have hent : entropy (Measure.pi (fun i : Fin (n + 1) => μ i.val)) f =
          entropy ((μ 0).prod ν) g := by
        have hc := entropy_comp_measurableEquiv e hsplit g
        have hcomp : g ∘ e = f := by
          funext x
          change f (e.symm (e x)) = f x
          rw [e.symm_apply_apply]
        simpa [hcomp] using hc
      change EntropyTensorizationIntegrable (μ 0) ν g ∧
          (∀ x, FiniteTensorizationRegularity (fun i => μ (i + 1)) n
            (fun tail => f (e.symm (x, tail)))) ∧
          Integrable (fun x => entropy ν (fun tail => f (e.symm (x, tail)))) (μ 0) ∧
          Integrable (fun x => coordinateEntropySum (fun i => μ (i + 1)) n
            (fun tail => f (e.symm (x, tail)))) (μ 0) at h
      rcases h with ⟨hbin, htail, hentInt, hsumInt⟩
      have hbinary := entropy_prod_le (μ 0) ν g hbin
      have htailPoint :
          (fun x => entropy ν (fun tail => f (e.symm (x, tail)))) ≤ᵐ[μ 0]
            fun x => coordinateEntropySum (fun i => μ (i + 1)) n
              (fun tail => f (e.symm (x, tail))) := by
        filter_upwards with x
        exact ih (fun i => μ (i + 1)) (fun tail => f (e.symm (x, tail))) (htail x)
      have htailIntegral := integral_mono_ae hentInt hsumInt htailPoint
      have hsum :
          (∫ y, entropy (μ 0) (fun x => g (x, y)) ∂ν) +
              (∫ x, entropy ν (fun y => g (x, y)) ∂μ 0) ≤
            (∫ y, entropy (μ 0) (fun x => g (x, y)) ∂ν) +
              ∫ x, coordinateEntropySum (fun i => μ (i + 1)) n
                (fun tail => f (e.symm (x, tail))) ∂μ 0 := by
        exact add_le_add_right (by simpa [g] using htailIntegral) _
      rw [hent]
      apply hbinary.trans
      simpa [coordinateEntropySum, e, ν, g] using hsum

end Causalean.Stat.Concentration.EntropyMethod
