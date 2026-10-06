module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Nested-event first moments on iid membership patterns

A membership-pattern rectangle fixes the positions lying in the containing event.
The smaller-event first moment on this rectangle has a division-free identity.
This is the analytic input to the count-fibre identity; aggregating patterns of
the same cardinality is a separate finite-partition argument.
-/

public section

open MeasureTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean

variable {X : Type*} [MeasurableSpace X]

/-- Under [an observation probability law](hyp:P), [a tuple size](hyp:n), [a set of
prescribed positions](hyp:U), two [events](hyp:A,B) with [measurable membership](hyp:hA,hB),
and [containment of the first in the second](hyp:hAB), [the smaller-event count moment on
the corresponding iid membership rectangle obeys the division-free identity](goal). -/
theorem iid_nested_pattern_first_moment
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) (U : Finset (Fin n))
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    P.real B *
        (∫ x : Fin n → X, iidEventCount A x
          ∂(Measure.pi (fun _ : Fin n => P)).restrict
            (Set.univ.pi (fun i => if i ∈ U then B else Bᶜ))) =
      P.real A * (U.card : ℝ) *
        (Measure.pi (fun _ : Fin n => P)).real
          (Set.univ.pi (fun i => if i ∈ U then B else Bᶜ)) := by
  /- Use `Measure.restrict_pi_pi` and `integral_fintype_prod_eq_prod` to
  factor the restricted product integral coordinate by coordinate.
  Expand iidEventCount and interchange the finite sum with the restricted
  integral (each indicator is bounded and measurable). For each position i,
  rewrite the restricted integral as an unrestricted integral of a product of
  coordinate indicators: at i use A ∩ B = A if i ∈ U, and A ∩ Bᶜ = ∅ otherwise;
  at j ≠ i use B or Bᶜ according to U. Fubini factors this product. Multiplying
  by P(B) restores the removed i-factor, so summing the |U| identical terms
  gives the formula even when P(B)=0. Use product-with-one-factor-erased
  identities, never division by event mass. U=∅ and n=0 must work. Private
  coordinate-integral/product helpers are appropriate if needed.
  No normalized conditional laws, standard-Borel assumptions, or binomial
  infrastructure are necessary. -/
  classical
  let S : Fin n → Set X := fun i => if i ∈ U then B else Bᶜ
  let μ : Measure (Fin n → X) := Measure.pi (fun i => P.restrict (S i))
  let q : Fin n → ℝ := fun i => P.real (S i)
  have hrect : (Measure.pi (fun _ : Fin n => P)).real (Set.univ.pi S) =
      ∏ i, q i := by
    have h := integral_fintype_prod_eq_prod
      (μ := fun i => P.restrict (S i)) (fun _ _ => (1 : ℝ))
    rw [← measureReal_restrict_apply_univ, Measure.restrict_pi_pi]
    simpa [integral_const, measureReal_restrict_apply_univ, q] using h
  have hind (i : Fin n) :
      Integrable (fun x : Fin n → X => if x i ∈ A then (1 : ℝ) else 0) μ := by
    apply Integrable.of_mem_Icc 0 1
    · exact (Measurable.ite (hA.preimage (measurable_pi_apply i))
        measurable_const measurable_const).aemeasurable
    · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num
  have hcoord (i : Fin n) :
      (∫ x, (if x ∈ A then (1 : ℝ) else 0) ∂P.restrict (S i)) =
        if i ∈ U then P.real A else 0 := by
    have heq : (fun x : X => if x ∈ A then (1 : ℝ) else 0) =
        A.indicator (fun _ => (1 : ℝ)) := by
      funext x
      simp [Set.indicator_apply]
    rw [heq, integral_indicator_const 1 hA, measureReal_restrict_apply hA]
    by_cases hi : i ∈ U
    · simp [S, hi, Set.inter_eq_left.mpr hAB]
    · have hempty : A ∩ Bᶜ = ∅ := Set.eq_empty_iff_forall_notMem.mpr
        (fun x hx => hx.2 (hAB hx.1))
      simp [S, hi, hempty]
  have hterm (i : Fin n) :
      P.real B * (∫ x : Fin n → X, (if x i ∈ A then (1 : ℝ) else 0) ∂μ) =
        if i ∈ U then P.real A * ∏ j, q j else 0 := by
    let f : Fin n → X → ℝ := fun j x =>
      if j = i then (if x ∈ A then 1 else 0) else 1
    have hf : (fun x : Fin n → X => if x i ∈ A then (1 : ℝ) else 0) =
        (fun x => ∏ j, f j (x j)) := by
      funext x
      simp [f]
    rw [hf, integral_fintype_prod_eq_prod]
    have hfactor : (∏ j, ∫ x, f j x ∂P.restrict (S j)) =
        (if i ∈ U then P.real A else 0) *
          ∏ j ∈ Finset.univ.erase i, q j := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      congr 1
      · simpa [f] using hcoord i
      · apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [f, hji, integral_const, q]
    rw [hfactor]
    by_cases hi : i ∈ U
    · have hqi : q i = P.real B := by simp [q, S, hi]
      rw [if_pos hi, if_pos hi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hqi]
      ring
    · simp [hi]
  rw [Measure.restrict_pi_pi]
  change P.real B * (∫ x, iidEventCount A x ∂μ) = _
  unfold iidEventCount
  rw [integral_finsetSum _ (fun i _ => hind i), Finset.mul_sum]
  simp_rw [hterm]
  rw [hrect]
  simp [Finset.sum_ite_mem, mul_comm, mul_assoc]


end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean
