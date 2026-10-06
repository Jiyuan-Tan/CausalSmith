module
public import Causalean.Stat.UStatistic.LocalizedVariance.Coordinates
public import Causalean.Stat.UStatistic.LocalizedVariance.Counting

/-!
# Mean of an unordered order-two U-statistic

For a measurable integrable symmetric pair kernel, each distinct finite-product
coordinate pair has the independent two-draw expectation. Averaging over
unordered pairs preserves that mean. This module is independent of causal
models and supplies the integrable finite-product transport.
-/

public section

open MeasureTheory ProbabilityTheory

open Causalean.Stat.UStatistic.LocalizedVariance

namespace Causalean.Stat.UStatistic.LocalizedVariance

variable {X : Type*} [MeasurableSpace X] (P : Measure X)
variable [IsProbabilityMeasure P]

/-- A [probability law](hyp:P), [sample size](hyp:n), [two sample
coordinates](hyp:i,j), [their distinctness](hyp:hij), [pair kernel](hyp:H),
[measurability of that kernel](hyp:hH), and [its integrability under the
independent two-draw law](hyp:hInt) give [a coordinate-pair mean equal to its
independent two-draw mean](goal). -/
theorem integral_two_coordinates_integrable {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (H : X → X → ℝ)
    (hH : Measurable fun z : X × X => H z.1 z.2)
    (hInt : Integrable (fun z : X × X => H z.1 z.2) (P.prod P)) :
    ∫ ω, H (ω i) (ω j) ∂iidLaw P n =
      ∫ z : X × X, H z.1 z.2 ∂(P.prod P) := by
  -- Follow `LocalizedVariance.integral_two_coordinates`: the joint coordinate
  -- map sends `iidLaw P n` to `P.prod P`. Use `integral_map` with `hInt`.
  letI : IsProbabilityMeasure (iidLaw P n) := by unfold iidLaw; infer_instance
  have hcoord : iIndepFun (fun a : Fin n => fun ω : Fin n → X => ω a) (iidLaw P n) := by
    unfold iidLaw
    simpa using (iIndepFun_pi (μ := fun _ : Fin n => P)
      (X := fun _ : Fin n => id) (fun _ => aemeasurable_id))
  have hpair : (iidLaw P n).map (fun ω => (ω i, ω j)) = P.prod P := by
    have hind := hcoord.indepFun hij
    simpa only [(measurePreserving_eval (fun _ : Fin n => P) i).map_eq,
      (measurePreserving_eval (fun _ : Fin n => P) j).map_eq, iidLaw] using
      (hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable)
  calc
    _ = ∫ z : X × X, H z.1 z.2 ∂(iidLaw P n).map (fun ω => (ω i, ω j)) := by
      rw [integral_map (by fun_prop) hH.aestronglyMeasurable]
    _ = _ := by rw [hpair]

/-- A [probability law](hyp:P), [sample size](hyp:n), [at least two
observations](hyp:hn), [pair kernel](hyp:H), [symmetry of that kernel](hyp:hSym),
[its measurability](hyp:hH), and [its integrability under the independent
two-draw law](hyp:hInt) give [an unordered U-statistic mean equal to its
independent two-draw mean](goal). -/
theorem integral_uStatistic_eq_pair (n : ℕ) (hn : 2 ≤ n)
    (H : X → X → ℝ) (hSym : ∀ x y, H x y = H y x)
    (hH : Measurable fun z : X × X => H z.1 z.2)
    (hInt : Integrable (fun z : X × X => H z.1 z.2) (P.prod P)) :
    ∫ ω, uStatistic n H ω ∂iidLaw P n =
      ∫ z : X × X, H z.1 z.2 ∂(P.prod P) := by
  -- Integrate the finite sum in `uStatistic`, using the integrability supplied
  -- by `integral_two_coordinates_integrable` for every pair. Every summand
  -- has the same mean. `hn` makes `pairIndices n` nonempty, so its cardinal
  -- cancels the normalization. Symmetry records the unordered-kernel contract.
  letI : IsProbabilityMeasure (iidLaw P n) := by unfold iidLaw; infer_instance
  have hcoord : iIndepFun (fun a : Fin n => fun ω : Fin n → X => ω a) (iidLaw P n) := by
    unfold iidLaw
    simpa using (iIndepFun_pi (μ := fun _ : Fin n => P)
      (X := fun _ : Fin n => id) (fun _ => aemeasurable_id))
  have hpair (p : Fin n × Fin n) (hp : p ∈ pairIndices n) :
      (iidLaw P n).map (fun ω => (ω p.1, ω p.2)) = P.prod P := by
    have hpord : p.1 < p.2 := by simpa [pairIndices] using hp
    have hind := hcoord.indepFun (ne_of_lt hpord)
    simpa only [(measurePreserving_eval (fun _ : Fin n => P) p.1).map_eq,
      (measurePreserving_eval (fun _ : Fin n => P) p.2).map_eq, iidLaw] using
      (hind.map_prod_eq_prod_map_map (measurable_pi_apply p.1).aemeasurable
        (measurable_pi_apply p.2).aemeasurable)
  have hIntCoord (p : Fin n × Fin n) (hp : p ∈ pairIndices n) :
      Integrable (fun ω => H (ω p.1) (ω p.2)) (iidLaw P n) := by
    have hm : Measurable (fun ω : Fin n → X => (ω p.1, ω p.2)) := by fun_prop
    have hi : Integrable (fun z : X × X => H z.1 z.2)
        ((iidLaw P n).map (fun ω => (ω p.1, ω p.2))) := by
      rw [hpair p hp]
      exact hInt
    exact hi.comp_measurable hm
  have hsum :
      (∑ p ∈ pairIndices n, ∫ ω, H (ω p.1) (ω p.2) ∂iidLaw P n) =
        ((pairIndices n).card : ℝ) * ∫ z : X × X, H z.1 z.2 ∂(P.prod P) := by
    calc
      _ = ∑ _p ∈ pairIndices n, ∫ z : X × X, H z.1 z.2 ∂(P.prod P) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact integral_two_coordinates_integrable P (ne_of_lt (by
          simpa [pairIndices] using hp)) H hH hInt
      _ = _ := by simp
  have hcard : ((pairIndices n).card : ℝ) ≠ 0 := by
    rw [card_pairIndices]
    exact_mod_cast (Nat.choose_pos hn).ne'
  calc
    ∫ ω, uStatistic n H ω ∂iidLaw P n =
        ((pairIndices n).card : ℝ)⁻¹ *
          ∑ p ∈ pairIndices n, ∫ ω, H (ω p.1) (ω p.2) ∂iidLaw P n := by
      simp only [uStatistic, integral_const_mul]
      congr 1
      exact integral_finsetSum (pairIndices n) hIntCoord
    _ = ∫ z : X × X, H z.1 z.2 ∂(P.prod P) := by
      rw [hsum]
      simp [hcard]

end Causalean.Stat.UStatistic.LocalizedVariance
