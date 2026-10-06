module
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.PoissonCell
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.PoissonProduct
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Aggregating independent Poisson cells

The deterministic light and heavy mass split and the resulting product-law
Laplace estimate are separated from transport of the finite Poisson sample.
-/

public section

namespace Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open scoped NNReal

/-- For nonnegative cell intensities summing to `total`, the quadratic cost in
cells of intensity at most one and linear cost in the other cells dominate the
birthday-scale quantity `total² / max total d`. This includes zero intensity
and null cells.

The proof splits according to whether heavy cells carry at least half the
total intensity. Otherwise Cauchy--Schwarz on the light cells gives the
quadratic term; the heavy case uses `total² / max total d ≤ total`. -/
theorem lightHeavyExponent_ge_birthdayScale
    {d : ℕ} (hd : 0 < d) {total a b : ℝ}
    (htotal : 0 ≤ total) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (x : Fin d → ℝ) (hx : ∀ k, 0 ≤ x k)
    (hsum : ∑ k, x k = total) :
    min (a / 4) (b / 2) * total ^ 2 / max total (d : ℝ) ≤
      a * ∑ k ∈ Finset.univ.filter (fun k ↦ x k ≤ 1), x k ^ 2 +
      b * ∑ k ∈ Finset.univ.filter (fun k ↦ 1 < x k), x k := by
  let light : Finset (Fin d) := Finset.univ.filter (fun k ↦ x k ≤ 1)
  let heavy : Finset (Fin d) := Finset.univ.filter (fun k ↦ 1 < x k)
  have hpartition : (∑ k ∈ light, x k) + ∑ k ∈ heavy, x k = total := by
    rw [← hsum]
    classical
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k ↦ x k ≤ 1) x]
    simp only [light, heavy, not_le]
  have hmax_pos : 0 < max total (d : ℝ) :=
    lt_of_lt_of_le (by exact_mod_cast hd) (le_max_right _ _)
  have htotal_rate : total ^ 2 / max total (d : ℝ) ≤ total := by
    apply (div_le_iff₀ hmax_pos).2
    nlinarith [le_max_left total (d : ℝ)]
  by_cases hheavy : total / 2 ≤ ∑ k ∈ heavy, x k
  · have hc_le : min (a / 4) (b / 2) ≤ b / 2 := min_le_right _ _
    have hleft : min (a / 4) (b / 2) * total ^ 2 / max total (d : ℝ) ≤
        b * (total / 2) := by
      calc
        min (a / 4) (b / 2) * total ^ 2 / max total (d : ℝ) =
            min (a / 4) (b / 2) * (total ^ 2 / max total (d : ℝ)) := by ring
        _ ≤ min (a / 4) (b / 2) * total :=
          mul_le_mul_of_nonneg_left htotal_rate (le_min (by positivity) (by positivity))
        _ ≤ (b / 2) * total := mul_le_mul_of_nonneg_right hc_le htotal
        _ = b * (total / 2) := by ring
    have hlight_nonneg : 0 ≤ a * ∑ k ∈ light, x k ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hheavy hb
    change min (a / 4) (b / 2) * total ^ 2 / max total (d : ℝ) ≤
      a * ∑ k ∈ light, x k ^ 2 + b * ∑ k ∈ heavy, x k
    nlinarith
  · have hlight_mass : total / 2 < ∑ k ∈ light, x k := by
      linarith
    have hcauchy : (∑ k ∈ light, x k) ^ 2 ≤
        (light.card : ℝ) * ∑ k ∈ light, x k ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := light) (f := x)
    have hcard : (light.card : ℝ) ≤ d := by
      have hcardNat : light.card ≤ Fintype.card (Fin d) := light.card_le_univ
      rw [Fintype.card_fin] at hcardNat
      exact_mod_cast hcardNat
    have hsquares_nonneg : 0 ≤ ∑ k ∈ light, x k ^ 2 := by positivity
    have hcauchy_d : (∑ k ∈ light, x k) ^ 2 ≤
        (d : ℝ) * ∑ k ∈ light, x k ^ 2 :=
      hcauchy.trans (mul_le_mul_of_nonneg_right hcard hsquares_nonneg)
    have hhalf_sq : (total / 2) ^ 2 ≤ (∑ k ∈ light, x k) ^ 2 := by
      nlinarith [Finset.sum_nonneg (s := light) (fun k _ ↦ hx k)]
    have hsquares : total ^ 2 / (4 * d) ≤ ∑ k ∈ light, x k ^ 2 := by
      have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * d)).2
      nlinarith
    have hrate_d : total ^ 2 / max total (d : ℝ) ≤ total ^ 2 / d := by
      exact div_le_div_of_nonneg_left (sq_nonneg total) (by exact_mod_cast hd)
        (le_max_right _ _)
    have hc_le : min (a / 4) (b / 2) ≤ a / 4 := min_le_left _ _
    have hleft : min (a / 4) (b / 2) * total ^ 2 / max total (d : ℝ) ≤
        a * (total ^ 2 / (4 * d)) := by
      calc
        min (a / 4) (b / 2) * total ^ 2 / max total (d : ℝ) =
            min (a / 4) (b / 2) * (total ^ 2 / max total (d : ℝ)) := by ring
        _ ≤ min (a / 4) (b / 2) * (total ^ 2 / d) :=
          mul_le_mul_of_nonneg_left hrate_d (le_min (by positivity) (by positivity))
        _ ≤ (a / 4) * (total ^ 2 / d) :=
          mul_le_mul_of_nonneg_right hc_le (by positivity)
        _ = a * (total ^ 2 / (4 * d)) := by ring
    have hheavy_nonneg : 0 ≤ b * ∑ k ∈ heavy, x k := by
      exact mul_nonneg hb (Finset.sum_nonneg fun k _ ↦ hx k)
    dsimp [light, heavy] at *
    nlinarith [mul_le_mul_of_nonneg_left hsquares ha]

/-- An [overlap margin below one half](hyp:epsilon,hepsilon,hepsilon_half)
gives [a positive-constant birthday-scale bound for the usable-count Laplace
transform](goal) of any finite-cell two-arm intensity table. -/
theorem independent_poisson_laplace_rate (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (hd : 0 < d) (u v : Fin d → ℝ≥0)
        (x : Fin d → ℝ) (total : ℝ),
        (∀ k, (u k : ℝ) + v k = x k) →
        (∀ k, epsilon * x k ≤ u k) →
        (∀ k, epsilon * x k ≤ v k) →
        (∑ k, x k = total) →
        (∫ z : Fin d → ℕ × ℕ,
          Real.exp (-(∑ k, (usablePoissonPairCount (z k) : ℝ)))
          ∂Measure.pi (fun k =>
            (poissonMeasure (u k)).prod (poissonMeasure (v k)))) ≤
          Real.exp (-(c * total ^ 2 / max total (d : ℝ))) := by
  obtain ⟨a, ha, hlight⟩ :=
    poissonCellLaplace_light_rate epsilon hepsilon hepsilon_half
  obtain ⟨b, hb, hheavy⟩ :=
    poissonCellLaplace_heavy_rate epsilon hepsilon hepsilon_half
  let c : ℝ := min (a / 4) (b / 2)
  refine ⟨c, lt_min (by positivity) (by positivity), ?_⟩
  intro d hd u v x total hx hu hv hsum
  have hx0 (k : Fin d) : 0 ≤ x k := by
    rw [← hx k]
    positivity
  have htotal : 0 ≤ total := by
    rw [← hsum]
    exact Finset.sum_nonneg (fun k _ => hx0 k)
  have hcost := lightHeavyExponent_ge_birthdayScale hd htotal ha.le hb.le x hx0 hsum
  have hprod := poisson_cell_product_le_exp_sum u v x a b
    (fun k hk => hlight (u k) (v k) (x k) (hx k) (hu k) (hv k) hk)
    (fun k hk => hheavy (u k) (v k) (x k) (hx k) (hu k) (hv k) hk.le)
  calc
    (∫ z : Fin d → ℕ × ℕ,
      Real.exp (-(∑ k, (usablePoissonPairCount (z k) : ℝ)))
      ∂Measure.pi (fun k =>
        (poissonMeasure (u k)).prod (poissonMeasure (v k)))) =
        ∏ k, poissonCellLaplace (u k) (v k) :=
          poisson_usable_integral_eq_prod u v
    _ ≤ Real.exp (-(a * ∑ k ∈ Finset.univ.filter (fun k ↦ x k ≤ 1), x k ^ 2 +
        b * ∑ k ∈ Finset.univ.filter (fun k ↦ 1 < x k), x k)) := hprod
    _ ≤ Real.exp (-(c * total ^ 2 / max total (d : ℝ))) := by
      apply Real.exp_le_exp.mpr
      linarith [hcost]

end Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk
