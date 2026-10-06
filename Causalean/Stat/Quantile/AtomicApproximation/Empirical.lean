module
public import Causalean.Stat.Quantile.AtomicApproximation.DenseLocations
public import Causalean.Stat.Quantile.AtomicApproximation.QuantileGrid

/-!
# Equal-mass empirical approximation on a compact real interval

The empirical approximation has a positive number of equally weighted atoms
for every sufficiently large sample size. Their locations lie in any dense
subset of the support interval, including when the original law has atoms or
zero mass.
-/

public section

open MeasureTheory Set

noncomputable section

namespace Causalean.Stat.Quantile.AtomicApproximation

/-- [A finite real measure](hyp:μ), [an ordered closed interval](hyp:a,b,hab),
[concentration on that interval](hyp:hμ), [a location set contained in it](hyp:D,hD),
[density of that set inside the interval](hyp:hDense), and [a tolerance](hyp:ε) [that is positive](hyp:hε) give [a threshold after which every positive grid size has an equally
weighted approximation located in that dense set within the tolerance](goal). -/
theorem eventually_equalAtomMeasure_approx
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (hab : a ≤ b) (hμ : μ (Set.Icc a b)ᶜ = 0)
    (D : Set ℝ) (hD : D ⊆ Set.Icc a b)
    (hDense : Dense ((Subtype.val : Set.Icc a b → ℝ) ⁻¹' D))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
      ∃ x : Fin N → D,
        cdfDistance a b μ
          (equalAtomMeasure N (μ.real Set.univ) (fun i => (x i : ℝ))) < ε := by
  /- Apply `eventually_equalAtomMeasure_interval_approx` with half the
     tolerance and then `equalAtomMeasure_dense_locations` to each grid.
     More precisely, choose `ε / 2` for both steps, extract their common
     threshold `N₀`, and for each positive `N ≥ N₀` obtain `x₀` in `Icc a b`
     and then `x` in `D`. Supply `IsFiniteMeasure` for the two finite Dirac
     sums using `Measure.smul_finite` and `infer_instance`, as in
     `QuantileGrid.eventually_equalAtomMeasure_interval_approx`. Apply
     `cdfDistance_triangle a b hab` and close the strict inequality with
     the two half-tolerance bounds. This also covers zero mass and endpoint
     atoms without further cases. -/
  obtain ⟨N₀, hN₀⟩ := eventually_equalAtomMeasure_interval_approx
    μ a b hab hμ (ε / 2) (by linarith)
  refine ⟨N₀, ?_⟩
  intro N hN₀N hN
  obtain ⟨x₀, hx₀⟩ := hN₀ N hN₀N hN
  obtain ⟨x, hx⟩ := equalAtomMeasure_dense_locations
    a b hab D hD hDense N hN (μ.real Set.univ) measureReal_nonneg
    x₀ (ε / 2) (by linarith)
  refine ⟨x, ?_⟩
  have hfinite (z : Fin N → ℝ) :
      IsFiniteMeasure (equalAtomMeasure N (μ.real Set.univ) z) := by
    haveI : ∀ i : Fin N,
        IsFiniteMeasure
          (ENNReal.ofReal (μ.real Set.univ / N) • Measure.dirac (z i)) :=
      fun _ => Measure.smul_finite _ (by simp)
    unfold equalAtomMeasure
    infer_instance
  letI : IsFiniteMeasure
      (equalAtomMeasure N (μ.real Set.univ) (fun i => (x₀ i : ℝ))) := hfinite _
  letI : IsFiniteMeasure
      (equalAtomMeasure N (μ.real Set.univ) (fun i => (x i : ℝ))) := hfinite _
  have htri := cdfDistance_triangle a b hab μ
    (equalAtomMeasure N (μ.real Set.univ) (fun i => (x₀ i : ℝ)))
    (equalAtomMeasure N (μ.real Set.univ) (fun i => (x i : ℝ)))
  linarith

end Causalean.Stat.Quantile.AtomicApproximation
