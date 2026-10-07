module
public import Causalean.Stat.Quantile.AtomicApproximation.Empirical

/-!
# Synchronized rational atomic density for paired finite measures

Two compactly supported finite real measures of equal mass can be approximated
simultaneously with one rational total mass and one positive atom count.
-/

public section

open MeasureTheory Set

noncomputable section

namespace Causalean.Stat.Quantile.AtomicApproximation

/-- [Two finite real measures](hyp:μ₁,μ₂),
[two ordered closed intervals](hyp:a₁,b₁,a₂,b₂),
[the first interval is ordered](hyp:hab₁), [the second interval is ordered](hyp:hab₂),
[concentration of the first measure on its interval](hyp:hμ₁) and
[concentration of the second measure on its interval](hyp:hμ₂),
[equality of their total real masses](hyp:hmass), [two location sets](hyp:D₁,D₂),
[density of each location set in its interval](hyp:hdense₁,hdense₂), and
[a positive tolerance](hyp:η,hη) give
[a common positive atom count, nonnegative rational mass, and two equally weighted
dense-location atomic approximations with exact mass and total error below the
tolerance](goal). -/
theorem exists_synchronized_rational_equalAtom_approx
    (μ₁ μ₂ : Measure ℝ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (a₁ b₁ a₂ b₂ : ℝ) (hab₁ : a₁ ≤ b₁) (hab₂ : a₂ ≤ b₂)
    (hμ₁ : μ₁ (Set.Icc a₁ b₁)ᶜ = 0)
    (hμ₂ : μ₂ (Set.Icc a₂ b₂)ᶜ = 0)
    (hmass : μ₁.real Set.univ = μ₂.real Set.univ)
    (D₁ D₂ : Set ℝ)
    (hdense₁ : Dense ((Subtype.val : Set.Icc a₁ b₁ → ℝ) ⁻¹' D₁))
    (hdense₂ : Dense ((Subtype.val : Set.Icc a₂ b₂ → ℝ) ⁻¹' D₂))
    (η : ℝ) (hη : 0 < η) :
    ∃ (N : ℕ) (hN : 0 < N) (q : ℚ),
      0 ≤ q ∧
      ∃ (x : Fin N → D₁) (y : Fin N → D₂),
        (equalAtomMeasure N (q : ℝ) (fun i => (x i : ℝ))).real Set.univ = (q : ℝ) ∧
        (equalAtomMeasure N (q : ℝ) (fun i => (y i : ℝ))).real Set.univ = (q : ℝ) ∧
        cdfDistance a₁ b₁ μ₁
          (equalAtomMeasure N (q : ℝ) (fun i => (x i : ℝ))) +
        cdfDistance a₂ b₂ μ₂
          (equalAtomMeasure N (q : ℝ) (fun i => (y i : ℝ))) < η := by
  /- Put `m = μ₁.real univ = μ₂.real univ` and
     `C = (1 + (b₁-a₁)) + (1 + (b₂-a₂))`, so `m ≥ 0` and `C ≥ 2`.
     Apply `exists_rat_btwn` to `m < m + η/(2*C)` to obtain a rational
     `q > m ≥ 0`; then `|m-q| < η/(2*C)`, including when `m = 0`.
     Apply `eventually_equalAtomMeasure_approx` to each measure with
     tolerance `η/4`, and take a positive `N` above both thresholds.
     For each interval, use `cdfDistance_triangle` followed by
     `cdfDistance_equalAtomMeasure_weight_le` to replace the empirical
     measure's weight `m` by `q`. The two empirical errors total less than
     `η/2`, and the two weight-change bounds total less than `η/2`.
     Close exact masses with `equalAtomMeasure_mass`. Countability remains in
     the public API for sieve reuse; the density hypotheses do the work here. -/
  let m : ℝ := μ₁.real Set.univ
  let C : ℝ := (1 + (b₁ - a₁)) + (1 + (b₂ - a₂))
  have hm : 0 ≤ m := measureReal_nonneg
  have hC : 0 < C := by dsimp [C]; linarith
  have hδ : 0 < η / (2 * C) := div_pos hη (by positivity)
  obtain ⟨q, hmq, hqUpper⟩ := exists_rat_btwn (lt_add_of_pos_right m hδ)
  have hq : 0 ≤ (q : ℝ) := le_trans hm hmq.le
  have hweight : C * |m - (q : ℝ)| < η / 2 := by
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hmq)]
    have hdiff : (q : ℝ) - m < η / (2 * C) := by linarith
    calc
      C * ((q : ℝ) - m) < C * (η / (2 * C)) :=
        mul_lt_mul_of_pos_left hdiff hC
      _ = η / 2 := by field_simp
  obtain ⟨N₁, hN₁⟩ := eventually_equalAtomMeasure_approx
    μ₁ a₁ b₁ hab₁ hμ₁ D₁ hdense₁ (η / 4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := eventually_equalAtomMeasure_approx
    μ₂ a₂ b₂ hab₂ hμ₂ D₂ hdense₂ (η / 4) (by linarith)
  let N := max N₁ N₂ + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hN₁' : N₁ ≤ N := by dsimp [N]; omega
  have hN₂' : N₂ ≤ N := by dsimp [N]; omega
  obtain ⟨x, hx⟩ := hN₁ N hN₁' hN
  obtain ⟨y, hy⟩ := hN₂ N hN₂' hN
  have hfinite (w : ℝ) (z : Fin N → ℝ) :
      IsFiniteMeasure (equalAtomMeasure N w z) := by
    haveI : ∀ i : Fin N,
        IsFiniteMeasure (ENNReal.ofReal (w / N) • Measure.dirac (z i)) :=
      fun _ => Measure.smul_finite _ (by simp)
    unfold equalAtomMeasure
    infer_instance
  letI : IsFiniteMeasure (equalAtomMeasure N m (fun i => (x i : ℝ))) := hfinite _ _
  letI : IsFiniteMeasure (equalAtomMeasure N (q : ℝ) (fun i => (x i : ℝ))) :=
    hfinite _ _
  letI : IsFiniteMeasure (equalAtomMeasure N m (fun i => (y i : ℝ))) := hfinite _ _
  letI : IsFiniteMeasure (equalAtomMeasure N (q : ℝ) (fun i => (y i : ℝ))) :=
    hfinite _ _
  have htri₁ := cdfDistance_triangle a₁ b₁ hab₁ μ₁
    (equalAtomMeasure N m (fun i => (x i : ℝ)))
    (equalAtomMeasure N (q : ℝ) (fun i => (x i : ℝ)))
  have htri₂ := cdfDistance_triangle a₂ b₂ hab₂ μ₂
    (equalAtomMeasure N m (fun i => (y i : ℝ)))
    (equalAtomMeasure N (q : ℝ) (fun i => (y i : ℝ)))
  have hw₁ := cdfDistance_equalAtomMeasure_weight_le a₁ b₁ hab₁ N hN
    m (q : ℝ) hm hq (fun i => (x i : ℝ))
  have hw₂ := cdfDistance_equalAtomMeasure_weight_le a₂ b₂ hab₂ N hN
    m (q : ℝ) hm hq (fun i => (y i : ℝ))
  have hsumWeight :
      cdfDistance a₁ b₁ (equalAtomMeasure N m (fun i => (x i : ℝ)))
          (equalAtomMeasure N (q : ℝ) (fun i => (x i : ℝ))) +
        cdfDistance a₂ b₂ (equalAtomMeasure N m (fun i => (y i : ℝ)))
          (equalAtomMeasure N (q : ℝ) (fun i => (y i : ℝ))) < η / 2 := by
    have hbound :
        cdfDistance a₁ b₁ (equalAtomMeasure N m (fun i => (x i : ℝ)))
            (equalAtomMeasure N (q : ℝ) (fun i => (x i : ℝ))) +
          cdfDistance a₂ b₂ (equalAtomMeasure N m (fun i => (y i : ℝ)))
            (equalAtomMeasure N (q : ℝ) (fun i => (y i : ℝ))) ≤
        C * |m - (q : ℝ)| := by
      dsimp [C]
      nlinarith [hw₁, hw₂]
    exact lt_of_le_of_lt hbound hweight
  refine ⟨N, hN, q, ?_, x, y, ?_, ?_, ?_⟩
  · exact_mod_cast hq
  · exact equalAtomMeasure_mass N hN (q : ℝ) hq _
  · exact equalAtomMeasure_mass N hN (q : ℝ) hq _
  · have hx' : cdfDistance a₁ b₁ μ₁
        (equalAtomMeasure N m (fun i => (x i : ℝ))) < η / 4 := hx
    have hy' : cdfDistance a₂ b₂ μ₂
        (equalAtomMeasure N m (fun i => (y i : ℝ))) < η / 4 := by
      simpa [m, hmass] using hy
    linarith

end Causalean.Stat.Quantile.AtomicApproximation
