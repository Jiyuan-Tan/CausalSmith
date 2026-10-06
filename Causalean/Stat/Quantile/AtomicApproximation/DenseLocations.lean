module
public import Causalean.Stat.Quantile.AtomicApproximation.Basic

/-!
# Moving finitely many interval atoms into a dense location set

The atom weights and count stay fixed while the finitely many locations are
perturbed inside the support interval.
-/

public section

open MeasureTheory Set

noncomputable section

namespace Causalean.Stat.Quantile.AtomicApproximation

/-- [An ordered interval](hyp:a,b,hab), [a positive atom count](hyp:N,hN),
[a nonnegative total weight](hyp:w,hw), and [two lists of interval-valued atom
locations](hyp:x,y) give [a displacement bound for their integrated-CDF discrepancy](goal). -/
theorem cdfDistance_equalAtomMeasure_locations_le
    (a b : ℝ) (hab : a ≤ b) (N : ℕ) (hN : 0 < N)
    (w : ℝ) (hw : 0 ≤ w)
    (x y : Fin N → Set.Icc a b) :
    cdfDistance a b
      (equalAtomMeasure N w (fun i => (x i : ℝ)))
      (equalAtomMeasure N w (fun i => (y i : ℝ))) ≤
        (w / N) * ∑ i, |(x i : ℝ) - (y i : ℝ)| := by
  let c : ℝ := w / N
  have hc : 0 ≤ c := div_nonneg hw (Nat.cast_nonneg _)
  let f (i : Fin N) (t : ℝ) : ℝ :=
    |(Measure.dirac (x i : ℝ)).real (Iic t) -
      (Measure.dirac (y i : ℝ)).real (Iic t)|
  have hformula (z : Fin N → ℝ) (t : ℝ) :
      (equalAtomMeasure N w z).real (Iic t) =
        c * ∑ i, (Measure.dirac (z i)).real (Iic t) := by
    simp only [equalAtomMeasure, Measure.real, Measure.finsetSum_apply,
      Measure.smul_apply]
    rw [ENNReal.toReal_sum (by
      intro i hi
      by_cases hz : z i ∈ Iic t <;> simp [hz])]
    simp [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hc, ← Finset.mul_sum, c]
  have hfinite (z : Fin N → ℝ) : IsFiniteMeasure (equalAtomMeasure N w z) := by
    have : ∀ i : Fin N,
        IsFiniteMeasure (ENNReal.ofReal c • Measure.dirac (z i)) :=
      fun i => Measure.smul_finite _ (by simp)
    unfold equalAtomMeasure
    infer_instance
  let μf : FiniteMeasure ℝ := ⟨equalAtomMeasure N w (fun i => (x i : ℝ)),
    hfinite _⟩
  let νf : FiniteMeasure ℝ := ⟨equalAtomMeasure N w (fun i => (y i : ℝ)),
    hfinite _⟩
  have hmain := Causalean.Stat.Quantile.FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub
    μf νf a b
  change IntervalIntegrable (fun t : ℝ =>
    |(equalAtomMeasure N w (fun i => (x i : ℝ))).real (Iic t) -
      (equalAtomMeasure N w (fun i => (y i : ℝ))).real (Iic t)|) volume a b at hmain
  have hfi (i : Fin N) : IntervalIntegrable (f i) volume a b := by
    let μi : FiniteMeasure ℝ := ⟨Measure.dirac (x i : ℝ), inferInstance⟩
    let νi : FiniteMeasure ℝ := ⟨Measure.dirac (y i : ℝ), inferInstance⟩
    have hi := Causalean.Stat.Quantile.FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub
      μi νi a b
    exact hi
  have hsum : IntervalIntegrable (fun t => c * ∑ i, f i t) volume a b := by
    apply IntervalIntegrable.const_mul
    have heq : (fun t => ∑ i, f i t) = ∑ i, f i := by
      funext t
      simp
    rw [heq]
    exact IntervalIntegrable.sum Finset.univ (fun i _ => hfi i)
  have hpoint (t : ℝ) :
      |(equalAtomMeasure N w (fun i => (x i : ℝ))).real (Iic t) -
        (equalAtomMeasure N w (fun i => (y i : ℝ))).real (Iic t)| ≤
        c * ∑ i, f i t := by
    rw [hformula (fun i => (x i : ℝ)) t, hformula (fun i => (y i : ℝ)) t,
      ← mul_sub, abs_mul, abs_of_nonneg hc, ← Finset.sum_sub_distrib]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hc
  have hint := intervalIntegral.integral_mono_on hab hmain hsum
    (fun t _ => hpoint t)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun i _ => hfi i)] at hint
  have hident (i : Fin N) :
      (∫ t in a..b, f i t) = |(x i : ℝ) - (y i : ℝ)| := by
    rw [Causalean.Stat.Quantile.Transport.abs_sub_eq_integral_Icc_indicator
      (x i).property (y i).property]
    congr 1
    funext t
    by_cases hx : (x i : ℝ) ≤ t <;> by_cases hy : (y i : ℝ) ≤ t <;>
      simp [f, Measure.real, Set.indicator, hx, hy]
  simp_rw [hident] at hint
  rw [cdfDistance, equalAtomMeasure_mass N hN w hw (fun i => (x i : ℝ)),
    equalAtomMeasure_mass N hN w hw (fun i => (y i : ℝ))]
  simpa [c] using hint

/-- [An ordered interval](hyp:a,b,hab), [a location set contained in it](hyp:D,hD),
[density of that set inside the interval](hyp:hDense), [an atom count](hyp:N) [that is positive](hyp:hN), [a nonnegative total weight](hyp:w,hw), [interval-valued source atoms]
(hyp:x), and [a positive tolerance](hyp:ε,hε) give [equally weighted atoms in the
dense set within that integrated-CDF tolerance](goal). -/
theorem equalAtomMeasure_dense_locations
    (a b : ℝ) (hab : a ≤ b) (D : Set ℝ) (hD : D ⊆ Set.Icc a b)
    (hDense : Dense ((Subtype.val : Set.Icc a b → ℝ) ⁻¹' D))
    (N : ℕ) (hN : 0 < N) (w : ℝ) (hw : 0 ≤ w)
    (x : Fin N → Set.Icc a b) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : Fin N → D,
      cdfDistance a b
        (equalAtomMeasure N w (fun i => (x i : ℝ)))
        (equalAtomMeasure N w (fun i => (y i : ℝ))) < ε := by
  let δ : ℝ := ε / (w + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hnear (i : Fin N) :
      ∃ z : Set.Icc a b, (z : ℝ) ∈ D ∧ |(x i : ℝ) - (z : ℝ)| < δ := by
    obtain ⟨z, hz, hdist⟩ := hDense.exists_dist_lt (x i) hδ
    refine ⟨z, hz, ?_⟩
    simpa only [Subtype.dist_eq, Real.dist_eq] using hdist
  choose z hz hdist using hnear
  let y : Fin N → D := fun i => ⟨(z i : ℝ), hz i⟩
  refine ⟨y, ?_⟩
  have hsum : (∑ i : Fin N, |(x i : ℝ) - (z i : ℝ)|) ≤ (N : ℝ) * δ := by
    calc
      (∑ i : Fin N, |(x i : ℝ) - (z i : ℝ)|) ≤ ∑ _i : Fin N, δ :=
        Finset.sum_le_sum (fun i _ => le_of_lt (hdist i))
      _ = (N : ℝ) * δ := by simp
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hcoef : 0 ≤ w / (N : ℝ) := div_nonneg hw (le_of_lt hNreal)
  calc
    cdfDistance a b
        (equalAtomMeasure N w (fun i => (x i : ℝ)))
        (equalAtomMeasure N w (fun i => (y i : ℝ))) ≤
        (w / N) * ∑ i, |(x i : ℝ) - (z i : ℝ)| := by
          simpa [y] using cdfDistance_equalAtomMeasure_locations_le
            a b hab N hN w hw x z
    _ ≤ (w / N) * ((N : ℝ) * δ) := mul_le_mul_of_nonneg_left hsum hcoef
    _ = w * δ := by field_simp
    _ < ε := by
      dsimp [δ]
      calc
        w * (ε / (w + 1)) = w * ε / (w + 1) := by ring
        _ < ε := (div_lt_iff₀ (by linarith : (0 : ℝ) < w + 1)).2 (by nlinarith)

end Causalean.Stat.Quantile.AtomicApproximation
