module
public import Causalean.Stat.Quantile.AtomicApproximation.ProbabilityGrid

/-!
# Equal-weight quantile grids on compact intervals

This module isolates the measure-theoretic approximation before atom locations
are moved into a prescribed dense subset.
-/

public section

open MeasureTheory Set

noncomputable section

namespace Causalean.Stat.Quantile.AtomicApproximation

/-- [A finite real measure](hyp:μ), [an ordered closed interval](hyp:a,b,hab),
[concentration on that interval](hyp:hμ), and [a positive grid size](hyp:N,hN)
give [interval-valued equally weighted atoms whose CDF error is at most one atom's
share of the total mass at every threshold](goal). -/
theorem exists_equalAtomMeasure_interval_cdf_error_le
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (hab : a ≤ b) (hμ : μ (Set.Icc a b)ᶜ = 0)
    (N : ℕ) (hN : 0 < N) :
    ∃ x : Fin N → Set.Icc a b,
      ∀ t : ℝ,
        |μ.real (Set.Iic t) -
          (equalAtomMeasure N (μ.real Set.univ) (fun i => (x i : ℝ))).real
            (Set.Iic t)| ≤ μ.real Set.univ / N := by
  /- Let `μf : FiniteMeasure ℝ := ⟨μ, inferInstance⟩` and set
     `m := μ.real univ`. If `m > 0`, use
     `FiniteMassTransport.normalize_support_Icc` and apply
     `exists_probability_equalAtom_interval_cdf_error_le` to `μf.normalize`.
     `FiniteMassTransport.cdf_normalize_eq_div` identifies its CDF with
     `μ.real (Iic t) / m`. Expand the finite Dirac sum to show that the
     `m`-weight grid has CDF `m` times the unit-weight grid's CDF; multiply
     the probability bound by `m` and simplify.
     If `m = 0`, finite-measure monotonicity makes every CDF value zero.
     Put every grid point at `a`; its weight `m / N` is zero. -/
  let m : ℝ := μ.real univ
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hformula (w : ℝ) (hw : 0 ≤ w) (x : Fin N → ℝ) (t : ℝ) :
      (equalAtomMeasure N w x).real (Iic t) =
        (w / N) * ∑ i, (Measure.dirac (x i)).real (Iic t) := by
    simp only [equalAtomMeasure, Measure.real, Measure.finsetSum_apply,
      Measure.smul_apply]
    rw [ENNReal.toReal_sum (by
      intro i hi
      by_cases hx : x i ∈ Iic t <;> simp [hx])]
    simp [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg hw (Nat.cast_nonneg _)), ← Finset.mul_sum]
  by_cases hm : m = 0
  · let x : Fin N → Icc a b := fun _ => ⟨a, ⟨le_refl a, hab⟩⟩
    refine ⟨x, ?_⟩
    intro t
    have hzero : μ.real (Iic t) = 0 := by
      have hle : μ.real (Iic t) ≤ m := measureReal_mono (subset_univ _)
      have hnonneg : 0 ≤ μ.real (Iic t) := measureReal_nonneg
      linarith
    rw [hzero, show μ.real univ = 0 from hm]
    rw [hformula 0 (le_refl 0) (fun i => (x i : ℝ)) t]
    norm_num
  · have hmp : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
    let μf : FiniteMeasure ℝ := ⟨μ, inferInstance⟩
    have hmass : (μf.mass : ℝ) = m := rfl
    have hpos : 0 < (μf.mass : ℝ) := by simpa [hmass] using hmp
    have hsupport : (μf.normalize : Measure ℝ) (Icc a b)ᶜ = 0 :=
      Causalean.Stat.Quantile.FiniteMassTransport.normalize_support_Icc μf hpos hμ
    obtain ⟨x, hx⟩ := exists_probability_equalAtom_interval_cdf_error_le
      (μf.normalize : Measure ℝ) a b hab hsupport N hN
    refine ⟨x, ?_⟩
    intro t
    have hnorm := hx t
    have hcdf : (μf.normalize : Measure ℝ).real (Iic t) = μ.real (Iic t) / m := by
      rw [← ProbabilityTheory.cdf_eq_real,
        Causalean.Stat.Quantile.FiniteMassTransport.cdf_normalize_eq_div μf hpos]
      rfl
    rw [hcdf] at hnorm
    have hscale :
        (equalAtomMeasure N m (fun i => (x i : ℝ))).real (Iic t) =
          m * (equalAtomMeasure N 1 (fun i => (x i : ℝ))).real (Iic t) := by
      rw [hformula m hm0, hformula 1 (by norm_num)]
      ring
    change |μ.real (Iic t) -
      (equalAtomMeasure N m (fun i => (x i : ℝ))).real (Iic t)| ≤ m / N
    rw [hscale]
    have hident : μ.real (Iic t) -
        m * (equalAtomMeasure N 1 (fun i => (x i : ℝ))).real (Iic t) =
        m * (μ.real (Iic t) / m -
          (equalAtomMeasure N 1 (fun i => (x i : ℝ))).real (Iic t)) := by
      field_simp
    rw [hident, abs_mul, abs_of_nonneg hm0]
    have hbound := mul_le_mul_of_nonneg_left hnorm hm0
    simpa [div_eq_mul_inv] using hbound

/-- [Two finite real measures](hyp:μ,ν), [an interval and error level](hyp:a,b,c),
[the interval endpoints ordered](hyp:hab), [equal total real masses](hyp:hmass), and [a uniform CDF-error
bound on the interval](hyp:hpoint) give [an integrated-CDF discrepancy bound by
interval length times that error level](goal). -/
theorem cdfDistance_le_of_pointwise_cdf_le
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (a b c : ℝ) (hab : a ≤ b)
    (hmass : μ.real Set.univ = ν.real Set.univ)
    (hpoint : ∀ t ∈ Set.Icc a b,
      |μ.real (Set.Iic t) - ν.real (Set.Iic t)| ≤ c) :
    cdfDistance a b μ ν ≤ (b - a) * c := by
  /- Use `FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub` for the
     integrand and `intervalIntegral.integral_mono_on` against the constant
     function `c`. Rewrite `intervalIntegral.integral_const`, then eliminate
     the mass term with `hmass`. No positivity of the original mass is needed. -/
  let μf : FiniteMeasure ℝ := ⟨μ, inferInstance⟩
  let νf : FiniteMeasure ℝ := ⟨ν, inferInstance⟩
  have hint := Causalean.Stat.Quantile.FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub
    μf νf a b
  change IntervalIntegrable
    (fun t : ℝ => |μ.real (Iic t) - ν.real (Iic t)|) volume a b at hint
  have hbound := intervalIntegral.integral_mono_on hab hint
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume a b)
    hpoint
  rw [intervalIntegral.integral_const] at hbound
  simpa [cdfDistance, hmass, smul_eq_mul, mul_comm] using hbound

/-- [A finite real measure](hyp:μ), [an ordered closed interval](hyp:a,b,hab),
[concentration on that interval](hyp:hμ), and [a positive tolerance](hyp:ε,hε)
give [a threshold after which every positive grid size admits an equally weighted
interval-atomic approximation within that tolerance](goal). -/
theorem eventually_equalAtomMeasure_interval_approx
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (hab : a ≤ b) (hμ : μ (Set.Icc a b)ᶜ = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
      ∃ x : Fin N → Set.Icc a b,
        cdfDistance a b μ
          (equalAtomMeasure N (μ.real Set.univ) (fun i => (x i : ℝ))) < ε := by
  /- Apply `exists_equalAtomMeasure_interval_cdf_error_le` and
     `cdfDistance_le_of_pointwise_cdf_le` with the mass identity from
     `equalAtomMeasure_mass`; the distance is bounded by
     `(b-a) * μ.real univ / N`.
     For the numerical step, `tendsto_const_div_atTop_nhds_zero_nat`
     applied to `(b-a) * μ.real univ`, followed by
     `Filter.Tendsto.eventually (eventually_lt_nhds hε)`, gives an
     eventual strict bound. Extract `N₀` with `Filter.eventually_atTop.1`;
     take its maximum with `1`. The mass can be zero, so avoid division
     by the mass. -/
  have hlim : Filter.Tendsto
      (fun N : ℕ => ((b - a) * μ.real Set.univ) / (N : ℝ))
      Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      ((b - a) * μ.real Set.univ) / (N : ℝ) < ε :=
    hlim.eventually (eventually_lt_nhds hε)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, ?_⟩
  intro N hN₀N hN
  obtain ⟨x, hx⟩ :=
    exists_equalAtomMeasure_interval_cdf_error_le μ a b hab hμ N hN
  refine ⟨x, ?_⟩
  have hm : 0 ≤ μ.real Set.univ := measureReal_nonneg
  have hmass : μ.real Set.univ =
      (equalAtomMeasure N (μ.real Set.univ) (fun i => (x i : ℝ))).real Set.univ := by
    symm
    exact equalAtomMeasure_mass N hN _ hm _
  haveI : IsFiniteMeasure
      (equalAtomMeasure N (μ.real Set.univ) (fun i => (x i : ℝ))) := by
    haveI : ∀ i : Fin N,
        IsFiniteMeasure
          (ENNReal.ofReal (μ.real Set.univ / N) • Measure.dirac (x i : ℝ)) :=
      fun _ => Measure.smul_finite _ (by simp)
    unfold equalAtomMeasure
    infer_instance
  have hbound := cdfDistance_le_of_pointwise_cdf_le μ
    (equalAtomMeasure N (μ.real Set.univ) (fun i => (x i : ℝ)))
    a b (μ.real Set.univ / N) hab hmass
    (fun t _ => hx t)
  calc
    cdfDistance a b μ
        (equalAtomMeasure N (μ.real Set.univ) (fun i => (x i : ℝ))) ≤
        (b - a) * (μ.real Set.univ / N) := hbound
    _ = ((b - a) * μ.real Set.univ) / (N : ℝ) := by ring
    _ < ε := hN₀ N hN₀N

end Causalean.Stat.Quantile.AtomicApproximation
