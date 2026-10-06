module
public import Causalean.Stat.Quantile.AtomicApproximation.Basic

/-!
# Uniform cumulative-mass grids for compactly supported probability measures

This module isolates the quantile-selection step for an equally weighted
empirical approximation. The finite-mass result follows by normalization and
a separate zero-mass case.
-/

public section

open MeasureTheory ProbabilityTheory Set Causalean.Stat

noncomputable section

namespace Causalean.Stat.Quantile.AtomicApproximation

/-- [A probability measure](hyp:μ), [an ordered closed interval](hyp:a,b,hab),
[concentration of that measure on the interval](hyp:hμ), and [a positive grid
size](hyp:N,hN) give [interval-valued equally weighted atoms whose CDF error is at
most one grid share at every threshold](goal). -/
theorem exists_probability_equalAtom_interval_cdf_error_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (hab : a ≤ b) (hμ : μ (Set.Icc a b)ᶜ = 0)
    (N : ℕ) (hN : 0 < N) :
    ∃ x : Fin N → Set.Icc a b,
      ∀ t : ℝ,
        |μ.real (Set.Iic t) -
          (equalAtomMeasure N 1 (fun i => (x i : ℝ))).real
            (Set.Iic t)| ≤ 1 / (N : ℝ) := by
  /- Use normalized midpoint ranks `((i : ℝ) + 1/2) / N`, all strictly in
     `(0,1)`. The quantile/CDF adjunction in Mathlib (`quantile_le_iff`)
     makes each atom's indicator at `t` equivalent to its rank being below
     `μ.real (Iic t)`. Count midpoint ranks below a value in `[0,1]` using
     floor bounds. Compact support puts every selected quantile in `Icc a b`,
     including when the measure charges either endpoint. -/
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hgrid (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
      |p - (((Finset.univ.filter
        (fun i : Fin N => ((i : ℝ) + 1 / 2) / N ≤ p)).card : ℝ) / N)| ≤
        1 / (N : ℝ) := by
    let m := ⌊(N : ℝ) * p + 1 / 2⌋₊
    have hnonneg : 0 ≤ (N : ℝ) * p + 1 / 2 := by positivity
    have hmle : m ≤ N := by
      have hmul : (N : ℝ) * p ≤ N :=
        (mul_le_mul_of_nonneg_left hp1 hNreal.le).trans_eq (mul_one _)
      have hbound : (N : ℝ) * p + 1 / 2 < (N : ℝ) + 1 := by linarith
      have hh : m < N + 1 :=
        (Nat.floor_lt hnonneg).mpr (by
          simpa only [Nat.cast_add, Nat.cast_one] using hbound)
      omega
    have hiff (i : Fin N) :
        ((i : ℝ) + 1 / 2) / N ≤ p ↔ (i : ℕ) < m := by
      have hm : (i : ℕ) + 1 ≤ m ↔
          ((i : ℝ) + 1 : ℝ) ≤ (N : ℝ) * p + 1 / 2 := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (Nat.le_floor_iff hnonneg (n := (i : ℕ) + 1))
      constructor
      · intro h
        have hh := (div_le_iff₀ hNreal).mp h
        have hi : ((i : ℝ) + 1 : ℝ) ≤ (N : ℝ) * p + 1 / 2 := by linarith
        exact Nat.lt_of_succ_le (hm.mpr (by exact_mod_cast hi))
      · intro h
        have hh : ((i : ℝ) + 1 : ℝ) ≤ (N : ℝ) * p + 1 / 2 :=
          hm.mp (Nat.succ_le_iff.mpr h)
        apply (div_le_iff₀ hNreal).mpr
        linarith
    have hc :
        (Finset.univ.filter
          (fun i : Fin N => ((i : ℝ) + 1 / 2) / N ≤ p)).card = m := by
      have heq :
          Finset.univ.filter
            (fun i : Fin N => ((i : ℝ) + 1 / 2) / N ≤ p) =
          Finset.univ.filter (fun i : Fin N => (i : ℕ) < m) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hiff i
      rw [heq, Fin.card_filter_val_lt, min_eq_right hmle]
    rw [hc]
    have hmlo : (m : ℝ) ≤ (N : ℝ) * p + 1 / 2 := Nat.floor_le hnonneg
    have hmhi : (N : ℝ) * p + 1 / 2 < (m : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hdu : (1 : ℝ) / N * N = 1 := by field_simp
    rw [abs_le]
    constructor
    · have hh : (m : ℝ) / N ≤ p + 1 / N := by
        apply (div_le_iff₀ hNreal).mpr
        calc
          (m : ℝ) ≤ N * p + 1 / 2 := hmlo
          _ ≤ (p + 1 / N) * N := by rw [add_mul, hdu]; nlinarith
      linarith
    · have hh : p ≤ ((m : ℝ) + 1) / N := by
        apply (le_div_iff₀ hNreal).mpr
        nlinarith
      rw [add_div] at hh
      linarith
  have hcompb : μ (Iic b)ᶜ = 0 := measure_mono_null (by
    intro x hx hxab
    exact hx hxab.2) hμ
  have hmu_b : μ (Iic b) = 1 := by
    have hh := measure_compl (μ := μ) (s := (Iic b)ᶜ)
      (by measurability) (by simp)
    simpa only [compl_compl, hcompb, tsub_zero, measure_univ] using hh
  have hcdfb : cdf μ b = 1 := by
    rw [cdf_eq_real, measureReal_def, hmu_b]
    norm_num
  have hlow (t : ℝ) (ht : t < a) : cdf μ t = 0 := by
    have hh : μ (Iic t) = 0 := measure_mono_null (by
      intro x hx hxab
      exact (not_le_of_gt (lt_of_le_of_lt hx ht)) hxab.1) hμ
    rw [cdf_eq_real, measureReal_def, hh]
    norm_num
  have hrank (i : Fin N) :
      0 < ((i : ℝ) + 1 / 2) / N ∧
        ((i : ℝ) + 1 / 2) / N < 1 := by
    have hi : ((i : ℝ) + 1 : ℝ) ≤ N := by
      exact_mod_cast (Nat.succ_le_iff.mpr i.isLt)
    constructor
    · positivity
    · apply (div_lt_iff₀ hNreal).mpr
      norm_num only [one_mul]
      linarith
  have hmem (i : Fin N) :
      quantile μ (((i : ℝ) + 1 / 2) / N) ∈ Icc a b := by
    obtain ⟨hu0, hu1⟩ := hrank i
    refine ⟨?_, ?_⟩
    · by_contra hh
      have hqa : quantile μ (((i : ℝ) + 1 / 2) / N) < a :=
        lt_of_not_ge hh
      have huq :
          ((i : ℝ) + 1 / 2) / N ≤
            cdf μ (quantile μ (((i : ℝ) + 1 / 2) / N)) :=
        le_cdf_quantile hu1
      rw [hlow _ hqa] at huq
      linarith
    · exact (quantile_le_iff hu0 hu1).mpr (by rw [hcdfb]; exact hu1.le)
  let x : Fin N → Icc a b :=
    fun i => ⟨quantile μ (((i : ℝ) + 1 / 2) / N), hmem i⟩
  refine ⟨x, ?_⟩
  intro t
  have hemp :
      (equalAtomMeasure N 1 (fun i => (x i : ℝ))).real (Iic t) =
        ((Finset.univ.filter (fun i : Fin N => (x i : ℝ) ≤ t)).card : ℝ) / N := by
    have hformula :
        (equalAtomMeasure N 1 (fun i => (x i : ℝ))).real (Iic t) =
          (1 / (N : ℝ)) *
            ∑ i, (Measure.dirac (x i : ℝ)).real (Iic t) := by
      simp only [equalAtomMeasure, Measure.real, Measure.finsetSum_apply,
        Measure.smul_apply]
      rw [ENNReal.toReal_sum (by
        intro i hi
        by_cases hx : (x i : ℝ) ∈ Iic t <;> simp [hx])]
      simp [ENNReal.toReal_mul, ← Finset.mul_sum]
    rw [hformula]
    have hsum :
        (∑ i, (Measure.dirac (x i : ℝ)).real (Iic t)) =
          ((Finset.univ.filter
            (fun i : Fin N => (x i : ℝ) ≤ t)).card : ℝ) := by
      classical
      simp only [Measure.real, Measure.dirac_apply, Set.indicator, Set.mem_Iic]
      simp_rw [apply_ite ENNReal.toReal]
      simp
    rw [hsum]
    ring
  have heq :
      Finset.univ.filter (fun i : Fin N => (x i : ℝ) ≤ t) =
        Finset.univ.filter
          (fun i : Fin N => ((i : ℝ) + 1 / 2) / N ≤ μ.real (Iic t)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (quantile_le_iff (hrank i).1 (hrank i).2).trans
      (by rw [cdf_eq_real])
  rw [hemp, heq]
  exact hgrid (μ.real (Iic t)) (measureReal_nonneg) (by
    rw [← cdf_eq_real]
    exact cdf_le_one μ t)

end Causalean.Stat.Quantile.AtomicApproximation
