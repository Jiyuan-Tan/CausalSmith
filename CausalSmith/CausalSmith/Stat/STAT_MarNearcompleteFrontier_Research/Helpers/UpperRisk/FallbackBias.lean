module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.FallbackRisk
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamBiasAlgebra

/-!
# Population bias and large-dimension fallback risk

The fallback score averages the arrived centered cell contributions. The omitted
missing contributions have absolute sum at most the missingness envelope.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory
open scoped BigOperators

/-- The arrived regression times its cell mass is the arrived outcome mass,
including null arrived cells. Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_arrived_mass_mul_outcomeMean
lemma upper_arrived_mass_mul_outcomeMean {d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    arrivedCellMass P x a s * outcomeMean (observedLaw P) x a s =
      massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧
        w.R = true ∧ w.Y = true) := by
  classical
  let N := massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧
    w.R = true ∧ w.Y = true)
  have hN0 : 0 ≤ N := by
    unfold N massOf
    apply Finset.sum_nonneg
    intro w _
    split_ifs <;> simp [fullMass]
  have hND : N ≤ arrivedCellMass P x a s := by
    unfold N arrivedCellMass massOf
    apply Finset.sum_le_sum
    intro w _
    by_cases hc : w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true ∧ w.Y = true
    · simp [hc]
    · simp only [hc, if_false]
      split_ifs <;> simp [fullMass]
  rw [outcomeMean_observed]
  change arrivedCellMass P x a s * (N / arrivedCellMass P x a s) = N
  by_cases hz : arrivedCellMass P x a s = 0
  · have hNz : N = 0 := le_antisymm (hz ▸ hND) hN0
    simp [hz, hNz]
  · field_simp

/-- The population fallback score is the arrived part of the centered target. Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_fallbackScore_mean
lemma upper_fallbackScore_mean {d : ℕ} (P : FullLaw d) :
    (∫ o, upper_fallbackScore o ∂(observedLaw P).toMeasure) =
      2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        treatmentSign a * arrivedCellMass P x a s * cellEta P x a s) := by
  classical
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  have hcell (x : Fin d) (a s : Bool) :
      treatmentSign a * arrivedCellMass P x a s * cellEta P x a s =
        ∑ o : Obs d, if o.X = x ∧ o.A = a ∧ o.S = s ∧ o.R = true then
          obsMass (observedLaw P) o * treatmentSign a *
            ((if o.RY then (1 : ℝ) else 0) - 1 / 2) else 0 := by
    unfold cellEta
    rw [mul_sub, mul_assoc (treatmentSign a), upper_arrived_mass_mul_outcomeMean]
    unfold arrivedCellMass
    rw [← observed_arrived_outcome_mass, ← observed_arrived_mass]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro o _
    by_cases hc : o.X = x ∧ o.A = a ∧ o.S = s ∧ o.R = true
    · cases hy : o.RY <;> simp [hc, hy] <;> ring
    · have hn : ¬(o.X = x ∧ o.A = a ∧ o.S = s ∧ o.R = true ∧ o.RY = true) :=
        fun h => hc ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
      simp [hc, hn]
  simp_rw [hcell]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset Bool))
    (t := (Finset.univ : Finset (Obs d)))]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  cases hr : o.R <;> cases ha : o.A <;> cases hs : o.S <;>
    simp [upper_fallbackScore, hr, ha, hs, obsMass, treatmentSign, ← mul_assoc,
      Finset.sum_ite_eq', and_assoc] <;> ring <;> simp

/-- The missing part of the centered contrast has magnitude at most delta. Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_missing_contrast_abs_le_delta
lemma upper_missing_contrast_abs_le_delta {d : ℕ} {q : ℝ} (P : FullLaw d)
    (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    |2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      treatmentSign a * missingCellMass P x a s * cellEta P x a s)| ≤ delta q := by
  have hterm (x : Fin d) (a s : Bool) :
      |treatmentSign a * missingCellMass P x a s * cellEta P x a s| ≤
        missingCellMass P x a s / 2 := by
    have hw := (missingCellMass_bounds P h hq x a s).1
    have he := upper_cellEta_abs_le_half P x a s
    rw [abs_mul, abs_mul, abs_of_nonneg hw]
    have hsign : |treatmentSign a| = 1 := by cases a <;> norm_num [treatmentSign]
    rw [hsign, one_mul, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left he hw
  have hs : |∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      treatmentSign a * missingCellMass P x a s * cellEta P x a s| ≤
      ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool, missingCellMass P x a s / 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro x _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro a _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum (fun s _ => hterm x a s)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        missingCellMass P x a s / 2) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool, missingCellMass P x a s := by
      simp only [← Finset.sum_div]
      ring
    _ ≤ delta q := sum_missingCellMass_le_delta P h hq

/-- The population bias of the fallback estimator is bounded by delta. Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_fallback_bias_abs_le_delta
lemma upper_fallback_bias_abs_le_delta {d : ℕ} {q : ℝ} (P : FullLaw d)
    (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    |(∫ o, upper_fallbackScore o ∂(observedLaw P).toMeasure) - tau P| ≤ delta q := by
  rw [upper_fallbackScore_mean, tau_eq_arrived_missing_cells P h hq]
  have hid :
      2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        treatmentSign a * arrivedCellMass P x a s * cellEta P x a s) -
      2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        treatmentSign a * (arrivedCellMass P x a s * cellEta P x a s +
          missingCellMass P x a s * cellEta P x a s)) =
      -(2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        treatmentSign a * missingCellMass P x a s * cellEta P x a s)) := by
    simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib]
    ring
  rw [hid, abs_neg]
  exact upper_missing_contrast_abs_le_delta P h hq

/-- The fallback branch has risk at most twice the sampling and missingness budgets. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_fallback_risk_le_delta
lemma upper_fallback_risk_le_delta {n d : ℕ} {q : ℝ} (hn : 0 < n)
    (P : FullLaw d) (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∫ sample, (fallbackHT sample - tau P) ^ 2 ∂samplePi P n) ≤
      2 / (n : ℝ) + 2 * delta q ^ 2 := by
  have hb := upper_fallback_bias_abs_le_delta P h hq
  have hd : 0 ≤ delta q := by unfold delta; linarith [hq.2]
  have hb2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hb2
  exact (upper_fallback_risk_le_bias hn P).trans (by linarith)

/-- When dimension exceeds n log(e+n), the fallback risk is at most twice the rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `hneq`](hyp:hneq), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `hd`](hyp:hd). -/
-- @node: upper_large_dimension_risk_rate
lemma upper_large_dimension_risk_rate {n d : ℕ} {q : ℝ} (hn : 0 < n)
    (P : FullLaw d) (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hneq : q ≠ 1) (hd : (n : ℝ) * ell n ≤ d) :
    (∫ sample, (tauhatMM n d q sample - tau P) ^ 2 ∂samplePi P n) ≤
      2 * rate n d q := by
  have hden : 0 < (n : ℝ) * ell n :=
    mul_pos (Nat.cast_pos.mpr hn) (ell_pos_for_normalization n)
  have hg : gScale n d q = delta q := by
    unfold gScale
    rw [min_eq_left ((le_div_iff₀ hden).mpr (by simpa using hd)), mul_one]
  simp_rw [tauhatMM_fallback n d q _ hneq (Or.inr hd)]
  have hr := upper_fallback_risk_le_delta hn P h hq
  simpa only [rate, hg, mul_add, mul_one_div] using hr

end CausalSmith.Stat.MarNearcompleteFrontier
