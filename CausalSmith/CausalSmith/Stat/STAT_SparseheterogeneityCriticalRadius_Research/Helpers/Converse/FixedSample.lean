module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.Normalization
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.HomogeneousLow
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.RateAlgebra

/-! Fixed-sample mixture transfer and the all-estimator converse. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Filter Set
open scoped ENNReal

-- @node: known_radius_converse_laws
lemma known_radius_converse_laws :
    ∃ c : ℝ, 0 < c ∧ ∀ n M rho,
      3 ≤ n → 1 ≤ M → 0 ≤ rho → rho ≤ 2 →
      ∀ T : (Fin n → SampleObs n) → ℝ, Measurable T →
        ∃ P : KnownRadiusClass n M rho,
          ENNReal.ofReal (c * M ^ 2 * rate n rho) ≤
            ∫⁻ x, ENNReal.ofReal
              ((T x - DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2)
              ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law ∧
          (M = 1 →
            P.law.fullLaw {z | z.y0 ∉ ({-1 / 2, 1 / 2} : Set ℝ) ∨
              z.y1 ∉ ({-1 / 2, 1 / 2} : Set ℝ)} = 0 ∧
            ∀ a k, 0 < P.law.cellMass k →
              P.law.outcomeLaw a k (({-1 / 2, 1 / 2} : Set ℝ)ᶜ) = 0) := by
  refine ⟨1 / 100000000000000000000000000000000000000000000000000, by norm_num, ?_⟩
  intro n M rho hn hM hrho0 hrho2 T hT
  have hrho : 0 ≤ rho ∧ rho ≤ 2 := ⟨hrho0, hrho2⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hH : 0 < Hrho n rho := lt_of_lt_of_le zero_lt_one (Hrho_one_le n rho)
  let a : ℝ := 1 / (n : ℝ)
  let b : ℝ := rho ^ 2 / Hrho n rho ^ 2
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  by_cases hab : a ≤ b
  · have hrhopos : 0 < rho := by
      apply lt_of_le_of_ne hrho0
      intro hz
      subst rho
      simp [b] at hab
      linarith
    by_cases hlow : (n : ℝ) * rho ^ 2 / Hrho n rho ^ 2 ≤ converseSignalCutoff
    · obtain ⟨P, hrisk, hsupp, hhom⟩ :=
        homogeneousLow_exists_squaredRisk_lower n M rho hn hM hrho hrhopos hlow T hT
      refine ⟨P, ?_, hsupp⟩
      have habsum : a + b ≤ 2 * b := by linarith
      have hcoeff :
          (1 / 100000000000000000000000000000000000000000000000000 : ℝ) *
              M ^ 2 * (a + b) ≤
            (M * rho / Hrho n rho) ^ 2 / (32 * converseLowScale ^ 2) := by
        have hid : (M * rho / Hrho n rho) ^ 2 /
              (32 * converseLowScale ^ 2) =
            (1 / (32 * converseLowScale ^ 2)) * M ^ 2 * b := by
          dsimp [b]
          field_simp [hH.ne']
        rw [hid]
        have hc :
            (2 / 100000000000000000000000000000000000000000000000000 : ℝ) ≤
              1 / (32 * converseLowScale ^ 2) := by
          norm_num [converseLowScale]
        have hMb : 0 ≤ M ^ 2 * b := mul_nonneg (sq_nonneg M) hb0
        have hgap := mul_nonneg (sub_nonneg.mpr hc) hMb
        nlinarith
      exact (ENNReal.ofReal_le_ofReal (by simpa [rate, a, b] using hcoeff)).trans hrisk
    · have hhigh : converseSignalCutoff <
          (n : ℝ) * rho ^ 2 / Hrho n rho ^ 2 := lt_of_not_ge hlow
      obtain ⟨P, hrisk, hsupp⟩ :=
        selectedHigh_exists_squaredRisk_lower n M rho hn hM hrho hrhopos hhigh T hT
      refine ⟨P, ?_, hsupp⟩
      have habsum : a + b ≤ 2 * b := by linarith
      have hbudget := selected_high_budget_of_cutoff_lt n rho hn hrho hhigh
      have hbudget' : (1 / 8 : ℝ) <
          3 / 4 - 2 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) -
            8 * Real.exp (-(n : ℝ) /
              (100000000000000 * (dualDegree n rho : ℝ) ^ 2)) := by linarith
      have hcoeff :
          (1 / 100000000000000000000000000000000000000000000000000 : ℝ) *
              M ^ 2 * (a + b) ≤
            ((3 * converseC2 * M * rho / (4 * Hrho n rho)) ^ 2 *
              (3 / 4 - 2 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) -
                8 * Real.exp (-(n : ℝ) /
                  (100000000000000 * (dualDegree n rho : ℝ) ^ 2))) / 4) := by
        have hc :
            (2 / 100000000000000000000000000000000000000000000000000 : ℝ) ≤
              9 * converseC2 ^ 2 / 512 := by
          norm_num [converseC2]
        have hid : (3 * converseC2 * M * rho / (4 * Hrho n rho)) ^ 2 =
            (9 * converseC2 ^ 2 / 16) * M ^ 2 * b := by
          dsimp [b]
          field_simp [hH.ne']
          ring
        rw [hid]
        have hbase : 0 ≤ (9 * converseC2 ^ 2 / 16) * M ^ 2 * b := by positivity
        have hMb : 0 ≤ M ^ 2 * b := mul_nonneg (sq_nonneg M) hb0
        have hgap := mul_nonneg (sub_nonneg.mpr hc) hMb
        have hbudmul := mul_le_mul_of_nonneg_left (le_of_lt hbudget') hbase
        nlinarith
      exact (ENNReal.ofReal_le_ofReal (by simpa [rate, a, b] using hcoeff)).trans hrisk
  · obtain ⟨P, hrisk, hsupp⟩ :=
      centeredParametric_exists_squaredRisk_lower n M rho hn hM hrho T hT
    refine ⟨P, ?_, hsupp⟩
    have hsum : a + b ≤ 2 * a := by linarith
    have hcoeff :
        (1 / 100000000000000000000000000000000000000000000000000 : ℝ) *
            M ^ 2 * (a + b) ≤
          M ^ 2 / (288 * converseLowScale ^ 2 * (n : ℝ)) := by
      have hc :
          (2 / 100000000000000000000000000000000000000000000000000 : ℝ) ≤
            1 / (288 * converseLowScale ^ 2) := by
        norm_num [converseLowScale]
      have hid : M ^ 2 / (288 * converseLowScale ^ 2 * (n : ℝ)) =
          (1 / (288 * converseLowScale ^ 2)) * M ^ 2 * a := by
        dsimp [a]
        field_simp [hnR.ne']
      rw [hid]
      have hMa : 0 ≤ M ^ 2 * a := mul_nonneg (sq_nonneg M) ha0.le
      have hgap := mul_nonneg (sub_nonneg.mpr hc) hMa
      nlinarith
    exact (ENNReal.ofReal_le_ofReal (by simpa [rate, a, b] using hcoeff)).trans hrisk

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
