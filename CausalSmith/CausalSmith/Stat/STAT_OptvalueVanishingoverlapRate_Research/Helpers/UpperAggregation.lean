module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperBoundedAlphabet
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperClipping
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperDegreeCalibration
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperRaoBlackwell
public import Causalean.Stat.Concentration.Poisson.ConditionalProduct

/-! # Finite-sum bounds for upper-risk aggregation

Roadmap equations (30) and (32) aggregate cellwise pilot second moments and
square-root approximation biases. These lemmas retain null cells and use only
the probability-mass normalization and the active-branch rate bound. -/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open scoped BigOperators

-- @node: cellMass_sum_sqrt_sq_le
/-- Equation (30): probability masses control the squared sum of their square roots. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma cellMass_sum_sqrt_sq_le {d : ℕ} (P : DiscreteLaw d) :
    (∑ x : Fin d, Real.sqrt (cellMass P x)) ^ 2 ≤ (d : ℝ) := by
  have hp (x : Fin d) : 0 ≤ cellMass P x :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => ENNReal.toReal_nonneg
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
    (fun _ => (1 : ℝ)) (fun x => Real.sqrt (cellMass P x))
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Real.sq_sqrt (hp _),
    cellMass_sum_eq_one] using h

-- @node: cellMass_sum_scaled_sqrt_sq_le
/-- The square-root part of the bias in (32) has squared size at most R. The positive scale is m ε L in the active branch. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:ha), the [stated conclusion](goal) holds. -/
lemma cellMass_sum_scaled_sqrt_sq_le {d : ℕ} (P : DiscreteLaw d)
    (a : ℝ) (ha : 0 < a) :
    (∑ x : Fin d, Real.sqrt (cellMass P x / a)) ^ 2 ≤ (d : ℝ) / a := by
  have hp (x : Fin d) : 0 ≤ cellMass P x / a := by
    apply div_nonneg _ ha.le
    exact Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun y _ => ENNReal.toReal_nonneg
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
    (fun _ => (1 : ℝ)) (fun x => Real.sqrt (cellMass P x / a))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Real.sq_sqrt (hp _)] at h
  rw [← Finset.sum_div, cellMass_sum_eq_one] at h
  simpa only [mul_one_div] using h

-- @node: activeBranch_total_bias_sq_le
/-- Equation (32) with an explicit universal constant on the active branch R ≤ 8. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:ha,hactive), the [stated conclusion](goal) holds. -/
lemma activeBranch_total_bias_sq_le {d : ℕ} (P : DiscreteLaw d)
    (a : ℝ) (ha : 0 < a) (hactive : (d : ℝ) / a ≤ 8) :
    ((∑ x : Fin d, Real.sqrt (cellMass P x / a)) + (d : ℝ) / a) ^ 2 ≤
      18 * ((d : ℝ) / a) := by
  have hs := cellMass_sum_scaled_sqrt_sq_le P a ha
  have hR : 0 ≤ (d : ℝ) / a := div_nonneg (Nat.cast_nonneg _) ha.le
  have hR2 : ((d : ℝ) / a) ^ 2 ≤ 8 * ((d : ℝ) / a) := by
    nlinarith
  nlinarith [sq_nonneg ((∑ x : Fin d, Real.sqrt (cellMass P x / a)) - (d : ℝ) / a)]

-- @node: clippingScale_secondMoment_sum_le
/-- Equation (30): summing a cellwise radius-second-moment estimate uses only total mass one. Here v is the second moment already established by the pilot calculation (19). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hv), the [stated conclusion](goal) holds. -/
lemma clippingScale_secondMoment_sum_le {d : ℕ} (P : DiscreteLaw d)
    (v : Fin d → ℝ) (C L m ε : ℝ)
    (hv : ∀ x, v x ≤ C * (cellMass P x * L / (m * ε) + L ^ 2 / (m ^ 2 * ε ^ 2))) :
    (∑ x : Fin d, v x) ≤
      C * (L / (m * ε) + (d : ℝ) * L ^ 2 / (m ^ 2 * ε ^ 2)) := by
  calc
    _ ≤ ∑ x : Fin d,
        C * (cellMass P x * L / (m * ε) + L ^ 2 / (m ^ 2 * ε ^ 2)) :=
      Finset.sum_le_sum fun x _ => hv x
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div,
        ← Finset.sum_mul, cellMass_sum_eq_one]
      simp only [one_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate
