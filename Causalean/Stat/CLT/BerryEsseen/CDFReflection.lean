module
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Probability.CentralLimitTheorem

/-! # Reflection of scalar CDF comparisons

Reflection preserves first moments and characteristic-function discrepancies.
For a reference law with bounded interval mass, its absence of atoms supplies
the endpoint correction needed to turn an upper CDF bound into a lower bound.
These facts do not depend on an Esseen or Berry–Esseen theorem.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- A scalar law with an integrable first moment retains that property after
reflection through the origin. -/
theorem reflected_first_moment_integrable
    (μ : Measure ℝ) (hfirst : Integrable (fun y : ℝ => y) μ) :
    Integrable (fun y : ℝ => y) (μ.map (fun y : ℝ => -y)) := by
  exact (integrable_map_measure (by fun_prop) (by fun_prop)).2 hfirst.neg

/-- Reflecting two finite scalar laws leaves the magnitude of their
characteristic-function difference unchanged at each frequency. -/
theorem reflected_charFun_discrepancy
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : ℝ) :
    ‖charFun (μ.map (fun y : ℝ => -y)) t -
      charFun (ν.map (fun y : ℝ => -y)) t‖ =
      ‖charFun μ t - charFun ν t‖ := by
  have hm (ρ : Measure ℝ) :
      charFun (ρ.map (fun y : ℝ => -y)) t = charFun ρ (-t) := by
    simpa only [neg_one_mul] using (charFun_map_mul (μ := ρ) (-1) t)
  rw [hm μ, hm ν, charFun_neg, charFun_neg, ← map_sub]
  exact Complex.norm_conj _

/-- If [a probability reference law ν assigns every interval at most L times its
length](hyp:hν), for [a nonnegative constant L](hyp:hL), then
[its reflection y ↦ −y satisfies the same interval bound](goal), and
[the lower CDF discrepancy Fν(x) − Fμ(x) is at most the upper discrepancy of
the reflected laws at −x](goal), even when μ has an atom at x. -/
theorem reflected_reference_interval_and_cdf
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (L : ℝ) (hL : 0 ≤ L)
    (hν : ∀ a b : ℝ, a ≤ b →
      (ν (Set.Ioc a b)).toReal ≤ L * (b - a)) :
    (∀ a b : ℝ, a ≤ b →
      ((ν.map (fun y : ℝ => -y)) (Set.Ioc a b)).toReal ≤ L * (b - a)) ∧
    (∀ x : ℝ,
      (ν (Set.Iic x)).toReal - (μ (Set.Iic x)).toReal ≤
        ((μ.map (fun y : ℝ => -y)) (Set.Iic (-x))).toReal -
        ((ν.map (fun y : ℝ => -y)) (Set.Iic (-x))).toReal) := by
  /- First show ν {z} = 0 by bounding it with ν(Ioc (z-d) z)
  for every d>0, then sending d to zero (or use continuous CDF/no-atoms
  infrastructure). Reflection takes Ioc a b to Ico (-b) (-a); ν's
  zero endpoint masses identify Ico and Ioc. Reflection takes Iic (-x)
  to Ici x, whose probability is 1-ν(Iio x). For ν, Iio and Iic agree;
  for μ, monotonicity gives μ(Iio x)≤μ(Iic x), in the required direction.
  Do not assume μ has no atoms. -/
  have hsingleton (z : ℝ) : ν {z} = 0 := by
    have hz : (ν {z}).toReal = 0 := by
      apply le_antisymm _ ENNReal.toReal_nonneg
      by_contra! hpos
      obtain ⟨d, hd, hsmall⟩ := exists_pos_mul_lt hpos L
      have hsub : ({z} : Set ℝ) ⊆ Set.Ioc (z - d) z := by
        intro y hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact ⟨by linarith, le_rfl⟩
      have hmono := ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono hsub)
      have hbound := hν (z - d) z (by linarith)
      have hlength : z - (z - d) = d := by ring
      rw [hlength] at hbound
      exact (not_lt_of_ge (hmono.trans hbound)) hsmall
    exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top ν _)
  constructor
  · intro a b hab
    have hpre : (fun y : ℝ => -y) ⁻¹' Set.Ioc a b = Set.Ico (-b) (-a) := by
      ext y
      exact Set.neg_mem_Ioc_iff
    rw [Measure.map_apply (by fun_prop) measurableSet_Ioc, hpre,
      measure_congr (Ico_ae_eq_Ioc' (hsingleton (-b)) (hsingleton (-a)))]
    have hbound := hν (-b) (-a) (neg_le_neg hab)
    convert hbound using 1
    ring
  · intro x
    have hpre : (fun y : ℝ => -y) ⁻¹' Set.Iic (-x) = Set.Ici x := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici, neg_le_neg_iff]
    have htail (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
        (ρ (Set.Ici x)).toReal = 1 - (ρ (Set.Iio x)).toReal := by
      simpa only [Measure.real, Set.compl_Iio] using
        (probReal_compl_eq_one_sub (μ := ρ) (s := Set.Iio x) measurableSet_Iio)
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic,
      Measure.map_apply (by fun_prop) measurableSet_Iic, hpre, htail μ, htail ν,
      measure_congr (Iio_ae_eq_Iic' (hsingleton x))]
    have hmono := ENNReal.toReal_mono (measure_ne_top μ (Set.Iic x))
      (measure_mono (Set.Iio_subset_Iic_self (a := x)))
    linarith

end Causalean.Stat.CLT.BerryEsseen
