module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL.Count
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL.Marked

/-!
# Unequal-mass finite marked-Poisson divergence

This module identifies the relative entropy of finite marked Poisson laws
with scalar intensity times the finite-measure divergence, retaining the
total-mass correction.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

private lemma poissonRateKL_real_nonneg {r s : ℝ≥0} (hr : r ≠ 0) (hs : s ≠ 0) :
    0 ≤ (r : ℝ) * Real.log ((r : ℝ) / (s : ℝ)) + (s : ℝ) - (r : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast (pos_iff_ne_zero.mpr hr)
  have hs' : (0 : ℝ) < s := by exact_mod_cast (pos_iff_ne_zero.mpr hs)
  have h := Real.log_le_sub_one_of_pos (div_pos hs' hr')
  rw [Real.log_div (ne_of_gt hs') (ne_of_gt hr')] at h
  rw [Real.log_div (ne_of_gt hr') (ne_of_gt hs')]
  have hratio : (s : ℝ) / (r : ℝ) * (r : ℝ) = (s : ℝ) := by field_simp
  nlinarith [mul_nonneg (le_of_lt hr') (sub_nonneg.mpr h)]

private lemma klDiv_smul_probabilities
    {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (r s : ℝ≥0) :
    InformationTheory.klDiv (r • P) (s • Q) =
      poissonRateKL r s + (r : ℝ≥0∞) * InformationTheory.klDiv P Q := by
  by_cases hr : r = 0
  · subst r
    simp [poissonRateKL, Measure.smul_apply, measure_univ]
  by_cases hs : s = 0
  · subst s
    have hne : r • P ≠ 0 := by
      intro h
      have hmass := congrArg (fun m : Measure X => m Set.univ) h
      simp [Measure.smul_apply, measure_univ, hr] at hmass
    have hzero : InformationTheory.klDiv (r • P) (0 : Measure X) = ∞ :=
      @InformationTheory.klDiv_zero_right X _ (r • P) ⟨hne⟩
    simp [poissonRateKL, hr, hzero]
  have hr' : (r : ℝ≥0∞) ≠ 0 := by exact_mod_cast hr
  have hs' : (s : ℝ≥0∞) ≠ 0 := by exact_mod_cast hs
  by_cases hac : P ≪ Q
  · have hac' : r • P ≪ s • Q := (hac.smul_left r).smul_right hs'
    have hint_iff : Integrable (llr (r • P) (s • Q)) (r • P) ↔
        Integrable (llr P Q) P := by
      have hright := llr_smul_nnreal_right (hac.smul_left r) s hs
      have hleft := llr_smul_nnreal_left hac r hr
      rw [integrable_congr hright]
      change Integrable (fun x => llr (r • P) Q x - Real.log (s : ℝ))
        ((r : ℝ≥0∞) • P) ↔ Integrable (llr P Q) P
      rw [integrable_smul_measure hr' (by simp)]
      have heq : (fun x => llr (r • P) Q x - Real.log (s : ℝ)) =ᵐ[P]
          (fun x => llr P Q x + (Real.log (r : ℝ) - Real.log (s : ℝ))) := by
        filter_upwards [hleft] with x hx
        simp only [hx]
        ring
      rw [integrable_congr heq, integrable_add_const_iff]
    by_cases hint : Integrable (llr P Q) P
    · have hint' : Integrable (llr (r • P) (s • Q)) (r • P) := hint_iff.mpr hint
      have hreal :
          (InformationTheory.klDiv (r • P) (s • Q)).toReal =
            (r : ℝ) * (InformationTheory.klDiv P Q).toReal +
              ((r : ℝ) * Real.log ((r : ℝ) / (s : ℝ)) + (s : ℝ) - (r : ℝ)) := by
        have hleft : Integrable (llr (r • P) Q) (r • P) := by
          have heq := llr_smul_nnreal_left hac r hr
          have hintP : Integrable (llr (r • P) Q) P := by
            rw [integrable_congr heq, integrable_add_const_iff]
            exact hint
          change Integrable (llr (r • P) Q) ((r : ℝ≥0∞) • P)
          exact (integrable_smul_measure hr' (by simp)).mpr hintP
        rw [InformationTheory.toReal_klDiv_smul_right (hac.smul_left r) hleft hs,
          InformationTheory.toReal_klDiv_smul_left hac hint r]
        have hrr : (r : ℝ) ≠ 0 := by exact_mod_cast hr
        have hss : (s : ℝ) ≠ 0 := by exact_mod_cast hs
        rw [Real.log_div hrr hss]
        simp only [measureReal_nnreal_smul_apply]
        simp [measureReal_def, measure_univ]
        ring
      have hfin : InformationTheory.klDiv (r • P) (s • Q) ≠ ∞ :=
        InformationTheory.klDiv_ne_top hac' hint'
      have hfinPQ : InformationTheory.klDiv P Q ≠ ∞ :=
        InformationTheory.klDiv_ne_top hac hint
      have hrate : 0 ≤ (r : ℝ) * Real.log ((r : ℝ) / (s : ℝ)) +
          (s : ℝ) - (r : ℝ) := poissonRateKL_real_nonneg hr hs
      rw [← ENNReal.ofReal_toReal hfin, hreal,
        ENNReal.ofReal_add (mul_nonneg (by exact_mod_cast r.property)
          ENNReal.toReal_nonneg) hrate]
      rw [ENNReal.ofReal_mul (by exact_mod_cast r.property),
        ENNReal.ofReal_toReal hfinPQ]
      simp [poissonRateKL, hr, hs, add_comm]
    · rw [InformationTheory.klDiv_of_not_integrable (mt hint_iff.mp hint),
        InformationTheory.klDiv_of_not_integrable hint]
      simp [poissonRateKL, hr, hs, ENNReal.mul_top hr']
  · have hnot : ¬ r • P ≪ s • Q := by
      intro h
      have h' : P ≪ Q := by
        have h1 : P ≪ r • P := by
          change P ≪ (r : ℝ≥0∞) • P
          exact Measure.absolutelyContinuous_smul hr'
        have h2 : s • Q ≪ Q := (Measure.AbsolutelyContinuous.rfl : Q ≪ Q).smul_left s
        exact h1.trans (h.trans h2)
      exact hac h'
    rw [InformationTheory.klDiv_of_not_ac hnot,
      InformationTheory.klDiv_of_not_ac hac]
    simp [poissonRateKL, hr, hs, ENNReal.mul_top hr']

/-- The KL divergence between finite measures is the Poisson divergence of
their total masses plus the source mass times the KL divergence of their
normalized probability laws, with a shared fallback at zero mass. -/
private theorem klDiv_eq_poissonRateKL_add_normalized
    {X : Type*} [MeasurableSpace X]
    (ν₁ ν₀ : Measure X) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₀]
    (P₀ : Measure X) [IsProbabilityMeasure P₀] :
    InformationTheory.klDiv ν₁ ν₀ =
      poissonRateKL (finiteMeasureMass ν₁) (finiteMeasureMass ν₀) +
        (finiteMeasureMass ν₁ : ℝ≥0∞) *
          InformationTheory.klDiv
            (normalizedFiniteMeasure ν₁ P₀) (normalizedFiniteMeasure ν₀ P₀) := by
  /- First prove the general `klDiv (r • P) (s • Q)` decomposition for
     probability P,Q, splitting zero masses, absolute continuity, and
     integrability. Recover each nonzero ν as mass • normalized ν. The
     count term is exactly `poissonRateKL`, including `s-r`. -/
  have hrecover (ν : Measure X) [IsFiniteMeasure ν] :
      finiteMeasureMass ν • normalizedFiniteMeasure ν P₀ = ν := by
    by_cases hν : ν = 0
    · subst ν
      simp [finiteMeasureMass, normalizedFiniteMeasure]
    · ext s hs
      rw [normalizedFiniteMeasure, dif_neg hν, Measure.smul_apply,
        Measure.smul_apply]
      change ((finiteMeasureMass ν : ℝ≥0) : ℝ≥0∞) *
        ((ν Set.univ)⁻¹ * ν s) = ν s
      rw [finiteMeasureMass,
        ENNReal.coe_toNNReal (ne_of_lt (measure_lt_top ν Set.univ)),
        ← mul_assoc, ENNReal.mul_inv_cancel]
      · simp
      · exact fun h => hν (Measure.measure_univ_eq_zero.mp h)
      · exact ne_of_lt (measure_lt_top ν Set.univ)
  calc
    InformationTheory.klDiv ν₁ ν₀ =
        InformationTheory.klDiv
          (finiteMeasureMass ν₁ • normalizedFiniteMeasure ν₁ P₀)
          (finiteMeasureMass ν₀ • normalizedFiniteMeasure ν₀ P₀) := by
            rw [hrecover ν₁, hrecover ν₀]
    _ = _ := klDiv_smul_probabilities
      (normalizedFiniteMeasure ν₁ P₀) (normalizedFiniteMeasure ν₀ P₀)
      (finiteMeasureMass ν₁) (finiteMeasureMass ν₀)



open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- [Two finite intensity measures](hyp:ν₁,ν₀), [a shared fallback probability law](hyp:P₀),
[a shared real mark law](hyp:R), and [a nonnegative scalar intensity](hyp:lam) imply that
[the marked-Poisson divergence](goal) is intensity times finite-measure divergence, including
unequal total masses. -/
theorem klDiv_finiteMeasureMarkedPoissonLaw_unequal
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (ν₁ ν₀ : Measure X) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₀]
    (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    InformationTheory.klDiv
        (finiteMeasureMarkedPoissonLaw ν₁ P₀ R lam)
        (finiteMeasureMarkedPoissonLaw ν₀ P₀ R lam) =
      (lam : ℝ≥0∞) * InformationTheory.klDiv ν₁ ν₀ := by
  /- Unfold each marked law; use `klDiv_finiteMarkedPoissonSampleLaw_unequal`.
     Rewrite count KL by `klDiv_poissonMeasure` and scale the rate expression
     with `poissonRateKL_mul_left`. The remaining sum is `lam *` the
     `klDiv_eq_poissonRateKL_add_normalized` identity; use distributivity.
     Do not split on absolute continuity or mass here: those cases are
     already covered by the two imported identities, including `0 * ∞`. -/
  unfold finiteMeasureMarkedPoissonLaw
  rw [klDiv_finiteMarkedPoissonSampleLaw_unequal, klDiv_poissonMeasure,
    poissonRateKL_mul_left,
    klDiv_eq_poissonRateKL_add_normalized ν₁ ν₀ P₀]
  simp only [ENNReal.coe_mul, mul_add, mul_assoc]

/-- [Two finite intensity measures](hyp:ν₁,ν₀), [a shared fallback probability law](hyp:P₀),
[a shared real mark law](hyp:R), [a nonnegative scalar intensity](hyp:lam), and
[a finite scaled divergence](hyp:hRHS) imply that
[the marked-Poisson divergence is finite](goal). -/
theorem klDiv_finiteMeasureMarkedPoissonLaw_unequal_ne_top
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (ν₁ ν₀ : Measure X) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₀]
    (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0)
    (hRHS : (lam : ℝ≥0∞) * InformationTheory.klDiv ν₁ ν₀ ≠ ∞) :
    InformationTheory.klDiv
        (finiteMeasureMarkedPoissonLaw ν₁ P₀ R lam)
        (finiteMeasureMarkedPoissonLaw ν₀ P₀ R lam) ≠ ∞ := by
  rw [klDiv_finiteMeasureMarkedPoissonLaw_unequal]
  exact hRHS

/-- [Two finite intensity measures](hyp:ν₁,ν₀), [a shared fallback probability law](hyp:P₀),
[a shared real mark law](hyp:R), and [a nonnegative scalar intensity](hyp:lam)
imply that [the real-valued marked-Poisson divergence](goal) is real intensity
times real finite-measure divergence. -/
theorem toReal_klDiv_finiteMeasureMarkedPoissonLaw_unequal
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (ν₁ ν₀ : Measure X) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₀]
    (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    (InformationTheory.klDiv
        (finiteMeasureMarkedPoissonLaw ν₁ P₀ R lam)
        (finiteMeasureMarkedPoissonLaw ν₀ P₀ R lam)).toReal =
      (lam : ℝ) * (InformationTheory.klDiv ν₁ ν₀).toReal := by
  rw [klDiv_finiteMeasureMarkedPoissonLaw_unequal]
  rw [ENNReal.toReal_mul]
  simp

end Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL
