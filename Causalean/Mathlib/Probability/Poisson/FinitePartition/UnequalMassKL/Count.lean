module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.KL
public import Causalean.Mathlib.Probability.Poisson.Moments

/-!
# Unequal-rate Poisson count divergence

This module gives the exact extended-real divergence of Poisson count laws at
arbitrary nonnegative rates, including zero rates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL

/-- [The Poisson count law at zero rate](goal) is the point mass at count zero. -/
theorem poissonMeasure_zero_eq_dirac :
    poissonMeasure 0 = Measure.dirac 0 := by
  ext s hs
  rw [poissonMeasure, Measure.sum_apply _ hs]
  refine (tsum_eq_single 0 ?_).trans ?_
  · intro n hn
    rw [Measure.smul_apply, smul_eq_mul]
    simp [zero_pow hn]
  · simp

/-- On a countable discrete space with positive target singleton masses, the
Radon–Nikodym derivative is almost everywhere the ratio of singleton masses. -/
private theorem rnDeriv_countable_ae_eq_singleton_ratio
    (μ ν : Measure ℕ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (hν : ∀ n, 0 < ν {n}) :
    μ.rnDeriv ν =ᵐ[ν] (fun n : ℕ => μ {n} / ν {n}) := by
  /- Evaluate `ν.withDensity (μ.rnDeriv ν) = μ` on each singleton.
     Its positive finite target mass gives the ratio at every point. -/
  apply Filter.Eventually.of_forall
  intro n
  have hmass : μ {n} = μ.rnDeriv ν n * ν {n} := by
    calc
      μ {n} = (ν.withDensity (μ.rnDeriv ν)) {n} :=
        congrArg (fun ρ : Measure ℕ => ρ {n}) (Measure.withDensity_rnDeriv_eq μ ν hμν).symm
      _ = _ := by rw [withDensity_apply _ (measurableSet_singleton n), lintegral_singleton]
  exact (ENNReal.eq_div_iff (ne_of_gt (hν n)) (measure_ne_top ν {n})).2
    (by rw [mul_comm, ← hmass])

/-- On a countable space with positive target mass at every singleton, the
log likelihood ratio is almost everywhere the log of the singleton mass ratio. -/
private theorem llr_countable_ae_eq_log_mass_ratio
    (μ ν : Measure ℕ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (hν : ∀ n, 0 < ν.real {n}) :
    llr μ ν =ᵐ[μ]
      (fun n : ℕ => Real.log (μ.real {n} / ν.real {n})) := by
  have hν' : ∀ n, 0 < ν {n} := by
    intro n
    exact (ENNReal.toReal_pos_iff.mp (by simpa only [measureReal_def] using hν n)).1
  have h := hμν.ae_eq (rnDeriv_countable_ae_eq_singleton_ratio μ ν hμν hν')
  filter_upwards [h] with n hn
  simp only [llr, hn, measureReal_def, ENNReal.toReal_div]

/-- For two positive Poisson rates, the log ratio of count probabilities is
the count times the log rate ratio plus target rate minus source rate. -/
private theorem poisson_log_mass_ratio (r s : ℝ≥0)
    (hr : r ≠ 0) (hs : s ≠ 0) (n : ℕ) :
    Real.log ((poissonMeasure r).real {n} /
      (poissonMeasure s).real {n}) =
      (n : ℝ) * Real.log ((r : ℝ) / (s : ℝ)) +
        (s : ℝ) - (r : ℝ) := by
  /- Rewrite both masses by `poissonMeasure_real_singleton`; cancel the
     factorial, split `log` over positive factors, and use `log_pow`. -/
  rw [poissonMeasure_real_singleton, poissonMeasure_real_singleton]
  have hr₀ : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have hs₀ : (s : ℝ) ≠ 0 := by exact_mod_cast hs
  have hf₀ : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) hf₀,
    Real.log_div (by positivity) hf₀,
    Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hr₀),
    Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hs₀),
    Real.log_exp, Real.log_exp, Real.log_pow, Real.log_pow,
    Real.log_div hr₀ hs₀]
  ring


open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

private lemma poissonPMFReal_succ_mul (r : ℝ≥0) (n : ℕ) :
    (n + 1 : ℝ) * poissonPMFReal r (n + 1) =
      (r : ℝ) * poissonPMFReal r n := by
  rw [poissonPMFReal, poissonPMFReal, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

private lemma poissonPMF_succ_mul (r : ℝ≥0) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ≥0∞) * poissonPMF r (n + 1) =
      (r : ℝ≥0∞) * poissonPMF r n := by
  change ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (poissonPMFReal r (n + 1)) =
    (r : ℝ≥0∞) * ENNReal.ofReal (poissonPMFReal r n)
  have h := congrArg ENNReal.ofReal (poissonPMFReal_succ_mul r n)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)] at h
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one] at h
  simpa using h

/-- [A nonnegative Poisson rate](hyp:r) determines [an extended-real first count moment](goal)
equal to that rate. -/
theorem poisson_lintegral_count (r : ℝ≥0) :
    ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂poissonMeasure r = (r : ℝ≥0∞) := by
  rw [lintegral_countable']
  simp_rw [poissonMeasure_singleton_eq_poissonPMF]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  simp_rw [poissonPMF_succ_mul]
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]


/-- [Two nonnegative Poisson rates](hyp:r,s) determine [the extended-real rate divergence](goal),
given by [three cases](step:1): the second rate when the first rate is zero; infinity when
the first rate is positive and the second is zero; and otherwise the first rate times the
logarithm of the ratio of first to second rate, plus the second rate, minus the first. -/
noncomputable def poissonRateKL (r s : ℝ≥0) : ℝ≥0∞ :=
  if r = 0 then (s : ℝ≥0∞)
  else if s = 0 then ∞
  else ENNReal.ofReal
    ((r : ℝ) * Real.log ((r : ℝ) / (s : ℝ)) + (s : ℝ) - (r : ℝ))

/-- A zero-rate Poisson source has KL divergence equal to the target rate. -/
private theorem klDiv_poissonMeasure_zero_left (s : ℝ≥0) :
    InformationTheory.klDiv (poissonMeasure 0) (poissonMeasure s) =
      (s : ℝ≥0∞) := by
  by_cases hs : s = 0
  · subst s
    simp
  have hspos : 0 < s := pos_of_ne_zero hs
  have hmass : ∀ n : ℕ, 0 < (poissonMeasure s).real {n} := by
    intro n
    exact poissonMeasure_real_singleton_pos n hspos
  have hac : poissonMeasure 0 ≪ poissonMeasure s := by
    rw [poissonMeasure_zero_eq_dirac]
    apply Measure.AbsolutelyContinuous.mk
    intro t ht hnull
    have hnot : 0 ∉ t := by
      intro hmem
      have hsingle : poissonMeasure s ({0} : Set ℕ) = 0 := by
        exact le_antisymm ((measure_mono (Set.singleton_subset_iff.mpr hmem)).trans hnull.le) bot_le
      have hpos : 0 < poissonMeasure s ({0} : Set ℕ) :=
        (ENNReal.toReal_pos_iff.mp (by simpa only [measureReal_def] using hmass 0)).1
      exact (ne_of_gt hpos) hsingle
    simp [hnot]
  have hllr := llr_countable_ae_eq_log_mass_ratio
    (poissonMeasure 0) (poissonMeasure s) hac hmass
  have hzero : Real.log ((poissonMeasure 0).real {0} /
      (poissonMeasure s).real {0}) = (s : ℝ) := by
    simp [poissonMeasure_real_singleton]
  have hint : Integrable (llr (poissonMeasure 0) (poissonMeasure s))
      (poissonMeasure 0) := by
    rw [poissonMeasure_zero_eq_dirac]
    exact integrable_dirac (by simp)
  rw [InformationTheory.klDiv_of_ac_of_integrable hac hint]
  have hintegral : ∫ n : ℕ, llr (poissonMeasure 0) (poissonMeasure s) n
      ∂poissonMeasure 0 = (s : ℝ) := by
    rw [integral_congr_ae hllr, poissonMeasure_zero_eq_dirac, integral_dirac]
    simpa only [poissonMeasure_zero_eq_dirac] using hzero
  rw [hintegral]
  simp

/-- A positive-rate Poisson source has infinite KL divergence against the
zero-rate Poisson target. -/
private theorem klDiv_poissonMeasure_zero_right (r : ℝ≥0) (hr : r ≠ 0) :
    InformationTheory.klDiv (poissonMeasure r) (poissonMeasure 0) = ∞ := by
  apply InformationTheory.klDiv_of_not_ac
  intro hac
  have hzero : poissonMeasure 0 ({1} : Set ℕ) = 0 := by
    simp [poissonMeasure_singleton]
  have hpos : 0 < poissonMeasure r ({1} : Set ℕ) := by
    rw [poissonMeasure_singleton]
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast (pos_of_ne_zero hr)
    exact ENNReal.ofReal_pos.mpr (by simpa using mul_pos (Real.exp_pos _) hrpos)
  exact (ne_of_gt hpos) (hac hzero)

/-- Every Poisson count law is absolutely continuous with respect to a
Poisson count law with positive rate. -/
private theorem poissonMeasure_ac_of_pos (r s : ℝ≥0) (hs : s ≠ 0) :
    poissonMeasure r ≪ poissonMeasure s := by
  apply Measure.AbsolutelyContinuous.mk
  intro t ht hnull
  have hempty : t = ∅ := by
    ext n
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hn
    have hsingle : poissonMeasure s ({n} : Set ℕ) = 0 := by
      apply le_antisymm _ bot_le
      exact (measure_mono (Set.singleton_subset_iff.mpr hn)).trans hnull.le
    have hspos : 0 < poissonMeasure s ({n} : Set ℕ) := by
      rw [poissonMeasure_singleton]
      have hsp : 0 < (s : ℝ) := by exact_mod_cast (pos_of_ne_zero hs)
      exact ENNReal.ofReal_pos.mpr (by positivity)
    exact (ne_of_gt hspos) hsingle
  simp [hempty]

/-- At positive rates, the Poisson log-likelihood ratio agrees almost
everywhere with an affine function of the observed count. -/
private theorem llr_poissonMeasure_ae_eq (r s : ℝ≥0)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    llr (poissonMeasure r) (poissonMeasure s) =ᵐ[poissonMeasure r]
      (fun n : ℕ => (n : ℝ) * Real.log ((r : ℝ) / (s : ℝ)) +
        (s : ℝ) - (r : ℝ)) := by
  /- Apply `llr_countable_ae_eq_log_mass_ratio` using
     `poissonMeasure_ac_of_pos` and positive Poisson singleton masses.
     Finish pointwise with `poisson_log_mass_ratio`. -/
  have hmass : ∀ n : ℕ, 0 < (poissonMeasure s).real {n} := by
    intro n
    exact poissonMeasure_real_singleton_pos n (pos_of_ne_zero hs)
  have hllr := llr_countable_ae_eq_log_mass_ratio
    (poissonMeasure r) (poissonMeasure s)
    (poissonMeasure_ac_of_pos r s hs) hmass
  filter_upwards [hllr] with n hn
  exact hn.trans (poisson_log_mass_ratio r s hr hs n)

/-- The log-likelihood ratio of two positive-rate Poisson count laws is
integrable under the source law. -/
private theorem integrable_llr_poissonMeasure (r s : ℝ≥0)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    Integrable (llr (poissonMeasure r) (poissonMeasure s))
      (poissonMeasure r) := by
  /- Rewrite almost everywhere using `llr_poissonMeasure_ae_eq` and use
     integrability of the count under a Poisson law. The imported Causalean
     lemma `poisson_natCast_memLp_two` supplies the real-count integrability:
     `.integrable (by norm_num)`. Build the affine function with
     `Integrable.const_mul`, `Integrable.add`, and `integrable_const`, then
     transfer integrability across the a.e. equality. -/
  have hk : Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) :=
    (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two r).integrable
      (by norm_num)
  have hfun : Integrable
      (fun n : ℕ => (n : ℝ) * Real.log ((r : ℝ) / (s : ℝ)) +
        (s : ℝ) - (r : ℝ)) (poissonMeasure r) :=
    ((hk.mul_const _).add (integrable_const _)).sub (integrable_const _)
  exact hfun.congr (llr_poissonMeasure_ae_eq r s hr hs).symm

/-- The expected log-likelihood ratio of two positive-rate Poisson count
laws is source rate times log rate ratio, plus target minus source rate. -/
private theorem integral_llr_poissonMeasure (r s : ℝ≥0)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    ∫ n : ℕ, llr (poissonMeasure r) (poissonMeasure s) n
      ∂poissonMeasure r =
      (r : ℝ) * Real.log ((r : ℝ) / (s : ℝ)) +
        (s : ℝ) - (r : ℝ) := by
  /- Use `llr_poissonMeasure_ae_eq`, linearity of the integral, and
     `poisson_natCast_first_moment` from the imported Poisson moments module.
     Replace the integral using `integral_congr_ae`, pull out the real log
     constant with `integral_const_mul`, and use `measureReal_univ` for the
     two additive constants under the probability count law. -/
  rw [integral_congr_ae (llr_poissonMeasure_ae_eq r s hr hs)]
  have hk : Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) :=
    (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two r).integrable
      (by norm_num)
  have hmul : Integrable
      (fun n : ℕ => (n : ℝ) * Real.log ((r : ℝ) / (s : ℝ)))
      (poissonMeasure r) := hk.mul_const _
  have hadd : Integrable
      (fun n : ℕ => (n : ℝ) * Real.log ((r : ℝ) / (s : ℝ)) + (s : ℝ))
      (poissonMeasure r) := hmul.add (integrable_const _)
  rw [integral_sub hadd (integrable_const _),
    integral_add hmul (integrable_const _), integral_mul_const,
    Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment]
  simp

/-- For strictly positive source and target rates, Poisson count KL is the
usual log-rate expression with the target-minus-source mass correction. -/
private theorem klDiv_poissonMeasure_pos (r s : ℝ≥0)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    InformationTheory.klDiv (poissonMeasure r) (poissonMeasure s) =
      ENNReal.ofReal
        ((r : ℝ) * Real.log ((r : ℝ) / (s : ℝ)) + (s : ℝ) - (r : ℝ)) := by
  /- Apply `InformationTheory.klDiv_of_ac_of_integrable` with
     `poissonMeasure_ac_of_pos` and `integrable_llr_poissonMeasure`.
     Rewrite the integral using `integral_llr_poissonMeasure`; both laws are
     probabilities, so the finite-measure mass correction cancels. The
     target/source rate correction is already part of the integral. -/
  rw [InformationTheory.klDiv_of_ac_of_integrable
    (poissonMeasure_ac_of_pos r s hs)
    (integrable_llr_poissonMeasure r s hr hs),
    integral_llr_poissonMeasure r s hr hs]
  simp

/-- [Two nonnegative Poisson rates](hyp:r,s) imply that
[the exact extended-real count-law divergence](goal) equals their rate
divergence, including the zero-rate cases. -/
theorem klDiv_poissonMeasure (r s : ℝ≥0) :
    InformationTheory.klDiv
        (poissonMeasure r) (poissonMeasure s) =
      poissonRateKL r s := by
  by_cases hr : r = 0
  · subst r
    simpa [poissonRateKL] using klDiv_poissonMeasure_zero_left s
  by_cases hs : s = 0
  · subst s
    simpa [poissonRateKL, hr] using klDiv_poissonMeasure_zero_right r hr
  simpa [poissonRateKL, hr, hs] using klDiv_poissonMeasure_pos r s hr hs

/-- [A common intensity multiplier and two Poisson rates](hyp:lam,r,s) imply that
[their rate divergence scales by that multiplier](goal), including zero rates. -/
theorem poissonRateKL_mul_left (lam r s : ℝ≥0) :
    poissonRateKL (lam * r) (lam * s) =
      (lam : ℝ≥0∞) * poissonRateKL r s := by
  by_cases hl : lam = 0
  · subst lam
    simp [poissonRateKL]
  by_cases hr : r = 0
  · subst r
    simp [poissonRateKL]
  by_cases hs : s = 0
  · subst s
    simp [poissonRateKL, hl, hr]
  have hlr : lam * r ≠ 0 := mul_ne_zero hl hr
  have hls : lam * s ≠ 0 := mul_ne_zero hl hs
  simp only [poissonRateKL, if_neg hlr, if_neg hls, if_neg hr, if_neg hs]
  have hla : (lam : ℝ) ≠ 0 := by exact_mod_cast hl
  have hsa : (s : ℝ) ≠ 0 := by exact_mod_cast hs
  have hratio : ((lam * r : ℝ≥0) : ℝ) / ((lam * s : ℝ≥0) : ℝ) =
      (r : ℝ) / (s : ℝ) := by
    push_cast
    field_simp
  rw [hratio]
  have hfactor :
      ((lam * r : ℝ≥0) : ℝ) * Real.log ((r : ℝ) / (s : ℝ)) +
          ((lam * s : ℝ≥0) : ℝ) - ((lam * r : ℝ≥0) : ℝ) =
        (lam : ℝ) * ((r : ℝ) * Real.log ((r : ℝ) / (s : ℝ)) +
          (s : ℝ) - (r : ℝ)) := by
    push_cast
    ring
  rw [hfactor]
  rw [ENNReal.ofReal_mul (by exact_mod_cast (show 0 ≤ lam from lam.property))]
  simp

end Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL
