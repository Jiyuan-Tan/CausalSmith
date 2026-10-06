/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.Efficiency.LAN.Convolution.Basic

/-!
# Likelihood-ratio normalization

This module isolates the measure-theoretic normalization facts used by Le Cam's change-of-measure
argument.  They apply to varying sample spaces and do not depend on the Gaussian structure of a
LAN experiment.
-/

public section

namespace Causalean.Estimation.Efficiency.AsymptoticLanConvolution

open Filter MeasureTheory Topology

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- If real random variables converge weakly, their exponential limit has expectation one, and
the row exponential expectations have asymptotic upper bound one, then those expectations tend
to one.  This is the nonnegative lower-semicontinuous Portmanteau step. -/
theorem exp_integral_tendsto_one_of_weaklyConverges
    {P : (n : ℕ) → Measure (Ω n)} {X : (n : ℕ) → Ω n → ℝ} {Q : Measure ℝ}
    (hP : ∀ n, IsProbabilityMeasure (P n)) (hQ : IsProbabilityMeasure Q)
    (hweak : WeaklyConverges P X Q)
    (hrowIntegrable : ∀ n, Integrable (fun ω => Real.exp (X n ω)) (P n))
    (hlimit : ∫ x, Real.exp x ∂Q = 1)
    (hupper : ∀ n, ∫ ω, Real.exp (X n ω) ∂P n ≤ 1 + Real.exp (-(n : ℝ))) :
    Tendsto (fun n => ∫ ω, Real.exp (X n ω) ∂P n) atTop (𝓝 1) := by
  -- Approximate `exp` from below by bounded continuous truncations.  Weak convergence gives
  -- their integral limits, monotone convergence recovers `hlimit`, and `hupper` supplies limsup.
  -- `hrowIntegrable` is essential because Lean's Bochner integral is defined as zero for a
  -- non-integrable function; without it the statement is false despite the numerical upper bound.
  let trunc (k : ℕ) : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun x => min (Real.exp x) (k : ℝ), Real.continuous_exp.min continuous_const⟩
      (k : ℝ) (by
        intro x y
        change |min (Real.exp x) (k : ℝ) - min (Real.exp y) (k : ℝ)| ≤ k
        have hx0 : 0 ≤ min (Real.exp x) (k : ℝ) :=
          le_min (Real.exp_pos x).le (Nat.cast_nonneg k)
        have hy0 : 0 ≤ min (Real.exp y) (k : ℝ) :=
          le_min (Real.exp_pos y).le (Nat.cast_nonneg k)
        have hxk : min (Real.exp x) (k : ℝ) ≤ k := min_le_right _ _
        have hyk : min (Real.exp y) (k : ℝ) ≤ k := min_le_right _ _
        rw [abs_le]
        constructor <;> linarith)
  have hexp_integrable : Integrable (fun x : ℝ => Real.exp x) Q := by
    by_contra h
    rw [integral_undef h] at hlimit
    norm_num at hlimit
  have htrunc_limit : Tendsto (fun k : ℕ => ∫ x, trunc k x ∂Q) atTop (𝓝 1) := by
    have hdom : Tendsto (fun k : ℕ => ∫ x, min (Real.exp x) (k : ℝ) ∂Q) atTop
        (𝓝 (∫ x, Real.exp x ∂Q)) := by
      apply tendsto_integral_of_dominated_convergence (fun x : ℝ => Real.exp x)
      · intro k
        exact (Real.continuous_exp.min continuous_const).aestronglyMeasurable
      · exact hexp_integrable
      · intro k
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg
          (le_min (Real.exp_pos x).le (Nat.cast_nonneg k))]
        exact min_le_left _ _
      · filter_upwards with x
        apply tendsto_nhds_of_eventually_eq
        have hx : ∀ᶠ k : ℕ in atTop, Real.exp x ≤ (k : ℝ) :=
          tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp x))
        filter_upwards [hx] with k hk
        exact min_eq_left hk
    simpa [trunc, hlimit] using hdom
  have htrunc_row_integrable (k n : ℕ) :
      Integrable (fun ω => trunc k (X n ω)) (P n) := by
    apply (hrowIntegrable n).mono'
    · exact (trunc k).continuous.measurable.comp_aemeasurable
        (hweak.1 n) |>.aestronglyMeasurable
    · filter_upwards with ω
      change |min (Real.exp (X n ω)) (k : ℝ)| ≤ Real.exp (X n ω)
      rw [abs_of_nonneg
        (le_min (Real.exp_pos (X n ω)).le (Nat.cast_nonneg k))]
      exact min_le_left _ _
  have hexp_zero : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨k, hk⟩ := ((tendsto_order.mp htrunc_limit).1 a ha).exists
    have hweak_k := hweak.2 (trunc k)
    filter_upwards [(tendsto_order.mp hweak_k).1 _ hk] with n hn
    exact hn.trans_le (integral_mono (htrunc_row_integrable k n) (hrowIntegrable n)
      fun ω => min_le_left _ _)
  · intro b hb
    have hup : Tendsto (fun n : ℕ => 1 + Real.exp (-(n : ℝ))) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hexp_zero
    filter_upwards [(tendsto_order.mp hup).2 b hb] with n hn
    exact (hupper n).trans_lt hn

/-- For [a fixed local direction](hyp:h), [a complex observable measurable under both the local and base laws](hyp:hlocal,hbase), [a uniform bound for that observable](hyp:hbounded), and [asymptotic likelihood-ratio normalization](hyp:hnormalized), [its local-law integral and guarded likelihood-ratio base-law integral have vanishing difference](goal). -/
theorem local_integral_sub_exp_logLikelihoodRatio_integral_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] {E : LocalExperiment Ω H} (h : H)
    {φ : (n : ℕ) → Ω n → ℂ}
    (hlocal : ∀ n, AEMeasurable (φ n) (E.localLaw n h))
    (hbase : ∀ n, AEMeasurable (φ n) (E.baseLaw n))
    (hbounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ n ω, ‖φ n ω‖ ≤ C)
    (hnormalized : Tendsto
      (fun n => ∫ ω, Real.exp (E.logLikelihoodRatio n h ω) ∂E.baseLaw n)
      atTop (𝓝 1)) :
    Tendsto (fun n =>
      (∫ ω, φ n ω ∂E.localLaw n h) -
        ∫ ω, φ n ω * (Real.exp (E.logLikelihoodRatio n h ω) : ℂ) ∂E.baseLaw n)
      atTop (𝓝 0) := by
  -- Decompose the local measure into its absolutely continuous and singular parts.  On the
  -- positive-density set the guarded exponential is the RN derivative; on its zero set it is
  -- `exp (-n)`.  Normalization forces the missing singular mass to zero, and boundedness of `φ`
  -- controls both errors.
  rcases hbounded with ⟨C, hC, hφ⟩
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hnormalization (n : ℕ) :
      (∫ ω, Real.exp (E.logLikelihoodRatio n h ω) ∂E.baseLaw n) =
        1 - ((E.localLaw n h).singularPart (E.baseLaw n)).real Set.univ +
          Real.exp (-(n : ℝ)) *
            (E.baseLaw n).real {ω |
              ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal = 0} := by
    letI : IsProbabilityMeasure (E.baseLaw n) := E.base_probability n
    letI : IsProbabilityMeasure (E.localLaw n h) := E.local_probability n h
    let r : Ω n → ℝ := fun ω =>
      ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal
    let z : Set (Ω n) := {ω | r ω = 0}
    have hr : Measurable r :=
      (Measure.measurable_rnDeriv _ _).ennreal_toReal
    have hz : MeasurableSet z := hr (measurableSet_singleton 0)
    have hr_int : Integrable r (E.baseLaw n) := by
      simpa only [integrableOn_univ] using
        (Measure.integrableOn_toReal_rnDeriv
          (μ := E.localLaw n h) (ν := E.baseLaw n) (s := Set.univ)
          (measure_ne_top _ _))
    have hi_int : Integrable (z.indicator fun _ => Real.exp (-(n : ℝ)))
        (E.baseLaw n) :=
      (integrable_const _).indicator hz
    have hpoint : (fun ω => Real.exp (E.logLikelihoodRatio n h ω)) =
        fun ω => r ω + z.indicator (fun _ => Real.exp (-(n : ℝ))) ω := by
      funext ω
      unfold LocalExperiment.logLikelihoodRatio
      dsimp only
      by_cases hzero : r ω = 0
      · simp [r, z, hzero]
      · have hpos : 0 < r ω := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
        simp [r, z, hzero, Real.exp_log hpos]
    rw [hpoint, integral_add hr_int hi_int, integral_indicator hz,
      setIntegral_const, Measure.integral_toReal_rnDeriv']
    simp [r, z]
    ring
  have hsmall : Tendsto (fun n : ℕ =>
      Real.exp (-(n : ℝ)) *
        (E.baseLaw n).real {ω |
          ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal = 0})
      atTop (𝓝 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n : ℕ =>
        mul_nonneg (Real.exp_pos _).le measureReal_nonneg)
      (Filter.Eventually.of_forall fun n : ℕ => ?_) hexp
    haveI : IsProbabilityMeasure (E.baseLaw n) := E.base_probability n
    exact mul_le_of_le_one_right (Real.exp_pos _).le measureReal_le_one
  have hsing : Tendsto (fun n =>
      ((E.localLaw n h).singularPart (E.baseLaw n)).real Set.univ)
      atTop (𝓝 0) := by
    have heq : (fun n : ℕ =>
        ((E.localLaw n h).singularPart (E.baseLaw n)).real Set.univ) =
        fun n : ℕ => 1 +
          (Real.exp (-(n : ℝ)) *
            (E.baseLaw n).real {ω |
              ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal = 0}) -
          (∫ ω, Real.exp (E.logLikelihoodRatio n h ω) ∂E.baseLaw n) := by
      funext n
      rw [hnormalization n]
      ring
    rw [heq]
    convert (tendsto_const_nhds.add hsmall).sub hnormalized using 1 <;> norm_num
  have herror (n : ℕ) :
      (∫ ω, φ n ω ∂E.localLaw n h) -
          ∫ ω, φ n ω * (Real.exp (E.logLikelihoodRatio n h ω) : ℂ) ∂E.baseLaw n =
        (∫ ω, φ n ω ∂(E.localLaw n h).singularPart (E.baseLaw n)) -
          (Real.exp (-(n : ℝ)) : ℂ) *
            ∫ ω in {ω |
              ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal = 0}, φ n ω ∂E.baseLaw n := by
    letI : IsProbabilityMeasure (E.baseLaw n) := E.base_probability n
    letI : IsProbabilityMeasure (E.localLaw n h) := E.local_probability n h
    let r : Ω n → ℝ := fun ω =>
      ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal
    let z : Set (Ω n) := {ω | r ω = 0}
    have hr : Measurable r :=
      (Measure.measurable_rnDeriv _ _).ennreal_toReal
    have hz : MeasurableSet z := hr (measurableSet_singleton 0)
    have hφlocal : Integrable (φ n) (E.localLaw n h) :=
      Integrable.of_bound (hlocal n).aestronglyMeasurable C
        (ae_of_all _ (hφ n))
    have hφsing : Integrable (φ n)
        ((E.localLaw n h).singularPart (E.baseLaw n)) :=
      hφlocal.mono_measure (Measure.singularPart_le _ _)
    have hφdensity : Integrable (φ n)
        ((E.baseLaw n).withDensity ((E.localLaw n h).rnDeriv (E.baseLaw n))) := by
      have hi := hφlocal
      rw [← Measure.singularPart_add_rnDeriv
        (E.localLaw n h) (E.baseLaw n)] at hi
      exact (integrable_add_measure.mp hi).2
    have hdecomp :
        (∫ ω, φ n ω ∂E.localLaw n h) =
          (∫ ω, φ n ω ∂(E.localLaw n h).singularPart (E.baseLaw n)) +
            ∫ ω, φ n ω ∂(E.baseLaw n).withDensity
              ((E.localLaw n h).rnDeriv (E.baseLaw n)) := by
      calc
        (∫ ω, φ n ω ∂E.localLaw n h) =
            ∫ ω, φ n ω ∂((E.localLaw n h).singularPart (E.baseLaw n) +
              (E.baseLaw n).withDensity
                ((E.localLaw n h).rnDeriv (E.baseLaw n))) := by
              rw [Measure.singularPart_add_rnDeriv]
        _ = _ := integral_add_measure hφsing hφdensity
    have hweight_point : (fun ω =>
        φ n ω * (Real.exp (E.logLikelihoodRatio n h ω) : ℂ)) =
        fun ω => φ n ω * (r ω : ℂ) +
          (z.indicator fun ω =>
            φ n ω * (Real.exp (-(n : ℝ)) : ℂ)) ω := by
      funext ω
      unfold LocalExperiment.logLikelihoodRatio
      dsimp only
      by_cases hzero : r ω = 0
      · simp [r, z, hzero]
      · have hpos : 0 < r ω := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
        simp [r, z, hzero, Real.exp_log hpos]
    have hdensity :
        (∫ ω, φ n ω ∂(E.baseLaw n).withDensity
          ((E.localLaw n h).rnDeriv (E.baseLaw n))) =
          ∫ ω, φ n ω * (r ω : ℂ) ∂E.baseLaw n := by
      rw [integral_withDensity_eq_integral_toReal_smul
        (Measure.measurable_rnDeriv _ _) (Measure.rnDeriv_lt_top _ _) (φ n)]
      apply integral_congr_ae
      filter_upwards with ω
      simp [r, mul_comm]
    have hmul_int : Integrable (fun ω => φ n ω * (r ω : ℂ)) (E.baseLaw n) := by
      have hi := (integrable_withDensity_iff_integrable_smul'
        (Measure.measurable_rnDeriv _ _) (Measure.rnDeriv_lt_top _ _)).mp hφdensity
      exact hi.congr (ae_of_all _ fun ω => by simp [r, mul_comm])
    have hind_int : Integrable
        (z.indicator fun ω => φ n ω * (Real.exp (-(n : ℝ)) : ℂ))
        (E.baseLaw n) := by
      have hi := ((Integrable.of_bound (hbase n).aestronglyMeasurable C
        (ae_of_all _ (hφ n))).indicator hz).mul_const
          (Real.exp (-(n : ℝ)) : ℂ)
      exact hi.congr (ae_of_all _ fun ω => by
        by_cases hw : ω ∈ z <;> simp [hw])
    rw [hdecomp, hweight_point, integral_add, hdensity]
    · rw [integral_indicator hz, integral_mul_const]
      ring
    · exact hmul_int
    · exact hind_int
  rw [show (fun n =>
      (∫ ω, φ n ω ∂E.localLaw n h) -
        ∫ ω, φ n ω * (Real.exp (E.logLikelihoodRatio n h ω) : ℂ) ∂E.baseLaw n) =
      fun n =>
        (∫ ω, φ n ω ∂(E.localLaw n h).singularPart (E.baseLaw n)) -
          (Real.exp (-(n : ℝ)) : ℂ) *
            ∫ ω in {ω |
              ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal = 0}, φ n ω ∂E.baseLaw n from
    funext herror]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero
  · intro n
    exact norm_nonneg _
  · intro n
    letI : IsProbabilityMeasure (E.baseLaw n) := E.base_probability n
    letI : IsProbabilityMeasure (E.localLaw n h) := E.local_probability n h
    calc
      ‖(∫ ω, φ n ω ∂(E.localLaw n h).singularPart (E.baseLaw n)) -
          (Real.exp (-(n : ℝ)) : ℂ) *
            ∫ ω in {ω |
              ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal = 0}, φ n ω ∂E.baseLaw n‖
          ≤ C * ((E.localLaw n h).singularPart (E.baseLaw n)).real Set.univ +
              Real.exp (-(n : ℝ)) * C := by
            calc
              _ ≤ ‖∫ ω, φ n ω ∂(E.localLaw n h).singularPart (E.baseLaw n)‖ +
                    ‖(Real.exp (-(n : ℝ)) : ℂ) *
                      ∫ ω in {ω |
                        ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal = 0},
                          φ n ω ∂E.baseLaw n‖ := norm_sub_le _ _
              _ ≤ C * ((E.localLaw n h).singularPart (E.baseLaw n)).real Set.univ +
                    Real.exp (-(n : ℝ)) *
                      (C * (E.baseLaw n).real {ω |
                        ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal = 0}) := by
                  gcongr
                  · exact norm_integral_le_of_norm_le_const (ae_of_all _ (hφ n))
                  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                      abs_of_pos (Real.exp_pos _)]
                    gcongr
                    have hb := norm_integral_le_of_norm_le_const
                      (μ := (E.baseLaw n).restrict {ω |
                        ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal = 0})
                      (ae_of_all _ (hφ n))
                    simpa [measureReal_restrict_apply] using hb
              _ ≤ C * ((E.localLaw n h).singularPart (E.baseLaw n)).real Set.univ +
                    Real.exp (-(n : ℝ)) * C := by
                  gcongr
                  exact mul_le_of_le_one_right hC measureReal_le_one
      _ = C * ((E.localLaw n h).singularPart (E.baseLaw n)).real Set.univ +
          C * Real.exp (-(n : ℝ)) := by ring
  · convert (tendsto_const_nhds.mul hsing).add
      (tendsto_const_nhds.mul hexp) using 1 <;> norm_num

end Causalean.Estimation.Efficiency.AsymptoticLanConvolution
