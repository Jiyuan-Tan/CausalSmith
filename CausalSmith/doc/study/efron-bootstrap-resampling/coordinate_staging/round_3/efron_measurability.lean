module
public import Causalean.Stat.Bootstrap.EfronFiniteRepresentation
public import Causalean.Stat.Quantile.Quantile

/-!
# Measurability of bootstrap distribution functions and quantiles

This module defines the data-dependent bootstrap CDF and lower quantile.  The CDF is a finite
average of measurable threshold indicators.  Right-continuity reduces the quantile infimum to
rational thresholds, yielding measurability as a function of the observed data.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- Given [a statistic](hyp:T), [observed data](hyp:x), and [a threshold](hyp:t), the [bootstrap
cumulative distribution value](goal) is the real mass that the bootstrap law assigns to
`(-∞,t]`. -/
def bootstrapCDF (T : (Fin n → X) → ℝ) (x : Fin n → X) (t : ℝ) : ℝ :=
  (bootstrapLaw T x (Iic t)).toReal

/-- For [a real-valued sample statistic](hyp:T) that is [measurable](hyp:hT), [observed data]
(hyp:x), [a threshold](hyp:t), and [a nonzero sample size](hyp:hn), [the bootstrap CDF is the
average of the threshold indicators over all index resamples](goal). -/
theorem bootstrapCDF_eq_average_indicators (T : (Fin n → X) → ℝ) (hT : Measurable T)
    (x : Fin n → X) (t : ℝ) (hn : n ≠ 0) :
    bootstrapCDF T x t =
      ((n : ℝ) ^ n)⁻¹ *
        ∑ j : Fin n → Fin n, if T (x ∘ j) ≤ t then 1 else 0 := by
  -- Proof plan: use `Measure.map_apply hT` on `Iic t`, rewrite the resampling measure by its
  -- atomic representation, and evaluate each Dirac mass; `hn` converts the ENNReal weight.
  classical
  unfold bootstrapCDF bootstrapLaw
  rw [Measure.map_apply hT measurableSet_Iic, bootstrapResample_eq_average_dirac,
    Measure.smul_apply, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply' _ (hT measurableSet_Iic), smul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_natCast]
  rw [ENNReal.toReal_sum (by
    intro j hj
    by_cases h : T (x ∘ j) ≤ t <;> simp [Set.indicator, h])]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : T (x ∘ j) ≤ t <;> simp [Set.indicator, h]

/-- For [a real-valued sample statistic](hyp:T) that is [measurable](hyp:hT), [a nonzero sample
size](hyp:hn), and [each fixed threshold](hyp:t), [the bootstrap CDF is measurable as a function
of the data](goal). -/
theorem measurable_bootstrapCDF (T : (Fin n → X) → ℝ) (hT : Measurable T)
    (hn : n ≠ 0) (t : ℝ) :
    Measurable (fun x : Fin n → X ↦ bootstrapCDF T x t) := by
  -- Proof plan: rewrite by `bootstrapCDF_eq_average_indicators`; for fixed `j`, the map
  -- `x ↦ x ∘ j` is measurable coordinatewise, hence so is the threshold indicator.
  classical
  rw [show (fun x : Fin n → X ↦ bootstrapCDF T x t) = fun x ↦
      ((n : ℝ) ^ n)⁻¹ *
        ∑ j : Fin n → Fin n, if T (x ∘ j) ≤ t then 1 else 0 by
    funext x
    exact bootstrapCDF_eq_average_indicators T hT x t hn]
  apply Measurable.const_mul
  apply Finset.measurable_sum Finset.univ
  intro j hj
  have hcomp : Measurable (fun x : Fin n → X ↦ x ∘ j) := by
    refine measurable_pi_iff.mpr fun i ↦ ?_
    exact measurable_pi_apply (j i)
  exact Measurable.ite
    (measurableSet_le (hT.comp hcomp) measurable_const) measurable_const measurable_const

/-- For [a real-valued sample statistic](hyp:T) that is [measurable](hyp:hT), [observed data]
(hyp:x), [a nonzero sample size](hyp:hn), and [a threshold](hyp:t), [the bootstrap CDF is
right-continuous at that threshold](goal). -/
theorem bootstrapCDF_rightContinuous (T : (Fin n → X) → ℝ) (hT : Measurable T)
    (x : Fin n → X) (hn : n ≠ 0) (t : ℝ) :
    ContinuousWithinAt (bootstrapCDF T x) (Ici t) t := by
  -- Proof plan: install probability for `bootstrapLaw T x`, identify `bootstrapCDF` with
  -- `ProbabilityTheory.cdf` via `cdf_eq_real`, and use the Stieltjes CDF's `right_continuous`.
  let _ : IsProbabilityMeasure (bootstrapLaw T x) :=
    bootstrapLaw_isProbabilityMeasure T x hn hT
  have hcdf : bootstrapCDF T x = ProbabilityTheory.cdf (bootstrapLaw T x) := by
    funext s
    unfold bootstrapCDF
    exact (ProbabilityTheory.cdf_eq_real (bootstrapLaw T x) s).symm
  rw [hcdf]
  exact (ProbabilityTheory.cdf (bootstrapLaw T x)).right_continuous t

/-- Given [a statistic](hyp:T), [a quantile level](hyp:β), and [observed data](hyp:x), the
[lower bootstrap quantile](goal) is the infimum of thresholds where the bootstrap CDF reaches
that level. -/
def bootstrapLowerQuantile (T : (Fin n → X) → ℝ) (β : ℝ) (x : Fin n → X) : ℝ :=
  sInf {t : ℝ | β ≤ bootstrapCDF T x t}

private lemma bootstrapCDF_eq_cdf (T : (Fin n → X) → ℝ) (hT : Measurable T)
    (x : Fin n → X) (hn : n ≠ 0) (t : ℝ) :
    bootstrapCDF T x t = ProbabilityTheory.cdf (bootstrapLaw T x) t := by
  let _ : IsProbabilityMeasure (bootstrapLaw T x) :=
    bootstrapLaw_isProbabilityMeasure T x hn hT
  unfold bootstrapCDF
  exact (ProbabilityTheory.cdf_eq_real (bootstrapLaw T x) t).symm

private lemma bootstrapCDF_reaches_one (T : (Fin n → X) → ℝ) (hT : Measurable T)
    (x : Fin n → X) (hn : n ≠ 0) :
    ∃ t, bootstrapCDF T x t = 1 := by
  classical
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  let M := Finset.univ.sup' Finset.univ_nonempty
    (fun j : Fin n → Fin n ↦ T (x ∘ j))
  refine ⟨M, ?_⟩
  rw [bootstrapCDF_eq_average_indicators T hT x M hn]
  simp only [M, if_pos (Finset.le_sup' (fun j : Fin n → Fin n ↦ T (x ∘ j))
    (Finset.mem_univ _)), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  exact inv_mul_cancel₀ (pow_ne_zero n (Nat.cast_ne_zero.mpr hn))

private lemma bddBelow_bootstrapQuantileSet (T : (Fin n → X) → ℝ) (hT : Measurable T)
    (x : Fin n → X) (hn : n ≠ 0) {β : ℝ} (hβ0 : 0 < β) :
    BddBelow {t : ℝ | β ≤ bootstrapCDF T x t} := by
  obtain ⟨N, hN⟩ := Filter.eventually_atBot.mp
    ((ProbabilityTheory.tendsto_cdf_atBot (bootstrapLaw T x)).eventually_lt_const hβ0)
  refine ⟨N, fun s hs ↦ ?_⟩
  change β ≤ bootstrapCDF T x s at hs
  by_contra hlt
  push Not at hlt
  have hs' : β ≤ ProbabilityTheory.cdf (bootstrapLaw T x) s := by
    rwa [← bootstrapCDF_eq_cdf T hT x hn]
  exact (not_le_of_gt (hN s hlt.le)) hs'

private lemma nonempty_bootstrapQuantileSet (T : (Fin n → X) → ℝ) (hT : Measurable T)
    (x : Fin n → X) (hn : n ≠ 0) {β : ℝ} (hβ1 : β ≤ 1) :
    {t : ℝ | β ≤ bootstrapCDF T x t}.Nonempty := by
  obtain ⟨t, ht⟩ := bootstrapCDF_reaches_one T hT x hn
  refine ⟨t, ?_⟩
  change β ≤ bootstrapCDF T x t
  rw [ht]
  exact hβ1

private lemma le_bootstrapCDF_bootstrapLowerQuantile (T : (Fin n → X) → ℝ)
    (hT : Measurable T) (x : Fin n → X) (hn : n ≠ 0) {β : ℝ} (hβ1 : β ≤ 1) :
    β ≤ bootstrapCDF T x (bootstrapLowerQuantile T β x) := by
  set a := bootstrapLowerQuantile T β x with ha
  have hne := nonempty_bootstrapQuantileSet T hT x hn hβ1
  have hgt : ∀ y, a < y → β ≤ bootstrapCDF T x y := by
    intro y hy
    obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt hne hy
    exact le_trans hs (by
      rw [bootstrapCDF_eq_cdf T hT x hn, bootstrapCDF_eq_cdf T hT x hn]
      exact ProbabilityTheory.monotone_cdf (bootstrapLaw T x) hsy.le)
  have htends : Tendsto (bootstrapCDF T x) (𝓝[Ioi a] a)
      (𝓝 (bootstrapCDF T x a)) :=
    (bootstrapCDF_rightContinuous T hT x hn a).mono_left
      (nhdsWithin_mono a Ioi_subset_Ici_self)
  have hev : ∀ᶠ y in 𝓝[Ioi a] a, β ≤ bootstrapCDF T x y := by
    filter_upwards [self_mem_nhdsWithin] with y hy using hgt y hy
  exact ge_of_tendsto htends hev

private lemma bootstrapLowerQuantile_le_iff_aux (T : (Fin n → X) → ℝ)
    (hT : Measurable T) (x : Fin n → X) (hn : n ≠ 0) (β t : ℝ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    bootstrapLowerQuantile T β x ≤ t ↔ β ≤ bootstrapCDF T x t := by
  constructor
  · intro h
    exact le_trans (le_bootstrapCDF_bootstrapLowerQuantile T hT x hn hβ1) (by
      rw [bootstrapCDF_eq_cdf T hT x hn, bootstrapCDF_eq_cdf T hT x hn]
      exact ProbabilityTheory.monotone_cdf (bootstrapLaw T x) h)
  · exact csInf_le (bddBelow_bootstrapQuantileSet T hT x hn hβ0)

/-- For [a real-valued sample statistic](hyp:T) that is [measurable](hyp:hT), [observed data]
(hyp:x), [a nonzero sample size](hyp:hn), and [a quantile level](hyp:β) that is [positive and no
greater than one](hyp:hβ0,hβ1), [the lower bootstrap quantile can be computed by taking the
infimum only over rational thresholds](goal). -/
theorem bootstrapLowerQuantile_eq_sInf_rat (T : (Fin n → X) → ℝ) (hT : Measurable T)
    (x : Fin n → X) (hn : n ≠ 0) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    bootstrapLowerQuantile T β x =
      sInf ((fun q : ℚ ↦ (q : ℝ)) ''
        {q : ℚ | β ≤ bootstrapCDF T x (q : ℝ)}) := by
  -- Proof plan: prove both candidate sets have the same greatest lower bound.  Approximate any
  -- real candidate from above by rationals and pass the CDF inequality to the limit using
  -- `bootstrapCDF_rightContinuous`; `hβ0` bounds the sets below and `hβ1` plus finite support
  -- makes them nonempty.
  let A : Set ℝ := {t | β ≤ bootstrapCDF T x t}
  let B : Set ℝ := (fun q : ℚ ↦ (q : ℝ)) ''
    {q : ℚ | β ≤ bootstrapCDF T x (q : ℝ)}
  have hA_bdd : BddBelow A := bddBelow_bootstrapQuantileSet T hT x hn hβ0
  have hA_ne : A.Nonempty := nonempty_bootstrapQuantileSet T hT x hn hβ1
  have hBA : B ⊆ A := by
    intro y hy
    rcases hy with ⟨q, hq, rfl⟩
    exact hq
  have hB_ne : B.Nonempty := by
    obtain ⟨a, ha⟩ := hA_ne
    obtain ⟨q, haq⟩ := exists_rat_gt a
    refine ⟨(q : ℝ), ⟨q, ?_, rfl⟩⟩
    exact (bootstrapLowerQuantile_le_iff_aux T hT x hn β (q : ℝ) hβ0 hβ1).mp
      ((bootstrapLowerQuantile_le_iff_aux T hT x hn β a hβ0 hβ1).mpr ha |>.trans haq.le)
  have hB_bdd : BddBelow B := hA_bdd.mono hBA
  change sInf A = sInf B
  apply le_antisymm
  · exact le_csInf hB_ne fun b hb ↦ csInf_le hA_bdd (hBA hb)
  · apply le_csInf hA_ne
    intro a ha
    by_contra hnot
    have haB : a < sInf B := lt_of_not_ge hnot
    obtain ⟨q, haq, hqB⟩ := exists_rat_btwn haB
    have hqA : (q : ℝ) ∈ A :=
      (bootstrapLowerQuantile_le_iff_aux T hT x hn β (q : ℝ) hβ0 hβ1).mp
        ((bootstrapLowerQuantile_le_iff_aux T hT x hn β a hβ0 hβ1).mpr ha |>.trans haq.le)
    have hqmem : (q : ℝ) ∈ B := ⟨q, hqA, rfl⟩
    exact (not_le_of_gt hqB) (csInf_le hB_bdd hqmem)

/-- For [a real-valued sample statistic](hyp:T) that is [measurable](hyp:hT), [observed data]
(hyp:x), [a nonzero sample size](hyp:hn), [a quantile level](hyp:β) that is [positive and no
greater than one](hyp:hβ0,hβ1), and [a threshold](hyp:t), [a lower bootstrap quantile is at most
that threshold exactly when the bootstrap CDF has reached the level there](goal). -/
theorem bootstrapLowerQuantile_le_iff (T : (Fin n → X) → ℝ) (hT : Measurable T)
    (x : Fin n → X) (hn : n ≠ 0) (β t : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    bootstrapLowerQuantile T β x ≤ t ↔ β ≤ bootstrapCDF T x t := by
  -- Proof plan: the reverse direction is `csInf_le`; for the forward direction show the
  -- infimum attains the CDF level using right-continuity and upward closure.  At `β = 1`, use
  -- the maximum of the finite set `T (x ∘ j)` to establish nonemptiness.
  exact bootstrapLowerQuantile_le_iff_aux T hT x hn β t hβ0 hβ1

/-- For [a real-valued sample statistic](hyp:T) that is [measurable](hyp:hT), [a nonzero sample
size](hyp:hn), and [any real quantile level](hyp:β), [the lower bootstrap quantile is measurable
as a function of the data](goal).
Outside `(0,1]` the `sInf` convention makes the generalized inverse degenerate, but it remains
measurable. -/
theorem measurable_bootstrapLowerQuantile (T : (Fin n → X) → ℝ) (hT : Measurable T)
    (hn : n ≠ 0) (β : ℝ) :
    Measurable (bootstrapLowerQuantile T β) := by
  -- Proof plan: split into `β ≤ 0`, `0 < β ≤ 1`, and `1 < β`.  The outer cases are
  -- constant by CDF bounds.  In the middle case, use `measurable_of_Iic`, rewrite each preimage
  -- with `bootstrapLowerQuantile_le_iff`, and apply `measurable_bootstrapCDF`.
  by_cases hβ0 : β ≤ 0
  · rw [show bootstrapLowerQuantile T β = fun _ ↦ 0 by
      funext x
      unfold bootstrapLowerQuantile
      rw [show {t : ℝ | β ≤ bootstrapCDF T x t} = Set.univ by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact hβ0.trans (ENNReal.toReal_nonneg), Real.sInf_univ]]
    exact measurable_const
  · have hβ0' : 0 < β := lt_of_not_ge hβ0
    by_cases hβ1 : β ≤ 1
    · apply measurable_of_Iic
      intro t
      rw [show (bootstrapLowerQuantile T β) ⁻¹' Iic t =
          {x : Fin n → X | β ≤ bootstrapCDF T x t} by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq]
        exact bootstrapLowerQuantile_le_iff T hT x hn β t hβ0' hβ1]
      exact measurableSet_le measurable_const (measurable_bootstrapCDF T hT hn t)
    · have hβ1' : 1 < β := lt_of_not_ge hβ1
      rw [show bootstrapLowerQuantile T β = fun _ ↦ 0 by
        funext x
        unfold bootstrapLowerQuantile
        rw [show {t : ℝ | β ≤ bootstrapCDF T x t} = ∅ by
          ext t
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          intro ht
          let _ : IsProbabilityMeasure (bootstrapLaw T x) :=
            bootstrapLaw_isProbabilityMeasure T x hn hT
          have hcdf : bootstrapCDF T x t = ProbabilityTheory.cdf (bootstrapLaw T x) t :=
            bootstrapCDF_eq_cdf T hT x hn t
          exact (not_le_of_gt hβ1') (ht.trans (by
            rw [hcdf]
            exact ProbabilityTheory.cdf_le_one (bootstrapLaw T x) t)), Real.sInf_empty]]
      exact measurable_const

end

end Causalean.Stat
