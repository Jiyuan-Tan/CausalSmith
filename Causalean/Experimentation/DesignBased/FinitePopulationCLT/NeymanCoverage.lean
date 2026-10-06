/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.DifferenceInMeans
public import Causalean.Experimentation.DesignBased.NeymanComposition
public import Causalean.Experimentation.DesignBased.WaldCoverage
public import Causalean.Experimentation.TwoStageInterference.DesignBasedDifferenceInMeans
public import Causalean.Stat.Quantile.CdfConvergence

/-!
# Feasible Neyman coverage under complete randomization

This module combines the finite-population difference-in-means CLT with consistency of the two
arm sample variances and the generic feasible Wald transfer theorem.  The resulting random Neyman
interval has asymptotic coverage at least its nominal level.
-/

@[expose] public section

open scoped BigOperators Topology
namespace Causalean.Experimentation.DesignBased
open Causalean.Stat Filter FinitePopulationMoments ProbabilityTheory
open MeasureTheory

private lemma finiteDesign_const_boundedInProb_of_tendsto
    {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (D : ∀ n, FiniteDesign (Ω n)) (a : ℕ → ℝ) (c : ℝ)
    (ha : Tendsto a atTop (nhds c)) :
    FiniteDesign.BoundedInProb D (fun n _ => a n) := by
  intro η hη
  refine ⟨|c| + 1, ?_⟩
  have hev : ∀ᶠ n in atTop, |a n - c| < 1 := by
    simpa [Real.dist_eq] using (Metric.tendsto_atTop.1 ha 1 zero_lt_one)
  filter_upwards [hev] with n hn
  have han : |a n| < |c| + 1 := by
    calc
      |a n| = |(a n - c) + c| := by ring_nf
      _ ≤ |a n - c| + |c| := abs_add_le _ _
      _ < |c| + 1 := by linarith
  have hz : (D n).Pr (fun _ => |c| + 1 ≤ |a n|) = 0 := by
    unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
    simp [not_le.mpr han]
  rw [hz]
  exact hη.le

private lemma tendstoInProb_mul_deterministic_of_tendsto
    {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    {D : ∀ n, FiniteDesign (Ω n)} {X : ∀ n, Ω n → ℝ} {b : ℕ → ℝ}
    (a : ℕ → ℝ) (c : ℝ) (hX : FiniteDesign.TendstoInProb D X b)
    (ha : Tendsto a atTop (nhds c)) :
    FiniteDesign.TendstoInProb D (fun n z => a n * X n z) (fun n => a n * b n) := by
  have hzero : FiniteDesign.TendstoInProb D
      (fun n z => X n z - b n) (fun _ => 0) := by
    intro ε hε
    simpa only [sub_zero] using hX ε hε
  have hprod := hzero.mul_boundedInProb (finiteDesign_const_boundedInProb_of_tendsto D a c ha)
  intro ε hε
  convert hprod ε hε using 1
  funext n
  apply (D n).Pr_congr
  intro z
  ring_nf

private lemma scaledN_varianceEstimator_tendstoInProb
    (N K : ℕ → ℕ) [∀ n, Nonempty (Fin (N n))]
    (hK2 : ∀ n, 2 ≤ K n) (hKlt : ∀ n, K n < N n)
    (hL2 : ∀ n, 2 ≤ N n - K n)
    (Y1 Y0 : ∀ n, Fin (N n) → ℝ) (v1 v0 c1 c0 : ℝ)
    (hKTop : Tendsto K atTop atTop) (hLTop : Tendsto (fun n => N n - K n) atTop atTop)
    (hvar1 : Tendsto (fun n => popVar (Y1 n)) atTop (nhds v1))
    (hvar0 : Tendsto (fun n => popVar (Y0 n)) atTop (nhds v0))
    (hmax1 : Tendsto (fun n => popMaxSqDev (Y1 n) / (K n : ℝ)) atTop (nhds 0))
    (hmax0 : Tendsto (fun n => popMaxSqDev (Y0 n) / ((N n - K n : ℕ) : ℝ))
      atTop (nhds 0))
    (hc1 : Tendsto (fun n => (N n : ℝ) / (K n : ℝ)) atTop (nhds c1))
    (hc0 : Tendsto (fun n => (N n : ℝ) / ((N n - K n : ℕ) : ℝ)) atTop (nhds c0)) :
    FiniteDesign.TendstoInProb
      (fun n => completeRandomization (V := Fin (N n)) (K n)
        (by simpa using (hKlt n).le))
      (fun n S => (N n : ℝ) * DifferenceInMeans.varianceEstimator (K n) (Y1 n) (Y0 n) S)
      (fun n => (N n : ℝ) / (K n : ℝ) * popVar (Y1 n) +
        (N n : ℝ) / ((N n - K n : ℕ) : ℝ) * popVar (Y0 n)) := by
  let D := fun n => completeRandomization (V := Fin (N n)) (K n)
    (by simpa using (hKlt n).le)
  have ht := SampleVarianceConsistency.sampleVariance_tendstoInProb
    K hK2 (fun n => by simpa using (hKlt n).le) Y1 v1 hKTop hvar1 hmax1
  have hc := control_sampleVariance_tendstoInProb
    (U := fun n => Fin (N n)) K (fun n => by simpa using (hKlt n).le)
    (fun n => by simpa using hL2 n) Y0 v0 (by simpa using hLTop) hvar0 (by simpa using hmax0)
  have hc' : FiniteDesign.TendstoInProb D
      (fun n S => sampleVariance (N n - K n) (Y0 n)
        (finCompleteRandomizationComplementEquiv (K n) (hKlt n).le S))
      (fun n => popVar (Y0 n)) := by
    intro ε hε
    have h := hc ε hε
    convert h using 1
    funext n
    apply (D n).Pr_congr
    intro S
    have hs : sampleVariance (N n - K n) (Y0 n)
        (finCompleteRandomizationComplementEquiv (K n) (hKlt n).le S) =
      sampleVariance (Fintype.card (Fin (N n)) - K n) (Y0 n)
        (completeRandomizationComplementEquiv (K n) (by simpa using (hKlt n).le) S) := by
      unfold sampleVariance sampleMean finCompleteRandomizationComplementEquiv
        completeRandomizationComplementEquiv
      simp only [Fintype.card_fin]
      congr
    change ε ≤ |sampleVariance (N n - K n) (Y0 n)
        (finCompleteRandomizationComplementEquiv (K n) (hKlt n).le S) - popVar (Y0 n)| ↔
      ε ≤ |sampleVariance (Fintype.card (Fin (N n)) - K n) (Y0 n)
        (completeRandomizationComplementEquiv (K n)
          (by simpa using (hKlt n).le) S) - popVar (Y0 n)|
    rw [hs]
  have hts := tendstoInProb_mul_deterministic_of_tendsto
    (fun n => (N n : ℝ) / (K n : ℝ)) c1 ht hc1
  have hcs := tendstoInProb_mul_deterministic_of_tendsto
    (fun n => (N n : ℝ) / ((N n - K n : ℕ) : ℝ)) c0 hc' hc0
  have hadd := hts.add hcs
  intro ε hε
  have h := hadd ε hε
  convert h using 1
  funext n
  apply (D n).Pr_congr
  intro S
  change ε ≤ |(N n : ℝ) * DifferenceInMeans.varianceEstimator
      (K n) (Y1 n) (Y0 n) S - _| ↔ _
  rw [DifferenceInMeans.varianceEstimator_eq_sampleVariances (K n) (hKlt n).le]
  change ε ≤ |(N n : ℝ) *
      (sampleVariance (K n) (Y1 n) S / (K n : ℝ) +
        sampleVariance (N n - K n) (Y0 n)
          (finCompleteRandomizationComplementEquiv (K n) (hKlt n).le S) /
            ((N n - K n : ℕ) : ℝ)) - _| ↔
    ε ≤ |(N n : ℝ) / (K n : ℝ) * sampleVariance (K n) (Y1 n) S +
      (N n : ℝ) / ((N n - K n : ℕ) : ℝ) *
        sampleVariance (N n - K n) (Y0 n)
          (finCompleteRandomizationComplementEquiv (K n) (hKlt n).le S) - _|
  ring

private lemma scaledVar_diffInMeans_le_proxy {N K : ℕ} (hK2 : 2 ≤ K) (hKlt : K < N)
    (hL2 : 2 ≤ N - K) (Y1 Y0 : Fin N → ℝ) :
    (N : ℝ) * (completeRandomization (V := Fin N) K
        (by simpa using hKlt.le)).Var (diffInMeans K Y1 Y0) ≤
      (N : ℝ) / (K : ℝ) * popVar Y1 +
        (N : ℝ) / ((N - K : ℕ) : ℝ) * popVar Y0 := by
  have hKpos : 0 < K := by omega
  have hS0 : S0 Y0 = popVar Y0 := by
    simp [S0, popVar, popMeanV, popMean]
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
  have hStau : 0 ≤ Stau Y1 Y0 / (N : ℝ) := by
    apply div_nonneg
    · unfold Stau
      apply div_nonneg
      · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
      · linarith
    · linarith
  have hbase :
      (completeRandomization (V := Fin N) K (by simpa using hKlt.le)).Var
          (diffInMeans K Y1 Y0) ≤
        popVar Y1 / (K : ℝ) + popVar Y0 / ((N - K : ℕ) : ℝ) := by
    rw [DifferenceInMeans.Var_diffInMeans_eq_neyman hKpos hKlt, S1_eq_popVar, hS0]
    rw [Nat.cast_sub hKlt.le]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg N)
  calc
    (N : ℝ) * (completeRandomization (V := Fin N) K
        (by simpa using hKlt.le)).Var (diffInMeans K Y1 Y0)
        ≤ (N : ℝ) *
          (popVar Y1 / (K : ℝ) + popVar Y0 / ((N - K : ℕ) : ℝ)) := hmul
    _ = (N : ℝ) / (K : ℝ) * popVar Y1 +
        (N : ℝ) / ((N - K : ℕ) : ℝ) * popVar Y0 := by ring

private lemma varianceEstimator_undershoot_tendsto_zero
    (N K : ℕ → ℕ) [∀ n, Nonempty (Fin (N n))]
    (hK2 : ∀ n, 2 ≤ K n) (hKlt : ∀ n, K n < N n)
    (hL2 : ∀ n, 2 ≤ N n - K n) (Y1 Y0 : ∀ n, Fin (N n) → ℝ)
    (v : ℝ) (hv : 0 < v)
    (hscaled : FiniteDesign.TendstoInProb
      (fun n => completeRandomization (V := Fin (N n)) (K n)
        (by simpa using (hKlt n).le))
      (fun n S => (N n : ℝ) * DifferenceInMeans.varianceEstimator (K n) (Y1 n) (Y0 n) S)
      (fun n => (N n : ℝ) / (K n : ℝ) * popVar (Y1 n) +
        (N n : ℝ) / ((N n - K n : ℕ) : ℝ) * popVar (Y0 n)))
    (htrue : Tendsto (fun n => (N n : ℝ) *
      (completeRandomization (V := Fin (N n)) (K n)
        (by simpa using (hKlt n).le)).Var (diffInMeans (K n) (Y1 n) (Y0 n)))
      atTop (nhds v)) :
    ∀ η : ℝ, 0 < η → Tendsto (fun n =>
      (completeRandomization (V := Fin (N n)) (K n)
        (by simpa using (hKlt n).le)).Pr (fun S =>
          DifferenceInMeans.varianceEstimator (K n) (Y1 n) (Y0 n) S <
            (1 - η) * (completeRandomization (V := Fin (N n)) (K n)
              (by simpa using (hKlt n).le)).Var (diffInMeans (K n) (Y1 n) (Y0 n))))
      atTop (nhds 0) := by
  intro η hη
  have hε : 0 < η * v / 2 := by positivity
  have htail := hscaled (η * v / 2) hε
  have htrueLower : ∀ᶠ n in atTop, v / 2 ≤ (N n : ℝ) *
      (completeRandomization (V := Fin (N n)) (K n)
        (by simpa using (hKlt n).le)).Var (diffInMeans (K n) (Y1 n) (Y0 n)) := by
    have hnear := (Metric.tendsto_nhds.1 htrue) (v / 2) (by positivity)
    filter_upwards [hnear] with n hn
    rw [Real.dist_eq] at hn
    linarith [abs_lt.1 hn |>.1]
  refine squeeze_zero' (by
    filter_upwards [] with n
    exact (completeRandomization (V := Fin (N n)) (K n)
      (by simpa using (hKlt n).le)).Pr_nonneg _) ?_ htail
  filter_upwards [htrueLower] with n hn
  apply (completeRandomization (V := Fin (N n)) (K n)
    (by simpa using (hKlt n).le)).Pr_mono
  intro S hbad
  let trueScale := (N n : ℝ) *
    (completeRandomization (V := Fin (N n)) (K n)
      (by simpa using (hKlt n).le)).Var (diffInMeans (K n) (Y1 n) (Y0 n))
  let proxy := (N n : ℝ) / (K n : ℝ) * popVar (Y1 n) +
    (N n : ℝ) / ((N n - K n : ℕ) : ℝ) * popVar (Y0 n)
  let feasible := (N n : ℝ) *
    DifferenceInMeans.varianceEstimator (K n) (Y1 n) (Y0 n) S
  have hKposNat : 0 < K n := lt_of_lt_of_le (by norm_num) (hK2 n)
  have hNposNat : 0 < N n := hKposNat.trans (hKlt n)
  have hNpos : (0 : ℝ) < N n := by exact_mod_cast hNposNat
  have hproxy : trueScale ≤ proxy := by
    exact scaledVar_diffInMeans_le_proxy (hK2 n) (hKlt n) (hL2 n) (Y1 n) (Y0 n)
  have hbadScaled : feasible < (1 - η) * trueScale := by
    dsimp only [feasible, trueScale]
    have := mul_lt_mul_of_pos_left hbad hNpos
    nlinarith
  have htruePos : 0 < trueScale := by dsimp only [trueScale]; linarith [hv]
  have hfeasibleProxy : feasible ≤ proxy := by
    exact (calc feasible < (1 - η) * trueScale := hbadScaled
      _ < trueScale := by nlinarith
      _ ≤ proxy := hproxy).le
  change η * v / 2 ≤ |feasible - proxy|
  rw [abs_of_nonpos (sub_nonpos.mpr hfeasibleProxy)]
  nlinarith

private lemma finiteDesign_cdf_of_tendstoInDistribution
    {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)] [∀ n, MeasurableSpace (Ω n)]
    [∀ n, MeasurableSingletonClass (Ω n)]
    (D : ∀ n, FiniteDesign (Ω n)) (T : ∀ n, Ω n → ℝ)
    (hT : TendstoInDistribution (fun n => (D n).toMeasure) T
      (gaussianReal 0 1) (fun n => (measurable_of_finite (T n)).aemeasurable)) :
    ∀ t : ℝ, Tendsto (fun n => (D n).Pr (fun z => T n z ≤ t))
      atTop (nhds (stdNormalCdf t)) := by
  intro t
  let νs : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨((D n).toMeasure).map (T n),
      Measure.isProbabilityMeasure_map (measurable_of_finite (T n)).aemeasurable⟩
  let ν : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hweak : Tendsto νs atTop (nhds ν) := by
    simpa [νs, ν, Measure.map_id] using hT.tendsto
  have hcont : ContinuousAt (cdf (gaussianReal 0 1) : ℝ → ℝ) t := by
    have heq : cdf (gaussianReal 0 1) = stdNormalCdf := by
      funext x
      rw [cdf_eq_real]
      rfl
    rw [heq]
    exact continuous_stdNormalCdf.continuousAt
  have h := Causalean.Stat.tendsto_cdf_at_of_tendsto hweak hcont
  convert h using 1
  · funext n
    letI : IsProbabilityMeasure (νs n : Measure ℝ) := (νs n).property
    rw [cdf_eq_real]
    change (D n).Pr (fun z => T n z ≤ t) =
      (Measure.map (T n) (D n).toMeasure).real (Set.Iic t)
    rw [MeasureTheory.map_measureReal_apply_of_aemeasurable
      (measurable_of_finite (T n)).aemeasurable measurableSet_Iic]
    exact (FiniteDesign.toMeasure_real_setOf (D n) (fun z => T n z ≤ t)).symm
  · congr 1
    letI : IsProbabilityMeasure (ν : Measure ℝ) := ν.property
    rw [cdf_eq_real]
    change stdNormalCdf t = (gaussianReal 0 1).real (Set.Iic t)
    rfl

/-- Given [population-size and treated-count sequences](hyp:N,K) with [at least two units in each
arm](hyp:hK2,hKlt,hL2), and [fixed treated and control potential outcomes](hyp:Y1,Y0), suppose
[Li and Ding's transformed population is nondegenerate](hyp:htransVar) and [satisfies their
maximal-deviation condition](hyp:htransMax).  If [both arm sizes diverge](hyp:hKTop,hLTop), [the
arm variances converge](hyp:hvar1,hvar0) to [finite limits](hyp:v1,v0), [the armwise maximal
deviations vanish at their sampling rates](hyp:hmax1,hmax0), [the reciprocal allocation fractions
converge](hyp:hc1,hc0) to [finite limits](hyp:c1,c0), and [the scaled exact variance
converges](hyp:htrue) to [a positive limit](hyp:v,hv), then [the feasible Neyman interval formed
with the separate-arm variance estimator has coverage liminf at least `1-α`](goal) for [a
nonnegative standard-normal quantile](hyp:α,z,hz0,hz). -/
theorem diffInMeans_neyman_coverage
    (N K : ℕ → ℕ) [∀ n, Nonempty (Fin (N n))]
    (hK2 : ∀ n, 2 ≤ K n) (hKlt : ∀ n, K n < N n)
    (hL2 : ∀ n, 2 ≤ N n - K n) (Y1 Y0 : ∀ n, Fin (N n) → ℝ)
    (htransVar : ∀ n, 0 < popVar
      (diffInMeansTransformedOutcome (N n) (K n) (Y1 n) (Y0 n)))
    (htransMax : Tendsto (fun n =>
      popMaxSqDev (diffInMeansTransformedOutcome (N n) (K n) (Y1 n) (Y0 n)) /
        (((min (K n) (N n - K n) : ℕ) : ℝ) *
          popVar (diffInMeansTransformedOutcome (N n) (K n) (Y1 n) (Y0 n))))
      atTop (nhds 0))
    (v1 v0 c1 c0 v : ℝ) (hv : 0 < v)
    (hKTop : Tendsto K atTop atTop)
    (hLTop : Tendsto (fun n => N n - K n) atTop atTop)
    (hvar1 : Tendsto (fun n => popVar (Y1 n)) atTop (nhds v1))
    (hvar0 : Tendsto (fun n => popVar (Y0 n)) atTop (nhds v0))
    (hmax1 : Tendsto (fun n => popMaxSqDev (Y1 n) / (K n : ℝ)) atTop (nhds 0))
    (hmax0 : Tendsto (fun n => popMaxSqDev (Y0 n) / ((N n - K n : ℕ) : ℝ))
      atTop (nhds 0))
    (hc1 : Tendsto (fun n => (N n : ℝ) / (K n : ℝ)) atTop (nhds c1))
    (hc0 : Tendsto (fun n => (N n : ℝ) / ((N n - K n : ℕ) : ℝ)) atTop (nhds c0))
    (htrue : Tendsto (fun n => (N n : ℝ) *
      (completeRandomization (V := Fin (N n)) (K n)
        (by simpa using (hKlt n).le)).Var (diffInMeans (K n) (Y1 n) (Y0 n)))
      atTop (nhds v))
    (α z : ℝ) (hz0 : 0 ≤ z) (hz : stdNormalCdf z = 1 - α / 2) :
    1 - α ≤ liminf (fun n =>
      (completeRandomization (V := Fin (N n)) (K n)
        (by simpa using (hKlt n).le)).Pr (fun S =>
          |sateEstimand (Y1 n) (Y0 n) - diffInMeans (K n) (Y1 n) (Y0 n) S| ≤
            z * Real.sqrt (DifferenceInMeans.varianceEstimator (K n) (Y1 n) (Y0 n) S)))
      atTop := by
  let D := fun n => completeRandomization (V := Fin (N n)) (K n)
    (by simpa using (hKlt n).le)
  let est := fun n => diffInMeans (K n) (Y1 n) (Y0 n)
  let θ := fun n => sateEstimand (Y1 n) (Y0 n)
  let trueVar := fun n => (D n).Var (est n)
  let vhat := fun n => DifferenceInMeans.varianceEstimator (K n) (Y1 n) (Y0 n)
  have hKpos : ∀ n, 0 < K n := fun n => lt_of_lt_of_le (by norm_num) (hK2 n)
  have hscaled := scaledN_varianceEstimator_tendstoInProb
    N K hK2 hKlt hL2 Y1 Y0 v1 v0 c1 c0
    hKTop hLTop hvar1 hvar0 hmax1 hmax0 hc1 hc0
  have hunder := varianceEstimator_undershoot_tendsto_zero
    N K hK2 hKlt hL2 Y1 Y0 v hv hscaled htrue
  have hdist := diffInMeans_clt N K hKpos hKlt Y1 Y0 htransVar htransMax
  have hcdf0 := finiteDesign_cdf_of_tendstoInDistribution D
    (fun n S => (est n S - θ n) / Real.sqrt (trueVar n)) hdist
  have hcdf : ∀ t : ℝ, Tendsto (fun n => (D n).Pr (fun S =>
      Real.sqrt (1 : ℝ) * (est n S - θ n) / Real.sqrt (trueVar n) ≤ t))
      atTop (nhds (stdNormalCdf t)) := by
    intro t
    simpa using hcdf0 t
  have hvarpos : ∀ n, 0 < trueVar n := by
    intro n
    have hfactor : (0 : ℝ) < 1 / (K n : ℝ) - 1 / (N n : ℝ) := by
      exact sub_pos.mpr (one_div_lt_one_div_of_lt (by exact_mod_cast hKpos n)
        (by exact_mod_cast hKlt n))
    have hsrs : 0 < srsSampleMeanVariance (N n) (K n)
        (diffInMeansTransformedOutcome (N n) (K n) (Y1 n) (Y0 n)) :=
      srsSampleMeanVariance_pos (hKpos n) (hKlt n) (htransVar n)
    dsimp only [trueVar, D, est]
    rw [Var_diffInMeans_eq_scaled_srsSampleMeanVariance (hKpos n) (hKlt n)]
    have hc : (0 : ℝ) < (N n : ℝ) / ((N n - K n : ℕ) : ℝ) := by
      have hN : 0 < N n := (hKpos n).trans (hKlt n)
      have hL : 0 < N n - K n := Nat.sub_pos_of_lt (hKlt n)
      positivity
    exact mul_pos (sq_pos_of_pos hc) hsrs
  have hcov := conservative_wald_liminf_of_feasible_studentized_cdf
    D est θ trueVar (fun _ => 1) vhat (fun _ => one_pos) hvarpos hunder
    α z hcdf hz0 hz
  simpa only [D, est, θ, trueVar, vhat, div_one] using hcov

end Causalean.Experimentation.DesignBased
