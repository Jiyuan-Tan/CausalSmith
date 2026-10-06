/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.PO.ID.Partial.SupportFunction.Calculus
public import Causalean.PO.ID.Partial.RandomSet.SetValued
public import Causalean.Stat.CLT.GaussianLimit

/-! # Finite-Direction Support-Process Central Limit Theorem

This file proves a finite-dimensional central limit theorem for support-function
deviations evaluated on a fixed grid. Its main limit theorem assumes
measurability, a finite second moment, and mean zero for the resulting vector. A
separate coordinate lemma connects normalized sums to empirical Minkowski
averages for nonempty compact convex values. No theorem here identifies the
grid statistic with a Hausdorff distance or requires unit directions. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped RealInnerProductSpace

namespace Causalean.PartialID.RandomSet

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {k : ℕ} [NeZero k]

/-- For [a nonempty grid containing $k$ directions](hyp:k) and [a vector of support-process
deviations over that grid](hyp:w), the [grid supremum statistic](goal) is the largest absolute
coordinate of the vector.

The **finite-coordinate `ℓ^∞` functional** `w ↦ supⱼ |wⱼ|` on
`EuclideanSpace ℝ (Fin k)`.  This is the sup of the `|coordinate|` over the `k`
coordinates and the direct generalization of `maxAbs` (the `Fin 2` case).
The `[NeZero k]` instance makes `Finset.univ` nonempty. -/
noncomputable def maxAbsK (w : EuclideanSpace ℝ (Fin k)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => |w j|)

/-- The grid supremum statistic is continuous. -/
@[fun_prop]
lemma continuous_maxAbsK : Continuous (maxAbsK (k := k)) := by
  unfold maxAbsK
  fun_prop

/-- The grid supremum statistic is measurable. -/
@[fun_prop]
lemma measurable_maxAbsK : Measurable (maxAbsK (k := k)) :=
  continuous_maxAbsK.measurable

section CLT

variable {ψ : X → EuclideanSpace ℝ (Fin k)} (hψ : Measurable ψ)
  (hvar : Integrable (fun x => ‖ψ x‖ ^ 2) P)

/-- For [a measurable sample space equipped with a measure](hyp:X,P), [a
positive number of grid directions](hyp:k), and [a vector-valued process on that
space](hyp:ψ) that is [measurable](hyp:hψ) and has [an integrable squared norm
under the measure](hyp:hvar), the [law obtained by applying the grid supremum
statistic to its Gaussian limit is a probability measure](goal). [This follows
from taking the measurable pushforward of that Gaussian limit](step:1).

The limit law of the finite-grid support statistic is a probability measure
(pushforward of the Gaussian limit by the continuous `maxAbsK`). -/
instance : IsProbabilityMeasure ((gaussianLimit hψ hvar).map maxAbsK) :=
  Measure.isProbabilityMeasure_map measurable_maxAbsK.aemeasurable

omit [IsProbabilityMeasure P] in
/-- For a centered support process `ψ` on `k` fixed directions observed via an IID sample `S`, if
[`ψ` is mean zero, `E[ψ] = 0`](hyp:hmean), and [the normalized partial sums built from `S` are
almost-everywhere measurable at every sample size](hyp:hSum_meas), then [the grid supremum
statistic `maxAbsK` applied to those normalized sums converges in distribution to `maxAbsK`
applied to the Gaussian limit of `ψ`](goal).

**Abstract finite-vector continuous-mapping CLT.** For any centered
`k`-coordinate process, `maxAbsK` of the vector normalized sum converges in
distribution to the pushforward `(gaussianLimit ψ).map maxAbsK`. This follows
from the multivariate CLT and the continuous-mapping theorem; it does not assume
that the coordinates arise from sets or directions. -/
theorem supportProcess_sup_clt
    (S : IIDSample Ω X μ P)
    (hmean : ∫ x, ψ x ∂P = 0)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinearVec.normalizedSum S ψ (fun m => Finset.range m) n) μ) :
    Tendsto_dist_vec
      (fun n ω => maxAbsK (IsAsymLinearVec.normalizedSum S ψ (fun m => Finset.range m) n ω))
      ((gaussianLimit hψ hvar).map maxAbsK) μ
      (fun n => measurable_maxAbsK.comp_aemeasurable (hSum_meas n)) := by
  apply (Tendsto_dist_vec_iff _ _ _ _).2
  exact Tendsto_dist_vec.map_continuous continuous_maxAbsK hSum_meas
    (S.clt_normalizedSum_vec hψ hvar hmean)

end CLT

/-! ## Instantiation on set-valued maps

The shell above is a CLT for an abstract centered process `ψ`.  Here we feed it
the **support process** of a set-valued random variable, giving a finite-grid
CLT for the normalized sum of centered support-function coordinates.  The
separate coordinate bridge below identifies that normalized sum with empirical
Minkowski-average support deviations only under the body-valued hypothesis it
states explicitly. -/

section SetValued

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For [an observation space](hyp:X), [a nonempty grid containing $k$ directions](hyp:k), [an
inner-product outcome space](hyp:V), [a set-valued outcome function](hyp:F), [a proposed center
set](hyp:EF), and [a grid of directions](hyp:p), the [centered support process](goal) maps each
observation to the vector whose coordinate in each direction is the support value of its realized
set minus the support value of the proposed center set.

The centered support process records the support value of each realized set
minus that of the proposed center. The set `EF` is only a proposed center. A
later mean-zero assumption says that these support values agree in expectation
at the listed directions; it does not identify `EF` as an Aumann expectation or
characterize equality of sets. -/
noncomputable def supportProcess (F : X → Set V) (EF : Set V) (p : Fin k → V) :
    X → EuclideanSpace ℝ (Fin k) :=
  fun x => (WithLp.equiv 2 (Fin k → ℝ)).symm
    (fun j => supportFn (F x) (p j) - supportFn EF (p j))

omit [MeasurableSpace X] [NeZero k] in
/-- Each coordinate of the centered support process is the corresponding support deviation. -/
@[simp] lemma supportProcess_ofLp (F : X → Set V) (EF : Set V) (p : Fin k → V)
    (x : X) (j : Fin k) :
    (supportProcess F EF p x).ofLp j
      = supportFn (F x) (p j) - supportFn EF (p j) := rfl

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [NeZero k] in
/-- Each coordinate of the normalized support-process sum is the rescaled support
deviation of the empirical Minkowski average.

**The Minkowski-mean bridge in coordinates.** The `j`-th coordinate of the
normalised sum of the support process is exactly the rescaled support deviation
of the empirical Minkowski average,
`√n · (s(pⱼ, F̄ₙ) − s(pⱼ, EF))`. This is `supportFn_minkowskiMean` pushed
through the Euclidean coordinate algebra. It does not turn the finite grid into
a Hausdorff distance. -/
lemma supportProcess_normalizedSum_apply
    (S : IIDSample Ω X μ P) (F : X → Set V) (EF : Set V) (p : Fin k → V)
    (hbody : ∀ x, IsBody (F x)) (n : ℕ) (ω : Ω) (j : Fin k) :
    IsAsymLinearVec.normalizedSum S (supportProcess F EF p)
        (fun m => Finset.range m) n ω j
      = Real.sqrt (n : ℝ)
        * (supportFn (minkowskiMean (Finset.range n) (fun i => F (S.Z i ω))) (p j)
            - supportFn EF (p j)) := by
  rw [IsAsymLinearVec.normalizedSum]
  simp only [PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply,
    supportProcess_ofLp]
  rw [supportFn_minkowskiMean (Finset.range n) (fun i => F (S.Z i ω)) (p j)
        (fun i _ => hbody (S.Z i ω)), Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hnpos : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ))]

omit [IsProbabilityMeasure P] in
/-- For a set-valued random variable `F` with center `EF`, observed via an IID sample on a finite
grid of directions `p`, if [the centered support process is measurable](hyp:hψ), [it has finite
second moment](hyp:hvar), [it is mean zero, `E[ψ] = 0`](hyp:hmean), and [the normalized partial
sums of the process are almost-everywhere measurable at every sample size](hyp:hSum_meas), then
[the grid supremum statistic applied to those normalized sums converges in distribution to the
corresponding supremum functional of the process's Gaussian limit](goal).

This is the abstract finite-grid support-process CLT specialized to the support
process generated by `F`, `EF`, and the grid `p`.  It assumes measurability,
mean zero, and measurability of the normalized sums, and concludes
convergence in distribution of `maxAbsK` applied to those normalized sums.  It
does not by itself identify the statistic with empirical Minkowski-average
support deviations; that identification is provided separately by
`supportProcess_normalizedSum_apply` under the body-valued hypothesis. -/
-- TODO(faithfulness): Beresteanu-Molinari finite-grid CLT — to reach the
-- empirical-Minkowski statement directly, the public theorem should include
-- the body-valued bridge hypotheses and identify this normalized support-process
-- statistic with the Hausdorff-over-grid empirical-Minkowski statistic.
theorem setValued_supportProcess_clt
    (S : IIDSample Ω X μ P) (F : X → Set V) (EF : Set V) (p : Fin k → V)
    (hψ : Measurable (supportProcess F EF p))
    (hvar : Integrable (fun x => ‖supportProcess F EF p x‖ ^ 2) P)
    (hmean : ∫ x, supportProcess F EF p x ∂P = 0)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinearVec.normalizedSum S (supportProcess F EF p)
        (fun m => Finset.range m) n) μ) :
    Tendsto_dist_vec
      (fun n ω => maxAbsK (IsAsymLinearVec.normalizedSum S (supportProcess F EF p)
        (fun m => Finset.range m) n ω))
      ((gaussianLimit hψ hvar).map maxAbsK) μ
      (fun n => measurable_maxAbsK.comp_aemeasurable (hSum_meas n)) :=
  supportProcess_sup_clt hψ hvar S hmean hSum_meas

end SetValued

end Causalean.PartialID.RandomSet
