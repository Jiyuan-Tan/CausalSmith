import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.ScalarMixture

/-!
# Normalized moment-matched fuzzy hypotheses

This module turns independent nonnegative coordinate weights into genuine
probability vectors, defines the prior-predictive observation laws, and
packages the two fuzzy hypotheses used by the lower bound.  Its construction
theorem records coordinate moment matching, normalization, nondegeneracy of
both unknown distributions, target concentration, and observation-mixture
closeness at the large-alphabet scale.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower

/-- Normalize nonnegative weights to a probability vector, using a designated
atom only when all weights vanish. -/
noncomputable def normalizeWeights {d : ℕ} (i0 : Fin d)
    (w : Fin d → ℝ≥0) : ProbabilityVector d := by
  classical
  let s : ℝ≥0 := ∑ i, w i
  by_cases hs : s = 0
  · exact ⟨fun i => if i = i0 then 1 else 0, by simp⟩
  · exact ⟨fun i => w i / s, by
      change (∑ i, w i / s) = 1
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, show ∑ i, w i = s by rfl, mul_inv_cancel₀ hs]⟩

/-- Normalizing weights changes them in `L₁` by exactly the absolute error in
their total mass. -/
theorem normalizeWeights_l1_raw {d : ℕ} (i0 : Fin d) (w : Fin d → ℝ≥0) :
    (∑ i, |((normalizeWeights i0 w).1 i : ℝ) - (w i : ℝ)|) =
      |((∑ i, w i : ℝ≥0) : ℝ) - 1| := by
  classical
  let S : ℝ := ((∑ i, w i : ℝ≥0) : ℝ)
  have hp : ∑ i, ((normalizeWeights i0 w).1 i : ℝ) = 1 := by
    norm_cast
    exact (normalizeWeights i0 w).2
  have hw : ∑ i, (w i : ℝ) = S := by simp [S]
  by_cases hs : (∑ i, w i) = 0
  · have hwi : ∀ i, w i = 0 := by
      intro i
      exact Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => bot_le) |>.mp hs i
        (Finset.mem_univ i)
    simp_rw [hwi, NNReal.coe_zero, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _)]
    simpa [S, hs] using hp
  · have hcoord (i : Fin d) :
        ((normalizeWeights i0 w).1 i : ℝ) = (w i : ℝ) / S := by
      simp only [normalizeWeights]
      rw [dif_neg]
      · simp [S]
      · simpa using hs
    have hSpos : 0 < S := by exact_mod_cast (pos_iff_ne_zero.mpr hs)
    by_cases hS : S ≤ 1
    · have hle (i : Fin d) :
          (w i : ℝ) ≤ ((normalizeWeights i0 w).1 i : ℝ) := by
        rw [hcoord]
        exact (le_div_iff₀ hSpos).2
          (by nlinarith [NNReal.coe_nonneg (w i)])
      simp_rw [abs_of_nonneg (sub_nonneg.mpr (hle _))]
      rw [Finset.sum_sub_distrib, hp, hw,
        abs_of_nonpos (sub_nonpos.mpr hS)]
      ring
    · have hle (i : Fin d) :
          ((normalizeWeights i0 w).1 i : ℝ) ≤ (w i : ℝ) := by
        rw [hcoord]
        exact (div_le_iff₀ hSpos).2 (by
          have : 1 ≤ S := le_of_not_ge hS
          nlinarith [NNReal.coe_nonneg (w i)])
      simp_rw [abs_of_nonpos (sub_nonpos.mpr (hle _)), neg_sub]
      rw [Finset.sum_sub_distrib, hp, hw,
        abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hS))]

/-- The normalization map from weights to probability vectors is measurable. -/
theorem measurable_normalizeWeights {d : ℕ} (i0 : Fin d) :
    Measurable (normalizeWeights i0) := by
  classical
  have hsum : Measurable (fun w : Fin d → ℝ≥0 => ∑ i, w i) := by
    fun_prop
  let Z : Set (Fin d → ℝ≥0) := {w | ∑ i, w i = 0}
  have hZ : MeasurableSet Z := by
    change MeasurableSet ((fun w : Fin d → ℝ≥0 => ∑ i, w i) ⁻¹' {0})
    exact (measurableSet_singleton 0).preimage hsum
  have heq : (fun w => (normalizeWeights i0 w).1) =
      Z.piecewise (fun _ i => if i = i0 then 1 else 0)
        (fun w i => w i / ∑ j, w j) := by
    funext w
    by_cases hw : (∑ i, w i) = 0
    · rw [Set.piecewise_eq_of_mem]
      · ext i
        simp [normalizeWeights, hw]
      · exact hw
    · rw [Set.piecewise_eq_of_notMem]
      · ext i
        simp [normalizeWeights, hw]
      · exact hw
  have hval : Measurable (fun w => (normalizeWeights i0 w).1) := by
    rw [heq]
    exact Measurable.piecewise hZ (by fun_prop) (by fun_prop)
  have hm := @Measurable.subtype_mk
    (Fin d → ℝ≥0) (Fin d → ℝ≥0) _ _
    (fun f => ∑ i, f i = 1) (fun w => (normalizeWeights i0 w).1)
    hval (fun w => (normalizeWeights i0 w).2)
  simpa only [Subtype.eta] using hm

/-- Normalize both coordinate-weight vectors in a latent pair. -/
noncomputable def normalizeWeightPair {d : ℕ} (i0 : Fin d)
    (w : (Fin d → ℝ≥0) × (Fin d → ℝ≥0)) : TwoUnknownParameter d :=
  (normalizeWeights i0 w.1, normalizeWeights i0 w.2)

/-- The joint law of two independent arrays of independent coordinate
weights. -/
noncomputable def independentWeightPairLaw {d : ℕ}
    (νp νq : Fin d → Measure ℝ≥0) :
    Measure ((Fin d → ℝ≥0) × (Fin d → ℝ≥0)) :=
  (Measure.pi νp).prod (Measure.pi νq)

/-- The constructed prior on a pair of probability vectors is the pushforward
of independent coordinate weights through normalization. -/
noncomputable def constructedParameterPrior {d : ℕ} (i0 : Fin d)
    (νp νq : Fin d → Measure ℝ≥0) : Measure (TwoUnknownParameter d) :=
  (independentWeightPairLaw νp νq).map (normalizeWeightPair i0)

/-- Independent probability coordinate laws, followed by normalization, give
a probability prior on pairs of probability vectors. -/
theorem constructedParameterPrior_isProbabilityMeasure {d : ℕ} (i0 : Fin d)
    (νp νq : Fin d → Measure ℝ≥0)
    (hp : ∀ i, IsProbabilityMeasure (νp i))
    (hq : ∀ i, IsProbabilityMeasure (νq i)) :
    IsProbabilityMeasure (constructedParameterPrior i0 νp νq) := by
  letI : ∀ i, IsProbabilityMeasure (νp i) := hp
  letI : ∀ i, IsProbabilityMeasure (νq i) := hq
  have hnorm : Measurable (normalizeWeightPair i0) := by
    unfold normalizeWeightPair
    exact ((measurable_normalizeWeights i0).comp measurable_fst).prodMk
      ((measurable_normalizeWeights i0).comp measurable_snd)
  unfold constructedParameterPrior independentWeightPairLaw
  exact Measure.isProbabilityMeasure_map hnorm.aemeasurable

/-- The prior-predictive observation law averages the full two-sample Poisson
experiment over a prior on both unknown distributions. -/
noncomputable def mixtureObservationLaw (n d : ℕ)
    (π : Measure (TwoUnknownParameter d)) : Measure (TwoSampleCounts d) :=
  π.bind fun θ => poissonizedTwoSampleLaw n θ.1 θ.2

/-- A fuzzy witness consists of two priors on the full pair-parameter space,
separated concentrated targets, and close induced observation mixtures.
Either prior may be supported on a fixed-`q` submodel. -/
structure FuzzyWitness (n d : ℕ) where
  /-- Prior for the lower-target fuzzy hypothesis. -/
  prior0 : Measure (TwoUnknownParameter d)
  /-- Prior for the upper-target fuzzy hypothesis. -/
  prior1 : Measure (TwoUnknownParameter d)
  /-- The lower-target prior is a probability measure. -/
  prior0_probability : IsProbabilityMeasure prior0
  /-- The upper-target prior is a probability measure. -/
  prior1_probability : IsProbabilityMeasure prior1
  /-- Center of the lower target cloud. -/
  center0 : ℝ
  /-- Center of the upper target cloud. -/
  center1 : ℝ
  /-- Concentration radius of each target cloud. -/
  radius : ℝ
  /-- The concentration radius is strictly positive. -/
  radius_pos : 0 < radius
  /-- The two target clouds are separated by at least twice their diameters. -/
  target_separated : center0 + 2 * radius ≤ center1 - 2 * radius
  /-- The lower target lies within its cloud with probability at least `15/16`. -/
  target0_concentrated :
    (15 : ℝ≥0∞) / 16 ≤ prior0
      {θ | |probabilityVectorL1 θ.1 θ.2 - center0| ≤ radius}
  /-- The upper target lies within its cloud with probability at least `15/16`. -/
  target1_concentrated :
    (15 : ℝ≥0∞) / 16 ≤ prior1
      {θ | |probabilityVectorL1 θ.1 θ.2 - center1| ≤ radius}
  /-- Averaging the experiment over the lower prior gives a probability law. -/
  mixture0_probability : IsProbabilityMeasure (mixtureObservationLaw n d prior0)
  /-- Averaging the experiment over the upper prior gives a probability law. -/
  mixture1_probability : IsProbabilityMeasure (mixtureObservationLaw n d prior1)
  /-- The two prior-predictive observation laws are within `1/4` in total variation. -/
  mixture_tv : Causalean.Stat.tvDist
    (mixtureObservationLaw n d prior0)
    (mixtureObservationLaw n d prior1) ≤ 1 / 4

/-- A moment-matched construction records the independent scalar coordinate
priors whose normalized pushforwards are the two fuzzy hypotheses. -/
structure MomentMatchedFuzzyConstruction (n d : ℕ) where
  /-- A designated fallback atom for normalization. -/
  anchor : Fin d
  /-- Number of matched scalar moments. -/
  degree : ℕ
  /-- The moment degree is nontrivial. -/
  degree_ge_two : 2 ≤ degree
  /-- First-distribution coordinate laws under hypothesis zero. -/
  p0 : Fin d → Measure ℝ≥0
  /-- First-distribution coordinate laws under hypothesis one. -/
  p1 : Fin d → Measure ℝ≥0
  /-- Second-distribution coordinate laws under hypothesis zero. -/
  q0 : Fin d → Measure ℝ≥0
  /-- Second-distribution coordinate laws under hypothesis one. -/
  q1 : Fin d → Measure ℝ≥0
  /-- Every scalar coordinate law is a probability measure. -/
  coordinate_probability : ∀ h : Bool, ∀ side : Bool, ∀ i,
    IsProbabilityMeasure
      (if side then (if h then p1 i else p0 i)
       else (if h then q1 i else q0 i))
  /-- The first-distribution coordinates match moments across hypotheses. -/
  p_moments_eq : ∀ i k, k ≤ degree →
    (∫ x, (x : ℝ) ^ k ∂p0 i) = ∫ x, (x : ℝ) ^ k ∂p1 i
  /-- The second-distribution coordinates match moments across hypotheses. -/
  q_moments_eq : ∀ i k, k ≤ degree →
    (∫ x, (x : ℝ) ^ k ∂q0 i) = ∫ x, (x : ℝ) ^ k ∂q1 i
  /-- The resulting normalized priors and quantitative conclusions. -/
  witness : FuzzyWitness n d
  /-- The lower hypothesis is exactly the normalized coordinate construction. -/
  prior0_eq : witness.prior0 = constructedParameterPrior anchor p0 q0
  /-- The upper hypothesis is exactly the normalized coordinate construction. -/
  prior1_eq : witness.prior1 = constructedParameterPrior anchor p1 q1

/-- The constructed fuzzy priors have separated target centers by at least four
times their concentration radius. -/
theorem MomentMatchedFuzzyConstruction.target_gap {n d : ℕ}
    (C : MomentMatchedFuzzyConstruction n d) :
    4 * C.witness.radius ≤ C.witness.center1 - C.witness.center0 := by
  linarith [C.witness.target_separated]

/-- The constructed fuzzy priors induce observation mixtures within total
variation `1/4`. -/
theorem MomentMatchedFuzzyConstruction.mixtures_close {n d : ℕ}
    (C : MomentMatchedFuzzyConstruction n d) :
    Causalean.Stat.tvDist
      (mixtureObservationLaw n d C.witness.prior0)
      (mixtureObservationLaw n d C.witness.prior1) ≤ 1 / 4 :=
  C.witness.mixture_tv

/-- In the growing-alphabet regime, independent moment-matched scalar priors
can be transferred into two genuine priors on the full pair-parameter space;
their target radius is at least a universal multiple of the square root of
`min(1,d/(n log(e n)))`, while their count mixtures remain close.

Proof route: take degree proportional to `log(e n)` and split coordinates into
the boundary regime, where a one-sided moment prior on `[0,M]` is obtained from
duality for `(|x-a|-a)/x`, and the interior regime, where an affine copy of the
symmetric absolute-value prior suffices.  (The interior prior alone loses the
constant-rate boundary case `n ≍ d/log d`.)  Independent coordinate copies
have matching moments, while Hoeffding bounds control their total masses and
raw `L₁` targets.  Normalize the arrays and use `normalizeWeights_l1_raw`
to transfer separation.  The paper's proof only conditions approximate
probability vectors and then invokes a sample-size bridge; it does not prove
closeness for normalized prior-predictive laws.  The paper-faithful route is
therefore factored through `ApproximateBridge` and may keep the second
distribution fixed; the explicit submodel reduction then returns the result
to the full two-unknown minimax problem. -/
theorem exists_momentMatchedFuzzyConstruction (n d : ℕ)
    (hd : 8 ≤ d)
    (hn : (d : ℝ) /
      (100 * Real.log (Real.exp 1 * (d : ℝ))) ≤ (n : ℝ))
    (hlog : Real.log (Real.exp 1 * (n : ℝ)) ≤
      4 * Real.log (Real.exp 1 * (d : ℝ))) :
    ∃ C : MomentMatchedFuzzyConstruction n d,
      (1 / 1000 : ℝ) * Real.sqrt (largeAlphabetL1Rate n d) ≤
        C.witness.radius := by
  sorry

end CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower
