module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockDisjointPaths

/-!
# Arbitrary-start observable disjoint-window covariances

The observable marginal and cross moments are finite mixtures of their generated
path counterparts. Centering at the mixture's past mean and using one common
future anchor preserves the sharp disjoint-window covariance bound.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open Causalean.Mathlib.Probability.FiniteMarkovOscillation
open scoped BigOperators ENNReal

/-- Actual observable window means are mixtures of generated path window means, with the same
arbitrary initial full-state distribution. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the reward symbol](hyp:r), [the history length](hyp:k), and
[the epoch index assumption](hyp:ht), this establishes
[the partial-history importance-weighted score observed segment integral equality paths result](goal). -/
-- @node: phiwScore_observedSegment_integral_eq_paths
lemma phiwScore_observedSegment_integral_eq_paths {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (r k : Nat) (ht : r + k < n) :
    (∫ w, phiwScore k m.Mx.b (m.Mx.E j) w ⟨r + k, ht⟩
      ∂((segmentLaw m hClass.finite_state nu n).map obsProj)) =
      ∑ s, nu s * ∫ path, phiwPathShift (phiwPathReward m j k) r s path
        ∂segmentFrom m n s := by
  have hi : ∀ s, Integrable (fun path ↦ phiwScore k m.Mx.b (m.Mx.E j)
      (obsProj (decodeSegment (n := n)
        (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, path)))
      ⟨r + k, ht⟩) (segmentFrom m n s) := by
    intro s
    have : IsProbabilityMeasure (segmentFrom m n s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 n s
    exact (phiwScore_decodeSegment_memLp t0 zeta C m hClass j _ s r k ht 1).integrable le_rfl
  rw [observedSegment_integral_eq_sum_fixed_start m hClass.finite_state nu hnu _
    (by fun_prop) hi]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_congr_ae (phiwScore_decodeSegment_ae_eq_path_reward m
    hClass.sequential_ignorability.1 j _ s r k ht)]

/-- Observable cross moments, including disjoint windows, are mixtures of the actual
generated-path cross moments. This avoids mixing covariances. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the reward symbol](hyp:r), [the observed prefix](hyp:u), [the history length](hyp:k),
[the reward symbol assumption](hyp:hr), and [the observed prefix assumption](hyp:hu), this
establishes
[the partial-history importance-weighted score observed segment cross integral equality paths result](goal). -/
-- @node: phiwScore_observedSegment_cross_integral_eq_paths
lemma phiwScore_observedSegment_cross_integral_eq_paths {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (r u k : Nat) (hr : r + k < n) (hu : u + k < n) :
    (∫ w, phiwScore k m.Mx.b (m.Mx.E j) w ⟨r + k, hr⟩ *
      phiwScore k m.Mx.b (m.Mx.E j) w ⟨u + k, hu⟩
      ∂((segmentLaw m hClass.finite_state nu n).map obsProj)) =
      ∑ s, nu s * ∫ path, phiwPathShift (phiwPathReward m j k) r s path *
        phiwPathShift (phiwPathReward m j k) u s path ∂segmentFrom m n s := by
  have hi : ∀ s, Integrable (fun path ↦
      phiwScore k m.Mx.b (m.Mx.E j)
        (obsProj (decodeSegment (n := n)
          (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, path))) ⟨r + k, hr⟩ *
      phiwScore k m.Mx.b (m.Mx.E j)
        (obsProj (decodeSegment (n := n)
          (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, path))) ⟨u + k, hu⟩)
      (segmentFrom m n s) := by
    intro s
    exact (phiwScore_decodeSegment_memLp t0 zeta C m hClass j _ s r k hr 2).integrable_mul
      (phiwScore_decodeSegment_memLp t0 zeta C m hClass j _ s u k hu 2)
  rw [observedSegment_integral_eq_sum_fixed_start m hClass.finite_state nu hnu _
    (by fun_prop) hi]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  apply integral_congr_ae
  filter_upwards [phiwScore_decodeSegment_ae_eq_path_reward m
    hClass.sequential_ignorability.1 j _ s r k hr,
    phiwScore_decodeSegment_ae_eq_path_reward m
    hClass.sequential_ignorability.1 j _ s u k hu] with path hx hy
  rw [hx, hy]

/-- A common-anchor bound for each component's centered cross moment gives a covariance bound
under a finite mixture. The past center is the global mean. For [the index subset](hyp:S),
[the sample space](hyp:Ω), [the measure](hyp:μ), [the initial distribution](hyp:nu),
[the initial distribution assumption](hyp:hnu), [the x](hyp:X), [the y](hyp:Y),
[the x assumption](hyp:hX), [the y assumption](hyp:hY), [the ex](hyp:ex), [the ey](hyp:ey),
[the exy](hyp:exy), [the observed state assumption](hyp:hx), [the y assumption](hyp:hy),
[the xy assumption](hyp:hxy), [the c](hyp:c), [the d](hyp:D), and
[the behavior policy assumption](hyp:hb), this establishes
[the partial-history importance-weighted covariance bound of mixed centered moments result](goal). -/
-- @node: phiw_covariance_le_of_mixed_centered_moments
lemma phiw_covariance_le_of_mixed_centered_moments
    {S Ω : Type*} [Fintype S] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (nu : S → ℝ) (hnu : ProbabilityVector nu)
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (ex ey exy : S → ℝ)
    (hx : (∫ ω, X ω ∂μ) = ∑ s, nu s * ex s)
    (hy : (∫ ω, Y ω ∂μ) = ∑ s, nu s * ey s)
    (hxy : (∫ ω, X ω * Y ω ∂μ) = ∑ s, nu s * exy s)
    (c D : ℝ)
    (hb : ∀ s, |exy s - (∫ ω, X ω ∂μ) * ey s - c * ex s +
      (∫ ω, X ω ∂μ) * c| ≤ D) :
    |covariance X Y μ| ≤ D := by
  let a := ∫ ω, X ω ∂μ
  have heq : covariance X Y μ =
      ∑ s, nu s * (exy s - a * ey s - c * ex s + a * c) := by
    rw [covariance_eq_sub hX hY]
    change (∫ ω, X ω * Y ω ∂μ) - a * (∫ ω, Y ω ∂μ) = _
    simp_rw [mul_add, mul_sub]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp_rw [mul_left_comm (nu _) a, mul_left_comm (nu _) c]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, hnu.2, one_mul,
      ← hx, ← hy, ← hxy]
    dsimp [a]
    ring
  rw [heq]
  calc
    _ ≤ ∑ s, |nu s * (exy s - a * ey s - c * ex s + a * c)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, nu s * D := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul, abs_of_nonneg (hnu.1 s)]
      exact mul_le_mul_of_nonneg_left (hb s) (hnu.1 s)
    _ = D := by rw [← Finset.sum_mul, hnu.2, one_mul]

/-- Equation (9) under the observable arbitrary-start segment law. Both window moments are mixed
before centering, so no stationary start is required. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the code dimension](hyp:d), [the history length](hyp:k), [the stated assumption](hyp:h),
[the h assumption](hyp:hh), and [the epoch index assumption](hyp:ht), this establishes
[the partial-history importance-weighted score observed segment disjoint covariance result](goal). -/
-- @node: phiwScore_observedSegment_disjoint_covariance
lemma phiwScore_observedSegment_disjoint_covariance {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (d k h : Nat) (hh : k < h) (ht : d + h + k < n) :
    |covariance (fun w ↦ phiwScore k m.Mx.b (m.Mx.E j) w ⟨d + k, by omega⟩)
      (fun w ↦ phiwScore k m.Mx.b (m.Mx.E j) w ⟨d + h + k, ht⟩)
      ((segmentLaw m hClass.finite_state nu n).map obsProj)| ≤
      2 * mixingAlpha t0 ^ (h - 1) := by
  have : IsProbabilityMeasure ((segmentLaw m hClass.finite_state nu n).map obsProj) :=
    observedSegmentLaw_isProbability m hClass.sequential_ignorability.1
      hClass.finite_state nu hnu n
  let μ := (segmentLaw m hClass.finite_state nu n).map obsProj
  let X := fun w : ObsView n m.nX ↦ phiwScore k m.Mx.b (m.Mx.E j) w ⟨d + k, by omega⟩
  let Y := fun w : ObsView n m.nX ↦ phiwScore k m.Mx.b (m.Mx.E j) w ⟨d + h + k, ht⟩
  let r := h - k - 1
  let s₀ : JointState m.nX m.nH :=
    (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩)
  let c := markovOperatorIter (listPolicyKernel m m.Mx.b) r (phiwChronologicalMean m j k) s₀
  apply phiw_covariance_le_of_mixed_centered_moments μ nu hnu X Y
    (phiwScore_observedSegment_memLp t0 zeta C m hClass j nu hnu d k (by omega) 2)
    (phiwScore_observedSegment_memLp t0 zeta C m hClass j nu hnu (d + h) k ht 2)
    (fun s ↦ ∫ path, phiwPathShift (phiwPathReward m j k) d s path ∂segmentFrom m n s)
    (fun s ↦ ∫ path, phiwPathShift (phiwPathReward m j k) (d + h) s path ∂segmentFrom m n s)
    (fun s ↦ ∫ path, phiwPathShift (phiwPathReward m j k) d s path *
      phiwPathShift (phiwPathReward m j k) (d + h) s path ∂segmentFrom m n s)
    (phiwScore_observedSegment_integral_eq_paths t0 zeta C m hClass j nu hnu d k (by omega))
    (phiwScore_observedSegment_integral_eq_paths t0 zeta C m hClass j nu hnu (d + h) k ht)
    (phiwScore_observedSegment_cross_integral_eq_paths t0 zeta C m hClass j nu hnu
      d (d + h) k (by omega) ht) c
  intro s
  have ha0 : 0 ≤ ∫ w, X w ∂μ := integral_nonneg_of_ae
    (phiwScore_observedSegment_nonneg t0 zeta C m hClass j nu d k (by omega))
  have ha1 : (∫ w, X w ∂μ) ≤ 1 :=
    phiwScore_observedSegment_mean_le_one t0 zeta C m hClass j nu hnu d k (by omega)
  obtain ⟨extra, hn⟩ : ∃ extra, n = d + ((k + 1) + (r + ((k + 1) + extra))) :=
    ⟨n - (d + h + k + 1), by dsimp [r]; omega⟩
  have hb := phiwPathShift_disjoint_centered_cross_bound t0 zeta C m hClass j
    d k r extra s s₀ (∫ w, X w ∂μ) ha0 ha1
  dsimp only at hb
  simpa only [← hn, show k + 1 + r = h by dsimp [r]; omega,
    show k + r = h - 1 by dsimp [r]; omega, c] using hb

end CausalSmith.Stat.PomdpPolicyclassRegret
