module
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.ObservedTransport
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.RiskAlgebra

/-!
# Observed-law collision mean-square risk

This module combines a design-only usable-occupancy estimate with centered
real-mark variance and approximate homogeneity. Its estimator and every
hypothesis are functions of the observed law alone.
-/

public section

namespace Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

open MeasureTheory Causalean.Stat

variable {Ω κ : Type} [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- Centered observed arm-cell residuals bound the collision estimator's
integrated noise by the expected reciprocal usable total, with a constant
depending only on overlap. -/
theorem integral_collision_noise_sq_le {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (epsilon M rho : ℝ)
    (h : ObservedAssumptions μ X A Y center epsilon M rho) :
    (∫ z : Fin n → Ω,
      (collisionEstimator X A Y z - designCenter X A center z) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) ≤
    (16 / (epsilon ^ 2 * (1 - epsilon))) * M ^ 2 *
      ∫ z : Fin n → Ω, inverseUsableGroupTotal X A z
        ∂Measure.pi (fun _ : Fin n => μ) := by
  -- Rewrite noise as Causalean's occupancyWeightedResidual and apply
  -- integral_occupancyWeightedResidual_sq_le_reciprocal directly to h's
  -- measurable maps, L2, centered residual, second moment, and overlap fields.
  have hnoise := integral_occupancyWeightedResidual_sq_le_reciprocal
    (n := n) μ X A Y center M epsilon h.X_measurable h.A_measurable
    h.Y_measurable h.residual_L2 h.residual_centered
    (by simpa only [armCellMass] using h.residual_second_moment)
    h.epsilon_pos h.epsilon_lt_half.le
    (by intro k hk a; exact h.overlap a k hk)
  simpa only [← collision_sub_designCenter_eq_residual, inverseUsableGroupTotal]
    using hnoise

/-- The integrated squared design bias is bounded by homogeneity plus the
probability that no observed cell contains both arms. -/
theorem integral_designCenter_bias_sq_le {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (epsilon M rho : ℝ)
    (h : ObservedAssumptions μ X A Y center epsilon M rho) :
    (∫ z : Fin n → Ω,
      (designCenter X A center z - populationContrast μ X center) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) ≤
    M ^ 2 * (rho ^ 2 + 4 *
      ((Measure.pi (fun _ : Fin n => μ))
        {z | usableTotal X A z = 0}).toReal) := by
  classical
  let ν : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let S : Set (Fin n → Ω) := {z | usableTotal X A z = 0}
  have hS : MeasurableSet S :=
    (measurable_usableGroupTotal X A h.X_measurable h.A_measurable)
      (measurableSet_singleton 0)
  have hleft : Integrable (fun z : Fin n → Ω =>
      (designCenter X A center z - populationContrast μ X center) ^ 2) ν :=
    (designCenter_sub_target_memLp μ X A Y center epsilon M rho h).integrable_sq
  have hright : Integrable (fun z : Fin n → Ω =>
      M ^ 2 * rho ^ 2 + S.indicator (fun _ => 4 * M ^ 2) z) ν :=
    (integrable_const (M ^ 2 * rho ^ 2)).add
      ((integrable_const (4 * M ^ 2)).indicator hS)
  have hpoint : ∀ᵐ z ∂ν,
      (designCenter X A center z - populationContrast μ X center) ^ 2 ≤
        M ^ 2 * rho ^ 2 + S.indicator (fun _ => 4 * M ^ 2) z := by
    filter_upwards [usable_supported_ae μ X A h.X_measurable h.A_measurable n]
      with z hz
    have hb := designCenter_bias_sq_le μ X A Y center epsilon M rho h z hz
    by_cases hz0 : usableTotal X A z = 0
    · simpa [S, Set.indicator, hz0, mul_add, mul_comm] using hb
    · simpa [S, Set.indicator, hz0, mul_add] using hb
  have hbound := integral_mono_ae hleft hright hpoint
  have hright_integral :
      (∫ z : Fin n → Ω,
        M ^ 2 * rho ^ 2 + S.indicator (fun _ => 4 * M ^ 2) z ∂ν) =
        M ^ 2 * (rho ^ 2 + 4 * (ν S).toReal) := by
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hS)]
    rw [integral_const, integral_indicator_const _ hS]
    simp only [smul_eq_mul]
    have hνuniv : ν.real Set.univ = 1 := by
      simp [Measure.real, ν]
    rw [hνuniv]
    simp only [Measure.real]
    ring
  simpa only [ν, S, hright_integral] using hbound

/-- An [overlap margin strictly between zero and one half](hyp:epsilon,hepsilon,hepsilon_half)
gives [a uniform mean-square bound for the collision estimator with parametric,
heterogeneity, and finite-dimension terms](goal) in every finite observed-data
setting satisfying the stated observed-law conditions. -/
theorem observed_collision_mse_le (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2) :
    ∃ C_epsilon : ℝ, 0 < C_epsilon ∧
      ∀ (Ω κ : Type) [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
        [MeasurableSpace κ] [MeasurableSingletonClass κ]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
        (center : Bool → κ → ℝ) (M rho : ℝ) (n : ℕ),
        0 < n → ObservedAssumptions μ X A Y center epsilon M rho →
        (∫ z : Fin n → Ω,
          (collisionEstimator X A Y z - populationContrast μ X center) ^ 2
          ∂Measure.pi (fun _ : Fin n => μ)) ≤
        C_epsilon * M ^ 2 *
          (1 / (n : ℝ) + rho ^ 2 +
            (Fintype.card κ : ℝ) / (n : ℝ) ^ 2) := by
  -- Apply observed_bad_occupancy_rate and
  -- observed_reciprocal_occupancy_rate. Combine integral_collision_noise_sq_le and
  -- integral_designCenter_bias_sq_le with (u+v)^2 ≤ 2u²+2v² and the L2
  -- integrability helpers (`collision_sub_target_memLp`,
  -- `designCenter_sub_target_memLp`, and `occupancyWeightedResidual_memLp_two`).
  -- If Bbad and Brec are the two occupancy constants and
  -- K = 16 / (epsilon^2 * (1-epsilon)), choose
  -- C_epsilon = 2*K*Brec + 8*Bbad + 2. The inequalities
  -- 0 < epsilon < 1/2 give K > 0. Set R = 1/n + card(κ)/n^2;
  -- then 2*K*Brec*R + 2*rho^2 + 8*Bbad*R ≤
  -- C_epsilon * (R + rho^2), since R and rho^2 are nonnegative.
  classical
  obtain ⟨Bbad, hBbad, hbad⟩ :=
    observed_bad_occupancy_rate epsilon hepsilon hepsilon_half
  obtain ⟨Brec, hBrec, hrec⟩ :=
    observed_reciprocal_occupancy_rate epsilon hepsilon hepsilon_half
  let K : ℝ := 16 / (epsilon ^ 2 * (1 - epsilon))
  have hK : 0 < K := by
    dsimp [K]
    apply div_pos (by norm_num)
    exact mul_pos (sq_pos_of_pos hepsilon) (by linarith)
  let C_epsilon : ℝ := 2 * K * Brec + 8 * Bbad + 2
  have hC : 0 < C_epsilon := by
    dsimp [C_epsilon]
    positivity
  refine ⟨C_epsilon, hC, ?_⟩
  intro Ω κ _ _ _ _ _ μ _ X A Y center M rho n hn h
  let ν : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let R : ℝ := 1 / (n : ℝ) + (Fintype.card κ : ℝ) / (n : ℝ) ^ 2
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hoverlap : ∀ a k, 0 < cellMass μ X k →
      epsilon * cellMass μ X k ≤ armCellMass μ X A a k := by
    intro a k hk
    exact h.overlap a k hk
  have hbad' : (ν {z | usableTotal X A z = 0}).toReal ≤ Bbad * R := by
    exact hbad Ω κ μ X A n h.X_measurable h.A_measurable hn hoverlap
  have hrec' : (∫ z : Fin n → Ω, inverseUsableGroupTotal X A z ∂ν) ≤
      Brec * R := by
    exact hrec Ω κ μ X A n h.X_measurable h.A_measurable hn hoverlap
  have hnoiseLp : MemLp (fun z : Fin n → Ω =>
      collisionEstimator X A Y z - designCenter X A center z) 2 ν := by
    convert (collision_sub_target_memLp (n := n) μ X A Y center epsilon M rho h).sub
      (designCenter_sub_target_memLp (n := n) μ X A Y center epsilon M rho h)
      using 1
    funext z
    dsimp
    ring
  have hnoiseInt : Integrable (fun z : Fin n → Ω =>
      (collisionEstimator X A Y z - designCenter X A center z) ^ 2) ν :=
    hnoiseLp.integrable_sq
  have hbiasInt : Integrable (fun z : Fin n → Ω =>
      (designCenter X A center z - populationContrast μ X center) ^ 2) ν :=
    (designCenter_sub_target_memLp (n := n) μ X A Y center epsilon M rho h).integrable_sq
  have htargetInt : Integrable (fun z : Fin n → Ω =>
      (collisionEstimator X A Y z - populationContrast μ X center) ^ 2) ν :=
    (collision_sub_target_memLp (n := n) μ X A Y center epsilon M rho h).integrable_sq
  have hsplit :
      (∫ z : Fin n → Ω,
        (collisionEstimator X A Y z - populationContrast μ X center) ^ 2 ∂ν) ≤
      2 * (∫ z : Fin n → Ω,
        (collisionEstimator X A Y z - designCenter X A center z) ^ 2 ∂ν) +
      2 * (∫ z : Fin n → Ω,
        (designCenter X A center z - populationContrast μ X center) ^ 2 ∂ν) := by
    have hpoint : ∀ z : Fin n → Ω,
        (collisionEstimator X A Y z - populationContrast μ X center) ^ 2 ≤
        2 * (collisionEstimator X A Y z - designCenter X A center z) ^ 2 +
        2 * (designCenter X A center z - populationContrast μ X center) ^ 2 := by
      intro z
      calc
        _ = ((collisionEstimator X A Y z - designCenter X A center z) +
            (designCenter X A center z - populationContrast μ X center)) ^ 2 := by ring
        _ ≤ 2 * ((collisionEstimator X A Y z - designCenter X A center z) ^ 2 +
            (designCenter X A center z - populationContrast μ X center) ^ 2) := add_sq_le
        _ = _ := by ring
    have hright : Integrable (fun z : Fin n → Ω =>
        2 * (collisionEstimator X A Y z - designCenter X A center z) ^ 2 +
        2 * (designCenter X A center z - populationContrast μ X center) ^ 2) ν :=
      (hnoiseInt.const_mul 2).add (hbiasInt.const_mul 2)
    have hmono := integral_mono htargetInt hright hpoint
    rw [integral_add (hnoiseInt.const_mul 2) (hbiasInt.const_mul 2),
      integral_const_mul, integral_const_mul] at hmono
    exact hmono
  have hnoise := integral_collision_noise_sq_le (n := n)
    μ X A Y center epsilon M rho h
  have hbias := integral_designCenter_bias_sq_le (n := n)
    μ X A Y center epsilon M rho h
  have hbound :
      (∫ z : Fin n → Ω,
        (collisionEstimator X A Y z - populationContrast μ X center) ^ 2 ∂ν) ≤
        M ^ 2 * (2 * K * Brec * R + 2 * rho ^ 2 + 8 * Bbad * R) := by
    calc
      _ ≤ 2 * (∫ z : Fin n → Ω,
            (collisionEstimator X A Y z - designCenter X A center z) ^ 2 ∂ν) +
          2 * (∫ z : Fin n → Ω,
            (designCenter X A center z - populationContrast μ X center) ^ 2 ∂ν) := hsplit
      _ ≤ 2 * (K * M ^ 2 * (∫ z : Fin n → Ω,
            inverseUsableGroupTotal X A z ∂ν)) +
          2 * (M ^ 2 * (rho ^ 2 + 4 * (ν {z | usableTotal X A z = 0}).toReal)) := by
            gcongr
      _ ≤ 2 * (K * M ^ 2 * (Brec * R)) +
          2 * (M ^ 2 * (rho ^ 2 + 4 * (Bbad * R))) := by
            gcongr
      _ = M ^ 2 * (2 * K * Brec * R + 2 * rho ^ 2 + 8 * Bbad * R) := by ring
  have hscalar : 2 * K * Brec * R + 2 * rho ^ 2 + 8 * Bbad * R ≤
      C_epsilon * (1 / (n : ℝ) + rho ^ 2 +
        (Fintype.card κ : ℝ) / (n : ℝ) ^ 2) := by
    have hcoef : 0 ≤ 2 * K * Brec + 8 * Bbad := by positivity
    dsimp [C_epsilon, R] at *
    nlinarith [mul_nonneg hcoef (sq_nonneg rho)]
  calc
    _ ≤ M ^ 2 * (2 * K * Brec * R + 2 * rho ^ 2 + 8 * Bbad * R) := hbound
    _ ≤ M ^ 2 * (C_epsilon * (1 / (n : ℝ) + rho ^ 2 +
        (Fintype.card κ : ℝ) / (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hscalar hM2
    _ = _ := by ring

end Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk
