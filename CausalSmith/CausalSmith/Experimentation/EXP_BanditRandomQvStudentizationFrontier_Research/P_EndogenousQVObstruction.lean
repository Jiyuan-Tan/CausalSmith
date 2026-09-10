/- Explicit endogenous-variance obstruction to self-normalization. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Helpers.Estimator
import Causalean.Mathlib.Probability.BernoulliMeasure

/-! # Endogenous quadratic-variation obstruction -/

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

def endogenousLimit (z w : ℝ) : ℝ :=
  if 0 < z then (2 * z + 4 * w / Real.sqrt 3) / Real.sqrt (28 / 3)
  else (2 * z + 2 * w) / Real.sqrt 8

def standardNormalUnder {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (Z : Ω → ℝ) : Prop :=
  Measurable Z ∧ mu univ = 1 ∧
    ∀ z, (mu {ω | Z ω ≤ z}).toReal = Causalean.Mathlib.stdNormalCDF z
  -- @realizes Z_1(measurable random variable with standard normal CDF)

-- @node: prop:endogenous-qv-self-normalization-obstruction
theorem endogenous_qv_self_normalization_obstruction :
    let Ω := ℕ → (Bool × Bool)
    ∃ (E : ℕ → AdaptiveCausalExperiment Ω Unit 2 1 1)
      (rho D1 D2 hmin B epsilon : ℝ) (hhmin : 0 < hmin) (κ : ℝ → ℝ)
      (C : ∀ n, IPWZContract Ω Unit (E n) (2 * (n + 1)) rho)
      (muL : Measure (ℝ × ℝ)) (Z W : ℝ × ℝ → ℝ),
      (∀ n, (E n).horizon = 2 * (n + 1)) ∧
      (∀ n, IIDFullData (E n) ∧ SequentialRandomization (E n) ∧
        UniformOverlap (E n) epsilon ∧ BoundedScore (E n) B ∧
        SmoothZMap (E n) rho D1 D2 ∧ UniformRootSeparation (E n) κ ∧
        RootInterior (E n) 1 ∧ JacobianNonsingular (E n) hmin) ∧
      (∀ n, (E n).jacobianMap =
        fderiv ℝ (E n).populationMoment (E n).thetaStar) ∧
      (∀ n, (E n).thetaStar 0 = ∫ ω, (E n).potentialOutcome 1 0 ω -
        (E n).potentialOutcome 1 1 ω ∂(E n).law) ∧
      (∀ n, ∀ᵐ ω ∂(E n).law,
        4 ≤ ((2 * (n + 1) : ℕ) : ℝ)⁻¹ *
          qform ((E n).predictableQV (2 * (n + 1)) ω)
          (WithLp.toLp 2 ![1])) ∧
      TendstoInProbability (fun n => (E n).law)
        (fun n ω => (2 * (n + 1) : ℝ)⁻¹ *
          (qform ((E n).realizedQV (2 * (n + 1)) ω) (WithLp.toLp 2 ![1]) -
           qform ((E n).predictableQV (2 * (n + 1)) ω) (WithLp.toLp 2 ![1])))
        (fun _ _ => 0) ∧
      standardNormalUnder muL Z ∧ standardNormalUnder muL W ∧
      IndepFun Z W muL ∧ -- @realizes Z_1(independent of the covariance-regime variable V)
      CDFConverges (fun n => (E n).law)
        (fun n ω => let T := 2 * (n + 1)
          if qform ((E n).realizedQV T ω) (WithLp.toLp 2 ![1]) = 0 then 0 else
            dot (WithLp.toLp 2 ![1]) ((E n).scoreSum T ω) /
              Real.sqrt (qform ((E n).realizedQV T ω) (WithLp.toLp 2 ![1])))
        (fun x => (muL {zw | endogenousLimit (Z zw) (W zw) ≤ x}).toReal) ∧
      CDFConverges (fun n => (E n).law)
        (fun n => realizedQVPivot (2 * (n + 1)) (C n).T_pos
          (WithLp.toLp 2 ![1]) (E n).thetaStar (by simp) (ipwZEstimator (C n))
          (feasibleScore (C n)) (C n).Hhat hmin 2 hhmin (by norm_num))
        (fun x => (muL {zw | endogenousLimit (Z zw) (W zw) ≤ x}).toReal) ∧
      (∫ zw, endogenousLimit (Z zw) (W zw) ∂muL) =
        2 / Real.sqrt (2 * Real.pi) * (Real.sqrt (3 / 28) - 1 / Real.sqrt 8) ∧
      2 / Real.sqrt (2 * Real.pi) * (Real.sqrt (3 / 28) - 1 / Real.sqrt 8) ≠ 0 := by sorry

end

end CausalSmith.Experimentation.BanditRandomQV
