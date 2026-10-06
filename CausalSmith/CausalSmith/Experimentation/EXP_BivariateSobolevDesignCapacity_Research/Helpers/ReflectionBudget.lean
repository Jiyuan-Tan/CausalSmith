module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionPooledBudget
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionPlaneParseval
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionEndpointLimit
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionGradientLimit
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionTargetInterpolation

/-! # Exact pooled reflection budget

The component contraction and pooled ANOVA bound for the even reflected extension.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

-- @node: lem:exact-reflection-budget
/-- [ Exact component reflection contraction and its pooled ANOVA consequences.
Parseval and interpolation have proved witnesses; no periodic cube boundary condition is assumed. This uses [the stated conclusion](goal). -/
lemma exact_reflection_budget :
    (∀ (p : ℕ), p = 1 ∨ p = 2 → ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∀ g : Cube p → ℝ, Measurable g → MemLp g 2 (cubeMeasure p) →
        sobolevNormSq p s g < ⊤ → componentFourierBudget p s g ≤ sobolevNormSq p s g) ∧
    (∀ (d : ℕ) (s : ℝ), 2 ≤ d → 0 < s → s ≤ 1 →
      ∀ m : CenteredL2Fn d, SobolevClass d s m →
        Fhat m.val 0 = 0 ∧
        (∀ k, 2 < (frequencySupport k).card → Fhat m.val k = 0) ∧
        reflectedBudget s m.val ≤ 1 ∧
        (∫ x, |m.val x| ^ 2 ∂cubeMeasure d) ≤ 1) := by
  -- The zero-order endpoint is proved in ReflectionEndpointZero.
  -- ReflectionWeakDerivative proves the one-dimensional smooth first-order endpoint.
  -- ReflectionPlaneParseval assembles joint Parseval and the two derivative multipliers
  -- into the smooth two-dimensional spectral endpoint, with exact gradient factor 1/2.
  -- ReflectionTruncation constructs the smooth inverse integrals, proves all their
  -- frequency moments integrable, and proves exact weighted frequency convergence.
  -- ReflectionInverseL2 proves spatial L² membership, exact energy/distance identities,
  -- and existence of the spatial L² limit of the smooth inverse truncations.
  -- ReflectionInversePairing proves Fubini and exact adjoint pairing for these
  -- inverse integrals, and their a.e. agreement with the normalized, reflected
  -- Mathlib Fourier L² representatives.
  -- ReflectionInverseLimit identifies the completeness limit as the explicit normalized,
  -- reflected Mathlib Fourier L² representative for any measurable L² frequency profile.
  -- Adjoint pairing and Plancherel now identify the inverse representative of an
  -- admissible extension's angular profile with that original extension in L².
  -- ReflectionSmoothDerivative differentiates the smooth inverse integrals on every
  -- coordinate slice and proves their exact first-order spatial energy identity,
  -- coordinate-energy identities for differences, and the spectral truncation bound.
  -- ReflectionGradientLimit derives full coordinate-profile L² regularity from finite
  -- first-order energy, identifies all actual smooth derivative limits, proves their
  -- exact limiting energy, and proves convergence of the whole first-order error.
  -- ReflectionSmoothEndpoint applies the slice and plane spectral estimates to
  -- the genuine inverse truncations. It completes the one-dimensional endpoint
  -- in the actual reflection operator and takes the extension infimum in both
  -- dimensions. Joint Haar-coordinate identification and spatial L² convergence
  -- now complete the two-dimensional endpoint with exact gradient factor 1/2.
  -- ReflectionProfileEndpoint constructs the common frequency-to-torus operator
  -- on complete L² classes, proves both genuine endpoint gauge contractions,
  -- and applies normalized K-method interpolation with constant exactly one.
  -- ReflectionTargetInterpolation transports the periodic endpoint gauges through
  -- Fourier coefficients, applies exact weighted interpolation, and takes the
  -- extension infimum. The component contraction is now complete for every s.
  -- ReflectionANOVA derives canonical component L² regularity, main-effect centering,
  -- coordinate-local Fourier supports, and exact coefficient additivity.
  -- ReflectionANOVACentering proves pair centering in each coordinate, exact component
  -- supports, and identification of each ambient coefficient with its unique component.
  -- ReflectionCoefficientTransport identifies local and ambient coefficients and
  -- their exact local-dimension weights. ReflectionPooledBudget sums the disjoint
  -- canonical supports and applies the constant-one component contractions.
  refine ⟨?_, ?_⟩
  · intro p hp s hs hs1 g hg hLp hfinite
    exact componentFourierBudget_le_sobolevNormSq p hp s hs hs1 g
  · intro d s hd hs hs1 m hm
    have hsupport := Fhat_zero_of_orderTwo_from_components m hm.orderTwo
    have hbudget := reflectedBudget_le_one_of_sobolevClass hs hs1 m hm
    exact ⟨Fhat_zero_of_centered m, hsupport, hbudget,
      cube_second_moment_le_of_reflectedBudget (by omega) hs.le m hsupport hbudget⟩

/-- The pooled reflection estimate controls the original-cube second moment.](goal) Under [the stated conditions](hyp:hd,hs,hs1,hm). This uses [the stated conclusion](goal). -/
-- @node: sobolev_cube_second_moment_le_one
lemma sobolev_cube_second_moment_le_one
    {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs : 0 < s) (hs1 : s ≤ 1)
    (m : CenteredL2Fn d) (hm : SobolevClass d s m) :
    (∫ x, m.val x ^ 2 ∂cubeMeasure d) ≤ 1 := by
  have h := (exact_reflection_budget).2 d s hd hs hs1 m hm
  simpa only [sq_abs] using h.2.2.2

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
