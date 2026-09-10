import CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicWasserstein
import CausalSmith.Substrate.CollisionSafeSpectralLaw.FunctionalCalculus

/-!
# Collision-safe operator-to-law composition

This module composes the two-diagonalizer functional-calculus estimate with attained finite-atomic
Kantorovich--Rubinstein duality.  Its public theorem is entirely model-independent: a consumer only
supplies positive normalized atomic laws whose Lipschitz tests are represented by left-right
functional-calculus evaluations.
-/

namespace CausalSmith.Substrate.CollisionSafeSpectralLaw

open scoped Matrix.Norms.L2Operator

/-- A finite atomic law is represented by an anchored diagonalizable operator when every
one-Lipschitz test normalized at zero equals the corresponding left-right functional-calculus
evaluation. -/
def RepresentsAtomicLaw {ι : Type*} [Fintype ι] {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) (a c : Euc n) (μ : AtomicLaw ι) : Prop :=
  ∀ f : ℝ → ℝ, LipschitzWith 1 f → f 0 = 0 →
    μ.integral f = anchorEval a c (D.applyFunction f)

/-- Positive finite atomic laws represented by bounded anchored functional calculus satisfy a
uniform one-Wasserstein bound through arbitrary eigenvalue collisions.  The bound uses separate
diagonalizer condition numbers and only operator and anchor perturbations. -/
theorem atomicW1_le_operator_anchor_perturbation
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B)
    (a b c d : Euc n) (μ : AtomicLaw ι) (ν : AtomicLaw κ)
    (hμ : μ.Valid) (hν : ν.Valid)
    (hrepA : RepresentsAtomicLaw DA a c μ)
    (hrepB : RepresentsAtomicLaw DB b d ν)
    {κA κB R : ℝ} (hκA : DA.conditionNumber ≤ κA)
    (hκB : DB.conditionNumber ≤ κB)
    (hR0 : 0 ≤ R) (hRA : DA.SpectrumBound R) (hRB : DB.SpectrumBound R) :
    AtomicLaw.w1 μ ν ≤
      ‖a - b‖ * (κA * R) * ‖c‖ +
      ‖b‖ * ((n : ℝ) ^ 2 * κA * κB * ‖A - B‖) * ‖c‖ +
      ‖b‖ * (κB * R) * ‖c - d‖ := by
  /- Use the attained `krPotential`, which is already one-Lipschitz and normalized at zero.
  Rewrite both expectations with `hrepA` and `hrepB`, then apply
  `abs_anchorEval_applyFunction_sub_le`; the attainment equality avoids having to normalize an
  arbitrary dual test function. -/
  obtain ⟨hf, hatt⟩ := AtomicLaw.krPotential_attains μ ν hμ hν
  rw [hatt, hrepA _ hf (AtomicLaw.krPotential_zero μ ν),
    hrepB _ hf (AtomicLaw.krPotential_zero μ ν)]
  exact abs_anchorEval_applyFunction_sub_le DA DB a b c d _ hf
    (AtomicLaw.krPotential_zero μ ν) hκA hκB hR0 hRA hRB

end CausalSmith.Substrate.CollisionSafeSpectralLaw
