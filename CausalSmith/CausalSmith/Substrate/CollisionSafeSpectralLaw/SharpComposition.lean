import CausalSmith.Substrate.CollisionSafeSpectralLaw.Composition
import CausalSmith.Substrate.CollisionSafeSpectralLaw.SharpFunctionalCalculus

/-! # Sharp collision-safe operator-to-law composition -/

namespace CausalSmith.Substrate.CollisionSafeSpectralLaw

open scoped Matrix.Norms.L2Operator

/-- Finite-atomic Kantorovich--Rubinstein composition using the sharp square-root-dimensional
two-diagonalizer functional-calculus estimate. -/
theorem atomicW1_le_operator_anchor_perturbation_sqrt_dim
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
      ‖b‖ * (Real.sqrt n * κA * κB * ‖A - B‖) * ‖c‖ +
      ‖b‖ * (κB * R) * ‖c - d‖ := by
  obtain ⟨hf, hatt⟩ := AtomicLaw.krPotential_attains μ ν hμ hν
  rw [hatt, hrepA _ hf (AtomicLaw.krPotential_zero μ ν),
    hrepB _ hf (AtomicLaw.krPotential_zero μ ν)]
  exact abs_anchorEval_applyFunction_sub_le_sqrt_dim DA DB a b c d _ hf
    (AtomicLaw.krPotential_zero μ ν) hκA hκB hR0 hRA hRB

end CausalSmith.Substrate.CollisionSafeSpectralLaw
