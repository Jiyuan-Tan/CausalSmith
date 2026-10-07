module
public import Causalean.Mathlib.Analysis.SharpFunctionalCalculus
public import Causalean.Stat.Coupling.AtomicSpectralLaw.Basic

/-!
# One-Wasserstein stability of spectrally represented atomic laws, with a √n dimension factor

Two finite atomic probability laws on the real line are each represented through a real
diagonalizable `n × n` matrix and a pair of anchor vectors, in the sense that the expectation of
every 1-Lipschitz test function vanishing at zero equals the anchored evaluation of that function
of the matrix. Their one-Wasserstein distance is then bounded by the perturbations of the anchors
and of the matrices, with no eigenvalue-gap assumption:

    W₁(μ, ν) ≤ ‖a − b‖ κA R ‖c‖ + ‖b‖ √n κA κB ‖A − B‖ ‖c‖ + ‖b‖ κB R ‖c − d‖,

where `κA`, `κB` bound the condition numbers of the two diagonalizations and `R` bounds the
absolute values of all their eigenvalues.

## Main result

* `atomicW1_le_operator_anchor_perturbation_sqrt_dim` — the bound above. It sharpens the factor
  `n²` of `atomicW1_le_operator_anchor_perturbation` to `√n`; optimality of `√n` is not proved.
-/

public section

namespace Causalean.Stat.Coupling.AtomicSpectralLaw

open Causalean.Mathlib.Analysis
open scoped Matrix.Norms.L2Operator

/-- [Finite slot types](hyp:ι,κ), [a matrix dimension and two real matrices](hyp:n,A,B), [their real diagonalizations](hyp:DA,DB), [left and right anchor vectors](hyp:a,b,c,d), [finite atomic laws with valid probability weights](hyp:μ,ν,hμ,hν), [their anchored functional-calculus representations](hyp:hrepA,hrepB), [condition-number bounds](hyp:κA,κB,hκA,hκB), and [a nonnegative common spectral envelope](hyp:R,hR0,hRA,hRB) give [the square-root-dimensional collision-safe one-Wasserstein bound: the one-Wasserstein distance between the two laws is at most ‖a − b‖·κA·R·‖c‖ + ‖b‖·√n·κA·κB·‖A − B‖·‖c‖ + ‖b‖·κB·R·‖c − d‖](goal).

The condition number of a diagonalization is the product of the operator norms of its eigenvector
matrix and of that matrix's inverse, and the spectral envelope `R` bounds the absolute value of
every eigenvalue of both diagonalizations; ‖A − B‖ is the spectral operator norm. -/
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

end Causalean.Stat.Coupling.AtomicSpectralLaw
