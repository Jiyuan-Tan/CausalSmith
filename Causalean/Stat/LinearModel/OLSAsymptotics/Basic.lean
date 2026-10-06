/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.CLT.VectorWLLN
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Topology.Instances.Matrix

/-! # Population and sample objects for heteroskedastic OLS

This module defines the projection coefficient, the ordinary least-squares
estimator with a totalized inverse, the heteroskedastic sandwich covariance,
and the HC0/HC1 estimators.  A single finite raw-moment vector records every
monomial of degree at most four needed by the consistency proofs.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Matrix

noncomputable section

/-- For [a finite regressor-coordinate type](hyp:K), the [augmented OLS
coordinate type](goal) contains a constant coordinate, the outcome coordinate,
and every regressor coordinate. -/
abbrev OLSAugIndex (K : Type*) := Option (Option K)

/-- For [a finite regressor-coordinate type](hyp:K), an [OLS raw-moment
index](goal) selects four augmented coordinates whose product is averaged. -/
abbrev OLSMomentIndex (K : Type*) := Fin 4 → OLSAugIndex K

/-- For [a finite regressor-coordinate type](hyp:K), the [OLS raw-moment
space](goal) assigns a real number to every four-coordinate monomial. -/
abbrev OLSMoment (K : Type*) := OLSMomentIndex K → ℝ

/-- Given [a regressor](hyp:x), [an outcome](hyp:y) and [an observation](hyp:z),
the [augmented OLS coordinate](goal) is
one for `none`, the outcome for `some none`, and the selected regressor for
`some (some i)`. -/
def olsAugmented {X K : Type*} (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (z : X) : OLSAugIndex K → ℝ
  | none => 1
  | some none => y z
  | some (some i) => x z i

/-- Given [four augmented coordinates](hyp:a,b,c,d), the [corresponding raw
moment index](goal) places them in slots zero through three. -/
def olsMomentIndex {K : Type*} (a b c d : OLSAugIndex K) : OLSMomentIndex K
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d

/-- Given [a regressor](hyp:x), [an outcome](hyp:y), and [an
observation](hyp:z), the [raw OLS moment vector](goal) contains every product
of four augmented coordinates, with constant coordinates representing lower
degree monomials. -/
def olsRawMoment {X K : Type*} [Fintype K]
    (x : X → EuclideanSpace ℝ K) (y : X → ℝ) (z : X) : OLSMoment K :=
  fun a => ∏ t : Fin 4, olsAugmented x y z (a t)

/-- Given [a population law](hyp:P), [a regressor](hyp:x), and [an
outcome](hyp:y), the [population OLS raw moments](goal) are the expectations
of all degree-at-most-four augmented monomials. -/
def olsPopulationMoments {X K : Type*} [MeasurableSpace X] [Fintype K]
    (P : Measure X) (x : X → EuclideanSpace ℝ K) (y : X → ℝ) : OLSMoment K :=
  ∫ z, olsRawMoment x y z ∂P

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), [an outcome](hyp:y), and [a sample size](hyp:n), the [empirical OLS raw moments](goal) are the
averages of all degree-at-most-four augmented monomials. -/
def olsEmpiricalMoments {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Fintype K] {μ : Measure Ω} {P : Measure X}
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (n : ℕ) : Ω → OLSMoment K :=
  S.sampleMeanVec (olsRawMoment x y) n

/-- Given [a raw-moment vector](hyp:M), the [design second-moment
matrix](goal) extracts the `xᵢxⱼ` coordinates. -/
def olsQFromMoments {K : Type*} (M : OLSMoment K) : Matrix K K ℝ :=
  fun i j => M (olsMomentIndex (some (some i)) (some (some j)) none none)

/-- Given [a raw-moment vector](hyp:M), the [regressor-outcome cross
moment](goal) extracts the `xᵢy` coordinates. -/
def olsRFromMoments {K : Type*} (M : OLSMoment K) : K → ℝ :=
  fun i => M (olsMomentIndex (some (some i)) (some none) none none)

/-- Given [a raw-moment vector](hyp:M), the [OLS coefficient](goal) is the
ordinary inverse of its design moment matrix applied to its regressor-outcome
moment, with the ordinary matrix-inverse convention off invertibility. -/
def olsBetaFromMoments {K : Type*} [Fintype K] [DecidableEq K]
    (M : OLSMoment K) : EuclideanSpace ℝ K :=
  (olsQFromMoments M)⁻¹.toEuclideanLin (WithLp.toLp 2 (olsRFromMoments M))

/-- Given [a population law](hyp:P), [a regressor](hyp:x), and [an
outcome](hyp:y), the [population design moment matrix](goal) is `E[xx′]`. -/
def olsQ {X K : Type*} [MeasurableSpace X] [Fintype K]
    (P : Measure X) (x : X → EuclideanSpace ℝ K) (y : X → ℝ) : Matrix K K ℝ :=
  olsQFromMoments (olsPopulationMoments P x y)

/-- Given [a population law](hyp:P), [a regressor](hyp:x), and [an
outcome](hyp:y), the [population projection coefficient](goal) is
`E[xx′]⁻¹E[xy]`. -/
def olsBeta {X K : Type*} [MeasurableSpace X] [Fintype K] [DecidableEq K]
    (P : Measure X) (x : X → EuclideanSpace ℝ K) (y : X → ℝ) :
    EuclideanSpace ℝ K :=
  olsBetaFromMoments (olsPopulationMoments P x y)

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), [an outcome](hyp:y), and [a sample size](hyp:n), the [empirical design moment matrix](goal) is the
average `n⁻¹Σxᵢxᵢ′`. -/
def olsQHat {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Fintype K] {μ : Measure Ω} {P : Measure X}
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (n : ℕ) : Ω → Matrix K K ℝ :=
  fun ω => olsQFromMoments (olsEmpiricalMoments S x y n ω)

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), [an outcome](hyp:y), and [a sample size](hyp:n), the [empirical regressor-outcome moment](goal) is
the average `n⁻¹Σxᵢyᵢ`. -/
def olsRHat {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Fintype K] {μ : Measure Ω} {P : Measure X}
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (n : ℕ) : Ω → K → ℝ :=
  fun ω => olsRFromMoments (olsEmpiricalMoments S x y n ω)

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), [an outcome](hyp:y),
[a sample size](hyp:n), [a sample outcome](hyp:ω), and [two regressor
coordinates](hyp:i,j), [the corresponding empirical Gram entry is the raw
average `n⁻¹Σₜ xₜᵢxₜⱼ`](goal). -/
theorem olsQHat_apply {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Fintype K] {μ : Measure Ω} {P : Measure X}
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (n : ℕ) (ω : Ω) (i j : K) :
    olsQHat S x y n ω i j =
      (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, x (S.Z t ω) i * x (S.Z t ω) j := by
  simp [olsQHat, olsQFromMoments, olsEmpiricalMoments, IIDSample.sampleMeanVec,
    olsRawMoment, Fin.prod_univ_four, olsMomentIndex, olsAugmented, smul_eq_mul]

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), [an outcome](hyp:y),
[a sample size](hyp:n), [a sample outcome](hyp:ω), and [a regressor
coordinate](hyp:i), [the corresponding empirical regressor-outcome moment is
the raw average `n⁻¹Σₜ xₜᵢyₜ`](goal). -/
theorem olsRHat_apply {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Fintype K] {μ : Measure Ω} {P : Measure X}
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (n : ℕ) (ω : Ω) (i : K) :
    olsRHat S x y n ω i =
      (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, x (S.Z t ω) i * y (S.Z t ω) := by
  simp [olsRHat, olsRFromMoments, olsEmpiricalMoments, IIDSample.sampleMeanVec,
    olsRawMoment, Fin.prod_univ_four, olsMomentIndex, olsAugmented, smul_eq_mul]

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), and [an outcome](hyp:y),
the [ordinary least-squares estimator at each sample size](goal) is
`Q̂⁻¹(n⁻¹Σxᵢyᵢ)`, using the ordinary matrix-inverse convention when `Q̂` is
singular. -/
def olsBetaHat {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Fintype K] [DecidableEq K] {μ : Measure Ω} {P : Measure X}
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ) :
    ℕ → Ω → EuclideanSpace ℝ K :=
  fun n ω => olsBetaFromMoments (olsEmpiricalMoments S x y n ω)

/-- Given [a regressor](hyp:x), [an outcome](hyp:y), [a coefficient
vector](hyp:b), and [an observation](hyp:z), the [linear-projection
residual](goal) is `y-x′b`. -/
def olsResidual {X K : Type*} [Fintype K]
    (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (b : EuclideanSpace ℝ K) (z : X) : ℝ :=
  y z - ∑ i, x z i * b i

/-- Given [raw moments](hyp:M) and [a coefficient vector](hyp:b), the
[heteroskedastic meat matrix](goal) is the polynomial expansion of
`E[xx′(y-x′b)²]`. -/
def olsMeatFromMoments {K : Type*} [Fintype K]
    (M : OLSMoment K) (b : EuclideanSpace ℝ K) : Matrix K K ℝ :=
  fun i j =>
    M (olsMomentIndex (some (some i)) (some (some j)) (some none) (some none))
      - 2 * ∑ l, b l *
        M (olsMomentIndex (some (some i)) (some (some j)) (some none) (some (some l)))
      + ∑ l, ∑ m, b l * b m *
        M (olsMomentIndex (some (some i)) (some (some j))
          (some (some l)) (some (some m)))

/-- Given [a population law](hyp:P), [a regressor](hyp:x), and [an
outcome](hyp:y), the [heteroskedastic score second-moment matrix](goal) is
`Ω = E[xx′e²]` at the population projection coefficient. -/
def olsOmega {X K : Type*} [MeasurableSpace X] [Fintype K] [DecidableEq K]
    (P : Measure X) (x : X → EuclideanSpace ℝ K) (y : X → ℝ) : Matrix K K ℝ :=
  olsMeatFromMoments (olsPopulationMoments P x y) (olsBeta P x y)

/-- Given [a population law](hyp:P), [a regressor](hyp:x), and [an
outcome](hyp:y), the [heteroskedastic OLS asymptotic covariance](goal) is the
sandwich `V = Q⁻¹ΩQ⁻¹`. -/
def olsAsymptoticCovariance {X K : Type*} [MeasurableSpace X] [Fintype K]
    [DecidableEq K] (P : Measure X) (x : X → EuclideanSpace ℝ K) (y : X → ℝ) :
    Matrix K K ℝ :=
  (olsQ P x y)⁻¹ * olsOmega P x y * (olsQ P x y)⁻¹

/-- Given [a square matrix](hyp:V) and [a contrast vector](hyp:c), the
[variance of that linear contrast](goal) is the quadratic form `c′Vc`. -/
def olsContrastVariance {K : Type*} [Fintype K]
    (V : Matrix K K ℝ) (c : EuclideanSpace ℝ K) : ℝ :=
  ∑ i, ∑ j, c i * V i j * c j

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), [an outcome](hyp:y),
[a sample size](hyp:n), and [a sample outcome](hyp:ω), the [direct HC0 meat
matrix](goal) is `n⁻¹Σxᵢxᵢ′êᵢ²`, where the residuals use the sample OLS
coefficient. -/
def olsHC0MeatDirect {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Fintype K] [DecidableEq K] {μ : Measure Ω} {P : Measure X}
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (n : ℕ) (ω : Ω) : Matrix K K ℝ :=
  fun i j => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
    x (S.Z t ω) i * x (S.Z t ω) j *
      olsResidual x y (olsBetaHat S x y n ω) (S.Z t ω) ^ 2

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), [an outcome](hyp:y),
[a sample size](hyp:n), and [a sample outcome](hyp:ω), the [HC0 meat
matrix](goal) is the raw-moment polynomial expansion of
`n⁻¹Σxᵢxᵢ′êᵢ²`. -/
def olsHC0Meat {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Fintype K] [DecidableEq K] {μ : Measure Ω} {P : Measure X}
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (n : ℕ) (ω : Ω) : Matrix K K ℝ :=
  olsMeatFromMoments (olsEmpiricalMoments S x y n ω) (olsBetaHat S x y n ω)

private theorem ols_cross_sum {K : Type*} [Fintype K]
    (A : ℕ → ℝ) (U : ℕ → K → ℝ) (b : K → ℝ) (n : ℕ) :
    (∑ l, b l * ∑ t ∈ Finset.range n, A t * U t l) =
      ∑ t ∈ Finset.range n, A t * ∑ l, U t l * b l := by
  calc
    _ = ∑ l, ∑ t ∈ Finset.range n, b l * (A t * U t l) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
    _ = ∑ t ∈ Finset.range n, ∑ l, b l * (A t * U t l) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

private theorem ols_quad_sum {K : Type*} [Fintype K]
    (A : ℕ → ℝ) (U : ℕ → K → ℝ) (b : K → ℝ) (n : ℕ) :
    (∑ l, ∑ m, b l * b m * ∑ t ∈ Finset.range n, A t * U t l * U t m) =
      ∑ t ∈ Finset.range n, A t * (∑ l, U t l * b l) ^ 2 := by
  calc
    _ = ∑ l, ∑ m, ∑ t ∈ Finset.range n,
        b l * b m * (A t * U t l * U t m) := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
    _ = ∑ l, ∑ t ∈ Finset.range n, ∑ m,
        b l * b m * (A t * U t l * U t m) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_comm]
    _ = ∑ t ∈ Finset.range n, ∑ l, ∑ m,
        b l * b m * (A t * U t l * U t m) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      have hsq : (∑ l, U t l * b l) ^ 2 =
          ∑ l, ∑ m, (U t l * b l) * (U t m * b m) := by
        rw [pow_two, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum]
      rw [hsq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), [an outcome](hyp:y),
[a sample size](hyp:n), and [a sample outcome](hyp:ω), the [raw-moment HC0
meat equals the textbook residual sum `n⁻¹Σxᵢxᵢ′êᵢ²`](goal). -/
theorem olsHC0Meat_eq_direct {Ω X K : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [Fintype K] [DecidableEq K] {μ : Measure Ω}
    {P : Measure X} (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K)
    (y : X → ℝ) (n : ℕ) (ω : Ω) :
    olsHC0Meat S x y n ω = olsHC0MeatDirect S x y n ω := by
  ext i j
  simp [olsHC0Meat, olsHC0MeatDirect, olsMeatFromMoments,
    olsEmpiricalMoments, IIDSample.sampleMeanVec, olsRawMoment,
    Fin.prod_univ_four, olsMomentIndex, olsAugmented, olsResidual,
    smul_eq_mul]
  rw [show 2 * (∑ l,
      (olsBetaHat S x y n ω) l * ((n : ℝ)⁻¹ *
        ∑ t ∈ Finset.range n, x (S.Z t ω) i * x (S.Z t ω) j *
          y (S.Z t ω) * x (S.Z t ω) l)) =
      2 * (n : ℝ)⁻¹ *
        ∑ t ∈ Finset.range n, (x (S.Z t ω) i * x (S.Z t ω) j * y (S.Z t ω)) *
          ∑ l, x (S.Z t ω) l * (olsBetaHat S x y n ω) l by
    calc
      _ = 2 * (n : ℝ)⁻¹ * ∑ l, (olsBetaHat S x y n ω) l *
          ∑ t ∈ Finset.range n, (x (S.Z t ω) i * x (S.Z t ω) j * y (S.Z t ω)) *
            x (S.Z t ω) l := by
        repeat rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [ols_cross_sum]]
  rw [show (∑ l, ∑ m,
      (olsBetaHat S x y n ω) l * (olsBetaHat S x y n ω) m *
        ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, x (S.Z t ω) i * x (S.Z t ω) j *
          x (S.Z t ω) l * x (S.Z t ω) m)) =
      (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        (x (S.Z t ω) i * x (S.Z t ω) j) *
          (∑ l, x (S.Z t ω) l * (olsBetaHat S x y n ω) l) ^ 2 by
    calc
      _ = (n : ℝ)⁻¹ * ∑ l, ∑ m,
          (olsBetaHat S x y n ω) l * (olsBetaHat S x y n ω) m *
            ∑ t ∈ Finset.range n, (x (S.Z t ω) i * x (S.Z t ω) j) *
              x (S.Z t ω) l * x (S.Z t ω) m := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
      _ = _ := by rw [ols_quad_sum]]
  repeat rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), and [an outcome](hyp:y),
the [HC0 covariance estimator at each sample size](goal) is the sample sandwich
`Q̂⁻¹(n⁻¹Σxx′ê²)Q̂⁻¹`. -/
def olsHC0 {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Fintype K] [DecidableEq K] {μ : Measure Ω} {P : Measure X}
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ) :
    ℕ → Ω → Matrix K K ℝ :=
  fun n ω => (olsQHat S x y n ω)⁻¹ * olsHC0Meat S x y n ω *
    (olsQHat S x y n ω)⁻¹

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), and [an outcome](hyp:y),
the [HC1 covariance estimator at each sample size](goal) multiplies HC0 by
`n/(n-k)`, with ordinary real division providing a total convention at small
sample sizes. -/
def olsHC1 {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Fintype K] [DecidableEq K] {μ : Measure Ω} {P : Measure X}
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ) :
    ℕ → Ω → Matrix K K ℝ :=
  fun n ω => ((n : ℝ) / ((n : ℝ) - Fintype.card K)) • olsHC0 S x y n ω

/-- Given [a regressor](hyp:x), [an outcome](hyp:y), [a coefficient
vector](hyp:b), and [an observation](hyp:z), the [OLS score](goal) is `x(y-x′b)`. -/
def olsScore {X K : Type*} [Fintype K]
    (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (b : EuclideanSpace ℝ K) (z : X) : EuclideanSpace ℝ K :=
  olsResidual x y b z • x z

/-- Given [a regressor](hyp:x) and [an observation](hyp:z), the [regressor
functional](goal) sends a coefficient increment `h` to the dot product
`x′h`. -/
def olsRegressorFunctional {X K : Type*} [Fintype K]
    (x : X → EuclideanSpace ℝ K) (z : X) :
    EuclideanSpace ℝ K →L[ℝ] ℝ :=
  innerSL ℝ (x z)

/-- Given [a regressor](hyp:x) and [an observation](hyp:z), the
[observationwise OLS score derivative](goal) sends `h` to `-x(x′h)`. -/
def olsScoreDerivative {X K : Type*} [Fintype K]
    (x : X → EuclideanSpace ℝ K) (z : X) :
    EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K :=
  (-(olsRegressorFunctional x z)).smulRight (x z)

/-- Given [a population law](hyp:P), [a regressor](hyp:x), [an
outcome](hyp:y), and [an observation](hyp:z), the [OLS influence
function](goal) is `Q⁻¹x e`. -/
def olsInfluence {X K : Type*} [MeasurableSpace X] [Fintype K] [DecidableEq K]
    (P : Measure X) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (z : X) : EuclideanSpace ℝ K :=
  (olsQ P x y)⁻¹.toEuclideanLin (olsScore x y (olsBeta P x y) z)

end

end Causalean.Stat
