/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.SampleBlocks
import Causalean.Stat.Nonparametric.LocalPoly.DesignMatrixPosDef
import Causalean.Stat.Nonparametric.LocalPoly.Weights
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Realized local-polynomial design and estimators

This module gives full definitions of the paper's reference Gram, deterministic
three-way split, local count and total Gram, exact intercept weights, stabilized
estimator, bias-aware interval, and realized-design modulus handle.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set
open scoped BigOperators Matrix

noncomputable section

/-! ## S3: realized-design local-polynomial experiment -/

-- @env: S3
variable {J n ell : ℕ} {beta kappa L cminus cplus pmin delta h alpha : ℝ}

/-- Monomial basis `(1,u,...,u^ell)`. -/
def monomialVec (ell : ℕ) (u : ℝ) : Fin (ell + 1) → ℝ :=
  fun j => u ^ (j : ℕ) -- @realizes v_ell(monomial basis through degree ell)

/-- Normalized population reference moment matrix for `(rho+u)^kappa`. -/
def refMomentMatrix (ell : ℕ) (kappa rho : ℝ) :
    Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ :=
  fun i j =>
    (∫ u in Set.Icc (0 : ℝ) 1,
      monomialVec ell u i * monomialVec ell u j * (rho + u) ^ kappa) /
    (∫ u in Set.Icc (0 : ℝ) 1, (rho + u) ^ kappa)
  -- @realizes M_kappa_rho(normalized weighted monomial moment matrix)

/-- Quadratic form of a real square matrix. -/
def matrixQuadratic {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (z : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, z i * A i j * z j

/-- Smallest quadratic-form value on the Euclidean unit sphere. -/
def quadraticMin {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sInf {q : ℝ | ∃ z : Fin d → ℝ,
    (∑ i, (z i) ^ 2) = 1 ∧ q = matrixQuadratic A z}

/-- Uniform population-Gram constant. -/
def lambdaStar (ell : ℕ) (kappa cminus cplus : ℝ) : ℝ :=
  (cminus / cplus) * sInf {q : ℝ | ∃ rho : ℝ, 0 ≤ rho ∧
    q = quadraticMin (refMomentMatrix ell kappa rho)}
  -- @realizes lambda_star((c_minus/c_plus)*inf_{rho>=0} lambda_min(M_kappa_rho))

/-- Three deterministic, pairwise-disjoint sample blocks, each of size at least
`floor(n/4)`. -/
structure SplitBlocks (n : ℕ) where
  I0 : Finset (Fin n) -- @realizes I_0(first deterministic block)
  I1 : Finset (Fin n) -- @realizes I_1(second deterministic block)
  I2 : Finset (Fin n) -- @realizes I_2(third deterministic block)
  card_I0 : n / 4 ≤ I0.card -- @realizes I_0(cardinality at least floor(n/4))
  card_I1 : n / 4 ≤ I1.card -- @realizes I_1(cardinality at least floor(n/4))
  card_I2 : n / 4 ≤ I2.card -- @realizes I_2(cardinality at least floor(n/4))
  disjoint01 : Disjoint I0 I1
  disjoint02 : Disjoint I0 I2
  disjoint12 : Disjoint I1 I2

/-- Rescaled location of one observed treatment relative to the moving threshold. -/
def scaledDose (delta h : ℝ) (o : ClampObs J) : ℝ := (o.A - delta) / h

/-- Number of observations in stratum `x` and the local threshold window. -/
def localCount (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (x : Fin J) (delta h : ℝ) : ℕ := by
  classical
  exact ∑ i ∈ B.I2, if (z i).X = x ∧ (z i).A ∈ Set.Icc delta (delta + h)
    then 1 else 0
  -- @realizes N_x(sum over I_2 of the local stratum-window indicator)

/-- The zero-one localization weight on the full finite design. -/
def localKernelWeight (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (delta h : ℝ) (i : Fin n) : ℝ :=
  if i ∈ B.I2 ∧ (z i).X = x ∧
      scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1 then 1 else 0

/-- Unnormalized total local Gram matrix, realized by Causalean's weighted
monomial design matrix. -/
def localGram (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (ell : ℕ) (delta h : ℝ) : Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ :=
  Causalean.Stat.Nonparametric.designMatrix ell
    (fun i => scaledDose delta h (z i)) (localKernelWeight B z x delta h)
  -- @realizes G_x(total localized monomial Gram over I_2)

/-- For [sample blocks](hyp:B), [a realized sample](hyp:z), [a stratum](hyp:x), [a polynomial degree](hyp:ell), [a threshold and bandwidth](hyp:delta,h), and [two matrix coordinates](hyp:r,s), [the local Gram entry equals the active-window monomial sum](goal). -/
lemma localGram_apply (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (x : Fin J) (ell : ℕ) (delta h : ℝ) (r s : Fin (ell + 1)) :
    localGram B z x ell delta h r s = ∑ i ∈ B.I2,
      if (z i).X = x ∧ scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1 then
        monomialVec ell (scaledDose delta h (z i)) r *
          monomialVec ell (scaledDose delta h (z i)) s
      else 0 := by
  classical
  simp only [localGram, Causalean.Stat.Nonparametric.designMatrix]
  rw [show (∑ i, localKernelWeight B z x delta h i *
      scaledDose delta h (z i) ^ (r : ℕ) * scaledDose delta h (z i) ^ (s : ℕ)) =
      ∑ i ∈ B.I2, localKernelWeight B z x delta h i *
        scaledDose delta h (z i) ^ (r : ℕ) * scaledDose delta h (z i) ^ (s : ℕ) by
    symm
    apply Finset.sum_subset (Finset.subset_univ B.I2)
    intro i _ hi
    simp [localKernelWeight, hi]]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases ha : (z i).X = x ∧ scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1
  · simp [localKernelWeight, hi, ha, monomialVec]
  · rw [if_neg ha]
    have hw : localKernelWeight B z x delta h i = 0 := by
      rw [localKernelWeight, if_neg]
      exact fun hactive => ha hactive.2
    rw [hw]
    simp

/-- The good-design event, encoded by its load-bearing quadratic-form lower bound. -/
def GoodGramEvent (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (ell : ℕ) (kappa cminus cplus delta h : ℝ) : Prop :=
  0 < localCount B z x delta h ∧
  ∀ v : Fin (ell + 1) → ℝ,
    lambdaStar ell kappa cminus cplus * (localCount B z x delta h : ℝ) / 2 *
        (∑ j, (v j) ^ 2) ≤
      matrixQuadratic (localGram B z x ell delta h) v
  -- @realizes Omega_x(N_x>0 and lambda_min(G_x)>=lambda_star*N_x/2)

/-- Exact local-polynomial intercept weight from Causalean's equivalent kernel
on the good event, and zero off it. -/
def interceptWeight (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (ell : ℕ) (kappa cminus cplus delta h : ℝ) (i : Fin n) : ℝ := by
  classical
  exact if GoodGramEvent B z x ell kappa cminus cplus delta h then
    Causalean.Stat.Nonparametric.equivKernelWeight ell
      (fun j => scaledDose delta h (z j)) (localKernelWeight B z x delta h) i
  else 0
  -- @realizes w_ix(exact intercept weight on Omega_x, zero off Omega_x)

/-- Given [a good design](hyp:hgood), [an observation in the regression block](hyp:hi), [the required stratum match](hyp:hix), and [local-window membership](hyp:hu), [the intercept weight is the zeroth coordinate of the inverse-Gram feature vector](goal). -/
lemma interceptWeight_eq_mulVec (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (x : Fin J) (ell : ℕ) (kappa cminus cplus delta h : ℝ) (i : Fin n)
    (hgood : GoodGramEvent B z x ell kappa cminus cplus delta h)
    (hi : i ∈ B.I2) (hix : (z i).X = x)
    (hu : scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1) :
    interceptWeight B z x ell kappa cminus cplus delta h i =
      ((localGram B z x ell delta h)⁻¹ *ᵥ
        monomialVec ell (scaledDose delta h (z i))) 0 := by
  classical
  rw [interceptWeight, if_pos hgood]
  simp only [Causalean.Stat.Nonparametric.equivKernelWeight, Matrix.mulVec,
    dotProduct, localGram, monomialVec]
  simp [localKernelWeight, hi, hix, hu]

/-- On [the good-design event](hyp:hgood), [the intercept weight equals the equivalent-kernel weight](goal). -/
lemma interceptWeight_eq_equivKernel_of_good
    (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (ell : ℕ) (kappa cminus cplus delta h : ℝ)
    (hgood : GoodGramEvent B z x ell kappa cminus cplus delta h) (i : Fin n) :
    interceptWeight B z x ell kappa cminus cplus delta h i =
      Causalean.Stat.Nonparametric.equivKernelWeight ell
        (fun j => scaledDose delta h (z j)) (localKernelWeight B z x delta h) i := by
  simp [interceptWeight, hgood]

/-- On [the good-design event](hyp:hgood), if [an observation is inactive](hyp:hi), [its intercept weight is zero](goal). -/
lemma interceptWeight_eq_zero_of_inactive
    (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (ell : ℕ) (kappa cminus cplus delta h : ℝ) (i : Fin n)
    (hgood : GoodGramEvent B z x ell kappa cminus cplus delta h)
    (hi : ¬ (i ∈ B.I2 ∧ (z i).X = x ∧
      scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1)) :
    interceptWeight B z x ell kappa cminus cplus delta h i = 0 := by
  rw [interceptWeight_eq_equivKernel_of_good
    B z x ell kappa cminus cplus delta h hgood i]
  simp only [Causalean.Stat.Nonparametric.equivKernelWeight]
  have hw : localKernelWeight B z x delta h i = 0 := by
    rw [localKernelWeight, if_neg hi]
  simp [hw]

/-- Projection to the outcome range `[0,1]`. -/
def clampUnit (t : ℝ) : ℝ := min 1 (max 0 t)

/-- Empirical average over a deterministic finite block. -/
def blockAverage {X : Type*} {m : ℕ} (I : Finset (Fin m))
    (z : Fin m → X) (f : X → ℝ) : ℝ :=
  (I.card : ℝ)⁻¹ * ∑ i ∈ I, f (z i)

/-- Retained-course empirical mean on block zero. -/
def retainedEstimate (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (delta : ℝ) : ℝ :=
  blockAverage B.I0 z (fun o => if delta < o.A then o.Y else 0)

/-- Empirical threshold mass in one stratum on block one. -/
def atomEstimate (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (x : Fin J) (delta : ℝ) : ℝ :=
  blockAverage B.I1 z (fun o => if o.X = x ∧ o.A ≤ delta then 1 else 0)

/-- Stabilized local regression value, with the prescribed one-half fallback. -/
def localRegressionEstimate (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (x : Fin J) (ell : ℕ) (kappa cminus cplus delta h : ℝ) : ℝ := by
  classical
  exact if GoodGramEvent B z x ell kappa cminus cplus delta h then
    clampUnit (∑ i ∈ B.I2,
      interceptWeight B z x ell kappa cminus cplus delta h i * (z i).Y)
  else 1 / 2

/-- Sample-split total-Gram-stabilized estimator of the clamp functional. -/
-- @node: def:total-gram-estimator
def totalGramEstimator (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (ell : ℕ) (kappa cminus cplus delta h : ℝ) : ℝ :=
  clampUnit (retainedEstimate B z delta + ∑ x : Fin J,
    atomEstimate B z x delta *
      localRegressionEstimate B z x ell kappa cminus cplus delta h)
  -- @realizes theta_hat_n(sample-split stabilized estimator, projected to [0,1])

/-- Continuity-only estimator using the retained-course block and the fixed
one-half regression fallback for the total empirical atom mass. -/
-- @node: def:continuity-fallback-estimator
def contFallbackEstimator (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (delta : ℝ) : ℝ :=
  clampUnit (retainedEstimate B z delta +
    (1 / 2 : ℝ) * ∑ x : Fin J, atomEstimate B z x delta)
  -- @realizes theta_hat_cont_n(fixed one-half atom-regression fallback)

/-- Continuity-only Hoeffding interval, intersected with the outcome range. -/
-- @node: def:continuity-honest-interval
def contHoeffdingInterval (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (delta alpha : ℝ) : Set ℝ :=
  let t0 := Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ)))
  let t1 := Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ)))
  let atomTotal := ∑ x : Fin J, atomEstimate B z x delta
  let center := contFallbackEstimator B z delta
  let radius := t0 + t1 + atomTotal / 2
  Set.Icc (max 0 (center - radius)) (min 1 (center + radius))
  -- @realizes CI_cont_n(two-block Hoeffding interval with atom fallback radius)

/-- The per-stratum bias-plus-noise radius, including the singular-Gram fallback. -/
def stratumRadius (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (ell : ℕ) (beta kappa L cminus cplus delta h tAlpha b1 : ℝ) : ℝ := by
  classical
  exact if GoodGramEvent B z x ell kappa cminus cplus delta h then
    (atomEstimate B z x delta + b1) *
      (L * h ^ beta * ∑ i ∈ B.I2,
          |interceptWeight B z x ell kappa cminus cplus delta h i| +
        tAlpha * Real.sqrt (∑ i ∈ B.I2,
          (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2)) + b1
  else atomEstimate B z x delta + b1

/-- Bias-aware interval intersected with `[0,1]`. -/
-- @node: def:honest-interval
def honestInterval (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (ell : ℕ) (beta kappa L cminus cplus delta h alpha : ℝ) : Set ℝ :=
  let tAlpha := Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2)
  let b0 := tAlpha / Real.sqrt (B.I0.card : ℝ)
  let center := totalGramEstimator B z ell kappa cminus cplus delta h
  let b1 := tAlpha / Real.sqrt (B.I1.card : ℝ)
  let radius := b0 + ∑ x : Fin J,
    stratumRadius B z x ell beta kappa L cminus cplus delta h tAlpha b1
  Set.Icc (max 0 (center - radius)) (min 1 (center + radius))
  -- @realizes CI_n(bias-aware atom-fallback interval intersected with [0,1])

/-- Exact worst-case Hölder bias of affine weights on a realized local window.
The derivatives are intrinsic to `[0,1]`, so the value is invariant under any
change to an ambient extension of the regression. -/
def exactHolderBias (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (_x : Fin J) -- @realizes exactHolderBias(realized Hölder-bias supremum)
    (ell : ℕ) (beta L delta : ℝ) (w : Fin n → ℝ) : ℝ :=
  sSup {b : ℝ | ∃ f : ℝ → ℝ,
    ContinuousOn f (Set.Icc (0 : ℝ) 1) ∧
    (∀ a ∈ Set.Icc (0 : ℝ) 1, f a ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |f t - ∑ j ∈ Finset.range (ell + 1),
          iteratedDerivWithin j f (Set.Icc (0 : ℝ) 1) s *
            (t - s) ^ j / (Nat.factorial j : ℝ)| ≤ L * |t - s| ^ beta) ∧
    b = |(∑ i ∈ B.I2, w i * f (z i).A) - f delta|}

/-- Conditional affine modulus for one realized design. Only observations in
the local stratum-window may receive weight, and the full Hölder bias—not a
coarse `L h^beta sum |w_i|` upper bound—is optimized. -/
def realizedExactModulus -- @realizes realizedExactModulus(exact bias-plus-l2 infimum)
    (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (x : Fin J) (ell : ℕ) (beta L delta h t : ℝ)
    (_ht : 0 ≤ t) : ℝ :=
  sInf {v : ℝ | ∃ w : Fin n → ℝ,
    (∀ i, i ∉ B.I2 ∨ (z i).X ≠ x ∨
        scaledDose delta h (z i) ∉ Set.Icc (0 : ℝ) 1 → w i = 0) ∧
    (∀ j : Fin (ell + 1),
      (∑ i ∈ B.I2, w i * monomialVec ell (scaledDose delta h (z i)) j) =
        if j = 0 then 1 else 0) ∧
    v = exactHolderBias B z x ell beta L delta w +
      t * Real.sqrt (∑ i ∈ B.I2, (w i) ^ 2)}

/-- The realized-design exact-modulus handle integrates the conditional
sample-dependent modulus under a probability/support-pinned polynomial-
thinning design law, for a positive bandwidth and a nonnegative test
multiplier. -/
-- @node: def:exact-modulus-handle
def exactModulusHandle (P : ClampLaw J) (B : SplitBlocks n) (x : Fin J)
    (ell : ℕ) (beta kappa L cminus cplus pmin delta h t : ℝ)
    (_hh : 0 < h) (_ht : 0 ≤ t)
    (_hmodel : ClampModel P beta kappa L cminus cplus pmin) : ℝ :=
  ∫ z, realizedExactModulus B z x ell beta L delta h t _ht ∂iidProduct P n

end


end CausalSmith.Stat.LmtpThresholdAtomFrontier
