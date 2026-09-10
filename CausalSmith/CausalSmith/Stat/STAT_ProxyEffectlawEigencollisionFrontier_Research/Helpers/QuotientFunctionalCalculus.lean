import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.AtomicLaw
import Mathlib.Data.Matrix.Basic

/-!
Collision-stable finite functional calculus for quotient atomic laws.

The results deliberately use labelled diagonalizing coordinates only as a certificate.  Repeated
eigenvalues are allowed: the represented law is passed to `LawModulo`, so splitting, merging, or
permuting equal-eigenvalue slots has no mathematical effect.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators

namespace QuotientFunctionalCalculus

/-- A square real operator together with diagonalizing coordinates.  `recover` records the
diagonal entry of `basisInv * operator * basis`; it is the only part of diagonalization needed by
the perturbation bound, while `expand` is the usual reconstruction identity. -/
-- @node: quotientFunctionalCalculus_diagonalizedOperator
structure DiagonalizedOperator (k : ℕ) (radius : ℝ) where
  operator : Matrix (Fin k) (Fin k) ℝ
  basis : Matrix (Fin k) (Fin k) ℝ
  basisInv : Matrix (Fin k) (Fin k) ℝ
  spectrum : Fin k → ℝ
  spectrum_mem : ∀ i, spectrum i ∈ Set.Icc (-radius) radius
  expand : ∀ p q, operator p q =
    ∑ i, basis p i * spectrum i * basisInv i q
  recover : ∀ i, spectrum i =
    ∑ p, ∑ q, basisInv i p * operator p q * basis q i

/-- The left-right spectral weight occurring in `aᵀ f(D) c`. -/
-- @node: quotientFunctionalCalculus_spectralWeight
def spectralWeight {k : ℕ} {radius : ℝ} (A : DiagonalizedOperator k radius)
    (a c : Fin k → ℝ) (i : Fin k) : ℝ :=
  (∑ p, a p * A.basis p i) * (∑ q, A.basisInv i q * c q)

/-- The matrix obtained by applying a scalar function to diagonalized spectral coordinates. -/
-- @node: quotientFunctionalCalculus_applyFunction
def applyFunction {k : ℕ} {radius : ℝ} (A : DiagonalizedOperator k radius)
    (f : ℝ → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun p q ↦ ∑ i, A.basis p i * f (A.spectrum i) * A.basisInv i q

/-- The bilinear anchor evaluation of a square matrix. -/
-- @node: quotientFunctionalCalculus_anchorEval
def anchorEval {k : ℕ} (a c : Fin k → ℝ)
    (M : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  ∑ p, ∑ q, a p * M p q * c q

/-- Left-right functional calculus is exactly integration against the labelled spectral weights:
`aᵀ f(D)c` equals the weighted sum of `f` over the real spectrum. -/
-- @node: quotientFunctionalCalculus_anchorEval_applyFunction
theorem anchorEval_applyFunction {k : ℕ} {radius : ℝ} (A : DiagonalizedOperator k radius)
    (a c : Fin k → ℝ) (f : ℝ → ℝ) :
    anchorEval a c (applyFunction A f) =
      ∑ i, spectralWeight A a c i * f (A.spectrum i) := by
  classical
  simp only [anchorEval, applyFunction, spectralWeight]
  calc
    (∑ p, ∑ q, a p * (∑ i, A.basis p i * f (A.spectrum i) * A.basisInv i q) * c q) =
        ∑ p, ∑ q, ∑ i,
          a p * (A.basis p i * f (A.spectrum i) * A.basisInv i q) * c q := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ p, ∑ q,
          a p * (A.basis p i * f (A.spectrum i) * A.basisInv i q) * c q := by
      conv_lhs =>
        enter [2, p]
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = ∑ i, (∑ p, a p * A.basis p i) *
          (∑ q, A.basisInv i q * c q) * f (A.spectrum i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- The labelled atomic law extracted from left-right functional calculus. -/
-- @node: quotientFunctionalCalculus_atomicLaw
def atomicLaw {k : ℕ} {radius : ℝ} (A : DiagonalizedOperator k radius)
    (a c : Fin k → ℝ) : AtomicLaw k radius :=
  ⟨spectralWeight A a c, A.spectrum⟩

/-- Positivity and normalization of the spectral weights turn functional-calculus coordinates
into a valid atomic probability law. -/
-- @node: quotientFunctionalCalculus_atomicLaw_valid
theorem atomicLaw_valid {k : ℕ} {radius : ℝ} (A : DiagonalizedOperator k radius)
    (a c : Fin k → ℝ) (hpos : ∀ i, 0 ≤ spectralWeight A a c i)
    (hsum : ∑ i, spectralWeight A a c i = 1) :
    AtomicLaw.Valid (atomicLaw A a c) := by
  exact ⟨hpos, hsum, A.spectrum_mem⟩

/-- Public quotient-law constructor for a positive normalized left-right functional calculus. -/
-- @node: quotientFunctionalCalculus_quotientLaw
def quotientLaw {k : ℕ} {radius : ℝ} (A : DiagonalizedOperator k radius)
    (a c : Fin k → ℝ) (hpos : ∀ i, 0 ≤ spectralWeight A a c i)
    (hsum : ∑ i, spectralWeight A a c i = 1) : AtomicLaw.LawModulo k radius :=
  AtomicLaw.LawModulo.ofProbabilityLaw
    ⟨atomicLaw A a c, atomicLaw_valid A a c hpos hsum⟩

/-- Coordinatewise atom and weight perturbations control quotient Wasserstein loss.  This lemma
is independent of any eigengap and permits coincident atoms. -/
-- @node: quotientFunctionalCalculus_wass1_le_coordinateL1
theorem wass1_le_coordinateL1 {k : ℕ} {radius : ℝ}
    {nu xi : AtomicLaw.ProbabilityLaw k radius} :
    0 ≤ radius →
    AtomicLaw.wass1 nu.1 xi.1 ≤
      (∑ i, |nu.1.atom i - xi.1.atom i|) +
        2 * radius * ∑ i, |nu.1.weight i - xi.1.weight i| := by
  intro hradius
  classical
  calc
    AtomicLaw.wass1 nu.1 xi.1 ≤
        (∑ i, min (nu.1.weight i) (xi.1.weight i) *
          |nu.1.atom i - xi.1.atom i|) +
        2 * radius *
          (∑ i, (nu.1.weight i - min (nu.1.weight i) (xi.1.weight i))) :=
      AtomicLaw.LawModulo.wass1_le_coordinateBound nu xi
    _ ≤ (∑ i, |nu.1.atom i - xi.1.atom i|) +
        2 * radius * ∑ i, |nu.1.weight i - xi.1.weight i| := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro i hi
        have hmin : min (nu.1.weight i) (xi.1.weight i) ≤ 1 := by
          exact (min_le_left _ _).trans (by
            rw [← nu.2.2.1]
            exact Finset.single_le_sum (fun j _ ↦ nu.2.1 j) (Finset.mem_univ i))
        have hmin0 : 0 ≤ min (nu.1.weight i) (xi.1.weight i) :=
          le_min (nu.2.1 i) (xi.2.1 i)
        nlinarith [abs_nonneg (nu.1.atom i - xi.1.atom i)]
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hradius)
        apply Finset.sum_le_sum
        intro i hi
        by_cases hle : nu.1.weight i ≤ xi.1.weight i
        · rw [min_eq_left hle]
          simpa using abs_nonneg (nu.1.weight i - xi.1.weight i)
        · rw [min_eq_right (le_of_not_ge hle)]
          exact le_abs_self _

/-- Gap-free quotient-law modulus in diagonalized operator coordinates.  The right side contains
only the recovered operator entries and the left-right anchor weights; no eigenvalue separation
or choice of distinct spectral projectors occurs. -/
-- @node: quotientFunctionalCalculus_gapFree_operatorAnchor_bound
theorem gapFree_operatorAnchor_bound {k : ℕ} {radius : ℝ}
    (A B : DiagonalizedOperator k radius) (a c a' c' : Fin k → ℝ)
    (hradius : 0 ≤ radius)
    (hApos : ∀ i, 0 ≤ spectralWeight A a c i)
    (hAsum : ∑ i, spectralWeight A a c i = 1)
    (hBpos : ∀ i, 0 ≤ spectralWeight B a' c' i)
    (hBsum : ∑ i, spectralWeight B a' c' i = 1) :
    (quotientLaw A a c hApos hAsum).wass1
        (quotientLaw B a' c' hBpos hBsum) ≤
      (∑ i, |(∑ p, ∑ q, A.basisInv i p * A.operator p q * A.basis q i) -
        (∑ p, ∑ q, B.basisInv i p * B.operator p q * B.basis q i)|) +
      2 * radius * ∑ i, |spectralWeight A a c i - spectralWeight B a' c' i| := by
  have hcoord := wass1_le_coordinateL1
    (radius := radius)
    (nu := ⟨atomicLaw A a c, atomicLaw_valid A a c hApos hAsum⟩)
    (xi := ⟨atomicLaw B a' c', atomicLaw_valid B a' c' hBpos hBsum⟩) hradius
  have hlabel : AtomicLaw.wass1 (atomicLaw A a c) (atomicLaw B a' c') ≤
      (∑ i, |A.spectrum i - B.spectrum i|) +
        2 * radius * ∑ i, |spectralWeight A a c i - spectralWeight B a' c' i| := by
    simpa only [atomicLaw] using hcoord
  change (AtomicLaw.LawModulo.ofProbabilityLaw
      ⟨atomicLaw A a c, atomicLaw_valid A a c hApos hAsum⟩).wass1
      (AtomicLaw.LawModulo.ofProbabilityLaw
        ⟨atomicLaw B a' c', atomicLaw_valid B a' c' hBpos hBsum⟩) ≤ _
  rw [AtomicLaw.LawModulo.wass1_ofProbabilityLaw]
  calc
    AtomicLaw.wass1 (atomicLaw A a c) (atomicLaw B a' c') ≤
        (∑ i, |A.spectrum i - B.spectrum i|) +
          2 * radius * ∑ i, |spectralWeight A a c i - spectralWeight B a' c' i| := hlabel
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [A.recover i, B.recover i]

private lemma abs_fin_sum_le {k : ℕ} (g : Fin k → ℝ) (C : ℝ)
    (h : ∀ i, |g i| ≤ C) : |∑ i, g i| ≤ (k : ℝ) * C := by
  calc
    |∑ i, g i| ≤ ∑ i, |g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, C := Finset.sum_le_sum fun i _ ↦ h i
    _ = (k : ℝ) * C := by simp

private lemma abs_mul_mul_sub_mul_mul (x y z x' y' z' : ℝ) :
    |x * y * z - x' * y' * z'| ≤
      |x - x'| * |y| * |z| + |x'| * |y - y'| * |z| +
        |x'| * |y'| * |z - z'| := by
  rw [show x * y * z - x' * y' * z' =
      (x - x') * y * z + x' * (y - y') * z + x' * y' * (z - z') by ring]
  calc
    |_ + _ + _| ≤ |(x - x') * y * z| + |x' * (y - y') * z| +
        |x' * y' * (z - z')| := by
      exact abs_add_three _ _ _
    _ = _ := by simp only [abs_mul]

private lemma operator_entry_bound {k : ℕ} {radius : ℝ}
    (A : DiagonalizedOperator k radius)
    (K : ℝ) (hradius : 0 ≤ radius)
    (hbasis : ∀ p i, |A.basis p i| ≤ K)
    (hinv : ∀ i q, |A.basisInv i q| ≤ K) (p q : Fin k) :
    |A.operator p q| ≤ (k : ℝ) * (K * radius * K) := by
  rw [A.expand p q]
  apply abs_fin_sum_le
  intro i
  rw [abs_mul, abs_mul]
  have hs : |A.spectrum i| ≤ radius := abs_le.mpr (A.spectrum_mem i)
  have hK0 : 0 ≤ K := le_trans (abs_nonneg (A.basis p i)) (hbasis p i)
  gcongr <;> aesop

private lemma recovered_atom_difference_bound {k : ℕ} {radius : ℝ}
    (A B : DiagonalizedOperator k radius) (K δD δS δT : ℝ)
    (hradius : 0 ≤ radius) (hK : 0 ≤ K)
    (hAbasis : ∀ p i, |A.basis p i| ≤ K)
    (hBbasis : ∀ p i, |B.basis p i| ≤ K)
    (hAinv : ∀ i q, |A.basisInv i q| ≤ K)
    (hBinv : ∀ i q, |B.basisInv i q| ≤ K)
    (hD : ∀ p q, |A.operator p q - B.operator p q| ≤ δD)
    (hS : ∀ p i, |A.basis p i - B.basis p i| ≤ δS)
    (hT : ∀ i q, |A.basisInv i q - B.basisInv i q| ≤ δT)
    (i : Fin k) :
    |A.spectrum i - B.spectrum i| ≤
      (k : ℝ) * ((k : ℝ) *
        (δT * ((k : ℝ) * (K * radius * K)) * K +
          K * δD * K + K * ((k : ℝ) * (K * radius * K)) * δS)) := by
  rw [A.recover i, B.recover i, ← Finset.sum_sub_distrib]
  apply abs_fin_sum_le
  intro p
  rw [← Finset.sum_sub_distrib]
  apply abs_fin_sum_le
  intro q
  calc
    |A.basisInv i p * A.operator p q * A.basis q i -
        B.basisInv i p * B.operator p q * B.basis q i| ≤
        |A.basisInv i p - B.basisInv i p| * |A.operator p q| * |A.basis q i| +
          |B.basisInv i p| * |A.operator p q - B.operator p q| * |A.basis q i| +
          |B.basisInv i p| * |B.operator p q| * |A.basis q i - B.basis q i| :=
      abs_mul_mul_sub_mul_mul _ _ _ _ _ _
    _ ≤ δT * ((k : ℝ) * (K * radius * K)) * K +
          K * δD * K + K * ((k : ℝ) * (K * radius * K)) * δS := by
      have hδD0 : 0 ≤ δD := le_trans (abs_nonneg _) (hD p q)
      have hδS0 : 0 ≤ δS := le_trans (abs_nonneg _) (hS q i)
      have hδT0 : 0 ≤ δT := le_trans (abs_nonneg _) (hT i p)
      have hradK : 0 ≤ (k : ℝ) * (K * radius * K) := by positivity
      have hAop := operator_entry_bound A K hradius hAbasis hAinv p q
      have hBop := operator_entry_bound B K hradius hBbasis hBinv p q
      gcongr <;> aesop

private lemma spectral_weight_difference_bound {k : ℕ} {radius : ℝ}
    (A B : DiagonalizedOperator k radius) (a c a' c' : Fin k → ℝ)
    (K U δa δc δS δT : ℝ) (hK : 0 ≤ K) (hU : 0 ≤ U)
    (hAbasis : ∀ p i, |A.basis p i| ≤ K)
    (hBbasis : ∀ p i, |B.basis p i| ≤ K)
    (hAinv : ∀ i q, |A.basisInv i q| ≤ K)
    (hBinv : ∀ i q, |B.basisInv i q| ≤ K)
    (ha : ∀ p, |a p| ≤ U) (ha' : ∀ p, |a' p| ≤ U)
    (hc : ∀ q, |c q| ≤ U)
    (hda : ∀ p, |a p - a' p| ≤ δa)
    (hdc : ∀ q, |c q - c' q| ≤ δc)
    (hS : ∀ p i, |A.basis p i - B.basis p i| ≤ δS)
    (hT : ∀ i q, |A.basisInv i q - B.basisInv i q| ≤ δT)
    (i : Fin k) :
    |spectralWeight A a c i - spectralWeight B a' c' i| ≤
      ((k : ℝ) * (δa * K + U * δS)) * ((k : ℝ) * (K * U)) +
        ((k : ℝ) * (U * K)) * ((k : ℝ) * (δT * U + K * δc)) := by
  let x : ℝ := ∑ p, a p * A.basis p i
  let x' : ℝ := ∑ p, a' p * B.basis p i
  let y : ℝ := ∑ q, A.basisInv i q * c q
  let y' : ℝ := ∑ q, B.basisInv i q * c' q
  have hx : |x| ≤ (k : ℝ) * (U * K) := by
    apply abs_fin_sum_le
    intro p
    rw [abs_mul]
    gcongr <;> aesop
  have hx' : |x'| ≤ (k : ℝ) * (U * K) := by
    apply abs_fin_sum_le
    intro p
    rw [abs_mul]
    gcongr <;> aesop
  have hy : |y| ≤ (k : ℝ) * (K * U) := by
    apply abs_fin_sum_le
    intro q
    rw [abs_mul]
    gcongr <;> aesop
  have hdx : |x - x'| ≤ (k : ℝ) * (δa * K + U * δS) := by
    dsimp [x, x']
    rw [← Finset.sum_sub_distrib]
    apply abs_fin_sum_le
    intro p
    rw [show a p * A.basis p i - a' p * B.basis p i =
      (a p - a' p) * A.basis p i + a' p * (A.basis p i - B.basis p i) by ring]
    calc
      |_ + _| ≤ |(a p - a' p) * A.basis p i| +
          |a' p * (A.basis p i - B.basis p i)| := abs_add_le _ _
      _ ≤ δa * K + U * δS := by
        simp only [abs_mul]
        have hδa0 : 0 ≤ δa := le_trans (abs_nonneg _) (hda p)
        have hδS0 : 0 ≤ δS := le_trans (abs_nonneg _) (hS p i)
        gcongr <;> aesop
  have hdy : |y - y'| ≤ (k : ℝ) * (δT * U + K * δc) := by
    dsimp [y, y']
    rw [← Finset.sum_sub_distrib]
    apply abs_fin_sum_le
    intro q
    rw [show A.basisInv i q * c q - B.basisInv i q * c' q =
      (A.basisInv i q - B.basisInv i q) * c q +
        B.basisInv i q * (c q - c' q) by ring]
    calc
      |_ + _| ≤ |(A.basisInv i q - B.basisInv i q) * c q| +
          |B.basisInv i q * (c q - c' q)| := abs_add_le _ _
      _ ≤ δT * U + K * δc := by
        simp only [abs_mul]
        have hδT0 : 0 ≤ δT := le_trans (abs_nonneg _) (hT i q)
        have hδc0 : 0 ≤ δc := le_trans (abs_nonneg _) (hdc q)
        gcongr <;> aesop
  change |x * y - x' * y'| ≤ _
  rw [show x * y - x' * y' = (x - x') * y + x' * (y - y') by ring]
  calc
    |_ + _| ≤ |(x - x') * y| + |x' * (y - y')| := abs_add_le _ _
    _ ≤ ((k : ℝ) * (δa * K + U * δS)) * ((k : ℝ) * (K * U)) +
        ((k : ℝ) * (U * K)) * ((k : ℝ) * (δT * U + K * δc)) := by
      simp only [abs_mul]
      have hδa0 : 0 ≤ δa := le_trans (abs_nonneg _) (hda i)
      have hδc0 : 0 ≤ δc := le_trans (abs_nonneg _) (hdc i)
      have hδS0 : 0 ≤ δS := le_trans (abs_nonneg _) (hS i i)
      have hδT0 : 0 ≤ δT := le_trans (abs_nonneg _) (hT i i)
      gcongr <;> aesop

/-- With bounded diagonalizers and anchors, quotient Wasserstein loss has an explicit fixed-`k`
gap-free bound in entrywise operator, anchor, diagonalizer, and inverse perturbations.  The formula
is uniform over all real spectra in the radius interval, including arbitrary repeated eigenvalues. -/
-- @node: quotientFunctionalCalculus_gapFree_fixedK_envelope
theorem gapFree_fixedK_envelope {k : ℕ} {radius : ℝ}
    (A B : DiagonalizedOperator k radius)
    (a c a' c' : Fin k → ℝ) (K U δD δa δc δS δT : ℝ)
    (hradius : 0 ≤ radius) (hK : 0 ≤ K) (hU : 0 ≤ U)
    (hAbasis : ∀ p i, |A.basis p i| ≤ K)
    (hBbasis : ∀ p i, |B.basis p i| ≤ K)
    (hAinv : ∀ i q, |A.basisInv i q| ≤ K)
    (hBinv : ∀ i q, |B.basisInv i q| ≤ K)
    (ha : ∀ p, |a p| ≤ U) (ha' : ∀ p, |a' p| ≤ U)
    (hc : ∀ q, |c q| ≤ U)
    (hD : ∀ p q, |A.operator p q - B.operator p q| ≤ δD)
    (hda : ∀ p, |a p - a' p| ≤ δa)
    (hdc : ∀ q, |c q - c' q| ≤ δc)
    (hS : ∀ p i, |A.basis p i - B.basis p i| ≤ δS)
    (hT : ∀ i q, |A.basisInv i q - B.basisInv i q| ≤ δT)
    (hApos : ∀ i, 0 ≤ spectralWeight A a c i)
    (hAsum : ∑ i, spectralWeight A a c i = 1)
    (hBpos : ∀ i, 0 ≤ spectralWeight B a' c' i)
    (hBsum : ∑ i, spectralWeight B a' c' i = 1) :
    (quotientLaw A a c hApos hAsum).wass1
        (quotientLaw B a' c' hBpos hBsum) ≤
      (k : ℝ) * ((k : ℝ) * ((k : ℝ) *
        (δT * ((k : ℝ) * (K * radius * K)) * K +
          K * δD * K + K * ((k : ℝ) * (K * radius * K)) * δS))) +
      2 * radius * ((k : ℝ) *
        (((k : ℝ) * (δa * K + U * δS)) * ((k : ℝ) * (K * U)) +
          ((k : ℝ) * (U * K)) * ((k : ℝ) * (δT * U + K * δc)))) := by
  calc
    (quotientLaw A a c hApos hAsum).wass1
        (quotientLaw B a' c' hBpos hBsum) ≤
        (∑ i, |A.spectrum i - B.spectrum i|) +
          2 * radius * ∑ i,
            |spectralWeight A a c i - spectralWeight B a' c' i| := by
      have h := gapFree_operatorAnchor_bound A B a c a' c' hradius
        hApos hAsum hBpos hBsum
      simpa only [← A.recover, ← B.recover] using h
    _ ≤ _ := by
      apply add_le_add
      · calc
          (∑ i, |A.spectrum i - B.spectrum i|) ≤
              ∑ _i : Fin k, ((k : ℝ) * ((k : ℝ) *
                (δT * ((k : ℝ) * (K * radius * K)) * K +
                  K * δD * K + K * ((k : ℝ) * (K * radius * K)) * δS))) := by
            apply Finset.sum_le_sum
            intro i hi
            exact recovered_atom_difference_bound A B K δD δS δT hradius hK
              hAbasis hBbasis hAinv hBinv hD hS hT i
          _ = _ := by simp
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hradius)
        calc
          (∑ i, |spectralWeight A a c i - spectralWeight B a' c' i|) ≤
              ∑ _i : Fin k,
                (((k : ℝ) * (δa * K + U * δS)) * ((k : ℝ) * (K * U)) +
                  ((k : ℝ) * (U * K)) * ((k : ℝ) * (δT * U + K * δc))) := by
            apply Finset.sum_le_sum
            intro i hi
            exact spectral_weight_difference_bound A B a c a' c' K U δa δc δS δT
              hK hU hAbasis hBbasis hAinv hBinv ha ha' hc hda hdc hS hT i
          _ = _ := by simp; ring

end QuotientFunctionalCalculus

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
