import Mathlib.Probability.Distributions.Binomial
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Basic

set_option linter.style.openClassical false

/-!
# Exact binomial-test inversion

This file constructs the equal-tailed, two-sided Clopper--Pearson confidence
interval by inverting the two exact binomial tail tests.  The coverage proof is
finite-sample and allows the conservatism caused by atoms.
-/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory unitInterval Classical

/-- The lower-tail probability through count `k`. -/
noncomputable def binomialLowerTail (n : ℕ) (p : I) (k : ℕ) : ℝ≥0∞ :=
  Bin(n, p) (Iic k)

/-- The upper-tail probability from count `k`. -/
noncomputable def binomialUpperTail (n : ℕ) (p : I) (k : ℕ) : ℝ≥0∞ :=
  Bin(n, p) (Ici k)

/-- Parameters not rejected by either exact one-sided binomial test. -/
def clopperPearsonAcceptance (n : ℕ) (tailError : ℝ≥0∞) (k : ℕ) : Set I :=
  {p | tailError < binomialUpperTail n p k ∧
    tailError < binomialLowerTail n p k}

/-- The lower endpoint of the equal-tailed exact binomial interval. -/
noncomputable def clopperPearsonLower (n : ℕ) (tailError : ℝ≥0∞) (k : ℕ) : I :=
  sInf (clopperPearsonAcceptance n tailError k)

/-- The upper endpoint of the equal-tailed exact binomial interval. -/
noncomputable def clopperPearsonUpper (n : ℕ) (tailError : ℝ≥0∞) (k : ℕ) : I :=
  sSup (clopperPearsonAcceptance n tailError k)

/-- The two-sided Clopper--Pearson interval obtained by exact-test inversion.
Here `tailError` is the error allocated to each of the two tails. -/
noncomputable def clopperPearsonInterval
    (n : ℕ) (tailError : ℝ≥0∞) (k : ℕ) : Set I :=
  Icc (clopperPearsonLower n tailError k)
    (clopperPearsonUpper n tailError k)

/-- The usual equal-tailed Clopper--Pearson interval at total error
`marginalError`, allocating half of that error to each tail. -/
noncomputable def clopperPearsonIntervalAtError
    (n : ℕ) (marginalError : ℝ≥0∞) (k : ℕ) : Set I :=
  clopperPearsonInterval n (marginalError / 2) k

private theorem lowerTail_rejection_le
    (μ : Measure ℕ) (n : ℕ) (δ : ℝ≥0∞) :
    μ {k | k ≤ n ∧ μ (Iic k) ≤ δ} ≤ δ := by
  classical
  let s : Finset ℕ := (Finset.range (n + 1)).filter fun k => μ (Iic k) ≤ δ
  by_cases hs : s.Nonempty
  · let m := s.max' hs
    calc
      μ {k | k ≤ n ∧ μ (Iic k) ≤ δ} = μ (s : Set ℕ) := by
        congr 1
        ext k
        simp [s]
      _ ≤ μ (Iic m) := measure_mono (by
        intro k hk
        exact Finset.le_max' s k hk)
      _ ≤ δ := by
        have hm : m ∈ s := Finset.max'_mem s hs
        have hm' : m ≤ n ∧ μ (Iic m) ≤ δ := by simpa [s] using hm
        exact hm'.2
  · have hempty : {k | k ≤ n ∧ μ (Iic k) ≤ δ} = ∅ := by
      ext k
      constructor
      · intro hk
        have hks : k ∈ s := by simpa [s] using hk
        exact (hs ⟨k, hks⟩).elim
      · simp
    simp [hempty]

private theorem upperTail_rejection_le
    (μ : Measure ℕ) (n : ℕ) (δ : ℝ≥0∞) :
    μ {k | k ≤ n ∧ μ (Ici k) ≤ δ} ≤ δ := by
  classical
  let s : Finset ℕ := (Finset.range (n + 1)).filter fun k => μ (Ici k) ≤ δ
  by_cases hs : s.Nonempty
  · let m := s.min' hs
    calc
      μ {k | k ≤ n ∧ μ (Ici k) ≤ δ} = μ (s : Set ℕ) := by
        congr 1
        ext k
        simp [s]
      _ ≤ μ (Ici m) := measure_mono (by
        intro k hk
        exact Finset.min'_le s k hk)
      _ ≤ δ := by
        have hm : m ∈ s := Finset.min'_mem s hs
        have hm' : m ≤ n ∧ μ (Ici m) ≤ δ := by simpa [s] using hm
        exact hm'.2
  · have hempty : {k | k ≤ n ∧ μ (Ici k) ≤ δ} = ∅ := by
      ext k
      constructor
      · intro hk
        have hks : k ∈ s := by simpa [s] using hk
        exact (hs ⟨k, hks⟩).elim
      · simp
    simp [hempty]

/-- A parameter accepted by both exact tail tests lies in their inverted
Clopper--Pearson interval. -/
theorem mem_clopperPearsonInterval_of_tailError_lt
    (n : ℕ) (p : I) (tailError : ℝ≥0∞) (k : ℕ)
    (hUpper : tailError < binomialUpperTail n p k)
    (hLower : tailError < binomialLowerTail n p k) :
    p ∈ clopperPearsonInterval n tailError k := by
  have hp : p ∈ clopperPearsonAcceptance n tailError k := ⟨hUpper, hLower⟩
  exact ⟨sInf_le hp, le_sSup hp⟩

/-- Under the exact binomial law, the probability that the true parameter
misses the two-sided Clopper--Pearson interval is at most twice the per-tail
error.  No asymptotics or continuity of the binomial law are used. -/
theorem binomial_miss_clopperPearsonInterval_le
    (n : ℕ) (p : I) (tailError : ℝ≥0∞) :
    Bin(n, p) {k | p ∉ clopperPearsonInterval n tailError k} ≤
      tailError + tailError := by
  let μ : Measure ℕ := Bin(n, p)
  have hsupp : ∀ᵐ k ∂μ, k ≤ n :=
    ProbabilityTheory.ae_le_of_hasLaw_binomial (p := p) (n := n)
      (ProbabilityTheory.HasLaw.id (μ := μ))
  have hsubset :
      {k | k ≤ n ∧ p ∉ clopperPearsonInterval n tailError k} ⊆
        {k | k ≤ n ∧ μ (Ici k) ≤ tailError} ∪
          {k | k ≤ n ∧ μ (Iic k) ≤ tailError} := by
    intro k hk
    by_cases hUpper : μ (Ici k) ≤ tailError
    · exact Or.inl ⟨hk.1, hUpper⟩
    · by_cases hLower : μ (Iic k) ≤ tailError
      · exact Or.inr ⟨hk.1, hLower⟩
      · exfalso
        apply hk.2
        apply mem_clopperPearsonInterval_of_tailError_lt n p tailError k
        · simpa [binomialUpperTail, μ] using lt_of_not_ge hUpper
        · simpa [binomialLowerTail, μ] using lt_of_not_ge hLower
  calc
    μ {k | p ∉ clopperPearsonInterval n tailError k} ≤
        μ {k | k ≤ n ∧ p ∉ clopperPearsonInterval n tailError k} := by
      apply measure_mono_ae
      filter_upwards [hsupp] with k hk hmiss
      exact ⟨hk, hmiss⟩
    _ ≤ μ ({k | k ≤ n ∧ μ (Ici k) ≤ tailError} ∪
          {k | k ≤ n ∧ μ (Iic k) ≤ tailError}) := measure_mono hsubset
    _ ≤ μ {k | k ≤ n ∧ μ (Ici k) ≤ tailError} +
          μ {k | k ≤ n ∧ μ (Iic k) ≤ tailError} := measure_union_le _ _
    _ ≤ tailError + tailError := add_le_add
      (upperTail_rejection_le μ n tailError)
      (lowerTail_rejection_le μ n tailError)

/-- The per-cell miss probability of the two-sided Clopper--Pearson interval
is at most its stated marginal error. -/
theorem binomial_miss_clopperPearsonIntervalAtError_le
    (n : ℕ) (p : I) (marginalError : ℝ≥0∞) :
    Bin(n, p) {k | p ∉ clopperPearsonIntervalAtError n marginalError k} ≤
      marginalError := by
  simpa only [clopperPearsonIntervalAtError, ENNReal.add_halves] using
    binomial_miss_clopperPearsonInterval_le n p (marginalError / 2)

/-- The exact marginal interval for one cell under the Bonferroni allocation. -/
noncomputable def marginalCellInterval {O : Type*} [Fintype O]
    (n : ℕ) (alpha : ℝ≥0∞) (counts : O → ℕ) (o : O) : Set I :=
  clopperPearsonIntervalAtError n (alpha / Fintype.card O) (counts o)
  -- @realizes n(positive sample-size parameter)
  -- @realizes alpha(nominal error parameter)
  -- @realizes CI_o(two-sided Clopper-Pearson interval at alpha/|O|)

/-- The simultaneous simplex-valued Bonferroni confidence box. -/
noncomputable def simultaneousConfidenceBox {O : Type*} [Fintype O]
    (n : ℕ) (alpha : ℝ≥0∞) (counts : O → ℕ) : Set (O → I) :=
  {q | (∑ o, (q o : ℝ)) = 1 ∧ ∀ o, q o ∈ marginalCellInterval n alpha counts o}
  -- @realizes C_n_alpha(simplex intersected with all marginal intervals)

/-- The whole-identified-set confidence interval: optimize over response
weights whose induced law lies in the exact simultaneous box, with `[0,1]`
as the specified empty-intersection fallback. -/
-- @node: def:whole-set-confidence-construction
noncomputable def wholeSetConfidenceInterval
    {O T OBlind : Type*} [Fintype O] [Fintype T] [Fintype OBlind]
    [DecidableEq O] [DecidableEq T] [DecidableEq OBlind]
    (G : SLCCIncidence O T OBlind) (n : ℕ) (alpha : ℝ≥0∞)
    (counts : O → ℕ) : Set ℝ :=
  if (simultaneousConfidenceBox n alpha counts ∩
      {q | (fun o => (q o : ℝ)) ∈ observablePolytope G}).Nonempty then
    targetFunctional G ''
      {w | w ∈ stdSimplex ℝ T ∧
        ∃ q ∈ simultaneousConfidenceBox n alpha counts,
          G.B.mulVec w = fun o => (q o : ℝ)}
  else Set.Icc 0 1
  -- @realizes I_n_alpha(constrained value set or total fallback interval)

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
