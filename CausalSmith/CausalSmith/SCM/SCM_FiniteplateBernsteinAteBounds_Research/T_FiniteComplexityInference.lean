import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.RealAlgebraic

/-! # Exact multinomial size, semialgebraicity, and CAD output -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

/-- A rational polynomial sign cell in count-law coordinates. -/
def RationalSignCell {m : ℕ}
    (cell : Finset (MvPolynomial (CountIndex m) ℚ × Ordering))
    (b : CountIndex m → ℝ) : Prop :=
  ∀ item ∈ cell,
    match item.2 with
    | .eq => MvPolynomial.eval₂ (Rat.castHom ℝ) b item.1 = 0
    | .lt => MvPolynomial.eval₂ (Rat.castHom ℝ) b item.1 < 0
    | .gt => 0 < MvPolynomial.eval₂ (Rat.castHom ℝ) b item.1

/-- A finite union of rational polynomial sign cells. -/
def IsFiniteRationalSemialgebraic {m : ℕ}
    (S : Set (CountIndex m → ℝ)) : Prop :=
  ∃ cells : Finset (Finset (MvPolynomial (CountIndex m) ℚ × Ordering)),
    ∀ b, b ∈ S ↔ ∃ cell ∈ cells, RationalSignCell cell b

/-- The exact tie-inclusive nonrandomized p-value rejects with probability at
most the nominal level under every candidate multinomial law. -/
theorem finite_complexity_inference_size (m n : ℕ) (α : ℝ)
    (hα : ValidConfidenceLevel α) :
    ∀ bprime ∈ stdSimplex ℝ (CountIndex m),
      ∑ z : AggregateSpace m n with exactPValue n bprime z ≤ α,
        multinomialPmf n bprime z ≤ α := by
  sorry

/-- The inverted region is semialgebraic on its finite zero-pattern cells and
the induced ATE confidence set is contained in `[-1,1]`. -/
theorem finite_complexity_inference_semialgebraic
    (m n : ℕ) (ε α : ℝ) (zobs : AggregateSpace m n)
    (hα : ValidConfidenceLevel α) :
    IsFiniteRationalSemialgebraic (exactMultinomialRegion n α zobs) ∧
    wholeSetConfidenceSet m n ε α zobs ⊆ Set.Icc (-1) 1 := by
  sorry

/-- Conditional on CAD, rational inputs yield a terminating exact confidence
set decomposition or certified endpoint hull with attainability flags. -/
-- @node: thm:finite-complexity-inference
theorem finite_complexity_inference
    (hCAD_of_gate : CylindricalAlgebraicDecompositionQE)
    (m n : ℕ) (ε α : ℝ) (zobs : AggregateSpace m n) :
    (1 ≤ m ∧ 1 ≤ n ∧ ValidConfidenceLevel α ∧
      (∃ e : ℚ, (e : ℝ) = ε) ∧
      (∃ a : ℚ, (a : ℝ) = α)) →
    ∃ cad, CadAlgorithmCorrect cad ∧
      (∀ bprime ∈ stdSimplex ℝ (CountIndex m),
        ∑ z : AggregateSpace m n with exactPValue n bprime z ≤ α,
          multinomialPmf n bprime z ≤ α) ∧
      IsFiniteRationalSemialgebraic (exactMultinomialRegion n α zobs) ∧
      wholeSetConfidenceSet m n ε α zobs ⊆ Set.Icc (-1) 1 ∧
      ∃ out ∈ confidenceSetCadProcedure m n ε α zobs,
        CadCertifiesConfidence cad out ∧
        out.Valid (wholeSetConfidenceSet m n ε α zobs) ∧
        (∀ t, t ∈ out.resultSet ↔
          ∃ witness : ConfidenceAtomWitness m, witness.Valid ε α zobs t) := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds
