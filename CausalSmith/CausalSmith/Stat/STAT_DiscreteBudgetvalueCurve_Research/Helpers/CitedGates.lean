module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Basic

/-! The cited known-reference lower bound used by the two-sample reduction. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory
open scoped BigOperators

/-- A simplex vector has total ENNReal mass one. With [the specified inputs and conditions](hyp:k,R), [the stated relationship holds](goal). -/
lemma simplexMass_sum {k : ℕ} (R : ProbabilitySimplex k) :
    ∑ i : Fin k, ENNReal.ofReal (R.1 i) = 1 :=
  Causalean.Stat.Minimax.Multinomial.TwoSampleL1.simplexMass_sum R

/-- The PMF of a probability-simplex vector. -/
noncomputable abbrev simplexPMF {k : ℕ} (R : ProbabilitySimplex k) : PMF (Fin k) :=
  Causalean.Stat.Minimax.Multinomial.TwoSampleL1.simplexPMF R

/-- The fixed-sample law from a simplex vector. -/
noncomputable abbrev simplexSampleLaw {k : ℕ} (R : ProbabilitySimplex k) (n : ℕ) :
    Measure (Fin n → Fin k) :=
  Causalean.Stat.Minimax.Multinomial.TwoSampleL1.simplexSampleLaw R n

/-- Discrete L1 distance. -/
noncomputable abbrev simplexL1 {k : ℕ} (R S : ProbabilitySimplex k) : ℝ :=
  Causalean.Stat.Minimax.Multinomial.TwoSampleL1.simplexL1 R S

-- @node: simplexL1_nonneg_le_two
/-- The simplex l1 nonneg le two result. It proves [the stated conclusion](goal). -/
lemma simplexL1_nonneg_le_two {k : ℕ} (R S : ProbabilitySimplex k) :
    0 ≤ simplexL1 R S ∧ simplexL1 R S ≤ 2 := by
  simpa only [simplexL1] using
    Causalean.Stat.Minimax.Multinomial.TwoSampleL1.simplexL1_nonneg_le_two R S

-- @node: simplexL1_self
/-- The simplex l1 self result. It proves [the stated conclusion](goal). -/
lemma simplexL1_self {k : ℕ} (R : ProbabilitySimplex k) :
    simplexL1 R R = 0 := by
  simpa only [simplexL1] using
    Causalean.Stat.Minimax.Multinomial.TwoSampleL1.simplexL1_self R

-- @node: simplexL1_symm
/-- The simplex l1 symm result. It proves [the stated conclusion](goal). -/
lemma simplexL1_symm {k : ℕ} (R S : ProbabilitySimplex k) :
    simplexL1 R S = simplexL1 S R := by
  simpa only [simplexL1] using
    Causalean.Stat.Minimax.Multinomial.TwoSampleL1.simplexL1_symm R S

/-- All measurable scalar estimators using the first sample and a known reference vector. -/
abbrev KnownL1Estimator (n k : ℕ) :=
  {f : (Fin n → Fin k) → ℝ // Measurable f}

/-- Fixed-reference L1 squared risk. -/
noncomputable def knownL1Risk {k : ℕ} (n : ℕ) (S : ProbabilitySimplex k)
    (est : KnownL1Estimator n k) (R : ProbabilitySimplex k) : ℝ :=
  ∫ z, (est.1 z - simplexL1 R S) ^ 2 ∂simplexSampleLaw R n

/-- Jiao, Han, and Weissman (2018), *Minimax estimation of the L1 distance*,
Theorem 3, equation (24), and the discussion following Theorem 6;
arXiv:1705.00807v7. The known-reference large-alphabet bound in its stated regime. -/
-- @node: lem:jhw-known-q-l1-lower-regime
def JHWKnownQL1LowerRegime : Sort 0 :=
  ∀ a0 C0 : ℝ, 0 < a0 → ∃ c : ℝ, 0 < c ∧ ∃ k0 : ℕ,
    ∀ k n : ℕ, k0 ≤ k →
      a0 * k / Real.log k ≤ n → Real.log n ≤ C0 * Real.log k →
      c * k / (n * Real.log n) ≤
        sSup (Set.range (fun S : ProbabilitySimplex k =>
          Causalean.Stat.minimaxValueReal (knownL1Risk n S)))

end CausalSmith.Stat.DiscreteBudgetvalueCurve
