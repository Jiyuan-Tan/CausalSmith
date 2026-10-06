module
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Basic
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.T_minimax_lower
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Score-threshold overlap regret — accepted-bank cited gate

The concrete potential-outcome law uses Mathlib measures.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

/-- CausalSmith research bank (2026), accepted specialization `stat_policy_regret_margin_overlap/v1`,
`ass:overlap-decay`, `def:exponents`, `thm:rate-characterization`.
The carrier records only the cited lower-bound headline with the bank theorem's exact
admissibility hypotheses; the envelope and exponent formulas are local definitions. -/
noncomputable def bankMinimaxRegret (α γ u0 cB Cm Co co underlineP : ℝ)
    (policySet : Set (CausalSmith.Stat.PolicyRegretMarginOverlap.Policy ℝ)) (n : ℕ) : ℝ :=
  CausalSmith.Stat.PolicyRegretMarginOverlap.minimaxRegret
    {P : CausalSmith.Stat.PolicyRegretMarginOverlap.ObservedLaw ℝ |
      CausalSmith.Stat.PolicyRegretMarginOverlap.LawClass α γ Cm u0 Co co underlineP policySet P}
    policySet n

-- @node: lem:banked-local-substrate
/-- CausalSmith research bank (2026), accepted `stat_policy_regret_margin_overlap/v1`;
locator: `ass:overlap-decay`, `def:exponents`, `thm:rate-characterization`.
Cited logical lower-bound claim, conditional on the bank theorem's own exact inputs. -/
def BankedLocalSubstrate : Sort 0 :=
  ∀ (α γ u0 cB Cm Co co underlineP : ℝ)
    (policySet : Set (CausalSmith.Stat.PolicyRegretMarginOverlap.Policy ℝ)),
    CausalSmith.Stat.PolicyRegretMarginOverlap.MarginWindow u0 →
    0 ≤ α → 0 ≤ γ → 0 < Cm → 0 < Co → 0 < co → 0 < cB →
    cB ≤ Cm → cB ≤ Co → 0 < underlineP →
    (0 < γ → 0 < α → cB ≤ Co*co^(-(α/γ))) →
    (0 < γ → α = 0 → cB ≤ Co*(4:ℝ)^(-(1/γ))) →
    underlineP ≤ 1/4 → 8*cB < Real.log 5 →
    policySet.Nonempty → (∀ π ∈ policySet, Measurable π) →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      bankMinimaxRegret α γ u0 cB Cm Co co underlineP policySet n
        ≥ c*(n:ℝ)^(-rBank α γ)

/-- The accepted policy-regret bank supplies the cited local lower-bound substrate. -/
theorem bankedLocalSubstrate_proved : BankedLocalSubstrate := by
  intro α γ u0 cB Cm Co co underlineP policySet hwin hα hγ hCm hCo hco hcB
    hcBm hcBo hup hcB_gpos hcB_gzero huple hsmall hπnonempty hπmeas
  simpa [bankMinimaxRegret, rBank, bankD, bankBeta,
    CausalSmith.Stat.PolicyRegretMarginOverlap.rStar,
    CausalSmith.Stat.PolicyRegretMarginOverlap.Dag,
    CausalSmith.Stat.PolicyRegretMarginOverlap.betaAG] using
    CausalSmith.Stat.PolicyRegretMarginOverlap.rate_characterization
      α γ u0 cB Cm Co co underlineP policySet hwin hα hγ hCm hCo hco hcB hcBm hcBo
        hup hcB_gpos hcB_gzero huple hsmall hπnonempty hπmeas

end CausalSmith.Stat.ScorethresholdOverlapRegret
