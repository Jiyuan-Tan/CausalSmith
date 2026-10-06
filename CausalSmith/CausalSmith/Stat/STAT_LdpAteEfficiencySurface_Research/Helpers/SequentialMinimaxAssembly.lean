module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotRates
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Procedures

/-! # Structural assembly for sequential minimaxity

This file packages the elementary order-theoretic and pilot-rate steps used to
assemble the sequential local asymptotic minimax theorem.  In particular, the
infimum argument only needs a universal risk lower bound and one regular
procedure attaining that bound.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open scoped ENNReal

/-- The risks achieved by regular sequential procedures over arbitrary measurable output families. For the displayed inputs and conditions, the stated result follows. [The regular Procedure Risk Set](goal) is determined by [the displayed parameters](hyp:θ,p,ε). -/
@[no_expose]
def regularProcedureRiskSet (θ : TrialParameter) (p ε : ℝ) : Set ℝ≥0∞ :=
  {u | ∃ Z : OutputFamily,
    ∃ mZ : ∀ n i, MeasurableSpace (Z n i),
      letI := mZ
      ∃ P : ProcedureSequence Z ε,
        RegularProcedure P θ p ∧
        u = localAsymptoticRisk P θ p}

/-- The integer square-root pilot simultaneously diverges and is sublinear. [The stated result](goal) follows. -/
lemma natSqrt_pilotRates :
    PilotDiverges Nat.sqrt ∧ PilotSublinear Nat.sqrt :=
  ⟨natSqrt_pilotDiverges, natSqrt_pilotSublinear⟩

/-- A universal lower bound for procedure risk is a lower bound for the risks
of regular procedures. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:hlower), these specify the stated inputs. -/
lemma lowerBound_regularProcedureRiskSet {θ : TrialParameter} {p ε v : ℝ}
    (hlower : ∀ (Z : OutputFamily) [∀ n i, MeasurableSpace (Z n i)]
      (P : ProcedureSequence Z ε),
        ENNReal.ofReal v ≤ localAsymptoticRisk P θ p) :
    ∀ u ∈ regularProcedureRiskSet θ p ε, ENNReal.ofReal v ≤ u := by
  rintro u ⟨Z, mZ, P, -, rfl⟩
  let _ : ∀ n i, MeasurableSpace (Z n i) := mZ
  exact hlower Z P

/-- The risk of any displayed regular procedure belongs to the regular risk
set. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:Z,mZ,P,hregular), these specify the stated inputs. -/
lemma localAsymptoticRisk_mem_regularProcedureRiskSet
    {θ : TrialParameter} {p ε : ℝ}
    (Z : OutputFamily) (mZ : ∀ n i, MeasurableSpace (Z n i))
    (P : @ProcedureSequence Z mZ ε) (hregular : RegularProcedure P θ p) :
    localAsymptoticRisk P θ p ∈ regularProcedureRiskSet θ p ε := by
  refine ⟨Z, mZ, ?_⟩
  let _ : ∀ n i, MeasurableSpace (Z n i) := mZ
  exact ⟨P, hregular, rfl⟩

/-- If every procedure has risk at least the target and one regular procedure
attains it, then the infimum over regular risks equals the target. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:hlower,Z,mZ,P,hregular,hattains), these specify the stated inputs. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma sInf_regularProcedureRiskSet_eq_of_lowerBound_of_attained
    {θ : TrialParameter} {p ε v : ℝ}
    (hlower : ∀ (Z : OutputFamily) [∀ n i, MeasurableSpace (Z n i)]
      (P : ProcedureSequence Z ε),
        ENNReal.ofReal v ≤ localAsymptoticRisk P θ p)
    (Z : OutputFamily) (mZ : ∀ n i, MeasurableSpace (Z n i))
    (P : @ProcedureSequence Z mZ ε) (hregular : RegularProcedure P θ p)
    (hattains : localAsymptoticRisk P θ p = ENNReal.ofReal v) :
    sInf (regularProcedureRiskSet θ p ε) = ENNReal.ofReal v := by
  apply le_antisymm
  · apply sInf_le
    rw [← hattains]
    exact localAsymptoticRisk_mem_regularProcedureRiskSet Z mZ P hregular
  · apply le_sInf
    exact lowerBound_regularProcedureRiskSet hlower

end CausalSmith.Stat.LdpAteEfficiencySurface
