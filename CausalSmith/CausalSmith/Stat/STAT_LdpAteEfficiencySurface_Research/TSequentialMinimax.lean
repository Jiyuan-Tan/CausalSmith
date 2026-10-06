module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotLocalRiskAttainment
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotRates
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Procedures
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Refinement
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialDomination
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialLowerBound
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialMinimaxAssembly
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialScore
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TPilotAttainment
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.Main

/-! # Sequential local asymptotic minimax equality

The lower bound covers every history-dependent private procedure on arbitrary
measurable output spaces, whether regular or not. A single private-pilot
sequence is regular and attains the bound, giving the infimum equality. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- For the supplied quantities and conditions, the regular risk set is the mathematical object specified below. [The regular Risk Set](goal) is determined by [the displayed parameters](hyp:θ,p,ε). -/
def regularRiskSet (θ : TrialParameter) (p ε : ℝ) : Set ℝ≥0∞ :=
  {u | ∃ Z : OutputFamily,
    ∃ mZ : ∀ n i, MeasurableSpace (Z n i),
      letI := mZ
      ∃ P : ProcedureSequence Z ε,
        RegularProcedure P θ p ∧
        u = localAsymptoticRisk P θ p}

-- @node: thm:sequential-minimax
/-- Under the supplied quantities and conditions, the sequential minimax assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hfixed,hselect), [the sequential minimax](goal).

Under the stated assumptions, the sequential minimax. -/
theorem sequential_minimax
    (θ0 : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ0)
    -- @realizes \theta_0(interior local parameter point)
    (epsSeq : ℕ → ℝ) (hfixed : FixedPrivacy epsSeq ε)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (hselect : StrongSaddleSelection p ε select) :
    (∀ (Z : OutputFamily) [∀ n i, MeasurableSpace (Z n i)]
      (P : ProcedureSequence Z ε),
        ENNReal.ofReal (Vstar θ0 p ε) ≤
          localAsymptoticRisk P θ0 p) ∧
    (∃ m : ℕ → ℕ,
      m = Nat.sqrt ∧ PilotDiverges m ∧ PilotSublinear m ∧
      RegularProcedure (pilotEstimator p ε m select hselect hp hfixed.1) θ0 p ∧
      localAsymptoticRisk (pilotEstimator p ε m select hselect hp hfixed.1) θ0 p =
        ENNReal.ofReal (Vstar θ0 p ε)) ∧
    sInf (regularRiskSet θ0 p ε) =
      ENNReal.ofReal (Vstar θ0 p ε) := by
  have hlower : ∀ (Z : OutputFamily) [∀ n i, MeasurableSpace (Z n i)]
      (P : ProcedureSequence Z ε),
      ENNReal.ofReal (Vstar θ0 p ε) ≤ localAsymptoticRisk P θ0 p := by
    intro Z mZ P
    exact sequential_localAsymptoticRisk_lower_bound P θ0 p hp hθ hfixed.1
  have hrates := natSqrt_pilotRates
  have hpilot := pilot_attainment θ0 p ε (1 / 2) hp hθ
    epsSeq hfixed select hselect (by norm_num) Nat.sqrt hrates.1 hrates.2
  have hregular : RegularProcedure
      (pilotEstimator p ε Nat.sqrt select hselect hp hfixed.1) θ0 p :=
    hpilot.2.2.2.2.1
  have hrisk : localAsymptoticRisk
      (pilotEstimator p ε Nat.sqrt select hselect hp hfixed.1) θ0 p =
      ENNReal.ofReal (Vstar θ0 p ε) :=
    pilot_localAsymptoticRisk_eq select θ0 p ε Nat.sqrt hselect hp hθ hfixed.1
      hrates.1 hrates.2
  refine ⟨hlower, ?_, ?_⟩
  · exact ⟨Nat.sqrt, rfl, hrates.1, hrates.2, hregular, hrisk⟩
  · apply le_antisymm
    · apply sInf_le
      refine ⟨pilotOutputFamily, (fun _ _ => inferInstance), ?_⟩
      let _ : ∀ n i, MeasurableSpace (pilotOutputFamily n i) :=
        fun _ _ => inferInstance
      exact ⟨pilotEstimator p ε Nat.sqrt select hselect hp hfixed.1,
        hregular, hrisk.symm⟩
    · apply le_sInf
      rintro u ⟨Z, mZ, P, -, rfl⟩
      let _ : ∀ n i, MeasurableSpace (Z n i) := mZ
      exact hlower Z P

end CausalSmith.Stat.LdpAteEfficiencySurface
