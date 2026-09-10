import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.Scan
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TSharpRegretFormula

/-! Correctness, constructive endpoint attainment, and linear resources for the scan. -/

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

def ScanEntryAttains (F : FiniteScoreModel) (e : ScanEntry) : Prop :=
  ∃ (t : EReal) (ht : t ∈ F.toModel.T), inducedPolicyIndex F t = e.policyIndex ∧
    ∃ (u : EReal) (hu : u ∈ F.toModel.T), inducedPolicyIndex F u = e.comparatorIndex ∧
      e.regret = regretAt F.toModel ⟨t, ht⟩ ∧
      ∃ ν, DominatedAllocation F.toModel ν ∧
        ((u < t ∧ e.directionForward = true ∧
            e.regret = leftRegretTerm F.toModel ⟨u, hu⟩ ⟨t, ht⟩ ∧
            allocationMass (cutoffInterval u t) ν =
              massUpper F.toModel (cutoffInterval u t)) ∨
         (t = u ∧ e.regret = 0) ∨
         (t < u ∧ e.directionForward = false ∧
            e.regret = rightRegretTerm F.toModel ⟨t, ht⟩ ⟨u, hu⟩ ∧
            allocationMass (cutoffInterval t u) ν =
              massLower F.toModel (cutoffInterval t u))) ∧
        (∀ r side, e.allocationCoefficient r side ∈ Set.Icc (0 : ℝ) 1) ∧
        (let I := if e.directionForward then cutoffInterval u t else cutoffInterval t u
         ∀ r,
           (ν r).real I = e.allocationCoefficient r true * (obsMeasure F.toModel r).real I ∧
           (ν r).real (I : Set ℝ)ᶜ =
             e.allocationCoefficient r false *
               (obsMeasure F.toModel r).real (I : Set ℝ)ᶜ)

def ScanInputRealizes (F : FiniteScoreModel) (input : ScanInput F.toModel) : Prop :=
  input.m = F.m ∧
  (∀ r j, input.prefixes r j = prefixMass F r j) ∧
  input.a = diseaseMass F.toModel ∧ input.q = obsMass F.toModel ∧
  input.b = F.toModel.b ∧ input.c = F.toModel.c ∧
  input.indices = policyIndices F ∧
  (∀ j ∈ input.indices,
    inducedPolicyIndex F (input.representative j) = j)

def ScanCorrect (F : FiniteScoreModel) : Prop :=
  ∃ input : ScanInput F.toModel, ScanInputRealizes F input ∧
    let run := scan input
    let out := run.entries
    out.map ScanEntry.policyIndex = input.indices ∧
    (∀ j ∈ input.indices, ∃! e,
      e ∈ out ∧ e.policyIndex = j ∧ ScanEntryAttains F e) ∧
    run.operations ≤ 64 * (input.m + input.indices.length) ∧
    run.peakMemory ≤ 12 * (input.m + 1) ∧
    (input.indices = List.range (input.m + 1) →
      out.length = input.m + 1)

-- @node: thm:linear-whole-curve-scan
theorem linear_whole_curve_scan (M : ImperfectReferenceModel)
    (m : ℕ) (x : Fin m → ℝ) (hfinite : FiniteScoreSupport M m x)
    (hb : PositiveBenefit M) (hc : PositiveCost M)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M) :
    ScanCorrect { toModel := M, m := m, x := x, support := hfinite } := by sorry

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
