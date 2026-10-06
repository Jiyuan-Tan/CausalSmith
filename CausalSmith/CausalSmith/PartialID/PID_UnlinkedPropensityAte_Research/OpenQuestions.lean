module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerCertificate
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.Projection

/-! Open normalized external-score limit question. -/

@[expose] public section

open MeasureTheory Set Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

-- keep: generic functional needed to state the open subclass question without selecting a subclass.
/-- For [the specified mathematical inputs](hyp:ε,J,n,m,X,Qj,α), [this definition](goal) introduces the corresponding object. -/
def externalHonestProceduresOn {ε : ℝ} {J n m : ℕ}
    (X : Set (Measure (FullRow ε J) × Measure (ScoreSpace ε)))
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m)) (α : ℝ) :
    Set (ExternalIntervalProcedure ε J n m) :=
  {C | ∀ PH ∈ X,
    1 - α ≤ (Qj PH.1 PH.2).real {x | C.contains x (ate PH.1)}}

-- keep: generic functional needed to state the open subclass question without selecting a subclass.
/-- For [the external model, subclass, sampling law, and miscoverage inputs](hyp:ε,J,n,m,g,X,hX,Qj,α), [this definition gives the minimax expected positive excess length with honesty and the risk supremum restricted to the same subclass](goal). -/
noncomputable def externalExcessRiskOn {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J)
    (X : Set (Measure (FullRow ε J) × Measure (ScoreSpace ε)))
    (hX : X ⊆ ExternalLaws g)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m)) (α : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ C ∈ externalHonestProceduresOn X Qj α,
    v = sSup {u : ℝ | ∃ PH, ∃ hPH : PH ∈ X,
      u = ∫ x, max 0 (C.length x -
        sharpATELength PH.2 g (releasedLaw PH.1)
          (externalLawCellMasses g PH (hX hPH))) ∂(Qj PH.1 PH.2)}}

-- keep: generic functional needed to state the open subclass question without selecting a subclass.
/-- For [the sample sizes, external model, subclass, sampling law, and miscoverage inputs](hyp:ε,J,n,m,g,X,hX,Qj,α), [this definition normalizes the subclass-restricted excess risk by the two-sample root-rate factor](goal). -/
noncomputable def externalNormalizedRiskOn {ε : ℝ} {J : ℕ}
    (n m : ℕ) (g : ScoreSpace ε → LabelSpace J)
    (X : Set (Measure (FullRow ε J) × Measure (ScoreSpace ε)))
    (hX : X ⊆ ExternalLaws g)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m)) (α : ℝ) : ℝ :=
  externalNormalizer n m * externalExcessRiskOn g X hX Qj α

-- @node: oeq:external-score-projection
/-- For [the specified mathematical inputs](hyp:ε,J,g,α,_hg,_hα), [this definition](goal) introduces the corresponding object. -/
def ExternalSharpLimitQuestion {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (_hg : Measurable g) (_hα : 0 < α ∧ α < 1 / 2) : String :=
  "For each rho>0, determine the liminf and limsup of T_{n,m,alpha}(g) \
   as n,m→∞ and n/m→rho over ExternalLaws(g), using the product \
   externalExperiment and uniformly honest procedures. Decide whether the \
   values coincide and compute their common sharp value if so. If the full-class \
   sharp limit fails, identify an explicitly defined regular subclass of \
   ExternalLaws(g), state its regularity conditions, and determine its common \
   sharp limit for every rho>0. Restrict both uniform honesty and the supremum \
   in expected excess length to that same subclass. Use the external projection \
   handle to construct an attaining procedure or counterexample. This is an open \
   request, not an assertion or a greatest-subclass claim."

end CausalSmith.PartialID.UnlinkedPropensityAte
