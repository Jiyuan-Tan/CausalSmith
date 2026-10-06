module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Basic
public import Mathlib.MeasureTheory.Function.Floor

/-! Equal width finite label releases. -/

@[expose] public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,K,hK,e), [this definition](goal) introduces the corresponding object. -/
def equalWidthRelease (ε : ℝ) (K : ℕ) (hK : 0 < K)
    (e : ScoreSpace ε) : LabelSpace K :=
  ⟨min (Nat.floor ((K : ℝ) * ((e : ℝ) - ε) / (1 - 2 * ε)))
    (K - 1), by omega⟩

-- @node: equalWidthRelease_measurable
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,hK), this result [establishes the stated mathematical conclusion](goal). -/
lemma equalWidthRelease_measurable (ε : ℝ) (K : ℕ) (hK : 0 < K) :
    Measurable (equalWidthRelease ε K hK) := by
  let f : ℕ → Fin K := fun n => ⟨min n (K - 1), by omega⟩
  have hf : Measurable f := measurable_of_countable f
  have hfloor : Measurable (fun e : ScoreSpace ε =>
      Nat.floor ((K : ℝ) * ((e : ℝ) - ε) / (1 - 2 * ε))) :=
    Measurable.nat_floor (by fun_prop)
  convert hf.comp hfloor using 1
  funext e
  rfl

end
end CausalSmith.PartialID.UnlinkedPropensityAte
