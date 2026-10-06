module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Basic
public import Causalean.PO.ID.Partial.Inference.IntervalCI

/-! Finite-sample honest intervals for the known-score experiment. -/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

-- @env: S2
variable {ε : ℝ} {K n : ℕ}
/-- For [the specified mathematical inputs](hyp:n,K), [this definition](goal) introduces the corresponding object. -/
abbrev TrialSample (n K : ℕ) := Fin n → Observation K
  -- @realizes n(trial sample size)

/-- For [the specified mathematical inputs](hyp:n,K), [this definition](goal) introduces the corresponding object. -/
structure IntervalProcedure (n K : ℕ) where
  lo : TrialSample n K → ℝ -- @realizes Cn(lower endpoint map)
  hi : TrialSample n K → ℝ -- @realizes Cn(upper endpoint map)
  measurable_lo : Measurable lo
  measurable_hi : Measurable hi
  lower_bound : ∀ x, -1 ≤ lo x
  ordered : ∀ x, lo x ≤ hi x
  upper_bound : ∀ x, hi x ≤ 1
/-- For [the specified mathematical inputs](hyp:C,x,θ), [this definition](goal) introduces the corresponding object. -/
def IntervalProcedure.contains (C : IntervalProcedure n K) (x : TrialSample n K)
    (θ : ℝ) : Prop := θ ∈ Set.Icc (C.lo x) (C.hi x)
/-- For [the specified mathematical inputs](hyp:C,x), [this definition](goal) introduces the corresponding object. -/
def IntervalProcedure.length (C : IntervalProcedure n K) (x : TrialSample n K) : ℝ :=
  C.hi x - C.lo x

/-- For [the specified mathematical inputs](hyp:ε,K,r), [this definition](goal) introduces the corresponding object. -/
def equalWidthMidpoint (ε : ℝ) (K : ℕ) (r : LabelSpace K) : ℝ :=
  ε + ((r.val : ℝ) + 1 / 2) * (1 - 2 * ε) / K

/-- For [the specified mathematical inputs](hyp:ε,n,K,x), [this definition](goal) introduces the corresponding object. -/
def midpointWeightedCenter (ε : ℝ) (n K : ℕ)
    (x : TrialSample n K) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n,
    if (x i).2.1 then
      ((x i).2.2 : ℝ) / equalWidthMidpoint ε K (x i).1
    else -((x i).2.2 : ℝ) /
      (1 - equalWidthMidpoint ε K (x i).1)

/-- For [the specified mathematical inputs](hyp:ε,α,n,K), [this definition](goal) introduces the corresponding object. -/
def midpointWeightedRadius (ε α : ℝ) (n K : ℕ) : ℝ :=
  (4 / ε) * Real.sqrt (Real.log (4 / α) / n) +
    (1 - 2 * ε) / (2 * K * ε * (1 - ε))
/-- For [the specified mathematical inputs](hyp:x), [this definition](goal) introduces the corresponding object. -/
def clampATE (x : ℝ) : ℝ := max (-1) (min 1 x)

-- @node: ass:iid-trial-sampling
/-- For [the specified mathematical inputs](hyp:trialLaw), [this definition](goal) introduces the corresponding object. -/
def IIDTrialSampling (trialLaw : Measure (FullRow ε K) → Measure (TrialSample n K)) :
    Prop :=
  ∀ P : Measure (FullRow ε K), IsProbabilityMeasure P →
    trialLaw P = Measure.pi (fun _ : Fin n => releasedLaw P)

-- @node: def:honest-procedures
/-- For [the specified mathematical inputs](hyp:n,K,H,α), [this definition](goal) introduces the corresponding object. -/
def honestProcedures (n K : ℕ) (H : Measure (ScoreSpace ε))
    (α : ℝ) : Set ((ScoreSpace ε → LabelSpace K) × IntervalProcedure n K) :=
  {gC | gC.1 ∈ kLabelReleases ε K ∧
    ∀ P ∈ CausalLaws H gC.1,
      1 - α ≤ (Measure.pi (fun _ : Fin n => releasedLaw P)).real
        {x | gC.2.contains x (ate P)}}
  -- @realizes alpha(miscoverage level) @realizes Jhonest(uniform honest pair class)

-- @node: def:minimax-honest-length
/-- For [the specified mathematical inputs](hyp:n,K,H,α), [this definition](goal) introduces the corresponding object. -/
def minimaxHonestLength (n K : ℕ) (H : Measure (ScoreSpace ε))
    (α : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ gC ∈ honestProcedures n K H α,
    v = sSup {u : ℝ | ∃ P ∈ CausalLaws H gC.1,
      u = ∫ x, gC.2.length x ∂(Measure.pi (fun _ : Fin n => releasedLaw P))}}
  -- @realizes Lminimax(infimum of worst-case expected length)

end
end CausalSmith.PartialID.UnlinkedPropensityAte
