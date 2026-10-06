module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Basic
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.Inference
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Causalean.Stat.Bootstrap.EfronResampling.Basic

/-! The independent external score-log experiment and its honest excess-length risk. -/

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

-- @env: S3
variable {ε : ℝ} {J n m : ℕ}
/-- For [the specified mathematical inputs](hyp:ε,J,n,m), [this definition](goal) introduces the corresponding object. -/
abbrev ExternalSample (ε : ℝ) (J n m : ℕ) :=
  TrialSample n J × (Fin m → ScoreSpace ε)
  -- @realizes m(external log size) @realizes Elog(score-log array)

-- @node: def:external-law-class
/-- For [the specified mathematical inputs](hyp:g,P,H), [this definition](goal) introduces the corresponding object. -/
structure ExternalScoreLaw (g : ScoreSpace ε → LabelSpace J)
    (P : Measure (FullRow ε J)) (H : Measure (ScoreSpace ε)) : Prop where
  probabilityP : IsProbabilityMeasure P -- @realizes P(probability normalization)
  probabilityH : IsProbabilityMeasure H -- @realizes H(probability normalization)
  overlap : Overlap ε
  measurableRelease : Measurable g -- @realizes g(measurable release rule)
  scoreMarginal : ScoreMarginal P H
  randomizedAssignment : RandomizedAssignment P
  consistency : Consistency P
  deterministicRelease : DeterministicRelease g P
  -- @realizes Xext(external causal-law pair)
/-- For [the specified mathematical inputs](hyp:g), [this definition](goal) introduces the corresponding object. -/
abbrev ExternalLaws (g : ScoreSpace ε → LabelSpace J) :
    Set (Measure (FullRow ε J) × Measure (ScoreSpace ε)) :=
  {PH | IsProbabilityMeasure PH.1 ∧ IsProbabilityMeasure PH.2 ∧
    ExternalScoreLaw g PH.1 PH.2}
  -- @realizes P(probability normalization) @realizes H(probability normalization)

/-- Given [the stated mathematical inputs and assumptions](hyp:g,PH,hPH), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalLawCellMasses
    (g : ScoreSpace ε → LabelSpace J)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g) :
    CompatibleCellMasses PH.2 g (releasedLaw PH.1) := by
  have hX : ExternalScoreLaw g PH.1 PH.2 := hPH.2.2
  have hRandom : RandomizedCausalLaw PH.2 g PH.1 :=
    ⟨hX.probabilityP, hX.measurableRelease, hX.scoreMarginal,
      hX.randomizedAssignment,
      hX.consistency, hX.deterministicRelease⟩
  exact compatibleCellMasses_of_randomizedCausalLaw PH.2 g PH.1 hRandom

-- @node: ass:external-log-iid
/-- For [the specified mathematical inputs](hyp:g,Qj), [this definition](goal) introduces the corresponding object. -/
def ExternalLogIID (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m)) : Prop :=
  ∀ PH ∈ ExternalLaws g,
    (Qj PH.1 PH.2).map Prod.snd = Measure.pi (fun _ : Fin m => PH.2)

-- @node: ass:external-log-independent
/-- For [the specified mathematical inputs](hyp:g,Qj), [this definition](goal) introduces the corresponding object. -/
def ExternalLogIndependent (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m)) : Prop :=
  ∀ PH ∈ ExternalLaws g,
    Qj PH.1 PH.2 = ((Qj PH.1 PH.2).map Prod.fst).prod
      ((Qj PH.1 PH.2).map Prod.snd)

/-- For [the specified mathematical inputs](hyp:g,Qj), [this definition](goal) introduces the corresponding object. -/
def JointTrialIID (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m)) : Prop :=
  ∀ PH ∈ ExternalLaws g,
    (Qj PH.1 PH.2).map Prod.fst =
      Measure.pi (fun _ : Fin n => releasedLaw PH.1)

-- @node: def:external-experiment
/-- For [the specified mathematical inputs](hyp:n,m,P,H), [this definition](goal) introduces the corresponding object. -/
def externalExperiment (n m : ℕ) (P : Measure (FullRow ε J))
    (H : Measure (ScoreSpace ε)) : Measure (ExternalSample ε J n m) :=
  (Measure.pi (fun _ : Fin n => releasedLaw P)).prod
    (Measure.pi (fun _ : Fin m => H))
  -- @realizes Qext(product trial-log sampling law)

/-- Given [the stated mathematical inputs and assumptions](hyp:g,Qj,hTrial,hLog,hInd,PH,hPH), this result [establishes the stated mathematical conclusion](goal). -/
lemma jointTrialLog_eq_externalExperiment
    (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj) (hLog : ExternalLogIID g Qj)
    (hInd : ExternalLogIndependent g Qj)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g) :
    Qj PH.1 PH.2 = externalExperiment n m PH.1 PH.2 := by
  rw [hInd PH hPH, hTrial PH hPH, hLog PH hPH]
  rfl

/-- For [the specified mathematical inputs](hyp:ε,J,n,m), [this definition](goal) introduces the corresponding object. -/
structure ExternalIntervalProcedure (ε : ℝ) (J n m : ℕ) where
  lo : ExternalSample ε J n m → ℝ -- @realizes Cext(lower endpoint)
  hi : ExternalSample ε J n m → ℝ -- @realizes Cext(upper endpoint)
  measurable_lo : Measurable lo
  measurable_hi : Measurable hi
  lower_bound : ∀ x, -1 ≤ lo x
  ordered : ∀ x, lo x ≤ hi x
  upper_bound : ∀ x, hi x ≤ 1
/-- For [the specified mathematical inputs](hyp:C,x,θ), [this definition](goal) introduces the corresponding object. -/
def ExternalIntervalProcedure.contains
    (C : ExternalIntervalProcedure ε J n m) (x : ExternalSample ε J n m)
    (θ : ℝ) : Prop := θ ∈ Set.Icc (C.lo x) (C.hi x)
/-- For [the specified mathematical inputs](hyp:C,x), [this definition](goal) introduces the corresponding object. -/
def ExternalIntervalProcedure.length
    (C : ExternalIntervalProcedure ε J n m) (x : ExternalSample ε J n m) : ℝ :=
  C.hi x - C.lo x

-- @node: def:external-honest-procedures
/-- For [the specified mathematical inputs](hyp:g,Qj,α), [this definition](goal) introduces the corresponding object. -/
def externalHonestProcedures (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m)) (α : ℝ) :
    Set (ExternalIntervalProcedure ε J n m) :=
  {C | ∀ PH ∈ ExternalLaws g,
    1 - α ≤ (externalExperiment n m PH.1 PH.2).real
      {x | C.contains x (ate PH.1)}}
  -- @realizes Jext(uniformly honest external procedures)

-- @node: def:external-excess-risk
/-- For [the specified mathematical inputs](hyp:g,Qj,α), [this definition](goal) introduces the corresponding object. -/
def externalExcessRisk (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m)) (α : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ C ∈ externalHonestProcedures g Qj α,
    v = sSup {u : ℝ | ∃ PH, ∃ hPH : PH ∈ ExternalLaws g,
      u = ∫ x, max 0 (C.length x -
        sharpATELength PH.2 g (releasedLaw PH.1)
          (externalLawCellMasses g PH hPH))
        ∂(externalExperiment n m PH.1 PH.2)}}
  -- @realizes Rext(minimax expected positive excess length)
/-- For [the specified mathematical inputs](hyp:n,m), [this definition](goal) introduces the corresponding object. -/
def externalNormalizer (n m : ℕ) : ℝ :=
  ((Real.sqrt (n : ℝ))⁻¹ + (Real.sqrt (m : ℝ))⁻¹)⁻¹
  -- @realizes bext(two-sample root-rate normalizer)

-- @node: def:external-normalized-risk
/-- For [the specified mathematical inputs](hyp:g,Qj,α), [this definition](goal) introduces the corresponding object. -/
def externalNormalizedRisk (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m)) (α : ℝ) : ℝ :=
  externalNormalizer n m * externalExcessRisk g Qj α
  -- @realizes Text(normalized two-sample excess risk)

end
end CausalSmith.PartialID.UnlinkedPropensityAte
