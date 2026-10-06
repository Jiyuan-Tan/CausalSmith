module
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Causalean.Stat.Quantile.Quantile

/-! Law-level primitives for the unlinked propensity-score ATE problem. -/

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

-- @env: S1
variable {ε : ℝ} {J : ℕ}
/-- For [the specified mathematical inputs](hyp:ε), [this definition](goal) introduces the corresponding object. -/
abbrev ScoreSpace (ε : ℝ) := Set.Icc ε (1 - ε) -- @realizes Espace(score support)
/-- [This definition](goal) introduces the corresponding mathematical object. -/
abbrev OutcomeSpace := Set.Icc (0 : ℝ) 1 -- @realizes Yspace(outcome support)
/-- [This definition](goal) introduces the corresponding mathematical object. -/
abbrev ArmSpace := Bool -- @realizes Aspace(binary treatment) @realizes a(arm index)
/-- For [the specified mathematical inputs](hyp:J), [this definition](goal) introduces the corresponding object. -/
abbrev LabelSpace (J : ℕ) := Fin J -- @realizes Rspace(label alphabet) @realizes J(label count)
/-- For [the specified mathematical inputs](hyp:ε,J), [this definition](goal) introduces the corresponding object. -/
abbrev FullRow (ε : ℝ) (J : ℕ) :=
  ScoreSpace ε × OutcomeSpace × OutcomeSpace × ArmSpace × OutcomeSpace × LabelSpace J
  -- @realizes P(full-law carrier)
/-- For [the specified mathematical inputs](hyp:J), [this definition](goal) introduces the corresponding object. -/
abbrev Observation (J : ℕ) := LabelSpace J × ArmSpace × OutcomeSpace
  -- @realizes Prel(released-law carrier)
/-- For [the specified mathematical inputs](hyp:ω), [this definition](goal) introduces the corresponding object. -/
def score (ω : FullRow ε J) : ScoreSpace ε := ω.1 -- @realizes E(score coordinate)
/-- For [the specified mathematical inputs](hyp:ω), [this definition](goal) introduces the corresponding object. -/
def outcome0 (ω : FullRow ε J) : OutcomeSpace := ω.2.1 -- @realizes Y0(control outcome)
/-- For [the specified mathematical inputs](hyp:ω), [this definition](goal) introduces the corresponding object. -/
def outcome1 (ω : FullRow ε J) : OutcomeSpace := ω.2.2.1 -- @realizes Y1(treated outcome)
/-- For [the specified mathematical inputs](hyp:ω), [this definition](goal) introduces the corresponding object. -/
def arm (ω : FullRow ε J) : ArmSpace := ω.2.2.2.1 -- @realizes A(assigned arm)
/-- For [the specified mathematical inputs](hyp:ω), [this definition](goal) introduces the corresponding object. -/
def observed (ω : FullRow ε J) : OutcomeSpace := ω.2.2.2.2.1 -- @realizes Y(observed outcome)
/-- For [the specified mathematical inputs](hyp:ω), [this definition](goal) introduces the corresponding object. -/
def label (ω : FullRow ε J) : LabelSpace J := ω.2.2.2.2.2 -- @realizes R(released label)
/-- For [the specified mathematical inputs](hyp:ω), [this definition](goal) introduces the corresponding object. -/
def releasedRecord (ω : FullRow ε J) : Observation J :=
  (label ω, arm ω, observed ω)
/-- For [the specified mathematical inputs](hyp:P), [this definition](goal) introduces the corresponding object. -/
def releasedLaw (P : Measure (FullRow ε J)) : Measure (Observation J) :=
  P.map releasedRecord
  -- @realizes Prel(law of released R,A,Y)
/-- For [the specified mathematical inputs](hyp:P), [this definition](goal) introduces the corresponding object. -/
def ate (P : Measure (FullRow ε J)) : ℝ :=
  ∫ ω, ((outcome1 ω : ℝ) - (outcome0 ω : ℝ)) ∂P
  -- @realizes theta(mean Y1−Y0)

-- @node: ass:overlap
/-- For [the specified mathematical inputs](hyp:ε), [this definition](goal) introduces the corresponding object. -/
def Overlap (ε : ℝ) : Prop := 0 < ε ∧ ε < 1 / 2
  -- @realizes epsilon(overlap range)

-- @node: ass:score-marginal
/-- For [the specified mathematical inputs](hyp:P,H), [this definition](goal) introduces the corresponding object. -/
def ScoreMarginal (P : Measure (FullRow ε J)) (H : Measure (ScoreSpace ε)) : Prop :=
  P.map score = H -- @realizes H(score-law carrier and marginal)

-- @node: ass:randomized-assignment
/-- For [the specified mathematical inputs](hyp:P), [this definition](goal) introduces the corresponding object. -/
def RandomizedAssignment (P : Measure (FullRow ε J)) : Prop :=
  ∀ B : Set (ScoreSpace ε × OutcomeSpace × OutcomeSpace), MeasurableSet B →
    P.real {ω | arm ω = true ∧ (score ω, outcome0 ω, outcome1 ω) ∈ B} =
      ∫ ω in {ω | (score ω, outcome0 ω, outcome1 ω) ∈ B}, (score ω : ℝ) ∂P
  -- @realizes p(conditional Bernoulli assignment by score)

-- @node: ass:consistency
/-- For [the specified mathematical inputs](hyp:P), [this definition](goal) introduces the corresponding object. -/
def Consistency (P : Measure (FullRow ε J)) : Prop :=
  ∀ᵐ ω ∂P, observed ω = if arm ω then outcome1 ω else outcome0 ω

-- @node: ass:deterministic-release
/-- For [the specified mathematical inputs](hyp:g,P), [this definition](goal) introduces the corresponding object. -/
def DeterministicRelease (g : ScoreSpace ε → LabelSpace J)
    (P : Measure (FullRow ε J)) : Prop :=
  ∀ᵐ ω ∂P, label ω = g (score ω)
  -- @realizes g(deterministic release rule)

-- @node: ass:released-law
/-- For [the specified mathematical inputs](hyp:P,Prel), [this definition](goal) introduces the corresponding object. -/
def ReleasedLaw (P : Measure (FullRow ε J))
    (Prel : Measure (Observation J)) : Prop :=
  releasedLaw P = Prel

-- @node: def:causal-law-class
/-- For [the specified mathematical inputs](hyp:H,g,P), [this definition](goal) introduces the corresponding object. -/
structure RandomizedCausalLaw (H : Measure (ScoreSpace ε))
    (g : ScoreSpace ε → LabelSpace J) (P : Measure (FullRow ε J)) : Prop where
  probability : IsProbabilityMeasure P -- @realizes P(probability normalization)
  measurableRelease : Measurable g -- @realizes g(measurable release rule)
  scoreMarginal : ScoreMarginal P H
  randomizedAssignment : RandomizedAssignment P
  consistency : Consistency P
  deterministicRelease : DeterministicRelease g P
  -- @realizes Pclass(four causal-law conditions)

-- @node: def:compatible-law-class
/-- For [the specified mathematical inputs](hyp:H,g,Prel,P), [this definition](goal) introduces the corresponding object. -/
structure CompatibleCausalLaw (H : Measure (ScoreSpace ε))
    (g : ScoreSpace ε → LabelSpace J) (Prel : Measure (Observation J))
    (P : Measure (FullRow ε J)) : Prop where
  probability : IsProbabilityMeasure P -- @realizes P(probability normalization)
  measurableRelease : Measurable g -- @realizes g(measurable release rule)
  scoreMarginal : ScoreMarginal P H
  randomizedAssignment : RandomizedAssignment P
  consistency : Consistency P
  deterministicRelease : DeterministicRelease g P
  releasedLaw : ReleasedLaw P Prel
  -- @realizes Mclass(causal laws with released margin)
/-- For [the specified mathematical inputs](hyp:H,g), [this definition](goal) introduces the corresponding object. -/
abbrev CausalLaws (H : Measure (ScoreSpace ε))
    (g : ScoreSpace ε → LabelSpace J) : Set (Measure (FullRow ε J)) :=
  {P | IsProbabilityMeasure P ∧ RandomizedCausalLaw H g P}
  -- @realizes P(probability normalization)
/-- For [the specified mathematical inputs](hyp:H,g,Prel), [this definition](goal) introduces the corresponding object. -/
abbrev CompatibleLaws (H : Measure (ScoreSpace ε))
    (g : ScoreSpace ε → LabelSpace J) (Prel : Measure (Observation J)) :
    Set (Measure (FullRow ε J)) :=
  {P | IsProbabilityMeasure P ∧ CompatibleCausalLaw H g Prel P}

-- @node: ass:density-lower
/-- For [the specified mathematical inputs](hyp:H,f,mf), [this definition](goal) introduces the corresponding object. -/
def DensityLower (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ)
    (mf : ℝ) : Prop :=
  Measurable f ∧ -- @realizes f(measurable density)
  H = ((volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ)).withDensity
      (fun e => ENNReal.ofReal (f e)) ∧ -- @realizes H(density law) @realizes f(density formula)
    ∀ᵐ e ∂((volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ)), mf ≤ f e
    -- @realizes mf(a.e. lower density bound)

/-- For [the specified mathematical inputs](hyp:f,Mf), [this definition](goal) introduces the corresponding object. -/
def DensityUpper (f : ScoreSpace ε → ℝ) (Mf : ℝ) : Prop :=
  ∀ᵐ e ∂((volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ)), f e ≤ Mf

-- @node: def:score-lower-density-class
/-- For [the specified mathematical inputs](hyp:H,f,mf), [this definition](goal) introduces the corresponding object. -/
structure LowerScoreDensity (H : Measure (ScoreSpace ε))
    (f : ScoreSpace ε → ℝ) (mf : ℝ) : Prop where
  probability : IsProbabilityMeasure H -- @realizes H(probability score law)
  densityLower : DensityLower H f mf

/-- For [the specified mathematical inputs](hyp:H,f,mf,Mf), [this definition](goal) introduces the corresponding object. -/
structure BoundedScoreDensity (H : Measure (ScoreSpace ε))
    (f : ScoreSpace ε → ℝ) (mf Mf : ℝ) : Prop where
  probability : IsProbabilityMeasure H -- @realizes H(probability normalization)
  densityLower : DensityLower H f mf
  densityUpper : DensityUpper f Mf
/-- For [the specified mathematical inputs](hyp:a,e), [this definition](goal) introduces the corresponding object. -/
def armProb (a : ArmSpace) (e : ScoreSpace ε) : ℝ :=
  if a then (e : ℝ) else 1 - (e : ℝ) -- @realizes p(arm-specific score probability)
/-- For [the specified mathematical inputs](hyp:g,r), [this definition](goal) introduces the corresponding object. -/
def cell (g : ScoreSpace ε → LabelSpace J) (r : LabelSpace J) : Set (ScoreSpace ε) :=
  {e | g e = r} -- @realizes C(release cell)
/-- For [the specified mathematical inputs](hyp:H,g,a,r), [this definition](goal) introduces the corresponding object. -/
def armCellMass (H : Measure (ScoreSpace ε))
    (g : ScoreSpace ε → LabelSpace J) (a : ArmSpace) (r : LabelSpace J) : ℝ :=
  ∫ e in cell g r, armProb a e ∂H -- @realizes q(arm-cell mass)

/-- For [the specified mathematical inputs](hyp:H,g,Prel), [this definition](goal) introduces the corresponding object. -/
def CompatibleCellMasses (H : Measure (ScoreSpace ε))
    (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) : Prop :=
  IsProbabilityMeasure H ∧ -- @realizes H(probability score law)
  IsProbabilityMeasure Prel ∧ -- @realizes Prel(probability released law)
  Measurable g ∧ -- @realizes g(measurable release rule)
  ∀ a r, Prel.real {z | z.1 = r ∧ z.2.1 = a} = armCellMass H g a r
  -- @realizes q(all released arm-cell masses agree with score masses)

/-- Given [the stated mathematical inputs and assumptions](hyp:H,g,P,hP), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatibleCellMasses_of_randomizedCausalLaw
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (P : Measure (FullRow ε J)) (hP : RandomizedCausalLaw H g P) :
    CompatibleCellMasses H g (releasedLaw P) := by
  have hH : IsProbabilityMeasure H := by
    rw [← hP.scoreMarginal]
    exact @Measure.isProbabilityMeasure_map _ _ _ _ P hP.probability _
      (by unfold score; fun_prop : Measurable (score (ε := ε) (J := J))).aemeasurable
  have hRel : IsProbabilityMeasure (releasedLaw P) := by
    unfold releasedLaw
    exact @Measure.isProbabilityMeasure_map _ _ _ _ P hP.probability _
      (by unfold releasedRecord label arm observed; fun_prop :
        Measurable (releasedRecord (ε := ε) (J := J))).aemeasurable
  refine ⟨hH, hRel, hP.measurableRelease, ?_⟩
  intro a r
  let B : Set (ScoreSpace ε × OutcomeSpace × OutcomeSpace) :=
    {x | g x.1 = r}
  have hB : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_eq_fun (hP.measurableRelease.comp measurable_fst) measurable_const
  have hscore : Measurable (score (ε := ε) (J := J)) := by
    unfold score
    fun_prop
  have hrecord : Measurable (releasedRecord (ε := ε) (J := J)) := by
    unfold releasedRecord label arm observed
    fun_prop
  have hrel : MeasurableSet {z : Observation J | z.1 = r ∧ z.2.1 = a} := by
    exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
  have hlabel : ∀ᵐ ω ∂P, label ω = g (score ω) := hP.deterministicRelease
  have htreated :
      (releasedLaw P).real {z | z.1 = r ∧ z.2.1 = true} =
        ∫ e in cell g r, (e : ℝ) ∂H := by
    have hrand := hP.randomizedAssignment B hB
    have hsetRel : MeasurableSet {z : Observation J | z.1 = r ∧ z.2.1 = true} :=
      (measurableSet_eq_fun measurable_fst measurable_const).inter
        (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
    have hmap := MeasureTheory.map_measureReal_apply (μ := P) hrecord hsetRel
    change (P.map releasedRecord).real _ = _
    rw [hmap]
    have hset :
        P.real (releasedRecord ⁻¹' {z : Observation J | z.1 = r ∧ z.2.1 = true}) =
        P.real {ω | arm ω = true ∧ (score ω, outcome0 ω, outcome1 ω) ∈ B} := by
      apply measureReal_congr
      filter_upwards [hlabel] with ω hω
      change (label ω = r ∧ arm ω = true) =
        (arm ω = true ∧ g (score ω) = r)
      simp [hω, and_comm]
    rw [hset, hrand]
    rw [← hP.scoreMarginal]
    have hcell : MeasurableSet (cell g r) :=
      measurableSet_eq_fun hP.measurableRelease measurable_const
    have hmap := MeasureTheory.setIntegral_map (μ := P) (g := score)
      (f := fun e : ScoreSpace ε => (e : ℝ)) hcell
      (by fun_prop : AEStronglyMeasurable (fun e : ScoreSpace ε => (e : ℝ)) (P.map score))
      hscore.aemeasurable
    have hpre : {ω : FullRow ε J | (score ω, outcome0 ω, outcome1 ω) ∈ B} =
        (score (ε := ε) (J := J)) ⁻¹' cell g r := by
      ext ω
      rfl
    rw [hpre]
    exact hmap.symm
  cases a
  · letI : IsProbabilityMeasure P := hP.probability
    let C : Set (FullRow ε J) := score ⁻¹' cell g r
    let T : Set (FullRow ε J) := {ω | ω ∈ C ∧ arm ω = true}
    have hC : MeasurableSet C :=
      (measurableSet_eq_fun hP.measurableRelease measurable_const).preimage hscore
    have hT : MeasurableSet T :=
      hC.inter (measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const)
    have hTmass : P.real T = ∫ e in cell g r, (e : ℝ) ∂H := by
      rw [← htreated]
      have hsetRel : MeasurableSet {z : Observation J | z.1 = r ∧ z.2.1 = true} :=
        (measurableSet_eq_fun measurable_fst measurable_const).inter
          (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
      have hmap := MeasureTheory.map_measureReal_apply (μ := P) hrecord hsetRel
      rw [show releasedLaw P = P.map releasedRecord from rfl, hmap]
      apply measureReal_congr
      filter_upwards [hlabel] with ω hω
      change (ω ∈ C ∧ arm ω = true) = (label ω = r ∧ arm ω = true)
      simp [C, cell, hω]
    have hCmass : P.real C = H.real (cell g r) := by
      rw [← hP.scoreMarginal]
      exact (MeasureTheory.map_measureReal_apply hscore
        (measurableSet_eq_fun hP.measurableRelease measurable_const)).symm
    have hFmass :
        (releasedLaw P).real {z | z.1 = r ∧ z.2.1 = false} = P.real (C \ T) := by
      have hsetRel : MeasurableSet {z : Observation J | z.1 = r ∧ z.2.1 = false} :=
        (measurableSet_eq_fun measurable_fst measurable_const).inter
          (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
      have hmap := MeasureTheory.map_measureReal_apply (μ := P) hrecord hsetRel
      rw [show releasedLaw P = P.map releasedRecord from rfl, hmap]
      apply measureReal_congr
      filter_upwards [hlabel] with ω hω
      change (label ω = r ∧ arm ω = false) = (ω ∈ C ∧ ω ∉ T)
      cases hArm : arm ω <;> simp [C, T, cell, hω, hArm]
    rw [hFmass, measureReal_sdiff (show T ⊆ C from fun _ h => h.1) hT, hCmass,
      hTmass]
    letI : IsProbabilityMeasure H := hH
    have hint : IntegrableOn (fun e : ScoreSpace ε => (e : ℝ)) (cell g r) H := by
      apply Integrable.of_bound (by fun_prop)
        (|ε| + |1 - ε| + 1)
      filter_upwards [] with e
      change |(e : ℝ)| ≤ |ε| + |1 - ε| + 1
      rcases e.property with ⟨he₁, he₂⟩
      have h₁ := neg_le_abs ε
      have h₂ := le_abs_self (1 - ε)
      have h₃ := neg_le_abs (1 - ε)
      have h₄ := le_abs_self ε
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    rw [armCellMass]
    simp only [armProb, Bool.false_eq_true, ↓reduceIte]
    rw [integral_sub (integrable_const 1) hint]
    simp
  · simpa [armCellMass, armProb] using htreated

/-- Given [the stated mathematical inputs and assumptions](hyp:H,g,Prel,P,hP), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatibleCellMasses_of_compatibleCausalLaw
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (P : Measure (FullRow ε J))
    (hP : CompatibleCausalLaw H g Prel P) :
    CompatibleCellMasses H g Prel := by
  have hRandom : RandomizedCausalLaw H g P :=
    ⟨hP.probability, hP.measurableRelease, hP.scoreMarginal, hP.randomizedAssignment,
      hP.consistency, hP.deterministicRelease⟩
  rw [← hP.releasedLaw]
  exact compatibleCellMasses_of_randomizedCausalLaw H g P hRandom

/-- Given [the stated mathematical inputs and assumptions](hyp:H,g,Prel,hcomp), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatibleCellMasses_of_nonempty
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J))
    (hcomp : (CompatibleLaws H g Prel).Nonempty) :
    CompatibleCellMasses H g Prel := by
  obtain ⟨P, hP⟩ := hcomp
  exact compatibleCellMasses_of_compatibleCausalLaw H g Prel P hP.2
/-- For [the specified mathematical inputs](hyp:Prel,_hPrel,a,r,_hpos), [this definition](goal) introduces the corresponding object. -/
def armCellOutcomeLaw (Prel : Measure (Observation J))
    (_hPrel : IsProbabilityMeasure Prel)
    (a : ArmSpace) (r : LabelSpace J)
    (_hpos : 0 < Prel.real {z | z.1 = r ∧ z.2.1 = a}) : Measure ℝ :=
  (Prel {z | z.1 = r ∧ z.2.1 = a})⁻¹ •
    ((Prel.restrict {z | z.1 = r ∧ z.2.1 = a}).map (fun z => (z.2.2 : ℝ)))
  -- @realizes F(conditional released outcome law)
/-- For [the specified mathematical inputs](hyp:H,_hH,g,_hg,a,r,_hq), [this definition](goal) introduces the corresponding object. -/
def armCellScoreLaw (H : Measure (ScoreSpace ε))
    (_hH : IsProbabilityMeasure H)
    (g : ScoreSpace ε → LabelSpace J) (_hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J)
    (_hq : 0 < armCellMass H g a r) :
    Measure (ScoreSpace ε) :=
  (ENNReal.ofReal (armCellMass H g a r))⁻¹ •
    ((H.withDensity (fun e => ENNReal.ofReal (armProb a e))).restrict (cell g r))
  -- @realizes G(normalized tilted score law)
/-- For [the specified mathematical inputs](hyp:H,hH,g,hg,a,r,hq), [this definition](goal) introduces the corresponding object. -/
def armCellWeightLaw (H : Measure (ScoreSpace ε))
    (hH : IsProbabilityMeasure H)
    (g : ScoreSpace ε → LabelSpace J) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) : Measure ℝ :=
  (armCellScoreLaw H hH g hg a r hq).map (fun e => (armProb a e)⁻¹)
  -- @realizes W(inverse score under G)

/-- For [the specified mathematical inputs](hyp:μ,u), [this definition](goal) introduces the corresponding object. -/
abbrev generalizedQuantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  Causalean.Stat.quantile μ u -- @realizes Q(generalized lower quantile)

-- @node: def:arm-cell-primitives
/-- For [the specified mathematical inputs](hyp:H,g,Prel,a,r,hH,hg,hPrel), [this definition](goal) introduces the corresponding object. -/
def armCell (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (a : ArmSpace) (r : LabelSpace J)
    (hH : IsProbabilityMeasure H) (hg : Measurable g)
    (hPrel : IsProbabilityMeasure Prel) :
    ℝ ×
      (0 < Prel.real {z | z.1 = r ∧ z.2.1 = a} → Measure ℝ) ×
      (0 < armCellMass H g a r → Measure (ScoreSpace ε)) ×
      (0 < armCellMass H g a r → Measure ℝ) :=
  (armCellMass H g a r,
    armCellOutcomeLaw Prel hPrel a r,
    armCellScoreLaw H hH g hg a r,
    armCellWeightLaw H hH g hg a r)
/-- For [the specified mathematical inputs](hyp:H,g,Prel,hMass,a), [this definition](goal) introduces the corresponding object. -/
def muLower (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (a : ArmSpace) : ℝ :=
  ∑ r : LabelSpace J,
    if hq : 0 < armCellMass H g a r then
      armCellMass H g a r *
        ∫ u in (0 : ℝ)..1,
          generalizedQuantile
            (armCellOutcomeLaw Prel hMass.2.1 a r
              (by rw [hMass.2.2.2 a r]; exact hq)) u *
            generalizedQuantile
              (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) (1 - u)
    else 0
  -- @realizes muL(countermonotone quantile endpoint)
/-- For [the specified mathematical inputs](hyp:H,g,Prel,hMass,a), [this definition](goal) introduces the corresponding object. -/
def muUpper (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (a : ArmSpace) : ℝ :=
  ∑ r : LabelSpace J,
    if hq : 0 < armCellMass H g a r then
      armCellMass H g a r *
        ∫ u in (0 : ℝ)..1,
          generalizedQuantile
            (armCellOutcomeLaw Prel hMass.2.1 a r
              (by rw [hMass.2.2.2 a r]; exact hq)) u *
            generalizedQuantile
              (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) u
    else 0
  -- @realizes muU(comonotone quantile endpoint)

-- @node: def:mean-endpoints
/-- For [the specified mathematical inputs](hyp:H,g,Prel,hMass,a), [this definition](goal) introduces the corresponding object. -/
def armMeanEndpoints (H : Measure (ScoreSpace ε))
    (g : ScoreSpace ε → LabelSpace J) (Prel : Measure (Observation J))
    (hMass : CompatibleCellMasses H g Prel) (a : ArmSpace) : ℝ × ℝ :=
  (muLower H g Prel hMass a, muUpper H g Prel hMass a)

-- @node: def:sharp-ate-set
/-- For [the specified mathematical inputs](hyp:H,g,Prel,hMass), [this definition](goal) introduces the corresponding object. -/
def sharpATESet (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J))
    (hMass : CompatibleCellMasses H g Prel) : Set ℝ :=
  Set.Icc (muLower H g Prel hMass true - muUpper H g Prel hMass false)
    (muUpper H g Prel hMass true - muLower H g Prel hMass false)
  -- @realizes Isharp(candidate sharp ATE interval)
/-- For [the specified mathematical inputs](hyp:H,g,Prel,hMass), [this definition](goal) introduces the corresponding object. -/
def sharpATELength (H : Measure (ScoreSpace ε))
    (g : ScoreSpace ε → LabelSpace J) (Prel : Measure (Observation J))
    (hMass : CompatibleCellMasses H g Prel) : ℝ :=
  (muUpper H g Prel hMass true - muLower H g Prel hMass false) -
    (muLower H g Prel hMass true - muUpper H g Prel hMass false)

-- @node: def:worst-case-ambiguity
/-- For [the specified mathematical inputs](hyp:H,g), [this definition](goal) introduces the corresponding object. -/
def worstCaseAmbiguity (H : Measure (ScoreSpace ε))
    (g : ScoreSpace ε → LabelSpace J) : ℝ :=
  sSup {d : ℝ | ∃ P : Measure (FullRow ε J),
    ∃ (_hprob : IsProbabilityMeasure P), ∃ hP : RandomizedCausalLaw H g P,
      d = sharpATELength H g (releasedLaw P)
        (compatibleCellMasses_of_randomizedCausalLaw H g P hP)}
  -- @realizes D(worst-case attained sharp interval length)

-- @node: def:k-label-releases
/-- For [the specified mathematical inputs](hyp:ε,K), [this definition](goal) introduces the corresponding object. -/
def kLabelReleases (ε : ℝ) (K : ℕ) : Set (ScoreSpace ε → LabelSpace K) :=
  {g | Measurable g} -- @realizes g(measurable) @realizes GK(release family)
  -- @realizes K(label budget)

-- @node: def:optimal-k-ambiguity
/-- For [the specified mathematical inputs](hyp:ε,K,H), [this definition](goal) introduces the corresponding object. -/
def optimalKAmbiguity (ε : ℝ) (K : ℕ) (H : Measure (ScoreSpace ε)) : ℝ :=
  sInf {d : ℝ | ∃ g ∈ kLabelReleases ε K, d = worstCaseAmbiguity H g}
  -- @realizes DeltaK(infimum over measurable K-label releases)

/-- For [the specified mathematical inputs](hyp:f,t), [this definition](goal) introduces the corresponding object. -/
def densityExtension (f : ScoreSpace ε → ℝ) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Icc ε (1 - ε) then f ⟨t, ht⟩ else 0
/-- For [the specified mathematical inputs](hyp:f,x), [this definition](goal) introduces the corresponding object. -/
def compandingMass (f : ScoreSpace ε → ℝ) (x : ScoreSpace ε) : ℝ :=
  ∫ t in ε..(x : ℝ), Real.sqrt (densityExtension f t / (t * (1 - t)))
/-- For [the specified mathematical inputs](hyp:f,K,hK,e), [this definition](goal) introduces the corresponding object. -/
def compandingRelease (f : ScoreSpace ε → ℝ) (K : ℕ) (hK : 0 < K)
    (e : ScoreSpace ε) : LabelSpace K :=
  ⟨min (Nat.floor ((K : ℝ) * compandingMass f e /
      (∫ t in ε..(1 - ε), Real.sqrt (densityExtension f t / (t * (1 - t))))))
      (K - 1), by omega⟩

-- @node: def:high-resolution-handle
/-- [This definition](goal) introduces the corresponding mathematical object. -/
def highResolutionHandle : String :=
  "Proof strategy: uncross arbitrary measurable release cells for the paired \
   reciprocal-score absolute-deviation objective D_H(g); then use local scalar \
   quantization on ordered cells to derive matching lower and upper limits for \
   K Δ_K(H), with an ordered attaining sequence. Inputs: H, its density f, \
   measurable releases g, D_H(g), and Δ_K(H)."
  -- @realizes Hopt(proof-construction strategy)

end
end CausalSmith.PartialID.UnlinkedPropensityAte
