module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Kernel
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.MeasureTheory.Measure.Support
public import Causalean.Mathlib.Probability.Independence.Conditional

/-!
# Population ratio and conditional-rank decoder

The decoder is a function only of the observed probability laws.  It selects a
topological ordering internally, constructs `[0,1]`-valued conditional ranks,
and prunes to the unique minimal admissible parent sets on the model domain.
-/

@[expose] public section

open Causalean.Graph


open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @env: S4
variable {n : ℕ} {G : DAG (Fin n)} {s : SignVector n}

/-- A numerical linear extension of a directed relation. Injectivity excludes tied labels. -/
def IsTopologicalOrdering (E : Fin n → Fin n → Prop) (order : Fin n → ℕ) : Prop :=
  Function.Injective order ∧ ∀ ⦃j i⦄, E j i → order j < order i

/-- Labels preceding `i` in the explicitly selected ordering. -/
def predecessorSet (order : Fin n → ℕ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => order j < order i)
  -- @realizes \(B_i\)(labels preceding i in the selected order)

/-- Projection of a coordinate family onto a finite index set. -/
def familyProjection {X Y : Type*} (U : Fin n → X → Y) (S : Finset (Fin n))
    (x : X) : (j : {j // j ∈ S}) → Y := fun j => U j x

/-- A decoder input consists of genuine probability laws in all `n+1` environments. -/
abbrev ObservedProbabilityLawFamily (n : ℕ) :=
  {laws : ObservedLawFamily n // ∀ e, IsProbabilityMeasure (laws e)}

/-- Turn a measure family into a probability-law family when it is one, using a fixed
Dirac probability family only outside that domain.  Model hypotheses prove that this
fallback is never used by the exact-decoder theorem. -/
noncomputable def observedProbabilityLawFamily (laws : ObservedLawFamily n) :
    ObservedProbabilityLawFamily n := by
  classical
  exact if h : ∀ e, IsProbabilityMeasure (laws e) then ⟨laws, h⟩
  else ⟨fun _ => Measure.dirac 0, by intro e; infer_instance⟩

/-- A [continuous observed-ratio version](goal) for [law family `laws`](hyp:laws) and
[environment `i`](hyp:i) agrees almost everywhere with the canonical Radon--Nikodym ratio and is
continuous on the support of the observational law. -/
def IsContinuousObservedRatioVersion
    (laws : ObservedLawFamily n) (i : Fin n) (R : LatentState n → ℝ) : Prop :=
  R =ᵐ[laws 0] observedLawRatio laws i ∧
    ContinuousOn R (Measure.support (laws 0))

/-- The [law-only continuous ratio selector](goal) for [laws](hyp:laws) and [environment `i`](hyp:i)
chooses a continuous version when one exists and otherwise retains the canonical Radon--Nikodym
ratio. -/
noncomputable def observedContinuousRatio
    (laws : ObservedLawFamily n) (i : Fin n) : LatentState n → ℝ := by
  classical
  exact if h : ∃ R, IsContinuousObservedRatioVersion laws i R then
    (Measure.support (laws 0)).piecewise (Classical.choose h) (fun _ ↦ 0)
  else observedLawRatio laws i

/-- Whenever a continuous observed-ratio version exists, the law-only selector returns one.  Given [the stated inputs and conditions](hyp:hex), [the stated conclusion](goal) follows. -/
lemma observedContinuousRatio_isVersion
    (laws : ObservedLawFamily n) (i : Fin n)
    (hex : ∃ R, IsContinuousObservedRatioVersion laws i R) :
    IsContinuousObservedRatioVersion laws i (observedContinuousRatio laws i) := by
  classical
  rw [observedContinuousRatio, dif_pos hex]
  let R := Classical.choose hex
  have hR : IsContinuousObservedRatioVersion laws i R := Classical.choose_spec hex
  constructor
  · filter_upwards [hR.1, Measure.support_mem_ae (μ := laws 0)] with x hx hxs
    rw [Set.piecewise_eq_of_mem (Measure.support (laws 0))
      (Classical.choose hex) (fun _ ↦ 0) hxs]
    simpa only [R] using hx
  · exact hR.2.congr fun x hx ↦
      Set.piecewise_eq_of_mem (Measure.support (laws 0)) R (fun _ ↦ 0) hx

/-- The law-selected continuous ratio is globally measurable: outside the observational
support the selector uses the fixed zero extension.  [the stated conclusion](goal) follows. -/
lemma measurable_observedContinuousRatio
    (laws : ObservedLawFamily n) (i : Fin n) :
    Measurable (observedContinuousRatio laws i) := by
  classical
  rw [observedContinuousRatio]
  split
  · rename_i hex
    let R := Classical.choose hex
    have hR : IsContinuousObservedRatioVersion laws i R := Classical.choose_spec hex
    exact hR.2.measurable_piecewise continuous_const.continuousOn
      (laws 0).isClosed_support.measurableSet
  · exact measurable_observedLawRatio laws i

private lemma continuousOn_support_eq_of_ae_eq
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [HereditarilyLindelofSpace X] [TopologicalSpace Y] [T2Space Y]
    {μ : Measure X} {f g : X → Y}
    (hfg : f =ᵐ[μ] g) (hf : ContinuousOn f μ.support)
    (hg : ContinuousOn g μ.support) : EqOn f g μ.support := by
  intro x hx
  by_contra hne
  have hne_nhds : {y | f y ≠ g y} ∈ 𝓝[μ.support] x := by
    have hpair : ContinuousWithinAt (fun y => (f y, g y)) μ.support x :=
      (hf x hx).prodMk_nhds (hg x hx)
    exact hpair (isClosed_diagonal.isOpen_compl.mem_nhds hne)
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hne_nhds
  obtain ⟨U, hU, hUsub⟩ := hne_nhds
  have hUpos : 0 < μ U := (Measure.mem_support_iff_forall x).mp hx U hU
  have hneq0 : μ {y | f y ≠ g y} = 0 := ae_iff.mp hfg
  have hU0 : μ U = 0 := by
    apply measure_mono_null (t := {y | f y ≠ g y} ∪ μ.supportᶜ)
    · intro y hy
      by_cases hys : y ∈ μ.support
      · exact Or.inl (hUsub ⟨hy, hys⟩)
      · exact Or.inr hys
    · rw [measure_union_null hneq0 Measure.measure_compl_support]
  exact hUpos.ne' hU0

/-- Two continuous versions of the same almost-everywhere function agree throughout the
measure's support.  Given [the stated inputs and conditions](hyp:hR,hS), [the stated conclusion](goal) follows. -/
lemma IsContinuousObservedRatioVersion.eqOn
    {laws : ObservedLawFamily n} {i : Fin n} {R S : LatentState n → ℝ}
    (hR : IsContinuousObservedRatioVersion laws i R)
    (hS : IsContinuousObservedRatioVersion laws i S) :
    EqOn R S (Measure.support (laws 0)) := by
  exact continuousOn_support_eq_of_ae_eq (hR.1.trans hS.1.symm) hR.2 hS.2

/-- The observable log ratio constructed from the law-selected continuous ratio version. -/
def observedLawLogRatio (laws : ObservedLawFamily n) (i : Fin n) (x : LatentState n) : ℝ :=
  Real.log (observedContinuousRatio laws i x)

/-- The law-selected logarithmic ratio is globally measurable.  [the stated conclusion](goal) follows. -/
lemma measurable_observedLawLogRatio (laws : ObservedLawFamily n) (i : Fin n) :
    Measurable (observedLawLogRatio laws i) :=
  (measurable_observedContinuousRatio laws i).log

/-- Population MMD computed solely from the observed environment laws. -/
def observedLawDiscrepancy
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : UnitNormFeatureMap H) (laws : ObservedLawFamily n) (j i : Fin n) : ℝ :=
  ‖meanEmbedding U (Measure.map (observedLawRatio laws i) (laws 0)) -
    meanEmbedding U (Measure.map (observedLawRatio laws i) (laws j.succ))‖

/-- The ratio graph constructed solely from observed laws. -/
def observedLawRatioGraph
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : UnitNormFeatureMap H) (laws : ObservedLawFamily n) :
    Fin n → Fin n → Prop :=
  fun j i => j ≠ i ∧ 0 < observedLawDiscrepancy U laws j i
  -- @realizes \(H_D\)(observed-law MMD graph)

/-- The predecessor log-ratio vector used as the conditioning variable. -/
abbrev PredecessorLogRatios (order : Fin n → ℕ) (i : Fin n) :=
  (j : {j // j ∈ predecessorSet order i}) → ℝ

/-- The joint observed log-ratio and predecessor-log-ratio argument. -/
def conditionalRatioArgument (laws : ObservedLawFamily n) (order : Fin n → ℕ)
    (i : Fin n) (x : LatentState n) : ℝ × PredecessorLogRatios order i :=
  (observedLawLogRatio laws i x,
    familyProjection (observedLawLogRatio laws) (predecessorSet order i) x)

/-- The joint log-ratio and predecessor-log-ratio argument is measurable.  [the stated conclusion](goal) follows. -/
lemma measurable_conditionalRatioArgument
    (laws : ObservedLawFamily n) (order : Fin n → ℕ) (i : Fin n) :
    Measurable (conditionalRatioArgument laws order i) := by
  apply Measurable.prodMk (measurable_observedLawLogRatio laws i)
  apply measurable_pi_lambda
  intro j
  exact measurable_observedLawLogRatio laws j

/-- Evaluation of an s-finite real kernel on a varying lower interval is jointly measurable in
the endpoint and kernel parameter.  [the stated conclusion](goal) follows. -/
lemma measurable_kernel_Iic_uncurry
    {B : Type*} [MeasurableSpace B] (κ : Kernel B ℝ) [IsSFiniteKernel κ] :
    Measurable (fun z : ℝ × B ↦ κ z.2 (Set.Iic z.1)) := by
  let η : Kernel (ℝ × B) ℝ := κ.comap Prod.snd measurable_snd
  have hs : MeasurableSet {q : (ℝ × B) × ℝ | q.2 ≤ q.1.1} :=
    measurableSet_le measurable_snd measurable_fst.fst
  have hf : Measurable (Function.uncurry (fun z : ℝ × B ↦ fun y : ℝ ↦
      Set.indicator {q : (ℝ × B) × ℝ | q.2 ≤ q.1.1}
        (fun _ ↦ (1 : ENNReal)) (z, y))) :=
    measurable_const.indicator hs
  have hi := hf.lintegral_kernel_prod_right (κ := η)
  convert hi using 1
  funext z
  rw [Kernel.lintegral_comap]
  simp only [Set.indicator, Set.mem_ofPred_eq]
  change (κ z.2) (Set.Iic z.1) =
    ∫⁻ b, (Set.Iic z.1).indicator (fun _ ↦ (1 : ENNReal)) b ∂κ z.2
  rw [MeasureTheory.lintegral_indicator measurableSet_Iic, lintegral_one]
  simp

/-- The law-derived domain on which a conditional-CDF version is required to be continuous:
all thresholds over the support of the conditioning predecessor scores. -/
def observedConditionalRatioSupport (laws : ObservedLawFamily n) (order : Fin n → ℕ)
    (i : Fin n) : Set (ℝ × PredecessorLogRatios order i) :=
  Set.univ ×ˢ Measure.support (Measure.map
    (familyProjection (observedLawLogRatio laws) (predecessorSet order i)) (laws i.succ))

/-- The raw regular-conditional-distribution representative, with the original zero fallback
when the supplied environment laws are not finite. -/
def rawObservedConditionalRatioCDF
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n) (t : ℝ)
    (ell : PredecessorLogRatios order i) : ℝ := by
  classical
  exact if hfinite : ∀ e, IsFiniteMeasure (laws.1 e) then
    letI := hfinite i.succ
    (ProbabilityTheory.condDistrib (observedLawLogRatio laws.1 i)
        (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i))
        (laws.1 i.succ) ell (Set.Iic t)).toReal
  else 0

/-- The raw regular-conditional-distribution CDF is jointly measurable in threshold and
conditioning argument.  [the stated conclusion](goal) follows. -/
lemma measurable_rawObservedConditionalRatioCDF
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n) :
  Measurable (fun z : ℝ × PredecessorLogRatios order i ↦
      rawObservedConditionalRatioCDF laws order i z.1 z.2) := by
  classical
  unfold rawObservedConditionalRatioCDF
  split
  · rename_i hfinite
    letI := hfinite i.succ
    exact ENNReal.measurable_toReal.comp (measurable_kernel_Iic_uncurry
      (ProbabilityTheory.condDistrib (observedLawLogRatio laws.1 i)
        (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i))
        (laws.1 i.succ)))
  · exact measurable_const

/-- A law-only conditional-CDF version: it is jointly measurable, agrees almost everywhere with
the regular conditional distribution both at every fixed threshold and under the joint
ratio/predecessor law, and is continuous on the joint model support. -/
def IsContinuousConditionalRatioCDFVersion
  (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n)
    (C : ℝ → PredecessorLogRatios order i → Set.Icc (0 : ℝ) 1) : Prop :=
  Measurable (fun z : ℝ × PredecessorLogRatios order i => (C z.1 z.2 : ℝ)) ∧
  (∀ t, (fun ell => (C t ell : ℝ)) =ᵐ[Measure.map
      (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i)) (laws.1 i.succ)]
      rawObservedConditionalRatioCDF laws order i t) ∧
  (fun z : ℝ × PredecessorLogRatios order i => (C z.1 z.2 : ℝ)) =ᵐ[
      Measure.map (conditionalRatioArgument laws.1 order i) (laws.1 i.succ)]
    (fun z => rawObservedConditionalRatioCDF laws order i z.1 z.2) ∧
  ContinuousOn (fun z : ℝ × PredecessorLogRatios order i => (C z.1 z.2 : ℝ))
    (observedConditionalRatioSupport laws.1 order i)

/-- The raw conditional-CDF representative as a unit-interval value, retaining it when it
has the required range and using zero only as the range-check fallback. -/
def rawObservedConditionalRatioCDFUnit
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n) (t : ℝ)
    (ell : PredecessorLogRatios order i) : Set.Icc (0 : ℝ) 1 := by
  classical
  exact if h : rawObservedConditionalRatioCDF laws order i t ell ∈ Set.Icc (0 : ℝ) 1 then
    ⟨rawObservedConditionalRatioCDF laws order i t ell, h⟩
  else ⟨0, by constructor <;> norm_num⟩

/-- The range-checked raw conditional CDF is jointly measurable.  [the stated conclusion](goal) follows. -/
lemma measurable_rawObservedConditionalRatioCDFUnit
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n) :
    Measurable (fun z : ℝ × PredecessorLogRatios order i ↦
      rawObservedConditionalRatioCDFUnit laws order i z.1 z.2) := by
  have hraw := measurable_rawObservedConditionalRatioCDF laws order i
  have hs : MeasurableSet {z : ℝ × PredecessorLogRatios order i |
      rawObservedConditionalRatioCDF laws order i z.1 z.2 ∈ Set.Icc (0 : ℝ) 1} :=
    measurableSet_Icc.preimage hraw
  have hreal : Measurable (fun z : ℝ × PredecessorLogRatios order i ↦
      if rawObservedConditionalRatioCDF laws order i z.1 z.2 ∈ Set.Icc (0 : ℝ) 1
      then rawObservedConditionalRatioCDF laws order i z.1 z.2 else 0) := by
    exact Measurable.ite hs hraw measurable_const
  have hval : ∀ z : ℝ × PredecessorLogRatios order i,
      (if rawObservedConditionalRatioCDF laws order i z.1 z.2 ∈ Set.Icc (0 : ℝ) 1
       then rawObservedConditionalRatioCDF laws order i z.1 z.2 else 0) ∈ Set.Icc (0 : ℝ) 1 := by
    intro z
    split
    · assumption
    · constructor <;> norm_num
  convert hreal.subtype_mk (h := hval) using 1
  funext z
  unfold rawObservedConditionalRatioCDFUnit
  split <;> rfl

/-- The continuous conditional-CDF version selected from the observed laws alone. If no
continuous version exists, this retains the raw `condDistrib`/zero fallback. -/
noncomputable def observedConditionalRatioCDF
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n) :
    ℝ → PredecessorLogRatios order i → Set.Icc (0 : ℝ) 1 := by
  classical
  exact if h : ∃ C, IsContinuousConditionalRatioCDFVersion laws order i C then
    Classical.choose h
  else rawObservedConditionalRatioCDFUnit laws order i
  -- @realizes \(C_i\)(law-selected continuous conditional-CDF version)

-- @node: observedConditionalRatioCDF_isContinuousVersion
/-- Whenever a continuous conditional-CDF version exists, the law-only selector returns one.  Given [the stated inputs and conditions](hyp:hex), [the stated conclusion](goal) follows. -/
lemma observedConditionalRatioCDF_isContinuousVersion
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n)
    (hex : ∃ C, IsContinuousConditionalRatioCDFVersion laws order i C) :
    IsContinuousConditionalRatioCDFVersion laws order i
      (observedConditionalRatioCDF laws order i) := by
  classical
  rw [observedConditionalRatioCDF, dif_pos hex]
  exact Classical.choose_spec hex

/-- The selected conditional CDF is jointly measurable whether or not a continuous version
exists: the fallback is the measurable range-checked raw conditional distribution.  [the stated conclusion](goal) follows. -/
lemma measurable_observedConditionalRatioCDF_unconditional
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n) :
    Measurable (fun z : ℝ × PredecessorLogRatios order i ↦
      observedConditionalRatioCDF laws order i z.1 z.2) := by
  classical
  unfold observedConditionalRatioCDF
  split
  · rename_i hex
    exact (Classical.choose_spec hex).1.subtype_mk
  · exact measurable_rawObservedConditionalRatioCDFUnit laws order i

/-- Two continuous conditional-CDF versions agree everywhere on the support of the observed joint
ratio/predecessor law.  Given [the stated inputs and conditions](hyp:hC,hD), [the stated conclusion](goal) follows. -/
lemma IsContinuousConditionalRatioCDFVersion.eqOn
    {laws : ObservedProbabilityLawFamily n} {order : Fin n → ℕ} {i : Fin n}
    {C D : ℝ → PredecessorLogRatios order i → Set.Icc (0 : ℝ) 1}
    (hC : IsContinuousConditionalRatioCDFVersion laws order i C)
    (hD : IsContinuousConditionalRatioCDFVersion laws order i D) :
    Set.EqOn (fun z : ℝ × PredecessorLogRatios order i ↦ (C z.1 z.2 : ℝ))
      (fun z ↦ (D z.1 z.2 : ℝ)) (observedConditionalRatioSupport laws.1 order i) := by
  intro z hz
  let μ := Measure.map
    (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i))
    (laws.1 i.succ)
  have hmap : Set.MapsTo (fun ell : PredecessorLogRatios order i => (z.1, ell))
      (Measure.support μ) (observedConditionalRatioSupport laws.1 order i) := by
    intro ell hell
    exact ⟨Set.mem_univ _, hell⟩
  have hCcont : ContinuousOn (fun ell => (C z.1 ell : ℝ)) (Measure.support μ) :=
    hC.2.2.2.comp (continuousOn_const.prodMk continuousOn_id) hmap
  have hDcont : ContinuousOn (fun ell => (D z.1 ell : ℝ)) (Measure.support μ) :=
    hD.2.2.2.comp (continuousOn_const.prodMk continuousOn_id) hmap
  exact continuousOn_support_eq_of_ae_eq
    ((hC.2.1 z.1).trans (hD.2.1 z.1).symm) hCcont hDcont hz.2

/-- Every continuous conditional-CDF version agrees on joint support with the law-only selected
version.  Given [the stated inputs and conditions](hyp:hex,hC), [the stated conclusion](goal) follows. -/
lemma observedConditionalRatioCDF_eq_on_support
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n)
    (hex : ∃ C, IsContinuousConditionalRatioCDFVersion laws order i C)
    (C : ℝ → PredecessorLogRatios order i → Set.Icc (0 : ℝ) 1)
    (hC : IsContinuousConditionalRatioCDFVersion laws order i C) :
    ∀ z ∈ observedConditionalRatioSupport laws.1 order i,
      C z.1 z.2 = observedConditionalRatioCDF laws order i z.1 z.2 := by
  intro z hz
  apply Subtype.ext
  exact hC.eqOn (observedConditionalRatioCDF_isContinuousVersion laws order i hex) hz

/-- The identified rank coordinate, constructed only from observed laws and an explicit ordering. -/
def observedLawRankCoordinate
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n)
    (x : LatentState n) : Set.Icc (0 : ℝ) 1 :=
  observedConditionalRatioCDF laws order i (observedLawLogRatio laws.1 i x)
    (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i) x)
  -- @realizes \(U_i\)(conditional rank computed from observed laws)

/-- Every law-selected rank coordinate is measurable, including on the selector's raw fallback
branch.  [the stated conclusion](goal) follows. -/
lemma measurable_observedLawRankCoordinate
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n) :
    Measurable (observedLawRankCoordinate laws order i) := by
  exact (measurable_observedConditionalRatioCDF_unconditional laws order i).comp
    (measurable_conditionalRatioArgument laws.1 order i)

/-- Every finite projection of the law-selected rank family is measurable.  [the stated conclusion](goal) follows. -/
lemma measurable_rankFamilyProjection
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ)
    (S : Finset (Fin n)) :
    Measurable (familyProjection (observedLawRankCoordinate laws order) S) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_observedLawRankCoordinate laws order j

/-- Conditional independence of two measurable functions given a third. -/
def CondIndepGiven {Ω A B C : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) : Prop :=
  ∃ hμ : IsFiniteMeasure μ,
    letI := hμ
    ∃ _hX : Measurable X,
      ∃ _hY : Measurable Y,
        ∃ hZ : Measurable Z,
          ProbabilityTheory.CondIndepFun (MeasurableSpace.comap Z inferInstance)
            hZ.comap_le X Y μ

/-- A candidate parent set satisfies the observed-law conditional-independence test. -/
def AdmissibleParentSet (laws : ObservedProbabilityLawFamily n)
    (order : Fin n → ℕ) (i : Fin n) (A : Finset (Fin n)) : Prop :=
  A ⊆ predecessorSet order i ∧
    CondIndepGiven (laws.1 0) (observedLawRankCoordinate laws order i)
      (familyProjection (observedLawRankCoordinate laws order)
        ((predecessorSet order i) \ A))
      (familyProjection (observedLawRankCoordinate laws order) A)

/-- Inclusion-minimal admissibility for parent pruning. -/
def MinimalAdmissibleParentSet (laws : ObservedProbabilityLawFamily n)
    (order : Fin n → ℕ) (i : Fin n) (A : Finset (Fin n)) : Prop :=
  AdmissibleParentSet laws order i A ∧
    ∀ B, AdmissibleParentSet laws order i B → B ⊆ A → A ⊆ B

/-- The uniquely inclusion-minimal admissible set, defined only when it is genuinely unique.
`none` records that the observed laws lie outside the decoder's parent-pruning domain. -/
def selectedParentSet (laws : ObservedProbabilityLawFamily n)
    (order : Fin n → ℕ) (i : Fin n) : Option (Finset (Fin n)) := by
  classical
  exact if h : ∃! A : Finset (Fin n), MinimalAdmissibleParentSet laws order i A then
    some (Classical.choose h.exists)
  else none

/-- The parent relation carried by a successful unique-minimum selection. -/
def selectedParentRelation (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) :
    Fin n → Fin n → Prop :=
  fun j i => ∃ A, selectedParentSet laws order i = some A ∧ j ∈ A

/-- Every selected edge points forward in the supplied ordering.  Given [the stated inputs and conditions](hyp:hj), [the stated conclusion](goal) follows. -/
lemma selectedParentSet_precedes
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) {j i : Fin n}
    (hj : selectedParentRelation laws order j i) : order j < order i := by
  rcases hj with ⟨A, hA, hjA⟩
  unfold selectedParentSet at hA
  split at hA
  · rename_i h_unique
    injection hA with hA'
    subst A
    simpa [predecessorSet] using (Classical.choose_spec h_unique.exists).1.1 hjA
  · simp at hA

/-- The selected-parent relation is acyclic because every edge points forward in `order`.  [the stated conclusion](goal) follows. -/
lemma selectedParentRelation_acyclic
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n) :
    ¬ Relation.TransGen (selectedParentRelation laws order) i i := by
  intro h
  have path_lt : ∀ {a b : Fin n},
      Relation.TransGen (selectedParentRelation laws order) a b → order a < order b := by
    intro a b hab
    induction hab with
    | single hji => exact selectedParentSet_precedes laws order hji
    | tail hab hbc ih => exact lt_trans ih (selectedParentSet_precedes laws order hbc)
  have hi : order i < order i := path_lt h
  exact (lt_irrefl _ hi)

/-- The acyclic graph induced by all successful unique-minimum parent selections. -/
def selectedParentDAG (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) :
    DAG (Fin n) where
  edge := selectedParentRelation laws order
  decEdge := Classical.decRel _
  acyclic := selectedParentRelation_acyclic laws order

/-- Compatibility restricts law-coherence comparisons to representations of the same observed
law family on the same observed support. -/
def CompatibleObservedRepresentation
    {G₁ G₂ : DAG (Fin n)} {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
    (W₁ : ObservedWorld G₁ θ₁) (W₂ : ObservedWorld G₂ θ₂) : Prop :=
  W₁.law = W₂.law ∧ observedSupport G₁ W₁ = observedSupport G₂ W₂

/-- Coherence uses almost-everywhere Radon--Nikodym representatives, but compares the selected
continuous ranks pointwise on the full common observed support. -/
def ObservedWorldLawCoherent {θ : Mechanism n G} (W : ObservedWorld G θ) : Prop :=
  (∀ i, W.ratio i =ᵐ[W.law 0] observedLawRatio W.law i) ∧
  ∀ (G' : DAG (Fin n)) (θ' : Mechanism n G') (W' : ObservedWorld G' θ'),
    CompatibleObservedRepresentation W W' → ∀ order i,
      ∀ x ∈ observedSupport G W,
        observedLawRankCoordinate (observedProbabilityLawFamily W'.law) order i x =
          observedLawRankCoordinate (observedProbabilityLawFamily W.law) order i x

/-- A topological ordering selected from the ratio graph using only the observed laws.  The
numeric label order is a total fallback outside the acyclic model domain. -/
noncomputable def selectedTopologicalOrder
    (laws : ObservedProbabilityLawFamily n) : Fin n → ℕ := by
  classical
  exact if h : ∃ order, IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap laws.1) order then
    Classical.choose h
  else fun i => i.val

-- @node: selectedTopologicalOrder_isTopologicalOrdering
/-- If the observed ratio graph has a topological ordering, its law-only selected ordering is
itself topological.  Given [the stated inputs and conditions](hyp:hex), [the stated conclusion](goal) follows. -/
lemma selectedTopologicalOrder_isTopologicalOrdering
    (laws : ObservedProbabilityLawFamily n)
    (hex : ∃ order, IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap laws.1) order) :
    IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap laws.1)
      (selectedTopologicalOrder laws) := by
  classical
  rw [selectedTopologicalOrder, dif_pos hex]
  exact Classical.choose_spec hex

-- @node: def:population-decoder
/-- The law-only population recovery map.  It forms the Gaussian-MMD graph, selects its own
topological ordering, constructs unit-interval ranks, and returns the parent-pruned DAG. -/
def populationDecoder (laws : ObservedProbabilityLawFamily n) :
    (Fin n → Fin n → Prop) ×
      (Fin n → LatentState n → Set.Icc (0 : ℝ) 1) × DAG (Fin n) :=
  let order := selectedTopologicalOrder laws
  (observedLawRatioGraph gaussianFeatureMap laws.1,
    observedLawRankCoordinate laws order, selectedParentDAG laws order)
  -- @realizes \(\mathscr D\)(ratio graph, rank coordinates, parent-pruned environment DAG)

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
