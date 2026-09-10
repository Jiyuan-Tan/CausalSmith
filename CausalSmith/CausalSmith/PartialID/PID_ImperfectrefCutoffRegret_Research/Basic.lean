import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.EReal.Basic
import Causalean.PO.ID.Partial.Basic

set_option linter.style.longLine false

/-! Core objects for cutoff regret with an imperfect binary reference. -/

open MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

-- @env: S1
structure ImperfectReferenceModel where
  P : Measure (ℝ × Bool) -- @realizes \(P_{SR}\)(probability law on ℝ×Bool) @realizes \(S\)(ℝ coordinate) @realizes \(R\)(Bool coordinate)
  isProbability : IsProbabilityMeasure P -- @realizes \(P_{SR}\)(probability normalization)
  alpha : ℝ -- @realizes \(\alpha\)(real carrier)
  alpha_mem_Icc : alpha ∈ Set.Icc (0 : ℝ) 1 -- @realizes \(\alpha\)(range [0,1])
  beta : ℝ -- @realizes \(\beta\)(real carrier)
  beta_mem_Icc : beta ∈ Set.Icc (0 : ℝ) 1 -- @realizes \(\beta\)(range [0,1])
  b : ℝ -- @realizes \(b\)(real utility carrier)
  c : ℝ -- @realizes \(c\)(real utility carrier)
  T : Set EReal -- @realizes \(\mathcal T\)(subset of extended-real cutoffs) @realizes \(t\)(EReal cutoff carrier) @realizes \(u\)(EReal comparator carrier)
  T_nonempty : T.Nonempty -- @realizes \(\mathcal T\)(nonempty)

attribute [instance] ImperfectReferenceModel.isProbability

abbrev BorelScoreSet := {I : Set ℝ // MeasurableSet I}

def singletonBorel (x : ℝ) : BorelScoreSet := ⟨{x}, MeasurableSet.singleton x⟩

def iioBorel (x : ℝ) : BorelScoreSet := ⟨Set.Iio x, measurableSet_Iio⟩

abbrev Cutoff (M : ImperfectReferenceModel) := {t : EReal // t ∈ M.T}

/-- The observed score marginal. -/
noncomputable def scoreMarginal (M : ImperfectReferenceModel) : Measure ℝ :=
  M.P.map Prod.fst -- @realizes \(P_S\)(S-marginal of P_SR)

/-- A reference-stratum score submeasure together with its total mass. -/
structure ObservedSubmeasureData where
  measure : Measure ℝ
  mass : ℝ

-- @node: def:observed-submeasures
noncomputable def obsSubmeasure (M : ImperfectReferenceModel)
    (r : Bool) : ObservedSubmeasureData :=
  let μ := (M.P.restrict {z | z.2 = r}).map Prod.fst
  { measure := μ
    mass := μ.real Set.univ }
  -- @realizes \(\mu_r\)(P_SR restricted to R=r then mapped to S) @realizes \(q_r\)(total mass of μ_r)

noncomputable def obsMeasure (M : ImperfectReferenceModel) (r : Bool) : Measure ℝ :=
  (obsSubmeasure M r).measure

noncomputable def obsMass (M : ImperfectReferenceModel) (r : Bool) : ℝ :=
  (obsSubmeasure M r).mass

-- @node: obsMass_eq_reference_event
lemma obsMass_eq_reference_event (M : ImperfectReferenceModel) (r : Bool) :
    obsMass M r = M.P.real {z | z.2 = r} := by
  change ((M.P.restrict {z | z.2 = r}).map Prod.fst).real Set.univ =
    M.P.real {z | z.2 = r}
  rw [map_measureReal_apply measurable_fst MeasurableSet.univ]
  simp

instance obsMeasure_isFinite (M : ImperfectReferenceModel) (r : Bool) :
    IsFiniteMeasure (obsMeasure M r) := by
  dsimp [obsMeasure, obsSubmeasure]
  infer_instance
  -- @realizes \(\mu_r\)(finite subprobability measure)

lemma obsMass_mem_Icc (M : ImperfectReferenceModel) (r : Bool) :
    obsMass M r ∈ Set.Icc (0 : ℝ) 1 := by
  rw [obsMass_eq_reference_event]
  constructor
  · exact measureReal_nonneg
  · calc
      M.P.real {z | z.2 = r} ≤ M.P.real Set.univ :=
        measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  -- @realizes \(q_r\)(reference-stratum probability range [0,1])

def youden (M : ImperfectReferenceModel) : ℝ :=
  M.alpha + M.beta - 1 -- @realizes \(g\)(α+β-1)

def prevalence (M : ImperfectReferenceModel) : ℝ :=
  (obsMass M true + M.beta - 1) / youden M
  -- @realizes \(\pi\)((q_1+β-1)/g)

def diseaseMass (M : ImperfectReferenceModel) (r : Bool) : ℝ :=
  if r then M.alpha * prevalence M else (1 - M.alpha) * prevalence M
  -- @realizes \(a_r\)(απ in stratum 1 and (1-α)π in stratum 0)

def DiseaseMassRange (M : ImperfectReferenceModel) : Prop :=
  ∀ r, diseaseMass M r ∈ Set.Icc (0 : ℝ) 1
  -- @realizes \(a_r\)(range [0,1])

-- @node: def:derived-margins
def derivedMargins (M : ImperfectReferenceModel) : ℝ × ℝ × (Bool → ℝ) :=
  (youden M, prevalence M, diseaseMass M)

-- @node: ass:observed-margin
def ObservedMargin (M : ImperfectReferenceModel)
    (Q : Measure (ℝ × Bool × Bool)) : Prop :=
  Q.map (fun z => (z.1, z.2.1)) = M.P
  -- @realizes \(Q\)(candidate law with observed S,R margin) @realizes \(D\)(latent Bool coordinate)

-- @node: ass:reference-sensitivity
def ReferenceSensitivity (M : ImperfectReferenceModel)
    (Q : Measure (ℝ × Bool × Bool)) : Prop :=
  Q.real {z | z.2.1 = true ∧ z.2.2 = true} =
    M.alpha * Q.real {z | z.2.2 = true}

-- @node: ass:reference-specificity
def ReferenceSpecificity (M : ImperfectReferenceModel)
    (Q : Measure (ℝ × Bool × Bool)) : Prop :=
  Q.real {z | z.2.1 = false ∧ z.2.2 = false} =
    M.beta * Q.real {z | z.2.2 = false}

-- @node: ass:informative-reference
def InformativeReference (M : ImperfectReferenceModel) : Prop :=
  0 < youden M -- @realizes \(g\)(positive Youden orientation)

-- @node: ass:interior-prevalence
def InteriorPrevalence (M : ImperfectReferenceModel) : Prop :=
  0 < prevalence M ∧ prevalence M < 1
  -- @realizes \(\pi\)(interior range (0,1))

-- @node: ass:positive-benefit
def PositiveBenefit (M : ImperfectReferenceModel) : Prop :=
  0 < M.b -- @realizes \(b\)(positive)

-- @node: ass:positive-cost
def PositiveCost (M : ImperfectReferenceModel) : Prop :=
  0 < M.c -- @realizes \(c\)(positive)

-- @node: ass:submeasure-domination
def SubmeasureDomination (M : ImperfectReferenceModel)
    (ν : Bool → Measure ℝ) : Prop :=
  ∀ r, ν r ≤ obsMeasure M r

-- @node: ass:submeasure-mass
def SubmeasureMass (M : ImperfectReferenceModel)
    (ν : Bool → Measure ℝ) : Prop :=
  ∀ r, (ν r).real Set.univ = diseaseMass M r

-- @node: def:compatible-laws
structure CompatibleLaw (M : ImperfectReferenceModel)
    (Q : Measure (ℝ × Bool × Bool)) : Prop where
  probability : IsProbabilityMeasure Q -- @realizes \(Q\)(probability completion law)
  observed : ObservedMargin M Q
  sensitivity : ReferenceSensitivity M Q
  specificity : ReferenceSpecificity M Q
  informative : InformativeReference M
  interior : InteriorPrevalence M

def compatibleLaws (M : ImperfectReferenceModel) :
    Set (Measure (ℝ × Bool × Bool)) :=
  {Q | CompatibleLaw M Q}
  -- @realizes \(\mathcal M(P_{SR},\alpha,\beta)\)(compatible completion class)

abbrev CompatibleCompletion (M : ImperfectReferenceModel) :=
  {Q : Measure (ℝ × Bool × Bool) // Q ∈ compatibleLaws M}

-- @node: def:dominated-allocations
structure DominatedAllocation (M : ImperfectReferenceModel)
    (ν : Bool → Measure ℝ) : Prop where
  domination : SubmeasureDomination M ν
  mass : SubmeasureMass M ν

def dominatedAllocations (M : ImperfectReferenceModel) :
    Set (Bool → Measure ℝ) :=
  {ν | DominatedAllocation M ν}
  -- @realizes \(\mathcal N(P_{SR},α,β)\)(dominated fixed-mass class)

noncomputable def stratumMass (M : ImperfectReferenceModel) (r : Bool)
    (I : BorelScoreSet) : ℝ :=
  (obsMeasure M r).real I -- @realizes \(p_r(I)\)(μ_r(I)) @realizes \(I\)(Borel-set carrier)

/-- The paired lower and upper capped-allocation endpoints. -/
structure MassEndpointData where
  lower : ℝ
  upper : ℝ

-- @node: def:mass-endpoints
noncomputable def massEndpoints (M : ImperfectReferenceModel)
    (I : BorelScoreSet) : MassEndpointData :=
  { lower := ∑ r : Bool,
      max 0 (diseaseMass M r - obsMass M r + stratumMass M r I)
    upper := ∑ r : Bool, min (diseaseMass M r) (stratumMass M r I) }

noncomputable def massLower (M : ImperfectReferenceModel) (I : BorelScoreSet) : ℝ :=
  (massEndpoints M I).lower
  -- @realizes \(L(I)\)(lower capped-mass endpoint)

noncomputable def massUpper (M : ImperfectReferenceModel) (I : BorelScoreSet) : ℝ :=
  (massEndpoints M I).upper
  -- @realizes \(U(I)\)(upper capped-mass endpoint)

lemma measurableSet_referSet (t : EReal) :
    MeasurableSet {s : ℝ | t ≤ (s : EReal)} := by
  exact measurable_coe_real_ereal measurableSet_Ici

noncomputable def referSet (t : EReal) : BorelScoreSet :=
  ⟨{s | t ≤ (s : EReal)}, measurableSet_referSet t⟩
  -- @realizes \(\delta_t\)(refer iff S≥t)

lemma measurableSet_cutoffInterval (u t : EReal) :
    MeasurableSet {s : ℝ | u ≤ (s : EReal) ∧ (s : EReal) < t} := by
  exact (measurable_coe_real_ereal measurableSet_Ici).inter
    (measurable_coe_real_ereal measurableSet_Iio)

noncomputable def cutoffInterval (u t : EReal) : BorelScoreSet :=
  ⟨{s | u ≤ (s : EReal) ∧ (s : EReal) < t}, measurableSet_cutoffInterval u t⟩
  -- @realizes \(I_{u,t}\)(Borel half-open disagreement interval)

noncomputable def latentSubmeasure {M : ImperfectReferenceModel}
    (Q : CompatibleCompletion M)
    (r : Bool) : Measure ℝ :=
  (Q.1.restrict {z | z.2.1 = r ∧ z.2.2 = true}).map Prod.fst
  -- @realizes \(\nu_r\)(probability-completion slice with R=r,D=1)

/-- The law-specific value and both sharp endpoint functions at one cutoff. -/
structure NetValueData where
  value : ℝ
  allocationValue : ℝ
  lower : ℝ
  upper : ℝ

-- @node: def:net-value
noncomputable def netValue (M : ImperfectReferenceModel)
    (Q : CompatibleCompletion M) (t : EReal) : NetValueData :=
  { value := M.b * Q.1.real {z | z.2.2 = true ∧ z.1 ∈ referSet t} -
      M.c * Q.1.real {z | z.2.2 = false ∧ z.1 ∈ referSet t}
    allocationValue := (M.b + M.c) *
        (∑ r : Bool, (latentSubmeasure Q r).real (referSet t)) -
      M.c * ∑ r : Bool, stratumMass M r (referSet t)
    lower := (M.b + M.c) * massLower M (referSet t) -
      M.c * ∑ r : Bool, stratumMass M r (referSet t)
    upper := (M.b + M.c) * massUpper M (referSet t) -
      M.c * ∑ r : Bool, stratumMass M r (referSet t) }
  -- @realizes \(V_Q(t)\)(compatible-law value) @realizes \(V_L(t)\)(lower endpoint) @realizes \(V_U(t)\)(upper endpoint)

noncomputable def netValueAt (M : ImperfectReferenceModel)
    (Q : CompatibleCompletion M) (t : EReal) : ℝ :=
  (netValue M Q t).value

noncomputable def netValueLower (M : ImperfectReferenceModel) (t : EReal) : ℝ :=
  (M.b + M.c) * massLower M (referSet t) -
    M.c * ∑ r : Bool, stratumMass M r (referSet t)

noncomputable def netValueUpper (M : ImperfectReferenceModel) (t : EReal) : ℝ :=
  (M.b + M.c) * massUpper M (referSet t) -
    M.c * ∑ r : Bool, stratumMass M r (referSet t)

lemma netValue_allocation_identity (M : ImperfectReferenceModel)
    (Q : CompatibleCompletion M) (t : EReal) :
    (netValue M Q t).value = (netValue M Q t).allocationValue := by
  let _ := Q.2.probability
  let A : Set ℝ := referSet t
  let D : Set (ℝ × Bool × Bool) := {z | z.2.2 = true ∧ z.1 ∈ A}
  let H : Set (ℝ × Bool × Bool) := {z | z.2.2 = false ∧ z.1 ∈ A}
  let E : Set (ℝ × Bool × Bool) := {z | z.1 ∈ A}
  have hA : MeasurableSet A := (referSet t).property
  have hslice (r d : Bool) :
      ((Q.1.restrict {z | z.2.1 = r ∧ z.2.2 = d}).map Prod.fst).real A =
        Q.1.real {z | z.1 ∈ A ∧ z.2.1 = r ∧ z.2.2 = d} := by
    rw [map_measureReal_apply measurable_fst hA,
      measureReal_restrict_apply (hA.preimage measurable_fst)]
    apply congrArg Q.1.real
    ext z
    simp
  have hlatent :
      (∑ r : Bool, (latentSubmeasure Q r).real (referSet t)) = Q.1.real D := by
    simp only [Fintype.sum_bool]
    rw [show (latentSubmeasure Q true).real (referSet t) =
        Q.1.real {z | z.1 ∈ A ∧ z.2.1 = true ∧ z.2.2 = true} by
      simpa [latentSubmeasure, A] using hslice true true]
    rw [show (latentSubmeasure Q false).real (referSet t) =
        Q.1.real {z | z.1 ∈ A ∧ z.2.1 = false ∧ z.2.2 = true} by
      simpa [latentSubmeasure, A] using hslice false true]
    rw [← measureReal_union]
    · congr 1
      ext z
      cases h : z.2.1 <;> simp [h, D, A, and_comm]
    · simp [Set.disjoint_left]
    · measurability
  have hobsSlice (r : Bool) :
      stratumMass M r (referSet t) =
        Q.1.real {z | z.1 ∈ A ∧ z.2.1 = r} := by
    change ((M.P.restrict {z | z.2 = r}).map Prod.fst).real A = _
    rw [map_measureReal_apply measurable_fst hA,
      measureReal_restrict_apply (hA.preimage measurable_fst)]
    change M.P.real {z | z.1 ∈ A ∧ z.2 = r} = _
    rw [← Q.2.observed]
    have hs : MeasurableSet {z : ℝ × Bool | z.1 ∈ A ∧ z.2 = r} :=
      (hA.preimage measurable_fst).inter
        (measurable_snd (MeasurableSet.singleton r))
    exact map_measureReal_apply (by fun_prop) hs
  have hobs :
      (∑ r : Bool, stratumMass M r (referSet t)) = Q.1.real E := by
    simp only [Fintype.sum_bool, hobsSlice]
    rw [← measureReal_union]
    · congr 1
      ext z
      cases h : z.2.1 <;> simp [h, E, A]
    · simp [Set.disjoint_left]
    · measurability
  have hpartition : Q.1.real E = Q.1.real D + Q.1.real H := by
    rw [← measureReal_union]
    · congr 1
      ext z
      cases h : z.2.2 <;> simp [h, D, H, E, A]
    · simp [Set.disjoint_left, D, H]
    · measurability
  change M.b * Q.1.real D - M.c * Q.1.real H =
    (M.b + M.c) * (∑ r : Bool, (latentSubmeasure Q r).real (referSet t)) -
      M.c * ∑ r : Bool, stratumMass M r (referSet t)
  rw [hlatent, hobs, hpartition]
  ring

noncomputable def tprCurve (M : ImperfectReferenceModel)
    (Q : CompatibleCompletion M) (t : Cutoff M) : ℝ :=
  (∑ r : Bool, (latentSubmeasure Q r).real (referSet t.1)) / prevalence M
  -- @realizes \(\operatorname{TPR}_Q(t)\)(compatible-law curve on T)

noncomputable def fprCurve (M : ImperfectReferenceModel)
    (Q : CompatibleCompletion M) (t : Cutoff M) : ℝ :=
  ((∑ r : Bool, stratumMass M r (referSet t.1)) -
    ∑ r : Bool, (latentSubmeasure Q r).real (referSet t.1)) / (1 - prevalence M)
  -- @realizes \(\operatorname{FPR}_Q(t)\)(compatible-law curve on T)

-- @node: def:joint-curves
noncomputable def jointCurveSet (M : ImperfectReferenceModel) :
    Set (Cutoff M → ℝ × ℝ × ℝ) :=
  {curve | ∃ Q : CompatibleCompletion M,
    curve = (fun t => (tprCurve M Q t, fprCurve M Q t, netValueAt M Q t.1)) ∧
    ∀ t, tprCurve M Q t ∈ Set.Icc (0 : ℝ) 1 ∧
      fprCurve M Q t ∈ Set.Icc (0 : ℝ) 1}
  -- @realizes \(\mathfrak C\)(single compatible-law image on T)

/-- The regret function on the cutoff subtype, its minimax value, and its argmin set. -/
structure CutoffRegretData (M : ImperfectReferenceModel) where
  regret : Cutoff M → ℝ
  minimax : ℝ
  optimizers : Set (Cutoff M)

-- @node: def:cutoff-regret
noncomputable def worstCaseRegret (M : ImperfectReferenceModel) : CutoffRegretData M :=
  let R : Cutoff M → ℝ := fun t =>
    sSup {x : ℝ | ∃ Q : CompatibleCompletion M, ∃ u : Cutoff M,
      x = netValueAt M Q u.1 - netValueAt M Q t.1}
  let rstar := sInf (Set.range R)
  { regret := R
    minimax := rstar
    optimizers := {t | R t = rstar} }
  -- @realizes \(\overline{\mathcal R}(t)\)(regret on T) @realizes \(r^\star\)(infimum over T) @realizes \(\mathcal T^\star\)(argmin in T)

noncomputable def regretAt (M : ImperfectReferenceModel) (t : Cutoff M) : ℝ :=
  (worstCaseRegret M).regret t

noncomputable def minimaxRegretValue (M : ImperfectReferenceModel) : ℝ :=
  (worstCaseRegret M).minimax

noncomputable def optimizerSet (M : ImperfectReferenceModel) : Set EReal :=
  {t | ∃ ht : t ∈ M.T, (⟨t, ht⟩ : Cutoff M) ∈ (worstCaseRegret M).optimizers}

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
