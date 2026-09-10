import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Compactness.Compact

/-!
Finite atomic probability laws and their finite-transport formulation of one-Wasserstein loss.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators ENNReal
open MeasureTheory Set

/-- A labelled representation of a probability law with at most `k` atoms in `[-radius,radius]`.
Coincident locations are intentionally allowed; `toMeasure` aggregates them. -/
structure AtomicLaw (k : ℕ) (radius : ℝ) where
  weight : Fin k → ℝ
  atom : Fin k → ℝ

instance {k : ℕ} {radius : ℝ} : TopologicalSpace (AtomicLaw k radius) :=
  TopologicalSpace.induced (fun ν => (ν.weight, ν.atom)) inferInstance

/-- The canonical Borel structure inherited from the two real coordinate vectors. -/
instance {k : ℕ} {radius : ℝ} : MeasurableSpace (AtomicLaw k radius) :=
  MeasurableSpace.comap (fun ν => (ν.weight, ν.atom)) inferInstance

namespace AtomicLaw

/-- The labelled representation of the unit point mass at zero. -/
def deltaZero {k : ℕ} {radius : ℝ} : AtomicLaw k radius :=
  { weight := fun i => if i.val = 0 then 1 else 0
    atom := fun _ => 0 }

/-- The simplex and support constraints making a representation a probability law. -/
def Valid {k : ℕ} {radius : ℝ} (ν : AtomicLaw k radius) : Prop :=
  (∀ i, 0 ≤ ν.weight i) ∧
    (∑ i, ν.weight i = 1) ∧
    ∀ i, ν.atom i ∈ Set.Icc (-radius) radius

/-- Atomic-law coordinates give a homeomorphism with the pair of finite real coordinate vectors. -/
-- @node: atomicLaw_coordinateHomeomorph
def coordinateHomeomorph (k : ℕ) (radius : ℝ) :
    AtomicLaw k radius ≃ₜ (Fin k → ℝ) × (Fin k → ℝ) := by
  refine Homeomorph.mk {
    toFun := fun nu => (nu.weight, nu.atom)
    invFun := fun p => ⟨p.1, p.2⟩
    left_inv := fun nu => rfl
    right_inv := fun p => rfl } continuous_induced_dom ?_
  apply continuous_induced_rng.mpr
  exact continuous_id

/-- The valid labelled atomic parameter space is compact. -/
-- @node: atomicLaw_valid_isCompact
lemma valid_isCompact (k : ℕ) (radius : ℝ) :
    IsCompact {nu : AtomicLaw k radius | Valid nu} := by
  let T : Set ((Fin k → ℝ) × (Fin k → ℝ)) := {p |
    (∀ i, 0 ≤ p.1 i) ∧ (∑ i, p.1 i = 1) ∧
      ∀ i, p.2 i ∈ Set.Icc (-radius) radius}
  have hTclosed : IsClosed T := by
    dsimp [T]
    simp only [Set.setOf_and]
    apply IsClosed.inter
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun i => isClosed_le
          (continuous_const : Continuous (fun _ : (Fin k → ℝ) × (Fin k → ℝ) => (0 : ℝ)))
          (by fun_prop : Continuous (fun p : (Fin k → ℝ) × (Fin k → ℝ) => p.1 i)))
    apply IsClosed.inter
    · exact isClosed_eq
        (by fun_prop : Continuous (fun p : (Fin k → ℝ) × (Fin k → ℝ) => ∑ i, p.1 i))
        (continuous_const : Continuous (fun _ : (Fin k → ℝ) × (Fin k → ℝ) => (1 : ℝ)))
    · rw [show {p : (Fin k → ℝ) × (Fin k → ℝ) |
          ∀ i, p.2 i ∈ Set.Icc (-radius) radius} =
          ⋂ i, {p | -radius ≤ p.2 i} ∩ {p | p.2 i ≤ radius} by
            ext p
            simp [Set.mem_Icc]]
      exact isClosed_iInter fun i => IsClosed.inter
          (isClosed_le
            (continuous_const : Continuous
              (fun _ : (Fin k → ℝ) × (Fin k → ℝ) => -radius))
            (by fun_prop : Continuous
              (fun p : (Fin k → ℝ) × (Fin k → ℝ) => p.2 i)))
          (isClosed_le
            (by fun_prop : Continuous
              (fun p : (Fin k → ℝ) × (Fin k → ℝ) => p.2 i))
            (continuous_const : Continuous
              (fun _ : (Fin k → ℝ) × (Fin k → ℝ) => radius)))
  have hTsub : T ⊆ Set.Icc
      ((fun _ => 0), (fun _ => -radius)) ((fun _ => 1), (fun _ => radius)) := by
    intro p hp
    refine ⟨⟨hp.1, fun i => hp.2.2 i |>.1⟩, ⟨?_, fun i => hp.2.2 i |>.2⟩⟩
    intro i
    rw [← hp.2.1]
    exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
  have hTcompact : IsCompact T :=
    IsCompact.of_isClosed_subset isCompact_Icc hTclosed hTsub
  rw [show {nu : AtomicLaw k radius | Valid nu} =
      (coordinateHomeomorph k radius) ⁻¹' T by rfl]
  exact (coordinateHomeomorph k radius).isCompact_preimage.mpr hTcompact

/-- The actual carrier of at-most-`k` probability laws supported in the stated interval. -/
abbrev ProbabilityLaw (k : ℕ) (radius : ℝ) := {ν : AtomicLaw k radius // Valid ν}

/-- Valid labelled laws inherit compactness from the compact valid coordinate set. -/
-- @node: probabilityLaw_compactSpace
instance probabilityLawCompactSpace (k : ℕ) (radius : ℝ) :
    CompactSpace (ProbabilityLaw k radius) :=
  isCompact_iff_compactSpace.mp (valid_isCompact k radius)

lemma deltaZero_valid {k : ℕ} {radius : ℝ} (hk : 0 < k) (hradius : 0 ≤ radius) :
    Valid (deltaZero : AtomicLaw k radius) := by
  classical
  unfold Valid
  constructor
  · intro i
    change 0 ≤ if i.val = 0 then 1 else 0
    split_ifs <;> norm_num
  constructor
  · cases k with
    | zero => omega
    | succ k =>
      change (∑ i : Fin (k + 1), if i.val = 0 then (1 : ℝ) else 0) = 1
      rw [Fin.sum_univ_succ]
      simp
  · intro i
    change -radius ≤ 0 ∧ 0 ≤ radius
    constructor <;> linarith

/-- The bundled unit point mass at zero. -/
def deltaZeroLaw {k : ℕ} {radius : ℝ} (hk : 0 < k) (hradius : 0 ≤ radius) :
    ProbabilityLaw k radius :=
  ⟨deltaZero, deltaZero_valid hk hradius⟩

namespace ProbabilityLaw

instance {k : ℕ} {radius : ℝ} : Coe (ProbabilityLaw k radius) (AtomicLaw k radius) :=
  ⟨Subtype.val⟩

end ProbabilityLaw

/-- The probability measure represented by a finite atomic law. -/
noncomputable def toMeasure {k : ℕ} {radius : ℝ} (ν : AtomicLaw k radius) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (ν.weight i) • Measure.dirac (ν.atom i)

/-- The represented measure of a bundled valid atomic probability law. -/
noncomputable def ProbabilityLaw.toMeasure {k : ℕ} {radius : ℝ}
    (ν : ProbabilityLaw k radius) : Measure ℝ :=
  AtomicLaw.toMeasure ν.1

/-- A finite atomic law assigns a singleton its aggregate weight at that location. -/
-- @node: atomicLaw_toMeasure_singleton
lemma toMeasure_singleton {k : ℕ} {radius x : ℝ} (ν : AtomicLaw k radius)
    (hν : Valid ν) :
    ν.toMeasure {x} = ENNReal.ofReal (∑ i with ν.atom i = x, ν.weight i) := by
  simp only [toMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (MeasurableSet.singleton x)]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · simp [Set.indicator, eq_comm, Finset.sum_filter]
  · intro i hi
    exact hν.1 i

lemma ProbabilityLaw.toMeasure_isProbability {k : ℕ} {radius : ℝ}
    (ν : ProbabilityLaw k radius) : IsProbabilityMeasure ν.toMeasure := by
  constructor
  simp [ProbabilityLaw.toMeasure, AtomicLaw.toMeasure]
  convert congrArg ENNReal.ofReal ν.property.2.1 using 1 <;>
    simp [ENNReal.ofReal_sum_of_nonneg, ν.property.1]

instance {k : ℕ} {radius : ℝ} (ν : ProbabilityLaw k radius) :
    IsProbabilityMeasure ν.toMeasure := ν.toMeasure_isProbability

/-- Two valid finite representations denote the same law exactly when their represented measures
agree.  This removes all dependence on zero-mass slots and on how coincident atoms are labelled. -/
def ProbabilityLaw.MeasureEquivalent {k : ℕ} {radius : ℝ}
    (ν ξ : ProbabilityLaw k radius) : Prop :=
  ν.toMeasure = ξ.toMeasure

/-- Equivalent labelled laws have the same aggregate weight at every location. -/
-- @node: measureEquivalent_aggregate_weight
lemma ProbabilityLaw.MeasureEquivalent.aggregate_weight {k : ℕ} {radius : ℝ}
    {ν ξ : ProbabilityLaw k radius} (h : ν.MeasureEquivalent ξ) (x : ℝ) :
    (∑ i with ν.1.atom i = x, ν.1.weight i) =
      ∑ j with ξ.1.atom j = x, ξ.1.weight j := by
  have heq := congrArg (fun μ : Measure ℝ => μ {x}) h
  rw [ProbabilityLaw.toMeasure, ProbabilityLaw.toMeasure,
    toMeasure_singleton ν.1 ν.2, toMeasure_singleton ξ.1 ξ.2] at heq
  apply (ENNReal.ofReal_eq_ofReal_iff
    (Finset.sum_nonneg fun i _ => ν.2.1 i)
    (Finset.sum_nonneg fun j _ => ξ.2.1 j)).mp heq

instance probabilityLawSetoid (k : ℕ) (radius : ℝ) : Setoid (ProbabilityLaw k radius) where
  r := ProbabilityLaw.MeasureEquivalent
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Extensional at-most-`k` probability laws: valid atomic representations modulo `toMeasure`. -/
def LawModulo (k : ℕ) (radius : ℝ) := Quotient (probabilityLawSetoid k radius)

namespace LawModulo

/-- Send a valid labelled representation to its extensional law. -/
def ofProbabilityLaw {k : ℕ} {radius : ℝ} (ν : ProbabilityLaw k radius) :
    LawModulo k radius := Quotient.mk _ ν

/-- Extensional unit point mass at zero. -/
def deltaZeroLaw {k : ℕ} {radius : ℝ} (hk : 0 < k) (hradius : 0 ≤ radius) :
    LawModulo k radius :=
  ofProbabilityLaw (AtomicLaw.deltaZeroLaw hk hradius)

/-- A finite representative used internally by explicit algorithms.  Public equality remains
measure equality through the quotient. -/
noncomputable def representative {k : ℕ} {radius : ℝ} (ν : LawModulo k radius) :
    ProbabilityLaw k radius := Quotient.out ν

instance {k : ℕ} {radius : ℝ} : TopologicalSpace (LawModulo k radius) :=
  TopologicalSpace.coinduced (@ofProbabilityLaw k radius) inferInstance

instance {k : ℕ} {radius : ℝ} : MeasurableSpace (LawModulo k radius) :=
  MeasurableSpace.map (@ofProbabilityLaw k radius) inferInstance

/-- The quotient of the compact valid labelled parameter space is compact in its coinduced
topology. -/
-- @node: lawModulo_compactSpace
instance compactSpace (k : ℕ) (radius : ℝ) : CompactSpace (LawModulo k radius) := by
  rw [← isCompact_univ_iff]
  have hsurj : Function.Surjective (@ofProbabilityLaw k radius) := by
    intro q
    exact ⟨q.out, Quotient.out_eq q⟩
  rw [← Set.image_univ_of_surjective hsurj]
  exact isCompact_univ.image continuous_coinduced_rng

/-- The represented probability measure, independent of the chosen labelled representative. -/
noncomputable def toMeasure {k : ℕ} {radius : ℝ} (ν : LawModulo k radius) : Measure ℝ :=
  ν.representative.toMeasure

lemma toMeasure_eq_of_mk {k : ℕ} {radius : ℝ} (ν : ProbabilityLaw k radius) :
    toMeasure (ofProbabilityLaw ν) = ν.toMeasure := by
  exact Quotient.mk_out ν

instance {k : ℕ} {radius : ℝ} (ν : LawModulo k radius) :
    IsProbabilityMeasure ν.toMeasure := by
  unfold toMeasure
  infer_instance

end LawModulo

/-- A finite coupling between two labelled atomic representations. -/
structure TransportPlan {k : ℕ} {radius : ℝ} (ν ξ : AtomicLaw k radius) where
  mass : Fin k → Fin k → ℝ
  nonneg : ∀ i j, 0 ≤ mass i j
  fst_marginal : ∀ i, ∑ j, mass i j = ν.weight i
  snd_marginal : ∀ j, ∑ i, mass i j = ξ.weight j

/-- Equivalent labelled probability laws have a coupling supported on equal locations. -/
-- @node: measureEquivalent_zeroTransportPlan
noncomputable def ProbabilityLaw.MeasureEquivalent.zeroTransportPlan
    {k : ℕ} {radius : ℝ} (ν ξ : ProbabilityLaw k radius)
    (h : ν.MeasureEquivalent ξ) : TransportPlan ν.1 ξ.1 := by
  let A : ℝ → ℝ := fun x => ∑ j with ξ.1.atom j = x, ξ.1.weight j
  refine {
    mass := fun i j => if ν.1.atom i = ξ.1.atom j then
      ν.1.weight i * ξ.1.weight j / A (ν.1.atom i) else 0
    nonneg := ?_
    fst_marginal := ?_
    snd_marginal := ?_ }
  · intro i j
    split_ifs
    · exact div_nonneg (mul_nonneg (ν.2.1 i) (ξ.2.1 j))
        (Finset.sum_nonneg fun l _ => ξ.2.1 l)
    · exact le_rfl
  · intro i
    by_cases hwi : ν.1.weight i = 0
    · simp [hwi]
    have hAi : 0 < A (ν.1.atom i) := by
      change 0 < ∑ j with ξ.1.atom j = ν.1.atom i, ξ.1.weight j
      rw [← ProbabilityLaw.MeasureEquivalent.aggregate_weight h (ν.1.atom i)]
      exact lt_of_lt_of_le (lt_of_le_of_ne (ν.2.1 i) (Ne.symm hwi))
        (Finset.single_le_sum (fun l _ => ν.2.1 l)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩))
    calc
      (∑ j, if ν.1.atom i = ξ.1.atom j then
          ν.1.weight i * ξ.1.weight j / A (ν.1.atom i) else 0) =
          ∑ j with ξ.1.atom j = ν.1.atom i,
            ν.1.weight i * ξ.1.weight j / A (ν.1.atom i) := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hij : ξ.1.atom j = ν.1.atom i
              · simp only [hij, if_pos]
              · have hij' : ¬ν.1.atom i = ξ.1.atom j := fun e => hij e.symm
                simp only [hij, hij']
      _ = (ν.1.weight i / A (ν.1.atom i)) *
          (∑ j with ξ.1.atom j = ν.1.atom i, ξ.1.weight j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = ν.1.weight i := by
            rw [show (∑ j with ξ.1.atom j = ν.1.atom i, ξ.1.weight j) =
              A (ν.1.atom i) by rfl]
            exact div_mul_cancel₀ _ (ne_of_gt hAi)
  · intro j
    by_cases hwj : ξ.1.weight j = 0
    · simp [hwj]
    have hAj : 0 < A (ξ.1.atom j) :=
      lt_of_lt_of_le (lt_of_le_of_ne (ξ.2.1 j) (Ne.symm hwj))
        (Finset.single_le_sum (fun l _ => ξ.2.1 l)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩))
    calc
      (∑ i, if ν.1.atom i = ξ.1.atom j then
          ν.1.weight i * ξ.1.weight j / A (ν.1.atom i) else 0) =
          ∑ i with ν.1.atom i = ξ.1.atom j,
            ν.1.weight i * ξ.1.weight j / A (ξ.1.atom j) := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hij : ν.1.atom i = ξ.1.atom j <;> simp [hij]
      _ = ((∑ i with ν.1.atom i = ξ.1.atom j, ν.1.weight i) *
            ξ.1.weight j) / A (ξ.1.atom j) := by
            simp only [div_eq_mul_inv, ← Finset.sum_mul]
      _ = ξ.1.weight j := by
            rw [ProbabilityLaw.MeasureEquivalent.aggregate_weight h (ξ.1.atom j)]
            change A (ξ.1.atom j) * ξ.1.weight j / A (ξ.1.atom j) = _
            field_simp

/-- Cost of a finite transport plan for absolute-distance loss. -/
def transportCost {k : ℕ} {radius : ℝ} {ν ξ : AtomicLaw k radius}
    (γ : TransportPlan ν ξ) : ℝ :=
  ∑ i, ∑ j, γ.mass i j * |ν.atom i - ξ.atom j|

/-- The coupling between equivalent representations has zero transport cost. -/
-- @node: measureEquivalent_zeroTransportCost
lemma ProbabilityLaw.MeasureEquivalent.zeroTransportCost
    {k : ℕ} {radius : ℝ} (ν ξ : ProbabilityLaw k radius)
    (h : ν.MeasureEquivalent ξ) :
    transportCost (h.zeroTransportPlan ν ξ) = 0 := by
  classical
  unfold transportCost ProbabilityLaw.MeasureEquivalent.zeroTransportPlan
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hij : ν.1.atom i = ξ.1.atom j
  · simp [hij]
  · simp [hij]

/-- One-Wasserstein distance, definitionally the infimum over the finite transport polytope.
    @realizes \(W_1\)(infimum of finite transport costs) -/
noncomputable def wass1 {k : ℕ} {radius : ℝ} (ν ξ : AtomicLaw k radius) : ℝ :=
  sInf {c : ℝ | ∃ γ : TransportPlan ν ξ, transportCost γ = c}

/-- Every feasible transport plan upper-bounds the infimal transport cost. -/
-- @node: wass1_le_of_plan
lemma wass1_le_of_plan {k : ℕ} {radius : ℝ} {ν ξ : AtomicLaw k radius}
    (γ : TransportPlan ν ξ) : wass1 ν ξ ≤ transportCost γ := by
  unfold wass1
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨q, rfl⟩
    unfold transportCost
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (q.nonneg i j) (abs_nonneg _)
  · exact ⟨γ, rfl⟩

/-- The finite transport polytope attains the infimum defining `wass1`. -/
-- @node: wass1_optimal_plan
lemma wass1_optimal_plan {k : ℕ} {radius : ℝ} {ν ξ : AtomicLaw k radius}
    (hν : Valid ν) (hξ : Valid ξ) :
    ∃ γ : TransportPlan ν ξ, transportCost γ = wass1 ν ξ := by
  classical
  let S : Set (Fin k → Fin k → ℝ) := {m |
    (∀ i j, 0 ≤ m i j) ∧
    (∀ i, ∑ j, m i j = ν.weight i) ∧
    ∀ j, ∑ i, m i j = ξ.weight j}
  have hSne : S.Nonempty := by
    refine ⟨fun i j => ν.weight i * ξ.weight j, ?_⟩
    refine ⟨fun i j => mul_nonneg (hν.1 i) (hξ.1 j), ?_, ?_⟩
    · intro i
      rw [← Finset.mul_sum, hξ.2.1, mul_one]
    · intro j
      rw [← Finset.sum_mul, hν.2.1, one_mul]
  have hweight_le_one (i : Fin k) : ν.weight i ≤ 1 := by
    rw [← hν.2.1]
    exact Finset.single_le_sum (fun j _ => hν.1 j) (Finset.mem_univ i)
  have hSsub : S ⊆ Set.Icc (fun _ _ => 0) (fun _ _ => 1) := by
    intro m hm
    refine ⟨fun i j => hm.1 i j, fun i j => ?_⟩
    calc
      m i j ≤ ∑ r, m i r :=
        Finset.single_le_sum (fun r _ => hm.1 i r) (Finset.mem_univ j)
      _ = ν.weight i := hm.2.1 i
      _ ≤ 1 := hweight_le_one i
  have hSclosed : IsClosed S := by
    dsimp [S]
    simp only [Set.setOf_and]
    apply IsClosed.inter
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun i => isClosed_iInter fun j =>
          isClosed_le
            (continuous_const : Continuous (fun _ : Fin k → Fin k → ℝ => (0 : ℝ)))
            (by fun_prop : Continuous (fun m : Fin k → Fin k → ℝ => m i j)))
    apply IsClosed.inter
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun i => isClosed_eq
          (by fun_prop : Continuous (fun m : Fin k → Fin k → ℝ => ∑ j, m i j))
          (by fun_prop : Continuous (fun _ : Fin k → Fin k → ℝ => ν.weight i)))
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun j => isClosed_eq
          (by fun_prop : Continuous (fun m : Fin k → Fin k → ℝ => ∑ i, m i j))
          (by fun_prop : Continuous (fun _ : Fin k → Fin k → ℝ => ξ.weight j)))
  have hScompact : IsCompact S :=
    IsCompact.of_isClosed_subset isCompact_Icc hSclosed hSsub
  let cost : (Fin k → Fin k → ℝ) → ℝ := fun m =>
    ∑ i, ∑ j, m i j * |ν.atom i - ξ.atom j|
  have hcost_cont : Continuous cost := by
    unfold cost
    fun_prop
  obtain ⟨m, hmS, hmmin⟩ := hScompact.exists_isMinOn hSne hcost_cont.continuousOn
  let γ : TransportPlan ν ξ :=
    { mass := m
      nonneg := hmS.1
      fst_marginal := hmS.2.1
      snd_marginal := hmS.2.2 }
  refine ⟨γ, ?_⟩
  have hcost_nonneg (q : TransportPlan ν ξ) : 0 ≤ transportCost q := by
    unfold transportCost
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (q.nonneg i j) (abs_nonneg _)
  have hvalues_ne : ({c : ℝ | ∃ q : TransportPlan ν ξ, transportCost q = c}).Nonempty :=
    ⟨transportCost γ, γ, rfl⟩
  have hvalues_bdd : BddBelow {c : ℝ | ∃ q : TransportPlan ν ξ, transportCost q = c} := by
    refine ⟨0, ?_⟩
    rintro c ⟨q, rfl⟩
    exact hcost_nonneg q
  apply le_antisymm
  · unfold wass1
    apply le_csInf hvalues_ne
    rintro c ⟨q, rfl⟩
    simpa [cost, transportCost, γ] using
      hmmin ⟨q.nonneg, q.fst_marginal, q.snd_marginal⟩
  · unfold wass1
    exact csInf_le hvalues_bdd ⟨γ, rfl⟩

/-- Finite-transport Wasserstein loss is nonnegative on valid labelled laws. -/
-- @node: atomicLaw_wass1_nonneg
lemma wass1_nonneg {k : ℕ} {radius : ℝ} {ν ξ : AtomicLaw k radius}
    (hν : Valid ν) (hξ : Valid ξ) : 0 ≤ wass1 ν ξ := by
  obtain ⟨γ, hγ⟩ := wass1_optimal_plan hν hξ
  rw [← hγ]
  unfold transportCost
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (γ.nonneg i j) (abs_nonneg _)

/-- Transposing a finite coupling proves symmetry of finite-transport Wasserstein loss. -/
-- @node: atomicLaw_wass1_comm
lemma wass1_comm {k : ℕ} {radius : ℝ} (ν ξ : AtomicLaw k radius) :
    wass1 ν ξ = wass1 ξ ν := by
  unfold wass1
  congr 1
  ext c
  constructor
  · rintro ⟨γ, rfl⟩
    let γ' : TransportPlan ξ ν := {
      mass := fun i j => γ.mass j i
      nonneg := fun i j => γ.nonneg j i
      fst_marginal := γ.snd_marginal
      snd_marginal := γ.fst_marginal }
    refine ⟨γ', ?_⟩
    unfold transportCost γ'
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [abs_sub_comm]
  · rintro ⟨γ, rfl⟩
    let γ' : TransportPlan ν ξ := {
      mass := fun i j => γ.mass j i
      nonneg := fun i j => γ.nonneg j i
      fst_marginal := γ.snd_marginal
      snd_marginal := γ.fst_marginal }
    refine ⟨γ', ?_⟩
    unfold transportCost γ'
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [abs_sub_comm]

/-- A valid labelled law has zero finite-transport Wasserstein loss from itself. -/
-- @node: atomicLaw_wass1_self
lemma wass1_self {k : ℕ} {radius : ℝ} (ν : AtomicLaw k radius) (hν : Valid ν) :
    wass1 ν ν = 0 := by
  let γ : TransportPlan ν ν := {
    mass := fun i j => if i = j then ν.weight i else 0
    nonneg := fun i j => by
      split_ifs with hij
      · exact hν.1 i
      · exact le_rfl
    fst_marginal := fun i => by simp
    snd_marginal := fun j => by simp [eq_comm] }
  apply le_antisymm
  · calc
      wass1 ν ν ≤ transportCost γ := wass1_le_of_plan γ
      _ = 0 := by simp [transportCost, γ]
  · exact wass1_nonneg hν hν

/-- Finite-transport loss vanishes between measure-equivalent valid representations. -/
-- @node: measureEquivalent_wass1_eq_zero
lemma ProbabilityLaw.MeasureEquivalent.wass1_eq_zero
    {k : ℕ} {radius : ℝ} (ν ξ : ProbabilityLaw k radius)
    (h : ν.MeasureEquivalent ξ) : wass1 ν.1 ξ.1 = 0 := by
  apply le_antisymm
  · calc
      wass1 ν.1 ξ.1 ≤ transportCost (h.zeroTransportPlan ν ξ) :=
        wass1_le_of_plan (h.zeroTransportPlan ν ξ)
      _ = 0 := h.zeroTransportCost ν ξ
  · exact wass1_nonneg ν.2 ξ.2

/-- A zero marginal forces every entry in the corresponding column of a nonnegative plan to
vanish. -/
-- @node: transportPlan_mass_eq_zero_of_snd_weight_eq_zero
lemma TransportPlan.mass_eq_zero_of_snd_weight_eq_zero
    {k : ℕ} {radius : ℝ} {nu xi : AtomicLaw k radius}
    (gamma : TransportPlan nu xi) {j : Fin k} (hj : xi.weight j = 0) (i : Fin k) :
    gamma.mass i j = 0 := by
  apply le_antisymm
  · calc
      gamma.mass i j ≤ ∑ r, gamma.mass r j :=
        Finset.single_le_sum (fun r _ => gamma.nonneg r j) (Finset.mem_univ i)
      _ = 0 := by rw [gamma.snd_marginal j, hj]
  · exact gamma.nonneg i j

/-- Glue two finite couplings through their common intermediate marginal, interpreting every
zero-mass intermediate slice as zero. -/
-- @node: transportPlan_glue
noncomputable def TransportPlan.glue
    {k : ℕ} {radius : ℝ} {nu xi zeta : AtomicLaw k radius}
    (gamma : TransportPlan nu xi) (eta : TransportPlan xi zeta) : TransportPlan nu zeta := by
  classical
  refine {
    mass := fun i l => ∑ j, if xi.weight j = 0 then 0 else
      gamma.mass i j * eta.mass j l / xi.weight j
    nonneg := ?_
    fst_marginal := ?_
    snd_marginal := ?_ }
  · intro i l
    exact Finset.sum_nonneg fun j _ => by
      split_ifs with hj
      · exact le_rfl
      · exact div_nonneg (mul_nonneg (gamma.nonneg i j) (eta.nonneg j l))
          (lt_of_le_of_ne (by
            rw [← gamma.snd_marginal j]
            exact Finset.sum_nonneg fun r _ => gamma.nonneg r j) (Ne.symm hj)).le
  · intro i
    rw [Finset.sum_comm]
    calc
      (∑ j, ∑ l, if xi.weight j = 0 then 0 else
          gamma.mass i j * eta.mass j l / xi.weight j) =
          ∑ j, gamma.mass i j := by
            apply Finset.sum_congr rfl
            intro j hjmem
            by_cases hj : xi.weight j = 0
            · simp [hj, gamma.mass_eq_zero_of_snd_weight_eq_zero hj i]
            · simp only [hj, if_false, div_eq_mul_inv, ← Finset.sum_mul,
                ← Finset.mul_sum, eta.fst_marginal j]
              rw [mul_assoc, mul_inv_cancel₀ hj, mul_one]
      _ = nu.weight i := gamma.fst_marginal i
  · intro l
    rw [Finset.sum_comm]
    calc
      (∑ j, ∑ i, if xi.weight j = 0 then 0 else
          gamma.mass i j * eta.mass j l / xi.weight j) =
          ∑ j, eta.mass j l := by
            apply Finset.sum_congr rfl
            intro j hjmem
            by_cases hj : xi.weight j = 0
            · have heta : eta.mass j l = 0 := by
                apply le_antisymm
                · calc
                    eta.mass j l ≤ ∑ r, eta.mass j r :=
                      Finset.single_le_sum (fun r _ => eta.nonneg j r) (Finset.mem_univ l)
                    _ = 0 := by rw [eta.fst_marginal j, hj]
                · exact eta.nonneg j l
              simp [hj, heta]
            · simp only [hj, if_false, div_eq_mul_inv, ← Finset.sum_mul,
                ← Finset.sum_mul, gamma.snd_marginal j]
              field_simp
      _ = zeta.weight l := eta.snd_marginal l

/-- The glued coupling costs at most the sum of the two input coupling costs. -/
-- @node: transportCost_glue_le
lemma transportCost_glue_le
    {k : ℕ} {radius : ℝ} {nu xi zeta : AtomicLaw k radius}
    (gamma : TransportPlan nu xi) (eta : TransportPlan xi zeta) :
    transportCost (gamma.glue eta) ≤ transportCost gamma + transportCost eta := by
  classical
  let q : Fin k → Fin k → Fin k → ℝ := fun i j l =>
    if xi.weight j = 0 then 0 else gamma.mass i j * eta.mass j l / xi.weight j
  have hq_nonneg (i j l : Fin k) : 0 ≤ q i j l := by
    dsimp [q]
    split_ifs with hj
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (gamma.nonneg i j) (eta.nonneg j l))
        (lt_of_le_of_ne (by
          rw [← gamma.snd_marginal j]
          exact Finset.sum_nonneg fun r _ => gamma.nonneg r j) (Ne.symm hj)).le
  have hleft :
      (∑ i, ∑ l, ∑ j, q i j l * |nu.atom i - xi.atom j|) =
        transportCost gamma := by
    rw [show (∑ i, ∑ l, ∑ j, q i j l * |nu.atom i - xi.atom j|) =
      ∑ i, ∑ j, ∑ l, q i j l * |nu.atom i - xi.atom j| by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm]
    unfold transportCost
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hjmem
    by_cases hj : xi.weight j = 0
    · simp [q, hj, gamma.mass_eq_zero_of_snd_weight_eq_zero hj i]
    · simp only [q, hj, if_false]
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum,
        eta.fst_marginal j]
      field_simp
  have hright :
      (∑ i, ∑ l, ∑ j, q i j l * |xi.atom j - zeta.atom l|) =
        transportCost eta := by
    rw [show (∑ i, ∑ l, ∑ j, q i j l * |xi.atom j - zeta.atom l|) =
      ∑ j, ∑ l, ∑ i, q i j l * |xi.atom j - zeta.atom l| by
        calc
          (∑ i, ∑ l, ∑ j, q i j l * |xi.atom j - zeta.atom l|) =
              ∑ i, ∑ j, ∑ l, q i j l * |xi.atom j - zeta.atom l| := by
                apply Finset.sum_congr rfl
                intro i hi
                exact Finset.sum_comm
          _ = ∑ j, ∑ i, ∑ l, q i j l * |xi.atom j - zeta.atom l| :=
            Finset.sum_comm
          _ = ∑ j, ∑ l, ∑ i, q i j l * |xi.atom j - zeta.atom l| := by
                apply Finset.sum_congr rfl
                intro j hj
                exact Finset.sum_comm]
    unfold transportCost
    apply Finset.sum_congr rfl
    intro j hjmem
    apply Finset.sum_congr rfl
    intro l hlmem
    by_cases hj : xi.weight j = 0
    · have heta : eta.mass j l = 0 := by
        apply le_antisymm
        · calc
            eta.mass j l ≤ ∑ r, eta.mass j r :=
              Finset.single_le_sum (fun r _ => eta.nonneg j r) (Finset.mem_univ l)
            _ = 0 := by rw [eta.fst_marginal j, hj]
        · exact eta.nonneg j l
      simp [q, hj, heta]
    · simp only [q, hj, if_false]
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.sum_mul,
        gamma.snd_marginal j]
      field_simp
  calc
    transportCost (gamma.glue eta) =
        ∑ i, ∑ l, (∑ j, q i j l) * |nu.atom i - zeta.atom l| := by
          rfl
    _ ≤ ∑ i, ∑ l, ∑ j,
        q i j l * (|nu.atom i - xi.atom j| + |xi.atom j - zeta.atom l|) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro l hl
          rw [Finset.sum_mul]
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) (hq_nonneg i j l)
    _ = (∑ i, ∑ l, ∑ j, q i j l * |nu.atom i - xi.atom j|) +
        (∑ i, ∑ l, ∑ j, q i j l * |xi.atom j - zeta.atom l|) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
    _ = transportCost gamma + transportCost eta := by rw [hleft, hright]

/-- Finite-transport Wasserstein loss satisfies the triangle inequality on valid laws. -/
-- @node: atomicLaw_wass1_triangle
lemma wass1_triangle {k : ℕ} {radius : ℝ} (nu xi zeta : ProbabilityLaw k radius) :
    wass1 nu.1 zeta.1 ≤ wass1 nu.1 xi.1 + wass1 xi.1 zeta.1 := by
  obtain ⟨gamma, hgamma⟩ := wass1_optimal_plan nu.2 xi.2
  obtain ⟨eta, heta⟩ := wass1_optimal_plan xi.2 zeta.2
  calc
    wass1 nu.1 zeta.1 ≤ transportCost (gamma.glue eta) := wass1_le_of_plan _
    _ ≤ transportCost gamma + transportCost eta := transportCost_glue_le gamma eta
    _ = wass1 nu.1 xi.1 + wass1 xi.1 zeta.1 := by rw [hgamma, heta]

/-- A zero-cost nonnegative coupling has no mass between distinct locations. -/
-- @node: transportPlan_mass_eq_zero_of_cost_eq_zero
lemma TransportPlan.mass_eq_zero_of_cost_eq_zero
    {k : ℕ} {radius : ℝ} {nu xi : AtomicLaw k radius}
    (gamma : TransportPlan nu xi) (hcost : transportCost gamma = 0)
    {i j : Fin k} (hij : nu.atom i ≠ xi.atom j) : gamma.mass i j = 0 := by
  have hterm_nonneg (r s : Fin k) :
      0 ≤ gamma.mass r s * |nu.atom r - xi.atom s| :=
    mul_nonneg (gamma.nonneg r s) (abs_nonneg _)
  have hle : gamma.mass i j * |nu.atom i - xi.atom j| ≤ transportCost gamma := by
    unfold transportCost
    calc
      gamma.mass i j * |nu.atom i - xi.atom j| ≤
          ∑ s, gamma.mass i s * |nu.atom i - xi.atom s| :=
        Finset.single_le_sum (fun s _ => hterm_nonneg i s) (Finset.mem_univ j)
      _ ≤ ∑ r, ∑ s, gamma.mass r s * |nu.atom r - xi.atom s| :=
        Finset.single_le_sum
          (fun r _ => Finset.sum_nonneg fun s _ => hterm_nonneg r s) (Finset.mem_univ i)
  have hprod : gamma.mass i j * |nu.atom i - xi.atom j| = 0 := by
    apply le_antisymm
    · simpa [hcost] using hle
    · exact hterm_nonneg i j
  rcases mul_eq_zero.mp hprod with hmass | habs
  · exact hmass
  · exact False.elim (hij (sub_eq_zero.mp (abs_eq_zero.mp habs)))

/-- A zero-cost coupling identifies the represented probability measures. -/
-- @node: measureEquivalent_of_transportCost_eq_zero
lemma measureEquivalent_of_transportCost_eq_zero
    {k : ℕ} {radius : ℝ} (nu xi : ProbabilityLaw k radius)
    (gamma : TransportPlan nu.1 xi.1) (hcost : transportCost gamma = 0) :
    nu.MeasureEquivalent xi := by
  classical
  unfold ProbabilityLaw.MeasureEquivalent
  ext s hs
  simp only [ProbabilityLaw.toMeasure, AtomicLaw.toMeasure, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.smul_apply, Measure.dirac_apply' _ hs]
  have hnu :
      (∑ i, ENNReal.ofReal (nu.1.weight i) • s.indicator 1 (nu.1.atom i)) =
        ∑ i, ENNReal.ofReal (nu.1.weight i * s.indicator 1 (nu.1.atom i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases his : nu.1.atom i ∈ s <;> simp [Set.indicator, his]
  have hxi :
      (∑ j, ENNReal.ofReal (xi.1.weight j) • s.indicator 1 (xi.1.atom j)) =
        ∑ j, ENNReal.ofReal (xi.1.weight j * s.indicator 1 (xi.1.atom j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjs : xi.1.atom j ∈ s <;> simp [Set.indicator, hjs]
  rw [hnu, hxi]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      by_cases his : nu.1.atom i ∈ s <;> simp [Set.indicator, his, nu.2.1 i]),
    ← ENNReal.ofReal_sum_of_nonneg (fun j _ => by
      by_cases hjs : xi.1.atom j ∈ s <;> simp [Set.indicator, hjs, xi.2.1 j])]
  congr 1
  calc
    (∑ i, nu.1.weight i * s.indicator 1 (nu.1.atom i)) =
        ∑ i, ∑ j, gamma.mass i j * s.indicator 1 (nu.1.atom i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← gamma.fst_marginal i, Finset.sum_mul]
    _ = ∑ j, ∑ i, gamma.mass i j * s.indicator 1 (xi.1.atom j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hij : nu.1.atom i = xi.1.atom j
          · rw [hij]
          · rw [gamma.mass_eq_zero_of_cost_eq_zero hcost hij]
            simp
    _ = ∑ j, xi.1.weight j * s.indicator 1 (xi.1.atom j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.sum_mul, gamma.snd_marginal j]

/-- Wasserstein loss vanishes exactly between measure-equivalent valid representations. -/
-- @node: wass1_eq_zero_iff_measureEquivalent
lemma wass1_eq_zero_iff_measureEquivalent
    {k : ℕ} {radius : ℝ} (nu xi : ProbabilityLaw k radius) :
    wass1 nu.1 xi.1 = 0 ↔ nu.MeasureEquivalent xi := by
  constructor
  · intro h
    obtain ⟨gamma, hgamma⟩ := wass1_optimal_plan nu.2 xi.2
    exact measureEquivalent_of_transportCost_eq_zero nu xi gamma (hgamma.trans h)
  · exact fun h => h.wass1_eq_zero nu xi

/-- Wasserstein loss is unchanged when its left labelled representation is replaced by an
equivalent one. -/
-- @node: atomicLaw_wass1_congr_left
lemma wass1_congr_left {k : ℕ} {radius : ℝ}
    {nu nu' xi : ProbabilityLaw k radius} (h : nu.MeasureEquivalent nu') :
    wass1 nu.1 xi.1 = wass1 nu'.1 xi.1 := by
  apply le_antisymm
  · calc
      wass1 nu.1 xi.1 ≤ wass1 nu.1 nu'.1 + wass1 nu'.1 xi.1 :=
        wass1_triangle nu nu' xi
      _ = wass1 nu'.1 xi.1 := by rw [h.wass1_eq_zero nu nu', zero_add]
  · calc
      wass1 nu'.1 xi.1 ≤ wass1 nu'.1 nu.1 + wass1 nu.1 xi.1 :=
        wass1_triangle nu' nu xi
      _ = wass1 nu.1 xi.1 := by
        rw [ProbabilityLaw.MeasureEquivalent.wass1_eq_zero nu' nu h.symm, zero_add]

/-- Wasserstein loss is unchanged when its right labelled representation is replaced by an
equivalent one. -/
-- @node: atomicLaw_wass1_congr_right
lemma wass1_congr_right {k : ℕ} {radius : ℝ}
    {nu xi xi' : ProbabilityLaw k radius} (h : xi.MeasureEquivalent xi') :
    wass1 nu.1 xi.1 = wass1 nu.1 xi'.1 := by
  rw [wass1_comm nu.1 xi.1, wass1_comm nu.1 xi'.1]
  exact wass1_congr_left h

/-- Wasserstein loss is invariant under equivalent labelled representations in both arguments. -/
-- @node: atomicLaw_wass1_congr
lemma wass1_congr {k : ℕ} {radius : ℝ}
    {nu nu' xi xi' : ProbabilityLaw k radius}
    (hnu : nu.MeasureEquivalent nu') (hxi : xi.MeasureEquivalent xi') :
    wass1 nu.1 xi.1 = wass1 nu'.1 xi'.1 :=
  (wass1_congr_left hnu).trans (wass1_congr_right hxi)

/-- Wasserstein loss on extensional laws, computed using their finite representatives. -/
noncomputable def LawModulo.wass1 {k : ℕ} {radius : ℝ}
    (ν ξ : LawModulo k radius) : ℝ :=
  AtomicLaw.wass1 ν.representative.1 ξ.representative.1

namespace LawModulo

/-- Extensional Wasserstein loss is nonnegative. -/
lemma wass1_nonneg {k : ℕ} {radius : ℝ} (nu xi : LawModulo k radius) :
    0 ≤ nu.wass1 xi :=
  AtomicLaw.wass1_nonneg nu.representative.2 xi.representative.2

/-- Extensional Wasserstein loss vanishes on the diagonal. -/
-- @node: lawModulo_wass1_self
lemma wass1_self {k : ℕ} {radius : ℝ} (nu : LawModulo k radius) :
    nu.wass1 nu = 0 :=
  AtomicLaw.wass1_self nu.representative.1 nu.representative.2

/-- Extensional Wasserstein loss is symmetric. -/
-- @node: lawModulo_wass1_comm
lemma wass1_comm {k : ℕ} {radius : ℝ} (nu xi : LawModulo k radius) :
    nu.wass1 xi = xi.wass1 nu :=
  AtomicLaw.wass1_comm _ _

/-- Extensional Wasserstein loss satisfies the triangle inequality. -/
-- @node: lawModulo_wass1_triangle
lemma wass1_triangle {k : ℕ} {radius : ℝ} (nu xi zeta : LawModulo k radius) :
    nu.wass1 zeta ≤ nu.wass1 xi + xi.wass1 zeta :=
  AtomicLaw.wass1_triangle nu.representative xi.representative zeta.representative

/-- Extensional Wasserstein loss separates quotient laws. -/
-- @node: lawModulo_eq_of_wass1_eq_zero
lemma eq_of_wass1_eq_zero {k : ℕ} {radius : ℝ} {nu xi : LawModulo k radius}
    (h : nu.wass1 xi = 0) : nu = xi := by
  have hrel : nu.representative.MeasureEquivalent xi.representative :=
    (AtomicLaw.wass1_eq_zero_iff_measureEquivalent _ _).mp h
  calc
    nu = ofProbabilityLaw nu.representative := (Quotient.out_eq nu).symm
    _ = ofProbabilityLaw xi.representative := Quotient.sound hrel
    _ = xi := Quotient.out_eq xi

/-- The raw metric structure whose distance is exactly extensional Wasserstein loss.  Its induced
topology is compared with the pre-existing quotient topology before an instance is installed. -/
-- @node: lawModulo_rawMetricSpace
noncomputable def rawMetricSpace (k : ℕ) (radius : ℝ) : MetricSpace (LawModulo k radius) := by
  let d : Dist (LawModulo k radius) := ⟨LawModulo.wass1⟩
  letI : Dist (LawModulo k radius) := d
  let pm : PseudoMetricSpace (LawModulo k radius) := {
    dist_self := wass1_self
    dist_comm := wass1_comm
    dist_triangle := wass1_triangle }
  exact @MetricSpace.mk _ pm (fun {_ _} h => eq_of_wass1_eq_zero h)

/-- The raw metric distance unfolds to extensional Wasserstein loss. -/
-- @node: lawModulo_rawMetricSpace_dist
lemma rawMetricSpace_dist {k : ℕ} {radius : ℝ} (nu xi : LawModulo k radius) :
    @dist (LawModulo k radius) (rawMetricSpace k radius).toPseudoMetricSpace.toDist nu xi =
      nu.wass1 xi := by
  rfl

/-- Couple common coordinate mass diagonally and the two residual marginals by their normalized
product.  This coupling is used only to compare nearby labelled representatives. -/
-- @node: probabilityLaw_coordinateTransportPlan
noncomputable def probabilityLaw_coordinateTransportPlan
    {k : ℕ} {radius : ℝ} (nu xi : ProbabilityLaw k radius) :
    TransportPlan nu.1 xi.1 := by
  classical
  let a : Fin k → ℝ := fun i => nu.1.weight i - min (nu.1.weight i) (xi.1.weight i)
  let b : Fin k → ℝ := fun i => xi.1.weight i - min (nu.1.weight i) (xi.1.weight i)
  let s : ℝ := ∑ i, a i
  have ha (i : Fin k) : 0 ≤ a i := sub_nonneg.mpr (min_le_left _ _)
  have hb (i : Fin k) : 0 ≤ b i := sub_nonneg.mpr (min_le_right _ _)
  have hs : ∑ i, b i = s := by
    dsimp [a, b, s]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, nu.2.2.1, xi.2.2.1]
  refine {
    mass := fun i j => (if i = j then min (nu.1.weight i) (xi.1.weight i) else 0) +
      if s = 0 then 0 else a i * b j / s
    nonneg := ?_
    fst_marginal := ?_
    snd_marginal := ?_ }
  · intro i j
    apply add_nonneg
    · split_ifs
      · exact le_min (nu.2.1 i) (xi.2.1 i)
      · exact le_rfl
    · split_ifs with hzero
      · exact le_rfl
      · exact div_nonneg (mul_nonneg (ha i) (hb j))
          (Finset.sum_nonneg fun r _ => ha r)
  · intro i
    rw [Finset.sum_add_distrib]
    rw [show (∑ j, if i = j then min (nu.1.weight i) (xi.1.weight i) else 0) =
        min (nu.1.weight i) (xi.1.weight i) by simp]
    by_cases hzero : s = 0
    · have hai : a i = 0 := by
        apply le_antisymm
        · calc
            a i ≤ ∑ r, a r :=
              Finset.single_le_sum (fun r _ => ha r) (Finset.mem_univ i)
            _ = 0 := hzero
        · exact ha i
      have hmin : min (nu.1.weight i) (xi.1.weight i) = nu.1.weight i :=
        (eq_of_sub_eq_zero (by simpa [a] using hai)).symm
      simp [hzero, hmin]
    · simp only [hzero, if_false]
      calc
        min (nu.1.weight i) (xi.1.weight i) + ∑ j, a i * b j / s =
            min (nu.1.weight i) (xi.1.weight i) + a i := by
          congr 1
          calc
            (∑ j, a i * b j / s) = a i * (∑ j, b j) / s := by
              simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum]
            _ = a i := by rw [hs]; exact mul_div_cancel_right₀ _ hzero
        _ = nu.1.weight i := by dsimp [a]; ring
  · intro j
    rw [Finset.sum_add_distrib]
    rw [show (∑ i, if i = j then min (nu.1.weight i) (xi.1.weight i) else 0) =
        min (nu.1.weight j) (xi.1.weight j) by simp]
    by_cases hzero : s = 0
    · have hbj : b j = 0 := by
        apply le_antisymm
        · calc
            b j ≤ ∑ r, b r :=
              Finset.single_le_sum (fun r _ => hb r) (Finset.mem_univ j)
            _ = 0 := hs.trans hzero
        · exact hb j
      have hmin : min (nu.1.weight j) (xi.1.weight j) = xi.1.weight j :=
        (eq_of_sub_eq_zero (by simpa [b] using hbj)).symm
      simp [hzero, hmin]
    · simp only [hzero, if_false]
      calc
        min (nu.1.weight j) (xi.1.weight j) + ∑ i, a i * b j / s =
            min (nu.1.weight j) (xi.1.weight j) + b j := by
          congr 1
          calc
            (∑ i, a i * b j / s) = (∑ i, a i) * b j / s := by
              simp only [div_eq_mul_inv, ← Finset.sum_mul]
            _ = b j := by change s * b j / s = b j; field_simp
        _ = xi.1.weight j := by dsimp [b]; ring

/-- The coordinate coupling gives a continuous upper bound for Wasserstein loss. -/
-- @node: atomicLaw_wass1_le_coordinateBound
lemma wass1_le_coordinateBound {k : ℕ} {radius : ℝ}
    (nu xi : ProbabilityLaw k radius) :
    AtomicLaw.wass1 nu.1 xi.1 ≤
      (∑ i, min (nu.1.weight i) (xi.1.weight i) *
        |nu.1.atom i - xi.1.atom i|) +
      2 * radius *
        (∑ i, (nu.1.weight i - min (nu.1.weight i) (xi.1.weight i))) := by
  classical
  let a : Fin k → ℝ := fun i => nu.1.weight i - min (nu.1.weight i) (xi.1.weight i)
  let b : Fin k → ℝ := fun i => xi.1.weight i - min (nu.1.weight i) (xi.1.weight i)
  let s : ℝ := ∑ i, a i
  let gamma := probabilityLaw_coordinateTransportPlan nu xi
  have ha (i : Fin k) : 0 ≤ a i := sub_nonneg.mpr (min_le_left _ _)
  have hb (i : Fin k) : 0 ≤ b i := sub_nonneg.mpr (min_le_right _ _)
  have hs : ∑ i, b i = s := by
    dsimp [a, b, s]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, nu.2.2.1, xi.2.2.1]
  have hdist (i j : Fin k) : |nu.1.atom i - xi.1.atom j| ≤ 2 * radius := by
    calc
      |nu.1.atom i - xi.1.atom j| ≤ |nu.1.atom i| + |xi.1.atom j| := abs_sub _ _
      _ ≤ radius + radius := add_le_add (abs_le.mpr (nu.2.2.2 i)) (abs_le.mpr (xi.2.2.2 j))
      _ = 2 * radius := by ring
  calc
    AtomicLaw.wass1 nu.1 xi.1 ≤ transportCost gamma := wass1_le_of_plan gamma
    _ ≤ (∑ i, min (nu.1.weight i) (xi.1.weight i) *
          |nu.1.atom i - xi.1.atom i|) + 2 * radius * s := by
      unfold transportCost gamma probabilityLaw_coordinateTransportPlan
      simp_rw [add_mul, Finset.sum_add_distrib]
      apply add_le_add
      · apply Finset.sum_le_sum
        intro i hi
        simp
      · by_cases hzero : s = 0
        · have hzero' :
              (∑ i, (nu.1.weight i - min (nu.1.weight i) (xi.1.weight i))) = 0 := by
            simpa [s, a] using hzero
          simp [hzero', hzero]
        · have hzero' :
              ¬(∑ i, (nu.1.weight i - min (nu.1.weight i) (xi.1.weight i))) = 0 := by
            simpa [s, a] using hzero
          simp only [hzero', if_false]
          change (∑ i, ∑ j, a i * b j / s * |nu.1.atom i - xi.1.atom j|) ≤
              2 * radius * s
          calc
            (∑ i, ∑ j, a i * b j / s * |nu.1.atom i - xi.1.atom j|) ≤
                ∑ i, ∑ j, a i * b j / s * (2 * radius) := by
              apply Finset.sum_le_sum
              intro i hi
              apply Finset.sum_le_sum
              intro j hj
              exact mul_le_mul_of_nonneg_left (hdist i j)
                (div_nonneg (mul_nonneg (ha i) (hb j))
                  (Finset.sum_nonneg fun r _ => ha r))
            _ = 2 * radius * s := by
              simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum, hs]
              field_simp
              ring
    _ = _ := rfl

/-- Computing quotient Wasserstein loss on quotient constructors recovers the labelled loss. -/
-- @node: lawModulo_wass1_ofProbabilityLaw
lemma wass1_ofProbabilityLaw {k : ℕ} {radius : ℝ}
    (nu xi : ProbabilityLaw k radius) :
    (ofProbabilityLaw nu).wass1 (ofProbabilityLaw xi) = AtomicLaw.wass1 nu.1 xi.1 := by
  have hnu : (ofProbabilityLaw nu).representative.MeasureEquivalent nu := by
    change (probabilityLawSetoid k radius).r (ofProbabilityLaw nu).representative nu
    exact (Quotient.eq_mk_iff_out (x := ofProbabilityLaw nu) (y := nu)).mp rfl
  have hxi : (ofProbabilityLaw xi).representative.MeasureEquivalent xi := by
    change (probabilityLawSetoid k radius).r (ofProbabilityLaw xi).representative xi
    exact (Quotient.eq_mk_iff_out (x := ofProbabilityLaw xi) (y := xi)).mp rfl
  exact AtomicLaw.wass1_congr hnu hxi

/-- The quotient projection is continuous from labelled coordinates to the raw Wasserstein metric
topology. -/
-- @node: lawModulo_continuous_ofProbabilityLaw_rawMetric
lemma continuous_ofProbabilityLaw_rawMetric (k : ℕ) (radius : ℝ) :
    @Continuous (ProbabilityLaw k radius) (LawModulo k radius)
      instTopologicalSpaceSubtype
      (rawMetricSpace k radius).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      ofProbabilityLaw := by
  apply (@continuous_iff_continuousAt (ProbabilityLaw k radius) (LawModulo k radius)
    instTopologicalSpaceSubtype
    (rawMetricSpace k radius).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace _).2
  intro nu
  letI : MetricSpace (LawModulo k radius) := rawMetricSpace k radius
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  let B : ProbabilityLaw k radius → ℝ := fun xi =>
    (∑ i, min (nu.1.weight i) (xi.1.weight i) *
      |nu.1.atom i - xi.1.atom i|) +
    2 * radius *
      (∑ i, (nu.1.weight i - min (nu.1.weight i) (xi.1.weight i)))
  have hB : Continuous B := by
    dsimp [B]
    have hc : Continuous (fun xi : ProbabilityLaw k radius =>
        (xi.1.weight, xi.1.atom)) :=
      (coordinateHomeomorph k radius).continuous.comp continuous_subtype_val
    have hw (i : Fin k) : Continuous
        (fun xi : ProbabilityLaw k radius => xi.1.weight i) :=
      (continuous_apply i).comp (continuous_fst.comp hc)
    have ha (i : Fin k) : Continuous
        (fun xi : ProbabilityLaw k radius => xi.1.atom i) :=
      (continuous_apply i).comp (continuous_snd.comp hc)
    apply Continuous.add
    · apply continuous_finsetSum
      intro i hi
      exact (continuous_const.min (hw i)).mul (continuous_const.sub (ha i)).abs
    · apply Continuous.mul continuous_const
      apply continuous_finsetSum
      intro i hi
      exact continuous_const.sub (continuous_const.min (hw i))
  have hBnu : B nu = 0 := by simp [B]
  have hev : ∀ᶠ xi in nhds nu, B xi < epsilon := by
    have : {x | x < epsilon} ∈ nhds (B nu) := by
      rw [hBnu]
      exact Iio_mem_nhds hepsilon
    exact hB.continuousAt this
  filter_upwards [hev] with xi hxi
  rw [rawMetricSpace_dist]
  rw [LawModulo.wass1_comm, wass1_ofProbabilityLaw]
  exact lt_of_le_of_lt (wass1_le_coordinateBound nu xi) hxi

/-- The raw Wasserstein metric topology agrees with the original coinduced quotient topology. -/
-- @node: lawModulo_rawMetricSpace_topology_eq
lemma rawMetricSpace_topology_eq (k : ℕ) (radius : ℝ) :
    instTopologicalSpace =
      (rawMetricSpace k radius).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  letI : TopologicalSpace (LawModulo k radius) :=
    (rawMetricSpace k radius).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (LawModulo k radius) := rawMetricSpace k radius
  have hsurj : Function.Surjective (@ofProbabilityLaw k radius) := by
    intro q
    exact ⟨q.out, Quotient.out_eq q⟩
  have hquot : Topology.IsQuotientMap (@ofProbabilityLaw k radius) :=
    Topology.IsQuotientMap.of_surjective_continuous hsurj
      (continuous_ofProbabilityLaw_rawMetric k radius)
  exact hquot.isCoinducing.eq_coinduced.symm

/-- The Wasserstein metric installed on quotient laws, with the original quotient topology. -/
-- @node: lawModulo_metricSpace
noncomputable instance metricSpace (k : ℕ) (radius : ℝ) :
    MetricSpace (LawModulo k radius) :=
  (rawMetricSpace k radius).replaceTopology (rawMetricSpace_topology_eq k radius)

/-- The installed metric distance is extensional Wasserstein loss. -/
-- @node: lawModulo_dist_eq_wass1
@[simp] lemma dist_eq_wass1 {k : ℕ} {radius : ℝ} (nu xi : LawModulo k radius) :
    dist nu xi = nu.wass1 xi := by
  rfl

/-- Compact quotient laws are complete for their Wasserstein metric. -/
-- @node: lawModulo_completeSpace
noncomputable instance completeSpace (k : ℕ) (radius : ℝ) :
    CompleteSpace (LawModulo k radius) := complete_of_compact

end LawModulo

/-- The (finite) set of locations carrying positive represented mass. -/
noncomputable def support {k : ℕ} {radius : ℝ} (ν : AtomicLaw k radius) : Finset ℝ :=
  (Finset.univ.filter (fun i => 0 < ν.weight i)).image ν.atom

/-- Every distinct represented atom has at least the prescribed aggregate mass.
    @realizes \(\mathcal P_{\le k,m_\star}([-L_{\tau},L_{\tau}])\)(atom-floor class)
    @realizes \(\xi\)(generic member of the atom-floor class) -/
def AtomFloor (m : ℝ) {k : ℕ} {radius : ℝ} (ν : AtomicLaw k radius) : Prop :=
  ∀ x ∈ ν.support, m ≤ ∑ i with ν.atom i = x, ν.weight i

/-- Distance from a point to a finite set. -/
noncomputable def distToFinset (x : ℝ) (C : Finset ℝ) : ℝ :=
  sInf {d : ℝ | ∃ y ∈ C, d = |x - y|}

/-- Atom-floor transport implication used by the cluster report. -/
-- @node: support_close_of_wass1_le
lemma support_close_of_wass1_le {k : ℕ} {radius m ρ : ℝ}
    {ν ξ : AtomicLaw k radius} (hνValid : Valid ν) (hξValid : Valid ξ)
    (hν : AtomFloor m ν) (hξ : AtomFloor m ξ)
    (hm : 0 < m) (hW : wass1 ν ξ ≤ m * ρ) :
    (∀ x ∈ ν.support, distToFinset x ξ.support ≤ ρ) ∧
      ∀ y ∈ ξ.support, distToFinset y ν.support ≤ ρ := by
  classical
  have planExists (a b : AtomicLaw k radius) (ha : Valid a) (hb : Valid b) :
      Nonempty (TransportPlan a b) := by
    refine ⟨{
      mass := fun i j => a.weight i * b.weight j
      nonneg := fun i j => mul_nonneg (ha.1 i) (hb.1 j)
      fst_marginal := ?_
      snd_marginal := ?_ }⟩
    · intro i
      rw [← Finset.mul_sum, hb.2.1, mul_one]
    · intro j
      rw [← Finset.sum_mul, ha.2.1, one_mul]
  have supportNonempty (a : AtomicLaw k radius) (ha : Valid a) : a.support.Nonempty := by
    have hex : ∃ i, a.weight i ≠ 0 := by
      by_contra h
      push Not at h
      have hzero : ∑ i, a.weight i = 0 := by simp [h]
      linarith [ha.2.1]
    obtain ⟨i, hi⟩ := hex
    have hipos : 0 < a.weight i := lt_of_le_of_ne (ha.1 i) (Ne.symm hi)
    exact ⟨a.atom i, Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hipos⟩, rfl⟩⟩
  have wassSymm (a b : AtomicLaw k radius) : wass1 a b = wass1 b a := by
    unfold wass1
    congr 1
    ext c
    constructor
    · rintro ⟨γ, rfl⟩
      let γ' : TransportPlan b a := {
        mass := fun i j => γ.mass j i
        nonneg := fun i j => γ.nonneg j i
        fst_marginal := γ.snd_marginal
        snd_marginal := γ.fst_marginal }
      refine ⟨γ', ?_⟩
      unfold transportCost γ'
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_sub_comm]
    · rintro ⟨γ, rfl⟩
      let γ' : TransportPlan a b := {
        mass := fun i j => γ.mass j i
        nonneg := fun i j => γ.nonneg j i
        fst_marginal := γ.snd_marginal
        snd_marginal := γ.fst_marginal }
      refine ⟨γ', ?_⟩
      unfold transportCost γ'
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_sub_comm]
  have oneSide (a b : AtomicLaw k radius) (ha : Valid a) (hb : Valid b)
      (hfloor : AtomFloor m a) (hab : wass1 a b ≤ m * ρ)
      (x : ℝ) (hx : x ∈ a.support) :
      distToFinset x b.support ≤ ρ := by
    let d := distToFinset x b.support
    have hbne : b.support.Nonempty := supportNonempty b hb
    have hdistSet : ({r : ℝ | ∃ y ∈ b.support, r = |x - y|}).Nonempty := by
      obtain ⟨y, hy⟩ := hbne
      exact ⟨|x - y|, y, hy, rfl⟩
    have hdistLower : BddBelow {r : ℝ | ∃ y ∈ b.support, r = |x - y|} := by
      refine ⟨0, ?_⟩
      rintro r ⟨y, hy, rfl⟩
      exact abs_nonneg _
    have hd_nonneg : 0 ≤ d := by
      apply le_csInf hdistSet
      rintro r ⟨y, hy, rfl⟩
      exact abs_nonneg _
    have hd_le (y : ℝ) (hy : y ∈ b.support) : d ≤ |x - y| := by
      exact csInf_le hdistLower ⟨y, hy, rfl⟩
    by_contra hclose
    have hrho : ρ < d := lt_of_not_ge hclose
    have hcost (γ : TransportPlan a b) :
        m * d ≤ transportCost γ := by
      calc
        m * d ≤ (∑ i with a.atom i = x, a.weight i) * d :=
          mul_le_mul_of_nonneg_right (hfloor x hx) hd_nonneg
        _ = ∑ i, (if a.atom i = x then a.weight i else 0) * d := by
          rw [Finset.sum_mul]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hix : a.atom i = x <;> simp [hix]
        _ ≤ ∑ i, ∑ j, γ.mass i j * |a.atom i - b.atom j| := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hix : a.atom i = x
          · rw [if_pos hix, ← γ.fst_marginal i, Finset.sum_mul]
            apply Finset.sum_le_sum
            intro j hj
            by_cases hjpos : 0 < b.weight j
            · have hjSupp : b.atom j ∈ b.support := Finset.mem_image.mpr
                ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjpos⟩, rfl⟩
              simpa [hix] using
                (mul_le_mul_of_nonneg_left (hd_le (b.atom j) hjSupp) (γ.nonneg i j))
            · have hjzero : b.weight j = 0 := le_antisymm (le_of_not_gt hjpos) (hb.1 j)
              have hij_le : γ.mass i j ≤ ∑ r, γ.mass r j := by
                exact Finset.single_le_sum (fun r _ => γ.nonneg r j) (Finset.mem_univ i)
              rw [γ.snd_marginal j, hjzero] at hij_le
              have hijzero : γ.mass i j = 0 := le_antisymm hij_le (γ.nonneg i j)
              simp [hijzero]
          · rw [if_neg hix]
            rw [zero_mul]
            exact Finset.sum_nonneg fun j _ => mul_nonneg (γ.nonneg i j) (abs_nonneg _)
        _ = transportCost γ := rfl
    have hcostSet : ({c : ℝ | ∃ γ : TransportPlan a b, transportCost γ = c}).Nonempty := by
      obtain ⟨γ⟩ := planExists a b ha hb
      exact ⟨transportCost γ, γ, rfl⟩
    have hinf : m * d ≤ wass1 a b := by
      unfold wass1
      apply le_csInf hcostSet
      rintro c ⟨γ, rfl⟩
      exact hcost γ
    have hstrict : m * ρ < m * d := mul_lt_mul_of_pos_left hrho hm
    exact (not_lt_of_ge (hinf.trans hab)) hstrict
  exact ⟨oneSide ν ξ hνValid hξValid hν hW,
    oneSide ξ ν hξValid hνValid hξ ((wassSymm ξ ν).trans_le hW)⟩

end AtomicLaw
end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
