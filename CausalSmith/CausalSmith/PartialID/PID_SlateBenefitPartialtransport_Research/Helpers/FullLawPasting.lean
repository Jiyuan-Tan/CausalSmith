import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.SharpDefinitions
import Causalean.PO.Conditioning.CondExpTooling
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Finite full-law pasting substrate

This module supplies a universe-polymorphic finite atom space and reuses the
original slate's native node value spaces for the canonical structural law.
-/

open MeasureTheory Causalean PO

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

universe uV uVal uOmega uCell

variable {𝒳 : Type uCell} [Fintype 𝒳] [DecidableEq 𝒳] [MeasurableSpace 𝒳]
  [MeasurableSingletonClass 𝒳]
variable {K : ℕ}

/-- One atom stores the covariate, instrument, and the six latent arms. -/
structure ThresholdAtom (𝒳 : Type uCell) (K : ℕ) where
  x : 𝒳
  z : Bool
  d0 : Bool
  d1 : Bool
  s0 : Bool
  s1 : Bool
  y0 : Fin K
  y1 : Fin K
  deriving DecidableEq

/-- Threshold atoms have decidable equality. -/
add_decl_doc instDecidableEqThresholdAtom

private abbrev ThresholdAtomTuple (𝒳 : Type uCell) (K : ℕ) :=
  𝒳 × Bool × Bool × Bool × Bool × Bool × Fin K × Fin K

private def thresholdAtomEquiv : ThresholdAtom 𝒳 K ≃ ThresholdAtomTuple 𝒳 K where
  toFun a := (a.x, a.z, a.d0, a.d1, a.s0, a.s1, a.y0, a.y1)
  invFun a := ⟨a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1,
    a.2.2.2.2.2.1, a.2.2.2.2.2.2.1, a.2.2.2.2.2.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨x, z, d0, d1, s0, s1, y0, y1⟩; rfl

@[simp] private theorem thresholdAtomEquiv_symm_apply
    (x : 𝒳) (z d0 d1 s0 s1 : Bool) (y0 y1 : Fin K) :
    thresholdAtomEquiv.symm (x, z, d0, d1, s0, s1, y0, y1) =
      (⟨x, z, d0, d1, s0, s1, y0, y1⟩ : ThresholdAtom 𝒳 K) := rfl

/-- This declaration supplies the canonical canonical fintype threshold atom typeclass instance for the finite slate-benefit construction. -/
instance : Fintype (ThresholdAtom 𝒳 K) :=
  Fintype.ofEquiv (ThresholdAtomTuple 𝒳 K) thresholdAtomEquiv.symm

/-- The threshold index is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
abbrev ThresholdIndex (𝒳 : Type uCell) [Fintype 𝒳] (K : ℕ) :=
  Fin (Fintype.card (ThresholdAtom 𝒳 K))

/-- A threshold omega records the data and compatibility conditions used by the slate-benefit partial-transport construction. -/
structure ThresholdOmega.{w, u} (𝒳 : Type u) [Fintype 𝒳]
    (K : ℕ) : Type w where
  down : ThresholdIndex 𝒳 K

/-- This declaration supplies the canonical canonical measurable space threshold omega typeclass instance for the finite slate-benefit construction. -/
instance : MeasurableSpace (ThresholdOmega.{uOmega} 𝒳 K) := ⊤

/-- This declaration supplies the canonical canonical discrete measurable space threshold omega typeclass instance for the finite slate-benefit construction. -/
instance : DiscreteMeasurableSpace (ThresholdOmega.{uOmega} 𝒳 K) :=
  ⟨fun _ => MeasurableSet.of_discrete⟩

/-- This declaration supplies the canonical canonical fintype threshold omega typeclass instance for the finite slate-benefit construction. -/
instance : Fintype (ThresholdOmega.{uOmega} 𝒳 K) :=
  Fintype.ofEquiv (ThresholdIndex 𝒳 K)
    { toFun := ThresholdOmega.mk
      invFun := ThresholdOmega.down
      left_inv := fun _ => rfl
      right_inv := fun a => by cases a; rfl }

/-- The threshold atom at is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def thresholdAtomAt (ω : ThresholdOmega.{uOmega} 𝒳 K) :
    ThresholdAtom 𝒳 K :=
  (Fintype.equivFin (ThresholdAtom 𝒳 K)).symm ω.down

private def atomDArm (z : Bool) (a : ThresholdAtom 𝒳 K) : Bool :=
  if z then a.d1 else a.d0

private def atomSArm (d : Bool) (a : ThresholdAtom 𝒳 K) : Bool :=
  if d then a.s1 else a.s0

private def atomYArm (d : Bool) (a : ThresholdAtom 𝒳 K) : Fin K :=
  if d then a.y1 else a.y0

private def effectiveZ {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (r : Regime P.V P.X) (a : ThresholdAtom 𝒳 K) : Bool :=
  if h : S.zNode ∈ r.target then S.hZ (r.assign S.zNode h) else a.z

private def effectiveD {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (r : Regime P.V P.X) (a : ThresholdAtom 𝒳 K) : Bool :=
  if h : S.dNode ∈ r.target then S.hD (r.assign S.dNode h)
  else atomDArm (effectiveZ S r a) a

/-- Structural evaluator on finite atom indices.  The original node carrier and
native value family are retained, avoiding any universe-lowering assumption. -/
noncomputable def thresholdEval {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (r : Regime P.V P.X)
    (ω : ThresholdOmega.{uOmega} 𝒳 K) : ∀ v, P.X v := by
  classical
  intro v
  let a := thresholdAtomAt ω
  if hv : v ∈ r.target then
    exact r.assign v hv
  else if hx : v = S.xNode then
    exact hx ▸ S.hX.symm a.x
  else if hz : v = S.zNode then
    exact hz ▸ S.hZ.symm a.z
  else if hd : v = S.dNode then
    exact hd ▸ S.hD.symm (atomDArm (effectiveZ S r a) a)
  else if hs : v = S.sNode then
    exact hs ▸ S.hS.symm (atomSArm (effectiveD S r a) a)
  else if hy : v = S.yNode then
    exact hy ▸ S.hY.symm (atomYArm (effectiveD S r a) a)
  else
    exact P.eval Regime.empty
      (Classical.choice (nonempty_of_isProbabilityMeasure P.μ)) v

/-- [the threshold eval map is measurable](goal). -/
@[fun_prop]
theorem measurable_thresholdEval {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (r : Regime P.V P.X) :
    Measurable (thresholdEval S r : ThresholdOmega.{uOmega} 𝒳 K → ∀ v, P.X v) := by
  exact measurable_from_top

/-- [the threshold eval x empty property holds](goal). -/
@[simp] theorem thresholdEval_x_empty {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (ω : ThresholdOmega.{uOmega} 𝒳 K) :
    S.hX (thresholdEval S Regime.empty ω S.xNode) = (thresholdAtomAt ω).x := by
  simp [thresholdEval, Regime.empty]

/-- [the threshold eval z empty property holds](goal). -/
@[simp] theorem thresholdEval_z_empty {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (ω : ThresholdOmega.{uOmega} 𝒳 K) :
    S.hZ (thresholdEval S Regime.empty ω S.zNode) = (thresholdAtomAt ω).z := by
  simp only [thresholdEval, Regime.empty, Set.mem_empty_iff_false, ↓reduceDIte]
  rw [dif_neg S.hXZ.symm]
  simp

/-- [the threshold eval d empty property holds](goal). -/
@[simp] theorem thresholdEval_d_empty {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (ω : ThresholdOmega.{uOmega} 𝒳 K) :
    S.hD (thresholdEval S Regime.empty ω S.dNode) =
      atomDArm (thresholdAtomAt ω).z (thresholdAtomAt ω) := by
  simp only [thresholdEval, Regime.empty, Set.mem_empty_iff_false, ↓reduceDIte]
  rw [dif_neg S.hXD.symm, dif_neg S.hZD.symm]
  simp [effectiveZ]

/-- [the threshold eval s empty property holds](goal). -/
@[simp] theorem thresholdEval_s_empty {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (ω : ThresholdOmega.{uOmega} 𝒳 K) :
    S.hS (thresholdEval S Regime.empty ω S.sNode) =
      atomSArm (atomDArm (thresholdAtomAt ω).z (thresholdAtomAt ω))
        (thresholdAtomAt ω) := by
  simp only [thresholdEval, Regime.empty, Set.mem_empty_iff_false, ↓reduceDIte]
  rw [dif_neg S.hXS.symm, dif_neg S.hZS.symm, dif_neg S.hDS.symm]
  simp [effectiveD, effectiveZ]

/-- [the threshold eval y empty property holds](goal). -/
@[simp] theorem thresholdEval_y_empty {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (ω : ThresholdOmega.{uOmega} 𝒳 K) :
    S.hY (thresholdEval S Regime.empty ω S.yNode) =
      atomYArm (atomDArm (thresholdAtomAt ω).z (thresholdAtomAt ω))
        (thresholdAtomAt ω) := by
  simp only [thresholdEval, Regime.empty, Set.mem_empty_iff_false, ↓reduceDIte]
  rw [dif_neg S.hXY.symm, dif_neg S.hZY.symm, dif_neg S.hDY.symm, dif_neg S.hSY.symm]
  simp [effectiveD, effectiveZ]

/-- The atomic measure associated with real weights on the high-universe atom
description, represented on a small finite index type. -/
noncomputable def thresholdAtomicMeasure
    (weight : ThresholdAtom 𝒳 K → ℝ) : Measure (ThresholdOmega.{uOmega} 𝒳 K) :=
  ∑ i : ThresholdIndex 𝒳 K,
    ENNReal.ofReal (weight ((Fintype.equivFin (ThresholdAtom 𝒳 K)).symm i)) •
      Measure.dirac (ThresholdOmega.mk i)

/-- Given [the stated hypotheses](hyp:hweight,hsum), [the threshold atomic measure univ property holds](goal). -/
theorem thresholdAtomicMeasure_univ
    (weight : ThresholdAtom 𝒳 K → ℝ) (hweight : ∀ a, 0 ≤ weight a)
    (hsum : ∑ a, weight a = 1) :
    (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)) Set.univ = 1 := by
  unfold thresholdAtomicMeasure
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hweight _)]
  have hindex :
      (∑ i : ThresholdIndex 𝒳 K,
          weight ((Fintype.equivFin (ThresholdAtom 𝒳 K)).symm i)) =
        ∑ a : ThresholdAtom 𝒳 K, weight a := by
    symm
    exact Fintype.sum_equiv (Fintype.equivFin (ThresholdAtom 𝒳 K)) weight
      (fun i => weight ((Fintype.equivFin (ThresholdAtom 𝒳 K)).symm i))
      (fun a => by simp)
  rw [hindex, hsum]
  simp

/-- The canonical atomic measure assigns each decoded atom its specified real weight. Given [the stated hypotheses](hyp:hweight), [the stated conclusion follows](goal). -/
theorem thresholdAtomicMeasure_atom
    (weight : ThresholdAtom 𝒳 K → ℝ) (hweight : ∀ a, 0 ≤ weight a)
    (a : ThresholdAtom 𝒳 K) :
    (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
        {ω | thresholdAtomAt ω = a} = weight a := by
  unfold thresholdAtomicMeasure Measure.real
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single ((Fintype.equivFin (ThresholdAtom 𝒳 K)) a)]
  · simp [Measure.dirac_apply', thresholdAtomAt, hweight]
  · intro i _ hi
    have hdecode : (Fintype.equivFin (ThresholdAtom 𝒳 K)).symm i ≠ a := by
      intro h
      apply hi
      simpa using congrArg (Fintype.equivFin (ThresholdAtom 𝒳 K)) h
    simp [Measure.dirac_apply', thresholdAtomAt, hdecode]
  · simp

/-- Every finite event on decoded atoms has mass equal to the sum of its atom weights. Given [the stated hypotheses](hyp:hweight,hsum), [the stated conclusion follows](goal). -/
theorem thresholdAtomicMeasure_event
    (weight : ThresholdAtom 𝒳 K → ℝ) (hweight : ∀ a, 0 ≤ weight a)
    (hsum : ∑ a, weight a = 1)
    (q : ThresholdAtom 𝒳 K → Prop) [DecidablePred q] :
    (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
        {ω | q (thresholdAtomAt ω)} = ∑ a, if q a then weight a else 0 := by
  letI : IsProbabilityMeasure
      (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)) :=
    ⟨thresholdAtomicMeasure_univ weight hweight hsum⟩
  let I := {a : ThresholdAtom 𝒳 K // q a}
  let E : I → Set (ThresholdOmega.{uOmega} 𝒳 K) := fun a =>
    {ω | thresholdAtomAt ω = a.1}
  have hdisj : Pairwise (fun a b => Disjoint (E a) (E b)) := by
    intro a b hab
    apply Set.disjoint_left.2
    intro ω ha hb
    apply hab
    exact Subtype.ext (ha.symm.trans hb)
  have hmeas : ∀ a, MeasurableSet (E a) := fun _ => MeasurableSet.of_discrete
  rw [show {ω | q (thresholdAtomAt ω)} = ⋃ a : I, E a by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E]
    constructor
    · intro hq
      exact ⟨⟨thresholdAtomAt ω, hq⟩, rfl⟩
    · rintro ⟨a, ha⟩
      simpa [ha] using a.2]
  rw [measureReal_iUnion_fintype hdisj hmeas]
  change (∑ a : I, (thresholdAtomicMeasure weight :
    Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
      {ω | thresholdAtomAt ω = a.1}) = _
  simp_rw [thresholdAtomicMeasure_atom weight hweight]
  classical
  rw [← Finset.sum_filter]
  symm
  exact Finset.sum_subtype (Finset.univ.filter q) (by simp) weight

/-- A normalized nonnegative atom table gives a PO system in exactly the
universe parameters of the supplied system. -/
noncomputable def canonicalThresholdPOSystem {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (weight : ThresholdAtom 𝒳 K → ℝ)
    (hweight : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1) :
    POSystem.{uV, uVal, uOmega} := by
  letI : IsProbabilityMeasure
      (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)) :=
    ⟨thresholdAtomicMeasure_univ weight hweight hsum⟩
  exact
    { V := P.V
      X := P.X
      Ω := ThresholdOmega.{uOmega} 𝒳 K
      μ := thresholdAtomicMeasure weight
      eval := thresholdEval S
      measurable_eval := measurable_thresholdEval S }

/-- The canonical slate reuses all five original nodes and measurable
equivalences on the finite atomic PO system. -/
noncomputable def canonicalThresholdSlate {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (weight : ThresholdAtom 𝒳 K → ℝ)
    (hweight : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1) :
    POSlateSystem (canonicalThresholdPOSystem S weight hweight hsum) 𝒳 K where
  hK := S.hK
  xNode := S.xNode
  zNode := S.zNode
  dNode := S.dNode
  sNode := S.sNode
  yNode := S.yNode
  hX := S.hX
  hZ := S.hZ
  hD := S.hD
  hS := S.hS
  hY := S.hY
  hXZ := S.hXZ
  hXD := S.hXD
  hXS := S.hXS
  hXY := S.hXY
  hZD := S.hZD
  hZS := S.hZS
  hZY := S.hZY
  hDS := S.hDS
  hDY := S.hDY
  hSY := S.hSY
  borel := by
    change StandardBorelSpace (ThresholdOmega.{uOmega} 𝒳 K)
    infer_instance

/-- Given [the stated hypotheses](hyp:hweight,hsum), [the canonical threshold slate factual x property holds](goal). -/
@[simp] theorem canonicalThresholdSlate_factualX {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (weight : ThresholdAtom 𝒳 K → ℝ)
    (hweight : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1)
    (ω : ThresholdOmega.{uOmega} 𝒳 K) :
    (canonicalThresholdSlate S weight hweight hsum).factualX ω =
      (thresholdAtomAt ω).x := by
  change S.hX (thresholdEval S Regime.empty ω S.xNode) = _
  exact thresholdEval_x_empty S ω

/-- Given [the stated hypotheses](hyp:hweight,hsum), [the canonical threshold slate factual z property holds](goal). -/
@[simp] theorem canonicalThresholdSlate_factualZ {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (weight : ThresholdAtom 𝒳 K → ℝ)
    (hweight : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1)
    (ω : ThresholdOmega.{uOmega} 𝒳 K) :
    (canonicalThresholdSlate S weight hweight hsum).factualZ ω =
      (thresholdAtomAt ω).z := by
  change S.hZ (thresholdEval S Regime.empty ω S.zNode) = _
  exact thresholdEval_z_empty S ω

/-- Given [the stated hypotheses](hyp:hweight,hsum), [the canonical threshold slate dof z property holds](goal). -/
@[simp] theorem canonicalThresholdSlate_DofZ {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (weight : ThresholdAtom 𝒳 K → ℝ)
    (hweight : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1)
    (z : Bool) (ω : ThresholdOmega.{uOmega} 𝒳 K) :
    (canonicalThresholdSlate S weight hweight hsum).DofZ z ω =
      if z then (thresholdAtomAt ω).d1 else (thresholdAtomAt ω).d0 := by
  change S.hD (thresholdEval S (Regime.single S.zNode (S.hZ.symm z)) ω S.dNode) = _
  have hdZ : S.dNode ≠ S.zNode := S.hZD.symm
  have hdX : S.dNode ≠ S.xNode := S.hXD.symm
  simp [thresholdEval, Regime.single, effectiveZ, atomDArm, hdZ, hdX]

/-- Given [the stated hypotheses](hyp:hweight,hsum), [the canonical threshold slate sof d property holds](goal). -/
@[simp] theorem canonicalThresholdSlate_SofD {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (weight : ThresholdAtom 𝒳 K → ℝ)
    (hweight : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1)
    (d : Bool) (ω : ThresholdOmega.{uOmega} 𝒳 K) :
    (canonicalThresholdSlate S weight hweight hsum).SofD d ω =
      if d then (thresholdAtomAt ω).s1 else (thresholdAtomAt ω).s0 := by
  change S.hS (thresholdEval S (Regime.single S.dNode (S.hD.symm d)) ω S.sNode) = _
  have hsD : S.sNode ≠ S.dNode := S.hDS.symm
  have hsX : S.sNode ≠ S.xNode := S.hXS.symm
  have hsZ : S.sNode ≠ S.zNode := S.hZS.symm
  simp [thresholdEval, Regime.single, effectiveD, atomSArm, hsD, hsX, hsZ]

/-- Given [the stated hypotheses](hyp:hweight,hsum), [the canonical threshold slate yof d property holds](goal). -/
@[simp] theorem canonicalThresholdSlate_YofD {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (weight : ThresholdAtom 𝒳 K → ℝ)
    (hweight : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1)
    (d : Bool) (ω : ThresholdOmega.{uOmega} 𝒳 K) :
    (canonicalThresholdSlate S weight hweight hsum).YofD d ω =
      if d then (thresholdAtomAt ω).y1 else (thresholdAtomAt ω).y0 := by
  change S.hY (thresholdEval S (Regime.single S.dNode (S.hD.symm d)) ω S.yNode) = _
  have hyD : S.yNode ≠ S.dNode := S.hDY.symm
  have hyX : S.yNode ≠ S.xNode := S.hXY.symm
  have hyZ : S.yNode ≠ S.zNode := S.hZY.symm
  have hyS : S.yNode ≠ S.sNode := S.hSY.symm
  simp [thresholdEval, Regime.single, effectiveD, atomYArm, hyD, hyX, hyZ, hyS]

/-- A conditional latent table in each covariate cell. -/
abbrev ThresholdCellTable (𝒳 : Type uCell) (K : ℕ) :=
  𝒳 → Bool → Bool → Bool → Bool → Fin K → Fin K → ℝ

def ThresholdCellTable.Nonnegative (T : ThresholdCellTable 𝒳 K) : Prop :=
  ∀ x d0 d1 s0 s1 y0 y1, 0 ≤ T x d0 d1 s0 s1 y0 y1

def ThresholdCellTable.Normalized (T : ThresholdCellTable 𝒳 K) : Prop :=
  ∀ x, ∑ d0, ∑ d1, ∑ s0, ∑ s1, ∑ y0, ∑ y1,
    T x d0 d1 s0 s1 y0 y1 = 1

/-- The atom instrument mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def atomInstrumentMass {P : POSystem}
    (S : POSlateSystem P 𝒳 K) (x : 𝒳) (z : Bool) : ℝ :=
  if z then S.propensity x else 1 - S.propensity x

/-- Joint atom weights obtained from the observed covariate mass, conditional
instrument propensity, and a normalized conditional latent table. -/
noncomputable def thresholdPastedWeight {P : POSystem}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (a : ThresholdAtom 𝒳 K) : ℝ :=
  S.p a.x * atomInstrumentMass S a.x a.z *
    T a.x a.d0 a.d1 a.s0 a.s1 a.y0 a.y1

/-- Given [the stated hypotheses](hyp:hp,hprop,hT), [threshold pasted weight is nonnegative](goal). -/
theorem thresholdPastedWeight_nonnegative {P : POSystem}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hT : T.Nonnegative) :
    ∀ a, 0 ≤ thresholdPastedWeight S T a := by
  intro a
  apply mul_nonneg
  · apply mul_nonneg (hp a.x)
    unfold atomInstrumentMass
    cases a.z
    · simpa using sub_nonneg.mpr (hprop a.x).2
    · exact (hprop a.x).1
  · exact hT _ _ _ _ _ _ _

private theorem sum_cellProbability {P : POSystem} (S : POSlateSystem P 𝒳 K) :
    ∑ x, S.p x = 1 := by
  unfold POSlateSystem.p
  have hdisj : Pairwise (fun x y => Disjoint (S.xEvent x) (S.xEvent y)) := by
    intro x y hxy
    apply Set.disjoint_left.2
    intro ω hx hy
    exact hxy (hx.symm.trans hy)
  have hmeas : ∀ x, MeasurableSet (S.xEvent x) := fun x =>
    S.xVar.measurable_factual (measurableSet_singleton x)
  calc
    (∑ x, P.μ.real (S.xEvent x)) = P.μ.real (⋃ x, S.xEvent x) :=
      (measureReal_iUnion_fintype hdisj hmeas).symm
    _ = P.μ.real Set.univ := by
      congr 1
      ext ω
      simp [POSlateSystem.xEvent]
    _ = 1 := by simp [Measure.real]

/-- Given [the stated hypotheses](hyp:hT), [the threshold pasted weight sum one property holds](goal). -/
theorem thresholdPastedWeight_sum_one {P : POSystem}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hT : T.Normalized) :
    ∑ a, thresholdPastedWeight S T a = 1 := by
  unfold ThresholdCellTable.Normalized at hT
  let tupleWeight : ThresholdAtomTuple 𝒳 K → ℝ := fun a =>
    S.p a.1 * atomInstrumentMass S a.1 a.2.1 *
      T a.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1
        a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2
  calc
    (∑ a, thresholdPastedWeight S T a) =
        ∑ a : ThresholdAtomTuple 𝒳 K, tupleWeight a :=
      Fintype.sum_equiv thresholdAtomEquiv _ _ (fun a => rfl)
    _ = 1 := by
      dsimp [tupleWeight]
      simp only [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      simp_rw [hT]
      simp only [mul_one]
      simp only [atomInstrumentMass, Fintype.sum_bool, Bool.false_eq_true,
        ↓reduceIte, Bool.true_eq_false]
      rw [show (∑ x, (S.p x * S.propensity x + S.p x * (1 - S.propensity x))) =
          ∑ x, S.p x by
        apply Finset.sum_congr rfl
        intro x _
        ring]
      exact sum_cellProbability S

/-- Canonical full-law candidate generated by a normalized nonnegative cell table. -/
noncomputable def canonicalThresholdCandidate {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized) :
    FullLawCandidate P 𝒳 K :=
  let weight := thresholdPastedWeight S T
  let hweight := thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative
  let hsum := thresholdPastedWeight_sum_one S T hTnormalized
  { system := canonicalThresholdPOSystem S weight hweight hsum
    slate := canonicalThresholdSlate S weight hweight hsum }

/-- Given [the stated hypotheses](hyp:hp,hprop,hTnonnegative,hTnormalized), [the canonical threshold candidate full atom property holds](goal). -/
theorem canonicalThresholdCandidate_fullAtom {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized)
    (a : ThresholdAtom 𝒳 K) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    W.system.μ.real {ω | W.slate.factualX ω = a.x ∧
      W.slate.factualZ ω = a.z ∧ W.slate.D0 ω = a.d0 ∧
      W.slate.D1 ω = a.d1 ∧ W.slate.S0 ω = a.s0 ∧
      W.slate.S1 ω = a.s1 ∧ W.slate.Y0 ω = a.y0 ∧
      W.slate.Y1 ω = a.y1} = thresholdPastedWeight S T a := by
  dsimp only
  let weight := thresholdPastedWeight S T
  let hweight := thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative
  let hsum := thresholdPastedWeight_sum_one S T hTnormalized
  change (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
    {ω | (canonicalThresholdSlate S weight hweight hsum).factualX ω = a.x ∧
      (canonicalThresholdSlate S weight hweight hsum).factualZ ω = a.z ∧
      (canonicalThresholdSlate S weight hweight hsum).D0 ω = a.d0 ∧
      (canonicalThresholdSlate S weight hweight hsum).D1 ω = a.d1 ∧
      (canonicalThresholdSlate S weight hweight hsum).S0 ω = a.s0 ∧
      (canonicalThresholdSlate S weight hweight hsum).S1 ω = a.s1 ∧
      (canonicalThresholdSlate S weight hweight hsum).Y0 ω = a.y0 ∧
      (canonicalThresholdSlate S weight hweight hsum).Y1 ω = a.y1} = weight a
  rw [show ({ω | (canonicalThresholdSlate S weight hweight hsum).factualX ω = a.x ∧
      (canonicalThresholdSlate S weight hweight hsum).factualZ ω = a.z ∧
      (canonicalThresholdSlate S weight hweight hsum).D0 ω = a.d0 ∧
      (canonicalThresholdSlate S weight hweight hsum).D1 ω = a.d1 ∧
      (canonicalThresholdSlate S weight hweight hsum).S0 ω = a.s0 ∧
      (canonicalThresholdSlate S weight hweight hsum).S1 ω = a.s1 ∧
      (canonicalThresholdSlate S weight hweight hsum).Y0 ω = a.y0 ∧
      (canonicalThresholdSlate S weight hweight hsum).Y1 ω = a.y1} :
      Set (ThresholdOmega.{uOmega} 𝒳 K)) = {ω | thresholdAtomAt ω = a} by
    ext ω
    simp only [Set.mem_setOf_eq, canonicalThresholdSlate_factualX,
      canonicalThresholdSlate_factualZ, POSlateSystem.D0, POSlateSystem.D1,
      POSlateSystem.S0, POSlateSystem.S1, POSlateSystem.Y0, POSlateSystem.Y1,
      canonicalThresholdSlate_DofZ, canonicalThresholdSlate_SofD,
      canonicalThresholdSlate_YofD]
    rcases thresholdAtomAt ω with ⟨x, z, d0, d1, s0, s1, y0, y1⟩
    rcases a with ⟨x', z', d0', d1', s0', s1', y0', y1'⟩
    cases z <;> simp [ThresholdAtom.mk.injEq]
  ]
  exact thresholdAtomicMeasure_atom weight hweight a

/-- Given [the stated hypotheses](hyp:hp,hprop,hTnonnegative,hTnormalized), [the canonical threshold candidate latent tuple property holds](goal). -/
theorem canonicalThresholdCandidate_latentTuple {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized)
    (x : 𝒳) (d0 d1 s0 s1 : Bool) (y0 y1 : Fin K) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    W.system.μ.real {ω | W.slate.factualX ω = x ∧
      W.slate.D0 ω = d0 ∧ W.slate.D1 ω = d1 ∧
      W.slate.S0 ω = s0 ∧ W.slate.S1 ω = s1 ∧
      W.slate.Y0 ω = y0 ∧ W.slate.Y1 ω = y1} =
      S.p x * T x d0 d1 s0 s1 y0 y1 := by
  dsimp only
  let weight := thresholdPastedWeight S T
  let hweight := thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative
  let hsum := thresholdPastedWeight_sum_one S T hTnormalized
  letI : IsProbabilityMeasure
      (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)) :=
    ⟨thresholdAtomicMeasure_univ weight hweight hsum⟩
  let CS := canonicalThresholdSlate S weight hweight hsum
  change (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
    {ω | CS.factualX ω = x ∧ CS.D0 ω = d0 ∧ CS.D1 ω = d1 ∧
      CS.S0 ω = s0 ∧ CS.S1 ω = s1 ∧ CS.Y0 ω = y0 ∧ CS.Y1 ω = y1} =
    S.p x * T x d0 d1 s0 s1 y0 y1
  let E : Bool → Set (ThresholdOmega.{uOmega} 𝒳 K) := fun z =>
    {ω | CS.factualX ω = x ∧ CS.factualZ ω = z ∧ CS.D0 ω = d0 ∧ CS.D1 ω = d1 ∧
      CS.S0 ω = s0 ∧ CS.S1 ω = s1 ∧ CS.Y0 ω = y0 ∧ CS.Y1 ω = y1}
  have hdisj : Pairwise (fun z z' => Disjoint (E z) (E z')) := by
    intro z z' hne
    apply Set.disjoint_left.2
    intro ω hz hz'
    exact hne (hz.2.1.symm.trans hz'.2.1)
  have hmeas : ∀ z, MeasurableSet (E z) := fun _ => MeasurableSet.of_discrete
  dsimp only [CS] at E ⊢
  rw [show ({ω | (canonicalThresholdSlate S weight hweight hsum).factualX ω = x ∧
      (canonicalThresholdSlate S weight hweight hsum).D0 ω = d0 ∧
      (canonicalThresholdSlate S weight hweight hsum).D1 ω = d1 ∧
      (canonicalThresholdSlate S weight hweight hsum).S0 ω = s0 ∧
      (canonicalThresholdSlate S weight hweight hsum).S1 ω = s1 ∧
      (canonicalThresholdSlate S weight hweight hsum).Y0 ω = y0 ∧
      (canonicalThresholdSlate S weight hweight hsum).Y1 ω = y1} :
      Set (ThresholdOmega.{uOmega} 𝒳 K)) = ⋃ z, E z by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E]
    constructor
    · intro h
      exact ⟨(canonicalThresholdSlate S weight hweight hsum).factualZ ω,
        h.1, rfl, h.2⟩
    · rintro ⟨z, hx, -, hrest⟩
      exact ⟨hx, hrest⟩]
  rw [measureReal_iUnion_fintype hdisj hmeas]
  change (∑ z : Bool, (thresholdAtomicMeasure weight :
    Measure (ThresholdOmega.{uOmega} 𝒳 K)).real (E z)) = _
  simp_rw [show ∀ z : Bool, (thresholdAtomicMeasure weight :
      Measure (ThresholdOmega.{uOmega} 𝒳 K)).real (E z) =
      thresholdPastedWeight S T ⟨x, z, d0, d1, s0, s1, y0, y1⟩ by
    intro z
    rw [show E z = {ω | thresholdAtomAt ω =
        (⟨x, z, d0, d1, s0, s1, y0, y1⟩ : ThresholdAtom 𝒳 K)} by
      ext ω
      simp only [E, CS, Set.mem_setOf_eq, canonicalThresholdSlate_factualX,
        canonicalThresholdSlate_factualZ, POSlateSystem.D0, POSlateSystem.D1,
        POSlateSystem.S0, POSlateSystem.S1, POSlateSystem.Y0, POSlateSystem.Y1,
        canonicalThresholdSlate_DofZ, canonicalThresholdSlate_SofD,
        canonicalThresholdSlate_YofD]
      rcases thresholdAtomAt ω with ⟨x', z', d0', d1', s0', s1', y0', y1'⟩
      cases z' <;> cases z <;> simp [ThresholdAtom.mk.injEq]]
    exact thresholdAtomicMeasure_atom weight hweight _]
  simp [thresholdPastedWeight, atomInstrumentMass, Fintype.sum_bool]
  ring

/-- Given [the stated hypotheses](hyp:hp,hprop,hTnonnegative,hTnormalized), [the canonical threshold candidate cell mass property holds](goal). -/
theorem canonicalThresholdCandidate_cellMass {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized) (x : 𝒳) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    W.system.μ.real (W.slate.xEvent x) = S.p x := by
  dsimp only
  let weight := thresholdPastedWeight S T
  let hweight := thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative
  let hsum := thresholdPastedWeight_sum_one S T hTnormalized
  change (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
    {ω | (canonicalThresholdSlate S weight hweight hsum).factualX ω = x} = S.p x
  rw [show ({ω | (canonicalThresholdSlate S weight hweight hsum).factualX ω = x} :
      Set (ThresholdOmega.{uOmega} 𝒳 K)) = {ω | (thresholdAtomAt ω).x = x} by
    ext ω
    simp]
  rw [thresholdAtomicMeasure_event weight hweight hsum (fun a => a.x = x)]
  let tupleWeight : ThresholdAtomTuple 𝒳 K → ℝ := fun a =>
    if a.1 = x then S.p a.1 * atomInstrumentMass S a.1 a.2.1 *
      T a.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1
        a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2 else 0
  rw [show (∑ a : ThresholdAtom 𝒳 K, if a.x = x then weight a else 0) =
      ∑ a : ThresholdAtomTuple 𝒳 K, tupleWeight a by
    exact Fintype.sum_equiv thresholdAtomEquiv _ _ (fun a => rfl)]
  dsimp [tupleWeight]
  conv_lhs => simp only [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single x]
  · simp only [if_true]
    simp_rw [← Finset.mul_sum]
    rw [hTnormalized]
    simp [atomInstrumentMass, Fintype.sum_bool]
    ring
  · intro x' hne
    simp [hne]

/-- Under the pasted law, any event that separately constrains the instrument and the six latent arms factors inside a fixed covariate cell. Given [the stated hypotheses](hyp:hp,hprop,hTnonnegative,hTnormalized), [the stated conclusion follows](goal). -/
theorem canonicalThresholdCandidate_separatedEventMass
    {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized)
    (x : 𝒳) (qz : Bool → Prop) [DecidablePred qz]
    (qL : Bool → Bool → Bool → Bool → Fin K → Fin K → Prop)
    [∀ d0 d1 s0 s1 y0 y1, Decidable (qL d0 d1 s0 s1 y0 y1)] :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    W.system.μ.real { ω | W.slate.factualX ω = x ∧ qz (W.slate.factualZ ω) ∧
        qL (W.slate.D0 ω) (W.slate.D1 ω) (W.slate.S0 ω) (W.slate.S1 ω)
          (W.slate.Y0 ω) (W.slate.Y1 ω) } =
      S.p x * (∑ z, if qz z then atomInstrumentMass S x z else 0) *
        (∑ d0, ∑ d1, ∑ s0, ∑ s1, ∑ y0, ∑ y1,
          if qL d0 d1 s0 s1 y0 y1 then T x d0 d1 s0 s1 y0 y1 else 0) := by
  dsimp only
  let weight := thresholdPastedWeight S T
  let hweight := thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative
  let hsum := thresholdPastedWeight_sum_one S T hTnormalized
  change (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
    { ω | (canonicalThresholdSlate S weight hweight hsum).factualX ω = x ∧
      qz ((canonicalThresholdSlate S weight hweight hsum).factualZ ω) ∧
      qL ((canonicalThresholdSlate S weight hweight hsum).D0 ω)
        ((canonicalThresholdSlate S weight hweight hsum).D1 ω)
        ((canonicalThresholdSlate S weight hweight hsum).S0 ω)
        ((canonicalThresholdSlate S weight hweight hsum).S1 ω)
        ((canonicalThresholdSlate S weight hweight hsum).Y0 ω)
        ((canonicalThresholdSlate S weight hweight hsum).Y1 ω) } = _
  rw [show ({ ω | (canonicalThresholdSlate S weight hweight hsum).factualX ω = x ∧
      qz ((canonicalThresholdSlate S weight hweight hsum).factualZ ω) ∧
      qL ((canonicalThresholdSlate S weight hweight hsum).D0 ω)
        ((canonicalThresholdSlate S weight hweight hsum).D1 ω)
        ((canonicalThresholdSlate S weight hweight hsum).S0 ω)
        ((canonicalThresholdSlate S weight hweight hsum).S1 ω)
        ((canonicalThresholdSlate S weight hweight hsum).Y0 ω)
        ((canonicalThresholdSlate S weight hweight hsum).Y1 ω) } :
      Set (ThresholdOmega.{uOmega} 𝒳 K)) =
      { ω | (thresholdAtomAt ω).x = x ∧ qz (thresholdAtomAt ω).z ∧
        qL (thresholdAtomAt ω).d0 (thresholdAtomAt ω).d1
          (thresholdAtomAt ω).s0 (thresholdAtomAt ω).s1
          (thresholdAtomAt ω).y0 (thresholdAtomAt ω).y1 } by
    ext ω
    simp only [Set.mem_setOf_eq, canonicalThresholdSlate_factualX,
      canonicalThresholdSlate_factualZ, POSlateSystem.D0, POSlateSystem.D1,
      POSlateSystem.S0, POSlateSystem.S1, POSlateSystem.Y0, POSlateSystem.Y1,
      canonicalThresholdSlate_DofZ, canonicalThresholdSlate_SofD,
      canonicalThresholdSlate_YofD]
    rcases thresholdAtomAt ω with ⟨x', z, d0, d1, s0, s1, y0, y1⟩
    cases z <;> simp]
  change (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
      { ω | (fun a : ThresholdAtom 𝒳 K =>
        a.x = x ∧ qz a.z ∧ qL a.d0 a.d1 a.s0 a.s1 a.y0 a.y1)
          (thresholdAtomAt ω) } = _
  rw [thresholdAtomicMeasure_event weight hweight hsum
    (fun a : ThresholdAtom 𝒳 K =>
      a.x = x ∧ qz a.z ∧ qL a.d0 a.d1 a.s0 a.s1 a.y0 a.y1)]
  rw [show (∑ a : ThresholdAtom 𝒳 K,
      if a.x = x ∧ qz a.z ∧ qL a.d0 a.d1 a.s0 a.s1 a.y0 a.y1
      then weight a else 0) =
      ∑ a : ThresholdAtomTuple 𝒳 K,
        if a.1 = x ∧ qz a.2.1 ∧
          qL a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1
            a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2
        then weight (thresholdAtomEquiv.symm a) else 0 by
    exact Fintype.sum_equiv thresholdAtomEquiv _ _ (fun _ => rfl)]
  dsimp [weight, thresholdPastedWeight]
  simp only [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single x]
  · simp only [thresholdAtomEquiv_symm_apply, true_and]
    simp_rw [show ∀ z d0 d1 s0 s1 y0 y1,
        (if qz z ∧ qL d0 d1 s0 s1 y0 y1 then
          S.p x * atomInstrumentMass S x z * T x d0 d1 s0 s1 y0 y1 else 0) =
        S.p x * (if qz z then atomInstrumentMass S x z else 0) *
          (if qL d0 d1 s0 s1 y0 y1 then T x d0 d1 s0 s1 y0 y1 else 0) by
      intro z d0 d1 s0 s1 y0 y1
      by_cases hz : qz z <;> by_cases hL : qL d0 d1 s0 s1 y0 y1 <;>
        simp [hz, hL]]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [show ({true, false} : Finset Bool) = Finset.univ by
      ext b
      cases b <;> simp]
  · intro x' hne
    simp [hne]

private abbrev ThresholdLatentTuple (K : ℕ) :=
  Bool × Bool × Bool × Bool × Fin K × Fin K

private noncomputable def thresholdLatentAt
    (ω : ThresholdOmega.{uOmega} 𝒳 K) : ThresholdLatentTuple K :=
  ((thresholdAtomAt ω).d0, (thresholdAtomAt ω).d1,
    (thresholdAtomAt ω).s0, (thresholdAtomAt ω).s1,
    (thresholdAtomAt ω).y0, (thresholdAtomAt ω).y1)

/-- The canonical counterfactual bundle is a function only of the six latent
coordinates and does not inspect the instrument coordinate. -/
private theorem canonicalThresholdCandidate_cfBundle_factors_through_latent
    {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    ∃ g : ThresholdLatentTuple K →
        (∀ i : Fin W.slate.cfBundle.n, W.slate.cfBundle.type i),
      Measurable g ∧ W.slate.cfBundle.jointValue = g ∘ thresholdLatentAt := by
  dsimp only
  let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
  refine ⟨fun p i => ?_, measurable_of_finite _, ?_⟩
  · refine i.cases (motive := fun i => W.slate.cfBundle.type i) p.1 ?_
    intro i
    refine i.cases (motive := fun i => W.slate.cfBundle.type i.succ) p.2.1 ?_
    intro i
    refine i.cases (motive := fun i => W.slate.cfBundle.type i.succ.succ) p.2.2.1 ?_
    intro i
    refine i.cases (motive := fun i => W.slate.cfBundle.type i.succ.succ.succ) p.2.2.2.1 ?_
    intro i
    refine i.cases (motive := fun i => W.slate.cfBundle.type i.succ.succ.succ.succ)
      p.2.2.2.2.1 ?_
    intro i
    refine i.cases
      (motive := fun i => W.slate.cfBundle.type i.succ.succ.succ.succ.succ)
      p.2.2.2.2.2 ?_
    intro i
    exact Fin.elim0 i
  · funext ω i
    fin_cases i
    · change W.slate.D0 ω = (thresholdAtomAt ω).d0
      dsimp [W, canonicalThresholdCandidate]
      exact canonicalThresholdSlate_DofZ S _ _ _ false ω
    · change W.slate.D1 ω = (thresholdAtomAt ω).d1
      dsimp [W, canonicalThresholdCandidate]
      exact canonicalThresholdSlate_DofZ S _ _ _ true ω
    · change W.slate.S0 ω = (thresholdAtomAt ω).s0
      dsimp [W, canonicalThresholdCandidate]
      exact canonicalThresholdSlate_SofD S _ _ _ false ω
    · change W.slate.S1 ω = (thresholdAtomAt ω).s1
      dsimp [W, canonicalThresholdCandidate]
      exact canonicalThresholdSlate_SofD S _ _ _ true ω
    · change W.slate.Y0 ω = (thresholdAtomAt ω).y0
      dsimp [W, canonicalThresholdCandidate]
      exact canonicalThresholdSlate_YofD S _ _ _ false ω
    · change W.slate.Y1 ω = (thresholdAtomAt ω).y1
      dsimp [W, canonicalThresholdCandidate]
      exact canonicalThresholdSlate_YofD S _ _ _ true ω

/-- Every normalized pasted table satisfies conditional instrument independence: given the covariate, its weight is the product of the instrument mass and a latent-table mass. Given [the stated hypotheses](hyp:hp,hprop,hTnonnegative,hTnormalized), [the stated conclusion follows](goal). -/
theorem canonicalThresholdCandidate_ivIndependence
    {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    @IVIndependence 𝒳 _ K W.system W.slate.borel W.slate := by
  classical
  dsimp only
  let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
  letI : StandardBorelSpace W.system.Ω := W.slate.borel
  obtain ⟨g, hgmeas, hg⟩ :=
    canonicalThresholdCandidate_cfBundle_factors_through_latent
      S T hp hprop hTnonnegative hTnormalized
  let latentW : W.system.Ω → ThresholdLatentTuple K := fun ω =>
    (W.slate.D0 ω, W.slate.D1 ω, W.slate.S0 ω,
      W.slate.S1 ω, W.slate.Y0 ω, W.slate.Y1 ω)
  have hgW : W.slate.cfBundle.jointValue = g ∘ latentW := by
    rw [hg]
    funext ω
    apply congrArg g
    dsimp [latentW, W, canonicalThresholdCandidate] at ω ⊢
    apply Prod.ext
    · exact (canonicalThresholdSlate_DofZ S _ _ _ false ω).symm
    apply Prod.ext
    · exact (canonicalThresholdSlate_DofZ S _ _ _ true ω).symm
    apply Prod.ext
    · exact (canonicalThresholdSlate_SofD S _ _ _ false ω).symm
    apply Prod.ext
    · exact (canonicalThresholdSlate_SofD S _ _ _ true ω).symm
    apply Prod.ext
    · exact (canonicalThresholdSlate_YofD S _ _ _ false ω).symm
    · exact (canonicalThresholdSlate_YofD S _ _ _ true ω).symm
  unfold IVIndependence POSystem.CondIndepCF
  rw [hgW]
  change ProbabilityTheory.CondIndepFun
    (MeasurableSpace.comap W.slate.factualX inferInstance)
    W.slate.xVar.measurable_factual.comap_le W.slate.factualZ
      (g ∘ latentW) W.system.μ
  apply condIndepFun_finite_of_measureReal_fibers W.system.μ
    W.slate.factualX W.slate.xVar.measurable_factual
    W.slate.factualZ W.slate.zVar.measurable_factual
    (g ∘ latentW)
  · exact hgmeas.comp measurable_from_top
  · intro x s t _hs _ht
    let qz : Bool → Prop := fun z => z ∈ s
    let qL : Bool → Bool → Bool → Bool → Fin K → Fin K → Prop :=
      fun d0 d1 s0 s1 y0 y1 => g (d0, d1, s0, s1, y0, y1) ∈ t
    let zMass := ∑ z, if qz z then atomInstrumentMass S x z else 0
    let latentMass := ∑ d0, ∑ d1, ∑ s0, ∑ s1, ∑ y0, ∑ y1,
      if qL d0 d1 s0 s1 y0 y1 then T x d0 d1 s0 s1 y0 y1 else 0
    have hjRaw := canonicalThresholdCandidate_separatedEventMass
      S T hp hprop hTnonnegative hTnormalized x qz qL
    have hzRaw := canonicalThresholdCandidate_separatedEventMass
      S T hp hprop hTnonnegative hTnormalized x qz
        (fun _ _ _ _ _ _ => True)
    have hLRaw := canonicalThresholdCandidate_separatedEventMass
      S T hp hprop hTnonnegative hTnormalized x (fun _ => True) qL
    have hjoint :
        W.system.μ.real
            (((W.slate.factualZ ⁻¹' s) ∩ ((g ∘ latentW) ⁻¹' t)) ∩
              W.slate.factualX ⁻¹' {x}) =
          S.p x * zMass * latentMass := by
      rw [show (((W.slate.factualZ ⁻¹' s) ∩
          ((g ∘ latentW) ⁻¹' t)) ∩ W.slate.factualX ⁻¹' {x}) =
          { ω | W.slate.factualX ω = x ∧ qz (W.slate.factualZ ω) ∧
            qL (W.slate.D0 ω) (W.slate.D1 ω) (W.slate.S0 ω)
              (W.slate.S1 ω) (W.slate.Y0 ω) (W.slate.Y1 ω) } by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
          Set.mem_setOf_eq, Function.comp_apply, qz, qL]
        change ((W.slate.factualZ ω ∈ s ∧
          g (latentW ω) ∈ t) ∧ W.slate.factualX ω = x) ↔ _
        simp only [latentW]
        tauto]
      simpa [W, zMass, latentMass] using hjRaw
    have hz :
        W.system.μ.real ((W.slate.factualZ ⁻¹' s) ∩
            W.slate.factualX ⁻¹' {x}) = S.p x * zMass := by
      rw [show ((W.slate.factualZ ⁻¹' s) ∩ W.slate.factualX ⁻¹' {x}) =
          { ω | W.slate.factualX ω = x ∧ qz (W.slate.factualZ ω) ∧
            True } by
        ext ω
        simp [qz, W]
        tauto]
      calc
        _ = S.p x * zMass *
            (∑ d0, ∑ d1, ∑ s0, ∑ s1, ∑ y0, ∑ y1,
              T x d0 d1 s0 s1 y0 y1) := by
          simpa [W, zMass] using hzRaw
        _ = S.p x * zMass := by rw [hTnormalized x]; ring
    have hlatent :
        W.system.μ.real (((g ∘ latentW) ⁻¹' t) ∩
            W.slate.factualX ⁻¹' {x}) = S.p x * latentMass := by
      rw [show (((g ∘ latentW) ⁻¹' t) ∩
          W.slate.factualX ⁻¹' {x}) =
          { ω | W.slate.factualX ω = x ∧ True ∧
            qL (W.slate.D0 ω) (W.slate.D1 ω) (W.slate.S0 ω)
              (W.slate.S1 ω) (W.slate.Y0 ω) (W.slate.Y1 ω) } by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
          Set.mem_setOf_eq, Function.comp_apply, qL]
        simp only [latentW]
        tauto]
      have hinst : (∑ z, atomInstrumentMass S x z) = 1 := by
        simp [atomInstrumentMass, Fintype.sum_bool]
      calc
        _ = S.p x * (∑ z, atomInstrumentMass S x z) * latentMass := by
          simpa [W, latentMass] using hLRaw
        _ = S.p x * latentMass := by rw [hinst]; ring
    have hxmass : W.system.μ.real (W.slate.factualX ⁻¹' {x}) = S.p x := by
      rw [show W.slate.factualX ⁻¹' {x} = W.slate.xEvent x by
        ext ω
        rfl]
      exact canonicalThresholdCandidate_cellMass
        S T hp hprop hTnonnegative hTnormalized x
    rw [hjoint, hxmass, hz, hlatent]
    ring

/-- Given [the stated hypotheses](hyp:hp,hprop,hTnonnegative,hTnormalized,hx), [the canonical threshold candidate conditional tuple property holds](goal). -/
theorem canonicalThresholdCandidate_conditionalTuple {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized)
    (x : 𝒳) (hx : 0 < S.p x) (d0 d1 s0 s1 : Bool) (y0 y1 : Fin K) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    conditionalReal W.system.μ
      {ω | W.slate.D0 ω = d0 ∧ W.slate.D1 ω = d1 ∧
        W.slate.S0 ω = s0 ∧ W.slate.S1 ω = s1 ∧
        W.slate.Y0 ω = y0 ∧ W.slate.Y1 ω = y1}
      (W.slate.xEvent x) = T x d0 d1 s0 s1 y0 y1 := by
  dsimp only
  unfold conditionalReal
  have hcell := canonicalThresholdCandidate_cellMass S T hp hprop
    hTnonnegative hTnormalized x
  rw [if_pos (by simpa [hcell] using hx)]
  rw [show (canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized).system.μ.real
      ({ω |
        (canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized).slate.D0 ω = d0 ∧
        (canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized).slate.D1 ω = d1 ∧
        (canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized).slate.S0 ω = s0 ∧
        (canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized).slate.S1 ω = s1 ∧
        (canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized).slate.Y0 ω = y0 ∧
        (canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized).slate.Y1 ω = y1} ∩
       (canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized).slate.xEvent x) =
      S.p x * T x d0 d1 s0 s1 y0 y1 by
    rw [← canonicalThresholdCandidate_latentTuple S T hp hprop hTnonnegative hTnormalized
      x d0 d1 s0 s1 y0 y1]
    congr 1
    ext ω
    simp only [POSlateSystem.xEvent, POSlateSystem.factualX, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    tauto]
  rw [hcell]
  field_simp

/-- Given [the stated hypotheses](hyp:hp,hprop,hTnonnegative,hTnormalized), [the canonical threshold candidate consistency property holds](goal). -/
theorem canonicalThresholdCandidate_consistency {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    TreatmentConsistency W.slate ∧ SelectionExclusion W.slate ∧
      OutcomeExclusion W.slate := by
  dsimp only
  dsimp [canonicalThresholdCandidate]
  refine ⟨?_, ?_, ?_⟩
  · unfold TreatmentConsistency
    apply Filter.Eventually.of_forall
    intro ω
    change ThresholdOmega.{uOmega} 𝒳 K at ω
    change S.hD (thresholdEval S Regime.empty ω S.dNode) =
      (canonicalThresholdSlate S (thresholdPastedWeight S T)
        (thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative)
        (thresholdPastedWeight_sum_one S T hTnormalized)).DofZ
          (S.hZ (thresholdEval S Regime.empty ω S.zNode)) ω
    simp [thresholdEval_d_empty, thresholdEval_z_empty, atomDArm]
  · unfold SelectionExclusion
    apply Filter.Eventually.of_forall
    intro ω
    change ThresholdOmega.{uOmega} 𝒳 K at ω
    change S.hS (thresholdEval S Regime.empty ω S.sNode) =
      (canonicalThresholdSlate S (thresholdPastedWeight S T)
        (thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative)
        (thresholdPastedWeight_sum_one S T hTnormalized)).SofD
          (S.hD (thresholdEval S Regime.empty ω S.dNode)) ω
    simp [thresholdEval_s_empty, thresholdEval_d_empty, atomDArm, atomSArm]
  · unfold OutcomeExclusion
    apply Filter.Eventually.of_forall
    intro ω _
    change ThresholdOmega.{uOmega} 𝒳 K at ω
    change S.hY (thresholdEval S Regime.empty ω S.yNode) =
      (canonicalThresholdSlate S (thresholdPastedWeight S T)
        (thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative)
        (thresholdPastedWeight_sum_one S T hTnormalized)).YofD
          (S.hD (thresholdEval S Regime.empty ω S.dNode)) ω
    simp [thresholdEval_y_empty, thresholdEval_d_empty, atomDArm, atomYArm]

/-- Given [the stated hypotheses](hyp:hp,hprop,hTnonnegative,hTnormalized,hdefier), [the canonical threshold candidate no defiers property holds](goal). -/
theorem canonicalThresholdCandidate_noDefiers {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized)
    (hdefier : ∀ x s0 s1 y0 y1, T x true false s0 s1 y0 y1 = 0) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    NoDefiers W.slate := by
  dsimp only
  dsimp [canonicalThresholdCandidate]
  let weight := thresholdPastedWeight S T
  let hweight := thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative
  let hsum := thresholdPastedWeight_sum_one S T hTnormalized
  have hzreal : (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
      {ω | (thresholdAtomAt ω).d0 = true ∧ (thresholdAtomAt ω).d1 = false} = 0 := by
    rw [thresholdAtomicMeasure_event weight hweight hsum
      (fun a ↦ a.d0 = true ∧ a.d1 = false)]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a.d0 = true ∧ a.d1 = false
    · simp [ha, weight, thresholdPastedWeight, hdefier]
    · simp [ha]
  have hfinite : ((thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K))
      {ω | (thresholdAtomAt ω).d0 = true ∧ (thresholdAtomAt ω).d1 = false}) ≠ ⊤ := by
    apply ne_of_lt
    calc
      _ ≤ (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := thresholdAtomicMeasure_univ weight hweight hsum
      _ < ⊤ := ENNReal.one_lt_top
  have hz : (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K))
      {ω | (thresholdAtomAt ω).d0 = true ∧ (thresholdAtomAt ω).d1 = false} = 0 :=
    (measureReal_eq_zero_iff hfinite).mp hzreal
  rw [measure_eq_zero_iff_ae_notMem] at hz
  unfold NoDefiers
  filter_upwards [hz] with ω hω
  change ThresholdOmega.{uOmega} 𝒳 K at ω
  have hnot : ¬((thresholdAtomAt ω).d0 = true ∧
      (thresholdAtomAt ω).d1 = false) := hω
  simp only [canonicalThresholdSlate_DofZ, Bool.false_eq_true,
    Bool.true_eq_false, if_false, if_true]
  intro hd0
  cases h1 : (thresholdAtomAt ω).d1
  · exact False.elim (hnot ⟨hd0, h1⟩)
  · rfl

/-- The observed tuple decoded from a threshold atom. -/
def thresholdObservedDatum (a : ThresholdAtom 𝒳 K) : ObservedDatum 𝒳 K :=
  let d := if a.z then a.d1 else a.d0
  let s := if d then a.s1 else a.s0
  let y := if d then a.y1 else a.y0
  ⟨a.x, a.z, d, s, if s then some y else none⟩

/-- The conditional-table mass of all latent tuples decoding to one observed
instrument, treatment, selection, and reported-outcome tuple. -/
def thresholdObservedTableMargin (T : ThresholdCellTable 𝒳 K)
    (x : 𝒳) (z d s : Bool) (y : Option (Fin K)) : ℝ :=
  ∑ d0, ∑ d1, ∑ s0, ∑ s1, ∑ y0, ∑ y1,
    if thresholdObservedDatum (⟨x, z, d0, d1, s0, s1, y0, y1⟩ :
      ThresholdAtom 𝒳 K) = ⟨x, z, d, s, y⟩ then
      T x d0 d1 s0 s1 y0 y1 else 0

/-- The decoded atom sum factors into the observed cell mass, the appropriate instrument propensity factor, and the corresponding conditional-table margin. [the stated conclusion follows](goal). -/
theorem thresholdPastedWeight_observedSum
    {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (o : ObservedDatum 𝒳 K) :
    (∑ a, if thresholdObservedDatum a = o then thresholdPastedWeight S T a else 0) =
      S.p o.cell * atomInstrumentMass S o.cell o.instrument *
        thresholdObservedTableMargin T o.cell o.instrument o.treatment
          o.selected o.outcome := by
  rcases o with ⟨x, z, d, s, y⟩
  let tupleSummand : ThresholdAtomTuple 𝒳 K → ℝ := fun a =>
    if thresholdObservedDatum
        ⟨a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1,
          a.2.2.2.2.2.1, a.2.2.2.2.2.2.1, a.2.2.2.2.2.2.2⟩ =
        ⟨x, z, d, s, y⟩ then
      thresholdPastedWeight S T
        ⟨a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1,
          a.2.2.2.2.2.1, a.2.2.2.2.2.2.1, a.2.2.2.2.2.2.2⟩
    else 0
  rw [show (∑ a : ThresholdAtom 𝒳 K,
      if thresholdObservedDatum a = ⟨x, z, d, s, y⟩ then
        thresholdPastedWeight S T a else 0) =
      ∑ a : ThresholdAtomTuple 𝒳 K, tupleSummand a by
    exact Fintype.sum_equiv thresholdAtomEquiv _ _ (fun a => rfl)]
  simp only [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single x]
  · rw [Fintype.sum_eq_single z]
    · dsimp [tupleSummand, thresholdObservedTableMargin]
      simp only [thresholdPastedWeight]
      simp_rw [show ∀ d0 d1 s0 s1 y0 y1,
          (if thresholdObservedDatum
              (⟨x, z, d0, d1, s0, s1, y0, y1⟩ : ThresholdAtom 𝒳 K) =
              ⟨x, z, d, s, y⟩ then
            S.p x * atomInstrumentMass S x z * T x d0 d1 s0 s1 y0 y1 else 0) =
          S.p x * atomInstrumentMass S x z *
            (if thresholdObservedDatum
                (⟨x, z, d0, d1, s0, s1, y0, y1⟩ : ThresholdAtom 𝒳 K) =
                ⟨x, z, d, s, y⟩ then T x d0 d1 s0 s1 y0 y1 else 0) by
        intro d0 d1 s0 s1 y0 y1
        split <;> ring]
      simp only [Finset.mul_sum]
    · intro z' hz
      simp [tupleSummand, thresholdObservedDatum, hz]
  · intro x' hx
    simp [tupleSummand, thresholdObservedDatum, hx]

/-- [the threshold observed table margin false false selected property holds](goal). -/
theorem thresholdObservedTableMargin_false_false_selected
    (T : ThresholdCellTable 𝒳 K) (x : 𝒳) (i : Fin K) :
    thresholdObservedTableMargin T x false false true (some i) =
      ∑ d1, ∑ s1, ∑ y1, T x false d1 true s1 i y1 := by
  simp [thresholdObservedTableMargin, thresholdObservedDatum, Fintype.sum_bool]

/-- [the threshold observed table margin false true selected property holds](goal). -/
theorem thresholdObservedTableMargin_false_true_selected
    (T : ThresholdCellTable 𝒳 K) (x : 𝒳) (j : Fin K) :
    thresholdObservedTableMargin T x false true true (some j) =
      ∑ d1, ∑ s0, ∑ y0, T x true d1 s0 true y0 j := by
  simp [thresholdObservedTableMargin, thresholdObservedDatum, Fintype.sum_bool]

/-- [the threshold observed table margin true false selected property holds](goal). -/
theorem thresholdObservedTableMargin_true_false_selected
    (T : ThresholdCellTable 𝒳 K) (x : 𝒳) (i : Fin K) :
    thresholdObservedTableMargin T x true false true (some i) =
      ∑ d0, ∑ s1, ∑ y1, T x d0 false true s1 i y1 := by
  simp [thresholdObservedTableMargin, thresholdObservedDatum, Fintype.sum_bool]

/-- [the threshold observed table margin true true selected property holds](goal). -/
theorem thresholdObservedTableMargin_true_true_selected
    (T : ThresholdCellTable 𝒳 K) (x : 𝒳) (j : Fin K) :
    thresholdObservedTableMargin T x true true true (some j) =
      ∑ d0, ∑ s0, ∑ y0, T x d0 true s0 true y0 j := by
  simp [thresholdObservedTableMargin, thresholdObservedDatum, Fintype.sum_bool]

/-- [the threshold observed table margin false false unselected property holds](goal). -/
theorem thresholdObservedTableMargin_false_false_unselected
    (T : ThresholdCellTable 𝒳 K) (x : 𝒳) :
    thresholdObservedTableMargin T x false false false none =
      ∑ d1, ∑ s1, ∑ y0, ∑ y1, T x false d1 false s1 y0 y1 := by
  simp [thresholdObservedTableMargin, thresholdObservedDatum, Fintype.sum_bool]

/-- [the threshold observed table margin false true unselected property holds](goal). -/
theorem thresholdObservedTableMargin_false_true_unselected
    (T : ThresholdCellTable 𝒳 K) (x : 𝒳) :
    thresholdObservedTableMargin T x false true false none =
      ∑ d1, ∑ s0, ∑ y0, ∑ y1, T x true d1 s0 false y0 y1 := by
  simp [thresholdObservedTableMargin, thresholdObservedDatum, Fintype.sum_bool]

/-- [the threshold observed table margin true false unselected property holds](goal). -/
theorem thresholdObservedTableMargin_true_false_unselected
    (T : ThresholdCellTable 𝒳 K) (x : 𝒳) :
    thresholdObservedTableMargin T x true false false none =
      ∑ d0, ∑ s1, ∑ y0, ∑ y1, T x d0 false false s1 y0 y1 := by
  simp [thresholdObservedTableMargin, thresholdObservedDatum, Fintype.sum_bool]

/-- [the threshold observed table margin true true unselected property holds](goal). -/
theorem thresholdObservedTableMargin_true_true_unselected
    (T : ThresholdCellTable 𝒳 K) (x : 𝒳) :
    thresholdObservedTableMargin T x true true false none =
      ∑ d0, ∑ s0, ∑ y0, ∑ y1, T x d0 true s0 false y0 y1 := by
  simp [thresholdObservedTableMargin, thresholdObservedDatum, Fintype.sum_bool]

/-- [the threshold observed table margin invalid property holds](goal). -/
theorem thresholdObservedTableMargin_invalid
    (T : ThresholdCellTable 𝒳 K) (x : 𝒳) (z d : Bool) :
    thresholdObservedTableMargin T x z d true none = 0 ∧
      ∀ i, thresholdObservedTableMargin T x z d false (some i) = 0 := by
  constructor
  · cases z <;> cases d <;>
      simp [thresholdObservedTableMargin, thresholdObservedDatum]
  · intro i
    cases z <;> cases d <;>
      simp [thresholdObservedTableMargin, thresholdObservedDatum]

/-- Given [the stated hypotheses](hyp:hweight,hsum), [the canonical threshold slate observed datum property holds](goal). -/
@[simp] theorem canonicalThresholdSlate_observedDatum
    {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (weight : ThresholdAtom 𝒳 K → ℝ)
    (hweight : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1)
    (ω : ThresholdOmega.{uOmega} 𝒳 K) :
    (canonicalThresholdSlate S weight hweight hsum).observedDatum ω =
      thresholdObservedDatum (thresholdAtomAt ω) := by
  let CS := canonicalThresholdSlate S weight hweight hsum
  have hd : CS.factualD ω =
      atomDArm (thresholdAtomAt ω).z (thresholdAtomAt ω) := by
    change S.hD (thresholdEval S Regime.empty ω S.dNode) = _
    exact thresholdEval_d_empty S ω
  have hs : CS.factualS ω =
      atomSArm (atomDArm (thresholdAtomAt ω).z (thresholdAtomAt ω))
        (thresholdAtomAt ω) := by
    change S.hS (thresholdEval S Regime.empty ω S.sNode) = _
    exact thresholdEval_s_empty S ω
  have hy : CS.factualY ω =
      atomYArm (atomDArm (thresholdAtomAt ω).z (thresholdAtomAt ω))
        (thresholdAtomAt ω) := by
    change S.hY (thresholdEval S Regime.empty ω S.yNode) = _
    exact thresholdEval_y_empty S ω
  change CS.observedDatum ω = _
  unfold POSlateSystem.observedDatum thresholdObservedDatum
  simp only [CS, canonicalThresholdSlate_factualX, canonicalThresholdSlate_factualZ,
    hd, hs, hy]
  simp [atomDArm, atomSArm, atomYArm]

/-- The observed-data map of any finite slate system is measurable. [the stated conclusion follows](goal). -/
theorem measurable_observedDatum {P : POSystem}
    (S : POSlateSystem P 𝒳 K) : Measurable S.observedDatum := by
  intro t _
  rw [show S.observedDatum ⁻¹' t = ⋃ o : t, S.observedDatum ⁻¹' {o.1} by ext; simp]
  apply MeasurableSet.iUnion
  rintro ⟨⟨x, z, d, s, y⟩, -⟩
  have hout : MeasurableSet {ω |
      (if S.factualS ω then some (S.factualY ω) else none) = y} := by
    cases y with
    | none =>
        convert S.sVar.measurable_factual (measurableSet_singleton false) using 1 <;>
          ext ω <;> cases h : S.sVar.factual ω <;> simp [POSlateSystem.factualS, h]
    | some k =>
        convert (S.sVar.measurable_factual (measurableSet_singleton true)).inter
          (S.yVar.measurable_factual (measurableSet_singleton k)) using 1 <;>
          ext ω <;> cases h : S.sVar.factual ω <;>
            simp [POSlateSystem.factualS, POSlateSystem.factualY, h]
  have hm : MeasurableSet {ω | S.factualX ω = x ∧ S.factualZ ω = z ∧
      S.factualD ω = d ∧ S.factualS ω = s ∧
      (if S.factualS ω then some (S.factualY ω) else none) = y} := by
    have h := ((((S.xVar.measurable_factual (measurableSet_singleton x)).inter
      (S.zVar.measurable_factual (measurableSet_singleton z))).inter
      (S.dVar.measurable_factual (measurableSet_singleton d))).inter
      (S.sVar.measurable_factual (measurableSet_singleton s))).inter hout
    convert h using 1 <;> ext ω <;>
      simp [POSlateSystem.factualX, POSlateSystem.factualZ,
        POSlateSystem.factualD, POSlateSystem.factualS, and_assoc]
  convert hm using 1 <;> ext ω <;>
    simp [POSlateSystem.observedDatum, ObservedDatum.mk.injEq, and_assoc]

private theorem thresholdAtomicMeasure_observedSingleton
    (weight : ThresholdAtom 𝒳 K → ℝ) (hweight : ∀ a, 0 ≤ weight a)
    (hsum : ∑ a, weight a = 1) (o : ObservedDatum 𝒳 K) :
    ((thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).map
      (fun ω ↦ thresholdObservedDatum (thresholdAtomAt ω))).real {o} =
      ∑ a, if thresholdObservedDatum a = o then weight a else 0 := by
  rw [Measure.real, Measure.map_apply measurable_from_top MeasurableSet.of_discrete]
  change (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
      {ω | thresholdObservedDatum (thresholdAtomAt ω) = o} = _
  exact thresholdAtomicMeasure_event weight hweight hsum
    (fun a ↦ thresholdObservedDatum a = o)

/-- On every observed singleton, the canonical candidate has the mass obtained by summing the pasted weights of precisely the atoms decoding to that tuple. Given [the stated hypotheses](hyp:hp,hprop,hTnonnegative,hTnormalized), [the stated conclusion follows](goal). -/
theorem canonicalThresholdCandidate_observedSingleton
    {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized)
    (o : ObservedDatum 𝒳 K) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    W.slate.observedLaw.real {o} =
      ∑ a, if thresholdObservedDatum a = o then thresholdPastedWeight S T a else 0 := by
  dsimp only
  let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
  change W.slate.observedLaw.real {o} = _
  rw [show W.slate.observedLaw.real {o} =
      W.system.μ.real (W.slate.observedDatum ⁻¹' {o}) by
    unfold POSlateSystem.observedLaw Measure.real
    rw [Measure.map_apply (measurable_observedDatum W.slate)
      MeasurableSet.of_discrete]]
  change (thresholdAtomicMeasure (thresholdPastedWeight S T) :
      Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
      ((canonicalThresholdSlate S (thresholdPastedWeight S T)
        (thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative)
        (thresholdPastedWeight_sum_one S T hTnormalized)).observedDatum ⁻¹' {o}) = _
  rw [show ((canonicalThresholdSlate S (thresholdPastedWeight S T)
      (thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative)
      (thresholdPastedWeight_sum_one S T hTnormalized)).observedDatum ⁻¹' {o} :
      Set (ThresholdOmega.{uOmega} 𝒳 K)) =
      {ω | thresholdObservedDatum (thresholdAtomAt ω) = o} by
    ext ω
    change (canonicalThresholdSlate S (thresholdPastedWeight S T)
      (thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative)
      (thresholdPastedWeight_sum_one S T hTnormalized)).observedDatum ω = o ↔ _
    rw [canonicalThresholdSlate_observedDatum]
    rfl]
  exact thresholdAtomicMeasure_event (thresholdPastedWeight S T)
    (thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative)
    (thresholdPastedWeight_sum_one S T hTnormalized)
    (fun a ↦ thresholdObservedDatum a = o)

/-- Equality of the finite observed laws follows once the pasted atom table matches the original mass on every decoded observed singleton. Given [the stated hypotheses](hyp:hp,hprop,hTnonnegative,hTnormalized,hmatch), [the stated conclusion follows](goal). -/
theorem canonicalThresholdCandidate_observedLaw_eq_of_singletons
    {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized)
    (hmatch : ∀ o : ObservedDatum 𝒳 K,
      S.observedLaw.real {o} =
        ∑ a, if thresholdObservedDatum a = o then thresholdPastedWeight S T a else 0) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    W.slate.observedLaw = S.observedLaw := by
  dsimp only
  letI : IsProbabilityMeasure S.observedLaw :=
    Measure.isProbabilityMeasure_map (measurable_observedDatum S).aemeasurable
  letI : IsProbabilityMeasure
      (canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized).slate.observedLaw :=
    Measure.isProbabilityMeasure_map
      (measurable_observedDatum
        (canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized).slate).aemeasurable
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro o
  rw [canonicalThresholdCandidate_observedSingleton]
  exact (hmatch o).symm

/-- [the threshold pasted weight survivor benefit sum property holds](goal). -/
theorem thresholdPastedWeight_survivorBenefit_sum {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K) :
    (∑ a : ThresholdAtom 𝒳 K, if a.d0 = false ∧ a.d1 = true ∧
        a.s0 = true ∧ a.s1 = true ∧ a.y0 < a.y1 then
          thresholdPastedWeight S T a else 0) =
      ∑ x, S.p x * benefitMass (tableSurvivorCoupling (T x)) := by
  rw [show (∑ a : ThresholdAtom 𝒳 K, if a.d0 = false ∧ a.d1 = true ∧
      a.s0 = true ∧ a.s1 = true ∧ a.y0 < a.y1 then
        thresholdPastedWeight S T a else 0) =
      ∑ a : ThresholdAtomTuple 𝒳 K, if a.2.2.1 = false ∧
        a.2.2.2.1 = true ∧ a.2.2.2.2.1 = true ∧
        a.2.2.2.2.2.1 = true ∧ a.2.2.2.2.2.2.1 < a.2.2.2.2.2.2.2 then
          thresholdPastedWeight S T (thresholdAtomEquiv.symm a) else 0 by
    exact Fintype.sum_equiv thresholdAtomEquiv _ _ (fun a ↦ rfl)]
  simp only [Fintype.sum_prod_type]
  simp [thresholdAtomEquiv, thresholdPastedWeight, atomInstrumentMass, Fintype.sum_bool,
    benefitMass, tableSurvivorCoupling]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_filter]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j <;> simp [hij] <;> ring

/-- [the threshold pasted weight survivor mass sum property holds](goal). -/
theorem thresholdPastedWeight_survivorMass_sum {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K) :
    (∑ a : ThresholdAtom 𝒳 K, if a.d0 = false ∧ a.d1 = true ∧
        a.s0 = true ∧ a.s1 = true then thresholdPastedWeight S T a else 0) =
      ∑ x, S.p x * totalMass (tableSurvivorCoupling (T x)) := by
  rw [show (∑ a : ThresholdAtom 𝒳 K, if a.d0 = false ∧ a.d1 = true ∧
      a.s0 = true ∧ a.s1 = true then thresholdPastedWeight S T a else 0) =
      ∑ a : ThresholdAtomTuple 𝒳 K, if a.2.2.1 = false ∧
        a.2.2.2.1 = true ∧ a.2.2.2.2.1 = true ∧
        a.2.2.2.2.2.1 = true then
          thresholdPastedWeight S T (thresholdAtomEquiv.symm a) else 0 by
    exact Fintype.sum_equiv thresholdAtomEquiv _ _ (fun a ↦ rfl)]
  simp only [Fintype.sum_prod_type]
  simp [thresholdAtomEquiv, thresholdPastedWeight, atomInstrumentMass, Fintype.sum_bool,
    totalMass, tableSurvivorCoupling]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The aggregate strict-benefit probability of the canonical pasted law is the ratio of the corresponding survivor-table masses. Given [the stated hypotheses](hyp:hp,hprop,hTnonnegative,hTnormalized,hpositive), [the stated conclusion follows](goal). -/
theorem canonicalThresholdCandidate_benefitProbabilityOf
    {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized)
    (hpositive : 0 < ∑ x, S.p x * totalMass (tableSurvivorCoupling (T x))) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    benefitProbabilityOf W =
      (∑ x, S.p x * benefitMass (tableSurvivorCoupling (T x))) /
        (∑ x, S.p x * totalMass (tableSurvivorCoupling (T x))) := by
  dsimp only
  let weight := thresholdPastedWeight S T
  let hweight := thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative
  let hsum := thresholdPastedWeight_sum_one S T hTnormalized
  let CS := canonicalThresholdSlate S weight hweight hsum
  have hden : (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
      { ω | (thresholdAtomAt ω).d0 = false ∧ (thresholdAtomAt ω).d1 = true ∧
        (thresholdAtomAt ω).s0 = true ∧ (thresholdAtomAt ω).s1 = true } =
      ∑ x, S.p x * totalMass (tableSurvivorCoupling (T x)) := by
    calc
      _ = ∑ a : ThresholdAtom 𝒳 K, if a.d0 = false ∧ a.d1 = true ∧
          a.s0 = true ∧ a.s1 = true then weight a else 0 :=
        thresholdAtomicMeasure_event weight hweight hsum
          (fun a ↦ a.d0 = false ∧ a.d1 = true ∧ a.s0 = true ∧ a.s1 = true)
      _ = _ := by simpa [weight] using thresholdPastedWeight_survivorMass_sum S T
  have hnum : (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
      { ω | (thresholdAtomAt ω).d0 = false ∧ (thresholdAtomAt ω).d1 = true ∧
        (thresholdAtomAt ω).s0 = true ∧ (thresholdAtomAt ω).s1 = true ∧
        (thresholdAtomAt ω).y0 < (thresholdAtomAt ω).y1 } =
      ∑ x, S.p x * benefitMass (tableSurvivorCoupling (T x)) := by
    calc
      _ = ∑ a : ThresholdAtom 𝒳 K, if a.d0 = false ∧ a.d1 = true ∧
          a.s0 = true ∧ a.s1 = true ∧ a.y0 < a.y1 then weight a else 0 :=
        thresholdAtomicMeasure_event weight hweight hsum
          (fun a ↦ a.d0 = false ∧ a.d1 = true ∧ a.s0 = true ∧
            a.s1 = true ∧ a.y0 < a.y1)
      _ = _ := by simpa [weight] using thresholdPastedWeight_survivorBenefit_sum S T
  change benefitProbabilityOf
      ({ system := canonicalThresholdPOSystem S weight hweight hsum
         slate := CS } : FullLawCandidate P 𝒳 K) = _
  unfold benefitProbabilityOf conditionalReal
  dsimp only [FullLawCandidate.system, FullLawCandidate.slate]
  change (if 0 < (thresholdAtomicMeasure weight).real
      {ω | CS.S0 ω = true ∧ CS.S1 ω = true ∧ ω ∈ CS.complierEvent} then
    (thresholdAtomicMeasure weight).real
      ({ω | CS.Y0 ω < CS.Y1 ω ∧ CS.S0 ω = true ∧
        CS.S1 ω = true ∧ ω ∈ CS.complierEvent} ∩
       {ω | CS.S0 ω = true ∧ CS.S1 ω = true ∧ ω ∈ CS.complierEvent}) /
      (thresholdAtomicMeasure weight).real
        {ω | CS.S0 ω = true ∧ CS.S1 ω = true ∧ ω ∈ CS.complierEvent}
    else 0) = _
  have hsetden : ({ω | CS.S0 ω = true ∧ CS.S1 ω = true ∧
      ω ∈ CS.complierEvent} : Set (ThresholdOmega.{uOmega} 𝒳 K)) =
      {ω | (thresholdAtomAt ω).d0 = false ∧ (thresholdAtomAt ω).d1 = true ∧
        (thresholdAtomAt ω).s0 = true ∧ (thresholdAtomAt ω).s1 = true} := by
    ext ω
    change ThresholdOmega.{uOmega} 𝒳 K at ω
    change (CS.S0 ω = true ∧ CS.S1 ω = true ∧
      CS.D0 ω = false ∧ CS.D1 ω = true) ↔ _
    have hd0 : CS.D0 ω = (thresholdAtomAt ω).d0 := by
      simp [CS, POSlateSystem.D0, canonicalThresholdSlate_DofZ]
    have hd1 : CS.D1 ω = (thresholdAtomAt ω).d1 := by
      simp [CS, POSlateSystem.D1, canonicalThresholdSlate_DofZ]
    have hs0 : CS.S0 ω = (thresholdAtomAt ω).s0 := by
      simp [CS, POSlateSystem.S0, canonicalThresholdSlate_SofD]
    have hs1 : CS.S1 ω = (thresholdAtomAt ω).s1 := by
      simp [CS, POSlateSystem.S1, canonicalThresholdSlate_SofD]
    simp [hd0, hd1, hs0, hs1, and_assoc, and_left_comm, and_comm]
  have hsetnum : ({ω | CS.Y0 ω < CS.Y1 ω ∧ CS.S0 ω = true ∧
      CS.S1 ω = true ∧ ω ∈ CS.complierEvent} ∩
      {ω | CS.S0 ω = true ∧ CS.S1 ω = true ∧
        ω ∈ CS.complierEvent} :
      Set (ThresholdOmega.{uOmega} 𝒳 K)) =
      {ω | (thresholdAtomAt ω).d0 = false ∧ (thresholdAtomAt ω).d1 = true ∧
        (thresholdAtomAt ω).s0 = true ∧ (thresholdAtomAt ω).s1 = true ∧
        (thresholdAtomAt ω).y0 < (thresholdAtomAt ω).y1} := by
    ext ω
    change ThresholdOmega.{uOmega} 𝒳 K at ω
    change ((CS.Y0 ω < CS.Y1 ω ∧ CS.S0 ω = true ∧ CS.S1 ω = true ∧
      CS.D0 ω = false ∧ CS.D1 ω = true) ∧
      (CS.S0 ω = true ∧ CS.S1 ω = true ∧ CS.D0 ω = false ∧
        CS.D1 ω = true)) ↔ _
    have hd0 : CS.D0 ω = (thresholdAtomAt ω).d0 := by
      simp [CS, POSlateSystem.D0, canonicalThresholdSlate_DofZ]
    have hd1 : CS.D1 ω = (thresholdAtomAt ω).d1 := by
      simp [CS, POSlateSystem.D1, canonicalThresholdSlate_DofZ]
    have hs0 : CS.S0 ω = (thresholdAtomAt ω).s0 := by
      simp [CS, POSlateSystem.S0, canonicalThresholdSlate_SofD]
    have hs1 : CS.S1 ω = (thresholdAtomAt ω).s1 := by
      simp [CS, POSlateSystem.S1, canonicalThresholdSlate_SofD]
    have hy0 : CS.Y0 ω = (thresholdAtomAt ω).y0 := by
      simp [CS, POSlateSystem.Y0, canonicalThresholdSlate_YofD]
    have hy1 : CS.Y1 ω = (thresholdAtomAt ω).y1 := by
      simp [CS, POSlateSystem.Y1, canonicalThresholdSlate_YofD]
    simp [hd0, hd1, hs0, hs1, hy0, hy1, and_assoc, and_left_comm, and_comm]
  rw [hsetnum, hsetden, hden, hnum, if_pos hpositive]

/-- Cell-table support restrictions imply weak selection monotonicity for the canonical pasted law. Given [the stated hypotheses](hyp:hp,hprop,hTnonnegative,hTnormalized,hinc,hdec), [the stated conclusion follows](goal). -/
theorem canonicalThresholdCandidate_weakSelectionMonotonicity
    {P : POSystem.{uV, uVal, uOmega}}
    (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized)
    (d : 𝒳 → Bool)
    (hinc : ∀ x y0 y1, d x = true → T x false true true false y0 y1 = 0)
    (hdec : ∀ x y0 y1, d x = false → T x false true false true y0 y1 = 0) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    WeakSelectionMonotonicity W.slate d := by
  dsimp only
  dsimp [canonicalThresholdCandidate]
  let weight := thresholdPastedWeight S T
  let hweight := thresholdPastedWeight_nonnegative S T hp hprop hTnonnegative
  let hsum := thresholdPastedWeight_sum_one S T hTnormalized
  let CS := canonicalThresholdSlate S weight hweight hsum
  unfold WeakSelectionMonotonicity
  intro x _
  cases hd : d x
  · have hreal : (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
        {ω | (thresholdAtomAt ω).x = x ∧ (thresholdAtomAt ω).d0 = false ∧
          (thresholdAtomAt ω).d1 = true ∧ (thresholdAtomAt ω).s0 = false ∧
          (thresholdAtomAt ω).s1 = true} = 0 := by
      calc
        _ = ∑ a : ThresholdAtom 𝒳 K, if a.x = x ∧ a.d0 = false ∧ a.d1 = true ∧
            a.s0 = false ∧ a.s1 = true then weight a else 0 :=
          thresholdAtomicMeasure_event weight hweight hsum _
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro a _
          by_cases ha : a.x = x ∧ a.d0 = false ∧ a.d1 = true ∧
              a.s0 = false ∧ a.s1 = true
          · have hda : d a.x = false := by simpa [ha.1] using hd
            simp [ha, weight, thresholdPastedWeight, hdec a.x a.y0 a.y1 hda]
            exact Or.inr (hdec x a.y0 a.y1 hd)
          · simp [ha]
    have hfinite : (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K))
        {ω | (thresholdAtomAt ω).x = x ∧ (thresholdAtomAt ω).d0 = false ∧
          (thresholdAtomAt ω).d1 = true ∧ (thresholdAtomAt ω).s0 = false ∧
          (thresholdAtomAt ω).s1 = true} ≠ ⊤ := by
      apply ne_of_lt
      calc
        _ ≤ (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := thresholdAtomicMeasure_univ weight hweight hsum
        _ < ⊤ := ENNReal.one_lt_top
    have hzero := (measureReal_eq_zero_iff hfinite).mp hreal
    rw [measure_eq_zero_iff_ae_notMem] at hzero
    have hrestrictMeas : MeasurableSet (CS.complierEvent ∩ CS.xEvent x) := by
      change @MeasurableSet (ThresholdOmega.{uOmega} 𝒳 K) ⊤ _
      exact MeasurableSet.of_discrete
    filter_upwards [ae_restrict_of_ae hzero,
      ae_restrict_mem hrestrictMeas] with ω hω hmem
    change ThresholdOmega.{uOmega} 𝒳 K at ω
    have hxatom : (thresholdAtomAt ω).x = x := by
      have hxmem := hmem.2
      change CS.factualX ω = x at hxmem
      simpa [CS, canonicalThresholdSlate_factualX] using hxmem
    have hd0 : CS.D0 ω = (thresholdAtomAt ω).d0 := by
      simp [CS, POSlateSystem.D0, canonicalThresholdSlate_DofZ]
    have hd1 : CS.D1 ω = (thresholdAtomAt ω).d1 := by
      simp [CS, POSlateSystem.D1, canonicalThresholdSlate_DofZ]
    have hs0 : CS.S0 ω = (thresholdAtomAt ω).s0 := by
      simp [CS, POSlateSystem.S0, canonicalThresholdSlate_SofD]
    have hs1 : CS.S1 ω = (thresholdAtomAt ω).s1 := by
      simp [CS, POSlateSystem.S1, canonicalThresholdSlate_SofD]
    have hc : CS.D0 ω = false ∧ CS.D1 ω = true := hmem.1
    constructor
    · simp [hd]
    · intro _
      cases h0 : (thresholdAtomAt ω).s0 <;> cases h1 : (thresholdAtomAt ω).s1 <;>
        simp [hs0, hs1, h0, h1]
      exact False.elim (hω ⟨hxatom, hd0.symm.trans hc.1,
        hd1.symm.trans hc.2, h0, h1⟩)
  · have hreal : (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)).real
        {ω | (thresholdAtomAt ω).x = x ∧ (thresholdAtomAt ω).d0 = false ∧
          (thresholdAtomAt ω).d1 = true ∧ (thresholdAtomAt ω).s0 = true ∧
          (thresholdAtomAt ω).s1 = false} = 0 := by
      calc
        _ = ∑ a : ThresholdAtom 𝒳 K, if a.x = x ∧ a.d0 = false ∧ a.d1 = true ∧
            a.s0 = true ∧ a.s1 = false then weight a else 0 :=
          thresholdAtomicMeasure_event weight hweight hsum _
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro a _
          by_cases ha : a.x = x ∧ a.d0 = false ∧ a.d1 = true ∧
              a.s0 = true ∧ a.s1 = false
          · have hda : d a.x = true := by simpa [ha.1] using hd
            simp [ha, weight, thresholdPastedWeight, hinc a.x a.y0 a.y1 hda]
            exact Or.inr (hinc x a.y0 a.y1 hd)
          · simp [ha]
    have hfinite : (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K))
        {ω | (thresholdAtomAt ω).x = x ∧ (thresholdAtomAt ω).d0 = false ∧
          (thresholdAtomAt ω).d1 = true ∧ (thresholdAtomAt ω).s0 = true ∧
          (thresholdAtomAt ω).s1 = false} ≠ ⊤ := by
      apply ne_of_lt
      calc
        _ ≤ (thresholdAtomicMeasure weight : Measure (ThresholdOmega.{uOmega} 𝒳 K)) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := thresholdAtomicMeasure_univ weight hweight hsum
        _ < ⊤ := ENNReal.one_lt_top
    have hzero := (measureReal_eq_zero_iff hfinite).mp hreal
    rw [measure_eq_zero_iff_ae_notMem] at hzero
    have hrestrictMeas : MeasurableSet (CS.complierEvent ∩ CS.xEvent x) := by
      change @MeasurableSet (ThresholdOmega.{uOmega} 𝒳 K) ⊤ _
      exact MeasurableSet.of_discrete
    filter_upwards [ae_restrict_of_ae hzero,
      ae_restrict_mem hrestrictMeas] with ω hω hmem
    change ThresholdOmega.{uOmega} 𝒳 K at ω
    have hxatom : (thresholdAtomAt ω).x = x := by
      have hxmem := hmem.2
      change CS.factualX ω = x at hxmem
      simpa [CS, canonicalThresholdSlate_factualX] using hxmem
    have hd0 : CS.D0 ω = (thresholdAtomAt ω).d0 := by
      simp [CS, POSlateSystem.D0, canonicalThresholdSlate_DofZ]
    have hd1 : CS.D1 ω = (thresholdAtomAt ω).d1 := by
      simp [CS, POSlateSystem.D1, canonicalThresholdSlate_DofZ]
    have hs0 : CS.S0 ω = (thresholdAtomAt ω).s0 := by
      simp [CS, POSlateSystem.S0, canonicalThresholdSlate_SofD]
    have hs1 : CS.S1 ω = (thresholdAtomAt ω).s1 := by
      simp [CS, POSlateSystem.S1, canonicalThresholdSlate_SofD]
    have hc : CS.D0 ω = false ∧ CS.D1 ω = true := hmem.1
    constructor
    · intro _
      cases h0 : (thresholdAtomAt ω).s0 <;> cases h1 : (thresholdAtomAt ω).s1 <;>
        simp [hs0, hs1, h0, h1]
      exact False.elim (hω ⟨hxatom, hd0.symm.trans hc.1,
        hd1.symm.trans hc.2, h0, h1⟩)
    · simp [hd]

end CausalSmith.PartialID.SlateBenefitPartialTransport
