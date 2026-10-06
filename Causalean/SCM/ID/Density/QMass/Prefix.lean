/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.Density.LatentBlocks
public import Causalean.SCM.ID.Density.IdentifyMass
public import Causalean.SCM.ID.Density.MassBridge
public import Causalean.SCM.ID.DiscreteID.Positive
public import Causalean.SCM.ID.GraphicalThms.DoGFormula
public import Mathlib.Probability.Independence.InfinitePi
public import Causalean.Tactic.Attr
public import Causalean.SCM.ID.Density.QMass.Factorization

/-! # Positivity and telescoping for prefix q-masses

This file proves positivity of the do-model ancestral marginal under positive
observational mass and the ENNReal telescoping identity used to turn successive
prefix-mass ratios into a district factor.
-/

public section

open Causalean.Graph


set_option linter.unusedFintypeInType false

open Causalean.Mathlib.MeasureTheory

namespace Causalean.SCM.ID

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- For [an intervention set `X` whose random copies are observed and whose fixed copies are
not already frozen](hyp:hObs,hFix), [a positive observational kernel at every fixed-value
assignment](hyp:hpos), and [an outcome set `Y` disjoint from the random copies of
`X`](hyp:hYX), [the do(X)-law ancestral marginal kernel used in the identification density
assembly also has everywhere-positive point mass](goal). -/
lemma doObsKernelAncestralMarginal_positiveMass
    [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (hpos : ∀ s' : M.FixedValues, DiscreteID.PositiveMass (M.obsKernel s'))
    (hYX : ∀ d ∈ X, SWIGNode.random d ∉ Y)
    (sDo : (M.fixSet X hObs hFix).FixedValues) :
    DiscreteID.PositiveMass (doObsKernelAncestralMarginal M X hObs hFix Y sDo) := by
  classical
  let MX := M.fixSet X hObs hFix
  let D := fixObservedAncestralSet M X hObs hFix Y
  let A := fixAncestralSet M X hObs hFix Y
  have hDclosed : MX.ObsParentClosed D := by
    simpa [MX, D] using fixObservedAncestralSet_obsParent_closed M X hObs hFix Y
  intro xD
  let xFull : ValuesOn M.observed (swigΩ Ω) := fun v =>
    if hvD : v.val ∈ D then
      xD ⟨v.val, hvD⟩
    else
      match v.val with
      | SWIGNode.random d =>
          if hd : d ∈ X then
            sDo ⟨SWIGNode.fixed d,
              Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨d, hd, rfl⟩)⟩
          else
            Classical.choice (inferInstance : Nonempty (swigΩ Ω (SWIGNode.random d)))
      | SWIGNode.fixed d =>
          Classical.choice (inferInstance : Nonempty (swigΩ Ω (SWIGNode.fixed d)))
  let xDo : ValuesOn MX.observed (swigΩ Ω) := fun v =>
    xFull ⟨v.val, v.property⟩
  have hprojD :
      valuesProjection hDclosed.1 xDo = xD := by
    ext v
    simp [valuesProjection, xDo, xFull, v.property]
  have hpin : ∀ d (hd : d ∈ X),
      xFull ⟨SWIGNode.random d, hObs d hd⟩ =
        sDo ⟨SWIGNode.fixed d,
          Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨d, hd, rfl⟩)⟩ := by
    intro d hd
    have hnotD : SWIGNode.random d ∉ D := by
      intro hdD
      have hdA : SWIGNode.random d ∈ A := (Finset.mem_inter.mp hdD).1
      exact hYX d hd
        ((random_intervened_mem_fixAncestralSet_iff_mem_Y M X hObs hFix Y hd).mp hdA)
    simp [xFull, hnotD, hd]
  have hobsAgree : ∀ w (hw : w ∈ M.observed),
      xDo ⟨w, by simpa [MX, SCM.fixSet_observed] using hw⟩ = xFull ⟨w, hw⟩ := by
    intro w hw
    rfl
  have hq_ne :
      ∀ C ∈ MX.toSWIGGraph.cComponentSet,
        MX.qLocalMass sDo (C ∩ D)
            (fun _ hv => hDclosed.1 (Finset.mem_of_mem_inter_right hv)) xDo ≠ 0 := by
    intro C _hC
    have hsubsetM : C ∩ D ⊆ M.observed := by
      intro v hv
      have hvD : v ∈ D := Finset.mem_of_mem_inter_right hv
      exact Finset.inter_subset_right hvD
    have hqeq :
        MX.qLocalMass sDo (C ∩ D)
            (fun _ hv => hDclosed.1 (Finset.mem_of_mem_inter_right hv)) xDo =
          M.qLocalMass (M.fixSetProj X hObs hFix sDo) (C ∩ D) hsubsetM xFull := by
      simp only [causal_defs_simps]
      congr 1
      ext ℓ
      constructor
      · intro hLocal v hv
        have hvD : v ∈ D := Finset.mem_of_mem_inter_right hv
        have hnot : v ∉ X.image SWIGNode.random := by
          intro hvX
          rcases Finset.mem_image.mp hvX with ⟨d, hd, rfl⟩
          have hdA : SWIGNode.random d ∈ A := (Finset.mem_inter.mp hvD).1
          exact hYX d hd
            ((random_intervened_mem_fixAncestralSet_iff_mem_Y M X hObs hFix Y hd).mp hdA)
        exact (localConsistent_fixSet_iff M X hObs hFix sDo
          (M.fixSetProj X hObs hFix sDo) xDo xFull v
          ((fun _ hv => hDclosed.1 (Finset.mem_of_mem_inter_right hv)) v hv)
          (hsubsetM hv) hnot hobsAgree hpin rfl ℓ).mp (hLocal v hv)
      · intro hLocal v hv
        have hvD : v ∈ D := Finset.mem_of_mem_inter_right hv
        have hnot : v ∉ X.image SWIGNode.random := by
          intro hvX
          rcases Finset.mem_image.mp hvX with ⟨d, hd, rfl⟩
          have hdA : SWIGNode.random d ∈ A := (Finset.mem_inter.mp hvD).1
          exact hYX d hd
            ((random_intervened_mem_fixAncestralSet_iff_mem_Y M X hObs hFix Y hd).mp hdA)
        exact (localConsistent_fixSet_iff M X hObs hFix sDo
          (M.fixSetProj X hObs hFix sDo) xDo xFull v
          ((fun _ hv => hDclosed.1 (Finset.mem_of_mem_inter_right hv)) v hv)
          (hsubsetM hv) hnot hobsAgree hpin rfl ℓ).mpr (hLocal v hv)
    rw [hqeq]
    exact M.qLocalMass_pos_of_positiveObs (M.fixSetProj X hObs hFix sDo)
      (hpos (M.fixSetProj X hObs hFix sDo)) (C ∩ D) hsubsetM xFull
  have hmass := MX.obsKernel_marginal_singleton_eq_prod_qLocalMass sDo D hDclosed xDo
  have hkey : doObsKernelAncestralMarginal M X hObs hFix Y
      = MX.obsKernel.map (valuesProjection hDclosed.1) := rfl
  unfold DiscreteID.singletonMass
  rw [hkey,
    ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection hDclosed.1),
    ← hprojD, hmass]
  exact Finset.prod_ne_zero_iff.mpr hq_ne

/-- Pure ENNReal telescope for products of selected adjacent ratios. -/
lemma prod_filter_div_telescope
    (a : ℕ → ENNReal) (m : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.range m)
    (hne : ∀ i ≤ m, a i ≠ 0) (hfin : ∀ i ≤ m, a i ≠ ⊤)
    (hconst : ∀ i < m, i ∉ T → a (i + 1) = a i) :
    ∏ i ∈ T, a (i + 1) / a i = a m / a 0 := by
  classical
  have hrange_all :
      ∀ n : ℕ, (∀ i ≤ n, a i ≠ 0) → (∀ i ≤ n, a i ≠ ⊤) →
        ∏ i ∈ Finset.range n, a (i + 1) / a i = a n / a 0 := by
    intro n hnne hnfin
    induction n with
    | zero =>
        simp [ENNReal.div_self (hnne 0 le_rfl) (hnfin 0 le_rfl)]
    | succ m ih =>
        rw [Finset.prod_range_succ]
        have hih :
            ∏ i ∈ Finset.range m, a (i + 1) / a i = a m / a 0 :=
          ih (fun i hi => hnne i (Nat.le_trans hi (Nat.le_succ m)))
            (fun i hi => hnfin i (Nat.le_trans hi (Nat.le_succ m)))
        rw [hih]
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        rw [show a m * (a 0)⁻¹ * (a (m + 1) * (a m)⁻¹)
              = a (m + 1) * (a m * (a m)⁻¹) * (a 0)⁻¹ by ac_rfl]
        rw [ENNReal.mul_inv_cancel (hnne m (Nat.le_succ m)) (hnfin m (Nat.le_succ m))]
        simp
  have hrange :
      ∏ i ∈ Finset.range m, a (i + 1) / a i = a m / a 0 :=
    hrange_all m hne hfin
  have hsubset :
      ∏ i ∈ T, a (i + 1) / a i =
        ∏ i ∈ Finset.range m, a (i + 1) / a i := by
    exact Finset.prod_subset hT (by
      intro i hiRange hiT
      have hi_lt : i < m := Finset.mem_range.mp hiRange
      rw [hconst i hi_lt hiT]
      exact ENNReal.div_self (hne i (Nat.le_of_lt hi_lt))
        (hfin i (Nat.le_of_lt hi_lt)))
  rw [hsubset, hrange]


end Causalean.SCM.ID
