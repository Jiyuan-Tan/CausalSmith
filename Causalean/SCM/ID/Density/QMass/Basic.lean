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

/-! # Elimination and marginalization for local q-masses

This file develops the basic finite-mass calculus for `qLocalMass`: point-value
updates, one-coordinate summation, and marginalization over ancestrally closed
sets.  These operations are the mass-level substrate for later component
factorization and recursive district extraction.
-/

@[expose] public section

open Causalean.Graph


set_option linter.unusedFintypeInType false

open Causalean.Mathlib.MeasureTheory

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators
open MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- For [a structural causal model](hyp:M), [a fixed-value assignment](hyp:s),
    [a finite set of observed SWIG vertices](hyp:T), [contained in the model's observed-node set](hyp:hT), and [an assignment
    of values to all observed SWIG vertices](hyp:x), the [local q-mass](goal)
    is the latent-product mass of latent-variable assignments for which every
    vertex in the specified set satisfies its local structural consistency
    condition at those fixed and observed values. -/
noncomputable def qLocalMass
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (T : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) : ENNReal :=
  M.latentProduct {ℓ | ∀ v (hv : v ∈ T),
    M.localConsistent s x v (hT hv) ℓ}

/-- The local q-mass of an observed subset is the latent-product mass of the set of latent draws
that make every node of that subset locally consistent with the given fixed values and observed
values. -/
@[causal_defs_simps]
lemma qLocalMass_eq
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (T : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s T hT x =
      M.latentProduct {ℓ | ∀ v (hv : v ∈ T),
        M.localConsistent s x v (hT hv) ℓ} :=
  rfl

/-- The empty local q-mass is one. -/
@[simp] lemma qLocalMass_empty
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s ∅ (by simp) x = 1 := by
  simp [causal_defs_simps]

/-- Local q-mass is antitone in the constrained observed set. -/
lemma qLocalMass_anti
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    {T T' : Finset (SWIGNode N)} (hTT' : T ⊆ T')
    (hT : T ⊆ M.observed) (hT' : T' ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s T' hT' x ≤ M.qLocalMass s T hT x := by
  apply MeasureTheory.measure_mono
  intro ℓ hℓ v hv
  exact hℓ v (hTT' hv)

/-- A value at one SWIG node is packaged as an assignment on the singleton set containing that
node. This helper is used when conditioning or overriding a model with one node's specified value. -/
def singletonValuePt
    (v : SWIGNode N) (ω : swigΩ Ω v) :
    ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω) :=
  fun i => cast (congrArg (swigΩ Ω) (Finset.mem_singleton.mp i.property).symm) ω

@[simp] private lemma singletonValuePt_self
    (v : SWIGNode N) (ω : swigΩ Ω v) :
    singletonValuePt v ω ⟨v, by simp⟩ = ω := by
  simp [singletonValuePt]

@[simp] private lemma overrideOn_singleton_self
    {M : Causalean.SCM N Ω} {v : SWIGNode N} (hv : v ∈ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) (ω : swigΩ Ω v) :
    overrideOn x (singletonValuePt v ω)
      ⟨v, hv⟩ = ω := by
  simp

@[simp] private lemma overrideOn_singleton_ne
    {M : Causalean.SCM N Ω} {v w : SWIGNode N}
    (hw : w ∈ M.observed) (hvw : w ≠ v)
    (x : ValuesOn M.observed (swigΩ Ω)) (ω : swigΩ Ω v) :
    overrideOn x (singletonValuePt v ω)
      ⟨w, hw⟩ = x ⟨w, hw⟩ := by
  simp [hvw]

private noncomputable def singletonValuePtEquiv
    (v : SWIGNode N) :
    swigΩ Ω v ≃ ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω) where
  toFun := singletonValuePt v
  invFun := fun y => y ⟨v, by simp⟩
  left_inv := by
    intro ω
    simp
  right_inv := by
    intro y
    funext i
    rcases i with ⟨w, hw⟩
    have hwv : w = v := Finset.mem_singleton.mp hw
    subst w
    simp [singletonValuePt]

@[simp] private lemma singletonValuePtEquiv_symm_apply
    (v : SWIGNode N)
    (y : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω)) :
    singletonValuePt v ((singletonValuePtEquiv (Ω := Ω) v).symm y) = y := by
  exact (singletonValuePtEquiv (Ω := Ω) v).right_inv y

private lemma overrideOn_union_singletonValuePt
    {I U : Finset (SWIGNode N)} {v : SWIGNode N}
    (x : ValuesOn I (swigΩ Ω)) (y : ValuesOn U (swigΩ Ω))
    (ω : swigΩ Ω v) :
    overrideOn x (valuesUnionMk (singletonValuePt v ω) y) =
      overrideOn (overrideOn x y) (singletonValuePt v ω) := by
  classical
  funext i
  by_cases hiv : i.val = v
  · have hiSing : i.val ∈ ({v} : Finset (SWIGNode N)) := by simp [hiv]
    have hiUnion : i.val ∈ ({v} : Finset (SWIGNode N)) ∪ U :=
      Finset.mem_union_left U hiSing
    rw [overrideOn_mem _ _ i hiUnion]
    rw [valuesUnionMk_apply_left _ _ hiSing]
    rw [overrideOn_mem _ _ i hiSing]
  · have hiNotSing : i.val ∉ ({v} : Finset (SWIGNode N)) := by simpa using hiv
    by_cases hiU : i.val ∈ U
    · have hiUnion : i.val ∈ ({v} : Finset (SWIGNode N)) ∪ U :=
        Finset.mem_union_right _ hiU
      rw [overrideOn_mem _ _ i hiUnion]
      rw [valuesUnionMk_apply_right _ _ hiUnion hiNotSing]
      rw [overrideOn_notMem _ _ i hiNotSing]
      rw [overrideOn_mem x y i hiU]
    · have hiUnionNot : i.val ∉ ({v} : Finset (SWIGNode N)) ∪ U := by
        intro hmem
        rcases Finset.mem_union.mp hmem with hs | hUmem
        · exact hiNotSing hs
        · exact hiU hUmem
      rw [overrideOn_notMem _ _ i hiUnionNot]
      rw [overrideOn_notMem _ _ i hiNotSing]
      rw [overrideOn_notMem x y i hiU]

private lemma marginalizeOn_congr_finset
    [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) {A B : Finset (SWIGNode N)}
    (hAB : A = B) (hA : A ⊆ M.observed) (hB : B ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    marginalizeOn M.observed A hA q x = marginalizeOn M.observed B hB q x := by
  classical
  subst B
  unfold marginalizeOn
  refine Finset.sum_congr rfl ?_
  intro y _hy
  congr

/-- Marginalizing a mass function over an empty set of observed coordinates leaves its value at
every observed assignment unchanged. -/
lemma marginalizeOn_empty
    [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    marginalizeOn M.observed ∅ (by simp) q x = q x := by
  classical
  unfold marginalizeOn
  let y0 : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω) :=
    fun i => False.elim (Finset.notMem_empty i.val i.property)
  rw [Finset.sum_eq_single y0]
  · congr
    funext i
    simp
  · intro y _hy hy
    exact (hy (Subsingleton.elim y y0)).elim
  · intro hy
    exact (hy (Finset.mem_univ y0)).elim

private lemma marginalizeOn_insert
    [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) {U : Finset (SWIGNode N)} {v : SWIGNode N}
    (hvU : v ∉ U) (hins : insert v U ⊆ M.observed)
    (hU : U ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    marginalizeOn M.observed (insert v U) hins q x =
      marginalizeOn M.observed U hU
        (fun x' => ∑ ω : swigΩ Ω v,
          q (overrideOn x' (singletonValuePt v ω))) x := by
  classical
  have hvObs : v ∈ M.observed := hins (Finset.mem_insert_self v U)
  have hInsert : insert v U = ({v} : Finset (SWIGNode N)) ∪ U := by
    ext w
    simp [Finset.mem_insert]
  have hDisj : Disjoint ({v} : Finset (SWIGNode N)) U := by
    rw [Finset.disjoint_left]
    intro w hwv hwU
    exact hvU (by simpa [Finset.mem_singleton.mp hwv] using hwU)
  have hUnion : ({v} : Finset (SWIGNode N)) ∪ U ⊆ M.observed := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwv | hwU
    · simpa [Finset.mem_singleton.mp hwv] using hvObs
    · exact hU hwU
  unfold marginalizeOn
  calc
    (∑ y : ValuesOn (insert v U) (swigΩ Ω),
        q (overrideOn x y))
        = ∑ y : ValuesOn (({v} : Finset (SWIGNode N)) ∪ U) (swigΩ Ω),
            q (overrideOn x y) := by
          refine Fintype.sum_equiv
            (valuesEquivOfEq (Ω := swigΩ Ω) hInsert).toEquiv _ _ ?_
          intro y
          congr
    _ = ∑ p : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω) ×
              ValuesOn U (swigΩ Ω),
            q (overrideOn x ((valuesUnionEquiv (Ω := Ω) hDisj).symm p)) := by
          refine Fintype.sum_equiv (valuesUnionEquiv (Ω := Ω) hDisj).toEquiv _ _ ?_
          intro y
          congr
          exact ((valuesUnionEquiv (Ω := Ω) hDisj).left_inv y).symm
    _ = ∑ p : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω) ×
              ValuesOn U (swigΩ Ω),
            q (overrideOn x (valuesUnionMk p.1 p.2)) := by
          rfl
    _ = ∑ yv : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω),
          ∑ yU : ValuesOn U (swigΩ Ω),
            q (overrideOn x (valuesUnionMk yv yU)) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ yU : ValuesOn U (swigΩ Ω),
          ∑ yv : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω),
            q (overrideOn x (valuesUnionMk yv yU)) := by
          simpa using (Finset.sum_comm
            (s := (Finset.univ :
              Finset (ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω))))
            (t := (Finset.univ : Finset (ValuesOn U (swigΩ Ω))))
            (f := fun yv yU => q (overrideOn x (valuesUnionMk yv yU))))
    _ = ∑ yU : ValuesOn U (swigΩ Ω),
          ∑ ω : swigΩ Ω v,
            q (overrideOn (overrideOn x yU) (singletonValuePt v ω)) := by
          refine Finset.sum_congr rfl ?_
          intro yU _hyU
          refine (Fintype.sum_equiv (singletonValuePtEquiv (Ω := Ω) v)
            (fun ω : swigΩ Ω v =>
              q (overrideOn (overrideOn x yU) (singletonValuePt v ω)))
            (fun yv : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω) =>
              q (overrideOn x (valuesUnionMk yv yU))) ?_).symm
          intro ω
          exact (congrArg q
            (overrideOn_union_singletonValuePt x yU ω)).symm

private lemma localConsistent_override_singleton_of_ne
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    {T : Finset (SWIGNode N)} (hT : T ⊆ M.observed)
    {v w : SWIGNode N} (hwT : w ∈ T) (hwv : w ≠ v)
    (hNoEdge : ¬ M.dag.edge v w)
    (x : ValuesOn M.observed (swigΩ Ω)) (ω : swigΩ Ω v)
    (ℓ : M.LatentValues) :
    M.localConsistent s
        (overrideOn x (singletonValuePt v ω))
        w (hT hwT) ℓ ↔
      M.localConsistent s x w (hT hwT) ℓ := by
  classical
  rw [localConsistent_iff_structFun_dispatch,
    localConsistent_iff_structFun_dispatch]
  have htarget :
      overrideOn x (singletonValuePt v ω) ⟨w, hT hwT⟩ =
        x ⟨w, hT hwT⟩ := by
    exact overrideOn_singleton_ne (hT hwT) hwv x ω
  have hparents :
      (fun p : {p // p ∈ M.dag.parents w} =>
          if huo : p.val ∈ M.unobserved then ℓ ⟨p.val, huo⟩
          else if hfix : p.val ∈ M.fixed then s ⟨p.val, hfix⟩
          else
            have hedge : M.dag.edge p.val w :=
              M.dag.mem_parents.mp p.property
            have hobs : p.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            (show swigΩ Ω p.val from
              overrideOn x (singletonValuePt v ω) ⟨p.val, hobs⟩))
        =
      (fun p : {p // p ∈ M.dag.parents w} =>
          if huo : p.val ∈ M.unobserved then ℓ ⟨p.val, huo⟩
          else if hfix : p.val ∈ M.fixed then s ⟨p.val, hfix⟩
          else
            have hedge : M.dag.edge p.val w :=
              M.dag.mem_parents.mp p.property
            have hobs : p.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            (show swigΩ Ω p.val from x ⟨p.val, hobs⟩)) := by
    funext p
    by_cases huo : p.val ∈ M.unobserved
    · simp [huo]
    · by_cases hfix : p.val ∈ M.fixed
      · simp [huo, hfix]
      · have hpv : p.val ≠ v := by
          intro hpv
          exact hNoEdge (hpv ▸ M.dag.mem_parents.mp p.property)
        simp [huo, hfix, overrideOn_singleton_ne _ hpv x ω]
  rw [hparents, htarget]

private noncomputable def localStructValue
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω)) (v : SWIGNode N)
    (hv : v ∈ M.observed) (ℓ : M.LatentValues) : swigΩ Ω v :=
  M.structFun ⟨v, hv⟩
    (fun p : {p // p ∈ M.dag.parents v} =>
      if huo : p.val ∈ M.unobserved then ℓ ⟨p.val, huo⟩
      else if hfix : p.val ∈ M.fixed then s ⟨p.val, hfix⟩
      else
        have hedge : M.dag.edge p.val v :=
          M.dag.mem_parents.mp p.property
        have hobs : p.val ∈ M.observed := by
          rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
          · rcases Finset.mem_union.mp h1 with hfx | hob
            · exact absurd hfx hfix
            · exact hob
          · exact absurd h2 huo
        (show swigΩ Ω p.val from x ⟨p.val, hobs⟩))

private lemma localConsistent_override_singleton_self_iff
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    {T : Finset (SWIGNode N)} (hT : T ⊆ M.observed)
    {v : SWIGNode N} (hvT : v ∈ T)
    (x : ValuesOn M.observed (swigΩ Ω)) (ω : swigΩ Ω v)
    (ℓ : M.LatentValues) :
    M.localConsistent s
        (overrideOn x (singletonValuePt v ω))
        v (hT hvT) ℓ ↔
      localStructValue M s x v (hT hvT) ℓ = ω := by
  classical
  rw [localConsistent_iff_structFun_dispatch]
  unfold localStructValue
  have htarget :
      overrideOn x (singletonValuePt v ω) ⟨v, hT hvT⟩ = ω := by
    exact overrideOn_singleton_self (hT hvT) x ω
  have hparents :
      (fun p : {p // p ∈ M.dag.parents v} =>
          if huo : p.val ∈ M.unobserved then ℓ ⟨p.val, huo⟩
          else if hfix : p.val ∈ M.fixed then s ⟨p.val, hfix⟩
          else
            have hedge : M.dag.edge p.val v :=
              M.dag.mem_parents.mp p.property
            have hobs : p.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            (show swigΩ Ω p.val from
              overrideOn x (singletonValuePt v ω) ⟨p.val, hobs⟩))
        =
      (fun p : {p // p ∈ M.dag.parents v} =>
          if huo : p.val ∈ M.unobserved then ℓ ⟨p.val, huo⟩
          else if hfix : p.val ∈ M.fixed then s ⟨p.val, hfix⟩
          else
            have hedge : M.dag.edge p.val v :=
              M.dag.mem_parents.mp p.property
            have hobs : p.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            (show swigΩ Ω p.val from x ⟨p.val, hobs⟩)) := by
    funext p
    by_cases huo : p.val ∈ M.unobserved
    · simp [huo]
    · by_cases hfix : p.val ∈ M.fixed
      · simp [huo, hfix]
      · have hpv : p.val ≠ v := by
          intro hpv
          exact M.dag.irrefl v (by
            simpa [hpv] using M.dag.mem_parents.mp p.property)
        simp [huo, hfix, overrideOn_singleton_ne _ hpv x ω]
  rw [hparents, htarget]

private lemma qLocalEvent_override_singleton_eq_inter
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    {T : Finset (SWIGNode N)} (hT : T ⊆ M.observed)
    {v : SWIGNode N} (hvT : v ∈ T)
    (hNoChild : ∀ w ∈ T, ¬ M.dag.edge v w)
    (x : ValuesOn M.observed (swigΩ Ω)) (ω : swigΩ Ω v) :
    {ℓ : M.LatentValues | ∀ w (hw : w ∈ T),
      M.localConsistent s
        (overrideOn x (singletonValuePt v ω))
        w (hT hw) ℓ} =
      {ℓ : M.LatentValues | ∀ w (hw : w ∈ T.erase v),
        M.localConsistent s x w (hT (Finset.mem_of_mem_erase hw)) ℓ} ∩
      {ℓ : M.LatentValues | localStructValue M s x v (hT hvT) ℓ = ω} := by
  classical
  ext ℓ
  constructor
  · intro hℓ
    constructor
    · intro w hw
      have hwT : w ∈ T := Finset.mem_of_mem_erase hw
      have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
      exact (localConsistent_override_singleton_of_ne M s hT hwT hwv
        (hNoChild w hwT) x ω ℓ).mp (hℓ w hwT)
    · exact (localConsistent_override_singleton_self_iff M s hT hvT x ω ℓ).mp
        (hℓ v hvT)
  · rintro ⟨hrest, hv⟩ w hwT
    by_cases hwv : w = v
    · subst w
      exact (localConsistent_override_singleton_self_iff M s hT hvT x ω ℓ).mpr hv
    · have hwerase : w ∈ T.erase v := Finset.mem_erase.mpr ⟨hwv, hwT⟩
      exact (localConsistent_override_singleton_of_ne M s hT hwT hwv
        (hNoChild w hwT) x ω ℓ).mpr (hrest w hwerase)

/-- Summing a local q-mass over one childless observed coordinate removes that
coordinate from the constrained set. -/
lemma qLocalMass_sum_point_eliminate
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (T : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    {v : SWIGNode N} (hvT : v ∈ T)
    (hNoChild : ∀ w ∈ T, ¬ M.dag.edge v w)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (∑ ω : swigΩ Ω v,
      M.qLocalMass s T hT
        (overrideOn x (singletonValuePt v ω))) =
      M.qLocalMass s (T.erase v)
        (fun _ hv => hT (Finset.mem_of_mem_erase hv)) x := by
  classical
  let Erest : Set M.LatentValues :=
    {ℓ | ∀ w (hw : w ∈ T.erase v),
      M.localConsistent s x w (hT (Finset.mem_of_mem_erase hw)) ℓ}
  let Fset : swigΩ Ω v → Set M.LatentValues :=
    fun ω => {ℓ | localStructValue M s x v (hT hvT) ℓ = ω}
  have hevent :
      ∀ ω : swigΩ Ω v,
        {ℓ : M.LatentValues | ∀ w (hw : w ∈ T),
          M.localConsistent s
            (overrideOn x (singletonValuePt v ω))
            w (hT hw) ℓ} = Erest ∩ Fset ω := by
    intro ω
    simpa [Erest, Fset] using
      qLocalEvent_override_singleton_eq_inter M s hT hvT hNoChild x ω
  have hdisj :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (swigΩ Ω v)))
        (fun ω => Erest ∩ Fset ω) := by
    intro ω₁ _ ω₂ _ hne
    change Disjoint (Erest ∩ Fset ω₁) (Erest ∩ Fset ω₂)
    rw [Set.disjoint_left]
    intro ℓ hℓ₁ hℓ₂
    exact hne (hℓ₁.2.symm.trans hℓ₂.2)
  have hmeas :
      ∀ ω ∈ (Finset.univ : Finset (swigΩ Ω v)),
        MeasurableSet (Erest ∩ Fset ω) := by
    intro ω _hω
    exact Set.Finite.measurableSet (Set.toFinite _)
  have hunion :
      (⋃ ω ∈ (Finset.univ : Finset (swigΩ Ω v)), Erest ∩ Fset ω) = Erest := by
    ext ℓ
    simp [Fset]
  simp only [causal_defs_simps]
  calc
    (∑ ω : swigΩ Ω v,
        M.latentProduct {ℓ : M.LatentValues | ∀ w (hw : w ∈ T),
          M.localConsistent s
            (overrideOn x (singletonValuePt v ω))
            w (hT hw) ℓ})
        =
      ∑ ω : swigΩ Ω v, M.latentProduct (Erest ∩ Fset ω) := by
        refine Finset.sum_congr rfl ?_
        intro ω _hω
        rw [hevent ω]
    _ = M.latentProduct (⋃ ω ∈ (Finset.univ : Finset (swigΩ Ω v)),
          Erest ∩ Fset ω) := by
        symm
        simpa using
          (MeasureTheory.measure_biUnion_finset
            (μ := M.latentProduct)
            (s := (Finset.univ : Finset (swigΩ Ω v)))
            (f := fun ω => Erest ∩ Fset ω) hdisj hmeas)
    _ = M.latentProduct Erest := by
        rw [hunion]

private lemma exists_sdiff_topoMax_noChild
    (M : Causalean.SCM N Ω)
    {T W : Finset (SWIGNode N)}
    (hne : (T \ W).Nonempty)
    (hclosed : ∀ v ∈ T, ∀ w ∈ W, M.dag.edge v w → v ∈ W) :
    ∃ v ∈ T \ W, ∀ w ∈ T, ¬ M.dag.edge v w := by
  classical
  obtain ⟨v, hvS, hvMax⟩ :=
    Finset.exists_max_image (T \ W) M.dag.topoOrder hne
  refine ⟨v, hvS, ?_⟩
  intro w hwT hvw
  have hvT : v ∈ T := (Finset.mem_sdiff.mp hvS).1
  have hvNotW : v ∉ W := (Finset.mem_sdiff.mp hvS).2
  by_cases hwW : w ∈ W
  · exact hvNotW (hclosed v hvT w hwW hvw)
  · have hwS : w ∈ T \ W := Finset.mem_sdiff.mpr ⟨hwT, hwW⟩
    have hle : M.dag.topoOrder w ≤ M.dag.topoOrder v := hvMax w hwS
    exact (not_lt_of_ge hle) (M.dag.topoOrder_lt v w hvw)

omit [Fintype N] in
private lemma erase_sdiff_eq_sdiff_erase
    {T W : Finset (SWIGNode N)} {v : SWIGNode N} :
    (T.erase v) \ W = (T \ W).erase v := by
  ext w
  simp [Finset.mem_sdiff, Finset.mem_erase, and_assoc]

/-- For [a set of observed nodes `T`](hyp:hT) and [a subset `W` of `T`](hyp:hWT) such that
[every parent, within `T`, of a node in `W` also lies in `W`](hyp:hclosed), [marginalizing the
local q-mass on `T` over the coordinates in `T \ W` yields the local q-mass on `W`](goal). -/
lemma qLocalMass_marginalize_ancestralClosed
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (T W : Finset (SWIGNode N)) (hT : T ⊆ M.observed) (hWT : W ⊆ T)
    (hclosed : ∀ v ∈ T, ∀ w ∈ W, M.dag.edge v w → v ∈ W)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    marginalizeOn M.observed (T \ W)
        (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1))
        (M.qLocalMass s T hT) x =
      M.qLocalMass s W (fun _ hv => hT (hWT hv)) x := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ (T : Finset (SWIGNode N)) (hT : T ⊆ M.observed) (hWT : W ⊆ T),
      (∀ v ∈ T, ∀ w ∈ W, M.dag.edge v w → v ∈ W) →
      ∀ x : ValuesOn M.observed (swigΩ Ω),
      (T \ W).card = n →
        marginalizeOn M.observed (T \ W)
            (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1))
            (M.qLocalMass s T hT) x =
          M.qLocalMass s W (fun _ hv => hT (hWT hv)) x
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hT hWT hclosed x hcard
      by_cases hempty : T \ W = ∅
      · have hTW : T ⊆ W := by
          intro v hvT
          by_contra hvW
          have hvS : v ∈ T \ W := Finset.mem_sdiff.mpr ⟨hvT, hvW⟩
          simp [hempty] at hvS
        have hEq : T = W := Finset.Subset.antisymm hTW hWT
        subst T
        simpa [Finset.sdiff_self] using
          (marginalizeOn_empty M (M.qLocalMass s W hT) x)
      · have hne : (T \ W).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨v, hvS, hNoChild⟩ :=
          exists_sdiff_topoMax_noChild M hne hclosed
        let U : Finset (SWIGNode N) := (T \ W).erase v
        have hvT : v ∈ T := (Finset.mem_sdiff.mp hvS).1
        have hvNotW : v ∉ W := (Finset.mem_sdiff.mp hvS).2
        have hvNotU : v ∉ U := by
          dsimp [U]
          simp
        have hS_eq : T \ W = insert v U := by
          dsimp [U]
          exact (Finset.insert_erase hvS).symm
        have hUobs : U ⊆ M.observed := by
          intro u hu
          exact hT ((Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hu)).1)
        have hInsobs : insert v U ⊆ M.observed := by
          intro u hu
          have huS : u ∈ T \ W := by
            simpa [hS_eq] using hu
          exact hT ((Finset.mem_sdiff.mp huS).1)
        let hTerase : T.erase v ⊆ M.observed :=
          fun _ hv => hT (Finset.mem_of_mem_erase hv)
        have hfun :
            (fun x' : ValuesOn M.observed (swigΩ Ω) =>
              ∑ ω : swigΩ Ω v,
                M.qLocalMass s T hT
                  (overrideOn x' (singletonValuePt v ω))) =
            (fun x' : ValuesOn M.observed (swigΩ Ω) =>
              M.qLocalMass s (T.erase v) hTerase x') := by
          funext x'
          simpa using
            (qLocalMass_sum_point_eliminate M s T hT hvT hNoChild x')
        have hEraseSdiff : (T.erase v) \ W = U := by
          dsimp [U]
          exact erase_sdiff_eq_sdiff_erase
        have hcard_lt : ((T.erase v) \ W).card < n := by
          rw [hEraseSdiff]
          dsimp [U]
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem hvS
        have hWTerase : W ⊆ T.erase v := by
          intro w hw
          refine Finset.mem_erase.mpr ⟨?_, hWT hw⟩
          intro hwv
          exact hvNotW (by simpa [hwv] using hw)
        have hclosedErase :
            ∀ a ∈ T.erase v, ∀ w ∈ W, M.dag.edge a w → a ∈ W := by
          intro a ha w hw haw
          exact hclosed a (Finset.mem_of_mem_erase ha) w hw haw
        calc
          marginalizeOn M.observed (T \ W)
              (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1))
              (M.qLocalMass s T hT) x
              =
            marginalizeOn M.observed (insert v U) hInsobs (M.qLocalMass s T hT) x := by
              exact marginalizeOn_congr_finset M hS_eq
                (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1))
                hInsobs (M.qLocalMass s T hT) x
          _ =
            marginalizeOn M.observed U hUobs
              (fun x' => ∑ ω : swigΩ Ω v,
                M.qLocalMass s T hT
                  (overrideOn x' (singletonValuePt v ω))) x := by
              exact marginalizeOn_insert M hvNotU hInsobs hUobs
                (M.qLocalMass s T hT) x
          _ =
            marginalizeOn M.observed U hUobs
              (M.qLocalMass s (T.erase v) hTerase) x := by
              rw [hfun]
          _ =
            marginalizeOn M.observed ((T.erase v) \ W)
              (fun _ hv => hTerase ((Finset.mem_sdiff.mp hv).1))
              (M.qLocalMass s (T.erase v) hTerase) x := by
              exact marginalizeOn_congr_finset M hEraseSdiff.symm
                hUobs
                (fun _ hv => hTerase ((Finset.mem_sdiff.mp hv).1))
                (M.qLocalMass s (T.erase v) hTerase) x
          _ = M.qLocalMass s W (fun _ hv => hT (hWT hv)) x := by
              have hIH := ih ((T.erase v) \ W).card hcard_lt
                (T.erase v) hTerase hWTerase hclosedErase x rfl
              simpa [hTerase] using hIH
  exact hP (T \ W).card T hT hWT hclosed x rfl

end Causalean.SCM
