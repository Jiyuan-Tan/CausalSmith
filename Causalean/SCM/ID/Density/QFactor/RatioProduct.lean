/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.GraphicalThms.DoGFormula
public import Causalean.SCM.Do.ObsMarkov
public import Causalean.SCM.ID.Density.CComponentDensity
public import Causalean.SCM.ID.Density.DoLawMarginal
public import Causalean.SCM.ID.Density.MechCFactor
public import Causalean.Graph.DSep.InduceTransport
public import Causalean.SCM.ID.Density.QFactor.PrefixLemmas

/-! # Prefix-ratio products for recursive q-factor recovery

This file shows how ratios of prefix q-mass products isolate a selected
component.  It culminates in district extraction and the correspondence between
`identifyMassRec` and the local q-mass recovered along an IDENTIFY certificate.
-/

public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM.ID

/-- In a product over an abstract pairwise-disjoint family, the prefix-ratio
step at a node of `S` cancels every factor except the `S` factor. -/
lemma prefixIn_qProduct_ratio_eq_component_ratio_of_family
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (s : M.FixedValues)
    (𝒞 : Finset (Finset (SWIGNode N))) (S : Finset (SWIGNode N))
    (hS𝒞 : S ∈ 𝒞)
    (hdisj : ∀ C ∈ 𝒞, C ≠ S → Disjoint C S)
    (i : Fin D.card) (hDobs : D ⊆ M.observed)
    (hiS : (H.nodesAt D i).val ∈ S)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (∏ C ∈ 𝒞,
        M.qLocalMass s (C ∩ H.prefixIn D (i.val + 1))
          (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
            (Finset.mem_of_mem_inter_right hv))) x) /
      (∏ C ∈ 𝒞,
        M.qLocalMass s (C ∩ H.prefixIn D i.val)
          (fun _ hv => hDobs (H.prefixIn_subset D i.val
            (Finset.mem_of_mem_inter_right hv))) x)
      =
    M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
          (Finset.mem_of_mem_inter_right hv))) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x := by
  classical
  let f₁ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ H.prefixIn D (i.val + 1))
      (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
        (Finset.mem_of_mem_inter_right hv))) x
  let f₀ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ H.prefixIn D i.val)
      (fun _ hv => hDobs (H.prefixIn_subset D i.val
        (Finset.mem_of_mem_inter_right hv))) x
  have hrest :
      ∏ C ∈ 𝒞 \ {S}, f₁ C =
        ∏ C ∈ 𝒞 \ {S}, f₀ C := by
    refine Finset.prod_congr rfl ?_
    intro C hC
    have hC𝒞 : C ∈ 𝒞 := (Finset.mem_sdiff.mp hC).1
    have hCne : C ≠ S := by
      intro h
      exact (Finset.mem_sdiff.mp hC).2 (by simp [h])
    simp [f₁, f₀,
      family_inter_prefixIn_succ_eq_of_ne H D hiS (hdisj C hC𝒞 hCne)]
  have hsplit₁ : (∏ C ∈ 𝒞, f₁ C) =
      f₁ S * ∏ C ∈ 𝒞 \ {S}, f₁ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₁
      (by intro h; exact False.elim (h hS𝒞))
  have hsplit₀ : (∏ C ∈ 𝒞, f₀ C) =
      f₀ S * ∏ C ∈ 𝒞 \ {S}, f₀ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₀
      (by intro h; exact False.elim (h hS𝒞))
  have hr0 : (∏ C ∈ 𝒞 \ {S}, f₀ C) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by
      intro C _hC
      exact M.qLocalMass_pos_of_positiveObs s hpos (C ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x)
  have hrtop : (∏ C ∈ 𝒞 \ {S}, f₀ C) ≠ ∞ := by
    exact Finset.prod_ne_top_of_ne_top _ f₀ (by
      intro C _hC
      exact qLocalMass_ne_top M s (C ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x)
  change (∏ C ∈ 𝒞, f₁ C) / (∏ C ∈ 𝒞, f₀ C) = f₁ S / f₀ S
  rw [hsplit₁, hsplit₀, hrest]
  exact ENNReal.div_mul_common hr0 hrtop

/-- Given [a finite structural causal model, graph, observed node set, fixed assignment, district,
prefix index, and observed assignment](hyp:N,Ω,M,H,D,s,S,i,x), if [the set is a district](hyp:hScomp),
[the node set is observed](hyp:hDobs), [the next prefix node lies in that district](hyp:hiS), and
[the product of all other district factors is nonzero](hyp:hrest0), then [the ratio of successive
full prefix products equals the corresponding ratio for that district](goal). -/
lemma prefixIn_qProduct_ratio_eq_component_ratio_of_ne_zero
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (i : Fin D.card) (hDobs : D ⊆ M.observed)
    (hiS : (H.nodesAt D i).val ∈ S)
    (x : ValuesOn M.observed (swigΩ Ω))
    (hrest0 :
      (∏ C ∈ M.toSWIGGraph.cComponentSet \ {S},
        M.qLocalMass s (C ∩ H.prefixIn D i.val)
          (fun _ hv => hDobs (H.prefixIn_subset D i.val
            (Finset.mem_of_mem_inter_right hv))) x) ≠ 0) :
    (∏ C ∈ M.toSWIGGraph.cComponentSet,
        M.qLocalMass s (C ∩ H.prefixIn D (i.val + 1))
          (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
            (Finset.mem_of_mem_inter_right hv))) x) /
      (∏ C ∈ M.toSWIGGraph.cComponentSet,
        M.qLocalMass s (C ∩ H.prefixIn D i.val)
          (fun _ hv => hDobs (H.prefixIn_subset D i.val
            (Finset.mem_of_mem_inter_right hv))) x)
      =
    M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
          (Finset.mem_of_mem_inter_right hv))) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x := by
  classical
  let f₁ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ H.prefixIn D (i.val + 1))
      (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
        (Finset.mem_of_mem_inter_right hv))) x
  let f₀ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ H.prefixIn D i.val)
      (fun _ hv => hDobs (H.prefixIn_subset D i.val
        (Finset.mem_of_mem_inter_right hv))) x
  have hrest :
      ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₁ C =
        ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C := by
    refine Finset.prod_congr rfl ?_
    intro C hC
    have hCcomp : C ∈ M.toSWIGGraph.cComponentSet := (Finset.mem_sdiff.mp hC).1
    have hCne : C ≠ S := by
      intro h
      exact (Finset.mem_sdiff.mp hC).2 (by simp [h])
    simp [f₁, f₀,
      cComponent_inter_prefixIn_succ_eq_of_ne M H D hScomp hCcomp hDobs hiS hCne]
  have hsplit₁ : (∏ C ∈ M.toSWIGGraph.cComponentSet, f₁ C) =
      f₁ S * ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₁ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₁
      (by intro h; exact False.elim (h hScomp))
  have hsplit₀ : (∏ C ∈ M.toSWIGGraph.cComponentSet, f₀ C) =
      f₀ S * ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₀
      (by intro h; exact False.elim (h hScomp))
  have hrtop : (∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C) ≠ ∞ := by
    exact Finset.prod_ne_top_of_ne_top _ f₀ (by
      intro C _hC
      exact qLocalMass_ne_top M s (C ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x)
  change (∏ C ∈ M.toSWIGGraph.cComponentSet, f₁ C) /
      (∏ C ∈ M.toSWIGGraph.cComponentSet, f₀ C) = f₁ S / f₀ S
  rw [hsplit₁, hsplit₀, hrest]
  exact ENNReal.div_mul_common hrest0 hrtop

/-- Nonzero-denominator variant of
`prefixIn_qProduct_ratio_eq_component_ratio_of_family`. -/
lemma prefixIn_qProduct_ratio_eq_component_ratio_of_family_of_ne_zero
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (s : M.FixedValues)
    (𝒞 : Finset (Finset (SWIGNode N))) (S : Finset (SWIGNode N))
    (hS𝒞 : S ∈ 𝒞)
    (hdisj : ∀ C ∈ 𝒞, C ≠ S → Disjoint C S)
    (i : Fin D.card) (hDobs : D ⊆ M.observed)
    (hiS : (H.nodesAt D i).val ∈ S)
    (x : ValuesOn M.observed (swigΩ Ω))
    (hrest0 :
      (∏ C ∈ 𝒞 \ {S},
        M.qLocalMass s (C ∩ H.prefixIn D i.val)
          (fun _ hv => hDobs (H.prefixIn_subset D i.val
            (Finset.mem_of_mem_inter_right hv))) x) ≠ 0) :
    (∏ C ∈ 𝒞,
        M.qLocalMass s (C ∩ H.prefixIn D (i.val + 1))
          (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
            (Finset.mem_of_mem_inter_right hv))) x) /
      (∏ C ∈ 𝒞,
        M.qLocalMass s (C ∩ H.prefixIn D i.val)
          (fun _ hv => hDobs (H.prefixIn_subset D i.val
            (Finset.mem_of_mem_inter_right hv))) x)
      =
    M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
          (Finset.mem_of_mem_inter_right hv))) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x := by
  classical
  let f₁ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ H.prefixIn D (i.val + 1))
      (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
        (Finset.mem_of_mem_inter_right hv))) x
  let f₀ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ H.prefixIn D i.val)
      (fun _ hv => hDobs (H.prefixIn_subset D i.val
        (Finset.mem_of_mem_inter_right hv))) x
  have hrest :
      ∏ C ∈ 𝒞 \ {S}, f₁ C =
        ∏ C ∈ 𝒞 \ {S}, f₀ C := by
    refine Finset.prod_congr rfl ?_
    intro C hC
    have hC𝒞 : C ∈ 𝒞 := (Finset.mem_sdiff.mp hC).1
    have hCne : C ≠ S := by
      intro h
      exact (Finset.mem_sdiff.mp hC).2 (by simp [h])
    simp [f₁, f₀,
      family_inter_prefixIn_succ_eq_of_ne H D hiS (hdisj C hC𝒞 hCne)]
  have hsplit₁ : (∏ C ∈ 𝒞, f₁ C) =
      f₁ S * ∏ C ∈ 𝒞 \ {S}, f₁ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₁
      (by intro h; exact False.elim (h hS𝒞))
  have hsplit₀ : (∏ C ∈ 𝒞, f₀ C) =
      f₀ S * ∏ C ∈ 𝒞 \ {S}, f₀ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₀
      (by intro h; exact False.elim (h hS𝒞))
  have hrtop : (∏ C ∈ 𝒞 \ {S}, f₀ C) ≠ ∞ := by
    exact Finset.prod_ne_top_of_ne_top _ f₀ (by
      intro C _hC
      exact qLocalMass_ne_top M s (C ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x)
  change (∏ C ∈ 𝒞, f₁ C) / (∏ C ∈ 𝒞, f₀ C) = f₁ S / f₀ S
  rw [hsplit₁, hsplit₀, hrest]
  exact ENNReal.div_mul_common hrest0 hrtop

private lemma component_qLocalMass_ratio_product_prefixIn
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed) (hSD : S ⊆ D)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x)
      = M.qLocalMass s S hS x := by
  classical
  let hPrefObs : ∀ k, S ∩ H.prefixIn D k ⊆ M.observed := fun k _ hv =>
    hS (Finset.mem_of_mem_inter_left hv)
  let a : ℕ → ENNReal := fun k =>
    M.qLocalMass s (S ∩ H.prefixIn D k) (hPrefObs k) x
  let T : Finset ℕ := (Finset.range D.card).filter fun k =>
    if hk : k < D.card then (H.nodesAt D ⟨k, hk⟩).val ∈ S else False
  have hreindex :
      (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
        a (i.val + 1) / a i.val)
        = ∏ k ∈ T, a (k + 1) / a k := by
    refine Finset.prod_bij (fun i _hi => i.val) ?_ ?_ ?_ ?_
    · intro i hi
      simp [T, i.isLt, Finset.mem_filter.mp hi]
    · intro i _hi j _hj hij
      exact Fin.ext hij
    · intro k hk
      simp [T] at hk
      have hklt : k < D.card := hk.1
      refine ⟨⟨k, hklt⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa [hklt] using hk.2⟩
    · intro i _hi
      rfl
  have hTsubset : T ⊆ Finset.range D.card := by
    intro k hk
    exact (Finset.mem_filter.mp hk).1
  have hne : ∀ k ≤ D.card, a k ≠ 0 := by
    intro k hk
    exact M.qLocalMass_pos_of_positiveObs s hpos (S ∩ H.prefixIn D k) (hPrefObs k) x
  have hfin : ∀ k ≤ D.card, a k ≠ ∞ := by
    intro k hk
    exact qLocalMass_ne_top M s (S ∩ H.prefixIn D k) (hPrefObs k) x
  have hconst : ∀ k < D.card, k ∉ T → a (k + 1) = a k := by
    intro k hk hnot
    have hnode_not :
        (H.nodesAt D ⟨k, hk⟩).val ∉ S := by
      intro hnode
      exact hnot (by simp [T, hk, hnode])
    dsimp [a]
    have hset :
        S ∩ H.prefixIn D (k + 1) = S ∩ H.prefixIn D k :=
      cComponent_inter_prefixIn_succ_eq_of_node_not_mem H D hnode_not
    unfold qLocalMass
    congr 1
    ext ℓ
    constructor
    · intro hℓ v hv
      have hv' : v ∈ S ∩ H.prefixIn D (k + 1) := by
        simpa [hset] using hv
      simpa using hℓ v hv'
    · intro hℓ v hv
      have hv' : v ∈ S ∩ H.prefixIn D k := by
        simpa [hset] using hv
      simpa using hℓ v hv'
  have htelescope :
      ∏ k ∈ T, a (k + 1) / a k = a D.card / a 0 :=
    prod_filter_div_telescope a D.card T hTsubset hne hfin hconst
  have htop : S ∩ H.prefixIn D D.card = S := by
    rw [prefixIn_card H D]
    exact Finset.inter_eq_left.mpr hSD
  have hzero : S ∩ H.prefixIn D 0 = ∅ := by
    rw [prefixIn_zero H D, Finset.inter_empty]
  calc
    (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x)
        = ∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
          a (i.val + 1) / a i.val := by rfl
    _ = ∏ k ∈ T, a (k + 1) / a k := hreindex
    _ = a D.card / a 0 := htelescope
    _ = M.qLocalMass s S hS x / 1 := by
          simp [a, htop, hzero]
    _ = M.qLocalMass s S hS x := by
          simp

/-- Given [a finite structural causal model, graph, node set, fixed assignment, district, and
observed assignment](hyp:N,Ω,M,H,D,s,S,x), if [the district is observed](hyp:hS), [it lies in the
node set](hyp:hSD), and [all of its prefix local masses are nonzero](hyp:hne), then [the product of
its successive prefix-mass ratios equals its full local mass](goal). -/
lemma component_qLocalMass_ratio_product_prefixIn_of_ne_zero
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed) (hSD : S ⊆ D)
    (x : ValuesOn M.observed (swigΩ Ω))
    (hne : ∀ k ≤ D.card,
      M.qLocalMass s (S ∩ H.prefixIn D k)
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x ≠ 0) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x)
      = M.qLocalMass s S hS x := by
  classical
  let hPrefObs : ∀ k, S ∩ H.prefixIn D k ⊆ M.observed := fun k _ hv =>
    hS (Finset.mem_of_mem_inter_left hv)
  let a : ℕ → ENNReal := fun k =>
    M.qLocalMass s (S ∩ H.prefixIn D k) (hPrefObs k) x
  let T : Finset ℕ := (Finset.range D.card).filter fun k =>
    if hk : k < D.card then (H.nodesAt D ⟨k, hk⟩).val ∈ S else False
  have hreindex :
      (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
        a (i.val + 1) / a i.val)
        = ∏ k ∈ T, a (k + 1) / a k := by
    refine Finset.prod_bij (fun i _hi => i.val) ?_ ?_ ?_ ?_
    · intro i hi
      simp [T, i.isLt, Finset.mem_filter.mp hi]
    · intro i _hi j _hj hij
      exact Fin.ext hij
    · intro k hk
      simp [T] at hk
      have hklt : k < D.card := hk.1
      refine ⟨⟨k, hklt⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa [hklt] using hk.2⟩
    · intro i _hi
      rfl
  have hTsubset : T ⊆ Finset.range D.card := by
    intro k hk
    exact (Finset.mem_filter.mp hk).1
  have hne' : ∀ k ≤ D.card, a k ≠ 0 := by
    intro k hk
    exact hne k hk
  have hfin : ∀ k ≤ D.card, a k ≠ ∞ := by
    intro k hk
    exact qLocalMass_ne_top M s (S ∩ H.prefixIn D k) (hPrefObs k) x
  have hconst : ∀ k < D.card, k ∉ T → a (k + 1) = a k := by
    intro k hk hnot
    have hnode_not :
        (H.nodesAt D ⟨k, hk⟩).val ∉ S := by
      intro hnode
      exact hnot (by simp [T, hk, hnode])
    dsimp [a]
    have hset :
        S ∩ H.prefixIn D (k + 1) = S ∩ H.prefixIn D k :=
      cComponent_inter_prefixIn_succ_eq_of_node_not_mem H D hnode_not
    unfold qLocalMass
    congr 1
    ext ℓ
    constructor
    · intro hℓ v hv
      have hv' : v ∈ S ∩ H.prefixIn D (k + 1) := by
        simpa [hset] using hv
      simpa using hℓ v hv'
    · intro hℓ v hv
      have hv' : v ∈ S ∩ H.prefixIn D k := by
        simpa [hset] using hv
      simpa using hℓ v hv'
  have htelescope :
      ∏ k ∈ T, a (k + 1) / a k = a D.card / a 0 :=
    prod_filter_div_telescope a D.card T hTsubset hne' hfin hconst
  have htop : S ∩ H.prefixIn D D.card = S := by
    rw [prefixIn_card H D]
    exact Finset.inter_eq_left.mpr hSD
  have hzero : S ∩ H.prefixIn D 0 = ∅ := by
    rw [prefixIn_zero H D, Finset.inter_empty]
  calc
    (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x)
        = ∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
          a (i.val + 1) / a i.val := by rfl
    _ = ∏ k ∈ T, a (k + 1) / a k := hreindex
    _ = a D.card / a 0 := htelescope
    _ = M.qLocalMass s S hS x / 1 := by
          simp [a, htop, hzero]
    _ = M.qLocalMass s S hS x := by
          simp

/-- Given [a finite structural causal model, fixed assignment, ancestral set, and induced
district](hyp:N,Ω,M,s,A,C'), if [the ancestral set is observed](hyp:hA), [the set is a district of
the induced graph](hyp:hC'), and [the observational kernel has positive mass](hyp:hpos), then for
[an observed assignment](hyp:x), [extracting the district from the ancestral local mass recovers
that district's local mass](goal). -/
lemma extractDistrict_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (A C' : Finset (SWIGNode N)) (hA : A ⊆ M.observed)
    (hC' : C' ∈ (M.toSWIGGraph.induce A).cComponentSet)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    extractDistrict M.observed (M.toSWIGGraph.induce A) A C' hA
        (M.qLocalMass s A hA) x =
      M.qLocalMass s C'
        (fun _ hv =>
          hA (by
            have hHobs :
                (M.toSWIGGraph.induce A).observed = A := by
              simp [SWIGGraph.induce, Finset.inter_eq_left.mpr hA]
            exact hHobs ▸
              (M.toSWIGGraph.induce A).cComponentSet_subset_observed C' hC' hv)) x := by
  classical
  let H := M.toSWIGGraph.induce A
  have hHobs : H.observed = A := by
    simp [H, SWIGGraph.induce, Finset.inter_eq_left.mpr hA]
  have hCobs : C' ⊆ M.observed := by
    intro v hv
    exact hA (hHobs ▸ H.cComponentSet_subset_observed C' hC' hv)
  have hCA : C' ⊆ A := by
    intro v hv
    exact hHobs ▸ H.cComponentSet_subset_observed C' hC' hv
  have hdisj :
      (↑H.cComponentSet : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint U U') := by
    intro U hU V hV hne
    exact H.cComponentSet_pairwise_disjoint hU hV hne
  have hmarg : ∀ k,
      marginalizeOn M.observed (A \ H.prefixIn A k)
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1))
          (M.qLocalMass s A hA) x =
        M.qLocalMass s (H.prefixIn A k)
          (fun _ hv => hA (H.prefixIn_subset A k hv)) x := by
    intro k
    simpa [H] using
      M.qLocalMass_marginalize_ancestralClosed s A (H.prefixIn A k) hA
        (H.prefixIn_subset A k)
        (prefixIn_parent_closed_induce_observed M A hA k) x
  have hprod : ∀ k,
      M.qLocalMass s (H.prefixIn A k)
          (fun _ hv => hA (H.prefixIn_subset A k hv)) x =
        ∏ C ∈ H.cComponentSet,
          M.qLocalMass s (C ∩ H.prefixIn A k)
            (fun _ hv => hA (H.prefixIn_subset A k
              (Finset.mem_of_mem_inter_right hv))) x := by
    intro k
    simpa [H] using qLocalMass_prefixIn_eq_prod_induce_components M s A hA k x
  unfold SCM.extractDistrict
  calc
    (∏ i ∈ Finset.univ.filter
        (fun i : Fin A.card => (H.nodesAt A i).val ∈ C'),
      marginalizeOn M.observed (A \ H.prefixIn A (i.val + 1))
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1))
          (M.qLocalMass s A hA) x /
        marginalizeOn M.observed (A \ H.prefixIn A i.val)
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1))
          (M.qLocalMass s A hA) x)
        =
      ∏ i ∈ Finset.univ.filter
          (fun i : Fin A.card => (H.nodesAt A i).val ∈ C'),
        (∏ C ∈ H.cComponentSet,
          M.qLocalMass s (C ∩ H.prefixIn A (i.val + 1))
            (fun _ hv => hA (H.prefixIn_subset A (i.val + 1)
              (Finset.mem_of_mem_inter_right hv))) x) /
          (∏ C ∈ H.cComponentSet,
            M.qLocalMass s (C ∩ H.prefixIn A i.val)
              (fun _ hv => hA (H.prefixIn_subset A i.val
                (Finset.mem_of_mem_inter_right hv))) x) := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          rw [hmarg (i.val + 1), hmarg i.val, hprod (i.val + 1), hprod i.val]
    _ =
      ∏ i ∈ Finset.univ.filter
          (fun i : Fin A.card => (H.nodesAt A i).val ∈ C'),
        M.qLocalMass s (C' ∩ H.prefixIn A (i.val + 1))
          (fun _ hv => hA (H.prefixIn_subset A (i.val + 1)
            (Finset.mem_of_mem_inter_right hv))) x /
          M.qLocalMass s (C' ∩ H.prefixIn A i.val)
            (fun _ hv => hA (H.prefixIn_subset A i.val
              (Finset.mem_of_mem_inter_right hv))) x := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          have hiC : (H.nodesAt A i).val ∈ C' := (Finset.mem_filter.mp hi).2
          exact prefixIn_qProduct_ratio_eq_component_ratio_of_family
            M H A s H.cComponentSet C' hC'
              (fun C hC hne => hdisj hC hC' hne) i hA hiC hpos x
    _ =
      M.qLocalMass s C' hCobs x := by
          simpa using
            component_qLocalMass_ratio_product_prefixIn
              M H A s C' hCobs hCA hpos x
    _ =
      M.qLocalMass s C'
        (fun _ hv =>
          hA (by
            have hHobs' :
                (M.toSWIGGraph.induce A).observed = A := by
              simp [SWIGGraph.induce, Finset.inter_eq_left.mpr hA]
            exact hHobs' ▸
              (M.toSWIGGraph.induce A).cComponentSet_subset_observed C' hC' hv)) x := by
          rfl

/-- The target set of a recursive c-factor reachability certificate is contained
in the source set. -/
theorem CFactorReachableRec.target_subset
    {G : SWIGGraph N} {T C : Finset (SWIGNode N)}
    (h : CFactorReachableRec G T C) : C ⊆ T := by
  cases h with
  | base _ hCT _ => exact hCT
  | step _ hCT _ _ _ => exact hCT

/-- The local q-mass of an observed variable set does not depend on which proof
establishes that the set is observed. -/
lemma qLocalMass_obsProof_irrel
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (T : Finset (SWIGNode N)) (hT hT' : T ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s T hT x = M.qLocalMass s T hT' x := by
  unfold SCM.qLocalMass
  congr 1

/-- For [a finite structural causal model with finite measurable node-value spaces](hyp:N,Ω,M),
[a fixed-node assignment](hyp:s), [positive observational atom masses](hyp:hpos), [source and
target districts](hyp:T,C), [evidence that the source is observed](hyp:hT), [a recursive
c-factor reachability certificate from source to target](hyp:hReach), and [an observed
realization](hyp:x), [the observational IDENTIFY recursion recovers the target district's local
q-mass from the source district's local q-mass](goal).

The obs-side IDENTIFY recursion recovers the local q-mass of the target
district from the local q-mass of any recursively reachable source district. -/
theorem identifyMassRec_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    (T C : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (hReach : CFactorReachableRec M.toSWIGGraph T C)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    identifyMassRec M.observed M.toSWIGGraph T C hT (M.qLocalMass s T hT) x =
      M.qLocalMass s C (fun _ hv => hT (hReach.target_subset hv)) x := by
  classical
  induction hReach generalizing x with
  | base hne hCT hproject =>
      rename_i T₀ C₀
      rw [SCM.identifyMassRec_base M M.toSWIGGraph T₀ C₀ hT
        (M.qLocalMass s T₀ hT) hproject]
      have hclosed :
          ∀ v ∈ T₀, ∀ w ∈ C₀, M.dag.edge v w → v ∈ C₀ := by
        have hclosedA :=
          inducedAncestral_parent_closed M.toSWIGGraph
            (T := T₀) (C := C₀) (by simpa using hT)
        intro v hvT w hwC hEdge
        have hwA : w ∈ inducedAncestral M.toSWIGGraph T₀ C₀ := by
          simpa [hproject] using hwC
        have hvA := hclosedA v hvT w hwA hEdge
        simpa [hproject] using hvA
      exact M.qLocalMass_marginalize_ancestralClosed s T₀ C₀ hT hCT hclosed x
  | step hne hCT hnotC hnotT hrec ih =>
      rename_i T₀ C₀
      let A := inducedAncestral M.toSWIGGraph T₀ C₀
      let C₁ := containingCComponent (M.toSWIGGraph.induce A) C₀
      let hA : A ⊆ M.observed := fun _ hv =>
        hT (inducedAncestral_subset_left M.toSWIGGraph T₀ C₀ hv)
      let hC₁obs : C₁ ⊆ M.observed := fun _ hv =>
        hT (inducedAncestral_subset_left M.toSWIGGraph T₀ C₀
          (containingCComponent_induce_subset M.toSWIGGraph A C₀ hv))
      have hCobs : C₀ ⊆ M.toSWIGGraph.observed := by
        intro v hv
        simpa using hT (hCT hv)
      have hCA : C₀ ⊆ A :=
        subset_inducedAncestral M.toSWIGGraph hCT hCobs
      have hC₁mem : C₁ ∈ (M.toSWIGGraph.induce A).cComponentSet := by
        simp only [C₁, containingCComponent, dif_pos hne, SWIGGraph.cComponentSet]
        have hchooseA : hne.choose ∈ A := hCA hne.choose_spec
        have hchooseObs : hne.choose ∈ M.toSWIGGraph.observed :=
          hCobs hne.choose_spec
        have hchooseInd :
            hne.choose ∈ (M.toSWIGGraph.induce A).observed := by
          simp [SWIGGraph.induce, hchooseA, hchooseObs]
        exact Finset.mem_image.mpr ⟨hne.choose, hchooseInd, rfl⟩
      have hmarg :
          marginalizeOn M.observed (T₀ \ A)
              (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1))
              (M.qLocalMass s T₀ hT) =
            M.qLocalMass s A hA := by
        funext y
        have hclosedA :
            ∀ v ∈ T₀, ∀ w ∈ A, M.dag.edge v w → v ∈ A := by
          simpa [A] using
            inducedAncestral_parent_closed M.toSWIGGraph
              (T := T₀) (C := C₀) (by simpa using hT)
        exact M.qLocalMass_marginalize_ancestralClosed s T₀ A hT
          (inducedAncestral_subset_left M.toSWIGGraph T₀ C₀) hclosedA y
      have hextract :
          extractDistrict M.observed (M.toSWIGGraph.induce A) A C₁ hA
              (M.qLocalMass s A hA) =
            M.qLocalMass s C₁ hC₁obs := by
        funext y
        calc
          extractDistrict M.observed (M.toSWIGGraph.induce A) A C₁ hA
              (M.qLocalMass s A hA) y
              = M.qLocalMass s C₁
                  (fun _ hv =>
                    hA (by
                      have hHobs :
                          (M.toSWIGGraph.induce A).observed = A := by
                        simp [SWIGGraph.induce, Finset.inter_eq_left.mpr hA]
                      exact hHobs ▸
                        (M.toSWIGGraph.induce A).cComponentSet_subset_observed
                          C₁ hC₁mem hv)) y := by
                exact extractDistrict_qLocalMass M s A C₁ hA hC₁mem hpos y
          _ = M.qLocalMass s C₁ hC₁obs y := by
                exact qLocalMass_obsProof_irrel M s C₁ _ _ y
      rw [SCM.identifyMassRec_step M M.toSWIGGraph T₀ C₀ hT
        (M.qLocalMass s T₀ hT) hnotC hnotT]
      change
        identifyMassRec M.observed M.toSWIGGraph C₁ C₀ hC₁obs
          (extractDistrict M.observed (M.toSWIGGraph.induce A) A C₁ hA
            (marginalizeOn M.observed (T₀ \ A)
              (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1))
              (M.qLocalMass s T₀ hT))) x = _
      rw [hmarg, hextract]
      calc
        identifyMassRec M.observed M.toSWIGGraph C₁ C₀ hC₁obs
            (M.qLocalMass s C₁ hC₁obs) x
            = M.qLocalMass s C₀
                (fun _ hv => hC₁obs (hrec.target_subset hv)) x := by
              exact ih hC₁obs x
        _ = M.qLocalMass s C₀
              (fun _ hv =>
                hT ((CFactorReachableRec.step hne hCT hnotC hnotT hrec).target_subset hv)) x := by
              exact qLocalMass_obsProof_irrel M s C₀ _ _ x


end SCM.ID
end Causalean
