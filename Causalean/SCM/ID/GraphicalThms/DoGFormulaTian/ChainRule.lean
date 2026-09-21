/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.GraphicalThms.DoGFormula
public import Causalean.SCM.Do.ObsMarkov
public import Causalean.SCM.Factored.ObsChainKernel
public import Causalean.SCM.ID.Density.QFactor
public import Causalean.SCM.ID.Density.DoLawMarginal
public import Causalean.SCM.ID.GraphicalThms.NonAncestorKernelTransport
public import Causalean.Graph.DSep.InduceTransport
public import Causalean.SCM.ID.GraphicalThms.DoGFormulaTian.Prefix

/-! # Measure-level Tian chain rule and c-factorization

This file proves that a dominated finite law has density
`tianDensityProduct`, then regroups that product into district densities under
the global Markov property.  The results are measure-theoretic and do not yet
specialize the law to an SCM intervention.
-/

public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM.ID

/-- Prefix-level Radon--Nikodym chain rule for Tian's arbitrary-measure
conditional density product. -/
lemma measure_prefixIn_rnDeriv_eq_tianPrefixDensityProductInPrefix
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    [StandardBorelSpace (ValuesOn D (swigΩ Ω))]
    [MeasureTheory.IsProbabilityMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (hdom : μ ≪ Causalean.SCM.jointRef ref D) :
    ∀ (k : ℕ) (_hk : k ≤ D.card),
      (μ.map (valuesProjection (H.prefixIn_subset D k))).rnDeriv
          (Causalean.SCM.jointRef ref (H.prefixIn D k))
        =ᵐ[Causalean.SCM.jointRef ref (H.prefixIn D k)]
          tianPrefixDensityProductInPrefix H D μ ref k := by
  intro k
  induction k with
  | zero =>
      intro _hk
      have hsub : Subsingleton (ValuesOn (H.prefixIn D 0) (swigΩ Ω)) :=
        ⟨fun a b => funext fun i =>
          absurd (prefixIn_zero H D ▸ i.property) (Finset.notMem_empty i.val)⟩
      have heq :
          μ.map (valuesProjection (H.prefixIn_subset D 0))
            = Causalean.SCM.jointRef ref (H.prefixIn D 0) := by
        refine MeasureTheory.Measure.ext fun A _ => ?_
        rcases Set.eq_empty_or_nonempty A with rfl | hA
        · simp
        · obtain ⟨a, ha⟩ := hA
          have hAuniv : A = Set.univ :=
            Set.eq_univ_of_forall fun x => (hsub.elim x a) ▸ ha
          subst hAuniv
          rw [MeasureTheory.Measure.map_apply
            (measurable_valuesProjection (H.prefixIn_subset D 0)) MeasurableSet.univ]
          simp only [Set.preimage_univ]
          rw [MeasureTheory.measure_univ, Causalean.SCM.jointRef,
            MeasureTheory.Measure.pi_univ]
          symm
          apply Finset.prod_eq_one
          intro i hi
          have : i.val ∈ (∅ : Finset (SWIGNode N)) := by
            simpa [prefixIn_zero H D] using i.property
          simp at this
      rw [heq]
      have h1 :
          tianPrefixDensityProductInPrefix H D μ ref 0 =
            (fun _ => (1 : ENNReal)) := rfl
      rw [h1]
      exact MeasureTheory.Measure.rnDeriv_self _
  | succ k ih =>
      intro hk
      classical
      have hkc : k < D.card := Nat.lt_of_succ_le hk
      have hkprev : k ≤ D.card := Nat.le_of_succ_le hk
      let node : SWIGNode N := (H.nodesAt D ⟨k, hkc⟩).val
      let A : Finset (SWIGNode N) := H.prefixIn D k
      let B : Finset (SWIGNode N) := ({node} : Finset (SWIGNode N))
      let νk : MeasureTheory.Measure (ValuesOn A (swigΩ Ω)) :=
        Causalean.SCM.jointRef ref A
      let ρ : MeasureTheory.Measure (ValuesOn B (swigΩ Ω)) :=
        Causalean.SCM.jointRef ref B
      let prefixMap : ValuesOn D (swigΩ Ω) → ValuesOn A (swigΩ Ω) :=
        valuesProjection (H.prefixIn_subset D k)
      let nodeMap : ValuesOn D (swigΩ Ω) → ValuesOn B (swigΩ Ω) :=
        valuesProjection
          (show B ⊆ D from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            exact hv ▸ (H.nodesAt D ⟨k, hkc⟩).property)
      let succMap : ValuesOn D (swigΩ Ω) →
          ValuesOn (H.prefixIn D (k + 1)) (swigΩ Ω) :=
        valuesProjection (H.prefixIn_subset D (k + 1))
      let chain : MeasureTheory.Measure (ValuesOn A (swigΩ Ω)) :=
        μ.map prefixMap
      let stepK : ProbabilityTheory.Kernel (ValuesOn A (swigΩ Ω)) (ValuesOn B (swigΩ Ω)) :=
        ProbabilityTheory.condDistrib nodeMap prefixMap μ
      let ext : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) →
          ValuesOn (H.prefixIn D (k + 1)) (swigΩ Ω) :=
        extendTianPrefix (Ω := Ω) H D hkc
      have hcomp_ext : ext ∘ (fun x : ValuesOn D (swigΩ Ω) => (prefixMap x, nodeMap x))
          = succMap := by
        funext x
        ext a
        by_cases hmem : a.val ∈ H.prefixIn D k
        · simp [ext, prefixMap, nodeMap, succMap, A, B, node, extendTianPrefix,
            coe_valuesEquivOfEq, valuesProjection, valuesUnionMk, hmem]
        · simp [ext, prefixMap, nodeMap, succMap, A, B, node, extendTianPrefix,
            coe_valuesEquivOfEq, valuesProjection, valuesUnionMk, hmem]
      have hchainSucc :
          μ.map succMap = (chain ⊗ₘ stepK).map ext := by
        have hpair :
            chain ⊗ₘ stepK
              = μ.map (fun x : ValuesOn D (swigΩ Ω) => (prefixMap x, nodeMap x)) := by
          dsimp [chain, stepK]
          exact ProbabilityTheory.compProd_map_condDistrib
            ((measurable_valuesProjection (Ω' := swigΩ Ω)
              (show B ⊆ D from by
                intro v hv
                rw [Finset.mem_singleton] at hv
                exact hv ▸ (H.nodesAt D ⟨k, hkc⟩).property)).aemeasurable)
        rw [hpair]
        rw [MeasureTheory.Measure.map_map]
        · rw [hcomp_ext]
        · exact measurable_extendTianPrefix (Ω := Ω) H D hkc
        · exact (measurable_valuesProjection (Ω' := swigΩ Ω) (H.prefixIn_subset D k)).prod
            (measurable_valuesProjection (Ω' := swigΩ Ω)
              (show B ⊆ D from by
                intro v hv
                rw [Finset.mem_singleton] at hv
                exact hv ▸ (H.nodesAt D ⟨k, hkc⟩).property))
      have hrefSucc :
          Causalean.SCM.jointRef ref (H.prefixIn D (k + 1))
            = (νk.prod ρ).map ext := by
        dsimp [νk, ρ, A, B, node, ext]
        exact (jointRef_extendTianPrefix H D ref hkc).symm
      have hext_emb : MeasurableEmbedding ext := by
        dsimp [ext, A, B, node]
        unfold extendTianPrefix
        refine
          (valuesEquivOfEq (Ω := swigΩ Ω)
            (prefixIn_succ H D hkc).symm).measurableEmbedding.comp ?_
        change MeasurableEmbedding
          (fun p : ValuesOn (H.prefixIn D k) (swigΩ Ω) ×
              ValuesOn ({(H.nodesAt D ⟨k, hkc⟩).val} : Finset (SWIGNode N)) (swigΩ Ω) =>
            valuesUnionMk p.1 p.2)
        have hfun :
            (fun p : ValuesOn (H.prefixIn D k) (swigΩ Ω) ×
                ValuesOn ({(H.nodesAt D ⟨k, hkc⟩).val} : Finset (SWIGNode N)) (swigΩ Ω) =>
              valuesUnionMk p.1 p.2)
              =
            ((valuesUnionEquiv (Ω := Ω)
              (prefixIn_disjoint_singleton_next H D hkc)).symm) := by
          rfl
        rw [hfun]
        exact ((valuesUnionEquiv (Ω := Ω)
          (prefixIn_disjoint_singleton_next H D hkc)).symm.measurableEmbedding)
      have hcore :
          (chain ⊗ₘ stepK).rnDeriv (νk.prod ρ)
            =ᵐ[νk.prod ρ]
              fun p =>
                tianPrefixDensityProductInPrefix H D μ ref k p.1 *
                  (stepK p.1).rnDeriv ρ p.2 := by
        have hchain_ac : chain ≪ νk := by
          dsimp [chain, νk, prefixMap, A]
          exact measure_map_prefixIn_absolutelyContinuous_jointRef H D μ ref hdom k
        have hsucc_ac :
            μ.map succMap ≪ Causalean.SCM.jointRef ref (H.prefixIn D (k + 1)) := by
          dsimp [succMap]
          exact measure_map_prefixIn_absolutelyContinuous_jointRef H D μ ref hdom (k + 1)
        have hjoint_map : (chain ⊗ₘ stepK).map ext ≪ (νk.prod ρ).map ext := by
          simpa [hchainSucc, hrefSucc] using hsucc_ac
        have hjoint : chain ⊗ₘ stepK ≪ νk.prod ρ :=
          Causalean.SCM.absolutelyContinuous_of_map_measurableEmbedding hext_emb hjoint_map
        -- In this finite/discrete setting `ρ` is finite, so `Kernel.const _ ρ` is a
        -- finite kernel and fibre domination follows from joint domination.
        have hfiber : ∀ᵐ a ∂chain, stepK a ≪ ρ := by
          have hjoint_const :
              chain ⊗ₘ stepK ≪ νk ⊗ₘ ProbabilityTheory.Kernel.const _ ρ := by
            rwa [MeasureTheory.Measure.compProd_const]
          filter_upwards [hjoint_const.kernel_of_compProd] with a ha
          simpa [ProbabilityTheory.Kernel.const_apply] using ha
        have hfiber_meas :
            AEMeasurable
              (fun p : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
                (stepK p.1).rnDeriv ρ p.2)
              (νk.prod ρ) :=
          Causalean.SCM.aemeasurable_fiber_rnDeriv_of_finite (νk.prod ρ) ρ stepK
        exact MeasureTheory.rnDeriv_compProd_prod_sigmaFinite
          chain νk ρ stepK (tianPrefixDensityProductInPrefix H D μ ref k)
          hchain_ac hfiber hfiber_meas (ih hkprev)
      rw [hchainSucc, hrefSucc, Filter.EventuallyEq, hext_emb.ae_map_iff]
      filter_upwards [hext_emb.rnDeriv_map (chain ⊗ₘ stepK) (νk.prod ρ),
        hcore] with p hmap hp
      rw [hmap, hp]
      dsimp [ext, stepK, ρ, B, node]
      have hpair := valuesUnionEquiv_extendTianPrefix H D hkc p
      have hproj_ext :
          valuesProjection (prefixIn_mono H D (Nat.le_succ k))
              (extendTianPrefix (Ω := Ω) H D hkc p) = p.1 := by
        funext i
        have hi := congrArg (fun q => q.1 i) hpair
        simpa [valuesUnionEquiv, valuesProjection, coe_valuesEquivOfEq] using hi
      have hnode_ext :
          valuesProjection
              (show ({(H.nodesAt D ⟨k, hkc⟩).val} : Finset (SWIGNode N)) ⊆
                  H.prefixIn D (k + 1) from by
                intro v hv
                rw [Finset.mem_singleton] at hv
                subst hv
                rw [nodesAt_mem_prefixIn_iff H D (k + 1) ⟨k, hkc⟩]
                exact Nat.lt_succ_self k)
              (extendTianPrefix (Ω := Ω) H D hkc p) = p.2 := by
        funext i
        have hi := congrArg (fun q => q.2 i) hpair
        simpa [valuesUnionEquiv, valuesProjection, coe_valuesEquivOfEq] using hi
      rw [tianPrefixDensityProductInPrefix]
      simp [hkc, hproj_ext, hnode_ext, A, B, node, prefixMap, nodeMap]

/-- The density of any dominated finite law on a finite coordinate set factors
as the product of its one-coordinate conditional densities along the chosen
topological order.  The conditional density at each coordinate is computed from
Mathlib's regular conditional distribution given the preceding prefix.

This is the measure-only analogue of `SCM.obsDensity_eq_qFactorDensityProduct`.
The proof should induct over the prefixes of `D`: split the successor reference
as a product of the prefix reference and the next-node reference, rewrite the
successor law as the composition product of the prefix marginal and the
`condDistrib` kernel, and apply the σ-finite composition-product
Radon--Nikodym derivative lemma already isolated in
`Causalean.Mathlib.MeasureTheory.RnDerivCompProdSigmaFinite`. -/
theorem rnDeriv_eq_tianDensityProduct
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    [StandardBorelSpace (ValuesOn D (swigΩ Ω))]
    [MeasureTheory.IsProbabilityMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (hdom : μ ≪ Causalean.SCM.jointRef ref D) :
    μ.rnDeriv (Causalean.SCM.jointRef ref D)
      =ᵐ[Causalean.SCM.jointRef ref D] tianDensityProduct H D μ ref := by
  classical
  set e := valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_card H D) with he
  have hf : MeasurableEmbedding
      (e : ValuesOn (H.prefixIn D D.card) (swigΩ Ω) →
        ValuesOn D (swigΩ Ω)) := e.measurableEmbedding
  have hμe :
      (μ.map e.symm).map e = μ := by
    rw [MeasureTheory.Measure.map_map e.measurable e.symm.measurable]
    have hcomp : (e : ValuesOn (H.prefixIn D D.card) (swigΩ Ω) →
        ValuesOn D (swigΩ Ω)) ∘ e.symm = id := by
      funext x
      exact e.right_inv x
    rw [hcomp, MeasureTheory.Measure.map_id]
  have href :
      (Causalean.SCM.jointRef ref (H.prefixIn D D.card)).map e
        = Causalean.SCM.jointRef ref D := by
    rw [Causalean.SCM.jointRef, Causalean.SCM.jointRef,
      Causalean.SCM.map_pi_valuesEquivOfEq]
  have hprefixMap :
      valuesProjection (H.prefixIn_subset D D.card)
        =
      (e.symm : ValuesOn D (swigΩ Ω) → ValuesOn (H.prefixIn D D.card) (swigΩ Ω)) := by
    funext x i
    rfl
  have hprefix :
      (μ.map e.symm).rnDeriv (Causalean.SCM.jointRef ref (H.prefixIn D D.card))
        =ᵐ[Causalean.SCM.jointRef ref (H.prefixIn D D.card)]
          tianPrefixDensityProductInPrefix H D μ ref D.card := by
    simpa [hprefixMap] using
      (measure_prefixIn_rnDeriv_eq_tianPrefixDensityProductInPrefix
        H D μ ref hdom D.card (le_refl _))
  have hmap :
      μ.rnDeriv (Causalean.SCM.jointRef ref D)
        =ᵐ[Causalean.SCM.jointRef ref D]
          fun x =>
            ((μ.map e.symm).rnDeriv
              (Causalean.SCM.jointRef ref (H.prefixIn D D.card))) (e.symm x) := by
    rw [← href, Filter.EventuallyEq, hf.ae_map_iff]
    filter_upwards [hf.rnDeriv_map (μ.map e.symm)
      (Causalean.SCM.jointRef ref (H.prefixIn D D.card))] with y hy
    simpa [hμe] using hy
  refine hmap.trans ?_
  rw [← href, Filter.EventuallyEq, hf.ae_map_iff]
  filter_upwards [hprefix] with y hy
  have hleft : e.symm (e y) = y := e.left_inv y
  rw [hleft, hy]
  simpa using tianPrefixDensityProductInPrefix_card_eq_tianDensityProduct H D μ ref y

/-- **Density form of the Markov-to-c-factorization theorem.** Let `H` be a pure SWIG graph, `D`
a finite set of SWIG nodes, `μ` a finite (probability) measure on the assignments to `D`, and
`ref` a family of reference measures. If [`D` is exactly the observed-node set of `H`](hyp:hD)
and [`μ` is absolutely continuous with respect to the product reference measure on
`D`](hyp:hdom), then [the Radon–Nikodym density of `μ` against that product reference equals,
almost everywhere, the product over the c-components of `H` of their Tian district-density
factors](goal).

The statement is intentionally measure-native rather than an `SCM.induce`
specialization, so it can be applied directly to ancestral do-law marginals. -/
theorem markov_tian_cfactorization_density
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (hD : H.observed = D)
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    [StandardBorelSpace (ValuesOn D (swigΩ Ω))]
    [MeasureTheory.IsProbabilityMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (hdom : μ ≪ Causalean.SCM.jointRef ref D) :
    μ.rnDeriv (Causalean.SCM.jointRef ref D)
      =ᵐ[Causalean.SCM.jointRef ref D]
        fun x => ∏ S ∈ H.cComponentSet, tianDistrictDensity H D μ ref S x := by
  exact (rnDeriv_eq_tianDensityProduct H D μ ref hdom).trans
    (Filter.EventuallyEq.of_eq
      (prod_tianDistrictDensity_eq_tianDensityProduct H D hD μ ref).symm)


end SCM.ID
end Causalean
