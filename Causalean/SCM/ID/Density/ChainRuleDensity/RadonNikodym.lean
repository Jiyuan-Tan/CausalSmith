/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.MeasureTheory.FinsetValues
public import Causalean.Mathlib.MeasureTheory.RnDerivCompProdSigmaFinite
public import Causalean.SCM.ID.Density.ChainRuleDensity.Core
public import Causalean.SCM.ID.Density.FiniteReference
public import Causalean.SCM.ID.Density.PiUnion
public import Causalean.SCM.ID.GraphicalThms.ChainRuleFactorization
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.RadonNikodym
public import Mathlib.Probability.Kernel.RadonNikodym

/-! # Radon--Nikodym chain rule for observational densities

This file proves the prefix induction that turns stepwise conditional
Radon--Nikodym derivatives into the density of the observational chain kernel.
It concludes that `obsDensity` equals the product of the one-node q-factor
densities under the stated domination and measurability assumptions.
-/

public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory ENNReal

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Domination of the recursive observed-prefix chain by the prefix reference.

Proof plan: use `obsKernel_map_prefixNodes` to identify the chain as the
push-forward of `obsKernel s`; push `hdom s` forward; then prove the
finite-index `Measure.pi` marginal helper
`(jointRef ref M.observed).map (valuesProjection ...) ≪ jointRef ref (prefixNodes k)`.
-/
lemma obsChainKernel_absolutelyContinuous_jointRef_prefix
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (k : ℕ) (hk : k ≤ M.observed.card) :
    M.obsChainKernel k hk s ≪ jointRef ref (M.prefixNodes k) := by
  classical
  -- The chain kernel is the prefix marginal of the (dominated) observational law.
  rw [← M.obsKernel_map_prefixNodes s k hk]
  have hsubset : M.prefixNodes k ⊆ M.observed := M.prefixNodes_subset_observed k
  have hDisj : Disjoint (M.prefixNodes k) (M.observed \ M.prefixNodes k) :=
    disjoint_sdiff_self_right
  have hAB : M.prefixNodes k ∪ (M.observed \ M.prefixNodes k) = M.observed :=
    Finset.union_sdiff_of_subset hsubset
  -- The prefix projection factors as `fst ∘ union-equiv ∘ reindex`.
  have hfun :
      (valuesProjection (Ω := swigΩ Ω) hsubset)
        = Prod.fst ∘ (valuesUnionEquiv (Ω := Ω) hDisj) ∘
            (valuesEquivOfEq (Ω := swigΩ Ω) hAB.symm) := by
    funext ω i; rfl
  -- The reference marginal is a scalar multiple of the prefix reference.
  have hmarg :
      (jointRef ref M.observed).map (valuesProjection hsubset)
        = (jointRef ref (M.observed \ M.prefixNodes k) Set.univ)
            • jointRef ref (M.prefixNodes k) := by
    rw [hfun]
    rw [← MeasureTheory.Measure.map_map measurable_fst
        ((valuesUnionEquiv (Ω := Ω) hDisj).measurable.comp
          (valuesEquivOfEq (Ω := swigΩ Ω) hAB.symm).measurable)]
    rw [← MeasureTheory.Measure.map_map
        (valuesUnionEquiv (Ω := Ω) hDisj).measurable
        (valuesEquivOfEq (Ω := swigΩ Ω) hAB.symm).measurable]
    rw [jointRef,
      map_pi_valuesEquivOfEq hAB.symm (fun i : {i // i ∈ M.observed} => ref.μ i.val)]
    have hsplit :
        (MeasureTheory.Measure.pi
            (fun j : {j // j ∈ M.prefixNodes k ∪ (M.observed \ M.prefixNodes k)} =>
              ref.μ j.val)).map (valuesUnionEquiv (Ω := Ω) hDisj)
          = (jointRef ref (M.prefixNodes k)).prod
              (jointRef ref (M.observed \ M.prefixNodes k)) := by
      have hmp := measurePreserving_valuesUnionEquiv (Ω := Ω) hDisj ref.μ
      simpa [jointRef] using hmp.map_eq
    rw [hsplit, MeasureTheory.Measure.map_fst_prod]
  -- Push the joint domination forward and absorb the scalar.
  refine ((hdom s).map (measurable_valuesProjection hsubset)).trans ?_
  rw [hmarg]
  intro t ht
  simp [MeasureTheory.Measure.smul_apply, ht]

/-- General prefix-level RN derivative for the recursive observational chain. -/
lemma obsChainKernel_rnDeriv_eq_prefixDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hstep : ObsStepFiberRN M ref s) :
    ∀ (k : ℕ) (hk : k ≤ M.observed.card),
      (M.obsChainKernel k hk s).rnDeriv (jointRef ref (M.prefixNodes k))
        =ᵐ[jointRef ref (M.prefixNodes k)]
          M.prefixDensityProduct ref s k := by
  intro k
  induction k with
  | zero =>
      intro hk
      -- `ValuesOn (prefixNodes 0)` is a one-point space; both measures are probability
      -- measures there, hence equal, and `rnDeriv_self =ᵐ 1 = prefixDensityProduct 0`.
      have hsub : Subsingleton (ValuesOn (M.prefixNodes 0) (swigΩ Ω)) :=
        ⟨fun a b => funext fun i =>
          absurd (M.prefixNodes_zero ▸ i.property) (Finset.notMem_empty i.val)⟩
      have heq : M.obsChainKernel 0 hk s = jointRef ref (M.prefixNodes 0) := by
        refine MeasureTheory.Measure.ext fun A _ => ?_
        rcases Set.eq_empty_or_nonempty A with rfl | hA
        · simp
        · obtain ⟨a, ha⟩ := hA
          have hAuniv : A = Set.univ :=
            Set.eq_univ_of_forall fun x => (hsub.elim x a) ▸ ha
          subst hAuniv
          rw [MeasureTheory.measure_univ, jointRef, MeasureTheory.Measure.pi_univ]
          symm
          apply Finset.prod_eq_one
          intro i _
          obtain ⟨_, hlt⟩ := (M.mem_prefixNodes_iff 0 i.val).mp i.property
          exact absurd hlt (Nat.not_lt_zero _)
      rw [heq]
      have h1 : M.prefixDensityProduct ref s 0 = (fun _ => (1 : ENNReal)) := rfl
      rw [h1]
      exact MeasureTheory.Measure.rnDeriv_self _
  | succ k ih =>
      intro hk
      classical
      have hkc : k < M.observed.card := Nat.lt_of_succ_le hk
      have hkprev : k ≤ M.observed.card := Nat.le_of_succ_le hk
      let node : SWIGNode N := (M.observedAt ⟨k, hkc⟩).val
      let νk : MeasureTheory.Measure (ValuesOn (M.prefixNodes k) (swigΩ Ω)) :=
        jointRef ref (M.prefixNodes k)
      let refnode : MeasureTheory.Measure (swigΩ Ω node) := ref.μ node
      let chain : MeasureTheory.Measure (ValuesOn (M.prefixNodes k) (swigΩ Ω)) :=
        M.obsChainKernel k hkprev s
      let stepK : ProbabilityTheory.Kernel
          (ValuesOn (M.prefixNodes k) (swigΩ Ω)) (swigΩ Ω node) :=
        (M.obsStepCondKernel hkc).sectR s
      let ext :
          ValuesOn (M.prefixNodes k) (swigΩ Ω) × swigΩ Ω node →
            ValuesOn (M.prefixNodes (k + 1)) (swigΩ Ω) :=
        M.extendObsPrefix hkc
      have hchainSucc :
          M.obsChainKernel (k + 1) hk s = (chain ⊗ₘ stepK).map ext := by
        dsimp [chain, stepK, ext]
        change ((((M.obsChainKernel k hkprev) ⊗ₖ
          (M.obsStepCondKernel hkc)).map (M.extendObsPrefix hkc)) s)
            = (((M.obsChainKernel k hkprev) s) ⊗ₘ
              ((M.obsStepCondKernel hkc).sectR s)).map (M.extendObsPrefix hkc)
        rw [ProbabilityTheory.Kernel.map_apply _ (M.measurable_extendObsPrefix hkc)]
        rw [ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR]
      have hrefSucc :
          jointRef ref (M.prefixNodes (k + 1))
            = (νk.prod refnode).map ext := by
        dsimp [νk, refnode, node, ext]
        exact (jointRef_extendObsPrefix M ref hkc).symm
      have hsingle_emb : MeasurableEmbedding
          (singletonValues (α := swigΩ Ω) (v := node)) := by
        refine ⟨?_, measurable_singletonValues (α := swigΩ Ω), ?_⟩
        · intro x y hxy
          have := congrArg (singletonValue (α := swigΩ Ω) (v := node)) hxy
          simpa using this
        · intro A hA
          have hpre :
              singletonValues (α := swigΩ Ω) (v := node) '' A
                = (singletonValue (α := swigΩ Ω) (v := node)) ⁻¹' A := by
            ext x
            constructor
            · rintro ⟨a, ha, rfl⟩
              simpa using ha
            · intro hx
              refine ⟨singletonValue (α := swigΩ Ω) (v := node) x, hx, ?_⟩
              exact singletonValues_singletonValue (α := swigΩ Ω) x
          rw [hpre]
          exact hA.preimage (measurable_singletonValue (α := swigΩ Ω))
      have hext_emb : MeasurableEmbedding ext := by
        dsimp [ext, node]
        unfold extendObsPrefix
        refine
          (valuesEquivOfEq (Ω := swigΩ Ω)
            (M.prefixNodes_succ hkc).symm).measurableEmbedding.comp ?_
        change MeasurableEmbedding
          ((fun q : ValuesOn (M.prefixNodes k) (swigΩ Ω) ×
              ValuesOn ({(M.observedAt ⟨k, hkc⟩).val} : Finset (SWIGNode N)) (swigΩ Ω) =>
              valuesUnionMk q.1 q.2) ∘
            Prod.map id
              (singletonValues (α := swigΩ Ω) (v := (M.observedAt ⟨k, hkc⟩).val)))
        refine ((valuesUnionEquiv (Ω := Ω)
          (M.prefixNodes_disjoint_singleton_next hkc)).symm.measurableEmbedding).comp ?_
        exact MeasurableEmbedding.id.prodMap hsingle_emb
      have hcore :
          (chain ⊗ₘ stepK).rnDeriv (νk.prod refnode)
            =ᵐ[νk.prod refnode]
              fun p =>
                M.prefixDensityProduct ref s k p.1 *
                  (stepK p.1).rnDeriv refnode p.2 := by
        have hchain_ac : chain ≪ νk := by
          dsimp [chain, νk]
          exact M.obsChainKernel_absolutelyContinuous_jointRef_prefix ref hdom s k hkprev
        have hfiber := hstep k hkc
        have hfiber_meas :
            AEMeasurable
              (fun p : ValuesOn (M.prefixNodes k) (swigΩ Ω) × swigΩ Ω node =>
                (stepK p.1).rnDeriv refnode p.2)
              (νk.prod refnode) :=
          hfiber.2
        exact rnDeriv_compProd_prod_sigmaFinite_of_fiber_ac
          chain νk refnode stepK (M.prefixDensityProduct ref s k)
          hchain_ac hfiber.1 hfiber_meas (ih hkprev)
      rw [hchainSucc, hrefSucc, Filter.EventuallyEq, hext_emb.ae_map_iff]
      filter_upwards [hext_emb.rnDeriv_map (chain ⊗ₘ stepK) (νk.prod refnode),
        hcore] with p hmap hp
      rw [hmap, hp]
      dsimp [ext, stepK, node]
      have hpair := M.valuesUnionEquiv_extendObsPrefix hkc p
      have hproj_ext :
          valuesProjection (M.prefixNodes_mono (Nat.le_succ k))
              (M.extendObsPrefix hkc p) = p.1 := by
        funext i
        have hi := congrArg (fun q => q.1 i) hpair
        exact hi
      have hcoord_ext :
          M.extendObsPrefix hkc p ⟨(M.observedAt ⟨k, hkc⟩).val, by
            rw [M.prefixNodes_succ hkc]
            exact Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩ = p.2 := by
        have hnext :=
          congrArg
            (fun q => singletonValue (α := swigΩ Ω)
              (v := (M.observedAt ⟨k, hkc⟩).val) q.2) hpair
        exact hnext
      rw [prefixDensityProduct]
      simp [hkc, hproj_ext, hcoord_ext, refnode]
      rfl

/-- RN-derivative transport for `qFactorProduct`, assuming the final reference
transport has already been identified. -/
lemma qFactorProduct_rnDeriv_eq_obsChainKernel_card_pullback_of_jointRef
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (href :
      (jointRef ref (M.prefixNodes M.observed.card)).map
          (valuesEquivOfEq (Ω := swigΩ Ω)
            (M.prefixNodes_card M.observed.card (le_refl _)))
        = jointRef ref M.observed)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    (M.qFactorProduct s).rnDeriv (jointRef ref M.observed)
      =ᵐ[jointRef ref M.observed]
        fun x =>
          ((M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
            (jointRef ref (M.prefixNodes M.observed.card)))
            ((valuesEquivOfEq (Ω := swigΩ Ω)
              (M.prefixNodes_card M.observed.card (le_refl _))).symm x) := by
  classical
  set e := valuesEquivOfEq (Ω := swigΩ Ω)
    (M.prefixNodes_card M.observed.card (le_refl _)) with he
  have hf : MeasurableEmbedding
      (e : ValuesOn (M.prefixNodes M.observed.card) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω)) := e.measurableEmbedding
  have hq : M.qFactorProduct s
      = (M.obsChainKernel M.observed.card (le_refl _) s).map e := by
    rw [qFactorProduct, ProbabilityTheory.Kernel.map_apply _ e.measurable]
  rw [hq, ← href, Filter.EventuallyEq, hf.ae_map_iff]
  filter_upwards [hf.rnDeriv_map (M.obsChainKernel M.observed.card (le_refl _) s)
    (jointRef ref (M.prefixNodes M.observed.card))] with y hy
  simpa using hy

/-- Peel the final `qFactorProduct` map back to the full prefix chain kernel.

This is the `MeasurableEmbedding.rnDeriv_map` transport step for
`qFactorProduct = (obsChainKernel card).map (valuesEquivOfEq prefixNodes_card)`. -/
lemma qFactorProduct_rnDeriv_eq_obsChainKernel_card_pullback
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    (M.qFactorProduct s).rnDeriv (jointRef ref M.observed)
      =ᵐ[jointRef ref M.observed]
        fun x =>
          ((M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
            (jointRef ref (M.prefixNodes M.observed.card)))
            ((valuesEquivOfEq (Ω := swigΩ Ω)
              (M.prefixNodes_card M.observed.card (le_refl _))).symm x) := by
  exact
    qFactorProduct_rnDeriv_eq_obsChainKernel_card_pullback_of_jointRef
      M ref s (jointRef_prefix_card_map M ref)

/-- The analytic prefix induction for the density chain rule.

Inducting over `obsChainKernel` identifies the Radon--Nikodym derivative of the
full observed-prefix chain with the recursive prefix density product.  Each
successor step uses `jointRef_extendObsPrefix`, the measurable embedding
transport for Radon--Nikodym derivatives, and the comp-product derivative rule,
then the final prefix product is rewritten as `qFactorDensityProduct`. -/
lemma obsChainKernel_card_rnDeriv_eq_qFactorDensityProduct_prefix_induction
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hstep : ObsStepFiberRN M ref s) :
    (M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
        (jointRef ref (M.prefixNodes M.observed.card))
      =ᵐ[jointRef ref (M.prefixNodes M.observed.card)]
        fun y =>
          M.qFactorDensityProduct ref s
            ((valuesEquivOfEq (Ω := swigΩ Ω)
              (M.prefixNodes_card M.observed.card (le_refl _))) y) := by
  exact
    (obsChainKernel_rnDeriv_eq_prefixDensityProduct M ref hdom s hstep
      M.observed.card (le_refl _)).trans
      (Filter.EventuallyEq.of_eq
        (funext (prefixDensityProduct_card_eq_qFactorDensityProduct M ref s)))

/-- Prefix-level analytic chain rule at the full observed prefix.

The right side is the full density product, read after transporting a full-prefix
assignment to an observed assignment.  This wrapper exposes the completed prefix
induction in the shape consumed by the final observed-coordinate transport. -/
lemma obsChainKernel_card_rnDeriv_eq_qFactorDensityProduct_prefix
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hstep : ObsStepFiberRN M ref s) :
    (M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
        (jointRef ref (M.prefixNodes M.observed.card))
      =ᵐ[jointRef ref (M.prefixNodes M.observed.card)]
        fun y =>
          M.qFactorDensityProduct ref s
            ((valuesEquivOfEq (Ω := swigΩ Ω)
              (M.prefixNodes_card M.observed.card (le_refl _))) y) := by
  exact obsChainKernel_card_rnDeriv_eq_qFactorDensityProduct_prefix_induction
    M ref hdom s hstep

/-- Push the full-prefix a.e. density identity forward, assuming the reference
transport and prefix-level chain rule. -/
lemma obsChainKernel_card_rnDeriv_pullback_eq_qFactorDensityProduct_of_prefix
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (href :
      (jointRef ref (M.prefixNodes M.observed.card)).map
          (valuesEquivOfEq (Ω := swigΩ Ω)
            (M.prefixNodes_card M.observed.card (le_refl _)))
        = jointRef ref M.observed)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hprefix :
      (M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
          (jointRef ref (M.prefixNodes M.observed.card))
        =ᵐ[jointRef ref (M.prefixNodes M.observed.card)]
          fun y =>
            M.qFactorDensityProduct ref s
              ((valuesEquivOfEq (Ω := swigΩ Ω)
                (M.prefixNodes_card M.observed.card (le_refl _))) y)) :
    (fun x =>
      ((M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
        (jointRef ref (M.prefixNodes M.observed.card)))
        ((valuesEquivOfEq (Ω := swigΩ Ω)
          (M.prefixNodes_card M.observed.card (le_refl _))).symm x))
      =ᵐ[jointRef ref M.observed]
        M.qFactorDensityProduct ref s := by
  classical
  set e := valuesEquivOfEq (Ω := swigΩ Ω)
    (M.prefixNodes_card M.observed.card (le_refl _)) with he
  have hf : MeasurableEmbedding
      (e : ValuesOn (M.prefixNodes M.observed.card) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω)) := e.measurableEmbedding
  rw [← href, Filter.EventuallyEq, hf.ae_map_iff]
  filter_upwards [hprefix] with y hy
  simpa using hy

/-- Push the full-prefix a.e. density identity forward to observed coordinates. -/
lemma obsChainKernel_card_rnDeriv_pullback_eq_qFactorDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hstep : ObsStepFiberRN M ref s) :
    (fun x =>
      ((M.obsChainKernel M.observed.card (le_refl _) s).rnDeriv
        (jointRef ref (M.prefixNodes M.observed.card)))
        ((valuesEquivOfEq (Ω := swigΩ Ω)
          (M.prefixNodes_card M.observed.card (le_refl _))).symm x))
      =ᵐ[jointRef ref M.observed]
        M.qFactorDensityProduct ref s := by
  exact
    obsChainKernel_card_rnDeriv_pullback_eq_qFactorDensityProduct_of_prefix
      M ref s (jointRef_prefix_card_map M ref)
      (obsChainKernel_card_rnDeriv_eq_qFactorDensityProduct_prefix M ref hdom s hstep)

/-- **Analytic chain rule for the mapped observational product kernel.**

The Radon--Nikodym derivative of the kernel-native observational chain product
with respect to the product reference equals the product of the per-step
conditional Radon--Nikodym derivatives.  This is the measure-theoretic core:
one proves it by induction over `obsChainKernel`, applying
`ProbabilityTheory.rnDeriv_compProd` at each successor step and transporting
the result through `extendObsPrefix` and `valuesEquivOfEq`.

The domination hypothesis `DominatedObs M ref` is essential: without absolute
continuity the joint law can have a part singular to the reference, where the
Radon--Nikodym derivative vanishes while the product of conditional densities
need not, so the identity would be false. -/
theorem qFactorProduct_rnDeriv_eq_qFactorDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hstep : ObsStepFiberRN M ref s) :
    (M.qFactorProduct s).rnDeriv (jointRef ref M.observed)
      =ᵐ[jointRef ref M.observed]
        M.qFactorDensityProduct ref s := by
  exact
    (qFactorProduct_rnDeriv_eq_obsChainKernel_card_pullback M ref s).trans
      (obsChainKernel_card_rnDeriv_pullback_eq_qFactorDensityProduct M ref hdom s hstep)

/-- **Observational density chain rule.** In a [structural causal model whose observational
law is absolutely continuous with respect to the joint reference measure on the observed
nodes](hyp:hdom), if in addition [the stepwise fibre Radon--Nikodym condition holds along
the observed topological order](hyp:hstep), then [the joint observational density agrees,
almost everywhere with respect to that joint reference measure, with the product of the
one-node conditional density factors taken in observed topological order](goal).

Unlike a finite/discrete statement this covers continuous reference measures. -/
theorem obsDensity_eq_qFactorDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hstep : ObsStepFiberRN M ref s) :
    M.obsDensity ref s =ᵐ[jointRef ref M.observed]
      M.qFactorDensityProduct ref s := by
  unfold obsDensity
  rw [obsKernel_eq_chainRuleProduct M s]
  exact M.qFactorProduct_rnDeriv_eq_qFactorDensityProduct ref hdom s hstep

end Causalean.SCM
