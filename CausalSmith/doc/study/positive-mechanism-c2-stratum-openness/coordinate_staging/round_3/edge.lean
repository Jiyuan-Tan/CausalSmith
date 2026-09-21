import Causalean.Graph.FiniteDensity.Positive.Basic
/-!
# Edge minimality for compact positive DAG densities

This module characterizes a redundant edge in a compact strictly positive finite-DAG density:
conditional independence given the other parents is exactly pointwise independence of the
child's local factor, equivalently vanishing of its four-point contrast.
-/
open scoped ENNReal BigOperators
open Set Function MeasureTheory ProbabilityTheory
noncomputable section
namespace Causalean.Graph.FiniteDensity
open Causalean Causalean.Graph.FiniteDensity

universe uV uX

variable {V : Type uV} [Fintype V] [DecidableEq V]
variable {X : V → Type uX} [∀ i, MeasurableSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
variable {G : DAG V}
variable [∀ i, TopologicalSpace (X i)] [∀ i, BorelSpace (X i)]
variable [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
variable [∀ i, StandardBorelSpace (X i)] [∀ i, (μ i).IsOpenPosMeasure]
namespace CompactPositiveFactorization

variable (M : CompactPositiveFactorization G X μ)

/-- Splitting a parent assignment into the coordinates other than `j` and coordinate `j`. -/
private def parentSplitEquiv {i j : V} (hji : G.edge j i) :
    (∀ k : G.parents i, X k) ≃ᵐ
      ((∀ k : (G.parents i).erase j, X k) × X j) := by
  classical
  let C := (G.parents i).erase j
  have hjP : j ∈ G.parents i := G.mem_parents.mpr hji
  have hdisj : Disjoint C {j} := Finset.disjoint_singleton_right.mpr (by simp [C])
  let r : G.parents i ≃ (C ∪ {j} : Finset V) :=
    { toFun := fun k ↦ ⟨k, by simpa [C, hjP] using k.property⟩
      invFun := fun k ↦ ⟨k, by simpa [C, hjP] using k.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact (MeasurableEquiv.piCongrLeft
    (fun k : (C ∪ {j} : Finset V) ↦ X k) r).trans
    ((MeasurableEquiv.piFinsetUnion X hdisj).symm.trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (MeasurableEquiv.piUnique (fun k : ({j} : Finset V) ↦ X k))))

@[simp] private theorem parentSplitEquiv_apply {i j : V} (hji : G.edge j i)
    (p : ∀ k : G.parents i, X k) :
    parentSplitEquiv (X := X) hji p =
      (fun k : (G.parents i).erase j ↦
          p ⟨k, Finset.mem_of_mem_erase k.property⟩,
        p ⟨j, G.mem_parents.mpr hji⟩) := by
  classical
  let C := (G.parents i).erase j
  have hjP : j ∈ G.parents i := G.mem_parents.mpr hji
  have hdisj : Disjoint C {j} := Finset.disjoint_singleton_right.mpr (by simp [C])
  let r : G.parents i ≃ (C ∪ {j} : Finset V) :=
    { toFun := fun k ↦ ⟨k, by simpa [C, hjP] using k.property⟩
      invFun := fun k ↦ ⟨k, by simpa [C, hjP] using k.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let a := MeasurableEquiv.piCongrLeft (fun k : (C ∪ {j} : Finset V) ↦ X k) r p
  let q := (MeasurableEquiv.piFinsetUnion X hdisj).symm a
  change (q.1, q.2 default) = _
  apply Prod.ext
  · funext k
    have hu := congrFun ((MeasurableEquiv.piFinsetUnion X hdisj).apply_symm_apply a)
      (⟨k, Finset.mem_union_left {j} k.property⟩ : (C ∪ {j} : Finset V))
    change (Equiv.piFinsetUnion X hdisj) q
      ⟨k, Finset.mem_union_left {j} k.property⟩ = _ at hu
    rw [Equiv.piFinsetUnion_left X hdisj k.property] at hu
    calc
      q.1 k = a ⟨k, Finset.mem_union_left {j} k.property⟩ := by
        convert hu using 1
      _ = p ⟨k, Finset.mem_of_mem_erase k.property⟩ := by
        exact MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun k : (C ∪ {j} : Finset V) ↦ X k) r p
            (⟨k, Finset.mem_of_mem_erase k.property⟩ : G.parents i)
  · have hu := congrFun ((MeasurableEquiv.piFinsetUnion X hdisj).apply_symm_apply a)
      (⟨j, Finset.mem_union_right C (Finset.mem_singleton_self j)⟩ :
        (C ∪ {j} : Finset V))
    change (Equiv.piFinsetUnion X hdisj) q
      ⟨j, Finset.mem_union_right C (Finset.mem_singleton_self j)⟩ = _ at hu
    rw [Equiv.piFinsetUnion_right X hdisj (Finset.mem_singleton_self j)] at hu
    calc
      q.2 default = a ⟨j, Finset.mem_union_right C
          (Finset.mem_singleton_self j)⟩ := by
        have hs : default =
            (⟨j, Finset.mem_singleton_self j⟩ : ({j} : Finset V)) :=
          Subsingleton.elim _ _
        cases hs
        exact hu
      _ = p ⟨j, G.mem_parents.mpr hji⟩ := by
        exact MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun k : (C ∪ {j} : Finset V) ↦ X k) r p
            (⟨j, G.mem_parents.mpr hji⟩ : G.parents i)
/-- The real four-point cross-product contrast of a child's local density varies its own
coordinate and one parent coordinate while holding all remaining coordinates fixed. -/
def localContrast (i j : V) (x : ∀ k, X k)
    (xi xi' : X i) (xj xj' : X j) : ℝ :=
  (M.toFactorization.factor i
      (Function.update (Function.update x i xi) j xj)).toReal *
      (M.toFactorization.factor i
        (Function.update (Function.update x i xi') j xj')).toReal -
    (M.toFactorization.factor i
      (Function.update (Function.update x i xi) j xj')).toReal *
      (M.toFactorization.factor i
        (Function.update (Function.update x i xi') j xj)).toReal

/-- For an edge `j → i`, conditional independence of the endpoints given the other parents
forces reference-almost-everywhere independence of the child's local factor from `j`. -/
theorem aeFactorIndependent_of_edge_condIndep {i j : V} (hji : G.edge j i) :
    M.CondIndepCoordinates i j ((G.parents i).erase j) →
      M.AEFactorIndependentOf i j := by
  /- Use `lintegral_node_given_parents` with bounded indicator tests to identify the conditional
  law of `i` given all parents.  Conditional independence drops `j` from that law.  Strict
  positivity makes the observational law equivalent to the product reference law, after which
  uniqueness of Radon–Nikodym densities gives the iterated-a.e. update identity.

  Useful library bridges are
  `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` (after `CondIndepFun.symm`) for dropping
  `j` from the conditional kernel, and `MeasureTheory.withDensity_ae_eq` (or
  `withDensity_absolutelyContinuous'`) for transferring the resulting observational-a.e.
  statement to `Measure.pi μ`. -/
  intro hCI
  classical
  let C := (G.parents i).erase j
  let P := G.parents i
  let Y : (∀ k, X k) → X i := fun x ↦ x i
  let J : (∀ k, X k) → X j := fun x ↦ x j
  let K := coordinateProjection (X := X) C
  let R := coordinateProjection (X := X) P
  let e := parentSplitEquiv (X := X) hji
  have he : e ∘ R = fun x ↦ (K x, J x) := by
    funext x
    change e (R x) = (K x, J x)
    rw [show e (R x) =
      (fun k : (G.parents i).erase j ↦
          R x ⟨k, Finset.mem_of_mem_erase k.property⟩,
        R x ⟨j, G.mem_parents.mpr hji⟩) by
      exact parentSplitEquiv_apply (X := X) hji (R x)]
    rfl
  have hdrop :
      condDistrib Y (fun x ↦ (K x, J x)) M.observationalMeasure
        =ᵐ[Measure.map (fun x ↦ (K x, J x)) M.observationalMeasure]
          (condDistrib Y K M.observationalMeasure).prodMkRight _ := by
    apply (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
      (f := Y) (g := J) (k := K)
      (by fun_prop) (by fun_prop) (by fun_prop)).mp
    simpa [CondIndepCoordinates, Y, J, K, C] using hCI.symm
  have hreparam :=
    Causalean.condDistrib_comp_right_measurableEquiv M.observationalMeasure e
      (Y := Y) (X := R) (by fun_prop) (by fun_prop)
  have hparent := M.condDistrib_child_given_parents i
  change condDistrib Y R M.observationalMeasure
      =ᵐ[Measure.map R M.observationalMeasure] _ at hparent
  have hmap :
      Measure.map e (Measure.map R M.observationalMeasure) =
        Measure.map (fun x ↦ (K x, J x)) M.observationalMeasure := by
    rw [Measure.map_map e.measurable (by fun_prop), he]
  have hdrop' :
      (fun p ↦ condDistrib Y (fun x ↦ (K x, J x)) M.observationalMeasure (e p))
        =ᵐ[Measure.map R M.observationalMeasure]
          fun p ↦ condDistrib Y K M.observationalMeasure (e p).1 := by
    have h := ae_of_ae_map (μ := Measure.map R M.observationalMeasure)
      e.measurable.aemeasurable (by rw [hmap]; exact hdrop)
    filter_upwards [h] with p hp
    simpa using hp
  have hparent_drop :
      (fun p ↦ (Kernel.withDensity
        (Kernel.const (∀ k : P, X k) (μ i))
        (fun p z ↦ M.toFactorization.factor i
          (Function.update
            (coordinateExtension P (Classical.choice inferInstance) p) i z))) p)
        =ᵐ[Measure.map R M.observationalMeasure]
          fun p ↦ condDistrib Y K M.observationalMeasure (e p).1 := by
    filter_upwards [hparent, hreparam, hdrop'] with p hp hr hd
    exact hp.symm.trans (hr.symm.trans hd)
  have hobs := ae_of_ae_map (μ := M.observationalMeasure)
    (show AEMeasurable R M.observationalMeasure by fun_prop) hparent_drop
  have hfactor_ne_zero (k : V) (x : ∀ l, X l) :
      M.toFactorization.factor k x ≠ 0 := by
    intro hk
    have hle := M.lower_le_factor k x
    rw [hk] at hle
    simp only [ENNReal.toReal_zero] at hle
    exact (not_lt_of_ge hle) M.lower_pos
  have hdensity_ne_zero :
      ∀ᵐ x ∂Measure.pi μ, M.toFactorization.observationalDensity x ≠ 0 :=
    Filter.Eventually.of_forall fun x ↦
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ hfactor_ne_zero k x
  have hpi :
      (fun x ↦ (Kernel.withDensity
        (Kernel.const (∀ k : P, X k) (μ i))
        (fun p z ↦ M.toFactorization.factor i
          (Function.update
            (coordinateExtension P (Classical.choice inferInstance) p) i z))) (R x))
        =ᵐ[Measure.pi μ]
          fun x ↦ condDistrib Y K M.observationalMeasure (e (R x)).1 :=
    (withDensity_ae_eq
    M.toFactorization.measurable_observationalDensity.aemeasurable
      hdensity_ne_zero).mp (by
        change (fun x ↦ (Kernel.withDensity
          (Kernel.const (∀ k : P, X k) (μ i))
          (fun p z ↦ M.toFactorization.factor i
            (Function.update
              (coordinateExtension P (Classical.choice inferInstance) p) i z))) (R x))
          =ᵐ[M.observationalMeasure]
            fun x ↦ condDistrib Y K M.observationalMeasure (e (R x)).1
        exact hobs)
  let split := MeasurableEquiv.piEquivPiSubtypeProd X (fun k ↦ k ∈ C)
  let μC : Measure (∀ k : {k // k ∈ C}, X k) :=
    @Measure.pi {k : V // k ∈ C} (fun k ↦ X k)
      (Subtype.fintype fun k ↦ k ∈ C) (fun k ↦ inferInstance) (fun k ↦ μ k)
  let μD : Measure (∀ k : {k // k ∉ C}, X k) :=
    @Measure.pi {k : V // k ∉ C} (fun k ↦ X k)
      (Subtype.fintype fun k ↦ k ∉ C) (fun k ↦ inferInstance) (fun k ↦ μ k)
  have hsplit_pres : MeasurePreserving split (Measure.pi μ) (μC.prod μD) := by
    simpa [split, μC, μD] using
      measurePreserving_piEquivPiSubtypeProd μ (fun k ↦ k ∈ C)
  have hsplit :
      ∀ᵐ q ∂μC.prod μD,
        (Kernel.withDensity
          (Kernel.const (∀ k : P, X k) (μ i))
          (fun p z ↦ M.toFactorization.factor i
            (Function.update
              (coordinateExtension P (Classical.choice inferInstance) p) i z)))
            (R (split.symm q)) =
          condDistrib Y K M.observationalMeasure q.1 := by
    have hs := ae_of_ae_map (μ := μC.prod μD)
      split.symm.measurable.aemeasurable (by
        rw [(MeasurePreserving.symm split hsplit_pres).map_eq]
        exact hpi)
    filter_upwards [hs] with q hq
    rw [hq]
    congr 1
    change ((e ∘ R) (split.symm q)).1 = q.1
    rw [he]
    change K (split.symm q) = q.1
    funext k
    simp [K, coordinateProjection, split]
  have hsplit_nested := Measure.ae_ae_of_ae_prod hsplit
  let x₀ : ∀ k, X k := Classical.choice inferInstance
  let d : (∀ k : P, X k) → X i → ℝ≥0∞ := fun p z ↦
    M.toFactorization.factor i (Function.update (coordinateExtension P x₀ p) i z)
  have hd : Measurable (Function.uncurry d) := by
    unfold d
    exact (M.toFactorization.measurable_factor i).comp
      (measurable_update'.comp
        (((measurable_coordinateExtension P x₀).comp measurable_fst).prodMk measurable_snd))
  let κ : Kernel (∀ k : P, X k) (X i) :=
    Kernel.withDensity (Kernel.const (∀ k : P, X k) (μ i)) d
  have hκ_apply (p : ∀ k : P, X k) :
      κ p = (μ i).withDensity (d p) := by
    dsimp [κ]
    rw [Kernel.withDensity_apply _ hd, Kernel.const_apply]
  have hd_eq (x : ∀ k, X k) (z : X i) :
      d (R x) z = M.toFactorization.factor i (Function.update x i z) := by
    unfold d
    apply M.toFactorization.local_factor i
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simp
    · have hki : k ≠ i := by
        intro hki
        subst k
        exact G.irrefl i (G.mem_parents.mp hk)
      have hkP : k ∈ P := by simpa [P] using hk
      simp [R, coordinateProjection, coordinateExtension, hkP, hki]
  have hsection_ae :
      ∀ᵐ c ∂μC, ∀ᵐ r₁ ∂μD, ∀ᵐ r₂ ∂μD, ∀ᵐ z ∂μ i,
        M.toFactorization.factor i
            (Function.update (split.symm (c, r₁)) i z) =
          M.toFactorization.factor i
            (Function.update (split.symm (c, r₂)) i z) := by
    filter_upwards [hsplit_nested] with c hc
    filter_upwards [hc] with r₁ hr₁
    filter_upwards [hc] with r₂ hr₂
    have hκ : κ (R (split.symm (c, r₁))) = κ (R (split.symm (c, r₂))) := by
      exact hr₁.trans hr₂.symm
    have hden :
        d (R (split.symm (c, r₁))) =ᵐ[μ i]
          d (R (split.symm (c, r₂))) :=
      (withDensity_eq_iff_of_sigmaFinite
        (Measurable.of_uncurry_left hd
          (x := R (split.symm (c, r₁)))).aemeasurable
        (Measurable.of_uncurry_left hd
          (x := R (split.symm (c, r₂)))).aemeasurable).mp (by
            rw [← hκ_apply, ← hκ_apply]
            exact hκ)
    filter_upwards [hden] with z hz
    simpa only [hd_eq] using hz
  let f : ((∀ k : {k // k ∈ C}, X k) ×
      ((∀ k : {k // k ∉ C}, X k) ×
        ((∀ k : {k // k ∉ C}, X k) × X i))) → ℝ := fun q ↦
    (M.toFactorization.factor i
      (Function.update (split.symm (q.1, q.2.1)) i q.2.2.2)).toReal
  let g : ((∀ k : {k // k ∈ C}, X k) ×
      ((∀ k : {k // k ∉ C}, X k) ×
        ((∀ k : {k // k ∉ C}, X k) × X i))) → ℝ := fun q ↦
    (M.toFactorization.factor i
      (Function.update (split.symm (q.1, q.2.2.1)) i q.2.2.2)).toReal
  have hsplit_cont : Continuous split.symm := by
    change Continuous (Homeomorph.piEquivPiSubtypeProd (fun k ↦ k ∈ C) X).symm
    exact (Homeomorph.piEquivPiSubtypeProd (fun k ↦ k ∈ C) X).symm.continuous
  have hf : Continuous f := by
    unfold f
    exact (M.factor_continuous i).comp
      ((hsplit_cont.comp (continuous_fst.prodMk continuous_snd.fst)).update i
        continuous_snd.snd.snd)
  have hg : Continuous g := by
    unfold g
    exact (M.factor_continuous i).comp
      ((hsplit_cont.comp (continuous_fst.prodMk continuous_snd.snd.fst)).update i
        continuous_snd.snd.snd)
  have hfm : Measurable f := by
    unfold f
    exact ((M.toFactorization.measurable_factor i).comp
      (measurable_update'.comp
        ((split.symm.measurable.comp
          (measurable_fst.prodMk measurable_snd.fst)).prodMk
            measurable_snd.snd.snd))).ennreal_toReal
  have hgm : Measurable g := by
    unfold g
    exact ((M.toFactorization.measurable_factor i).comp
      (measurable_update'.comp
        ((split.symm.measurable.comp
          (measurable_fst.prodMk measurable_snd.snd.fst)).prodMk
            measurable_snd.snd.snd))).ennreal_toReal
  have hfg_ae : f =ᵐ[μC.prod (μD.prod (μD.prod (μ i)))] g := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun hfm hgm)).2
    filter_upwards [hsection_ae] with c hc
    have hfm_c : Measurable (fun y ↦ f (c, y)) :=
      hfm.comp (measurable_const.prodMk measurable_id)
    have hgm_c : Measurable (fun y ↦ g (c, y)) :=
      hgm.comp (measurable_const.prodMk measurable_id)
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun hfm_c hgm_c)).2
    filter_upwards [hc] with r₁ hr₁
    have hfm_cr₁ : Measurable (fun y ↦ f (c, r₁, y)) :=
      hfm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hgm_cr₁ : Measurable (fun y ↦ g (c, r₁, y)) :=
      hgm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun hfm_cr₁ hgm_cr₁)).2
    filter_upwards [hr₁] with r₂ hr₂
    filter_upwards [hr₂] with z hz
    exact congrArg ENNReal.toReal hz
  have hfg : f = g :=
    (hf.ae_eq_iff_eq (μC.prod (μD.prod (μD.prod (μ i)))) hg).mp hfg_ae
  have hsections (c : ∀ k : {k // k ∈ C}, X k)
      (r₁ r₂ : ∀ k : {k // k ∉ C}, X k) (z : X i) :
      M.toFactorization.factor i (Function.update (split.symm (c, r₁)) i z) =
        M.toFactorization.factor i (Function.update (split.symm (c, r₂)) i z) := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (M.factor_ne_top i (Function.update (split.symm (c, r₁)) i z))
      (M.factor_ne_top i (Function.update (split.symm (c, r₂)) i z))).mp
    exact congrFun hfg (c, r₁, r₂, z)
  refine Filter.Eventually.of_forall fun x ↦ Filter.Eventually.of_forall fun xj ↦ ?_
  have hij : i ≠ j := by
    intro hij
    subst j
    exact G.irrefl i hji
  have hfirst : (split (Function.update x j xj)).1 = (split x).1 := by
    funext k
    have hkj : (k : V) ≠ j := by
      exact Finset.ne_of_mem_erase k.property
    simp [split, hkj]
  have hassemble :
      split.symm ((split x).1, (split (Function.update x j xj)).2) =
        Function.update x j xj := by
    apply split.injective
    simp only [split.apply_symm_apply]
    exact Prod.ext hfirst.symm rfl
  have hs := hsections (split x).1 (split x).2
    (split (Function.update x j xj)).2 (x i)
  rw [split.symm_apply_apply, Function.update_eq_self, hassemble] at hs
  have hiupdate : Function.update x j xj i = x i := by
    exact Function.update_of_ne hij xj x
  have hidem :
      Function.update (Function.update x j xj) i (x i) =
        Function.update x j xj := by
    rw [← hiupdate, Function.update_eq_self]
  rw [hidem] at hs
  exact hs.symm

/-- Pointwise independence of a local factor from one coordinate implies the corresponding
iterated product-reference almost-everywhere update identity. -/
theorem aeFactorIndependent_of_factorIndependent {i j : V} :
    M.FactorIndependentOf i j → M.AEFactorIndependentOf i j := by
  intro h
  exact Filter.Eventually.of_forall fun x ↦
    Filter.Eventually.of_forall fun xj ↦ h x xj

/-- Continuity and full support upgrade the iterated product-reference almost-everywhere update
identity for a local factor to pointwise independence on the whole compact product domain. -/
theorem factorIndependent_of_aeFactorIndependent {i j : V} :
    M.AEFactorIndependentOf i j → M.FactorIndependentOf i j := by
  /- Regard the two sides as continuous real functions on `(∀ k, X k) × X j`.  Convert the
  iterated a.e. hypothesis to product-measure a.e. equality, apply full-support extensionality,
  and use `factor_ne_top` to reflect equality through `ENNReal.toReal`. -/
  intro h
  let f : ((∀ k, X k) × X j) → ℝ := fun z ↦
    (M.toFactorization.factor i (Function.update z.1 j z.2)).toReal
  let g : ((∀ k, X k) × X j) → ℝ := fun z ↦
    (M.toFactorization.factor i z.1).toReal
  have hf : Continuous f :=
    (M.factor_continuous i).comp (continuous_fst.update j continuous_snd)
  have hg : Continuous g := (M.factor_continuous i).comp continuous_fst
  have hae : f =ᵐ[(Measure.pi μ).prod (μ j)] g := by
    have hfm : Measurable f :=
      ((M.toFactorization.measurable_factor i).comp measurable_update').ennreal_toReal
    have hgm : Measurable g :=
      ((M.toFactorization.measurable_factor i).comp measurable_fst).ennreal_toReal
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hfm hgm)).2
    filter_upwards [h] with x hx
    filter_upwards [hx] with xj hxj
    exact congrArg ENNReal.toReal hxj
  have hfg : f = g :=
    (hf.ae_eq_iff_eq ((Measure.pi μ).prod (μ j)) hg).mp hae
  intro x xj
  apply (ENNReal.toReal_eq_toReal_iff'
    (M.factor_ne_top i (Function.update x j xj)) (M.factor_ne_top i x)).mp
  exact congrFun hfg (x, xj)

/-- Continuity and full support upgrade almost-everywhere independence of a local density factor
from one coordinate to pointwise independence on the entire compact product domain. -/
theorem aeFactorIndependent_iff_factorIndependent {i j : V} :
    M.AEFactorIndependentOf i j ↔ M.FactorIndependentOf i j := by
  exact ⟨M.factorIndependent_of_aeFactorIndependent,
    M.aeFactorIndependent_of_factorIndependent⟩

/-- For an edge `j → i`, pointwise independence of the child's local factor from `j` implies
conditional independence of the endpoints given the other parents. -/
theorem edge_condIndep_of_factorIndependent {i j : V} (hji : G.edge j i) :
    M.FactorIndependentOf i j →
      M.CondIndepCoordinates i j ((G.parents i).erase j) := by
  /- Delete the single edge `j → i`, reuse the same normalized factors as a factorization of
  the resulting sub-DAG (the new locality obligation is exactly factor independence), and apply
  the ordered local-Markov theorem in that sub-DAG.  Its parent set at `i` is
  `(G.parents i).erase j`; contract the predecessor residual to coordinate `j`. -/
  intro hind
  classical
  let H : DAG V :=
    { edge := fun u v ↦ G.edge u v ∧ ¬ (u = j ∧ v = i)
      decEdge := inferInstance
      acyclic := by
        intro v hv
        exact G.acyclic v ((Relation.TransGen.mono
          (r := fun u v ↦ G.edge u v ∧ ¬ (u = j ∧ v = i)) (p := G.edge)
          (fun _ _ h ↦ h.1)) v v hv) }
  let B : Factorization H X μ :=
    { factor := M.toFactorization.factor
      measurable_factor := M.toFactorization.measurable_factor
      normalized_factor := M.toFactorization.normalized_factor
      local_factor := by
        intro k x y hxy
        by_cases hki : k = i
        · have hxyi : ∀ l, l ∈ insert i (H.parents i) → x l = y l := by
            intro l hl
            apply hxy l
            simpa only [hki] using hl
          have hi : M.toFactorization.factor i x = M.toFactorization.factor i y := by
            calc
              M.toFactorization.factor i x =
                  M.toFactorization.factor i (Function.update x j (y j)) :=
                (hind x (y j)).symm
              _ = M.toFactorization.factor i y := by
                apply M.toFactorization.local_factor i
                intro l hl
                rcases Finset.mem_insert.mp hl with hli | hl
                · have hlj : l ≠ j := by
                    intro h
                    have hij : i ≠ j := fun hij ↦ G.irrefl i (hij ▸ hji)
                    exact hij (hli.symm.trans h)
                  rw [Function.update_of_ne hlj]
                  exact hxyi l (Finset.mem_insert.mpr (Or.inl hli))
                · by_cases hlj : l = j
                  · subst l
                    simp
                  · rw [Function.update_of_ne hlj]
                    apply hxyi l
                    apply Finset.mem_insert_of_mem
                    rw [H.mem_parents]
                    exact ⟨G.mem_parents.mp hl, fun h ↦ hlj h.1⟩
          simpa only [hki] using hi
        · apply M.toFactorization.local_factor k
          intro l hl
          apply hxy l
          rcases Finset.mem_insert.mp hl with hl | hl
          · exact Finset.mem_insert.mpr (Or.inl hl)
          · apply Finset.mem_insert_of_mem
            rw [H.mem_parents]
            refine ⟨G.mem_parents.mp hl, ?_⟩
            rintro ⟨rfl, rfl⟩
            exact hki rfl }
  let τG := canonicalTopologicalRanking G
  let τ : TopologicalRanking H :=
    { rank := τG.rank
      injective_rank := τG.injective_rank
      edge_lt := fun h ↦ τG.edge_lt h.1 }
  let C := (G.parents i).erase j
  have hparents : H.parents i = C := by
    ext k
    simp only [H.mem_parents, C, G.mem_parents, Finset.mem_erase]
    constructor
    · rintro ⟨hk, hdel⟩
      exact ⟨fun hkj ↦ hdel ⟨hkj, rfl⟩, hk⟩
    · rintro ⟨hkj, hk⟩
      exact ⟨hk, fun h ↦ hkj h.1⟩
  have hCpred : C ⊆ predecessors τ i := by
    intro k hk
    rw [predecessors, Finset.mem_filter]
    exact ⟨Finset.mem_univ k, τG.edge_lt (G.mem_parents.mp (Finset.mem_of_mem_erase hk))⟩
  have hmarkov := B.orderedLocalMarkov τ i C hCpred (by simpa [hparents])
  have hjpred : j ∈ predecessors τ i := by
    rw [predecessors, Finset.mem_filter]
    exact ⟨Finset.mem_univ j, τG.edge_lt hji⟩
  have hjC : j ∉ C := by simp [C]
  let e : (∀ k : ↑(predecessors τ i \ C), X k) → X j :=
    fun z ↦ z ⟨j, Finset.mem_sdiff.mpr ⟨hjpred, hjC⟩⟩
  have hcomp := hmarkov.comp measurable_id (measurable_pi_apply
    (⟨j, Finset.mem_sdiff.mpr ⟨hjpred, hjC⟩⟩ : ↑(predecessors τ i \ C)))
  have heval : e ∘ coordinateProjection (X := X) (predecessors τ i \ C) =
      fun x : ∀ k, X k ↦ x j := by
    funext x
    rfl
  rw [heval] at hcomp
  change CondIndepFun
    (MeasurableSpace.comap (coordinateProjection (X := X) C) inferInstance)
    (coordinateConditioning_comap_le (X := X) C)
    (fun x : ∀ k, X k ↦ x i) (fun x : ∀ k, X k ↦ x j)
    M.observationalMeasure
  simp only [Function.id_comp] at hcomp
  have hmeasure : B.observationalMeasure = M.observationalMeasure := by
    rfl
  cases hmeasure
  exact hcomp

/-- For an edge `j → i`, reference-almost-everywhere independence of the child's local factor
from `j` implies conditional independence of the endpoints given the other parents. -/
theorem edge_condIndep_of_aeFactorIndependent {i j : V} (hji : G.edge j i) :
    M.AEFactorIndependentOf i j →
      M.CondIndepCoordinates i j ((G.parents i).erase j) := by
  intro h
  exact M.edge_condIndep_of_factorIndependent hji
    (M.factorIndependent_of_aeFactorIndependent h)

/-- For an edge `j → i` in a compact positive DAG density, conditional independence of `i` and
`j` given the other parents is equivalent to reference-almost-everywhere independence of the
child's local factor from `j`. -/
theorem edge_condIndep_iff_aeFactorIndependent {i j : V} (hji : G.edge j i) :
    M.CondIndepCoordinates i j ((G.parents i).erase j) ↔
      M.AEFactorIndependentOf i j := by
  exact ⟨M.aeFactorIndependent_of_edge_condIndep hji,
    M.edge_condIndep_of_aeFactorIndependent hji⟩

/-- A [compact positive factorization](hyp:M) and [directed edge](hyp:hji) have [conditional
independence of its endpoints given the child's other parents exactly when the child's local
factor is pointwise unchanged by changing the parent coordinate](goal). -/
theorem edge_condIndep_iff_factorIndependent {i j : V} (hji : G.edge j i) :
    M.CondIndepCoordinates i j ((G.parents i).erase j) ↔ M.FactorIndependentOf i j := by
  exact (M.edge_condIndep_iff_aeFactorIndependent hji).trans
    M.aeFactorIndependent_iff_factorIndependent

/-- Pointwise independence of a child's factor from a parent coordinate forces every associated
four-point local cross-product contrast to vanish. -/
theorem localContrast_zero_of_factorIndependent {i j : V} (hji : G.edge j i) :
    M.FactorIndependentOf i j →
      ∀ (x : ∀ k, X k) (xi xi' : X i) (xj xj' : X j),
        M.localContrast i j x xi xi' xj xj' = 0 := by
  /- Rewrite all four factor values to a fixed value of coordinate `j`; `hji` supplies `i ≠ j`
  so the own-coordinate update is not disturbed. -/
  intro h x xi xi' xj xj'
  have hij : i ≠ j := by
    intro hij
    subst j
    exact G.irrefl i hji
  have hsection (z : X i) (w : X j) :
      M.toFactorization.factor i
          (Function.update (Function.update x j w) i z) =
        M.toFactorization.factor i (Function.update x i z) := by
    rw [← Function.update_comm hij]
    exact h (Function.update x i z) w
  unfold localContrast
  simp_rw [Function.update_comm hij]
  rw [hsection xi xj, hsection xi' xj', hsection xi xj', hsection xi' xj]
  ring

/-- If every four-point local cross-product contrast for an edge vanishes, normalization and
strict positivity force the child's factor to be independent of that parent coordinate. -/
theorem factorIndependent_of_localContrast_zero {i j : V} (hji : G.edge j i) :
    (∀ (x : ∀ k, X k) (xi xi' : X i) (xj xj' : X j),
        M.localContrast i j x xi xi' xj xj' = 0) →
      M.FactorIndependentOf i j := by
  /- Fix the base assignment and the new `j` value.  The contrast equations say the two positive
  own-coordinate density sections are proportional.  Integrate the equations in the second
  own-coordinate variable and use `normalized_factor` twice; the proportionality constant is
  one.  Finiteness reflects the real calculation back to `ENNReal`. -/
  intro h x xj
  have hij : i ≠ j := by
    intro hij
    subst j
    exact G.irrefl i hji
  let a : X i → ℝ≥0∞ := fun z ↦
    M.toFactorization.factor i
      (Function.update (Function.update x j xj) i z)
  let b : X i → ℝ≥0∞ := fun z ↦
    M.toFactorization.factor i (Function.update x i z)
  have ha_meas : Measurable a :=
    (M.toFactorization.measurable_factor i).comp
      (measurable_update (Function.update x j xj))
  have hb_meas : Measurable b :=
    (M.toFactorization.measurable_factor i).comp (measurable_update x)
  have hab (z w : X i) : a z * b w = b z * a w := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.mul_ne_top
        (M.factor_ne_top i (Function.update (Function.update x j xj) i z))
        (M.factor_ne_top i (Function.update x i w)))
      (ENNReal.mul_ne_top
        (M.factor_ne_top i (Function.update x i z))
        (M.factor_ne_top i (Function.update (Function.update x j xj) i w)))).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
    apply sub_eq_zero.mp
    simpa [localContrast, a, b, Function.update_comm hij] using
      h x z w xj (x j)
  have ha_norm : ∫⁻ z, a z ∂μ i = 1 := by
    exact M.toFactorization.normalized_factor i (Function.update x j xj)
  have hb_norm : ∫⁻ z, b z ∂μ i = 1 := by
    exact M.toFactorization.normalized_factor i x
  have hab_eq (z : X i) : a z = b z := by
    have hint : a z * (∫⁻ w, b w ∂μ i) = b z * (∫⁻ w, a w ∂μ i) := by
      calc
        a z * (∫⁻ w, b w ∂μ i) = ∫⁻ w, a z * b w ∂μ i := by
          exact (lintegral_const_mul (a z) hb_meas).symm
        _ = ∫⁻ w, b z * a w ∂μ i := lintegral_congr (hab z)
        _ = b z * (∫⁻ w, a w ∂μ i) := by
          exact lintegral_const_mul (b z) ha_meas
    simpa [ha_norm, hb_norm] using hint
  have hz := hab_eq (x i)
  change M.toFactorization.factor i
      (Function.update (Function.update x j xj) i (x i)) =
    M.toFactorization.factor i (Function.update x i (x i)) at hz
  rw [Function.update_eq_self] at hz
  have hcoord : Function.update x j xj i = x i := Function.update_of_ne hij _ _
  rw [← hcoord, Function.update_eq_self] at hz
  exact hz

/-- For an edge `j → i`, pointwise independence of the child's factor from `j` is equivalent to
vanishing of all its local four-point cross-product contrasts. -/
theorem factorIndependent_iff_localContrast_zero {i j : V} (hji : G.edge j i) :
    M.FactorIndependentOf i j ↔
      ∀ (x : ∀ k, X k) (xi xi' : X i) (xj xj' : X j),
        M.localContrast i j x xi xi' xj xj' = 0 := by
  exact ⟨M.localContrast_zero_of_factorIndependent hji,
    M.factorIndependent_of_localContrast_zero hji⟩

/-- For an edge `j → i`, conditional independence given the other parents is equivalent to
vanishing of every local factor cross-product contrast. -/
theorem edge_condIndep_iff_localContrast_zero {i j : V} (hji : G.edge j i) :
    M.CondIndepCoordinates i j ((G.parents i).erase j) ↔
      ∀ (x : ∀ k, X k) (xi xi' : X i) (xj xj' : X j),
        M.localContrast i j x xi xi' xj xj' = 0 := by
  exact (M.edge_condIndep_iff_factorIndependent hji).trans
    (M.factorIndependent_iff_localContrast_zero hji)

end CompactPositiveFactorization

end Causalean.Graph.FiniteDensity
