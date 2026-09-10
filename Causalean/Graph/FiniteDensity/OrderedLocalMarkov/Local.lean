import Causalean.Graph.FiniteDensity.OrderedLocalMarkov.Coordinates
import Causalean.Mathlib.CondIndep.ThreeBlockDensity
import Causalean.Mathlib.CondIndep
import Causalean.Mathlib.CondDistrib

/-!
# Density-factorization local Markov core

This module isolates the analytic core: under a finite DAG density factorization, a coordinate is
conditionally independent of any parent-closed block omitting it after its parents are removed,
given its parents.  The proof is intended to combine reverse-topological marginalization with a
three-block density factorization and Mathlib's conditional-independence characterization.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Graph.FiniteDensity

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {X : V → Type*} [∀ i, MeasurableSpace (X i)]
  [∀ i, StandardBorelSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
variable {G : Causalean.DAG V}

private theorem map_coordinateProjection_withDensity_eq_marginal
    (S : Finset V) (f : (∀ j, X j) → ℝ≥0∞) (hf : Measurable f)
    (x₀ : ∀ j, X j) :
    Measure.map (coordinateProjection (X := X) S)
        ((Measure.pi μ).withDensity f) =
      (Measure.pi (fun j : S ↦ μ j)).withDensity
        (fun z ↦ (∫⋯∫⁻_(Finset.univ \ S), f ∂μ)
          (coordinateExtension S x₀ z)) := by
  ext A hA
  have hproj : Measurable (coordinateProjection (X := X) S) :=
    measurable_coordinateProjection S
  have hext : Measurable (coordinateExtension (X := X) S x₀) :=
    measurable_coordinateExtension S x₀
  have hmarg : Measurable (∫⋯∫⁻_(Finset.univ \ S), f ∂μ) := hf.lmarginal μ
  rw [Measure.map_apply hproj hA,
    withDensity_apply _ (hproj hA), withDensity_apply _ hA]
  rw [← lintegral_indicator (hproj hA), ← lintegral_indicator hA]
  let F : (∀ j, X j) → ℝ≥0∞ :=
    (coordinateProjection (X := X) S ⁻¹' A).indicator f
  have hF : Measurable F := hf.indicator (hproj hA)
  change (∫⁻ x, F x ∂Measure.pi μ) = _
  rw [MeasureTheory.lintegral_eq_lmarginal_univ x₀]
  have huniv : S ∪ (Finset.univ \ S) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ S)
  have hsplit := congrFun
    (MeasureTheory.lmarginal_union (s := S) (t := Finset.univ \ S)
      μ F hF Finset.disjoint_sdiff) x₀
  rw [huniv] at hsplit
  rw [hsplit]
  simp only [MeasureTheory.lmarginal]
  apply lintegral_congr
  intro z
  change (∫⁻ y, F (Function.updateFinset
      (coordinateExtension S x₀ z) (Finset.univ \ S) y)
      ∂Measure.pi fun j : ↥(Finset.univ \ S) ↦ μ j) = _
  have hproj_update (y : ∀ j : ↥(Finset.univ \ S), X j) :
      coordinateProjection (X := X) S
          (Function.updateFinset (coordinateExtension S x₀ z)
            (Finset.univ \ S) y) = z := by
    funext j
    simp [coordinateProjection, coordinateExtension,
      Function.updateFinset_def, j.property]
  by_cases hz : z ∈ A
  · have hmem : ∀ y : ∀ j : ↥(Finset.univ \ S), X j,
        Function.updateFinset (coordinateExtension S x₀ z)
            (Finset.univ \ S) y ∈ coordinateProjection (X := X) S ⁻¹' A := by
      intro y
      simpa [hproj_update y] using hz
    simp only [F, Set.indicator, hz, if_pos]
    simp_rw [if_pos (hmem _)]
  · have hmem : ∀ y : ∀ j : ↥(Finset.univ \ S), X j,
        Function.updateFinset (coordinateExtension S x₀ z)
            (Finset.univ \ S) y ∉ coordinateProjection (X := X) S ⁻¹' A := by
      intro y h
      exact hz (hproj_update y ▸ h)
    simp only [F, Set.indicator, hz, if_false]
    simp_rw [if_neg (hmem _)]
    exact lintegral_zero

private theorem map_withDensity_equiv_of_measurePreserving
    {A D : Type*} [MeasurableSpace A] [MeasurableSpace D]
    (e : A ≃ᵐ D) {ν : Measure A} {ξ : Measure D}
    (he : MeasurePreserving e ν ξ) (d : A → ℝ≥0∞) (hd : Measurable d) :
    Measure.map e (ν.withDensity d) =
      ξ.withDensity (d ∘ e.symm) := by
  classical
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (e.measurable hs), ← lintegral_indicator hs]
  rw [he.lintegral_map_equiv
    (s.indicator (d ∘ e.symm)) e]
  apply lintegral_congr
  intro a
  change (if e a ∈ s then d a else 0) =
    if e a ∈ s then d (e.symm (e a)) else 0
  simp

private theorem condIndepFun_comp_of_map
    {A D Y Z C : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace D] [StandardBorelSpace D]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    [MeasurableSpace C]
    {φ : A → D} (hφ : Measurable φ)
    {y : D → Y} (hy : Measurable y)
    {z : D → Z} (hz : Measurable z)
    {c : D → C} (hc : Measurable c)
    {ν : Measure A} [IsFiniteMeasure ν]
    [IsFiniteMeasure (ν.map φ)]
    (h : CondIndepFun
      (MeasurableSpace.comap c inferInstance) hc.comap_le
      y z (ν.map φ)) :
    CondIndepFun
      (MeasurableSpace.comap (c ∘ φ) inferInstance)
      (hc.comp hφ).comap_le (y ∘ φ) (z ∘ φ) ν := by
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
    (hz.comp hφ) (hy.comp hφ) (hc.comp hφ)]
  have hjoint := (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
    (μ := ν.map φ) (f := z) (g := y) (k := c) hz hy hc).mp h
  have hpair : Measurable (fun d : D ↦ (c d, y d)) := hc.prodMk hy
  have htr_pair := Causalean.condDistrib_map_comp (𝒴 := Z) ν
    (φ := φ) (g := z) (f := fun d : D ↦ (c d, y d))
    hφ hz hpair
  have htr_c := Causalean.condDistrib_map_comp (𝒴 := Z) ν
    (φ := φ) (g := z) (f := c) hφ hz hc
  have hmap_pair : (ν.map φ).map (fun d : D ↦ (c d, y d)) =
      ν.map (fun a : A ↦ ((c ∘ φ) a, (y ∘ φ) a)) := by
    rw [Measure.map_map hpair hφ]
    rfl
  have hmap_c : (ν.map φ).map c = ν.map (c ∘ φ) := by
    rw [Measure.map_map hc hφ]
  rw [hmap_pair] at hjoint htr_pair
  rw [hmap_c] at htr_c
  have htr_c_fst :
      (fun p : C × Y ↦ condDistrib z c (ν.map φ) p.1)
        =ᵐ[ν.map (fun a : A ↦ ((c ∘ φ) a, (y ∘ φ) a))]
          fun p : C × Y ↦ condDistrib (z ∘ φ) (c ∘ φ) ν p.1 := by
    have hfst :
        (ν.map (fun a : A ↦ ((c ∘ φ) a, (y ∘ φ) a))).map Prod.fst =
          ν.map (c ∘ φ) := by
      rw [Measure.map_map measurable_fst ((hc.comp hφ).prodMk (hy.comp hφ))]
      rfl
    exact ae_eq_comp
      (μ := ν.map (fun a : A ↦ ((c ∘ φ) a, (y ∘ φ) a)))
      (f := Prod.fst) (g := fun c₀ ↦ condDistrib z c (ν.map φ) c₀)
      (g' := fun c₀ ↦ condDistrib (z ∘ φ) (c ∘ φ) ν c₀)
      measurable_fst.aemeasurable (by rw [hfst]; exact htr_c)
  filter_upwards [htr_pair.symm, hjoint, htr_c_fst] with p hp_pair hp_joint hp_c
  change (condDistrib (z ∘ φ) ((fun d : D ↦ (c d, y d)) ∘ φ) ν) p = _
  rw [hp_pair, hp_joint, Kernel.prodMkRight_apply, hp_c,
    Kernel.prodMkRight_apply]

/-- For a [finite DAG density factorization](hyp:B), a [parent-closed coordinate block](hyp:hP),
and a [vertex omitted from that block](hyp:hi), [the vertex coordinate is conditionally independent
of the block's non-parent coordinates given its parent coordinates](goal). -/
theorem Factorization.localMarkovParents_of_parentClosed
    (B : Factorization G X μ) {i : V} {P : Finset V}
    (hP : ParentClosed G P) (hi : i ∉ P) :
    CondIndepFun
      (MeasurableSpace.comap
        (coordinateProjection (X := X) (G.parents i)) inferInstance)
      (coordinateConditioning_comap_le (X := X) (G.parents i))
      (fun x : ∀ j, X j ↦ x i)
      (coordinateProjection (X := X) (P \ G.parents i))
      B.observationalMeasure := by
  classical
  by_cases hfull : Nonempty (∀ j, X j)
  · let x₀ : ∀ j, X j := Classical.choice hfull
    let R : Finset V := P ∪ nodeAncestralClosure G i
    let C : Finset V := G.parents i
    let Z : Finset V := R \ insert i C
    let I : Finset V := {i}
    let S : Finset V := I ∪ (Z ∪ C)
    have hiR : i ∈ R := by
      simp [R, nodeAncestralClosure]
    have hCR : C ⊆ R := by
      intro j hj
      exact Finset.mem_union_right P
        (selfParents_subset_nodeAncestralClosure i
          (Finset.mem_insert_of_mem (by simpa [C] using hj)))
    have hiC : i ∉ C := by
      simpa [C, Causalean.DAG.mem_parents] using G.irrefl i
    have hSR : S = R := by
      ext j
      simp only [S, I, Z, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro (rfl | (⟨hjR, _⟩ | hjC))
        · exact hiR
        · exact hjR
        · exact hCR hjC
      · intro hjR
        by_cases hji : j = i
        · exact Or.inl hji
        · by_cases hjC : j ∈ C
          · exact Or.inr (Or.inr hjC)
          · exact Or.inr (Or.inl ⟨hjR, by simp [hji, hjC]⟩)
    have hRclosed : ParentClosed G R := by
      intro j hj k hk
      rcases Finset.mem_union.mp hj with hjP | hjA
      · exact Finset.mem_union_left _ (hP hjP hk)
      · exact Finset.mem_union_right _
          (parentClosed_nodeAncestralClosure i hjA hk)
    have hSclosed : ParentClosed G S := hSR ▸ hRclosed
    have hnochild : ∀ j ∈ R, j ≠ i → i ∉ G.parents j := by
      intro j hjR hji hij
      rcases Finset.mem_union.mp hjR with hjP | hjA
      · exact hi (hP hjP hij)
      · have hjiA : G.isAncestor j i :=
          (mem_nodeAncestralClosure_iff.mp hjA).resolve_left hji
        exact G.isAncestor_irrefl i
          (G.isAncestor_trans (Causalean.DAG.isAncestor.edge
            (G.mem_parents.mp hij)) hjiA)
    have hZC : Disjoint Z C := by
      apply Finset.disjoint_left.mpr
      intro j hjZ hjC
      simp only [Z, Finset.mem_sdiff] at hjZ
      exact hjZ.2 (Finset.mem_insert_of_mem hjC)
    have hIZC : Disjoint I (Z ∪ C) := by
      apply Finset.disjoint_left.mpr
      intro j hjI hj
      have hji : j = i := by simpa [I] using hjI
      subst j
      rcases Finset.mem_union.mp hj with hjZ | hjC
      · simp only [Z, Finset.mem_sdiff] at hjZ
        exact hjZ.2 (Finset.mem_insert_self i C)
      · exact hiC hjC
    let eZC :
        ((∀ j : Z, X j) × (∀ j : C, X j)) ≃ᵐ
          (∀ j : ↥(Z ∪ C), X j) :=
      MeasurableEquiv.piFinsetUnion X hZC
    let e :
        ((∀ j : I, X j) × ((∀ j : Z, X j) × (∀ j : C, X j))) ≃ᵐ
          (∀ j : S, X j) :=
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) eZC).trans
        (MeasurableEquiv.piFinsetUnion X hIZC)
    let refI : Measure (∀ j : I, X j) := Measure.pi fun j : I ↦ μ j
    let refZ : Measure (∀ j : Z, X j) := Measure.pi fun j : Z ↦ μ j
    let refC : Measure (∀ j : C, X j) := Measure.pi fun j : C ↦ μ j
    let refS : Measure (∀ j : S, X j) := Measure.pi fun j : S ↦ μ j
    have he : MeasurePreserving e (refI.prod (refZ.prod refC)) refS := by
      have heZC := measurePreserving_piFinsetUnion hZC μ
      have heProd := (MeasurePreserving.id refI).prod heZC
      have heOuter := measurePreserving_piFinsetUnion hIZC μ
      refine ⟨e.measurable, ?_⟩
      have hm := (heOuter.comp heProd).map_eq
      change Measure.map e (refI.prod (refZ.prod refC)) = refS
      have hefun : (e :
          ((∀ j : I, X j) × ((∀ j : Z, X j) × (∀ j : C, X j))) →
            (∀ j : S, X j)) =
          fun q ↦ (MeasurableEquiv.piFinsetUnion X hIZC)
            (q.1, eZC q.2) := by
        funext q
        rfl
      rw [hefun]
      simpa [S, eZC, refI, refZ, refC, refS, Prod.map,
        Function.comp_def] using hm
    let ext (q : (∀ j : I, X j) × ((∀ j : Z, X j) × (∀ j : C, X j))) :
        ∀ j, X j := coordinateExtension S x₀ (e q)
    have ext_I (q : (∀ j : I, X j) × ((∀ j : Z, X j) × (∀ j : C, X j)))
        (j : I) : ext q j = q.1 j := by
      have hjS : (j : V) ∈ S :=
        Finset.mem_union_left _ j.property
      unfold ext coordinateExtension
      rw [dif_pos hjS]
      change (Equiv.piFinsetUnion X hIZC)
          (q.1, eZC q.2) ⟨j, hjS⟩ = q.1 j
      exact Equiv.piFinsetUnion_left X hIZC j.property hjS
    have ext_Z (q : (∀ j : I, X j) × ((∀ j : Z, X j) × (∀ j : C, X j)))
        (j : Z) : ext q j = q.2.1 j := by
      have hjZC : (j : V) ∈ Z ∪ C := Finset.mem_union_left _ j.property
      have hjS : (j : V) ∈ S := Finset.mem_union_right _ hjZC
      unfold ext coordinateExtension
      rw [dif_pos hjS]
      change (Equiv.piFinsetUnion X hIZC)
          (q.1, eZC q.2) ⟨j, hjS⟩ = q.2.1 j
      rw [Equiv.piFinsetUnion_right X hIZC hjZC hjS]
      change (Equiv.piFinsetUnion X hZC) q.2 ⟨j, hjZC⟩ = q.2.1 j
      exact Equiv.piFinsetUnion_left X hZC j.property hjZC
    have ext_C (q : (∀ j : I, X j) × ((∀ j : Z, X j) × (∀ j : C, X j)))
        (j : C) : ext q j = q.2.2 j := by
      have hjZC : (j : V) ∈ Z ∪ C := Finset.mem_union_right _ j.property
      have hjS : (j : V) ∈ S := Finset.mem_union_right _ hjZC
      unfold ext coordinateExtension
      rw [dif_pos hjS]
      change (Equiv.piFinsetUnion X hIZC)
          (q.1, eZC q.2) ⟨j, hjS⟩ = q.2.2 j
      rw [Equiv.piFinsetUnion_right X hIZC hjZC hjS]
      change (Equiv.piFinsetUnion X hZC) q.2 ⟨j, hjZC⟩ = q.2.2 j
      exact Equiv.piFinsetUnion_right X hZC j.property hjZC
    let d := fun q : (∀ j : I, X j) × ((∀ j : Z, X j) × (∀ j : C, X j)) ↦
      B.partialDensity S (ext q)
    have hd : Measurable d := by
      unfold d ext
      fun_prop
    let y₀ : ∀ j : I, X j := fun j ↦ x₀ j
    let z₀ : ∀ j : Z, X j := fun j ↦ x₀ j
    let a := fun q : (∀ j : I, X j) × (∀ j : C, X j) ↦
      B.factor i (ext (q.1, (z₀, q.2)))
    let b := fun q : (∀ j : Z, X j) × (∀ j : C, X j) ↦
      B.partialDensity (S.erase i) (ext (y₀, q))
    have ha : Measurable a := by
      unfold a ext
      exact (B.measurable_factor i).comp
        ((measurable_coordinateExtension S x₀).comp
          (e.measurable.comp
            (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))))
    have hb : Measurable b := by
      unfold b ext
      exact (B.measurable_partialDensity (S.erase i)).comp
        ((measurable_coordinateExtension S x₀).comp
          (e.measurable.comp
            (measurable_const.prodMk measurable_id)))
    have hfactor : d = fun q ↦ a (q.1, q.2.2) * b (q.2.1, q.2.2) := by
      funext q
      have hiI : i ∈ I := by simp [I]
      have hiS : i ∈ S := Finset.mem_union_left _ hiI
      have hfirst : B.factor i (ext q) =
          B.factor i (ext (q.1, (z₀, q.2.2))) := by
        apply B.local_factor i
        intro k hk
        rcases Finset.mem_insert.mp hk with hki | hkC
        · subst k
          exact ext_I q ⟨i, hiI⟩ |>.trans
            (ext_I (q.1, (z₀, q.2.2)) ⟨i, hiI⟩).symm
        · exact ext_C q ⟨k, by simpa [C] using hkC⟩ |>.trans
            (ext_C (q.1, (z₀, q.2.2))
              ⟨k, by simpa [C] using hkC⟩).symm
      have hrest : B.partialDensity (S.erase i) (ext q) =
          B.partialDensity (S.erase i) (ext (y₀, (q.2.1, q.2.2))) := by
        unfold Factorization.partialDensity
        apply Finset.prod_congr rfl
        intro j hj
        apply B.local_factor j
        have hj' := Finset.mem_erase.mp hj
        have hjS : j ∈ S := hj'.2
        have hji : j ≠ i := hj'.1
        have hjR : j ∈ R := hSR ▸ hjS
        have hij : i ∉ G.parents j := hnochild j hjR hji
        intro k hk
        have hkS : k ∈ S := by
          rcases Finset.mem_insert.mp hk with rfl | hkj
          · exact hjS
          · exact hSclosed hjS hkj
        have hki : k ≠ i := by
          rcases Finset.mem_insert.mp hk with hkj | hkp
          · exact hkj.trans_ne hji
          · exact fun h ↦ hij (h ▸ hkp)
        rcases Finset.mem_union.mp hkS with hkI | hkZC
        · have hki' : k = i := by simpa [I] using hkI
          exact (hki hki').elim
        · rcases Finset.mem_union.mp hkZC with hkZ | hkC
          · exact ext_Z q ⟨k, hkZ⟩ |>.trans
              (ext_Z (y₀, (q.2.1, q.2.2)) ⟨k, hkZ⟩).symm
          · exact ext_C q ⟨k, hkC⟩ |>.trans
              (ext_C (y₀, (q.2.1, q.2.2)) ⟨k, hkC⟩).symm
      unfold d a b
      calc
        B.partialDensity S (ext q) =
            B.factor i (ext q) * B.partialDensity (S.erase i) (ext q) := by
          unfold Factorization.partialDensity
          exact (Finset.mul_prod_erase S (fun j ↦ B.factor j (ext q)) hiS).symm
        _ = B.factor i (ext (q.1, (z₀, q.2.2))) *
            B.partialDensity (S.erase i) (ext (y₀, (q.2.1, q.2.2))) := by
          rw [hfirst, hrest]
    let φ : (∀ j, X j) →
        ((∀ j : I, X j) × ((∀ j : Z, X j) × (∀ j : C, X j))) :=
      e.symm ∘ coordinateProjection S
    have hφ : Measurable φ := e.symm.measurable.comp
      (measurable_coordinateProjection S)
    have hlaw : Measure.map φ B.observationalMeasure =
        (refI.prod (refZ.prod refC)).withDensity d := by
      let dS : (∀ j : S, X j) → ℝ≥0∞ :=
        fun z ↦ B.partialDensity S (coordinateExtension S x₀ z)
      have hdS : Measurable dS := by
        unfold dS
        exact (B.measurable_partialDensity S).comp
          (measurable_coordinateExtension S x₀)
      have hproj := map_coordinateProjection_withDensity_eq_marginal
        (X := X) (μ := μ)
        S B.observationalDensity B.measurable_observationalDensity x₀
      rw [B.lmarginal_compl_observationalDensity_eq hSclosed] at hproj
      change Measure.map (coordinateProjection (X := X) S) B.observationalMeasure =
        refS.withDensity dS at hproj
      calc
        Measure.map φ B.observationalMeasure =
            Measure.map e.symm
              (Measure.map (coordinateProjection (X := X) S)
                B.observationalMeasure) := by
          symm
          simpa [φ, Function.comp_def] using
            Measure.map_map e.symm.measurable
              (measurable_coordinateProjection S)
              (μ := B.observationalMeasure)
        _ = Measure.map e.symm (refS.withDensity dS) := by rw [hproj]
        _ = (refI.prod (refZ.prod refC)).withDensity d := by
          have heSymm : MeasurePreserving e.symm refS
              (refI.prod (refZ.prod refC)) :=
            MeasurePreserving.symm e he
          simpa [dS, d, ext, Function.comp_def] using
            map_withDensity_equiv_of_measurePreserving e.symm heSymm dS hdS
    have hfinite : IsFiniteMeasure
        ((refI.prod (refZ.prod refC)).withDensity d) := by
      rw [← hlaw]
      infer_instance
    letI : IsFiniteMeasure
        ((refI.prod (refZ.prod refC)).withDensity d) := hfinite
    have hciQ := condIndepFun_threeBlock_of_density_factors
      refI refZ refC hd a b ha hb (Filter.Eventually.of_forall (congrFun hfactor))
    have hciMap : CondIndepFun
        (MeasurableSpace.comap (fun q :
          (∀ j : I, X j) × ((∀ j : Z, X j) × (∀ j : C, X j)) ↦ q.2.2)
          inferInstance)
        ((measurable_snd.comp measurable_snd).comap_le)
        (fun q ↦ q.1) (fun q ↦ q.2.1) (Measure.map φ B.observationalMeasure) := by
      simpa only [hlaw] using hciQ
    letI : Nonempty (∀ j : I, X j) := ⟨fun j ↦ x₀ j⟩
    letI : Nonempty (∀ j : Z, X j) := ⟨fun j ↦ x₀ j⟩
    have hciFull := condIndepFun_comp_of_map hφ measurable_fst
      (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd) hciMap
    have hφBlocks : φ = fun x ↦
        (coordinateProjection (X := X) I x,
          (coordinateProjection (X := X) Z x,
            coordinateProjection (X := X) C x)) := by
      funext x
      apply e.injective
      change e (e.symm (coordinateProjection S x)) = _
      rw [e.apply_symm_apply]
      funext j
      by_cases hjI : (j : V) ∈ I
      · change x j = (Equiv.piFinsetUnion X hIZC)
            (coordinateProjection I x,
              eZC (coordinateProjection Z x, coordinateProjection C x)) j
        rw [Equiv.piFinsetUnion_left X hIZC hjI j.property]
        rfl
      · have hjZC : (j : V) ∈ Z ∪ C := by
          exact (Finset.mem_union.mp j.property).resolve_left hjI
        rw [show e (coordinateProjection I x,
              (coordinateProjection Z x, coordinateProjection C x)) j =
            eZC (coordinateProjection Z x, coordinateProjection C x)
              ⟨j, hjZC⟩ by
          change (MeasurableEquiv.piFinsetUnion X hIZC)
              (coordinateProjection I x,
                eZC (coordinateProjection Z x, coordinateProjection C x)) j = _
          exact Equiv.piFinsetUnion_right X hIZC hjZC j.property]
        rcases Finset.mem_union.mp hjZC with hjZ | hjC
        · rw [show eZC (coordinateProjection Z x, coordinateProjection C x)
                ⟨j, hjZC⟩ = coordinateProjection Z x ⟨j, hjZ⟩ by
              exact Equiv.piFinsetUnion_left X hZC hjZ hjZC]
          rfl
        · rw [show eZC (coordinateProjection Z x, coordinateProjection C x)
                ⟨j, hjZC⟩ = coordinateProjection C x ⟨j, hjC⟩ by
              exact Equiv.piFinsetUnion_right X hZC hjC hjZC]
          rfl
    have hφI : Prod.fst ∘ φ = coordinateProjection (X := X) I := by
      rw [hφBlocks]
      rfl
    have hφZ : (Prod.fst ∘ Prod.snd) ∘ φ =
        coordinateProjection (X := X) Z := by
      rw [hφBlocks]
      rfl
    have hφC : (Prod.snd ∘ Prod.snd) ∘ φ =
        coordinateProjection (X := X) C := by
      rw [hφBlocks]
      rfl
    have hciFull' : CondIndepFun
        (MeasurableSpace.comap (coordinateProjection (X := X) C) inferInstance)
        (coordinateConditioning_comap_le (X := X) C)
        (coordinateProjection (X := X) I)
        (coordinateProjection (X := X) Z) B.observationalMeasure := by
      simpa only [hφI, hφZ, hφC] using hciFull
    let evalI : (∀ j : I, X j) → X i :=
      fun y ↦ y ⟨i, by simp [I]⟩
    have hevalI : Measurable evalI := measurable_pi_apply _
    let restrictZ : (∀ j : Z, X j) → (∀ j : ↥(P \ C), X j) :=
      fun z j ↦ z ⟨j, by
        have hj := j.property
        simp only [Finset.mem_sdiff] at hj
        simp only [Z, Finset.mem_sdiff]
        exact ⟨Finset.mem_union_left _ hj.1, by
          intro hmem
          rcases Finset.mem_insert.mp hmem with hji | hjC
          · exact hi (hji ▸ hj.1)
          · exact hj.2 hjC⟩⟩
    have hrestrictZ : Measurable restrictZ := by
      unfold restrictZ
      fun_prop
    have hci := hciFull'.comp hevalI hrestrictZ
    change CondIndepFun
      (MeasurableSpace.comap
        (coordinateProjection (X := X) (G.parents i)) inferInstance)
      (coordinateConditioning_comap_le (X := X) (G.parents i))
      (fun x : ∀ j, X j ↦ x i)
      (fun x : ∀ j, X j ↦ fun j : ↥(P \ G.parents i) ↦ x j)
      B.observationalMeasure
    simpa [evalI, restrictZ, I, C, Function.comp_def,
      coordinateProjection] using hci
  · letI : IsEmpty (∀ j, X j) := not_nonempty_iff.mp hfull
    rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
      (measurable_pi_apply i) (measurable_coordinateProjection _)]
    intro s t hs ht
    exact ae_of_all _ fun x ↦ isEmptyElim x

end Causalean.Graph.FiniteDensity
