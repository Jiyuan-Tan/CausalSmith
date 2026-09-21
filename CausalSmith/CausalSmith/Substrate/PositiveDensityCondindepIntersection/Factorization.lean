module
public import CausalSmith.Substrate.PositiveDensityCondindepIntersection.ThreeBlockFactorization

/-!
# Conditional independence as density factorization

This module gives the three product-density factorization characterizations needed by the
intersection proof.  They deliberately use the same canonical four-block product measure, so
the subsequent splicing argument does not have to transport almost-everywhere statements across
ad hoc reorderings.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace CausalSmith.Substrate.PositiveDensityCondindepIntersection

universe uX uY uV uZ

private theorem map_withDensity_comp_of_measurePreservingEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) {μ : Measure α} {ν : Measure β}
    (he : MeasurePreserving e μ ν) (d : β → ℝ≥0∞) (hd : Measurable d) :
    (μ.withDensity (d ∘ e)).map e = ν.withDensity d := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator (e.measurable hs), ← lintegral_indicator hs]
  have h := he.lintegral_comp (hd.indicator hs)
  convert h using 1 <;> rfl

private theorem condIndepFun_of_map_local
    {α β γ δ ε : Type*}
    [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace β] [StandardBorelSpace β]
    [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
    [MeasurableSpace ε]
    {φ : α → β} (hφ : Measurable φ)
    {X : β → γ} (hX : Measurable X) {Y : β → δ} (hY : Measurable Y)
    {Z : β → ε} (hZ : Measurable Z)
    {ν : Measure α} [IsFiniteMeasure ν] [IsFiniteMeasure (ν.map φ)]
    (h : CondIndepFun
      (MeasurableSpace.comap (Z ∘ φ) inferInstance)
      (hZ.comp hφ).comap_le (X ∘ φ) (Y ∘ φ) ν) :
    CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y (ν.map φ) := by
  have hcd1 : condDistrib (Y ∘ φ) (Z ∘ φ) ν = condDistrib Y Z (ν.map φ) := by
    simp only [condDistrib]
    congr 1
    exact (Measure.map_map (hZ.prodMk hY) hφ).symm
  have hcd2 : condDistrib (Y ∘ φ) (fun ω ↦ ((Z ∘ φ) ω, (X ∘ φ) ω)) ν =
      condDistrib Y (fun b ↦ (Z b, X b)) (ν.map φ) := by
    simp only [condDistrib]
    congr 1
    exact (Measure.map_map ((hZ.prodMk hX).prodMk hY) hφ).symm
  have hfilt : ν.map (fun ω ↦ ((Z ∘ φ) ω, (X ∘ φ) ω)) =
      (ν.map φ).map (fun b ↦ (Z b, X b)) :=
    (Measure.map_map (hZ.prodMk hX) hφ).symm
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY hX hZ]
  have h' := (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
    (hY.comp hφ) (hX.comp hφ) (hZ.comp hφ)).mp h
  rw [hcd2, hcd1, hfilt] at h'
  exact h'

private theorem condIndepFun_measurableEquiv_iff
    {α β γ δ ε : Type*}
    [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace β] [StandardBorelSpace β]
    [MeasurableSpace γ] [StandardBorelSpace γ]
    [MeasurableSpace δ] [StandardBorelSpace δ]
    [MeasurableSpace ε]
    (e : α ≃ᵐ β) {ν : Measure α} {μ : Measure β}
    [IsFiniteMeasure ν] [IsFiniteMeasure μ] (he : ν.map e = μ)
    {X : β → γ} (hX : Measurable X) {Y : β → δ} (hY : Measurable Y)
    {Z : β → ε} (hZ : Measurable Z) :
    CondIndepFun
        (MeasurableSpace.comap (Z ∘ e) inferInstance)
        (hZ.comp e.measurable).comap_le (X ∘ e) (Y ∘ e) ν ↔
      CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y μ := by
  cases isEmpty_or_nonempty γ with
  | inl hγ =>
      letI := hγ
      have hs : CondIndepFun
          (MeasurableSpace.comap (Z ∘ e) inferInstance)
          (hZ.comp e.measurable).comap_le (X ∘ e) (Y ∘ e) ν := by
        rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
          (hX.comp e.measurable) (hY.comp e.measurable)]
        intro s t hs ht
        exact ae_of_all _ fun a ↦ isEmptyElim (X (e a))
      have ht : CondIndepFun
          (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y μ := by
        rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY]
        intro s t hs ht
        exact ae_of_all _ fun b ↦ isEmptyElim (X b)
      exact ⟨fun _ ↦ ht, fun _ ↦ hs⟩
  | inr hγ =>
      letI := hγ
      cases isEmpty_or_nonempty δ with
      | inl hδ =>
          letI := hδ
          have hs : CondIndepFun
              (MeasurableSpace.comap (Z ∘ e) inferInstance)
              (hZ.comp e.measurable).comap_le (X ∘ e) (Y ∘ e) ν := by
            rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
              (hX.comp e.measurable) (hY.comp e.measurable)]
            intro s t hs ht
            exact ae_of_all _ fun a ↦ isEmptyElim (Y (e a))
          have ht : CondIndepFun
              (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y μ := by
            rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY]
            intro s t hs ht
            exact ae_of_all _ fun b ↦ isEmptyElim (Y b)
          exact ⟨fun _ ↦ ht, fun _ ↦ hs⟩
      | inr hδ =>
          letI := hδ
          constructor
          · intro h
            simpa only [he] using condIndepFun_of_map_local e.measurable hX hY hZ h
          · intro h
            have he' : μ.map e.symm = ν := by
              rw [← he, Measure.map_map e.symm.measurable e.measurable]
              simpa using congrArg (fun f ↦ Measure.map f ν) e.symm_comp_self
            have h0 : CondIndepFun
                (MeasurableSpace.comap ((Z ∘ e) ∘ e.symm) inferInstance)
                ((hZ.comp e.measurable).comp e.symm.measurable).comap_le
                ((X ∘ e) ∘ e.symm) ((Y ∘ e) ∘ e.symm) μ := by
              simpa only [Function.comp_def, e.apply_symm_apply] using h
            have h' := condIndepFun_of_map_local e.symm.measurable
              (hX.comp e.measurable) (hY.comp e.measurable) (hZ.comp e.measurable) h0
            simpa only [he'] using h'

private def permXV [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace V] [MeasurableSpace Z] :
    (X × (V × (Y × Z))) ≃ᵐ (X × (Y × (V × Z))) where
  toFun q := (q.1, (q.2.2.1, (q.2.1, q.2.2.2)))
  invFun q := (q.1, (q.2.2.1, (q.2.1, q.2.2.2)))
  left_inv q := by cases q with | mk x r => cases r with | mk v r => cases r <;> rfl
  right_inv q := by cases q with | mk x r => cases r with | mk y r => cases r <;> rfl
  measurable_toFun := by
    change Measurable (fun q : X × (V × (Y × Z)) ↦ (q.1, (q.2.2.1, (q.2.1, q.2.2.2))))
    fun_prop
  measurable_invFun := by
    change Measurable (fun q : X × (Y × (V × Z)) ↦ (q.1, (q.2.2.1, (q.2.1, q.2.2.2))))
    fun_prop

private theorem measurePreserving_permXV
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]
    (μX : Measure X) (μY : Measure Y) (μV : Measure V) (μZ : Measure Z)
    [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μV] [SigmaFinite μZ] :
    MeasurePreserving (@permXV X Y V Z _ _ _ _)
      (μX.prod (μV.prod (μY.prod μZ))) (μX.prod (μY.prod (μV.prod μZ))) := by
  have hinner : MeasurePreserving
      (fun r : V × (Y × Z) ↦ (r.2.1, (r.1, r.2.2)))
      (μV.prod (μY.prod μZ)) (μY.prod (μV.prod μZ)) := by
    have h1 := (MeasureTheory.measurePreserving_prodAssoc μV μY μZ).symm
    have h2 := (Measure.measurePreserving_swap (μ := μV) (ν := μY)).prod
      (MeasurePreserving.id μZ)
    have h3 := MeasureTheory.measurePreserving_prodAssoc μY μV μZ
    convert h3.comp (h2.comp h1) using 1 <;> rfl
  have h := (MeasurePreserving.id μX).prod hinner
  convert h using 1 <;> rfl

private def assocYV [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace V] [MeasurableSpace Z] :
    (X × ((Y × V) × Z)) ≃ᵐ (X × (Y × (V × Z))) where
  toFun q := (q.1, (q.2.1.1, (q.2.1.2, q.2.2)))
  invFun q := (q.1, ((q.2.1, q.2.2.1), q.2.2.2))
  left_inv q := by cases q with | mk x r => cases r with | mk yv z => cases yv <;> rfl
  right_inv q := by cases q with | mk x r => cases r with | mk y vz => cases vz <;> rfl
  measurable_toFun := by
    change Measurable (fun q : X × ((Y × V) × Z) ↦ (q.1, (q.2.1.1, (q.2.1.2, q.2.2))))
    fun_prop
  measurable_invFun := by
    change Measurable (fun q : X × (Y × (V × Z)) ↦ (q.1, ((q.2.1, q.2.2.1), q.2.2.2)))
    fun_prop

private theorem measurePreserving_assocYV
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]
    (μX : Measure X) (μY : Measure Y) (μV : Measure V) (μZ : Measure Z)
    [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μV] [SigmaFinite μZ] :
    MeasurePreserving (@assocYV X Y V Z _ _ _ _)
      (μX.prod ((μY.prod μV).prod μZ)) (μX.prod (μY.prod (μV.prod μZ))) := by
  have h := (MeasurePreserving.id μX).prod
    (MeasureTheory.measurePreserving_prodAssoc μY μV μZ)
  convert h using 1 <;> rfl

variable {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]
variable [StandardBorelSpace X] [StandardBorelSpace Y]
  [StandardBorelSpace V] [StandardBorelSpace Z]
variable (μX : Measure X) (μY : Measure Y) (μV : Measure V) (μZ : Measure Z)
variable [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μV] [SigmaFinite μZ]
variable {d : FourBlock X Y V Z → ℝ≥0∞}
variable [IsFiniteMeasure ((fourBlockReference μX μY μV μZ).withDensity d)]

/-- For a finite measure with density over a four-fold product reference measure,
`X ⟂ Y | (Z,V)` holds exactly when the density factors into `(X,V,Z)` and `(Y,V,Z)` terms. -/
theorem condIndepFun_xy_given_zv_iff_factors (hd : Measurable d) :
    CondIndepFun
        (MeasurableSpace.comap (@zvCoord X Y V Z) inferInstance)
        measurable_zvCoord.comap_le (@xCoord X Y V Z) (@yCoord X Y V Z)
        ((fourBlockReference μX μY μV μZ).withDensity d) ↔
      FactorsXYGivenZV μX μY μV μZ d := by
  letI : IsFiniteMeasure ((threeBlockReference μX μY (μV.prod μZ)).withDensity d) := by
    simpa [threeBlockReference, fourBlockReference] using
      (inferInstance : IsFiniteMeasure ((fourBlockReference μX μY μV μZ).withDensity d))
  have hcomap :
      MeasurableSpace.comap (@zvCoord X Y V Z) inferInstance =
        MeasurableSpace.comap (@thirdThreeCoord X Y (V × Z)) inferInstance := by
    apply le_antisymm
    · exact (show Measurable[
          MeasurableSpace.comap (@thirdThreeCoord X Y (V × Z)) inferInstance]
          (@zvCoord X Y V Z) by
        change Measurable[
          MeasurableSpace.comap (@thirdThreeCoord X Y (V × Z)) inferInstance]
          (Prod.swap ∘ @thirdThreeCoord X Y (V × Z))
        exact measurable_swap.comp (Measurable.of_comap_le le_rfl)).comap_le
    · exact (show Measurable[
          MeasurableSpace.comap (@zvCoord X Y V Z) inferInstance]
          (@thirdThreeCoord X Y (V × Z)) by
        change Measurable[
          MeasurableSpace.comap (@zvCoord X Y V Z) inferInstance]
          (Prod.swap ∘ @zvCoord X Y V Z)
        exact measurable_swap.comp (Measurable.of_comap_le le_rfl)).comap_le
  change CondIndepFun
      (MeasurableSpace.comap (@zvCoord X Y V Z) inferInstance) _
      (@firstThreeCoord X Y (V × Z)) (@secondThreeCoord X Y (V × Z))
      ((threeBlockReference μX μY (μV.prod μZ)).withDensity d) ↔
    ThreeBlockFactors μX μY (μV.prod μZ) d
  simpa only [hcomap] using
    (condIndepFun_threeBlock_iff_factors μX μY (μV.prod μZ) hd)

/-- For a finite measure with density over a four-fold product reference measure,
`X ⟂ V | (Z,Y)` holds exactly when the density factors into `(X,Y,Z)` and `(V,Y,Z)` terms. -/
theorem condIndepFun_xv_given_zy_iff_factors (hd : Measurable d) :
    CondIndepFun
        (MeasurableSpace.comap (@zyCoord X Y V Z) inferInstance)
        measurable_zyCoord.comap_le (@xCoord X Y V Z) (@vCoord X Y V Z)
        ((fourBlockReference μX μY μV μZ).withDensity d) ↔
      FactorsXVGivenZY μX μY μV μZ d := by
  let e : (X × (V × (Y × Z))) ≃ᵐ FourBlock X Y V Z := permXV
  let d' : X × (V × (Y × Z)) → ℝ≥0∞ := d ∘ e
  let yz : FourBlock X Y V Z → Y × Z := fun q ↦ (yCoord q, zCoord q)
  have he : MeasurePreserving e
      (threeBlockReference μX μV (μY.prod μZ))
      (fourBlockReference μX μY μV μZ) := by
    simpa [e, threeBlockReference, fourBlockReference] using
      measurePreserving_permXV μX μY μV μZ
  have hd' : Measurable d' := hd.comp e.measurable
  have hlaw :
      ((threeBlockReference μX μV (μY.prod μZ)).withDensity d').map e =
        (fourBlockReference μX μY μV μZ).withDensity d := by
    simpa [d'] using map_withDensity_comp_of_measurePreservingEquiv e he d hd
  have hlaw' :
      ((fourBlockReference μX μY μV μZ).withDensity d).map e.symm =
        (threeBlockReference μX μV (μY.prod μZ)).withDensity d' := by
    rw [← hlaw, Measure.map_map e.symm.measurable e.measurable]
    simpa using congrArg
      (fun f ↦ Measure.map f
        ((threeBlockReference μX μV (μY.prod μZ)).withDensity d')) e.symm_comp_self
  letI : IsFiniteMeasure
      ((threeBlockReference μX μV (μY.prod μZ)).withDensity d') := by
    rw [← hlaw']
    infer_instance
  have htransport :
      CondIndepFun
          (MeasurableSpace.comap (@thirdThreeCoord X V (Y × Z)) inferInstance)
          measurable_thirdThreeCoord.comap_le
          (@firstThreeCoord X V (Y × Z)) (@secondThreeCoord X V (Y × Z))
          ((threeBlockReference μX μV (μY.prod μZ)).withDensity d') ↔
        CondIndepFun
          (MeasurableSpace.comap yz inferInstance)
          (show Measurable yz by simp only [yz]; fun_prop).comap_le
          (@xCoord X Y V Z) (@vCoord X Y V Z)
          ((fourBlockReference μX μY μV μZ).withDensity d) := by
    change CondIndepFun
        (MeasurableSpace.comap (fun q : X × (V × (Y × Z)) ↦ q.2.2) inferInstance) _
        (fun q : X × (V × (Y × Z)) ↦ q.1) (fun q ↦ q.2.1)
        ((threeBlockReference μX μV (μY.prod μZ)).withDensity d') ↔ _
    simpa [e, permXV, yz, xCoord, yCoord, vCoord, zCoord, Function.comp_def] using
      (condIndepFun_measurableEquiv_iff e hlaw measurable_xCoord measurable_vCoord
        (show Measurable yz by simp only [yz]; fun_prop))
  have hcomap :
      MeasurableSpace.comap (@zyCoord X Y V Z) inferInstance =
        MeasurableSpace.comap yz inferInstance := by
    apply le_antisymm
    · exact (show Measurable[MeasurableSpace.comap yz inferInstance]
          (@zyCoord X Y V Z) by
        change Measurable[MeasurableSpace.comap yz inferInstance] (Prod.swap ∘ yz)
        exact measurable_swap.comp (Measurable.of_comap_le le_rfl)).comap_le
    · exact (show Measurable[
          MeasurableSpace.comap (@zyCoord X Y V Z) inferInstance] yz by
        change Measurable[MeasurableSpace.comap (@zyCoord X Y V Z) inferInstance]
          (Prod.swap ∘ @zyCoord X Y V Z)
        exact measurable_swap.comp (Measurable.of_comap_le le_rfl)).comap_le
  have hfactors :
      ThreeBlockFactors μX μV (μY.prod μZ) d' ↔
        FactorsXVGivenZY μX μY μV μZ d := by
    constructor
    · rintro ⟨a, b, ha, hb, hab⟩
      refine ⟨a, b, ha, hb, ?_⟩
      change ∀ᵐ q ∂fourBlockReference μX μY μV μZ,
        d q = a (xCoord q, (yCoord q, zCoord q)) *
          b (vCoord q, (yCoord q, zCoord q))
      rw [← he.map_eq, e.measurableEmbedding.ae_map_iff]
      change ∀ᵐ q ∂threeBlockReference μX μV (μY.prod μZ),
        d' q = a (q.1, q.2.2) * b (q.2.1, q.2.2) at hab
      simpa [d', e, permXV, xCoord, yCoord, vCoord, zCoord, Function.comp_def] using hab
    · rintro ⟨a, b, ha, hb, hab⟩
      refine ⟨a, b, ha, hb, ?_⟩
      change ∀ᵐ q ∂threeBlockReference μX μV (μY.prod μZ),
        d' q = a (q.1, q.2.2) * b (q.2.1, q.2.2)
      change ∀ᵐ q ∂fourBlockReference μX μY μV μZ,
        d q = a (xCoord q, (yCoord q, zCoord q)) *
          b (vCoord q, (yCoord q, zCoord q)) at hab
      rw [← he.map_eq, e.measurableEmbedding.ae_map_iff] at hab
      simpa [d', e, permXV, xCoord, yCoord, vCoord, zCoord, Function.comp_def] using hab
  change CondIndepFun
      (MeasurableSpace.comap (@zyCoord X Y V Z) inferInstance) _
      (@xCoord X Y V Z) (@vCoord X Y V Z)
      ((fourBlockReference μX μY μV μZ).withDensity d) ↔
    FactorsXVGivenZY μX μY μV μZ d
  calc
    _ ↔ CondIndepFun (MeasurableSpace.comap yz inferInstance) _
        (@xCoord X Y V Z) (@vCoord X Y V Z)
        ((fourBlockReference μX μY μV μZ).withDensity d) := by simp only [hcomap]
    _ ↔ CondIndepFun
        (MeasurableSpace.comap (@thirdThreeCoord X V (Y × Z)) inferInstance) _
        (@firstThreeCoord X V (Y × Z)) (@secondThreeCoord X V (Y × Z))
        ((threeBlockReference μX μV (μY.prod μZ)).withDensity d') := htransport.symm
    _ ↔ ThreeBlockFactors μX μV (μY.prod μZ) d' :=
      condIndepFun_threeBlock_iff_factors μX μV (μY.prod μZ) hd'
    _ ↔ FactorsXVGivenZY μX μY μV μZ d := hfactors

/-- For a finite measure with density over a four-fold product reference measure,
`X ⟂ (Y,V) | Z` holds exactly when the density factors into `(X,Z)` and `(Y,V,Z)` terms. -/
theorem condIndepFun_xyv_given_z_iff_factors (hd : Measurable d) :
    CondIndepFun
        (MeasurableSpace.comap (@zCoord X Y V Z) inferInstance)
        measurable_zCoord.comap_le (@xCoord X Y V Z) (@yvCoord X Y V Z)
        ((fourBlockReference μX μY μV μZ).withDensity d) ↔
      FactorsXYVGivenZ μX μY μV μZ d := by
  let e : (X × ((Y × V) × Z)) ≃ᵐ FourBlock X Y V Z := assocYV
  let d' : X × ((Y × V) × Z) → ℝ≥0∞ := d ∘ e
  have he : MeasurePreserving e
      (threeBlockReference μX (μY.prod μV) μZ)
      (fourBlockReference μX μY μV μZ) := by
    simpa [e, threeBlockReference, fourBlockReference] using
      measurePreserving_assocYV μX μY μV μZ
  have hd' : Measurable d' := hd.comp e.measurable
  have hlaw :
      ((threeBlockReference μX (μY.prod μV) μZ).withDensity d').map e =
        (fourBlockReference μX μY μV μZ).withDensity d := by
    simpa [d'] using map_withDensity_comp_of_measurePreservingEquiv e he d hd
  have hlaw' :
      ((fourBlockReference μX μY μV μZ).withDensity d).map e.symm =
        (threeBlockReference μX (μY.prod μV) μZ).withDensity d' := by
    rw [← hlaw, Measure.map_map e.symm.measurable e.measurable]
    simpa using congrArg
      (fun f ↦ Measure.map f
        ((threeBlockReference μX (μY.prod μV) μZ).withDensity d')) e.symm_comp_self
  letI : IsFiniteMeasure
      ((threeBlockReference μX (μY.prod μV) μZ).withDensity d') := by
    rw [← hlaw']
    infer_instance
  have htransport :
      CondIndepFun
          (MeasurableSpace.comap (@thirdThreeCoord X (Y × V) Z) inferInstance)
          measurable_thirdThreeCoord.comap_le
          (@firstThreeCoord X (Y × V) Z) (@secondThreeCoord X (Y × V) Z)
          ((threeBlockReference μX (μY.prod μV) μZ).withDensity d') ↔
        CondIndepFun
          (MeasurableSpace.comap (@zCoord X Y V Z) inferInstance)
          measurable_zCoord.comap_le
          (@xCoord X Y V Z) (@yvCoord X Y V Z)
          ((fourBlockReference μX μY μV μZ).withDensity d) := by
    change CondIndepFun
        (MeasurableSpace.comap (fun q : X × ((Y × V) × Z) ↦ q.2.2) inferInstance) _
        (fun q : X × ((Y × V) × Z) ↦ q.1) (fun q ↦ q.2.1)
        ((threeBlockReference μX (μY.prod μV) μZ).withDensity d') ↔ _
    simpa [e, assocYV, xCoord, yCoord, vCoord, zCoord, yvCoord, Function.comp_def] using
      (condIndepFun_measurableEquiv_iff e hlaw measurable_xCoord measurable_yvCoord
        measurable_zCoord)
  have hfactors :
      ThreeBlockFactors μX (μY.prod μV) μZ d' ↔
        FactorsXYVGivenZ μX μY μV μZ d := by
    constructor
    · rintro ⟨a, b, ha, hb, hab⟩
      refine ⟨a, b, ha, hb, ?_⟩
      change ∀ᵐ q ∂fourBlockReference μX μY μV μZ,
        d q = a (xCoord q, zCoord q) * b ((yCoord q, vCoord q), zCoord q)
      rw [← he.map_eq, e.measurableEmbedding.ae_map_iff]
      change ∀ᵐ q ∂threeBlockReference μX (μY.prod μV) μZ,
        d' q = a (q.1, q.2.2) * b (q.2.1, q.2.2) at hab
      simpa [d', e, assocYV, xCoord, yCoord, vCoord, zCoord, Function.comp_def] using hab
    · rintro ⟨a, b, ha, hb, hab⟩
      refine ⟨a, b, ha, hb, ?_⟩
      change ∀ᵐ q ∂threeBlockReference μX (μY.prod μV) μZ,
        d' q = a (q.1, q.2.2) * b (q.2.1, q.2.2)
      change ∀ᵐ q ∂fourBlockReference μX μY μV μZ,
        d q = a (xCoord q, zCoord q) * b ((yCoord q, vCoord q), zCoord q) at hab
      rw [← he.map_eq, e.measurableEmbedding.ae_map_iff] at hab
      simpa [d', e, assocYV, xCoord, yCoord, vCoord, zCoord, Function.comp_def] using hab
  calc
    _ ↔ CondIndepFun
        (MeasurableSpace.comap (@thirdThreeCoord X (Y × V) Z) inferInstance) _
        (@firstThreeCoord X (Y × V) Z) (@secondThreeCoord X (Y × V) Z)
        ((threeBlockReference μX (μY.prod μV) μZ).withDensity d') := htransport.symm
    _ ↔ ThreeBlockFactors μX (μY.prod μV) μZ d' :=
      condIndepFun_threeBlock_iff_factors μX (μY.prod μV) μZ hd'
    _ ↔ FactorsXYVGivenZ μX μY μV μZ d := hfactors

end CausalSmith.Substrate.PositiveDensityCondindepIntersection
