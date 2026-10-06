module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-! # First-coordinate disintegration of cube measure -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

/-- Closed intervals may be split additively at a breakpoint under Lebesgue
measure; the duplicated endpoint is null. -/
lemma volume_restrict_Icc_split {l m u : ℝ} (hlm : l ≤ m) (hmu : m ≤ u) :
    (volume : Measure ℝ).restrict (Set.Icc l u) =
      volume.restrict (Set.Icc l m) + volume.restrict (Set.Icc m u) := by
  calc
    (volume : Measure ℝ).restrict (Set.Icc l u) =
        volume.restrict (Set.Icc l m ∪ Set.Ioc m u) := by
      rw [Set.Icc_union_Ioc_eq_Icc hlm hmu]
    _ = volume.restrict (Set.Icc l m) + volume.restrict (Set.Ioc m u) := by
      rw [Measure.restrict_union]
      · exact Set.disjoint_left.2 (by
          intro x hx h'x
          exact (not_lt_of_ge hx.2) h'x.1)
      · exact measurableSet_Ioc
    _ = volume.restrict (Set.Icc l m) + volume.restrict (Set.Icc m u) := by
      rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc]

lemma piFinSuccAbove_image_cube (n : ℕ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) ''
        cube (n + 1) =
      Set.Icc (0 : ℝ) 1 ×ˢ cube n := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · simpa [e, MeasurableEquiv.piFinSuccAbove] using hx (0 : Fin (n + 1))
    · intro i
      change x (Fin.succ i) ∈ Set.Icc (0 : ℝ) 1
      exact hx (Fin.succ i)
  · intro hp
    refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv] using hp.1
    · simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv] using hp.2 j

/-- Splitting off the first coordinate transports restricted product volume
to product volume restricted to the transported cube.  This is the measure
identity used before applying the one-dimensional folded branch calculation. -/
lemma cubeMeasure_map_piFinSuccAbove (n : ℕ) :
    Measure.map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
        (cubeMeasure (n + 1)) =
      ((volume : Measure ℝ).prod
          (Measure.pi fun _ : Fin n => (volume : Measure ℝ))).restrict
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) ''
          cube (n + 1)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hcube : MeasurableSet (cube (n + 1)) :=
    MeasurableSet.univ_pi' (fun _ : Fin (n + 1) => measurableSet_Icc)
  have himage : MeasurableSet (e '' cube (n + 1)) :=
    e.measurableSet_image.mpr hcube
  have hrestrict := Measure.restrict_map
    (μ := Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℝ))
    e.measurable himage
  rw [Set.preimage_image_eq _ e.injective] at hrestrict
  unfold cubeMeasure
  calc
    Measure.map e
        ((Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℝ)).restrict
          (cube (n + 1))) =
        (Measure.map e
          (Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℝ))).restrict
            (e '' cube (n + 1)) := hrestrict.symm
    _ = _ := by
      rw [(measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => (volume : Measure ℝ)) 0).map_eq]

/-- Product form of the cube disintegration, ready for Tonelli/Fubini. -/
lemma cubeMeasure_map_piFinSuccAbove_prod (n : ℕ) :
    Measure.map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
        (cubeMeasure (n + 1)) =
      ((volume : Measure ℝ).restrict (Set.Icc 0 1)).prod (cubeMeasure n) := by
  rw [cubeMeasure_map_piFinSuccAbove, piFinSuccAbove_image_cube]
  unfold cubeMeasure
  exact (Measure.prod_restrict
    (μ := (volume : Measure ℝ))
    (ν := Measure.pi fun _ : Fin n => (volume : Measure ℝ))
    (Set.Icc 0 1) (cube n)).symm

/-- Setwise Fubini formula for a pushforward.  It reduces the full score-law
identity to the one-dimensional pushforward of every transverse slice. -/
lemma map_prod_apply_eq_lintegral_slice
    {α ζ γ : Type*} [MeasurableSpace α] [MeasurableSpace ζ] [MeasurableSpace γ]
    {μ : Measure α} {η : Measure ζ} [SFinite μ] [SFinite η]
    {F : α × ζ → γ} (hF : Measurable F) {s : Set γ} (hs : MeasurableSet s) :
    Measure.map F (μ.prod η) s =
      ∫⁻ z, Measure.map (fun x => F (x, z)) μ s ∂η := by
  rw [Measure.map_apply hF hs,
    Measure.prod_apply_symm (hs.preimage hF)]
  apply lintegral_congr
  intro z
  symm
  have hm : Measurable (fun x => F (x, z)) :=
    hF.comp (measurable_id.prodMk measurable_const)
  calc
    Measure.map (fun x => F (x, z)) μ s =
        μ ((fun x => F (x, z)) ⁻¹' s) := Measure.map_apply hm hs
    _ = μ ((fun x => (x, z)) ⁻¹' F ⁻¹' s) := rfl

end CausalSmith.Experimentation.PilotscorePairingFrontier
