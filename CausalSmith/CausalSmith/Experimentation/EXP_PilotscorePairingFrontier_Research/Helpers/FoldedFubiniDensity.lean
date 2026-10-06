module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedFubini
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedPushforward

/-! # Reassembling slice densities over transverse coordinates -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

/-- A jointly measurable family of one-dimensional slice densities reassembles
to the transverse average density under a product pushforward. -/
lemma map_prod_eq_withDensity_lintegral_slices
    {alpha zeta gamma : Type*}
    [MeasurableSpace alpha] [MeasurableSpace zeta] [MeasurableSpace gamma]
    {mu : Measure alpha} {eta : Measure zeta} {nu : Measure gamma}
    [SFinite mu] [SFinite eta] [SFinite nu]
    {F : alpha × zeta -> gamma} {p : zeta -> gamma -> ENNReal}
    (hF : Measurable F)
    (hp : Measurable (fun zy : zeta × gamma => p zy.1 zy.2))
    (hslice : forall z, Measure.map (fun x => F (x, z)) mu =
      nu.withDensity (p z)) :
    Measure.map F (mu.prod eta) =
      nu.withDensity (fun y => ∫⁻ z, p z y ∂eta) := by
  ext s hs
  rw [map_prod_apply_eq_lintegral_slice hF hs]
  simp_rw [hslice, withDensity_apply _ hs]
  have hind : Measurable (fun zy : zeta × gamma =>
      s.indicator (fun y => p zy.1 y) zy.2) := by
    exact hp.indicator (hs.preimage measurable_snd)
  calc
    (∫⁻ z, ∫⁻ y in s, p z y ∂nu ∂eta) =
        ∫⁻ z, ∫⁻ y, s.indicator (fun y => p z y) y ∂nu ∂eta := by
      congr 1
      funext z
      exact (lintegral_indicator hs (p z)).symm
    _ = ∫⁻ y, ∫⁻ z, s.indicator (fun y => p z y) y ∂eta ∂nu := by
      rw [← lintegral_prod
        (μ := eta) (ν := nu) _ hind.aemeasurable]
      exact lintegral_prod_symm
        (μ := eta) (ν := nu) _ hind.aemeasurable
    _ = ∫⁻ y in s, ∫⁻ z, p z y ∂eta ∂nu := by
      rw [← lintegral_indicator hs]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ s <;> simp [hy]
    _ = ∫⁻ y in s, ∫⁻ z, p z y ∂eta ∂nu := rfl

/-- Weighting by a measurable function of the mapped coordinate commutes
with pushforward. -/
lemma map_withDensity_comp {alpha gamma : Type*}
    [MeasurableSpace alpha] [MeasurableSpace gamma]
    (mu : Measure alpha) (f : alpha -> gamma) (hf : Measurable f)
    (g : gamma -> ENNReal) (hg : Measurable g) :
    Measure.map f (mu.withDensity (g ∘ f)) =
      (Measure.map f mu).withDensity g := by
  apply Measure.ext_of_lintegral
  intro phi hphi
  rw [lintegral_map hphi hf]
  change (∫⁻ a, (phi ∘ f) a ∂mu.withDensity (g ∘ f)) = _
  rw [lintegral_withDensity_eq_lintegral_mul mu (hg.comp hf) (hphi.comp hf),
    lintegral_withDensity_eq_lintegral_mul (Measure.map f mu) hg hphi,
    lintegral_map (hg.mul hphi) hf]
  rfl

/-- The affine score map sends a Lebesgue density on the folded coordinate
to the inverse-coordinate density with Jacobian two. -/
lemma map_scoreAffine_withDensity (p : ℝ -> ENNReal) (hp : Measurable p) :
    Measure.map (fun y : ℝ => 1 / 4 + 1 / 2 * y)
        ((volume : Measure ℝ).withDensity p) =
      (volume : Measure ℝ).withDensity
        (fun t => ENNReal.ofReal 2 * p (2 * t - 1 / 2)) := by
  let f : ℝ -> ℝ := fun y => 1 / 4 + 1 / 2 * y
  let finv : ℝ -> ℝ := fun t => 2 * t - 1 / 2
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hfinv : Measurable finv := by dsimp [finv]; fun_prop
  have hcomp : (p ∘ finv) ∘ f = p := by
    funext y
    simp only [Function.comp_apply]
    dsimp [f, finv]
    congr 1
    ring
  have hw := map_withDensity_comp volume f hf (p ∘ finv) (hp.comp hfinv)
  rw [hcomp, map_affine_volume (1 / 4) (1 / 2) (by norm_num)] at hw
  change Measure.map f (volume.withDensity p) = _
  rw [hw]
  ext s hs
  simp only [withDensity_apply _ hs]
  rw [Measure.restrict_smul, lintegral_smul_measure]
  rw [lintegral_const_mul]
  · norm_num [finv, Function.comp_apply, smul_eq_mul]
  · simpa [finv, Function.comp_def] using hp.comp hfinv

end CausalSmith.Experimentation.PilotscorePairingFrontier
