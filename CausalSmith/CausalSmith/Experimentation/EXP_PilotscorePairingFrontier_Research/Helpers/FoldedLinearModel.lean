module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedLinearCube
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedModelAssembly
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedHolderBounds

/-! # Model packaging for the beta-one affine branch -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

set_option maxHeartbeats 800000

lemma FoldedGeometry.betaOne_regularScoreModel
    {hd : 0 < d} {q K : ℕ} {Q : Fin K → Set (XSpace d)}
    {psi : Fin K → XSpace d → ℝ} {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B)
    {L cX CX cg Cg eps : ℝ}
    (hpars : ValidClassParameters d 1 L cX CX cg Cg)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (hholder : 1 / 2 + 96 * (d : ℝ) * eps ≤ L)
    (herror : 256 * eps ≤ min (2 - cg) (Cg - 2))
    (theta : Fin K → Bool) :
    RegularScoreModel
      (bernoulliUnitLaw (foldedRawScore hd 1 (q : ℝ)⁻¹ 1 eps K psi theta))
      (foldedRawScore hd 1 (q : ℝ)⁻¹ 1 eps K psi theta)
      L 1 cX CX cg Cg := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  let g := foldedRawScore hd 1 (q : ℝ)⁻¹ 1 eps K psi theta
  have hpsi : ∀ j, Measurable (psi j) := by
    intro j
    rcases hgeo with ⟨hq, idx, hinj, hcomplete, hdefs⟩
    rw [(hdefs j).2.1]
    exact measurable_meshBump hd _ _
  have hg : Measurable g :=
    measurable_foldedRawScore_of_measurable_bumps hd 1 _ 1 eps K psi hpsi theta
  have hqR : (0 : ℝ) < q := by exact_mod_cast hgeo.1
  have hh : 0 < (q : ℝ)⁻¹ := inv_pos.mpr hqR
  have hhle : (q : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hqR]
    exact_mod_cast hgeo.1
  have heh : eps * (q : ℝ)⁻¹ ≤ 1 / 128 := by
    calc
      eps * (q : ℝ)⁻¹ ≤ (1 / 128 : ℝ) * 1 :=
        mul_le_mul heps hhle hh.le (by norm_num)
      _ = 1 / 128 := by ring
  have hrange : ∀ x ∈ cube (n + 1), 0 ≤ g x ∧ g x ≤ 1 := by
    intro x hx
    have hx0 := hx ⟨0, hd⟩
    rcases hx0 with ⟨hxlo, hxhi⟩
    have hS := signed_bump_sum_abs_le_one
      (fun i j hij => hgeo.pairwise_disjoint hij)
      (fun j w => ⟨(hgeo.bump_bounds j w).1, (hgeo.bump_bounds j w).2,
        fun hw => hgeo.bump_eq_zero_off_cell j hw⟩) theta x
    rw [abs_le] at hS
    have heh0 : 0 ≤ eps * (q : ℝ)⁻¹ := mul_nonneg heps0 hh.le
    have hplo : -(1 / 128 : ℝ) ≤
        eps * (q : ℝ)⁻¹ * ∑ j, localSign (theta j) * psi j x := by
      have := mul_le_mul_of_nonneg_left hS.1 heh0
      nlinarith
    have hphi : eps * (q : ℝ)⁻¹ * ∑ j, localSign (theta j) * psi j x ≤
        (1 / 128 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hS.2 heh0
      nlinarith
    simp only [g, foldedRawScore, lt_self_iff_false, if_false]
    constructor <;> nlinarith
  have hhold : HolderScore g L 1 := by
    intro x hx y hy
    have hz := coordinate_abs_sub_le_euclideanDistance x y ⟨0, hd⟩
    have hS := hgeo.signed_bump_sum_diff_le theta x y
    simp only [g, foldedRawScore, lt_self_iff_false, if_false, Real.rpow_one]
    rw [show (1 / 4 + x ⟨0, hd⟩ / 2 + eps * (q : ℝ)⁻¹ *
          ∑ i, localSign (theta i) * psi i x) -
        (1 / 4 + y ⟨0, hd⟩ / 2 + eps * (q : ℝ)⁻¹ *
          ∑ i, localSign (theta i) * psi i y) =
        (x ⟨0, hd⟩ - y ⟨0, hd⟩) / 2 +
          eps * (q : ℝ)⁻¹ * ((∑ i, localSign (theta i) * psi i x) -
            ∑ i, localSign (theta i) * psi i y) by ring]
    calc
      _ ≤ |x ⟨0, hd⟩ - y ⟨0, hd⟩| / 2 +
          (eps * (q : ℝ)⁻¹) *
            |(∑ i, localSign (theta i) * psi i x) -
              ∑ i, localSign (theta i) * psi i y| := by
        calc
          _ ≤ |(x ⟨0, hd⟩ - y ⟨0, hd⟩) / 2| +
              |eps * (q : ℝ)⁻¹ * ((∑ i, localSign (theta i) * psi i x) -
                ∑ i, localSign (theta i) * psi i y)| := abs_add_le _ _
          _ = _ := by rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
            abs_mul, abs_of_nonneg (mul_nonneg heps0 hh.le)]
      _ ≤ euclideanDistance x y / 2 +
          (eps * (q : ℝ)⁻¹) *
            (96 * (n.succ : ℝ) / (q : ℝ)⁻¹ * euclideanDistance x y) := by
        gcongr
      _ = (1 / 2 + 96 * (n.succ : ℝ) * eps) * euclideanDistance x y := by
        field_simp [hh.ne']
      _ ≤ L * euclideanDistance x y := by
        exact mul_le_mul_of_nonneg_right hholder (by unfold euclideanDistance; positivity)
  have hreg : RegularScorePushforward (bernoulliUnitLaw g) g cg Cg := by
    rcases hgeo with ⟨hq, idx, hinj, hcomplete, hdefs⟩
    have hpsiEq : psi = fun j => meshBump hd ((q : ℝ)⁻¹) (idx j) := by
      funext j
      exact (hdefs j).2.1
    subst psi
    let D := linearCubeScoreDensity n q K (q : ℝ)⁻¹ eps idx theta
    let p := fun t => (D t).toReal
    have hp : Measurable p :=
      (measurable_linearCubeScoreDensity n q K (q : ℝ)⁻¹ eps idx theta).ennreal_toReal
    have hp0 : ∀ t, 0 ≤ p t := fun t => ENNReal.toReal_nonneg
    have hbounds : ∀ᵐ t ∂(volume : Measure ℝ).restrict scoreInterval,
        cg ≤ p t ∧ p t ≤ Cg := by
      filter_upwards [linearCubeScoreDensity_error_ae n q K hq rfl idx hinj theta
        heps0 heps] with t ht
      have hlo := min_le_left (2 - cg) (Cg - 2)
      have hhi := min_le_right (2 - cg) (Cg - 2)
      dsimp [p, D]
      rw [abs_le] at ht
      constructor <;> linarith
    apply regularScorePushforward_of_cube_map_withDensity hg hrange hp hp0 hbounds
    have hfull := map_betaOne_foldedRawScore_eq_withDensity n q K hq rfl idx hinj
      theta heps0 heps
    have hDzero (t : ℝ) (ht : t ∉ scoreInterval) : D t = 0 := by
      unfold D linearCubeScoreDensity
      apply lintegral_eq_zero_of_ae_eq_zero
      exact Filter.Eventually.of_forall fun z =>
        linearMeshDensity_eq_zero_off q hq rfl
          (foldedTailCoefficient n K (q : ℝ)⁻¹ idx theta z)
          (fun k => foldedTailCoefficient_mem_Icc n K (q : ℝ)⁻¹ hinj theta z k)
          heps0 heps ht
    letI : IsProbabilityMeasure (cubeMeasure (n + 1)) :=
      cubeMeasure_isProbabilityMeasure (n + 1)
    have hDint : (∫⁻ t, D t ∂(volume : Measure ℝ)) ≠ ⊤ := by
      have hm : ((volume : Measure ℝ).withDensity D) Set.univ ≠ ⊤ := by
        rw [← hfull]
        exact measure_ne_top _ _
      simpa [withDensity_apply] using hm
    have hDfinite : ∀ᵐ t ∂(volume : Measure ℝ), D t < ⊤ :=
      ae_lt_top (measurable_linearCubeScoreDensity n q K (q : ℝ)⁻¹ eps idx theta) hDint
    calc
      Measure.map g (cubeMeasure (n + 1)) = (volume : Measure ℝ).withDensity D := hfull
      _ = (volume : Measure ℝ).withDensity (scoreInterval.indicator D) := by
        apply withDensity_congr_ae
        filter_upwards [] with t
        by_cases ht : t ∈ scoreInterval
        · simp [ht]
        · simp [ht, hDzero t ht]
      _ = ((volume : Measure ℝ).restrict scoreInterval).withDensity D := by
        exact MeasureTheory.withDensity_indicator measurableSet_Icc D
      _ = ((volume : Measure ℝ).restrict scoreInterval).withDensity
          (fun t => ENNReal.ofReal (p t)) := by
        apply withDensity_congr_ae
        filter_upwards [ae_restrict_of_ae hDfinite] with t ht
        exact (ENNReal.ofReal_toReal (ne_of_lt ht)).symm
  simpa [g] using bernoulliUnitLaw_regularScoreModel hpars hg hrange hhold hreg

end CausalSmith.Experimentation.PilotscorePairingFrontier
