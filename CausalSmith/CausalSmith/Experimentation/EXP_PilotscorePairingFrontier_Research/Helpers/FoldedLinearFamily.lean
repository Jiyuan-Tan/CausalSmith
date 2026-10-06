module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedLinearModel
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedKLAssembly

/-! # Hypercube algebra and information bound for the beta-one branch -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

lemma FoldedGeometry.betaOne_rawScore_additive
    {hd : 0 < d} {q K : ℕ} {Q : Fin K → Set (XSpace d)}
    {psi : Fin K → XSpace d → ℝ} {B : Fin K → Set (XSpace d)}
    (_hgeo : FoldedGeometry hd q K Q psi B) (eps : ℝ)
    (theta : Fin K → Bool) (x : XSpace d) :
    foldedRawScore hd 1 (q : ℝ)⁻¹ 1 eps K psi theta x =
      (1 / 4 + x ⟨0, hd⟩ / 2) +
        (eps * (q : ℝ)⁻¹) * ∑ j, localSign (theta j) * psi j x := by
  simp [foldedRawScore]

lemma FoldedGeometry.betaOne_rawScore_mem_band
    {hd : 0 < d} {q K : ℕ} {Q : Fin K → Set (XSpace d)}
    {psi : Fin K → XSpace d → ℝ} {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B)
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (theta : Fin K → Bool) (x : XSpace d) (hx : x ∈ cube d) :
    1 / 4 ≤ foldedRawScore hd 1 (q : ℝ)⁻¹ 1 eps K psi theta x ∧
      foldedRawScore hd 1 (q : ℝ)⁻¹ 1 eps K psi theta x ≤ 3 / 4 := by
  have hsum := signed_bump_sum_abs_le_one
    (fun i j hij => hgeo.pairwise_disjoint hij)
    (fun j w => ⟨(hgeo.bump_bounds j w).1, (hgeo.bump_bounds j w).2,
      fun hw => hgeo.bump_eq_zero_off_cell j hw⟩) theta x
  by_cases hS : (∑ j, localSign (theta j) * psi j x) = 0
  · rw [hgeo.betaOne_rawScore_additive eps, hS]
    simp only [mul_zero, add_zero]
    have hx0 := hx ⟨0, hd⟩
    exact ⟨by linarith [hx0.1], by linarith [hx0.2]⟩
  · obtain ⟨j, hj⟩ : ∃ j, psi j x ≠ 0 := by
      by_contra hn
      simp only [not_exists, not_not] at hn
      apply hS
      simp [hn]
    have hxQ : x ∈ Q j := by
      by_contra hxQ
      exact hj (hgeo.bump_eq_zero_off_cell j hxQ)
    have hgeo0 := hgeo
    rcases hgeo with ⟨hq, idx, hinj, hcomplete, hdefs⟩
    have hactive : activeMeshCell hd q (idx j) :=
      (hcomplete (idx j)).2 ⟨j, rfl⟩
    rw [(hdefs j).1] at hxQ
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hh : 0 < (q : ℝ)⁻¹ := inv_pos.mpr hqR
    have hx0lo : (1 / 3 : ℝ) ≤ x ⟨0, hd⟩ :=
      hactive.2.1.trans (hxQ.2 ⟨0, hd⟩).1
    have hx0hi : x ⟨0, hd⟩ ≤ (2 / 3 : ℝ) := by
      rcases (hxQ.2 ⟨0, hd⟩).2 with hlt | hend
      · exact hlt.le.trans hactive.2.2
      · exact hend.1.le.trans (hend.2 ▸ hactive.2.2)
    have hSbounds := abs_le.mp hsum
    have hpert : |eps * (q : ℝ)⁻¹ * ∑ j, localSign (theta j) * psi j x| ≤
        eps * (q : ℝ)⁻¹ := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg heps0 hh.le)]
      exact mul_le_of_le_one_right (mul_nonneg heps0 hh.le) hsum
    rw [hgeo0.betaOne_rawScore_additive eps]
    constructor
    · have heh : eps * (q : ℝ)⁻¹ ≤ 1 / 128 := by
        have hhle : (q : ℝ)⁻¹ ≤ 1 := by
          rw [inv_le_one₀ hqR]
          exact_mod_cast hq
        nlinarith [mul_le_mul heps hhle hh.le (by norm_num : (0 : ℝ) ≤ 1 / 128)]
      nlinarith [abs_le.mp hpert]
    · have heh : eps * (q : ℝ)⁻¹ ≤ 1 / 128 := by
        have hhle : (q : ℝ)⁻¹ ≤ 1 := by
          rw [inv_le_one₀ hqR]
          exact_mod_cast hq
        nlinarith [mul_le_mul heps hhle hh.le (by norm_num : (0 : ℝ) ≤ 1 / 128)]
      nlinarith [abs_le.mp hpert]

/-- The beta-one affine family has the required one-coordinate pilot KL rate. -/
lemma FoldedGeometry.betaOne_bernoulliPilotProduct_klDiv_flip_rpow_le
    {hd : 0 < d} {q K : ℕ} {Q : Fin K → Set (XSpace d)}
    {psi : Fin K → XSpace d → ℝ} {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B)
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128)
    (m : ℕ) (theta : Fin K → Bool) (j : Fin K) :
    InformationTheory.klDiv
      (Measure.pi fun _ : Fin m => pilotUnitLaw
        (bernoulliUnitLaw (foldedHypercube hd 1 (q : ℝ)⁻¹ 1 eps K psi theta)))
      (Measure.pi fun _ : Fin m => pilotUnitLaw
        (bernoulliUnitLaw (foldedHypercube hd 1 (q : ℝ)⁻¹ 1 eps K psi
          (flipCoordinate theta j)))) ≤
      ENNReal.ofReal ((32 * eps ^ 2) * (m : ℝ) *
        ((q : ℝ)⁻¹) ^ ((d : ℝ) + 2)) := by
  let g := foldedHypercube hd 1 (q : ℝ)⁻¹ 1 eps K psi theta
  let g' := foldedHypercube hd 1 (q : ℝ)⁻¹ 1 eps K psi (flipCoordinate theta j)
  have hpsi : ∀ i, Measurable (psi i) := by
    intro i
    rcases hgeo with ⟨hq, idx, hinj, hcomplete, hdefs⟩
    rw [(hdefs i).2.1]
    exact measurable_meshBump hd _ _
  have hg : Measurable g :=
    measurable_foldedRawScore_of_measurable_bumps hd 1 _ 1 eps K psi hpsi theta
  have hg' : Measurable g' :=
    measurable_foldedRawScore_of_measurable_bumps hd 1 _ 1 eps K psi hpsi
      (flipCoordinate theta j)
  have hband : ∀ x ∈ cube d, 1 / 4 ≤ g x ∧ g x ≤ 3 / 4 := by
    intro x hx
    exact hgeo.betaOne_rawScore_mem_band heps0 heps theta x hx
  have hband' : ∀ x ∈ cube d, 1 / 4 ≤ g' x ∧ g' x ≤ 3 / 4 := by
    intro x hx
    exact hgeo.betaOne_rawScore_mem_band heps0 heps (flipCoordinate theta j) x hx
  have hQ : MeasurableSet (Q j) := by
    rcases hgeo.isSideCube j with ⟨a, ha, hQa⟩
    rw [hQa]
    unfold cube
    measurability
  have hoff : ∀ x ∉ Q j, g x = g' x := by
    intro x hx
    exact hgeo.foldedHypercube_flip_eq_off_cell 1 1 eps theta j x hx
  have hqR : (0 : ℝ) < q := by exact_mod_cast hgeo.1
  have hh : 0 < (q : ℝ)⁻¹ := inv_pos.mpr hqR
  have hgap : ∀ x ∈ Q j, |g x - g' x| ≤ 2 * eps * (q : ℝ)⁻¹ := by
    intro x hx
    dsimp [g, g', foldedHypercube]
    rw [hgeo.betaOne_rawScore_additive eps,
      hgeo.betaOne_rawScore_additive eps]
    have hsum := flip_signed_bump_sum_gap theta psi j x
    have hb0 := (hgeo.bump_bounds j x).1
    have hb := (hgeo.bump_bounds j x).2
    rw [show (1 / 4 + x ⟨0, hd⟩ / 2 + eps * (q : ℝ)⁻¹ *
          ∑ i, localSign (theta i) * psi i x) -
        (1 / 4 + x ⟨0, hd⟩ / 2 + eps * (q : ℝ)⁻¹ *
          ∑ i, localSign ((flipCoordinate theta j) i) * psi i x) =
        (eps * (q : ℝ)⁻¹) *
          ((∑ i, localSign (theta i) * psi i x) -
            ∑ i, localSign ((flipCoordinate theta j) i) * psi i x) by ring,
      abs_mul, hsum, abs_of_nonneg (mul_nonneg heps0 hh.le), abs_of_nonneg hb0]
    nlinarith [mul_le_mul_of_nonneg_left hb (mul_nonneg heps0 hh.le)]
  refine (bernoulliPilotProduct_klDiv_le_cell m g g' hg hg' hband hband'
    (Q j) hQ hoff (2 * eps * (q : ℝ)⁻¹) (by positivity) hgap).trans ?_
  apply ENNReal.ofReal_le_ofReal
  calc
    (m : ℝ) * (8 * (2 * eps * (q : ℝ)⁻¹) ^ 2 *
        (cubeMeasure d).real (Q j)) ≤
        (m : ℝ) * (8 * (2 * eps * (q : ℝ)⁻¹) ^ 2 * ((q : ℝ)⁻¹) ^ d) := by
      gcongr
      exact hgeo.cell_measureReal_upper j
    _ =
        (32 * eps ^ 2) * (m : ℝ) *
          (((q : ℝ)⁻¹) ^ 2 * ((q : ℝ)⁻¹) ^ (d : ℝ)) := by
      rw [Real.rpow_natCast]
      ring
    _ = (32 * eps ^ 2) * (m : ℝ) *
          ((q : ℝ)⁻¹) ^ ((d : ℝ) + 2) := by
      rw [← Real.rpow_natCast ((q : ℝ)⁻¹) 2]
      rw [Real.rpow_add hh]
      simp only [mul_comm]
      norm_num

end CausalSmith.Experimentation.PilotscorePairingFrontier
