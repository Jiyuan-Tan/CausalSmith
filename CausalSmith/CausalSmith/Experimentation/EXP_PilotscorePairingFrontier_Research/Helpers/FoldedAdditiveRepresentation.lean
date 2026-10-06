module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedModelAssembly
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedScoreLocality

/-! # Additive sign representation of the folded score -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

noncomputable def foldedBaseScore (hd : 0 < d) (beta h kappa : ℝ)
    (x : XSpace d) : ℝ :=
  1 / 4 + 1 / 2 * triangularFold
    (x ⟨0, hd⟩ + kappa * h ^ beta * triangularWave (x ⟨0, hd⟩ / h))

/-- On the support of an active folded bump, both the unperturbed and signed
perturbed arguments stay in the identity branch of `triangularFold`. -/
lemma FoldedGeometry.folded_arguments_mem_Icc
    {hd : 0 < d} {q K : ℕ} {Q : Fin K -> Set (XSpace d)}
    {psi : Fin K -> XSpace d -> ℝ} {B : Fin K -> Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B)
    {beta kappa eps : ℝ} (ha0 : 0 ≤ kappa * (q : ℝ)⁻¹ ^ beta)
    (ha12 : kappa * (q : ℝ)⁻¹ ^ beta ≤ 1 / 12)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 64)
    (theta : Fin K -> Bool) (x : XSpace d)
    (hsum : (∑ j : Fin K, localSign (theta j) * psi j x) ≠ 0) :
    let u := x ⟨0, hd⟩ + kappa * (q : ℝ)⁻¹ ^ beta *
      triangularWave (x ⟨0, hd⟩ / (q : ℝ)⁻¹)
    let v := eps * (kappa * (q : ℝ)⁻¹ ^ beta) *
      ∑ j : Fin K, localSign (theta j) * psi j x
    u ∈ Set.Icc (0 : ℝ) 1 ∧ u + v ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  have hgeo0 := hgeo
  rcases hgeo with ⟨hq, idx, hinj, hcomplete, hdefs⟩
  have hex : ∃ j : Fin K, psi j x ≠ 0 := by
    by_contra hn
    push_neg at hn
    simp_rw [hn, mul_zero, Finset.sum_const_zero] at hsum
    exact hsum rfl
  obtain ⟨j, hj⟩ := hex
  have hactive : activeMeshCell hd q (idx j) :=
    (hcomplete (idx j)).2 ⟨j, rfl⟩
  have hjmesh : meshBump hd ((q : ℝ)⁻¹) (idx j) x ≠ 0 := by
    simpa [(hdefs j).2.1] using hj
  have hfirst : foldedFirstBump
      (x ⟨0, hd⟩ / (q : ℝ)⁻¹ - idx j ⟨0, hd⟩) ≠ 0 := by
    unfold meshBump at hjmesh
    exact (mul_ne_zero_iff.mp hjmesh).1
  have hr := foldedFirstBump_support hfirst
  let r : ℝ := x ⟨0, hd⟩ / (q : ℝ)⁻¹ - idx j ⟨0, hd⟩
  have hrlo : (13 / 32 : ℝ) < r := by simpa [r] using hr.1
  have hrhi : r < (19 / 32 : ℝ) := by simpa [r] using hr.2
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : 0 < (q : ℝ)⁻¹ := inv_pos.mpr hqR
  have hxrepr : x ⟨0, hd⟩ = ((idx j ⟨0, hd⟩ : ℝ) + r) * (q : ℝ)⁻¹ := by
    dsimp [r]
    field_simp [hqR.ne']
    ring
  have hwave : triangularWave (x ⟨0, hd⟩ / (q : ℝ)⁻¹) = 2 - 4 * r := by
    rw [show x ⟨0, hd⟩ / (q : ℝ)⁻¹ =
      (idx j ⟨0, hd⟩ : ℝ) + r by dsimp [r]; ring]
    exact triangularWave_nat_add_middle _ (by linarith [hrlo]) (by linarith [hrhi])
  have hxlo : (1 / 3 : ℝ) ≤ x ⟨0, hd⟩ := by
    have hk := hactive.2.1
    rw [hxrepr]
    have hr0 : 0 ≤ r := by linarith [hrlo]
    calc
      (1 / 3 : ℝ) ≤ (idx j ⟨0, hd⟩ : ℝ) * (q : ℝ)⁻¹ := by
        rw [div_eq_mul_inv] at hk
        exact hk
      _ ≤ ((idx j ⟨0, hd⟩ : ℝ) + r) * (q : ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_right (by linarith) hh.le
  have hxhi : x ⟨0, hd⟩ ≤ (2 / 3 : ℝ) := by
    have hk := hactive.2.2
    rw [hxrepr]
    have hr1 : r ≤ 1 := by linarith [hrhi]
    calc
      ((idx j ⟨0, hd⟩ : ℝ) + r) * (q : ℝ)⁻¹ ≤
          ((idx j ⟨0, hd⟩ : ℝ) + 1) * (q : ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_right (by linarith) hh.le
      _ ≤ (2 / 3 : ℝ) := by
        simpa [div_eq_mul_inv] using hk
  have hwabs : |2 - 4 * r| ≤ 3 / 8 := by
    rw [abs_le]
    constructor <;> linarith [hrlo, hrhi]
  have hS : |∑ j : Fin K, localSign (theta j) * psi j x| ≤ 1 := by
    apply signed_bump_sum_abs_le_one (Q := Q) (ψ := psi)
      (fun _i _j hij => hgeo0.pairwise_disjoint hij)
    intro i y
    have hb := hgeo0.bump_bounds i y
    exact ⟨hb.1, hb.2, fun hy => hgeo0.bump_eq_zero_off_cell i hy⟩
  let a := kappa * (q : ℝ)⁻¹ ^ beta
  let u := x ⟨0, hd⟩ + a * triangularWave (x ⟨0, hd⟩ / (q : ℝ)⁻¹)
  let v := eps * a * ∑ j : Fin K, localSign (theta j) * psi j x
  have hau : |a * triangularWave (x ⟨0, hd⟩ / (q : ℝ)⁻¹)| ≤ 1 / 32 := by
    rw [hwave, abs_mul, abs_of_nonneg ha0]
    nlinarith
  have hv : |v| ≤ 1 / 768 := by
    rw [abs_mul, abs_mul, abs_of_nonneg heps0, abs_of_nonneg ha0]
    have hepa : eps * (kappa * (q : ℝ)⁻¹ ^ beta) ≤ 1 / 768 := by
      calc
        eps * (kappa * (q : ℝ)⁻¹ ^ beta) ≤
            (1 / 64) * (kappa * (q : ℝ)⁻¹ ^ beta) :=
          mul_le_mul_of_nonneg_right heps ha0
        _ ≤ (1 / 64) * (1 / 12) :=
          mul_le_mul_of_nonneg_left ha12 (by norm_num)
        _ = 1 / 768 := by norm_num
    exact (mul_le_of_le_one_right (mul_nonneg heps0 ha0) hS).trans hepa
  dsimp only [u, v]
  constructor
  · constructor <;> nlinarith [abs_le.mp hau]
  · constructor <;> nlinarith [abs_le.mp hau, abs_le.mp hv]

/-- The nonlinear fold is affine in the sign perturbation on active bump
support, and is unchanged when the perturbation sum vanishes. -/
lemma FoldedGeometry.foldedRawScore_additive
    {hd : 0 < d} {q K : ℕ} {Q : Fin K -> Set (XSpace d)}
    {psi : Fin K -> XSpace d -> ℝ} {B : Fin K -> Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B)
    {beta kappa eps : ℝ} (hbeta : beta < 1)
    (ha0 : 0 ≤ kappa * (q : ℝ)⁻¹ ^ beta)
    (ha12 : kappa * (q : ℝ)⁻¹ ^ beta ≤ 1 / 12)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 64)
    (theta : Fin K -> Bool) (x : XSpace d) :
    foldedRawScore hd beta (q : ℝ)⁻¹ kappa eps K psi theta x =
      foldedBaseScore hd beta (q : ℝ)⁻¹ kappa x +
        (eps * (kappa * (q : ℝ)⁻¹ ^ beta) / 2) *
          ∑ j : Fin K, localSign (theta j) * psi j x := by
  let S := ∑ j : Fin K, localSign (theta j) * psi j x
  by_cases hS : S = 0
  · simp [foldedRawScore, foldedBaseScore, hbeta, S, hS]
  · have hmem := hgeo.folded_arguments_mem_Icc ha0 ha12 heps0 heps theta x hS
    simp only [foldedRawScore, foldedBaseScore, hbeta, if_true]
    rw [triangularFold_eq_self hmem.1, triangularFold_eq_self hmem.2]
    dsimp [S] at hmem ⊢
    ring

end CausalSmith.Experimentation.PilotscorePairingFrontier
