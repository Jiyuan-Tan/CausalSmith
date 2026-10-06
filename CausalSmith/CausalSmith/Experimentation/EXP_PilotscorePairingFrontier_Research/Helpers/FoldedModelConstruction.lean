module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedHolderScore

/-! # Model membership for the folded likelihood family -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

lemma FoldedGeometry.regularScoreModel
    {hd : 0 < d} {q K : ℕ} {Q : Fin K -> Set (XSpace d)}
    {psi : Fin K -> XSpace d -> ℝ} {B : Fin K -> Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B)
    {beta L cX CX cg Cg kappa eps : ℝ}
    (hpars : ValidClassParameters d beta L cX CX cg Cg)
    (hbeta : beta < 1) (hkappa0 : 0 ≤ kappa)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 64)
    (hepsD : (128 * (d : ℝ)) * eps ≤ 1)
    (hholder : 1 / 2 + (128 * (d : ℝ)) * kappa ≤ L)
    (hscale : 4 ≤ kappa * (q : ℝ)⁻¹ ^ beta / (q : ℝ)⁻¹)
    (hsmall : kappa * (q : ℝ)⁻¹ ^ beta * (1 + eps) ≤ 1 / 12)
    (herror : 4 * (q : ℝ)⁻¹ / (kappa * (q : ℝ)⁻¹ ^ beta) + 24 * eps ≤
      min (1 - cg / 2) (Cg / 2 - 1))
    (theta : Fin K -> Bool) :
    RegularScoreModel
      (bernoulliUnitLaw
        (foldedRawScore hd beta (q : ℝ)⁻¹ kappa eps K psi theta))
      (foldedRawScore hd beta (q : ℝ)⁻¹ kappa eps K psi theta)
      L beta cX CX cg Cg := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  let g := foldedRawScore hd beta (q : ℝ)⁻¹ kappa eps K psi theta
  have hpsi : ∀ j, Measurable (psi j) := by
    intro j
    rcases hgeo with ⟨hq, idx, hinj, hcomplete, hdefs⟩
    rw [(hdefs j).2.1]
    exact measurable_meshBump hd _ _
  have hg : Measurable g :=
    measurable_foldedRawScore_of_measurable_bumps hd beta _ kappa eps K psi hpsi theta
  have hrange : ∀ x ∈ cube (n + 1), 0 ≤ g x ∧ g x ≤ 1 := by
    intro x hx
    have hf := triangularFold_mem_Icc
      (x ⟨0, hd⟩ + kappa * (q : ℝ)⁻¹ ^ beta *
        triangularWave (x ⟨0, hd⟩ / (q : ℝ)⁻¹) +
        eps * (kappa * (q : ℝ)⁻¹ ^ beta) *
          ∑ j, localSign (theta j) * psi j x)
    simp only [g, foldedRawScore, hbeta, if_true]
    constructor <;> nlinarith [hf.1, hf.2]
  have hh : HolderScore g L beta := by
    have hbase := hgeo.foldedRawScore_holder hpars.2.1 hbeta hkappa0 heps0 hepsD theta
    intro x hx y hy
    exact (hbase x hx y hy).trans (mul_le_mul_of_nonneg_right hholder
      (Real.rpow_nonneg (by unfold euclideanDistance; positivity) _))
  have hreg : RegularScorePushforward (bernoulliUnitLaw g) g cg Cg := by
    rcases hgeo with ⟨hq, idx, hinj, hcomplete, hdefs⟩
    have hpsiEq : psi = fun j => meshBump hd ((q : ℝ)⁻¹) (idx j) := by
      funext j
      exact (hdefs j).2.1
    subst psi
    exact canonicalFoldedRawScore_regularPushforward n q K hq hbeta rfl idx hinj theta
      (mul_nonneg hkappa0 (Real.rpow_nonneg (by positivity) _)) hscale heps0 heps
      hsmall hpars.2.2.2.2.2.2.2.1 herror
  exact bernoulliUnitLaw_regularScoreModel hpars hg hrange hh hreg

end CausalSmith.Experimentation.PilotscorePairingFrontier
