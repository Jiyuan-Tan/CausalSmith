module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedJointDensity
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.BernoulliHypercube

/-! # Full-cube density from folded transverse slices -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open scoped ENNReal

noncomputable def foldedCubeScoreDensity (n q K : ℕ)
    (beta h kappa eps : ℝ)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool)
    (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, foldedSliceScoreDensity n q K beta h kappa eps idx theta z t
    ∂cubeMeasure n

@[fun_prop]
lemma measurable_canonicalFoldedRawScore (n K : ℕ)
    {beta h kappa eps : ℝ} (hbeta : beta < 1)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool) :
    Measurable (foldedRawScore (Nat.zero_lt_succ n) beta h kappa eps K
      (fun j => meshBump (Nat.zero_lt_succ n) h (idx j)) theta) := by
  unfold foldedRawScore
  simp only [hbeta, if_true]
  fun_prop

/-- Disintegrating reciprocal-cube volume along the first coordinate and
reassembling the exact slice laws gives the full folded score density. -/
lemma map_canonicalFoldedRawScore_eq_withDensity
    (n q K : ℕ) (hq : 0 < q) {beta h kappa eps : ℝ}
    (hbeta : beta < 1) (hhq : h = (q : ℝ)⁻¹)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (hinj : Function.Injective idx)
    (theta : Fin K -> Bool)
    (ha : 0 ≤ kappa * h ^ beta) (hscale : 4 ≤ kappa * h ^ beta / h)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 64)
    (hsmall : kappa * h ^ beta * (1 + eps) ≤ 1 / 12) :
    Measure.map
        (foldedRawScore (Nat.zero_lt_succ n) beta h kappa eps K
          (fun j => meshBump (Nat.zero_lt_succ n) h (idx j)) theta)
        (cubeMeasure (n + 1)) =
      (volume : Measure ℝ).withDensity
        (foldedCubeScoreDensity n q K beta h kappa eps idx theta) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let g := foldedRawScore (Nat.zero_lt_succ n) beta h kappa eps K
    (fun j => meshBump (Nat.zero_lt_succ n) h (idx j)) theta
  let F : ℝ × (Fin n -> ℝ) -> ℝ := fun xz => g (e.symm xz)
  have hg : Measurable g :=
    measurable_canonicalFoldedRawScore n K hbeta idx theta
  have hF : Measurable F := hg.comp e.symm.measurable
  have htransport : Measure.map g (cubeMeasure (n + 1)) =
      Measure.map F (((volume : Measure ℝ).restrict (Set.Icc 0 1)).prod
        (cubeMeasure n)) := by
    calc
      Measure.map g (cubeMeasure (n + 1)) =
          Measure.map F (Measure.map e (cubeMeasure (n + 1))) := by
        rw [Measure.map_map hF e.measurable]
        congr 1
        funext x
        exact congrArg g (e.symm_apply_apply x).symm
      _ = _ := by rw [cubeMeasure_map_piFinSuccAbove_prod]
  rw [htransport]
  letI : IsProbabilityMeasure (cubeMeasure n) := cubeMeasure_isProbabilityMeasure n
  apply map_prod_eq_withDensity_lintegral_slices hF
    (measurable_foldedSliceScoreDensity_joint n q K beta h kappa eps idx theta)
  intro z
  exact map_foldedRawScore_slice_eq_withDensity n q K hq hbeta hhq idx hinj
    theta z ha hscale heps0 heps hsmall

end CausalSmith.Experimentation.PilotscorePairingFrontier
