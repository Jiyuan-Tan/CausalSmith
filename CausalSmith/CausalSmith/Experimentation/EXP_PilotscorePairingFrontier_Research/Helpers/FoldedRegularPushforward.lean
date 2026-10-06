module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedCubeBounds
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedDensityTransfer

/-! # Regular-score pushforward for the folded cube construction -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open scoped ENNReal

lemma triangularFold_mem_Icc (t : ℝ) : triangularFold t ∈ Set.Icc (0 : ℝ) 1 := by
  let z : ℤ := Int.floor ((t + 1) / 2)
  have hzle : (z : ℝ) ≤ (t + 1) / 2 := Int.floor_le _
  have hzlt : (t + 1) / 2 < (z : ℝ) + 1 := Int.lt_floor_add_one _
  unfold triangularFold
  dsimp [z] at hzle hzlt ⊢
  constructor
  · exact abs_nonneg _
  · rw [abs_le]
    constructor <;> linarith

lemma canonicalFoldedRawScore_mem_scoreInterval
    (n K : ℕ) {beta h kappa eps : ℝ} (hbeta : beta < 1)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool)
    (x : XSpace (n + 1)) :
    foldedRawScore (Nat.zero_lt_succ n) beta h kappa eps K
      (fun j => meshBump (Nat.zero_lt_succ n) h (idx j)) theta x ∈ scoreInterval := by
  unfold foldedRawScore
  simp only [hbeta, if_true, scoreInterval]
  have hf := triangularFold_mem_Icc
    (x ⟨0, Nat.zero_lt_succ n⟩ + kappa * h ^ beta *
      triangularWave (x ⟨0, Nat.zero_lt_succ n⟩ / h) +
      eps * (kappa * h ^ beta) *
        ∑ j, localSign (theta j) * meshBump (Nat.zero_lt_succ n) h (idx j) x)
  constructor <;> linarith [hf.1, hf.2]

@[no_expose]
noncomputable def foldedCubeScoreDensityReal (n q K : ℕ)
    (beta h kappa eps : ℝ)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool)
    (t : ℝ) : ℝ :=
  (foldedCubeScoreDensity n q K beta h kappa eps idx theta t).toReal

@[fun_prop]
lemma measurable_foldedCubeScoreDensityReal
    (n q K : ℕ) (beta h kappa eps : ℝ)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool) :
    Measurable (foldedCubeScoreDensityReal n q K beta h kappa eps idx theta) := by
  unfold foldedCubeScoreDensityReal
  exact (measurable_foldedCubeScoreDensity n q K beta h kappa eps idx theta).ennreal_toReal

/-- Quantitative density control on the score interval yields the model's
regular pushforward predicate. -/
lemma canonicalFoldedRawScore_regularPushforward
    (n q K : ℕ) (hq : 0 < q) {beta h kappa eps cg Cg : ℝ}
    (hbeta : beta < 1) (hhq : h = (q : ℝ)⁻¹)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (hinj : Function.Injective idx)
    (theta : Fin K -> Bool)
    (ha : 0 ≤ kappa * h ^ beta) (hscale : 4 ≤ kappa * h ^ beta / h)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 64)
    (hsmall : kappa * h ^ beta * (1 + eps) ≤ 1 / 12)
    (hcg0 : 0 < cg)
    (herror : 4 * h / (kappa * h ^ beta) + 24 * eps ≤
      min (1 - cg / 2) (Cg / 2 - 1)) :
    RegularScorePushforward
      (bernoulliUnitLaw
        (foldedRawScore (Nat.zero_lt_succ n) beta h kappa eps K
          (fun j => meshBump (Nat.zero_lt_succ n) h (idx j)) theta))
      (foldedRawScore (Nat.zero_lt_succ n) beta h kappa eps K
        (fun j => meshBump (Nat.zero_lt_succ n) h (idx j)) theta) cg Cg := by
  let g := foldedRawScore (Nat.zero_lt_succ n) beta h kappa eps K
    (fun j => meshBump (Nat.zero_lt_succ n) h (idx j)) theta
  let D := foldedCubeScoreDensity n q K beta h kappa eps idx theta
  let p := foldedCubeScoreDensityReal n q K beta h kappa eps idx theta
  have hg : Measurable g := measurable_canonicalFoldedRawScore n K hbeta idx theta
  have hrange : ∀ x ∈ cube (n + 1), 0 ≤ g x ∧ g x ≤ 1 := by
    intro x hx
    have hm := canonicalFoldedRawScore_mem_scoreInterval n K
      (h := h) (kappa := kappa) (eps := eps) hbeta idx theta x
    simpa [g, scoreInterval] using ⟨hm.1.trans' (by norm_num), hm.2.trans (by norm_num)⟩
  have hp : Measurable p :=
    measurable_foldedCubeScoreDensityReal n q K beta h kappa eps idx theta
  have hp0 : ∀ t, 0 ≤ p t := fun t => ENNReal.toReal_nonneg
  have hh : 0 < h := by rw [hhq]; positivity
  have ha_pos : 0 < kappa * h ^ beta := by
    have ha4 := (le_div_iff₀ hh).mp hscale
    linarith
  have hE0 : 0 ≤ 4 * h / (kappa * h ^ beta) + 24 * eps := by positivity
  have hdelta0 : 0 ≤ min (1 - cg / 2) (Cg / 2 - 1) :=
    hE0.trans herror
  have hdelta1 : min (1 - cg / 2) (Cg / 2 - 1) ≤ 1 := by
    have := min_le_left (1 - cg / 2) (Cg / 2 - 1)
    linarith
  have hbounds : ∀ᵐ t ∂(volume : Measure ℝ).restrict scoreInterval,
      cg ≤ p t ∧ p t ≤ Cg := by
    rw [show (volume : Measure ℝ).restrict scoreInterval =
      volume.restrict (Set.Ioo (1 / 4 : ℝ) (3 / 4 : ℝ)) by
        simp [scoreInterval, MeasureTheory.restrict_Ioo_eq_restrict_Icc]]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hb := foldedCubeScoreDensity_bounds n q K hq hhq idx hinj theta
      ha hscale heps0 heps hsmall (herror.trans hdelta1) ht
    dsimp [p, foldedCubeScoreDensityReal]
    constructor
    · have hmin := min_le_left (1 - cg / 2) (Cg / 2 - 1)
      linarith [hb.1]
    · have hmin := min_le_right (1 - cg / 2) (Cg / 2 - 1)
      linarith [hb.2]
  apply regularScorePushforward_of_cube_map_withDensity hg hrange hp hp0 hbounds
  have hfull := map_canonicalFoldedRawScore_eq_withDensity n q K hq hbeta hhq
    idx hinj theta ha hscale heps0 heps hsmall
  have hsupport : Measure.map g (cubeMeasure (n + 1)) =
      (Measure.map g (cubeMeasure (n + 1))).restrict scoreInterval := by
    symm
    apply Measure.restrict_eq_self_of_ae_mem
    exact (ae_map_iff hg.aemeasurable measurableSet_Icc).2
      (Filter.Eventually.of_forall fun x => canonicalFoldedRawScore_mem_scoreInterval
        n K (h := h) (kappa := kappa) (eps := eps) hbeta idx theta x)
  rw [hfull] at hsupport
  letI : IsProbabilityMeasure (cubeMeasure (n + 1)) :=
    cubeMeasure_isProbabilityMeasure (n + 1)
  have hDint : ∫⁻ t, D t ∂(volume : Measure ℝ) ≠ ⊤ := by
    have hm : ((volume : Measure ℝ).withDensity D) Set.univ ≠ ⊤ := by
      rw [← hfull]
      exact measure_ne_top _ _
    simpa [withDensity_apply] using hm
  have hDfinite : ∀ᵐ t ∂(volume : Measure ℝ), D t < ⊤ :=
    ae_lt_top (measurable_foldedCubeScoreDensity n q K beta h kappa eps idx theta) hDint
  calc
    Measure.map g (cubeMeasure (n + 1)) = (volume : Measure ℝ).withDensity D := hfull
    _ = ((volume : Measure ℝ).withDensity D).restrict scoreInterval := hsupport
    _ = ((volume : Measure ℝ).restrict scoreInterval).withDensity D := by
      simpa [scoreInterval] using
        (restrict_withDensity (μ := (volume : Measure ℝ)) measurableSet_Icc D)
    _ = ((volume : Measure ℝ).restrict scoreInterval).withDensity
        (fun t => ENNReal.ofReal (p t)) := by
      apply withDensity_congr_ae
      rw [show (volume : Measure ℝ).restrict scoreInterval =
        volume.restrict (Set.Ioo (1 / 4 : ℝ) (3 / 4 : ℝ)) by
          simp [scoreInterval, MeasureTheory.restrict_Ioo_eq_restrict_Icc]]
      filter_upwards [ae_restrict_of_ae hDfinite,
        ae_restrict_mem measurableSet_Ioo] with t htfinite ht
      have htop : D t ≠ ⊤ := ne_of_lt htfinite
      simp [p, foldedCubeScoreDensityReal, D, ENNReal.ofReal_toReal htop]

end CausalSmith.Experimentation.PilotscorePairingFrontier
