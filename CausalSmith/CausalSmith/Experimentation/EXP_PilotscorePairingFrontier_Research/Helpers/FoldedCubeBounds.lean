module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedCubeDensity
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedReflectedReindex

/-! # Quantitative bounds for the full folded score density -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open scoped ENNReal

lemma foldedSliceScoreDensity_ne_top
    (n q K : ℕ) (beta h kappa eps : ℝ)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool)
    (z : Fin n -> ℝ) (t : ℝ) :
    foldedSliceScoreDensity n q K beta h kappa eps idx theta z t ≠ ⊤ := by
  unfold foldedSliceScoreDensity
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (perturbedMeshFoldedDensity_ne_top q h (kappa * h ^ beta) eps
      (foldedTailCoefficient n K h idx theta z) (2 * t - 1 / 2))

lemma foldedSliceScoreDensity_error
    (n q K : ℕ) (hq : 0 < q) {beta h kappa eps t : ℝ}
    (hhq : h = (q : ℝ)⁻¹)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (hinj : Function.Injective idx)
    (theta : Fin K -> Bool) (z : Fin n -> ℝ)
    (ha : 0 ≤ kappa * h ^ beta) (hscale : 4 ≤ kappa * h ^ beta / h)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 64)
    (hsmall : kappa * h ^ beta * (1 + eps) ≤ 1 / 12)
    (ht : t ∈ Set.Ioo (1 / 4 : ℝ) (3 / 4 : ℝ)) :
    |(foldedSliceScoreDensity n q K beta h kappa eps idx theta z t).toReal - 2| ≤
      2 * (4 * h / (kappa * h ^ beta) + 24 * eps) := by
  have hy : 2 * t - 1 / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have herr := perturbedMeshFoldedDensity_error
    (foldedTailCoefficient n K h idx theta z) hq hhq ha hscale
    heps0 heps
    (fun k => foldedTailCoefficient_mem_Icc n K h hinj theta z k)
    hsmall hy
  unfold foldedSliceScoreDensity
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show 2 *
      (perturbedMeshFoldedDensity q h (kappa * h ^ beta) eps
        (foldedTailCoefficient n K h idx theta z) (2 * t - 1 / 2)).toReal - 2 =
      2 * ((perturbedMeshFoldedDensity q h (kappa * h ^ beta) eps
        (foldedTailCoefficient n K h idx theta z) (2 * t - 1 / 2)).toReal - 1) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left herr (by norm_num)

@[fun_prop]
lemma measurable_foldedCubeScoreDensity
    (n q K : ℕ) (beta h kappa eps : ℝ)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool) :
    Measurable (foldedCubeScoreDensity n q K beta h kappa eps idx theta) := by
  unfold foldedCubeScoreDensity
  letI : IsProbabilityMeasure (cubeMeasure n) := cubeMeasure_isProbabilityMeasure n
  exact (measurable_foldedSliceScoreDensity_joint n q K beta h kappa eps idx theta).lintegral_prod_left'

lemma foldedCubeScoreDensity_bounds
    (n q K : ℕ) (hq : 0 < q) {beta h kappa eps t : ℝ}
    (hhq : h = (q : ℝ)⁻¹)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (hinj : Function.Injective idx)
    (theta : Fin K -> Bool)
    (ha : 0 ≤ kappa * h ^ beta) (hscale : 4 ≤ kappa * h ^ beta / h)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 64)
    (hsmall : kappa * h ^ beta * (1 + eps) ≤ 1 / 12)
    (herror : 4 * h / (kappa * h ^ beta) + 24 * eps ≤ 1)
    (ht : t ∈ Set.Ioo (1 / 4 : ℝ) (3 / 4 : ℝ)) :
    2 - 2 * (4 * h / (kappa * h ^ beta) + 24 * eps) ≤
        (foldedCubeScoreDensity n q K beta h kappa eps idx theta t).toReal ∧
      (foldedCubeScoreDensity n q K beta h kappa eps idx theta t).toReal ≤
        2 + 2 * (4 * h / (kappa * h ^ beta) + 24 * eps) := by
  let E : ℝ := 4 * h / (kappa * h ^ beta) + 24 * eps
  let lo : ℝ := 2 - 2 * E
  let hi : ℝ := 2 + 2 * E
  have hE0 : 0 ≤ E := by
    have hh : 0 < h := by rw [hhq]; positivity
    have ha_pos : 0 < kappa * h ^ beta := by
      have ha4 := (le_div_iff₀ hh).mp hscale
      linarith
    dsimp [E]
    positivity
  have hlo0 : 0 ≤ lo := by dsimp [lo]; linarith
  have hhi0 : 0 ≤ hi := by dsimp [hi]; linarith
  have hslice (z : Fin n -> ℝ) :
      |(foldedSliceScoreDensity n q K beta h kappa eps idx theta z t).toReal - 2| ≤
        2 * E := by
    simpa [E] using foldedSliceScoreDensity_error n q K hq hhq idx hinj theta z
      ha hscale heps0 heps hsmall ht
  have hsliceLo (z : Fin n -> ℝ) : ENNReal.ofReal lo ≤
      foldedSliceScoreDensity n q K beta h kappa eps idx theta z t := by
    apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
      (foldedSliceScoreDensity_ne_top n q K beta h kappa eps idx theta z t)).1
    rw [ENNReal.toReal_ofReal hlo0]
    have := (abs_le.mp (hslice z)).1
    dsimp [lo]
    linarith
  have hsliceHi (z : Fin n -> ℝ) :
      foldedSliceScoreDensity n q K beta h kappa eps idx theta z t ≤
        ENNReal.ofReal hi := by
    apply (ENNReal.toReal_le_toReal
      (foldedSliceScoreDensity_ne_top n q K beta h kappa eps idx theta z t)
      ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal hhi0]
    have := (abs_le.mp (hslice z)).2
    dsimp [hi]
    linarith
  letI : IsProbabilityMeasure (cubeMeasure n) := cubeMeasure_isProbabilityMeasure n
  have havgLo : ENNReal.ofReal lo ≤
      foldedCubeScoreDensity n q K beta h kappa eps idx theta t := by
    unfold foldedCubeScoreDensity
    calc
      ENNReal.ofReal lo = ∫⁻ _z : (Fin n -> ℝ), ENNReal.ofReal lo ∂cubeMeasure n := by simp
      _ ≤ _ := lintegral_mono hsliceLo
  have havgHi : foldedCubeScoreDensity n q K beta h kappa eps idx theta t ≤
      ENNReal.ofReal hi := by
    unfold foldedCubeScoreDensity
    calc
      _ ≤ ∫⁻ _z : (Fin n -> ℝ), ENNReal.ofReal hi ∂cubeMeasure n :=
        lintegral_mono hsliceHi
      _ = ENNReal.ofReal hi := by simp
  have havgTop : foldedCubeScoreDensity n q K beta h kappa eps idx theta t ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top havgHi
  constructor
  · dsimp [lo] at havgLo ⊢
    exact (ENNReal.ofReal_le_iff_le_toReal havgTop).mp havgLo
  · dsimp [hi] at havgHi ⊢
    have hh := (ENNReal.toReal_le_toReal havgTop ENNReal.ofReal_ne_top).2 havgHi
    rw [ENNReal.toReal_ofReal hhi0] at hh
    simpa [E] using hh

end CausalSmith.Experimentation.PilotscorePairingFrontier
