module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.Duality

/-! Helpers/Converse/Moments.lean; scaffold of the indicated proof chain. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

/-- A zero-intensity latent atom has admissible intensity, overlap, and score
coordinates. -/
lemma zeroLatent_admissible (h : Bool) :
    0 ≤ latentIntensity (zeroLatent h) ∧
    latentPropensity (zeroLatent h) ∈ Icc (1 / 4 : ℝ) (3 / 4) ∧
    latentScore (zeroLatent h) ∈ Icc (0 : ℝ) 1 := by
  simp [zeroLatent, latentIntensity, latentPropensity, latentScore, Set.mem_Icc]
  norm_num

/-- The common reference atom has admissible intensity, overlap, and score
coordinates. -/
lemma referenceLatent_admissible :
    0 ≤ latentIntensity referenceLatent ∧
    latentPropensity referenceLatent ∈ Icc (1 / 4 : ℝ) (3 / 4) ∧
    latentScore referenceLatent ∈ Icc (0 : ℝ) 1 := by
  simp [referenceLatent, latentIntensity, latentPropensity, latentScore, Set.mem_Icc]
  norm_num

/-- The guarded inverse-intensity map used by the tilted prior stays in the
admissible latent region whenever its positive input lies above the dual
interval endpoint. -/
lemma latentFromIntensity_admissible (h : Bool) {a x : ℝ}
    (ha : 0 < a) (hx : x = 0 ∨ a ≤ x) :
    0 ≤ latentIntensity (latentFromIntensity h a x) ∧
    latentPropensity (latentFromIntensity h a x) ∈ Icc (1 / 4 : ℝ) (3 / 4) ∧
    latentScore (latentFromIntensity h a x) ∈ Icc (0 : ℝ) 1 := by
  rcases hx with rfl | hx
  · simpa [latentFromIntensity] using zeroLatent_admissible h
  · have hxpos : 0 < x := ha.trans_le hx
    have hratio0 : 0 ≤ a / (4 * x) := by positivity
    have hratio4 : a / (4 * x) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : 0 < 4 * x)]
      nlinarith
    have hscore0 : 0 ≤ x / (x + a) := by positivity
    have hscore1 : x / (x + a) ≤ 1 := by
      rw [div_le_one (by positivity : 0 < x + a)]
      linarith
    simp only [latentFromIntensity, if_neg hxpos.ne', latentIntensity,
      latentPropensity, latentScore, Set.mem_Icc]
    constructor
    · exact hxpos.le
    constructor
    · constructor <;> nlinarith
    · exact ⟨hscore0, hscore1⟩

/-- The inverse-intensity tilted measure is concentrated on zero together with
the dual interval. -/
lemma tiltedSide_ae_zero_or_mem_interval (a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool) :
    ∀ᵐ x ∂tiltedSide a J D h, x = 0 ∨ x ∈ Icc a 1 := by
  classical
  rw [tiltedSide, ae_add_measure_iff]
  constructor
  · rw [ae_finsetSum_measure_iff]
    intro i _
    apply Measure.ae_smul_measure
    exact (ae_dirac_iff ((measurableSet_singleton 0).union measurableSet_Icc)).2
      (Or.inr (D.nodes_mem i))
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff ((measurableSet_singleton 0).union measurableSet_Icc)).2
      (Or.inl rfl)

/-- Almost every draw from either tilted side maps to an admissible latent
cell. -/
-- keep: support certificate connecting tilted dual atoms to admissible latent cells
lemma tiltedSide_ae_latentFromIntensity_admissible (a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool) (ha : 0 < a) :
    ∀ᵐ x ∂tiltedSide a J D h,
      0 ≤ latentIntensity (latentFromIntensity h a x) ∧
      latentPropensity (latentFromIntensity h a x) ∈ Icc (1 / 4 : ℝ) (3 / 4) ∧
      latentScore (latentFromIntensity h a x) ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D h] with x hx
  exact latentFromIntensity_admissible h ha (hx.imp_right And.left)

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
