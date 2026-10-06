module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.CalibratedModelProperties
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedSingletonMatching

/-! # Fair native prognosis envelope

The calibrated root's quadratic displacement and the bounded sign field keep
both fair control risks near the asymmetric center. This proves the native
prognosis envelope on one absolute signed neighborhood, including fallback laws.
-/
@[expose] public section
set_option linter.style.whitespace false
noncomputable section
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Quadratic centering and a small sign perturbation keep both fair control
risks in the interval where the native logit has magnitude at most one. [the documented result](goal) Under [the stated assumptions](hyp:x,hδ,hp). -/
-- @node: fair_control_risk_bounds_of_centering
lemma fair_control_risk_bounds_of_centering (b : Bool) (k : ℕ)
    (σ : Fin (k+1) → Bool) (t δ : ℝ) (x : Covariate)
    (hδ : |δ| ≤ 1/100) (hp : |fairRoot t δ (cellCoord k x)-2/5| ≤ 1/100) :
    (if b then fairRoot t δ (cellCoord k x)+δ*signFieldZ k σ x
      else fairRoot t δ (cellCoord k x)) ∈ Set.Icc (1/3 : ℝ) (2/3) := by
  have hprod : |δ*signFieldZ k σ x| ≤ 1/50 := by
    rw [abs_mul]
    calc
      _ ≤ (1/100 : ℝ)*2 := mul_le_mul hδ (signFieldZ_abs_le_two k σ x)
        (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  obtain ⟨hplo,hphi⟩ := abs_le.mp hp
  obtain ⟨hlo,hhi⟩ := abs_le.mp hprod
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> linarith

/-- [The exact fair arm normalization identifies its native control risk.](goal) Under [the stated assumptions](hyp:x). Under [the stated assumptions](hyp:hv). -/
-- @node: fairCells_armRisk_control
lemma fairCells_armRisk_control (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (t δ : ℝ) (hv : ValidCells (fairCells b k σ t δ)) (x : Covariate) :
    armRisk (totalCellLaw (fairCells b k σ t δ)) false x =
      if b then fairRoot t δ (cellCoord k x)+δ*signFieldZ k σ x
      else fairRoot t δ (cellCoord k x) := by
  rw [armRisk, totalCellLaw_cells_of_valid _ hv]
  simp only [fairCells, Bool.false_eq_true, ↓reduceIte]
  ring

/-- [Centered fair roots give the native prognosis envelope even if cell
continuity has not yet been established, because the fallback has zero logit. [the documented result](goal) Under [the stated assumptions](hyp:hδ,hp). -/
-- @node: fairCells_prognosis_envelope_of_centering
lemma fairCells_prognosis_envelope_of_centering (b : Bool) (k : ℕ)
    (σ : Fin (k+1) → Bool) (t δ : ℝ) (hδ : |δ| ≤ 1/100)
    (hp : ∀ x : Covariate, |fairRoot t δ (cellCoord k x)-2/5| ≤ 1/100) :
    PrognosisEnvelope (totalCellLaw (fairCells b k σ t δ)) := by
  classical
  intro x
  by_cases hv : ValidCells (fairCells b k σ t δ)
  · change |logit (armRisk (totalCellLaw (fairCells b k σ t δ)) false x)| ≤ 1
    rw [fairCells_armRisk_control b k σ t δ hv x]
    exact calibrated_logit_abs_le_one _
      (fair_control_risk_bounds_of_centering b k σ t δ x hδ (hp x))
  · norm_num [prognosisLogit, armRisk, totalCellLaw, hv, lawFromCells, logit]

/-- The calibration lemma's quadratic root bound yields one positive signed
radius on which both fair constructions satisfy the model's prognosis envelope. [the documented result](goal) -/
-- @node: fairCells_uniform_prognosis_envelope
lemma fairCells_uniform_prognosis_envelope : ∃ r : ℝ, 0 < r ∧ r ≤ 1/100 ∧
    ∀ k : ℕ, 1 ≤ k → ∀ σ : Fin (k+1) → Bool,
      ∀ t δ : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ r → ∀ b,
        PrognosisEnvelope (totalCellLaw (fairCells b k σ t δ)) := by
  obtain ⟨ε, M, hε, hM, _, _, _, _, hf⟩ := exact_calibrations
  let r := min ε (min (1/100) (1/(100*(M+1))))
  have hr : 0 < r := lt_min hε (lt_min (by norm_num) (by positivity))
  have hre : r ≤ ε := min_le_left _ _
  have hrs : r ≤ 1/100 := (min_le_right _ _).trans (min_le_left _ _)
  have hrM : r ≤ 1/(100*(M+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hMr : M*r ≤ 1/100 := by
    have hh := (le_div_iff₀ (show 0 < 100*(M+1) by positivity)).mp hrM
    nlinarith
  refine ⟨r, hr, hrs, ?_⟩
  intro k hk σ t δ ht hδ b
  apply fairCells_prognosis_envelope_of_centering b k σ t δ (hδ.trans hrs)
  intro x
  have hh := hf t δ (cellCoord k x) ht (hδ.trans hre) (cellCoord_mem_unit k hk x)
  have hp := hh.2.2.2.2.2.2.2.2.1
  have hs : δ^2 ≤ r^2 := by nlinarith [sq_abs δ, abs_nonneg δ]
  have hb : M*δ^2 ≤ M*r^2 := mul_le_mul_of_nonneg_left hs hM.le
  nlinarith [abs_nonneg (deriv (fairRoot t δ) (cellCoord k x))]

/-- The two remaining spatial prognosis obligations, separated from the
pointwise envelope already proved from quadratic root centering. -/
-- @node: CalibratedPrognosisSpatialBounds
structure CalibratedPrognosisSpatialBounds (β : ℝ) (k : ℕ) (P : ObservedLaw) : Prop where
  prognosis_linear : ∀ x z, |prognosisLogit P x-prognosisLogit P z| ≤
    (k : ℝ) ^ (1-β) * |(x : ℝ)-(z : ℝ)|
  prognosis_oscillation : ∀ x z, |prognosisLogit P x-prognosisLogit P z| ≤
    2 * (k : ℝ) ^ (-β)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
