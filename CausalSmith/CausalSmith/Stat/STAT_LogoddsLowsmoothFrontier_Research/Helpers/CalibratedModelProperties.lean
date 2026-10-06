module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.CalibratedEffects
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.CalibratedHolderModulus

/-! # Basic model properties of the calibrated constructions

The explicit cells give uniform covariate design, homogeneous scalar effects,
and the required effect envelopes. Fair treatment is exactly balanced. Only
native logit envelopes and spatial scale bounds remain in the reduced assembly.
-/
@[expose] public section
noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Totalization retains the public uniform design, even on fallback inputs. [the stated conclusion](goal) holds. -/
-- @node: totalCellLaw_uniform
lemma totalCellLaw_uniform (p : Bool → Bool → Covariate → ℝ) :
    Measure.map covariate (totalCellLaw p).measure = uniformLaw := by
  classical
  unfold totalCellLaw
  split
  · rename_i hp
    change Measure.map covariate (jointLaw uniformLaw p) = uniformLaw
    exact jointLaw_uniform p hp
  · change Measure.map covariate (jointLaw uniformLaw (fun _ _ _ => 1/4)) = uniformLaw
    exact jointLaw_uniform _ fairDefault_valid

/-- Fair tables have exactly balanced treatment, including totalization fallback. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: fairCells_propensity_half
lemma fairCells_propensity_half (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (t δ : ℝ) (x : Covariate) :
    propensity (totalCellLaw (fairCells b k σ t δ)) x = 1/2 := by
  classical
  unfold totalCellLaw
  split
  · change fairCells b k σ t δ true false x + fairCells b k σ t δ true true x = _
    simp only [fairCells, Bool.false_eq_true, ↓reduceIte]
    ring
  · norm_num [propensity, lawFromCells]

/-- [Exact fair treatment balance makes the native propensity logit zero.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: fairCells_propensityLogit_zero
lemma fairCells_propensityLogit_zero (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (t δ : ℝ) (x : Covariate) :
    propensityLogit (totalCellLaw (fairCells b k σ t δ)) x = 0 := by
  rw [propensityLogit, fairCells_propensity_half]
  norm_num [logit]

/-- Fair supports satisfy the propensity envelope and both spatial scale bounds at every exponent and rank, because their propensity logit vanishes. the documented result Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: fairCells_propensity_bounds
lemma fairCells_propensity_bounds (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (t δ α : ℝ) :
    PropensityEnvelope (totalCellLaw (fairCells b k σ t δ)) ∧
    (∀ x z, |propensityLogit (totalCellLaw (fairCells b k σ t δ)) x -
      propensityLogit (totalCellLaw (fairCells b k σ t δ)) z| ≤
        (k : ℝ)^(1-α) * |(x : ℝ)-(z : ℝ)|) ∧
    (∀ x z, |propensityLogit (totalCellLaw (fairCells b k σ t δ)) x -
      propensityLogit (totalCellLaw (fairCells b k σ t δ)) z| ≤ 2*(k : ℝ)^(-α)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [fairCells_propensityLogit_zero]
    norm_num
  · intro x z
    rw [fairCells_propensityLogit_zero, fairCells_propensityLogit_zero]
    simp only [sub_self, abs_zero]
    positivity
  · intro x z
    rw [fairCells_propensityLogit_zero, fairCells_propensityLogit_zero]
    simp only [sub_self, abs_zero]
    positivity

/-- [The mixed effect from cell odds stays in the model envelope on the signed
calibration square; uniform design and homogeneity hold for every valid table. [the documented result](goal) Under [the stated assumptions](hyp:hη,hζ,hv). -/
-- @node: mixedCells_basic_model_properties
lemma mixedCells_basic_model_properties (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (η ζ : ℝ) (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100)
    (hv : ValidCells (mixedCells b k σ η ζ)) :
    UniformDesign (mixedLaw b k σ η ζ) ∧
      HomogeneousLogit (mixedLaw b k σ η ζ) ∧ EffectEnvelope (mixedLaw b k σ η ζ) := by
  obtain ⟨he,hh⟩ := mixedCells_homogeneous_effect b k σ η ζ hη hζ hv
  refine ⟨totalCellLaw_uniform _, hh, ?_⟩
  change |effect (mixedLaw b k σ η ζ)| ≤ 1/2
  rw [he]
  cases b
  · norm_num
  · simp only [↓reduceIte, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 32)]
    have h := mul_le_mul hη hζ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/100)
    nlinarith

/-- [Fair effects and comparator effects lie in the model envelope, as follows
from exact cell odds and the calibrated comparator range. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hv). -/
-- @node: fairCells_basic_model_properties
lemma fairCells_basic_model_properties (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (t δ : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100)
    (hv : ValidCells (fairCells b k σ t δ)) :
    UniformDesign (totalCellLaw (fairCells b k σ t δ)) ∧
      HomogeneousLogit (totalCellLaw (fairCells b k σ t δ)) ∧
      EffectEnvelope (totalCellLaw (fairCells b k σ t δ)) := by
  obtain ⟨he,hh⟩ := fairCells_homogeneous_effect b k σ t δ hδ hv
  refine ⟨totalCellLaw_uniform _, hh, ?_⟩
  change |effect (totalCellLaw (fairCells b k σ t δ))| ≤ 1/2
  rw [he]
  obtain ⟨hlo,hhi⟩ := comparatorEffect_range_bounds t δ ht hδ
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [abs_of_nonneg (by linarith : 0 ≤ comparatorEffect t δ)]
    linarith [ht.2]
  · rw [abs_of_nonneg ht.1]
    linarith [ht.2]

/-- [Interior probabilities between one third and two thirds have native
logit magnitude at most one, using the two elementary logarithm bounds. [the documented result](goal) Under [the stated assumptions](hyp:hp). -/
-- @node: calibrated_logit_abs_le_one
lemma calibrated_logit_abs_le_one (p : ℝ) (hp : p ∈ Set.Icc (1/3 : ℝ) (2/3)) :
    |logit p| ≤ 1 := by
  have hpos : 0 < p := by linarith [hp.1]
  have hc : 0 < 1-p := by linarith [hp.2]
  have hlo : (1/2 : ℝ) ≤ p/(1-p) := (le_div_iff₀ hc).mpr (by linarith [hp.1])
  have hhi : p/(1-p) ≤ 2 := (div_le_iff₀ hc).mpr (by linarith [hp.2])
  have hi : (p/(1-p))⁻¹ ≤ 2 := by
    rw [inv_div]
    apply (div_le_iff₀ hpos).mpr
    linarith [hp.1]
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hpos hc)
  have hu := Real.log_le_sub_one_of_pos (div_pos hpos hc)
  change |Real.log (p/(1-p))| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Small covariance and centered margins keep the table's control risk
between one third and two thirds. [the documented result](goal) Under [the stated assumptions](hyp:he,hm,hc). -/
-- @node: mixed_table_control_risk_bounds
lemma mixed_table_control_risk_bounds (e m c : ℝ)
    (he : |e-1/2| ≤ 1/40) (hm : |m-1/2| ≤ 1/40) (hc : |c| ≤ 1/24) :
    tableCell e m c false true /
      (tableCell e m c false false + tableCell e m c false true) ∈
        Set.Icc (1/3 : ℝ) (2/3) := by
  obtain ⟨helo,hehi⟩ := abs_le.mp he
  obtain ⟨hmlo,hmhi⟩ := abs_le.mp hm
  obtain ⟨hclo,hchi⟩ := abs_le.mp hc
  have hd : 0 < 1-e := by linarith
  simp only [tableCell, Bool.false_eq_true, ↓reduceIte]
  have hn : (1-e)*(1-m)+c+((1-e)*m-c) = 1-e := by ring
  rw [hn]
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ 1-e by linarith)
      (show 0 ≤ m-19/40 by linarith)]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ 1-e by linarith)
      (show 0 ≤ 21/40-m by linarith)]

/-- [Both mixed native logit envelopes follow from the centered margins and
small calibrated covariance on the fixed signed support square. [the documented result](goal) Under [the stated assumptions](hyp:hη,hζ,hv). -/
-- @node: mixedCells_logit_envelopes
lemma mixedCells_logit_envelopes (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (η ζ : ℝ) (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100)
    (hv : ValidCells (mixedCells b k σ η ζ)) :
    PropensityEnvelope (mixedLaw b k σ η ζ) ∧
      PrognosisEnvelope (mixedLaw b k σ η ζ) := by
  have hcells := totalCellLaw_cells_of_valid _ hv
  constructor
  · intro x
    obtain ⟨he,_⟩ := mixed_margin_bounds b k σ η ζ x hη hζ
    apply calibrated_logit_abs_le_one
    change propensity (totalCellLaw (mixedCells b k σ η ζ)) x ∈ _
    rw [propensity, hcells]
    simp only [mixedCells, tableCell, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨helo,hehi⟩ := abs_le.mp he
    constructor <;> linarith
  · intro x
    obtain ⟨he,hm⟩ := mixed_margin_bounds b k σ η ζ x hη hζ
    apply calibrated_logit_abs_le_one
    change armRisk (totalCellLaw (mixedCells b k σ η ζ)) false x ∈ _
    rw [armRisk, hcells]
    dsimp only [mixedCells]
    apply mixed_table_control_risk_bounds _ _ _ he hm
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at he ⊢
    · norm_num
    · have ht : |32*η*ζ| ≤ 1/8 := by
        simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 32)]
        have h := mul_le_mul hη hζ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/100)
        nlinarith
      exact (covarianceBranch_local_bounds _ _ _ ht (by linarith) (by linarith)).2.2

/-- [The remaining mixed spatial scale bounds after design, homogeneous effects,
and all three pointwise envelopes have been proved from explicit cells. -/
-- @node: CalibratedSpatialBounds
structure CalibratedSpatialBounds (α β : ℝ) (k : ℕ) (P : ObservedLaw) : Prop where
  propensity_linear : ∀ x z, |propensityLogit P x-propensityLogit P z| ≤
    (k : ℝ) ^ (1-α) * |(x : ℝ)-(z : ℝ)|
  propensity_oscillation : ∀ x z, |propensityLogit P x-propensityLogit P z| ≤
    2 * (k : ℝ) ^ (-α)
  prognosis_linear : ∀ x z, |prognosisLogit P x-prognosisLogit P z| ≤
    (k : ℝ) ^ (1-β) * |(x : ℝ)-(z : ℝ)|
  prognosis_oscillation : ∀ x z, |prognosisLogit P x-prognosisLogit P z| ≤
    2 * (k : ℝ) ^ (-β)

/-- Native-logit spatial bounds combine with independently proved mixed
cell-law properties and envelopes to feed the global Hölder assembly. [the documented result](goal) Under [the stated assumptions](hyp:hη,hζ,hv,h). -/
-- @node: mixedCells_model_bounds_of_spatial
lemma mixedCells_model_bounds_of_spatial (α β : ℝ) (b : Bool) (k : ℕ)
    (σ : Fin (k+1) → Bool) (η ζ : ℝ) (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100)
    (hv : ValidCells (mixedCells b k σ η ζ))
    (h : CalibratedSpatialBounds α β k (mixedLaw b k σ η ζ)) :
    CalibratedModelBounds α β k (mixedLaw b k σ η ζ) := by
  obtain ⟨hu,hh,he⟩ := mixedCells_basic_model_properties b k σ η ζ hη hζ hv
  obtain ⟨hp,hn⟩ := mixedCells_logit_envelopes b k σ η ζ hη hζ hv
  exact ⟨hu,hh,he,hp,hn,h.propensity_linear,h.propensity_oscillation,
    h.prognosis_linear,h.prognosis_oscillation⟩

/-- [For fair treatment, only the prognosis envelope and its two spatial scale
bounds remain; the propensity logit is already identically zero. -/
-- @node: CalibratedPrognosisBounds
structure CalibratedPrognosisBounds (β : ℝ) (k : ℕ) (P : ObservedLaw) : Prop where
  prognosis_envelope : PrognosisEnvelope P
  prognosis_linear : ∀ x z, |prognosisLogit P x-prognosisLogit P z| ≤
    (k : ℝ) ^ (1-β) * |(x : ℝ)-(z : ℝ)|
  prognosis_oscillation : ∀ x z, |prognosisLogit P x-prognosisLogit P z| ≤
    2 * (k : ℝ) ^ (-β)

/-- The actual fair tables' balanced treatment supplies every propensity
obligation, leaving just the native prognosis bounds for Hölder assembly. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hv,h). -/
-- @node: fairCells_model_bounds_of_prognosis
lemma fairCells_model_bounds_of_prognosis (α β : ℝ) (b : Bool) (k : ℕ)
    (σ : Fin (k+1) → Bool) (t δ : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/4))
    (hδ : |δ| ≤ 1/100) (hv : ValidCells (fairCells b k σ t δ))
    (h : CalibratedPrognosisBounds β k (totalCellLaw (fairCells b k σ t δ))) :
    CalibratedModelBounds α β k (totalCellLaw (fairCells b k σ t δ)) := by
  obtain ⟨hp,hlin,hosc⟩ := fairCells_propensity_bounds b k σ t δ α
  obtain ⟨hu,hh,he⟩ := fairCells_basic_model_properties b k σ t δ ht hδ hv
  exact ⟨hu,hh,he,hp,h.prognosis_envelope,hlin,hosc,
    h.prognosis_linear,h.prognosis_oscillation⟩

end CausalSmith.Stat.LogoddsLowsmoothFrontier
