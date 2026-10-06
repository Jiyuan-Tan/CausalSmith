module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.HostileRayleigh

/-! # Propensity and treatment-channel checks for the binary lower pair

These checks implement the treatment construction and the tail-envelope step
of the lower-pair membership proof. The tail check is separated from the
remaining proof that the nested sampling construction has uniform marginal.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped ENNReal

/-- The baseline treatment probability has its prescribed range on the cube. -/
-- @node: baselinePropensity_unit_interval
lemma baselinePropensity_unit_interval (d : ℕ) (q : ℝ) (hd : 1 ≤ d)
    (hq : 0 < q) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    baselinePropensity d q x ∈ Set.Icc (0 : ℝ) 1 := by
  have hb : BddAbove (Set.range x) :=
    ⟨1, by rintro y ⟨i, rfl⟩; exact (hx i (Set.mem_univ i)).2⟩
  have hn : Set.Nonempty (Set.range x) := ⟨x ⟨0, hd⟩, ⟨⟨0, hd⟩, rfl⟩⟩
  have h0 : 0 ≤ maxCoordinate x :=
    (hx ⟨0, hd⟩ (Set.mem_univ _)).1.trans
      (le_csSup hb ⟨⟨0, hd⟩, rfl⟩)
  have h1 : maxCoordinate x ≤ 1 :=
    csSup_le hn (by rintro y ⟨i, rfl⟩; exact (hx i (Set.mem_univ i)).2)
  exact ⟨Real.rpow_nonneg h0 _, Real.rpow_le_one h0 h1 (by positivity)⟩

/-- The constructed laws have a measurable, valid propensity version. -/
-- @node: lowerPair_measurablePropensity
lemma lowerPair_measurablePropensity (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (sign : Bool) :
    MeasurablePropensity (lowerPair d β q h δ M sign) := by
  constructor
  · change Measurable (fun x : cube d => baselinePropensity d q x)
    first | fun_prop | exact (baselinePropensity_measurable d q hq).comp measurable_subtype_coe
  · exact baselinePropensity_unit_interval d q hd hq

/-- Once the covariate marginal is identified, the existing cube-volume
calculation gives the global tail condition with every compatible constant. -/
-- @node: lowerPair_globalTail_of_uniformDesign
lemma lowerPair_globalTail_of_uniformDesign (d : ℕ) (β γ C h δ M : ℝ)
    (hd : 1 ≤ d) (hγ : 1 < γ) (hC : 1 ≤ C) (sign : Bool)
    (hu : UniformDesign (lowerPair d β (tailExponent γ) h δ M sign)) :
    GlobalTail (lowerPair d β (tailExponent γ) h δ M sign) C γ := by
  intro t ht
  change (lowerPair d β (tailExponent γ) h δ M sign).xLaw.real
    {x | baselinePropensity d (tailExponent γ) x ≤ t} ≤ C * t ^ tailExponent γ
  rw [hu]
  have hq : 0 < tailExponent γ := by unfold tailExponent; linarith
  calc
    _ ≤ t ^ tailExponent γ := baselinePropensity_sublevel_volume d _ hd hq t ht
    _ ≤ C * t ^ tailExponent γ := le_mul_of_one_le_left
      (Real.rpow_nonneg ht.1.le _) hC

/-- A valid treatment probability normalizes the two treatment atoms. -/
-- @node: treatmentMeasure_isProbabilityMeasure
lemma treatmentMeasure_isProbabilityMeasure (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (treatmentMeasure p) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [treatmentMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp.1 (sub_nonneg.mpr hp.2)]
  norm_num

/-- The treatment channel's mean indicator equals its nominal propensity. -/
-- @node: treatmentMeasure_integral_indicator
lemma treatmentMeasure_integral_indicator (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (∫ a : Bool, (if a then (1 : ℝ) else 0) ∂treatmentMeasure p) = p := by
  have hi (a : Bool) (c : ℝ) : Integrable (fun a : Bool => if a then (1 : ℝ) else 0)
      (ENNReal.ofReal c • Measure.dirac a) := by
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [treatmentMeasure, integral_add_measure (hi _ _) (hi _ _)]
  simp [integral_smul_measure, ENNReal.toReal_ofReal hp.1]

/-- Every cube fibre of the least-favorable treatment channel is a probability law. -/
-- @node: baselineTreatment_isProbabilityMeasure
lemma baselineTreatment_isProbabilityMeasure (d : ℕ) (q : ℝ) (hd : 1 ≤ d)
    (hq : 0 < q) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    IsProbabilityMeasure (treatmentMeasure (baselinePropensity d q x)) := by
  exact treatmentMeasure_isProbabilityMeasure _
    (baselinePropensity_unit_interval d q hd hq x hx)

end CausalSmith.Stat.GlobalTailDesignRobustCate
