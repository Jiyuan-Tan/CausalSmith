module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.ConditionalMargins
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.MembershipSupport
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.SourceOverlap

/-! # Probability and covariate support of the legal primitive laws

The normalized finite masses and the zero-integral perturbation verify the
probability-law requirement in the membership roadmap (7), (13)--(18).
-/

public section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Covariate mixing preserves the unit-interval covariate support.  Under [the displayed assumptions and inputs](hyp:s,density,mass,hm), [the stated conclusion holds](goal). -/
-- @node: primitivePopulation_covariate_support
lemma primitivePopulation_covariate_support (s : Bool) (density : ℝ → ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1) :
    ∀ᵐ o ∂primitivePopulation s density mass, covariate o ∈ covariateSpace := by
  have hcov : Measurable covariate := by unfold covariate; fun_prop
  have hbad : MeasurableSet {o : FullData | covariate o ∉ covariateSpace} := by
    exact (measurableSet_Icc.preimage hcov).compl
  rw [ae_iff]
  unfold primitivePopulation
  rw [Measure.bind_apply hbad (primitiveKernel_measurable_of s mass hm).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  have hx : ∀ᵐ x ∂(volume.restrict covariateSpace).withDensity
      (fun x => ENNReal.ofReal (density x)), x ∈ covariateSpace :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hx] with x hx
  simp [primitiveKernel, covariate, hx]

/-- Two normalized primitive populations give a normalized full-data mixture.  Under [the displayed assumptions and inputs](hyp:fS,fT,e,mass,hm,hm0,hsum,hS,hT), [the stated conclusion holds](goal). -/
-- @node: lawFromMass_full_isProbability
lemma lawFromMass_full_isProbability (fS fT e : ℝ → ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1)
    (hm0 : ∀ x d0 d1 y0 y1, 0 ≤ mass x d0 d1 y0 y1)
    (hsum : ∀ x, ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      mass x d0 d1 y0 y1 = 1)
    (hS : ((volume.restrict covariateSpace).withDensity
      (fun x => ENNReal.ofReal (fS x))) univ = 1)
    (hT : ((volume.restrict covariateSpace).withDensity
      (fun x => ENNReal.ofReal (fT x))) univ = 1) :
    IsProbabilityMeasure (lawFromMass fS fT e mass).fullLaw := by
  constructor
  change ((1 / 2 : ℝ≥0∞) • primitivePopulation true fS mass +
    (1 / 2 : ℝ≥0∞) • primitivePopulation false fT mass) univ = 1
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    primitivePopulation_univ true fS mass hm hm0 hsum,
    primitivePopulation_univ false fT mass hm hm0 hsum, hS, hT]
  simpa using ENNReal.inv_two_add_inv_two

/-- The full mixture satisfies the covariate and potential-outcome support clause.  Under [the displayed assumptions and inputs](hyp:fS,fT,e,mass,hm), [the stated conclusion holds](goal). -/
-- @node: lawFromMass_full_support
lemma lawFromMass_full_support (fS fT e : ℝ → ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1) :
    ∀ᵐ o ∂(lawFromMass fS fT e mass).fullLaw,
      covariate o ∈ covariateSpace ∧
      outcome0 o ∈ Icc (0 : ℝ) 1 ∧ outcome1 o ∈ Icc (0 : ℝ) 1 := by
  change ∀ᵐ o ∂(1 / 2 : ℝ≥0∞) • primitivePopulation true fS mass +
    (1 / 2 : ℝ≥0∞) • primitivePopulation false fT mass, _
  rw [ae_add_measure_iff]
  constructor <;> apply Measure.ae_smul_measure
  · exact (primitivePopulation_covariate_support true fS mass hm).and
      (primitivePopulation_outcome_bounds true fS mass hm)
  · exact (primitivePopulation_covariate_support false fT mass hm).and
      (primitivePopulation_outcome_bounds false fT mass hm)

/-- The baseline center's full-data law is a probability measure.  Under [the displayed assumptions and inputs](hyp:a,n,hb), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_full_isProbability
lemma mixtureCenter_full_isProbability (a : ℝ) (n : ℕ)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4) :
    IsProbabilityMeasure (mixtureCenter a n).fullLaw := by
  apply lawFromMass_full_isProbability
  · exact fun _ _ _ _ => measurable_const
  · intro x d0 d1 y0 y1
    exact primitiveMass_nonneg_of_bounds (actualStrength a n) 0 0 hb
      (by norm_num) (by norm_num) (by nlinarith [hb.1]) d0 d1 y0 y1
  · intro x
    exact primitiveMass_sum (actualStrength a n) 0 0 (ne_of_gt hb.1) (by norm_num)
  · simp [covariateSpace]
  · simp [covariateSpace]

/-- The perturbed component's full-data law is a probability measure. Under [the displayed assumptions and inputs](hyp:a,n,cStar,sgn,hb,hAdm,hn,hτ), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_full_isProbability
lemma legalIVComponent_full_isProbability (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1)
    (hn : 0 < n) :
    IsProbabilityMeasure (legalIVComponent a n cStar τ sgn).fullLaw := by
  apply lawFromMass_full_isProbability
  · exact lowerMass_measurable a n cStar τ sgn
  · exact lowerMass_nonneg a n cStar τ sgn hb hAdm hτ
  · intro x
    apply primitiveMass_sum _ _ _ (ne_of_gt hb.1)
    have h := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
    have h' := le_trans h hAdm.2.1
    nlinarith [sq_abs (tiledPerturbation cStar n sgn x),
      abs_nonneg (tiledPerturbation cStar n sgn x)]
  · simp [covariateSpace]
  · apply targetDensity_univ cStar n sgn hn
    intro x
    have h := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
    have h' := le_trans h hAdm.2.1
    linarith [neg_abs_le (tiledPerturbation cStar n sgn x)]

/-- All primitive component covariates and potential outcomes have the required support.  Under [the displayed assumptions and inputs](hyp:a,n,cStar,sgn), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_full_support
lemma legalIVComponent_full_support (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool) :
    ∀ᵐ o ∂(legalIVComponent a n cStar τ sgn).fullLaw,
      covariate o ∈ covariateSpace ∧
      outcome0 o ∈ Icc (0 : ℝ) 1 ∧ outcome1 o ∈ Icc (0 : ℝ) 1 :=
  lawFromMass_full_support _ _ _ _ (lowerMass_measurable a n cStar τ sgn)

/-- The center's covariates and potential outcomes have the required support.  Under [the displayed assumptions and inputs](hyp:a,n), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_full_support
lemma mixtureCenter_full_support (a : ℝ) (n : ℕ) :
    ∀ᵐ o ∂(mixtureCenter a n).fullLaw,
      covariate o ∈ covariateSpace ∧
      outcome0 o ∈ Icc (0 : ℝ) 1 ∧ outcome1 o ∈ Icc (0 : ℝ) 1 :=
  lawFromMass_full_support _ _ _ _ (fun _ _ _ _ => measurable_const)

/-- Summing the normalized observed cells leaves the uniform covariate marginal.  Under [the displayed assumptions and inputs](hyp:a,u,hu,hq), [the stated conclusion holds](goal). -/
-- @node: explicitSourceLaw_covariate
lemma explicitSourceLaw_covariate (a τ : ℝ) (u : ℝ → ℝ)
    (hu : Measurable u)
    (hq : ∀ x c, 0 ≤ sourceCellMass a (u x) (τ * u x) c) :
    (explicitSourceLaw a u (fun x => τ * u x)).map Prod.fst =
      volume.restrict covariateSpace := by
  classical
  ext B hB
  rw [Measure.map_apply measurable_fst hB,
    explicitSourceLaw_apply a u (fun x => τ * u x) hu
      (measurable_const.mul hu) _ (hB.preimage measurable_fst)]
  unfold encodedCellSetMass
  have hsum (x : ℝ) :
      ∑ c : SourceCell, ENNReal.ofReal (sourceCellMass a (u x) (τ * u x) c) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => hq x c), sourceCellMass_sum]
    simp
  calc
    _ = ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) x
        ∂volume.restrict covariateSpace := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ B
      · simpa [sourceCellObservation, hx] using hsum x
      · simp [sourceCellObservation, hx]
    _ = _ := lintegral_indicator_one hB

/-- The center's observed source covariate density is exactly one.  Under [the displayed assumptions and inputs](hyp:a,n,hb), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_sourceXLaw
lemma mixtureCenter_sourceXLaw (a : ℝ) (n : ℕ)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4) :
    sourceXLaw (mixtureCenter a n) = volume.restrict covariateSpace := by
  change (Measure.map observeSource (assignedFrom
    (primitivePopulation true (fun _ => 1)
      (fun _ => primitiveMass (actualStrength a n) 0 0)) (fun _ => 1 / 2))).map
    Prod.fst = _
  rw [centerSourceLaw_eq_explicit a n hb]
  have hq (x : ℝ) (c : SourceCell) :
      0 ≤ sourceCellMass (actualStrength a n) 0 (0 * 0) c := by
    simpa [sourceCenterMass] using
      (sourceCenterMass_pos (actualStrength a n) ⟨hb.1, by linarith [hb.2]⟩ c).le
  simpa using explicitSourceLaw_covariate (actualStrength a n) 0
    (fun _ => 0) measurable_const hq

/-- The component's observed source covariate density is exactly one. Under [the displayed assumptions and inputs](hyp:a,n,cStar,sgn,hb,hAdm,hτ), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_sourceXLaw
lemma legalIVComponent_sourceXLaw (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1) :
    sourceXLaw (legalIVComponent a n cStar τ sgn) = volume.restrict covariateSpace := by
  have hq := lowerSourceCellMass_nonneg a n cStar τ sgn hb hAdm hτ
  have hsource := sourceLaw_eq_explicit_of_nonneg a n cStar τ sgn
    (lowerMass_nonneg a n cStar τ sgn hb hAdm hτ)
    (fun x z => (lowerAssignmentWeight_mem_Icc a n cStar τ sgn hAdm x z).1)
    hb.1 (by
      intro x
      have h := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
      have h' := le_trans h hAdm.2.1
      nlinarith [sq_abs (tiledPerturbation cStar n sgn x),
        abs_nonneg (tiledPerturbation cStar n sgn x)])
  change (sourceObsLaw (legalIVComponent a n cStar τ sgn)).map Prod.fst = _
  change (Measure.map observeSource (assignedFrom
    (primitivePopulation true (fun _ => 1) (lowerMass a n cStar τ sgn))
    (fun x => 1 / 2 + tiledPerturbation cStar n sgn x))).map Prod.fst = _
  rw [hsource]
  exact explicitSourceLaw_covariate (actualStrength a n) τ _
    (tiledPerturbation_measurable cStar n sgn) hq

/-- The center satisfies every source-density bound and full-data support requirement.  Under [the displayed assumptions and inputs](hyp:a,c_f,C_f,n,hf,hF,hb), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_sourceDensityBounds
lemma mixtureCenter_sourceDensityBounds (a c_f C_f : ℝ) (n : ℕ)
    (hf : 0 < c_f ∧ c_f < 1) (hF : 1 < C_f)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4) :
    SourceDensityBounds c_f C_f (mixtureCenter a n) := by
  refine ⟨hf, hF, mixtureCenter_full_isProbability a n hb,
    mixtureCenter_full_support a n, ?_, ?_⟩
  · simpa [mixtureCenter, lawFromMass] using mixtureCenter_sourceXLaw a n hb
  · intro x hx
    exact ⟨hf.2.le, hF.le⟩

/-- The perturbed component satisfies every source-density and full-data support requirement. Under [the displayed assumptions and inputs](hyp:a,c_f,C_f,n,cStar,sgn,hf,hF,hb,hAdm,hn,hτ), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_sourceDensityBounds
lemma legalIVComponent_sourceDensityBounds (a c_f C_f : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hf : 0 < c_f ∧ c_f < 1) (hF : 1 < C_f)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1) (hn : 0 < n) :
    SourceDensityBounds c_f C_f (legalIVComponent a n cStar τ sgn) := by
  refine ⟨hf, hF, legalIVComponent_full_isProbability a n cStar τ sgn hb hAdm hτ hn,
    legalIVComponent_full_support a n cStar τ sgn, ?_, ?_⟩
  · simpa [legalIVComponent, lawFromMass] using
      legalIVComponent_sourceXLaw a n cStar τ sgn hb hAdm hτ
  · intro x hx
    exact ⟨hf.2.le, hF.le⟩

/-- The center's target density is uniform and obeys both envelopes.  Under [the displayed assumptions and inputs](hyp:a,c_f,C_f,n,hf,hF,hb), [the stated conclusion holds](goal). -/
lemma mixtureCenter_targetDensityBounds (a c_f C_f : ℝ) (n : ℕ)
    (hf : 0 < c_f ∧ c_f < 1) (hF : 1 < C_f)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4) :
    TargetDensityBounds c_f C_f (mixtureCenter a n) := by
  constructor
  · simpa [targetXLaw, populationLaw, mixtureCenter, lawFromMass] using
      centerTargetLaw_eq_volume a n hb
  · refine ⟨?_, hf.1⟩
    intro x hx
    exact ⟨hf.2.le, hF.le⟩

/-- The component's target density obeys the envelopes when the height respects their margins. Under [the displayed assumptions and inputs](hyp:a,c_f,C_f,n,cStar,sgn,hb,hAdm,hn,hlo,hhi,hf,hτ), [the stated conclusion holds](goal). -/
lemma legalIVComponent_targetDensityBounds (a c_f C_f : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1) (hn : 0 < n)
    (hlo : lowerHeight cStar n ≤ 1 - c_f)
    (hhi : lowerHeight cStar n ≤ C_f - 1) (hf : 0 < c_f) :
    TargetDensityBounds c_f C_f (legalIVComponent a n cStar τ sgn) := by
  constructor
  · exact legalTargetLaw_eq_density a n cStar τ sgn hb hAdm hτ hn
  · refine ⟨?_, hf⟩
    intro x hx
    have hu := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
    change c_f ≤ 1 + tiledPerturbation cStar n sgn x ∧
      1 + tiledPerturbation cStar n sgn x ≤ C_f
    constructor <;> linarith [neg_abs_le (tiledPerturbation cStar n sgn x),
      le_abs_self (tiledPerturbation cStar n sgn x)]

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
