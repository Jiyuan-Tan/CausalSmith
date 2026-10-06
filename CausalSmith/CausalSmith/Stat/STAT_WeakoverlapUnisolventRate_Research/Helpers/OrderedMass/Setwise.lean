module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Template
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.OrderedMass.Geometry
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.OrderedMass.Density
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Data.List.GetD

/-! # Setwise and ordered treated-mass bounds -/
public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory
set_option linter.style.haveILetI false

/-- The conditional treatment kernel disintegrates treated mass over any
measurable covariate set. [For the stated inputs and conditions](hyp:d,P,E,hE), [the asserted conclusion holds](goal). -/
lemma orderedMass_treated_measure_disintegration {d : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (E : Set (Fin d → ℝ)) (hE : MeasurableSet E) :
    (∫⁻ x in E, (ProbabilityTheory.condDistrib
      (fun z : Obs d => z.2.1) (fun z => z.1) P x) {true} ∂covariateLaw P) =
      P {z | z.2.1 = true ∧ z.1 ∈ E} := by
  have hX : Measurable (fun z : Obs d => z.1) := by fun_prop
  have hA : AEMeasurable (fun z : Obs d => z.2.1) P :=
    (by fun_prop : Measurable (fun z : Obs d => z.2.1)).aemeasurable
  have hkernel : Measurable (fun x : Fin d → ℝ =>
      (ProbabilityTheory.condDistrib
        (fun z : Obs d => z.2.1) (fun z => z.1) P x) {true}) :=
    (ProbabilityTheory.condDistrib
      (fun z : Obs d => z.2.1) (fun z => z.1) P).measurable_coe (by simp)
  rw [show covariateLaw P = P.map (fun z : Obs d => z.1) from rfl]
  rw [Measure.restrict_map hX hE]
  rw [lintegral_map hkernel hX]
  have hdis := ProbabilityTheory.setLIntegral_preimage_condDistrib
    hX hA (show MeasurableSet ({true} : Set Bool) by simp) hE
  have hset : (fun z : Obs d => z.1) ⁻¹' E ∩
      (fun z : Obs d => z.2.1) ⁻¹' {true} =
      {z : Obs d | z.2.1 = true ∧ z.1 ∈ E} := by
    ext z
    simp [and_comm]
  rw [hset] at hdis
  exact hdis

/-- The propensity version from the model gives the same setwise treated mass. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel,E,hE), [the asserted conclusion holds](goal). -/
lemma orderedMass_treated_measure_propensity {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (E : Set (Fin d → ℝ)) (hE : MeasurableSet E) :
    (∫⁻ x in E, ENNReal.ofReal (e x) ∂covariateLaw (Pc.map observed)) =
      (Pc.map observed) {z | z.2.1 = true ∧ z.1 ∈ E} := by
  letI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  have hAE : (fun x => ENNReal.ofReal (e x)) =ᵐ[covariateLaw (Pc.map observed)]
      (fun x => (ProbabilityTheory.condDistrib
        (fun z : Obs d => z.2.1) (fun z => z.1) (Pc.map observed) x) {true}) := by
    filter_upwards [hmodel.tail.1] with x hx
    rw [hx]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [← orderedMass_treated_measure_disintegration (Pc.map observed) E hE]
  exact lintegral_congr_ae (ae_restrict_of_ae hAE)

/-- The setwise treatment probability is the real integral of the propensity. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel,E,hE), [the asserted conclusion holds](goal). -/
lemma orderedMass_treated_real_integral {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (E : Set (Fin d → ℝ)) (hE : MeasurableSet E) :
    (∫ x in E, e x ∂covariateLaw (Pc.map observed)) =
      (Pc.map observed).real {z | z.2.1 = true ∧ z.1 ∈ E} := by
  letI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  letI : IsProbabilityMeasure (covariateLaw (Pc.map observed)) := by
    unfold covariateLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hprop : Measurable (propensity (Pc.map observed)) := by
    unfold propensity
    have hk : Measurable (fun x : Fin d → ℝ =>
        (ProbabilityTheory.condDistrib
          (fun z : Obs d => z.2.1) (fun z => z.1) (Pc.map observed) x) {true}) :=
      (ProbabilityTheory.condDistrib
        (fun z : Obs d => z.2.1) (fun z => z.1) (Pc.map observed)).measurable_coe
          (by simp)
    fun_prop
  have hsym : propensity (Pc.map observed) =ᵐ[covariateLaw (Pc.map observed)] e := by
    filter_upwards [hmodel.tail.1] with x hx
    exact hx.symm
  have hmeas : AEMeasurable e (covariateLaw (Pc.map observed)) :=
    hprop.aemeasurable.congr hsym
  have hnn : 0 ≤ᵐ[covariateLaw (Pc.map observed)] e := by
    filter_upwards [hmodel.tail.1] with x hx
    rw [hx]
    exact ENNReal.toReal_nonneg
  rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hnn)
    (hmeas.restrict.aestronglyMeasurable)]
  rw [orderedMass_treated_measure_propensity β B L C c_f γ Pc μ₁ e hmodel E hE]
  rfl

/-- A propensity version is almost everywhere between zero and one. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel), [the asserted conclusion holds](goal). -/
lemma orderedMass_propensity_ae_bounds {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e) :
    ∀ᵐ x ∂covariateLaw (Pc.map observed), e x ∈ Set.Icc 0 1 := by
  letI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  filter_upwards [hmodel.tail.1] with x hx
  rw [hx]
  constructor
  · exact ENNReal.toReal_nonneg
  · letI : IsProbabilityMeasure
        ((ProbabilityTheory.condDistrib
          (fun z : Obs d => z.2.1) (fun z => z.1) (Pc.map observed)) x) :=
      ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure x
    exact measureReal_le_one

/-- The propensity version is integrable on every measurable covariate set. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel,E,_hE), [the asserted conclusion holds](goal). -/
lemma orderedMass_propensity_integrable {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (E : Set (Fin d → ℝ)) (_hE : MeasurableSet E) :
    Integrable e ((covariateLaw (Pc.map observed)).restrict E) := by
  letI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  letI : IsProbabilityMeasure (covariateLaw (Pc.map observed)) := by
    unfold covariateLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hprop : Measurable (propensity (Pc.map observed)) := by
    unfold propensity
    have hk : Measurable (fun x : Fin d → ℝ =>
        (ProbabilityTheory.condDistrib
          (fun z : Obs d => z.2.1) (fun z => z.1) (Pc.map observed) x) {true}) :=
      (ProbabilityTheory.condDistrib
        (fun z : Obs d => z.2.1) (fun z => z.1) (Pc.map observed)).measurable_coe
          (by simp)
    fun_prop
  have hmeas : AEMeasurable e (covariateLaw (Pc.map observed)) :=
    hprop.aemeasurable.congr (by
      filter_upwards [hmodel.tail.1] with x hx
      exact hx.symm)
  have hbounded : ∀ᵐ x ∂(covariateLaw (Pc.map observed)).restrict E,
      e x ∈ Set.Icc (0 : ℝ) 1 :=
    ae_restrict_of_ae (orderedMass_propensity_ae_bounds β B L C c_f γ Pc μ₁ e hmodel)
  exact Integrable.of_mem_Icc 0 1 hmeas.restrict hbounded

/-- Layer cake expresses treated propensity mass through upper-level sets. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel,E,hE), [the asserted conclusion holds](goal). -/
lemma orderedMass_setwise_layercake {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (E : Set (Fin d → ℝ)) (hE : MeasurableSet E) :
    (∫ x in E, e x ∂covariateLaw (Pc.map observed)) =
      ∫ t in Set.Ioi (0 : ℝ),
        ((covariateLaw (Pc.map observed)).restrict E).real {x | t < e x} := by
  have hnonneg : 0 ≤ᵐ[(covariateLaw (Pc.map observed)).restrict E] e := by
    filter_upwards [ae_restrict_of_ae
      (orderedMass_propensity_ae_bounds β B L C c_f γ Pc μ₁ e hmodel)] with x hx
    exact hx.1
  exact (orderedMass_propensity_integrable β B L C c_f γ Pc μ₁ e hmodel E hE)
    |>.integral_eq_integral_meas_lt hnonneg

/-- The global tail bound also controls the part of an arbitrary set lying in
the low-propensity region. This is the setwise estimate used by layer cake. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel,E,t,ht), [the asserted conclusion holds](goal). -/
lemma orderedMass_intersection_tail_le {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (E : Set (Fin d → ℝ)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (covariateLaw (Pc.map observed)).real (E ∩ {x | e x ≤ t}) ≤
      C * t ^ (γ - 1) := by
  letI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  letI : IsProbabilityMeasure (covariateLaw (Pc.map observed)) := by
    unfold covariateLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  calc
    (covariateLaw (Pc.map observed)).real (E ∩ {x | e x ≤ t}) ≤
        (covariateLaw (Pc.map observed)).real {x | e x ≤ t} := by
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_right)
    _ ≤ C * t ^ (γ - 1) := hmodel.tail.2 t ht

/-- Each set retains at least its mass minus the global lower tail above a
propensity threshold. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel,E,t,ht), [the asserted conclusion holds](goal). -/
lemma orderedMass_high_part_lower {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (E : Set (Fin d → ℝ)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (covariateLaw (Pc.map observed)).real E - C * t ^ (γ - 1) ≤
      (covariateLaw (Pc.map observed)).real (E ∩ {x | t < e x}) := by
  letI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  letI : IsProbabilityMeasure (covariateLaw (Pc.map observed)) := by
    unfold covariateLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  let ν := covariateLaw (Pc.map observed)
  have hcover : E ⊆ (E ∩ {x | t < e x}) ∪ (E ∩ {x | e x ≤ t}) := by
    intro x hx
    by_cases h : t < e x
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, le_of_not_gt h⟩
  have hmass : ν.real E ≤
      ν.real (E ∩ {x | t < e x}) + ν.real (E ∩ {x | e x ≤ t}) := by
    have hle : ν E ≤ ν (E ∩ {x | t < e x}) + ν (E ∩ {x | e x ≤ t}) :=
      (measure_mono hcover).trans
        (measure_union_le (E ∩ {x | t < e x}) (E ∩ {x | e x ≤ t}))
    have hfinite : ν (E ∩ {x | t < e x}) + ν (E ∩ {x | e x ≤ t}) ≠ ⊤ := by
      exact ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
    have := ENNReal.toReal_mono hfinite hle
    simpa only [Measure.real, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      using this
  have htail := orderedMass_intersection_tail_le β B L C c_f γ Pc μ₁ e hmodel E t ht
  dsimp [ν] at hmass
  linarith

/-- On a bounded threshold interval, the layer-cake integrand dominates the
set mass minus the global lower-tail envelope. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel,E,hE,s,hs,hγ), [the asserted conclusion holds](goal). -/
lemma orderedMass_layercake_piece_lower {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (E : Set (Fin d → ℝ)) (hE : MeasurableSet E)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hγ : 1 < γ) :
    (∫ t in (0 : ℝ)..s,
        (covariateLaw (Pc.map observed)).real E - C * t ^ (γ - 1)) ≤
      ∫ t in (0 : ℝ)..s,
        ((covariateLaw (Pc.map observed)).restrict E).real {x | t < e x} := by
  let ν := covariateLaw (Pc.map observed)
  letI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  letI : IsProbabilityMeasure ν := by
    dsimp [ν, covariateLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  let F : ℝ → ℝ := fun t => (ν.restrict E).real {x | t < e x}
  have hanti : Antitone F := by
    intro t t' htt'
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (by intro x hx; exact lt_of_le_of_lt htt' hx))
  have hFint : IntervalIntegrable F volume 0 s := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1]
    exact (hanti.locallyIntegrable.integrableOn_isCompact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hpoly : IntervalIntegrable
      (fun t : ℝ => ν.real E - C * t ^ (γ - 1)) volume 0 s := by
    apply IntervalIntegrable.sub
    · exact intervalIntegrable_const
    · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < γ - 1)).const_mul C
  apply intervalIntegral.integral_mono_on hs.1 hpoly hFint
  intro t ht
  have hbound := orderedMass_high_part_lower β B L C c_f γ Pc μ₁ e hmodel E t
    ⟨ht.1, ht.2.trans hs.2⟩
  simpa only [F, ν, Measure.real, Measure.restrict_apply' hE, Set.inter_comm]
    using hbound

/-- The exact integral in the setwise treated-mass argument. [For the stated inputs and conditions](hyp:u,C,γ,s,hγ), [the asserted conclusion holds](goal). -/
lemma orderedMass_integral_tail (u C γ s : ℝ) (hγ : 1 < γ) :
    (∫ t in (0 : ℝ)..s, (u - C * t ^ (γ - 1))) =
      u * s - C * s ^ γ / γ := by
  have hr : -1 < γ - 1 := by linarith
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((intervalIntegral.intervalIntegrable_rpow' hr).const_mul C),
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr)]
  have hγne : γ ≠ 0 := ne_of_gt (by linarith)
  have he : γ - 1 + 1 = γ := by ring
  rw [he]
  rw [Real.zero_rpow hγne]
  simp only [sub_zero]
  field_simp
  ring

/-- Substituting the tail threshold into the layer-cake integral. [For the stated inputs and conditions](hyp:u,C,γ,s,hγ,hs,hthreshold), [the asserted conclusion holds](goal). -/
lemma orderedMass_integral_optimal (u C γ s : ℝ) (hγ : 1 < γ)
    (hs : 0 < s) (hthreshold : C * s ^ (γ - 1) = u) :
    (∫ t in (0 : ℝ)..s, (u - C * t ^ (γ - 1))) =
      ((γ - 1) / γ) * u * s := by
  rw [orderedMass_integral_tail u C γ s hγ]
  have hpow : s ^ γ = s ^ (γ - 1) * s := by
    conv_lhs => rw [show γ = γ - 1 + 1 by ring]
    rw [Real.rpow_add hs]
    simp
  rw [hpow]
  have hγne : γ ≠ 0 := ne_of_gt (by linarith)
  field_simp
  nlinarith [hthreshold]

/-- The proposed threshold balances the set mass against the tail envelope. [For the stated inputs and conditions](hyp:u,C,γ,hu,hC,hγ), [the asserted conclusion holds](goal). -/
lemma orderedMass_threshold_identity (u C γ : ℝ) (hu : 0 < u)
    (hC : 0 < C) (hγ : 1 < γ) :
    C * ((u / C) ^ (1 / (γ - 1))) ^ (γ - 1) = u := by
  have huc : 0 ≤ u / C := le_of_lt (div_pos hu hC)
  have hden : γ - 1 ≠ 0 := ne_of_gt (by linarith)
  rw [← Real.rpow_mul huc]
  have hexp : 1 / (γ - 1) * (γ - 1) = 1 := by
    field_simp
  rw [hexp, Real.rpow_one]
  exact mul_div_cancel₀ u (ne_of_gt hC)

/-- The layer-cake cutoff lies in the unit interval for a probability mass. [For the stated inputs and conditions](hyp:u,C,γ,hu,huone,hC,hγ), [the asserted conclusion holds](goal). -/
lemma orderedMass_threshold_mem_unit (u C γ : ℝ) (hu : 0 < u)
    (huone : u ≤ 1) (hC : 1 ≤ C) (hγ : 1 < γ) :
    (u / C) ^ (1 / (γ - 1)) ∈ Set.Icc (0 : ℝ) 1 := by
  have hCpos : 0 < C := by linarith
  have hquotpos : 0 < u / C := div_pos hu hCpos
  have hquotle : u / C ≤ 1 := (div_le_one hCpos).mpr (huone.trans hC)
  have hexppos : 0 ≤ 1 / (γ - 1) := by positivity
  constructor
  · exact (Real.rpow_pos_of_pos hquotpos _).le
  · exact Real.rpow_le_one hquotpos.le hquotle hexppos

/-- The analytic value of the layer-cake lower bound at its balancing threshold. [For the stated inputs and conditions](hyp:u,C,γ,hu,hC,hγ), [the asserted conclusion holds](goal). -/
lemma orderedMass_integral_at_threshold (u C γ : ℝ) (hu : 0 < u)
    (hC : 0 < C) (hγ : 1 < γ) :
    (∫ t in (0 : ℝ)..((u / C) ^ (1 / (γ - 1))),
        (u - C * t ^ (γ - 1))) =
      ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        u ^ (γ / (γ - 1)) := by
  have hs : 0 < (u / C) ^ (1 / (γ - 1)) :=
    Real.rpow_pos_of_pos (div_pos hu hC) _
  rw [orderedMass_integral_optimal u C γ _ hγ hs
    (orderedMass_threshold_identity u C γ hu hC hγ)]
  rw [Real.div_rpow hu.le hC.le]
  have hden : γ - 1 ≠ 0 := ne_of_gt (by linarith)
  have he : γ / (γ - 1) = 1 + 1 / (γ - 1) := by
    field_simp
    ring
  rw [he, Real.rpow_add hu, Real.rpow_one]
  have hneg : -(1 : ℝ) / (γ - 1) = -(1 / (γ - 1)) := by ring
  rw [hneg, Real.rpow_neg hC.le]
  ring

/-- The global propensity tail yields the sharp setwise treated-mass bound. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel,hC,hγ,E,hE), [the asserted conclusion holds](goal). -/
lemma orderedMass_setwise_lower {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (hC : 1 ≤ C) (hγ : 1 < γ)
    (E : Set (Fin d → ℝ)) (hE : MeasurableSet E) :
    ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        (covariateLaw (Pc.map observed)).real E ^ (γ / (γ - 1)) ≤
      (Pc.map observed).real {z | z.2.1 = true ∧ z.1 ∈ E} := by
  let ν := covariateLaw (Pc.map observed)
  letI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  letI : IsProbabilityMeasure ν := by
    dsimp [ν, covariateLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  let u := ν.real E
  have hu0 : 0 ≤ u := ENNReal.toReal_nonneg
  have hu1 : u ≤ 1 := by
    dsimp [u]
    calc
      ν.real E ≤ ν.real Set.univ :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ E))
      _ = 1 := by simp
  by_cases hu : u = 0
  · rw [show ν.real E = 0 from hu]
    simp only [Real.zero_rpow (by positivity : γ / (γ - 1) ≠ 0), mul_zero]
    exact ENNReal.toReal_nonneg
  have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
  let s := (u / C) ^ (1 / (γ - 1))
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := orderedMass_threshold_mem_unit u C γ hupos hu1 hC hγ
  let F : ℝ → ℝ := fun t => (ν.restrict E).real {x | t ≤ e x}
  have hanti : Antitone F := by
    intro t t' htt'
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (by intro x hx; exact htt'.trans hx))
  have hFint : IntervalIntegrable F volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hanti.locallyIntegrable.integrableOn_isCompact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hFnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] F :=
    Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  have hmass : (Pc.map observed).real {z | z.2.1 = true ∧ z.1 ∈ E} =
      ∫ t in (0 : ℝ)..1, F t := by
    rw [← orderedMass_treated_real_integral β B L C c_f γ Pc μ₁ e hmodel E hE]
    have hbound := orderedMass_propensity_ae_bounds β B L C c_f γ Pc μ₁ e hmodel
    have hboundE : e ≤ᵐ[ν.restrict E] fun _ => (1 : ℝ) :=
      ae_restrict_of_ae (by filter_upwards [hbound] with x hx; exact hx.2)
    have hnonneg : 0 ≤ᵐ[ν.restrict E] e :=
      ae_restrict_of_ae (by filter_upwards [hbound] with x hx; exact hx.1)
    have hi := orderedMass_propensity_integrable β B L C c_f γ Pc μ₁ e hmodel E hE
    rw [hi.integral_eq_integral_Ioc_meas_le hnonneg hboundE]
    exact (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm
  have hpiece : (∫ t in (0 : ℝ)..s, u - C * t ^ (γ - 1)) ≤
      ∫ t in (0 : ℝ)..s, F t := by
    have hfirst := orderedMass_layercake_piece_lower β B L C c_f γ Pc μ₁ e hmodel E hE s hs hγ
    apply hfirst.trans
    apply intervalIntegral.integral_mono_on hs.1
    · let F' : ℝ → ℝ := fun t => (ν.restrict E).real {x | t < e x}
      have hanti' : Antitone F' := by
        intro t t' htt'
        exact ENNReal.toReal_mono (measure_ne_top _ _)
          (measure_mono (by intro x hx; exact lt_of_le_of_lt htt' hx))
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1]
      exact (hanti'.locallyIntegrable.integrableOn_isCompact isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1]
      exact (hanti.locallyIntegrable.integrableOn_isCompact isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self
    · intro t ht
      exact ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (by intro x hx; change t < e x at hx; exact hx.le))
  calc
    ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) * ν.real E ^ (γ / (γ - 1)) =
        ∫ t in (0 : ℝ)..s, u - C * t ^ (γ - 1) := by
          exact (orderedMass_integral_at_threshold u C γ hupos (by linarith) hγ).symm
    _ ≤ ∫ t in (0 : ℝ)..s, F t := hpiece
    _ ≤ ∫ t in (0 : ℝ)..1, F t :=
      intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2 hFnn hFint
    _ = (Pc.map observed).real {z | z.2.1 = true ∧ z.1 ∈ E} := hmass.symm

/-- The ordered-cell coefficient has a positive lower bound over a compact
range of overlap exponents. [For the stated inputs and conditions](hyp:C,a,γ_min,γ_max,hC,ha,hγmin,hγrange), [the asserted conclusion holds](goal). -/
lemma orderedMass_uniform_coefficient (C a γ_min γ_max : ℝ)
    (hC : 0 < C) (ha : 0 < a)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ γ ∈ Set.Icc γ_min γ_max,
      κ ≤ ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        a ^ (γ / (γ - 1)) := by
  let f : ℝ → ℝ := fun γ => ((γ - 1) / γ) *
    C ^ (-(1 : ℝ) / (γ - 1)) * a ^ (γ / (γ - 1))
  have hcont : ContinuousOn f (Set.Icc γ_min γ_max) := by
    have hden : ∀ γ ∈ Set.Icc γ_min γ_max, γ - 1 ≠ 0 := by
      intro γ hγ
      exact ne_of_gt (by linarith [hγ.1])
    have hγne : ∀ γ ∈ Set.Icc γ_min γ_max, γ ≠ 0 := by
      intro γ hγ
      exact ne_of_gt (by linarith [hγ.1])
    have hbase : ContinuousOn (fun γ : ℝ => (γ - 1) / γ)
        (Set.Icc γ_min γ_max) := by
      fun_prop (disch := assumption)
    have hCexp : ContinuousOn (fun γ : ℝ => -(1 : ℝ) / (γ - 1))
        (Set.Icc γ_min γ_max) := by
      fun_prop (disch := assumption)
    have haexp : ContinuousOn (fun γ : ℝ => γ / (γ - 1))
        (Set.Icc γ_min γ_max) := by
      fun_prop (disch := assumption)
    have hCpow : ContinuousOn (fun γ : ℝ => C ^ (-(1 : ℝ) / (γ - 1)))
        (Set.Icc γ_min γ_max) :=
      continuousOn_const.rpow hCexp (by intro γ hγ; exact Or.inl (ne_of_gt hC))
    have hapow : ContinuousOn (fun γ : ℝ => a ^ (γ / (γ - 1)))
        (Set.Icc γ_min γ_max) :=
      continuousOn_const.rpow haexp (by intro γ hγ; exact Or.inl (ne_of_gt ha))
    exact (hbase.mul hCpow).mul hapow
  obtain ⟨γ₀, hγ₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn ⟨γ_min, ⟨le_refl _, le_of_lt hγrange⟩⟩ hcont
  have hpos : 0 < f γ₀ := by
    dsimp [f]
    have hγ : 1 < γ₀ := lt_of_lt_of_le hγmin hγ₀.1
    positivity
  refine ⟨f γ₀, hpos, ?_⟩
  intro γ hγ
  exact hmin hγ

end CausalSmith.Stat.WeakOverlap
