module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairFiberIndependence

/-! # Conditional exchangeability of the binary witnesses

The independence in each recorded covariate fibre from equations (14)--(16)
of the membership roadmap lifts to conditional independence under the mixture.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory ProbabilityTheory

/-- Mixing fibres that record the base leaves the base marginal unchanged. -/
-- @node: map_bind_recording
lemma map_bind_recording {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) (κ : X → Measure Y) (base : Y → X)
    (hκ : Measurable κ) (hb : Measurable base)
    (hr : ∀ᵐ x ∂μ, (κ x).map base = Measure.dirac x) :
    (μ.bind κ).map base = μ := by
  rw [map_bind_channel _ _ _ hκ hb]
  calc
    μ.bind (fun x => (κ x).map base) = μ.bind Measure.dirac :=
      Measure.bind_congr_right hr
    _ = μ := Measure.bind_dirac

/-- Conditional event probabilities are the event masses of the recorded fibres. -/
-- @node: condExp_indicator_bind_recording
lemma condExp_indicator_bind_recording {X Y : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [MeasurableSpace Y]
    (μ : Measure X) (κ : X → Measure Y) (base : Y → X)
    [IsFiniteMeasure (μ.bind κ)]
    (hκ : Measurable κ) (hb : Measurable base)
    (hr : ∀ᵐ x ∂μ, (κ x).map base = Measure.dirac x)
    (hp : ∀ᵐ x ∂μ, IsProbabilityMeasure (κ x))
    (s : Set Y) (hs : MeasurableSet s) :
    (μ.bind κ)[s.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap base inferInstance] =ᵐ[μ.bind κ]
      fun y => (κ (base y)).real s := by
  have hg : Measurable (fun x => (κ x).real s) :=
    (Measure.measurable_measure.mp hκ s hs).ennreal_toReal
  have hp' : ∀ᵐ y ∂μ.bind κ, IsProbabilityMeasure (κ (base y)) := by
    apply ae_of_ae_map (μ := μ.bind κ) (p := fun x => IsProbabilityMeasure (κ x)) hb.aemeasurable
    rw [map_bind_recording μ κ base hκ hb hr]
    exact hp
  have hgi : Integrable (fun y => (κ (base y)).real s) (μ.bind κ) := by
    apply Integrable.of_bound (hg.comp hb).aestronglyMeasurable 1
    filter_upwards [hp'] with y hy
    have := hy
    change ‖(κ (base y)).real s‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  apply condExp_bind_recording μ κ base hκ hb hr _
    ((integrable_const (1 : ℝ)).indicator hs) _ hg hgi
  exact Filter.Eventually.of_forall (fun x => by simp [integral_indicator, hs])

/-- Independent functions in almost every recorded fibre are conditionally
independent given the base in the mixture. -/
-- @node: condIndepFun_bind_recording
lemma condIndepFun_bind_recording {X Y A B : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure X) (κ : X → Measure Y) (base : Y → X)
    [IsFiniteMeasure (μ.bind κ)]
    (hκ : Measurable κ) (hb : Measurable base)
    (hr : ∀ᵐ x ∂μ, (κ x).map base = Measure.dirac x)
    (hp : ∀ᵐ x ∂μ, IsProbabilityMeasure (κ x))
    (f : Y → A) (g : Y → B) (hf : Measurable f) (hg : Measurable g)
    (hi : ∀ᵐ x ∂μ, IndepFun f g (κ x)) :
    CondIndepFun (MeasurableSpace.comap base inferInstance) hb.comap_le
      f g (μ.bind κ) := by
  apply (condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg).mpr
  intro s t hs ht
  have hst := condExp_indicator_bind_recording μ κ base hκ hb hr hp
    (f ⁻¹' s ∩ g ⁻¹' t) ((hs.preimage hf).inter (ht.preimage hg))
  have hs' := condExp_indicator_bind_recording μ κ base hκ hb hr hp
    (f ⁻¹' s) (hs.preimage hf)
  have ht' := condExp_indicator_bind_recording μ κ base hκ hb hr hp
    (g ⁻¹' t) (ht.preimage hg)
  have hi' : ∀ᵐ y ∂μ.bind κ, IndepFun f g (κ (base y)) := by
    apply ae_of_ae_map (μ := μ.bind κ) (p := fun x => IndepFun f g (κ x)) hb.aemeasurable
    rw [map_bind_recording μ κ base hκ hb hr]
    exact hi
  filter_upwards [hst, hs', ht', hi'] with y hst hs' ht' hi'
  rw [hst, hs', ht']
  exact congrArg ENNReal.toReal (hi'.measure_inter_preimage_eq_mul s t hs ht) |>.trans
    (ENNReal.toReal_mul)

/-- The bounded binary construction has joint conditional exchangeability,
as stipulated by its independent treatment draw in (16). -/
-- @node: lowerPair_exchangeability
lemma lowerPair_exchangeability (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) : Exchangeability (lowerPair d β q h δ M sign) := by
  intro hfinite
  let κ (x : Fin d → ℝ) : Measure (Full d) :=
    (treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))
  have hκ : Measurable κ := lowerPair_fullKernel_measurable d β q h δ M hq sign
  have hr : ∀ᵐ x ∂volume.restrict (cube d), (κ x).map Prod.fst = Measure.dirac x := by
    filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
    exact lowerPair_fiber_xLaw d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign x hx
  have hp : ∀ᵐ x ∂volume.restrict (cube d), IsProbabilityMeasure (κ x) := by
    filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
    exact lowerPair_fiber_isProbabilityMeasure d β q h δ M
      hd hq hβ hδ hh hh1 hM hsmall sign x hx
  have hi : ∀ᵐ x ∂volume.restrict (cube d),
      IndepFun (fun u : Full d => (u.2.2.1, u.2.2.2))
        (fun u : Full d => u.2.1) (κ x) := by
    filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
    exact lowerPair_fiber_indepFun d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign x hx
  have : IsFiniteMeasure ((volume.restrict (cube d)).bind κ) := hfinite
  change CondIndepFun _ _ _ _ ((volume.restrict (cube d)).bind κ)
  exact condIndepFun_bind_recording (volume.restrict (cube d)) κ Prod.fst
    hκ measurable_fst hr hp (fun u : Full d => (u.2.2.1, u.2.2.2))
    (fun u : Full d => u.2.1) (by fun_prop) (by fun_prop) hi

end CausalSmith.Stat.GlobalTailDesignRobustCate
