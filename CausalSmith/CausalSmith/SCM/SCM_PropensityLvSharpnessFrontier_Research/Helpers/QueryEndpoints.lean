import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Legality
import Mathlib.Probability.ConditionalProbability

/-! # Expectation endpoints over dominated residual mixtures -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set

private lemma integrable_of_ae_bounded {Y : Type*} [MeasurableSpace Y]
    (P : Measure Y) [IsProbabilityMeasure P] (h : Y → ℝ)
    (hmeas : Measurable h) (hbounded : ∃ C : ℝ, ∀ᵐ x ∂P, |h x| ≤ C) :
    Integrable h P := by
  rcases hbounded with ⟨C, hC⟩
  exact Integrable.of_bound hmeas.aestronglyMeasurable C hC

private lemma lowerBounds_nonempty_bddAbove {Y : Type*} [MeasurableSpace Y]
    (P : Measure Y) [IsProbabilityMeasure P] (h : Y → ℝ)
    (hbounded : ∃ C : ℝ, ∀ᵐ x ∂P, |h x| ≤ C) :
    {r : ℝ | ∀ᵐ x ∂P, r ≤ h x}.Nonempty ∧
      BddAbove {r : ℝ | ∀ᵐ x ∂P, r ≤ h x} := by
  rcases hbounded with ⟨C, hC⟩
  constructor
  · refine ⟨-C, ?_⟩
    filter_upwards [hC] with x hx
    exact (neg_le_of_abs_le hx)
  · refine ⟨C, ?_⟩
    intro r hr
    have hboth : ∀ᵐ x ∂P, r ≤ h x ∧ h x ≤ C := by
      filter_upwards [hr, hC] with x hlow habs
      exact ⟨hlow, le_of_abs_le habs⟩
    obtain ⟨x, hx⟩ := hboth.exists
    exact hx.1.trans hx.2

private lemma upperBounds_nonempty_bddBelow {Y : Type*} [MeasurableSpace Y]
    (P : Measure Y) [IsProbabilityMeasure P] (h : Y → ℝ)
    (hbounded : ∃ C : ℝ, ∀ᵐ x ∂P, |h x| ≤ C) :
    {r : ℝ | ∀ᵐ x ∂P, h x ≤ r}.Nonempty ∧
      BddBelow {r : ℝ | ∀ᵐ x ∂P, h x ≤ r} := by
  rcases hbounded with ⟨C, hC⟩
  constructor
  · refine ⟨C, ?_⟩
    filter_upwards [hC] with x hx
    exact le_of_abs_le hx
  · refine ⟨-C, ?_⟩
    intro r hr
    have hboth : ∀ᵐ x ∂P, -C ≤ h x ∧ h x ≤ r := by
      filter_upwards [hC, hr] with x habs hupp
      exact ⟨neg_le_of_abs_le habs, hupp⟩
    obtain ⟨x, hx⟩ := hboth.exists
    exact hx.1.trans hx.2

/-- The infimum of expectations over probability laws dominated by `P` is
the essential infimum of the query under `P`.  For the specified model objects, [the stated conditions](hyp:h,hmeas,hbounded), [the stated mathematical relationship holds](goal).
-/
-- @node: dominatedProbability_integral_sInf
lemma dominatedProbability_integral_sInf {Y : Type*} [MeasurableSpace Y]
    (P : Measure Y) [IsProbabilityMeasure P] (h : Y → ℝ)
    (hmeas : Measurable h) (hbounded : ∃ C : ℝ, ∀ᵐ x ∂P, |h x| ≤ C) :
    sInf {θ : ℝ | ∃ R : Measure Y, IsProbabilityMeasure R ∧
      R.AbsolutelyContinuous P ∧ θ = ∫ x, h x ∂R} =
      sSup {r : ℝ | ∀ᵐ x ∂P, r ≤ h x} := by
  let S : Set ℝ := {r : ℝ | ∀ᵐ x ∂P, r ≤ h x}
  let T : Set ℝ := {θ : ℝ | ∃ R : Measure Y, IsProbabilityMeasure R ∧
    R.AbsolutelyContinuous P ∧ θ = ∫ x, h x ∂R}
  obtain ⟨hSne, hSbdd⟩ := lowerBounds_nonempty_bddAbove P h hbounded
  have hPint := integrable_of_ae_bounded P h hmeas hbounded
  have hTne : T.Nonempty := ⟨∫ x, h x ∂P, P, inferInstance,
    Measure.AbsolutelyContinuous.rfl, rfl⟩
  have hLlower : ∀ θ ∈ T, sSup S ≤ θ := by
    rintro θ ⟨R, hRprob, hRac, rfl⟩
    let _ : IsProbabilityMeasure R := hRprob
    rcases hbounded with ⟨C, hC⟩
    have hRbound : ∀ᵐ x ∂R, |h x| ≤ C := hRac hC
    have hRint : Integrable h R := Integrable.of_bound
      hmeas.aestronglyMeasurable C hRbound
    apply csSup_le hSne
    intro r hr
    have hrR : ∀ᵐ x ∂R, r ≤ h x := hRac hr
    calc
      r = ∫ _x, r ∂R := by simp
      _ ≤ ∫ x, h x ∂R := integral_mono_ae (integrable_const r) hRint hrR
  have hTbdd : BddBelow T := ⟨sSup S, hLlower⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro eps heps
    let A : Set Y := {x | h x < sSup S + eps}
    have hAmeas : MeasurableSet A := measurableSet_lt hmeas measurable_const
    have hApos : P A ≠ 0 := by
      intro hAzero
      have hnew : sSup S + eps ∈ S := by
        change ∀ᵐ x ∂P, sSup S + eps ≤ h x
        rw [ae_iff]
        simpa only [not_le] using hAzero
      have := le_csSup hSbdd hnew
      linarith
    let R : Measure Y := P[|A]
    let _ : IsProbabilityMeasure R := cond_isProbabilityMeasure hApos
    have hRac : R.AbsolutelyContinuous P := by
      exact Measure.AbsolutelyContinuous.trans Measure.smul_absolutelyContinuous
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    have hRbound : ∀ᵐ x ∂R, |h x| ≤ (Classical.choose hbounded) :=
      hRac (Classical.choose_spec hbounded)
    have hRint : Integrable h R := Integrable.of_bound
      hmeas.aestronglyMeasurable _ hRbound
    have hRle : ∀ᵐ x ∂R, h x ≤ sSup S + eps := by
      have hRrestrict : R.AbsolutelyContinuous (P.restrict A) := by
        exact Measure.smul_absolutelyContinuous
      exact hRrestrict ((ae_restrict_mem hAmeas).mono fun x hx =>
        (show h x < sSup S + eps from hx).le)
    have hRle' : ∫ x, h x ∂R ≤ sSup S + eps := by
      exact (integral_mono_ae hRint (integrable_const _) hRle).trans_eq (by simp)
    exact (csInf_le hTbdd ⟨R, inferInstance, hRac, rfl⟩).trans hRle'
  · exact le_csInf hTne hLlower

/-- The supremum of expectations over probability laws dominated by `P` is
the essential supremum of the query under `P`.  For the specified model objects, [the stated conditions](hyp:h,hmeas,hbounded), [the stated mathematical relationship holds](goal).
-/
-- @node: dominatedProbability_integral_sSup
lemma dominatedProbability_integral_sSup {Y : Type*} [MeasurableSpace Y]
    (P : Measure Y) [IsProbabilityMeasure P] (h : Y → ℝ)
    (hmeas : Measurable h) (hbounded : ∃ C : ℝ, ∀ᵐ x ∂P, |h x| ≤ C) :
    sSup {θ : ℝ | ∃ R : Measure Y, IsProbabilityMeasure R ∧
      R.AbsolutelyContinuous P ∧ θ = ∫ x, h x ∂R} =
      sInf {r : ℝ | ∀ᵐ x ∂P, h x ≤ r} := by
  let T : Set ℝ := {θ : ℝ | ∃ R : Measure Y, IsProbabilityMeasure R ∧
    R.AbsolutelyContinuous P ∧ θ = ∫ x, h x ∂R}
  let U : Set ℝ := {r : ℝ | ∀ᵐ x ∂P, h x ≤ r}
  let Tneg : Set ℝ := {θ : ℝ | ∃ R : Measure Y, IsProbabilityMeasure R ∧
    R.AbsolutelyContinuous P ∧ θ = ∫ x, -h x ∂R}
  let Sneg : Set ℝ := {r : ℝ | ∀ᵐ x ∂P, r ≤ -h x}
  have hnegBound : ∃ C : ℝ, ∀ᵐ x ∂P, |-h x| ≤ C := by
    rcases hbounded with ⟨C, hC⟩
    exact ⟨C, hC.mono fun x hx => by simpa using hx⟩
  have hmain := dominatedProbability_integral_sInf P (-h) hmeas.neg hnegBound
  have hTneg : Tneg = -T := by
    ext θ
    rw [Set.mem_neg]
    change (∃ R : Measure Y, IsProbabilityMeasure R ∧ R ≪ P ∧
      θ = ∫ x, -h x ∂R) ↔
      ∃ R : Measure Y, IsProbabilityMeasure R ∧ R ≪ P ∧
        -θ = ∫ x, h x ∂R
    constructor
    · rintro ⟨R, hR, hRac, hθ⟩
      refine ⟨R, hR, hRac, ?_⟩
      rw [integral_neg] at hθ
      linarith
    · rintro ⟨R, hR, hRac, hθ⟩
      refine ⟨R, hR, hRac, ?_⟩
      rw [integral_neg]
      linarith
  have hSneg : Sneg = -U := by
    ext r
    rw [Set.mem_neg]
    change (∀ᵐ x ∂P, r ≤ -h x) ↔ (∀ᵐ x ∂P, h x ≤ -r)
    constructor
    · intro hr
      filter_upwards [hr] with x hx
      linarith
    · intro hu
      filter_upwards [hu] with x hx
      linarith
  change sSup T = sInf U
  change sInf Tneg = sSup Sneg at hmain
  rw [hTneg, hSneg, Real.sInf_neg, Real.sSup_neg] at hmain
  linarith

/-- Positive affine maps commute with the infimum of a nonempty real set
bounded below.  For the specified model objects, [the stated conditions](hyp:hTne,hTbdd,hb), [the stated mathematical relationship holds](goal).
-/
-- @node: sInf_affine_image
lemma sInf_affine_image (T : Set ℝ) (a b : ℝ) (hTne : T.Nonempty)
    (hTbdd : BddBelow T) (hb : 0 < b) :
    sInf ((fun t => a + b * t) '' T) = a + b * sInf T := by
  have hImageNe : ((fun t => a + b * t) '' T).Nonempty := hTne.image _
  have hTbdd' := hTbdd
  obtain ⟨L, hL⟩ := hTbdd
  have hImageBdd : BddBelow ((fun t => a + b * t) '' T) := by
    refine ⟨a + b * L, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    simpa [add_comm] using add_le_add_right
      (mul_le_mul_of_nonneg_left (hL ht) hb.le) a
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro eps heps
    have hex : ∃ t ∈ T, t < sInf T + eps / b := by
      by_contra hnot
      push Not at hnot
      have hle := le_csInf hTne hnot
      have : 0 < eps / b := div_pos heps hb
      linarith
    rcases hex with ⟨t, ht, htlt⟩
    have himage : a + b * t ∈ (fun t => a + b * t) '' T := ⟨t, ht, rfl⟩
    have hle := csInf_le hImageBdd himage
    calc
      sInf ((fun t => a + b * t) '' T) ≤ a + b * t := hle
      _ ≤ a + b * sInf T + eps := by
        have := mul_lt_mul_of_pos_left htlt hb
        field_simp [ne_of_gt hb] at this ⊢
        linarith
  · apply le_csInf hImageNe
    rintro _ ⟨t, ht, rfl⟩
    simpa [add_comm] using add_le_add_right
      (mul_le_mul_of_nonneg_left (csInf_le hTbdd' ht) hb.le) a

/-- Positive affine maps commute with the supremum of a nonempty real set
bounded above.  For the specified model objects, [the stated conditions](hyp:hTne,hTbdd,hb), [the stated mathematical relationship holds](goal).
-/
-- @node: sSup_affine_image
lemma sSup_affine_image (T : Set ℝ) (a b : ℝ) (hTne : T.Nonempty)
    (hTbdd : BddAbove T) (hb : 0 < b) :
    sSup ((fun t => a + b * t) '' T) = a + b * sSup T := by
  let N : Set ℝ := -T
  have hNne : N.Nonempty := hTne.neg
  have hNbdd : BddBelow N := hTbdd.neg
  have h := sInf_affine_image N (-a) b hNne hNbdd hb
  have hset : (fun t => -a + b * t) '' N = -((fun t => a + b * t) '' T) := by
    ext z
    rw [Set.mem_neg]
    constructor
    · rintro ⟨nt, hnt, rfl⟩
      rw [Set.mem_neg] at hnt
      exact ⟨-nt, hnt, by ring⟩
    · rintro ⟨t, ht, hzt⟩
      refine ⟨-t, ?_, ?_⟩
      · rw [Set.mem_neg]
        simpa using ht
      · linarith
  rw [hset, Real.sInf_neg, Real.sInf_neg] at h
  linarith

private lemma integral_propensity_mixture {Y : Type*} [MeasurableSpace Y]
    (P R : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (e : ℝ) (h : Y → ℝ) (hPos : StrictPositivity e)
    (hmeas : Measurable h) (hbounded : ∃ C : ℝ, ∀ᵐ x ∂P, |h x| ≤ C)
    (hRac : R.AbsolutelyContinuous P) :
    ∫ x, h x ∂(ENNReal.ofReal e • P + ENNReal.ofReal (1 - e) • R) =
      e * ∫ x, h x ∂P + (1 - e) * ∫ x, h x ∂R := by
  have hPint := integrable_of_ae_bounded P h hmeas hbounded
  rcases hbounded with ⟨C, hC⟩
  have hRint : Integrable h R := Integrable.of_bound hmeas.aestronglyMeasurable C (hRac hC)
  rw [integral_add_measure (hPint.smul_measure (by simp)) (hRint.smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal hPos.1.le, ENNReal.toReal_ofReal (sub_nonneg.mpr hPos.2.le)]
  ring

private lemma dominatedIntegral_set_bounds {Y : Type*} [MeasurableSpace Y]
    (P : Measure Y) [IsProbabilityMeasure P] (h : Y → ℝ)
    (hmeas : Measurable h) (hbounded : ∃ C : ℝ, ∀ᵐ x ∂P, |h x| ≤ C) :
    let T : Set ℝ := {θ : ℝ | ∃ R : Measure Y, IsProbabilityMeasure R ∧
      R.AbsolutelyContinuous P ∧ θ = ∫ x, h x ∂R}
    T.Nonempty ∧ BddBelow T ∧ BddAbove T := by
  dsimp only
  rcases hbounded with ⟨C, hC⟩
  refine ⟨⟨∫ x, h x ∂P, P, inferInstance, Measure.AbsolutelyContinuous.rfl, rfl⟩,
    ⟨-C, ?_⟩, ⟨C, ?_⟩⟩
  · rintro _ ⟨R, hR, hRac, rfl⟩
    let _ : IsProbabilityMeasure R := hR
    have hRint : Integrable h R := Integrable.of_bound hmeas.aestronglyMeasurable C (hRac hC)
    calc
      -C = ∫ _x, -C ∂R := by simp
      _ ≤ ∫ x, h x ∂R := integral_mono_ae (integrable_const _) hRint
        (hRac (hC.mono fun x hx => neg_le_of_abs_le hx))
  · rintro _ ⟨R, hR, hRac, rfl⟩
    let _ : IsProbabilityMeasure R := hR
    have hRint : Integrable h R := Integrable.of_bound hmeas.aestronglyMeasurable C (hRac hC)
    calc
      ∫ x, h x ∂R ≤ ∫ _x, C ∂R := integral_mono_ae hRint (integrable_const _)
        (hRac (hC.mono fun x hx => le_of_abs_le hx))
      _ = C := by simp

private lemma mixtureIntegral_values_eq_affine {Y : Type*} [MeasurableSpace Y]
    (P : Measure Y) [IsProbabilityMeasure P] (e : ℝ) (h : Y → ℝ)
    (hPos : StrictPositivity e) (hmeas : Measurable h)
    (hbounded : ∃ C : ℝ, ∀ᵐ x ∂P, |h x| ≤ C) :
    {θ : ℝ | ∃ Q ∈ mixtureClassSet e P, θ = ∫ x, h x ∂Q} =
      (fun t => e * ∫ x, h x ∂P + (1 - e) * t) ''
        {θ : ℝ | ∃ R : Measure Y, IsProbabilityMeasure R ∧
          R.AbsolutelyContinuous P ∧ θ = ∫ x, h x ∂R} := by
  ext θ
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    rcases hQ.representation (ne_of_lt hPos.2) with ⟨R, hR, hRac, hrepr⟩
    let _ : IsProbabilityMeasure R := hR
    refine ⟨∫ x, h x ∂R, ⟨R, hR, hRac, rfl⟩, ?_⟩
    rw [hrepr, integral_propensity_mixture P R e h hPos hmeas hbounded hRac]
  · rintro ⟨t, ⟨R, hR, hRac, rfl⟩, rfl⟩
    let _ : IsProbabilityMeasure R := hR
    let Q := ENNReal.ofReal e • P + ENNReal.ofReal (1 - e) • R
    have hQprob : IsProbabilityMeasure Q := ⟨by
      simp only [Q, Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply,
        measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add hPos.1.le (sub_nonneg.mpr hPos.2.le)]
      norm_num⟩
    have hQ : Q ∈ mixtureClassSet e P :=
      { positivity := Or.inr hPos
        observed_probability := inferInstance
        candidate_probability := hQprob
        representation := fun _ => ⟨R, hR, hRac, rfl⟩
        boundary := fun he => (ne_of_lt hPos.2 he).elim }
    refine ⟨Q, hQ, ?_⟩
    exact (integral_propensity_mixture P R e h hPos hmeas hbounded hRac).symm

/-- The lower expectation endpoint of the dominated-residual mixture class.  For the specified model objects, [the stated conditions](hyp:h,hPos,hmeas,hbounded), [the stated mathematical relationship holds](goal).
-/
-- @node: mixtureClass_integral_sInf
lemma mixtureClass_integral_sInf {Y : Type*} [MeasurableSpace Y]
    (P : Measure Y) [IsProbabilityMeasure P] (e : ℝ) (h : Y → ℝ)
    (hPos : StrictPositivity e) (hmeas : Measurable h)
    (hbounded : ∃ C : ℝ, ∀ᵐ x ∂P, |h x| ≤ C) :
    sInf {θ : ℝ | ∃ Q ∈ mixtureClassSet e P, θ = ∫ x, h x ∂Q} =
      lowerQueryEndpoint e P h := by
  let T : Set ℝ := {θ : ℝ | ∃ R : Measure Y, IsProbabilityMeasure R ∧
    R.AbsolutelyContinuous P ∧ θ = ∫ x, h x ∂R}
  obtain ⟨hTne, hTbelow, _⟩ := dominatedIntegral_set_bounds P h hmeas hbounded
  rw [mixtureIntegral_values_eq_affine P e h hPos hmeas hbounded,
    sInf_affine_image T _ _ hTne hTbelow (sub_pos.mpr hPos.2)]
  rw [dominatedProbability_integral_sInf P h hmeas hbounded]
  rfl

/-- The upper expectation endpoint of the dominated-residual mixture class.  For the specified model objects, [the stated conditions](hyp:h,hPos,hmeas,hbounded), [the stated mathematical relationship holds](goal).
-/
-- @node: mixtureClass_integral_sSup
lemma mixtureClass_integral_sSup {Y : Type*} [MeasurableSpace Y]
    (P : Measure Y) [IsProbabilityMeasure P] (e : ℝ) (h : Y → ℝ)
    (hPos : StrictPositivity e) (hmeas : Measurable h)
    (hbounded : ∃ C : ℝ, ∀ᵐ x ∂P, |h x| ≤ C) :
    sSup {θ : ℝ | ∃ Q ∈ mixtureClassSet e P, θ = ∫ x, h x ∂Q} =
      upperQueryEndpoint e P h := by
  let T : Set ℝ := {θ : ℝ | ∃ R : Measure Y, IsProbabilityMeasure R ∧
    R.AbsolutelyContinuous P ∧ θ = ∫ x, h x ∂R}
  obtain ⟨hTne, _, hTabove⟩ := dominatedIntegral_set_bounds P h hmeas hbounded
  rw [mixtureIntegral_values_eq_affine P e h hPos hmeas hbounded,
    sSup_affine_image T _ _ hTne hTabove (sub_pos.mpr hPos.2)]
  rw [dominatedProbability_integral_sSup P h hmeas hbounded]
  rfl

end CausalSmith.SCM.PropensityLvSharpnessFrontier
