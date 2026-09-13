import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Decoder
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Scalar conditional-rank identities

This file proves the one-dimensional integration step in equation (12): evaluating a
conditional CDF at a strictly monotone score returns the intervention CDF, reflected when
the score is decreasing.
-/

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- Equation (11): conditional on predecessor ranks (hence on the parents), the target log-ratio
CDF integrates the intervention density over own-coordinate values below the log-ratio threshold. -/
def equationElevenConditionalRatioCDF
    {n : ℕ} {G : Causalean.DAG (Fin n)} (θ : Mechanism n G)
    (i : Fin n) (t : ℝ) (v : LatentState n) : ℝ :=
  ∫ w in Set.Icc (0 : ℝ) 1,
    if Real.log (θ.q i w / θ.p i (Function.update v i w)) ≤ t then θ.q i w else 0

-- @node: interventionCDF_mem_Icc
/-- The normalized positive intervention density has a distribution function valued in the
unit interval at every point of the unit interval.  Given [the stated inputs and conditions](hyp:hpos,hz), [the stated conclusion](goal) follows. -/
lemma interventionCDF_mem_Icc
    {n : ℕ} {G : Causalean.DAG (Fin n)} (θ : Mechanism n G)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (i : Fin n) (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    interventionCDF θ i z ∈ Set.Icc (0 : ℝ) 1 := by
  have hq : IntervalIntegrable (θ.q i) volume 0 1 := by
    have hcont : ContinuousOn (θ.q i) (uIcc (0 : ℝ) 1) := by
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
        (hpos.2.2.2.1 i).continuousOn
    exact hcont.intervalIntegrable
  have hq_nonneg : ∀ᵐ w ∂volume.restrict (Set.Ioc (0 : ℝ) 1), 0 ≤ θ.q i w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    exact le_of_lt (hpos.2.1 i w ⟨le_of_lt hw.1, hw.2⟩)
  have hnorm := hpos.2.2.2.2.2 i
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one] at hnorm
  rw [interventionCDF]
  constructor
  · exact intervalIntegral.integral_nonneg hz.1 fun w hw ↦
      le_of_lt (hpos.2.1 i w ⟨hw.1, hw.2.trans hz.2⟩)
  · rw [← hnorm]
    exact intervalIntegral.integral_mono_interval le_rfl hz.1 hz.2 hq_nonneg hq

-- @node: equationElevenConditionalRatioCDF_mem_Icc
/-- The equation-(11) conditional kernel is a genuine unit-interval-valued CDF at every
threshold and every latent state in the cube.  Given [the stated inputs and conditions](hyp:hpos,hv), [the stated conclusion](goal) follows. -/
lemma equationElevenConditionalRatioCDF_mem_Icc
    {n : ℕ} {G : Causalean.DAG (Fin n)} (θ : Mechanism n G)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (i : Fin n) (t : ℝ) (v : LatentState n) (hv : v ∈ latentCube n) :
    equationElevenConditionalRatioCDF θ i t v ∈ Set.Icc (0 : ℝ) 1 := by
  let f : ℝ → ℝ := fun w ↦
    if Real.log (θ.q i w / θ.p i (Function.update v i w)) ≤ t then θ.q i w else 0
  have hq : IntegrableOn (θ.q i) (Set.Icc (0 : ℝ) 1) := by
    exact (hpos.2.2.2.1 i).continuousOn.integrableOn_compact isCompact_Icc
  have hscore : ContinuousOn
      (fun w ↦ Real.log (θ.q i w / θ.p i (Function.update v i w)))
      (Set.Icc (0 : ℝ) 1) := by
    have hqcont := (hpos.2.2.2.1 i).continuousOn
    have hpcont : ContinuousOn (fun w ↦ θ.p i (Function.update v i w))
        (Set.Icc (0 : ℝ) 1) := by
      apply (hpos.2.2.1 i).continuousOn.comp
      · fun_prop
      · intro w hw j hj
        by_cases hji : j = i
        · subst j
          simpa using hw
        · simp [hji]
          exact hv j (Set.mem_univ j)
    have hpne : ∀ w ∈ Set.Icc (0 : ℝ) 1, θ.p i (Function.update v i w) ≠ 0 :=
      fun w hw ↦ ne_of_gt (hpos.1 i _ (by
        intro j hj
        by_cases hji : j = i
        · subst j
          simpa using hw
        · simp [hji]
          exact hv j (Set.mem_univ j)))
    have hqne : ∀ w ∈ Set.Icc (0 : ℝ) 1, θ.q i w ≠ 0 :=
      fun w hw ↦ ne_of_gt (hpos.2.1 i w hw)
    exact (hqcont.div hpcont hpne).log
      (fun w hw ↦ div_ne_zero (hqne w hw) (hpne w hw))
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hqae : AEMeasurable (θ.q i) μ :=
    (hpos.2.2.2.1 i).continuousOn.aemeasurable measurableSet_Icc
  have hscoreae : AEMeasurable
      (fun w ↦ Real.log (θ.q i w / θ.p i (Function.update v i w))) μ :=
    hscore.aemeasurable measurableSet_Icc
  let qm := hqae.mk
  let sm := hscoreae.mk
  have hfm : Measurable (fun w ↦ if sm w ≤ t then qm w else 0) := by
    exact Measurable.ite (measurableSet_le hscoreae.measurable_mk measurable_const)
      hqae.measurable_mk measurable_const
  have hfeq : (fun w ↦ if sm w ≤ t then qm w else 0) =ᵐ[μ] f := by
    filter_upwards [hqae.ae_eq_mk, hscoreae.ae_eq_mk] with w hqw hsw
    simp only [qm, sm] at hqw hsw ⊢
    rw [← hqw, ← hsw]
  have hfstrong : AEStronglyMeasurable f μ :=
    hfm.aestronglyMeasurable.congr hfeq
  have hf : IntegrableOn f (Set.Icc (0 : ℝ) 1) := by
    apply hq.mono' hfstrong
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
      simp only [f]
      split
      · rw [Real.norm_eq_abs, abs_of_pos (hpos.2.1 i w hw)]
      · simpa only [norm_zero] using le_of_lt (hpos.2.1 i w hw)
  have hnonneg : 0 ≤ ∫ w in Set.Icc (0 : ℝ) 1, f w := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
    simp only [f]
    split
    · exact le_of_lt (hpos.2.1 i w hw)
    · exact le_rfl
  have hle : (∫ w in Set.Icc (0 : ℝ) 1, f w) ≤
      ∫ w in Set.Icc (0 : ℝ) 1, θ.q i w := by
    apply MeasureTheory.integral_mono_ae hf hq
    filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
    simp only [f]
    split
    · exact le_rfl
    · exact le_of_lt (hpos.2.1 i w hw)
  rw [hpos.2.2.2.2.2 i] at hle
  change 0 ≤ ∫ w in Set.Icc (0 : ℝ) 1, f w ∧
    (∫ w in Set.Icc (0 : ℝ) 1, f w) ≤ 1
  exact ⟨hnonneg, hle⟩

-- @node: equationElevenConditionalRatioCDF_eq_of_parents_eq
/-- The equation-(11) kernel depends on the conditioning state only through the target's
parent coordinates.  Given [the stated inputs and conditions](hyp:hparents), [the stated conclusion](goal) follows. -/
lemma equationElevenConditionalRatioCDF_eq_of_parents_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} (θ : Mechanism n G)
    (i : Fin n) (t : ℝ) {v v' : LatentState n}
    (hparents : ∀ j ∈ G.parents i, v j = v' j) :
    equationElevenConditionalRatioCDF θ i t v =
      equationElevenConditionalRatioCDF θ i t v' := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with w
  have hp : θ.p i (Function.update v i w) =
      θ.p i (Function.update v' i w) := by
    apply θ.parent_local i
    · simp
    · intro j hj
      have hji : j ≠ i := by
        intro hEq
        subst j
        exact G.acyclic i (Relation.TransGen.single (G.mem_parents.mp hj))
      simpa [Function.update, hji] using hparents j hj
  rw [hp]

-- @node: conditionalCDF_at_strictMono_score
/-- On the unit interval, a score whose lower level set at `z` is `[0,z]` has conditional
CDF equal to the integral of its density from zero to `z`.  Given [the stated inputs and conditions](hyp:hz,hlevel), [the stated conclusion](goal) follows. -/
lemma conditionalCDF_at_strictMono_score
    (q score : ℝ → ℝ) (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hlevel : ∀ w ∈ Set.Icc (0 : ℝ) 1, score w ≤ score z ↔ w ≤ z) :
    (∫ w in Set.Icc (0 : ℝ) 1, if score w ≤ score z then q w else 0) =
      ∫ w in (0 : ℝ)..z, q w := by
  rw [intervalIntegral.integral_of_le hz.1,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← MeasureTheory.integral_indicator measurableSet_Icc,
    ← MeasureTheory.integral_indicator measurableSet_Icc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with w
  by_cases hw : w ∈ Set.Icc (0 : ℝ) 1
  · simp only [Set.indicator_of_mem hw]
    have hm := hlevel w hw
    by_cases hwz : w ≤ z
    · have hwmem : w ∈ Set.Icc (0 : ℝ) z := ⟨hw.1, hwz⟩
      simp [hm, hwz, hwmem]
    · have hwnmem : w ∉ Set.Icc (0 : ℝ) z := fun h ↦ hwz h.2
      simp [hm, hwz, hwnmem]
  · have hw' : w ∉ Set.Icc (0 : ℝ) z := by
      intro hwz
      exact hw ⟨hwz.1, hwz.2.trans hz.2⟩
    simp [hw, hw']

-- @node: conditionalCDF_at_strictAnti_score
/-- On the unit interval, a decreasing score has conditional CDF equal to one minus the
integral of its normalized density from zero to `z`.  Given [the stated inputs and conditions](hyp:hz,hq,hnorm,hlevel), [the stated conclusion](goal) follows. -/
lemma conditionalCDF_at_strictAnti_score
    (q score : ℝ → ℝ) (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hq : IntervalIntegrable q volume 0 1)
    (hnorm : ∫ w in Set.Icc (0 : ℝ) 1, q w = 1)
    (hlevel : ∀ w ∈ Set.Icc (0 : ℝ) 1, score w ≤ score z ↔ z ≤ w) :
    (∫ w in Set.Icc (0 : ℝ) 1, if score w ≤ score z then q w else 0) =
      1 - ∫ w in (0 : ℝ)..z, q w := by
  have htail :
      (∫ w in Set.Icc (0 : ℝ) 1, if score w ≤ score z then q w else 0) =
        ∫ w in z..(1 : ℝ), q w := by
    rw [intervalIntegral.integral_of_le hz.2,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← MeasureTheory.integral_indicator measurableSet_Icc,
      ← MeasureTheory.integral_indicator measurableSet_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with w
    by_cases hw : w ∈ Set.Icc (0 : ℝ) 1
    · simp only [Set.indicator_of_mem hw]
      have hm := hlevel w hw
      by_cases hzw : z ≤ w
      · have hwmem : w ∈ Set.Icc z (1 : ℝ) := ⟨hzw, hw.2⟩
        simp [hm, hzw, hwmem]
      · have hwnmem : w ∉ Set.Icc z (1 : ℝ) := fun h ↦ hzw h.1
        simp [hm, hzw, hwnmem]
    · have hw' : w ∉ Set.Icc z (1 : ℝ) := by
        intro hwz
        exact hw ⟨hz.1.trans hwz.1, hwz.2⟩
      simp [hw, hw']
  rw [htail]
  have hq0z : IntervalIntegrable q volume 0 z := by
    apply hq.mono_set
    rw [uIcc_of_le hz.1, uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc_right hz.2
  have hqz1 : IntervalIntegrable q volume z 1 := by
    apply hq.mono_set
    rw [uIcc_of_le hz.2, uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc_left hz.1
  have hadd := intervalIntegral.integral_add_adjacent_intervals hq0z hqz1
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one] at hnorm
  linarith

-- @node: conditionalCDF_at_strictMonoOn_score
/-- A normalized density evaluated through a strictly increasing score produces its ordinary
distribution function.  Given [the stated inputs and conditions](hyp:hz,hmono), [the stated conclusion](goal) follows. -/
lemma conditionalCDF_at_strictMonoOn_score
    (q score : ℝ → ℝ) (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hmono : StrictMonoOn score (Set.Icc (0 : ℝ) 1)) :
    (∫ w in Set.Icc (0 : ℝ) 1, if score w ≤ score z then q w else 0) =
      ∫ w in (0 : ℝ)..z, q w := by
  apply conditionalCDF_at_strictMono_score q score z hz
  intro w hw
  exact hmono.le_iff_le hw hz

-- @node: conditionalCDF_at_strictAntiOn_score
/-- A normalized density evaluated through a strictly decreasing score produces its reflected
distribution function.  Given [the stated inputs and conditions](hyp:hz,hq,hnorm,hanti), [the stated conclusion](goal) follows. -/
lemma conditionalCDF_at_strictAntiOn_score
    (q score : ℝ → ℝ) (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hq : IntervalIntegrable q volume 0 1)
    (hnorm : ∫ w in Set.Icc (0 : ℝ) 1, q w = 1)
    (hanti : StrictAntiOn score (Set.Icc (0 : ℝ) 1)) :
    (∫ w in Set.Icc (0 : ℝ) 1, if score w ≤ score z then q w else 0) =
      1 - ∫ w in (0 : ℝ)..z, q w := by
  apply conditionalCDF_at_strictAnti_score q score z hz hq hnorm
  intro w hw
  exact hanti.le_iff_ge hw hz

-- @node: equationEleven_at_strictMonoOwnScore
/-- Equation (11), evaluated at the realized own-coordinate score, is the intervention CDF
when that score is strictly increasing on the unit interval.  Given [the stated inputs and conditions](hyp:hv,hmono), [the stated conclusion](goal) follows. -/
lemma equationEleven_at_strictMonoOwnScore
    {n : ℕ} {G : Causalean.DAG (Fin n)} (θ : Mechanism n G)
    (i : Fin n) (v : LatentState n) (hv : v ∈ latentCube n)
    (hmono : StrictMonoOn
      (fun w => Real.log (θ.q i w / θ.p i (Function.update v i w)))
      (Set.Icc (0 : ℝ) 1)) :
    equationElevenConditionalRatioCDF θ i
        (Real.log (θ.q i (v i) / θ.p i v)) v =
      interventionCDF θ i (v i) := by
  have hvi : v i ∈ Set.Icc (0 : ℝ) 1 := hv i (Set.mem_univ i)
  have hvupdate : Function.update v i (v i) = v := Function.update_eq_self i v
  simpa only [equationElevenConditionalRatioCDF, interventionCDF, hvupdate] using
    conditionalCDF_at_strictMonoOn_score (θ.q i)
      (fun w => Real.log (θ.q i w / θ.p i (Function.update v i w))) (v i) hvi hmono

-- @node: equationEleven_at_strictAntiOwnScore
/-- Equation (11), evaluated at the realized own-coordinate score, is the reflected
intervention CDF when that score is strictly decreasing on the unit interval.  Given [the stated inputs and conditions](hyp:hpos,hv,hanti), [the stated conclusion](goal) follows. -/
lemma equationEleven_at_strictAntiOwnScore
    {n : ℕ} {G : Causalean.DAG (Fin n)} (θ : Mechanism n G)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (i : Fin n) (v : LatentState n) (hv : v ∈ latentCube n)
    (hanti : StrictAntiOn
      (fun w => Real.log (θ.q i w / θ.p i (Function.update v i w)))
      (Set.Icc (0 : ℝ) 1)) :
    equationElevenConditionalRatioCDF θ i
        (Real.log (θ.q i (v i) / θ.p i v)) v =
      1 - interventionCDF θ i (v i) := by
  have hvi : v i ∈ Set.Icc (0 : ℝ) 1 := hv i (Set.mem_univ i)
  have hvupdate : Function.update v i (v i) = v := Function.update_eq_self i v
  have hq : IntervalIntegrable (θ.q i) volume 0 1 := by
    have hcont : ContinuousOn (θ.q i) (uIcc (0 : ℝ) 1) := by
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
        (hpos.2.2.2.1 i).continuousOn
    exact hcont.intervalIntegrable
  simpa only [equationElevenConditionalRatioCDF, interventionCDF, hvupdate] using
    conditionalCDF_at_strictAntiOn_score (θ.q i)
      (fun w => Real.log (θ.q i w / θ.p i (Function.update v i w)))
      (v i) hvi hq (hpos.2.2.2.2.2 i) hanti

-- @node: fixedOwnDerivativeSign_strictMonoOn
/-- A positive prescribed own-score derivative makes the own-coordinate score strictly
increasing on the closed unit interval.  Given [the stated inputs and conditions](hyp:hpos,hsign,hv,hsi), [the stated conclusion](goal) follows. -/
lemma fixedOwnDerivativeSign_strictMonoOn
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hsign : FixedOwnDerivativeSign G s θ)
    (i : Fin n) (v : LatentState n) (hv : v ∈ latentCube n)
    (hsi : s.value i = 1) :
    StrictMonoOn
      (fun w => Real.log (θ.q i w / θ.p i (Function.update v i w)))
      (Set.Icc (0 : ℝ) 1) := by
  let score : ℝ → ℝ := fun w => Real.log (θ.q i w / θ.p i (Function.update v i w))
  apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
  · have hq : ContinuousOn (θ.q i) (Set.Icc (0 : ℝ) 1) := (hpos.2.2.2.1 i).continuousOn
    have hp : ContinuousOn (fun w => θ.p i (Function.update v i w)) (Set.Icc (0 : ℝ) 1) := by
      apply (hpos.2.2.1 i).continuousOn.comp
      · fun_prop
      · intro w hw j hj
        by_cases hji : j = i
        · subst j
          simpa using hw
        · simp [hji]
          exact hv j (Set.mem_univ j)
    have hpne : ∀ w ∈ Set.Icc (0 : ℝ) 1, θ.p i (Function.update v i w) ≠ 0 := fun w hw =>
      ne_of_gt (hpos.1 i _ (by
      intro j hj
      by_cases hji : j = i
      · subst j
        simpa using hw
      · simp [hji]
        exact hv j (Set.mem_univ j)))
    have hqne : ∀ w ∈ Set.Icc (0 : ℝ) 1, θ.q i w ≠ 0 := fun w hw =>
      ne_of_gt (hpos.2.1 i w hw)
    exact (hq.div hp hpne).log (fun w hw => div_ne_zero (hqne w hw) (hpne w hw))
  · intro w hw
    rw [interior_Icc] at hw
    have hwIcc : w ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hw.1, le_of_lt hw.2⟩
    let vw := Function.update v i w
    have hvw : vw ∈ latentCube n := by
      intro j hj
      by_cases hji : j = i
      · subst j
        simpa [vw] using hwIcc
      · simp [vw, hji]
        exact hv j (Set.mem_univ j)
    have hs := hsign i vw hvw
    rw [hsi, one_mul] at hs
    have hscore : (fun z => Real.log (θ.q i z / θ.p i (Function.update vw i z))) = score := by
      funext z
      simp [vw, score, Function.update_idem]
    have hderivWithin : derivWithin score (Set.Icc (0 : ℝ) 1) w =
        ownLogRatioDerivative θ i vw := by
      simp only [ownLogRatioDerivative, hscore, vw, Function.update_self]
    rw [← derivWithin_of_mem_nhds
      (Filter.mem_of_superset (Ioo_mem_nhds hw.1 hw.2) Set.Ioo_subset_Icc_self)]
    rw [hderivWithin]
    exact hs

-- @node: fixedOwnDerivativeSign_strictAntiOn
/-- A negative prescribed own-score derivative makes the own-coordinate score strictly
decreasing on the closed unit interval.  Given [the stated inputs and conditions](hyp:hpos,hsign,hv,hsi), [the stated conclusion](goal) follows. -/
lemma fixedOwnDerivativeSign_strictAntiOn
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hsign : FixedOwnDerivativeSign G s θ)
    (i : Fin n) (v : LatentState n) (hv : v ∈ latentCube n)
    (hsi : s.value i = -1) :
    StrictAntiOn
      (fun w => Real.log (θ.q i w / θ.p i (Function.update v i w)))
      (Set.Icc (0 : ℝ) 1) := by
  let score : ℝ → ℝ := fun w => Real.log (θ.q i w / θ.p i (Function.update v i w))
  apply strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) 1)
  · have hq : ContinuousOn (θ.q i) (Set.Icc (0 : ℝ) 1) := (hpos.2.2.2.1 i).continuousOn
    have hp : ContinuousOn (fun w => θ.p i (Function.update v i w)) (Set.Icc (0 : ℝ) 1) := by
      apply (hpos.2.2.1 i).continuousOn.comp
      · fun_prop
      · intro w hw j hj
        by_cases hji : j = i
        · subst j
          simpa using hw
        · simp [hji]
          exact hv j (Set.mem_univ j)
    have hpne : ∀ w ∈ Set.Icc (0 : ℝ) 1, θ.p i (Function.update v i w) ≠ 0 := fun w hw =>
      ne_of_gt (hpos.1 i _ (by
      intro j hj
      by_cases hji : j = i
      · subst j
        simpa using hw
      · simp [hji]
        exact hv j (Set.mem_univ j)))
    have hqne : ∀ w ∈ Set.Icc (0 : ℝ) 1, θ.q i w ≠ 0 := fun w hw =>
      ne_of_gt (hpos.2.1 i w hw)
    exact (hq.div hp hpne).log (fun w hw => div_ne_zero (hqne w hw) (hpne w hw))
  · intro w hw
    rw [interior_Icc] at hw
    have hwIcc : w ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hw.1, le_of_lt hw.2⟩
    let vw := Function.update v i w
    have hvw : vw ∈ latentCube n := by
      intro j hj
      by_cases hji : j = i
      · subst j
        simpa [vw] using hwIcc
      · simp [vw, hji]
        exact hv j (Set.mem_univ j)
    have hs := hsign i vw hvw
    rw [hsi] at hs
    have hscore : (fun z => Real.log (θ.q i z / θ.p i (Function.update vw i z))) = score := by
      funext z
      simp [vw, score, Function.update_idem]
    have hderivWithin : derivWithin score (Set.Icc (0 : ℝ) 1) w =
        ownLogRatioDerivative θ i vw := by
      simp only [ownLogRatioDerivative, hscore, vw, Function.update_self]
    rw [← derivWithin_of_mem_nhds
      (Filter.mem_of_superset (Ioo_mem_nhds hw.1 hw.2) Set.Ioo_subset_Icc_self)]
    rw [hderivWithin]
    linarith

/-- With parent coordinates fixed, equality of a node's log-ratio score is equivalent to equality
of its own coordinate.  Given [the stated inputs and conditions](hyp:hpos,hsign,hv,hw,hparents), [the stated conclusion](goal) follows. -/
lemma mechanismLogRatio_eq_iff_own_eq_of_parents_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hsign : FixedOwnDerivativeSign G s θ) (i : Fin n)
    {v w : LatentState n} (hv : v ∈ latentCube n) (hw : w ∈ latentCube n)
    (hparents : ∀ j ∈ G.parents i, v j = w j) :
    Real.log (θ.q i (v i) / θ.p i v) = Real.log (θ.q i (w i) / θ.p i w) ↔
      v i = w i := by
  let score : ℝ → ℝ := fun z ↦
    Real.log (θ.q i z / θ.p i (Function.update v i z))
  have hvi : v i ∈ Set.Icc (0 : ℝ) 1 := hv i (Set.mem_univ i)
  have hwi : w i ∈ Set.Icc (0 : ℝ) 1 := hw i (Set.mem_univ i)
  have hscore_v : score (v i) = Real.log (θ.q i (v i) / θ.p i v) := by
    simp [score, Function.update_eq_self]
  have hp_update : θ.p i (Function.update v i (w i)) = θ.p i w := by
    apply θ.parent_local i
    · simp
    · intro j hj
      have hji : j ≠ i := by
        intro hEq
        subst j
        exact G.acyclic i (Relation.TransGen.single (G.mem_parents.mp hj))
      simpa [Function.update, hji] using hparents j hj
  have hscore_w : score (w i) = Real.log (θ.q i (w i) / θ.p i w) := by
    simp only [score, hp_update]
  constructor
  · intro heq
    have hscore_eq : score (v i) = score (w i) := by
      rw [hscore_v, hscore_w]
      exact heq
    rcases s.signed i with hneg | hpossign
    · exact (fixedOwnDerivativeSign_strictAntiOn s θ hpos hsign i v hv hneg).injOn
        hvi hwi hscore_eq
    · exact (fixedOwnDerivativeSign_strictMonoOn s θ hpos hsign i v hv hpossign).injOn
        hvi hwi hscore_eq
  · intro hi
    have hp : θ.p i v = θ.p i w := θ.parent_local i v w hi hparents
    rw [hi, hp]

-- @node: equationEleven_at_fixedOwnDerivativeSign
/-- Equation (12) follows from equation (11) and the prescribed own-coordinate derivative
sign: the recovered rank is the intervention CDF, reflected exactly for negative sign.  Given [the stated inputs and conditions](hyp:hpos,hsign,hv), [the stated conclusion](goal) follows. -/
lemma equationEleven_at_fixedOwnDerivativeSign
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hsign : FixedOwnDerivativeSign G s θ)
    (i : Fin n) (v : LatentState n) (hv : v ∈ latentCube n) :
    equationElevenConditionalRatioCDF θ i
        (Real.log (θ.q i (v i) / θ.p i v)) v =
      if s.value i = 1 then interventionCDF θ i (v i)
      else 1 - interventionCDF θ i (v i) := by
  rcases s.signed i with hneg | hposi
  · rw [if_neg (by linarith : s.value i ≠ 1)]
    exact equationEleven_at_strictAntiOwnScore θ hpos i v hv
      (fixedOwnDerivativeSign_strictAntiOn s θ hpos hsign i v hv hneg)
  · rw [if_pos hposi]
    exact equationEleven_at_strictMonoOwnScore θ i v hv
      (fixedOwnDerivativeSign_strictMonoOn s θ hpos hsign i v hv hposi)

-- @node: equationEleven_at_fixedOwnDerivativeSign_mem_Icc
/-- At the realized score, the signed equation-(11) formula has the unit-interval range
required by the decoder's conditional-CDF codomain.  Given [the stated inputs and conditions](hyp:hpos,hsign,hv), [the stated conclusion](goal) follows. -/
lemma equationEleven_at_fixedOwnDerivativeSign_mem_Icc
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hsign : FixedOwnDerivativeSign G s θ)
    (i : Fin n) (v : LatentState n) (hv : v ∈ latentCube n) :
    equationElevenConditionalRatioCDF θ i
        (Real.log (θ.q i (v i) / θ.p i v)) v ∈ Set.Icc (0 : ℝ) 1 := by
  rw [equationEleven_at_fixedOwnDerivativeSign s θ hpos hsign i v hv]
  have hvi : v i ∈ Set.Icc (0 : ℝ) 1 := hv i (Set.mem_univ i)
  have hQ := interventionCDF_mem_Icc θ hpos i (v i) hvi
  split
  · exact hQ
  · constructor <;> linarith [hQ.1, hQ.2]

-- @node: observedLawRankCoordinate_eq_of_equationEleven
/-- Once the law-selected conditional CDF is identified with equation (11), evaluating it at
the pointwise identified log ratio gives the signed intervention-CDF rank of equation (12).  Given [the stated inputs and conditions](hyp:hpos,hsign,hEleven,hRatio), [the stated conclusion](goal) follows. -/
lemma observedLawRankCoordinate_eq_of_equationEleven
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (W : ObservedWorld G θ)
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hsign : FixedOwnDerivativeSign G s θ)
    (i : Fin n)
    (hEleven : ∀ t v, v ∈ latentCube n →
      (observedConditionalRatioCDF laws order i t
          (familyProjection (observedLawLogRatio laws.1)
            (predecessorSet order i) (W.mix v)) : ℝ) =
        equationElevenConditionalRatioCDF θ (W.targetPerm i) t v)
    (hRatio : ∀ v, v ∈ latentCube n →
      observedLawLogRatio laws.1 i (W.mix v) =
        Real.log (θ.q (W.targetPerm i) (v (W.targetPerm i)) /
          θ.p (W.targetPerm i) v)) :
    ∀ v, v ∈ latentCube n →
      (observedLawRankCoordinate laws order i (W.mix v) : ℝ) =
        if s.value (W.targetPerm i) = 1
        then interventionCDF θ (W.targetPerm i) (v (W.targetPerm i))
        else 1 - interventionCDF θ (W.targetPerm i) (v (W.targetPerm i)) := by
  intro v hv
  rw [observedLawRankCoordinate, hEleven _ v hv, hRatio v hv]
  exact equationEleven_at_fixedOwnDerivativeSign s θ hpos hsign
    (W.targetPerm i) v hv

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
