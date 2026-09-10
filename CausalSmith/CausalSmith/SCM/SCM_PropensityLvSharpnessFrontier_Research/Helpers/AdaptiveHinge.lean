import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Statements

/-! # Analytic facts for the propensity-adaptive hinge -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set

/-- The propensity-adaptive hinge is an admissible generator with zero
calibrated radius at every strictly positive propensity.  For the specified model objects, [the stated conditions](hyp:hPos), [the stated mathematical relationship holds](goal).
-/
-- @node: adaptiveHinge_admissible_and_radius
lemma adaptiveHinge_admissible_and_radius (e : ℝ) (hPos : StrictPositivity e) :
    AdmissibleGenerator (adaptiveHinge e) ∧
      divRadius (adaptiveHinge e) e = 0 := by
  have he : e ≠ 0 := ne_of_gt hPos.1
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · apply Continuous.continuousOn
      unfold adaptiveHinge
      fun_prop
    · constructor
      · exact convex_Ici 0
      · intro x hx y hy a b ha hb hab
        change max (a * x + b * y - 1 / e) 0 ≤
          a * max (x - 1 / e) 0 + b * max (y - 1 / e) 0
        apply max_le
        · calc
            a * x + b * y - 1 / e =
                a * x + b * y - (a + b) * (1 / e) := by rw [hab]; ring
            _ = a * (x - 1 / e) + b * (y - 1 / e) := by ring
            _ ≤ a * max (x - 1 / e) 0 + b * max (y - 1 / e) 0 :=
              add_le_add
                (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
                (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
        · positivity
    · have hc : 1 ≤ 1 / e := one_le_one_div hPos.1 hPos.2.le
      simp only [adaptiveHinge, max_eq_right (sub_nonpos.mpr hc)]
  · simp [divRadius, adaptiveHinge, one_div, hPos.1.le]

/-- A measurable propensity system produces a jointly measurable adaptive
hinge over the finite arm index, covariate, and likelihood-ratio argument.  For the specified model objects, [the stated conditions](hyp:he), [the stated mathematical relationship holds](goal).
-/
-- @node: measurable_adaptiveHinge_joint
lemma measurable_adaptiveHinge_joint {X : Type*} [MeasurableSpace X]
    (e : Bool → X → ℝ) (he : ∀ a, Measurable (e a)) :
    Measurable (fun z : Bool × X × ℝ => adaptiveHinge (e z.1 z.2.1) z.2.2) := by
  have heJoint : Measurable (fun z : Bool × X => e z.1 z.2) := by
    have hset : MeasurableSet {z : Bool × X | z.1 = true} :=
      (measurableSet_singleton true).preimage measurable_fst
    have hpiece : Measurable (fun z : Bool × X =>
        if z ∈ {z : Bool × X | z.1 = true} then e true z.2 else e false z.2) :=
      ((he true).comp measurable_snd).piecewise hset ((he false).comp measurable_snd)
    convert hpiece using 1
    funext z
    rcases z with ⟨b, x⟩
    cases b <;> simp
  have heTriple : Measurable (fun z : Bool × X × ℝ => e z.1 z.2.1) :=
    heJoint.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  unfold adaptiveHinge
  fun_prop

/-- For probability laws, nonpositive adaptive-hinge divergence is exactly
the propensity likelihood-ratio cap.  For the specified model objects, [the stated mathematical relationship holds](goal).
-/
-- @node: adaptiveHinge_fDiv_nonpos_iff_cap
lemma adaptiveHinge_fDiv_nonpos_iff_cap {Y : Type*} [MeasurableSpace Y]
    (e : ℝ) (P Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    fDiv (adaptiveHinge e) P Q ≤ (0 : EReal) ↔
      ∀ᵐ y ∂Q, (P.rnDeriv Q y).toReal ≤ 1 / e := by
  have hInt : Integrable (fun y => adaptiveHinge e ((P.rnDeriv Q y).toReal)) Q := by
    have hSub := (Measure.integrable_toReal_rnDeriv (μ := P) (ν := Q)).sub
      (integrable_const (1 / e))
    convert (hSub.add hSub.abs).const_mul (1 / 2) using 1
    funext y
    change max ((P.rnDeriv Q y).toReal - 1 / e) 0 =
      (1 / 2 : ℝ) * (((P.rnDeriv Q y).toReal - 1 / e) +
        |(P.rnDeriv Q y).toReal - 1 / e|)
    by_cases hy : (P.rnDeriv Q y).toReal - 1 / e ≤ 0
    · rw [max_eq_right hy, abs_of_nonpos hy]
      ring
    · have hy' : 0 ≤ (P.rnDeriv Q y).toReal - 1 / e := le_of_not_ge hy
      rw [max_eq_left hy', abs_of_nonneg hy']
      ring
  rw [show fDiv (adaptiveHinge e) P Q =
      ((∫ y, adaptiveHinge e ((P.rnDeriv Q y).toReal) ∂Q : ℝ) : EReal) by
    simp [fDiv, hInt]]
  norm_cast
  have hNonneg : 0 ≤ᵐ[Q] fun y => adaptiveHinge e ((P.rnDeriv Q y).toReal) := by
    filter_upwards [] with y
    exact le_max_right _ _
  have hIntegralNonneg : 0 ≤ ∫ y, adaptiveHinge e ((P.rnDeriv Q y).toReal) ∂Q :=
    integral_nonneg_of_ae hNonneg
  constructor
  · intro hle
    have hz : ∫ y, adaptiveHinge e ((P.rnDeriv Q y).toReal) ∂Q = 0 :=
      le_antisymm hle hIntegralNonneg
    have hae := (integral_eq_zero_iff_of_nonneg_ae hNonneg hInt).1 hz
    filter_upwards [hae] with y hy
    simpa [adaptiveHinge] using hy
  · intro hcap
    have hae : (fun y => adaptiveHinge e ((P.rnDeriv Q y).toReal)) =ᵐ[Q] 0 := by
      filter_upwards [hcap] with y hy
      have hy' : (P.rnDeriv Q y).toReal ≤ e⁻¹ := by simpa only [one_div] using hy
      simp [adaptiveHinge, hy']
    rw [(integral_eq_zero_iff_of_nonneg_ae hNonneg hInt).2 hae]

/-- Under strict propensity positivity, the likelihood-ratio cap is equivalent
to domination by the propensity-scaled observed law.  For the specified model objects, [the stated conditions](hyp:hPos,hAC), [the stated mathematical relationship holds](goal).
-/
-- @node: adaptiveHinge_cap_iff_measure_le
lemma adaptiveHinge_cap_iff_measure_le {Y : Type*} [MeasurableSpace Y]
    (e : ℝ) (P Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPos : StrictPositivity e) (hAC : P.AbsolutelyContinuous Q) :
    (∀ᵐ x ∂Q, (P.rnDeriv Q x).toReal ≤ 1 / e) ↔
      ENNReal.ofReal e • P ≤ Q := by
  have he_top : ENNReal.ofReal e ≠ ⊤ := ENNReal.ofReal_ne_top
  have heP_ac : (ENNReal.ofReal e • P).AbsolutelyContinuous Q := by
    intro s hs
    simp [Measure.smul_apply, hAC hs]
  rw [← Measure.rnDeriv_le_one_iff_le heP_ac]
  constructor
  · intro h
    filter_upwards [h, Measure.rnDeriv_smul_left_of_ne_top P Q he_top,
      P.rnDeriv_ne_top Q] with x hx hscale hfinite
    rw [hscale]
    simp only [Pi.one_apply]
    apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top he_top hfinite)
      ENNReal.one_ne_top).mp
    simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal hPos.1.le]
    exact (le_div_iff₀' hPos.1).1 hx
  · intro h
    filter_upwards [h, Measure.rnDeriv_smul_left_of_ne_top P Q he_top,
      P.rnDeriv_ne_top Q] with x hx hscale hfinite
    rw [hscale] at hx
    simp only [Pi.one_apply] at hx
    have hr := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top he_top hfinite)
      ENNReal.one_ne_top).2 hx
    simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal hPos.1.le] at hr
    exact (le_div_iff₀' hPos.1).2 hr

/-- The common-conull adaptive-hinge ball is exactly the common-conull
measure-cap class.  For the specified model objects, [the stated conditions](hyp:hOverlap,hP), [the stated mathematical relationship holds](goal).
-/
-- @node: condAdaptiveHingeBallOneSided_eq_condCap
lemma condAdaptiveHingeBallOneSided_eq_condCap
    {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) [IsProbabilityMeasure muX]
    (e : Bool → X → ℝ) (P : Bool → Kernel X Y)
    (hOverlap : CondOverlap kappa e) (hP : ∀ a, IsMarkovKernel (P a)) :
    condAdaptiveHingeBallOneSidedSet kappa muX e P = condCapSet muX e P := by
  ext Q
  constructor
  · intro hQ
    refine ⟨hQ.candidate_markov, ?_⟩
    obtain ⟨S, hS, hSc, hfib⟩ := hQ.fiberwise
    refine ⟨S, hS, hSc, ?_⟩
    intro x hx a
    have heRange := hOverlap.2.2.2 x a
    have hePos : StrictPositivity (e a x) := by
      constructor <;> linarith [hOverlap.1, heRange.1, heRange.2]
    have hAC := (hfib x hx a).1
    letI : IsMarkovKernel (P a) := hP a
    letI : IsMarkovKernel (Q a) := hQ.candidate_markov a
    have hdiv := (hfib x hx a).2
    rw [(adaptiveHinge_admissible_and_radius (e a x) hePos).2] at hdiv
    have hcap :=
      (adaptiveHinge_fDiv_nonpos_iff_cap (e a x) (P a x) (Q a x)).1 hdiv
    exact ⟨(adaptiveHinge_cap_iff_measure_le (e a x) (P a x) (Q a x) hePos hAC).1 hcap,
      hAC, hcap⟩
  · intro hQ
    refine
      { overlap := hOverlap
        covariate_probability := inferInstance
        observed_markov := hP
        candidate_markov := hQ.1
        fiberwise := ?_ }
    obtain ⟨S, hS, hSc, hcap⟩ := hQ.2
    refine ⟨S, hS, hSc, ?_⟩
    intro x hx a
    have heRange := hOverlap.2.2.2 x a
    have hePos : StrictPositivity (e a x) := by
      constructor <;> linarith [hOverlap.1, heRange.1, heRange.2]
    letI : IsMarkovKernel (P a) := hP a
    letI : IsMarkovKernel (Q a) := hQ.1 a
    have hradius := (adaptiveHinge_admissible_and_radius (e a x) hePos).2
    refine ⟨(hcap x hx a).2.1, ?_⟩
    rw [hradius]
    exact (adaptiveHinge_fDiv_nonpos_iff_cap (e a x) (P a x) (Q a x)).2
      (hcap x hx a).2.2

end CausalSmith.SCM.PropensityLvSharpnessFrontier
