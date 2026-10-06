module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialVanTreesRegularity

/-! # Product integral identities for the sequential van Trees adapter -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Causalean.Stat.Minimax.ObservationDependentVanTrees

/-- Integrable normalized likelihood sections lift an integrable nonnegative
prior density to an integrable joint density. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:w,p,hw_nonneg,hp_nonneg,hpint,hnorm,hwint,hmeas), these specify the stated inputs. -/
lemma integrable_jointDensity_of_normalization {X : Type*} [MeasurableSpace X]
    {mu : Measure X} [SigmaFinite mu] {ell upper : ℝ}
    (w : ℝ → ℝ) (p : ℝ → X → ℝ)
    (hw_nonneg : ∀ a, 0 ≤ w a) (hp_nonneg : ∀ a x, 0 ≤ p a x)
    (hpint : ∀ᵐ a ∂parameterMeasure ell upper, Integrable (fun x ↦ p a x) mu)
    (hnorm : ∀ᵐ a ∂parameterMeasure ell upper, ∫ x, p a x ∂mu = 1)
    (hwint : Integrable w (parameterMeasure ell upper))
    (hmeas : AEStronglyMeasurable (jointDensity w p)
      ((parameterMeasure ell upper).prod mu)) :
    Integrable (jointDensity w p) ((parameterMeasure ell upper).prod mu) := by
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards [hpint] with a ha
    exact (ha.const_mul (w a)).congr (by
      filter_upwards with x
      rfl)
  · apply hwint.congr
    filter_upwards [hnorm] with a ha
    symm
    unfold jointDensity
    calc
      ∫ x, ‖w a * p a x‖ ∂mu = ∫ x, w a * p a x ∂mu := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.norm_of_nonneg (mul_nonneg (hw_nonneg a) (hp_nonneg a x))]
      _ = w a * ∫ x, p a x ∂mu :=
        integral_const_mul (μ := mu) (w a) (fun x ↦ p a x)
      _ = w a := by rw [ha, mul_one]

/-- Joint-density integrability gives integrability of the affine target
sensitivity field. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:w,p,v,mu,hjoint), these specify the stated inputs. -/
lemma integrable_sequentialSensitivity_of_jointDensity {X : Type*}
    [MeasurableSpace X] (w : ℝ → ℝ) (p : ℝ → X → ℝ)
    (v : TrialParameter) (mu : Measure (ℝ × X))
    (hjoint : Integrable (jointDensity w p) mu) :
    Integrable (sensitivityField w p (vtTargetDeriv (X := X) v)) mu := by
  have h := hjoint.const_mul (contrast v)
  apply h.congr
  filter_upwards with z
  unfold sensitivityField vtTargetDeriv
  rfl

/-- Prior-score integrability and normalized integrable likelihood sections
imply integrability of the lifted prior-score square on product space. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:w,dw,p,hw_nonneg,hp_nonneg,hpint,hnorm,hprior,hmeas), these specify the stated inputs. -/
lemma integrable_priorJointSq_of_normalization {X : Type*} [MeasurableSpace X]
    {mu : Measure X} [SigmaFinite mu] {ell upper : ℝ}
    (w dw : ℝ → ℝ) (p : ℝ → X → ℝ)
    (hw_nonneg : ∀ a, 0 ≤ w a) (hp_nonneg : ∀ a x, 0 ≤ p a x)
    (hpint : ∀ᵐ a ∂parameterMeasure ell upper, Integrable (fun x ↦ p a x) mu)
    (hnorm : ∀ᵐ a ∂parameterMeasure ell upper, ∫ x, p a x ∂mu = 1)
    (hprior : Integrable (fun a ↦ w a * (priorScore w dw a) ^ 2)
      (parameterMeasure ell upper))
    (hmeas : AEStronglyMeasurable (fun z : ℝ × X ↦
      w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2)
      ((parameterMeasure ell upper).prod mu)) :
    Integrable (fun z : ℝ × X ↦
      w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2)
      ((parameterMeasure ell upper).prod mu) := by
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards [hpint] with a ha
    have hc := ha.const_mul (w a * (priorScore w dw a) ^ 2)
    apply hc.congr
    filter_upwards with x
    ring
  · apply hprior.congr
    filter_upwards [hnorm] with a ha
    symm
    calc
      ∫ x, ‖w a * p a x * (priorScore w dw a) ^ 2‖ ∂mu =
          ∫ x, w a * p a x * (priorScore w dw a) ^ 2 ∂mu := by
            apply integral_congr_ae
            filter_upwards with x
            rw [Real.norm_of_nonneg (mul_nonneg
              (mul_nonneg (hw_nonneg a) (hp_nonneg a x)) (sq_nonneg _))]
      _ =
          (w a * (priorScore w dw a) ^ 2) * ∫ x, p a x ∂mu := by
            rw [← integral_const_mul (μ := mu)
              (w a * (priorScore w dw a) ^ 2) (fun x ↦ p a x)]
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = w a * (priorScore w dw a) ^ 2 := by rw [ha, mul_one]

/-- A normalized likelihood lifts the prior score square from parameter space to
parameter--observation product space without changing its integral. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:w,dw,p,hnorm,hint), these specify the stated inputs. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma integral_priorJointSq_eq_priorInformation {X : Type*} [MeasurableSpace X]
    {mu : Measure X} [SigmaFinite mu] {ell upper : ℝ}
    (w dw : ℝ → ℝ) (p : ℝ → X → ℝ)
    (hnorm : ∀ᵐ a ∂parameterMeasure ell upper, ∫ x, p a x ∂mu = 1)
    (hint : Integrable (fun z : ℝ × X =>
      w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2)
      ((parameterMeasure ell upper).prod mu)) :
    ∫ z, w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2
        ∂((parameterMeasure ell upper).prod mu) =
      priorInformation ell upper w dw := by
  letI : IsFiniteMeasure (parameterMeasure ell upper) := by
    unfold parameterMeasure
    infer_instance
  rw [integral_prod _ hint]
  unfold priorInformation
  apply integral_congr_ae
  filter_upwards [hnorm] with a ha
  calc
    ∫ x, w a * p a x * (priorScore w dw a) ^ 2 ∂mu =
        ∫ x, (w a * (priorScore w dw a) ^ 2) * p a x ∂mu := by
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = (w a * (priorScore w dw a) ^ 2) * ∫ x, p a x ∂mu :=
      integral_const_mul (μ := mu) (w a * (priorScore w dw a) ^ 2)
        (fun x ↦ p a x)
    _ = w a * (priorScore w dw a) ^ 2 := by rw [ha, mul_one]

/-- The product integral of the weighted likelihood-score square is the prior
average of conditional Fisher information. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:w,p,dp,hint), these specify the stated inputs. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma integral_fisherJointSq_eq {X : Type*} [MeasurableSpace X]
    {mu : Measure X} [SigmaFinite mu] {ell upper : ℝ}
    (w : ℝ → ℝ) (p dp : ℝ → X → ℝ)
    (hint : Integrable (fun z : ℝ × X =>
      w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2)
      ((parameterMeasure ell upper).prod mu)) :
    ∫ z, w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2
        ∂((parameterMeasure ell upper).prod mu) =
      ∫ a, w a * fisherInformation mu p dp a ∂parameterMeasure ell upper := by
  letI : IsFiniteMeasure (parameterMeasure ell upper) := by
    unfold parameterMeasure
    infer_instance
  rw [integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards with a
  unfold fisherInformation
  calc
    ∫ x, w a * p a x * (likelihoodScore p dp a x) ^ 2 ∂mu =
        ∫ x, w a * (p a x * (likelihoodScore p dp a x) ^ 2) ∂mu := by
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = w a * ∫ x, p a x * (likelihoodScore p dp a x) ^ 2 ∂mu :=
      integral_const_mul (μ := mu) (w a)
        (fun x ↦ p a x * (likelihoodScore p dp a x) ^ 2)

/-- Conditional centering of the likelihood score makes the prior--likelihood
score cross term integrate to zero. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:w,dw,p,dp,hcenter,hint), these specify the stated inputs. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma integral_priorLikelihoodCross_eq_zero {X : Type*} [MeasurableSpace X]
    {mu : Measure X} [SigmaFinite mu] {ell upper : ℝ}
    (w dw : ℝ → ℝ) (p dp : ℝ → X → ℝ)
    (hcenter : ∀ᵐ a ∂parameterMeasure ell upper,
      ∫ x, likelihoodScore p dp a x * p a x ∂mu = 0)
    (hint : Integrable (fun z : ℝ × X =>
      w z.1 * p z.1 z.2 *
        (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2))
      ((parameterMeasure ell upper).prod mu)) :
    ∫ z, w z.1 * p z.1 z.2 *
        (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2)
        ∂((parameterMeasure ell upper).prod mu) = 0 := by
  letI : IsFiniteMeasure (parameterMeasure ell upper) := by
    unfold parameterMeasure
    infer_instance
  rw [integral_prod _ hint]
  calc
    ∫ a, (∫ x, w a * p a x *
        (priorScore w dw a * likelihoodScore p dp a x) ∂mu)
        ∂parameterMeasure ell upper =
      ∫ a, 0 ∂parameterMeasure ell upper := by
        apply integral_congr_ae
        filter_upwards [hcenter] with a ha
        calc
          ∫ x, w a * p a x *
              (priorScore w dw a * likelihoodScore p dp a x) ∂mu =
            ∫ x, (w a * priorScore w dw a) *
              (likelihoodScore p dp a x * p a x) ∂mu := by
                apply integral_congr_ae
                filter_upwards with x
                ring
          _ = (w a * priorScore w dw a) *
              ∫ x, likelihoodScore p dp a x * p a x ∂mu :=
            integral_const_mul (μ := mu) (w a * priorScore w dw a)
              (fun x ↦ likelihoodScore p dp a x * p a x)
          _ = 0 := by rw [ha, mul_zero]
    _ = 0 := integral_zero ℝ ℝ

/-- For the affine contrast target, normalized prior and likelihood make the
integrated sensitivity equal the directional contrast. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:w,p,v,hprior,hnorm,hint), these specify the stated inputs. -/
lemma integral_sequentialSensitivity_eq {X : Type*} [MeasurableSpace X]
    {mu : Measure X} [SigmaFinite mu] {ell upper : ℝ}
    (w : ℝ → ℝ) (p : ℝ → X → ℝ) (v : TrialParameter)
    (hprior : ∫ a, w a ∂parameterMeasure ell upper = 1)
    (hnorm : ∀ᵐ a ∂parameterMeasure ell upper, ∫ x, p a x ∂mu = 1)
    (hint : Integrable (sensitivityField w p (vtTargetDeriv (X := X) v))
      ((parameterMeasure ell upper).prod mu)) :
    ∫ z, sensitivityField w p (vtTargetDeriv (X := X) v) z
        ∂((parameterMeasure ell upper).prod mu) = contrast v := by
  letI : IsFiniteMeasure (parameterMeasure ell upper) := by
    unfold parameterMeasure
    infer_instance
  rw [integral_prod _ hint]
  have hinner : (fun a => ∫ x, sensitivityField w p (vtTargetDeriv (X := X) v) (a,x) ∂mu)
      =ᵐ[parameterMeasure ell upper] fun a => contrast v * w a := by
    filter_upwards [hnorm] with a ha
    unfold sensitivityField vtTargetDeriv jointDensity
    calc
      ∫ x, contrast v * (w a * p a x) ∂mu =
          ∫ x, (contrast v * w a) * p a x ∂mu := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = (contrast v * w a) * ∫ x, p a x ∂mu :=
        integral_const_mul (μ := mu) (contrast v * w a) (fun x ↦ p a x)
      _ = contrast v * w a := by rw [ha, mul_one]
  rw [integral_congr_ae hinner]
  calc
    ∫ a, contrast v * w a ∂parameterMeasure ell upper =
        contrast v * ∫ a, w a ∂parameterMeasure ell upper :=
      integral_const_mul (μ := parameterMeasure ell upper) (contrast v) w
    _ = contrast v := by rw [hprior, mul_one]

/-- Under the usual zero-density derivative conditions, the derivative-balance
field is exactly error-score minus sensitivity. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:w,dw,p,dp,g,dg,T,hw,hp,hwzero,hpzero), these specify the stated inputs. -/
lemma derivativeBalanceField_eq_errorScore_sub_sensitivity {X : Type*}
    (w dw : ℝ → ℝ) (p dp g dg : ℝ → X → ℝ) (T : X → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hp : ∀ a x, 0 ≤ p a x)
    (hwzero : ∀ a, w a = 0 → dw a = 0)
    (hpzero : ∀ a x, p a x = 0 → dp a x = 0) :
    derivativeBalanceField w dw p dp g dg T =
      fun z => errorScoreField w dw p dp g T z - sensitivityField w p dg z := by
  funext z
  rw [errorScoreField_eq_numerator (hw z.1) (hp z.1 z.2)
    (hwzero z.1) (hpzero z.1 z.2)]
  unfold derivativeBalanceField sensitivityField jointDensity
  ring

/-- Prior and likelihood weighted square integrability implies integrability
of their weighted score cross term. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:w,dw,p,dp,mu,hw,hdw,hp,hdp,hw_nonneg,hp_nonneg,hprior,hfisher), these specify the stated inputs. -/
lemma integrable_priorLikelihoodCross_of_squares {X : Type*} [MeasurableSpace X]
    (w dw : ℝ → ℝ) (p dp : ℝ → X → ℝ) (mu : Measure (ℝ × X))
    (hw : Measurable w) (hdw : Measurable dw)
    (hp : Measurable (fun z : ℝ × X ↦ p z.1 z.2))
    (hdp : Measurable (fun z : ℝ × X ↦ dp z.1 z.2))
    (hw_nonneg : ∀ a, 0 ≤ w a) (hp_nonneg : ∀ a x, 0 ≤ p a x)
    (hprior : Integrable (fun z : ℝ × X ↦
      w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2) mu)
    (hfisher : Integrable (fun z : ℝ × X ↦
      w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2) mu) :
    Integrable (fun z : ℝ × X ↦
      w z.1 * p z.1 z.2 *
        (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2)) mu := by
  have hwj : Measurable (fun z : ℝ × X ↦ w z.1) := hw.comp measurable_fst
  have hdwj : Measurable (fun z : ℝ × X ↦ dw z.1) := hdw.comp measurable_fst
  have hpriorScore : Measurable (fun z : ℝ × X ↦ priorScore w dw z.1) := by
    unfold priorScore
    exact Measurable.ite (measurableSet_lt measurable_const hwj)
      (hdwj.div hwj) measurable_const
  have hlikeScore : Measurable
      (fun z : ℝ × X ↦ likelihoodScore p dp z.1 z.2) := by
    unfold likelihoodScore
    exact Measurable.ite (measurableSet_lt measurable_const hp)
      (hdp.div hp) measurable_const
  have h := integrable_mul_mul_of_integrable_sq_mul
    (fun z : ℝ × X ↦ priorScore w dw z.1)
    (fun z : ℝ × X ↦ likelihoodScore p dp z.1 z.2)
    (jointDensity w p) mu hpriorScore hlikeScore (hwj.mul hp)
    (fun z ↦ mul_nonneg (hw_nonneg z.1) (hp_nonneg z.1 z.2))
    (by
      apply hprior.congr
      filter_upwards with z
      unfold jointDensity
      ring)
    (by
      apply hfisher.congr
      filter_upwards with z
      unfold jointDensity
      ring)
  convert h using 1
  funext z
  unfold jointDensity
  ring

/-- Once the error-score and sensitivity fields are integrable, their exact
balance identity supplies derivative-balance integrability. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:w,dw,p,dp,g,dg,T,mu,hw,hp,hwzero,hpzero,herr,hsens), these specify the stated inputs. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma integrable_derivativeBalance_of_rewrite {X : Type*}
    [MeasurableSpace X] (w dw : ℝ → ℝ)
    (p dp g dg : ℝ → X → ℝ) (T : X → ℝ) (mu : Measure (ℝ × X))
    (hw : ∀ a, 0 ≤ w a) (hp : ∀ a x, 0 ≤ p a x)
    (hwzero : ∀ a, w a = 0 → dw a = 0)
    (hpzero : ∀ a x, p a x = 0 → dp a x = 0)
    (herr : Integrable (errorScoreField w dw p dp g T) mu)
    (hsens : Integrable (sensitivityField w p dg) mu) :
    Integrable (derivativeBalanceField w dw p dp g dg T) mu := by
  rw [derivativeBalanceField_eq_errorScore_sub_sensitivity
    w dw p dp g dg T hw hp hwzero hpzero]
  exact herr.sub hsens

end CausalSmith.Stat.LdpAteEfficiencySurface
