module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ObservableOdds
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Native-logit Hölder control of the observable cells

The quarter-Lipschitz logistic map transports the model's native Hölder radii
to propensity and arm risks. On the unit covariate interval, the smoother
propensity exponent can be lowered to the prognosis exponent. Product bounds
then give the unit Hölder radii of both off-diagonal cells used in the bias proof.
-/
public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The logistic derivative is globally bounded by one quarter. [the stated conclusion](goal) holds. -/
-- @node: logistic_sub_le_quarter
lemma logistic_sub_le_quarter (s t : ℝ) :
    |logistic s - logistic t| ≤ (1/4 : ℝ) * |s-t| := by
  have hbound (x : ℝ) : ‖deriv Real.sigmoid x‖ ≤ (1/4 : ℝ) := by
    rw [Real.deriv_sigmoid, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sigmoid_pos x).le
        (sub_nonneg.mpr (Real.sigmoid_le_one x)))]
    nlinarith [sq_nonneg (Real.sigmoid x - 1/2)]
  simpa only [logistic, Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => (Real.hasDerivAt_sigmoid x).differentiableAt)
      (fun x _ => hbound x) (Set.mem_univ t) (Set.mem_univ s)

/-- A finite extended Hölder radius gives its pointwise real modulus. Under the stated assumptions. [The stated hypotheses](hyp:hL,h) hold, and [the stated conclusion follows](goal). -/
-- @node: holderSeminorm_pointwise
lemma holderSeminorm_pointwise (γ L : ℝ) (f : Covariate → ℝ)
    (hL : 0 ≤ L) (h : holderSeminorm γ f ≤ ENNReal.ofReal L)
    (x z : Covariate) : |f x-f z| ≤ L * |(x : ℝ)-(z : ℝ)|^γ := by
  by_cases hxz : x = z
  · subst z
    simp
    positivity
  have hd : 0 < |(x : ℝ)-(z : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr
    (fun he => hxz (Subtype.ext he)))
  unfold holderSeminorm at h
  have hratio : ENNReal.ofReal (|f x-f z| / |(x : ℝ)-(z : ℝ)|^γ) ≤
      ENNReal.ofReal L :=
    (le_iSup_of_le x (le_iSup_of_le z
      (le_iSup_of_le (f := fun (_ : x ≠ z) =>
        ENNReal.ofReal (|f x-f z| / |(x : ℝ)-(z : ℝ)|^γ)) hxz le_rfl))).trans h
  have hr : |f x-f z| / |(x : ℝ)-(z : ℝ)|^γ ≤ L :=
    (ENNReal.ofReal_le_ofReal_iff hL).mp hratio
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hd _)).mp hr

/-- A pointwise modulus bounds the extended Hölder seminorm. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:h) hold, and [the stated conclusion follows](goal). -/
-- @node: holderSeminorm_le_of_pointwise
lemma holderSeminorm_le_of_pointwise (γ L : ℝ) (f : Covariate → ℝ)
    (h : ∀ x z : Covariate, |f x-f z| ≤ L * |(x : ℝ)-(z : ℝ)|^γ) :
    holderSeminorm γ f ≤ ENNReal.ofReal L := by
  refine iSup_le fun x => iSup_le fun z => iSup_le fun hxz => ?_
  apply ENNReal.ofReal_le_ofReal
  have hd : 0 < |(x : ℝ)-(z : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr
    (fun he => hxz (Subtype.ext he)))
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hd _)).mpr (h x z)

/-- [Hölder powers decrease with the exponent on the unit covariate interval.](goal) Under [the stated assumptions](hyp:x,hβα,hβ). -/
-- @node: covariate_rpow_exponent_mono
lemma covariate_rpow_exponent_mono (x z : Covariate) (α β : ℝ) (hβα : β ≤ α) (hβ : 0 < β) :
    |(x : ℝ)-(z : ℝ)|^α ≤ |(x : ℝ)-(z : ℝ)|^β := by
  have hd : |(x : ℝ)-(z : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [x.property.1, x.property.2, z.property.1, z.property.2]
  by_cases hz : |(x : ℝ)-(z : ℝ)| = 0
  · rw [hz, Real.zero_rpow (ne_of_gt (hβ.trans_le hβα)), Real.zero_rpow hβ.ne']
  · exact Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)) hd hβα

/-- [Native propensity regularity is transported through the logistic map.](goal) Under [the stated assumptions](hyp:h,x). -/
-- @node: propensity_holder_modulus
lemma propensity_holder_modulus (P : ObservedLaw) (α : ℝ)
    (h : PropensityHolder α P) (x z : Covariate) :
    |propensity P x-propensity P z| ≤ (1/2 : ℝ)*|(x : ℝ)-(z : ℝ)|^α := by
  have hg := holderSeminorm_pointwise α 2 (propensityLogit P) (by norm_num)
    (by simpa [PropensityHolder] using h) x z
  have he (v : Covariate) : logistic (propensityLogit P v) = propensity P v :=
    logistic_logit _ (propensity_interior P v).1 (propensity_interior P v).2
  have hl := logistic_sub_le_quarter (propensityLogit P x) (propensityLogit P z)
  rw [he x, he z] at hl
  linarith

/-- [Both arm risks inherit the same prognosis Hölder modulus; the effect is constant.](goal) Under [the stated assumptions](hyp:h,hh,x). -/
-- @node: armRisk_holder_modulus
lemma armRisk_holder_modulus (P : ObservedLaw) (β : ℝ)
    (h : PrognosisHolder β P) (hh : HomogeneousLogit P) (a : Bool)
    (x z : Covariate) :
    |armRisk P a x-armRisk P a z| ≤ (1/2 : ℝ)*|(x : ℝ)-(z : ℝ)|^β := by
  have hn := holderSeminorm_pointwise β 2 (prognosisLogit P) (by norm_num)
    (by simpa [PrognosisHolder] using h) x z
  cases a
  · have he (v : Covariate) : logistic (prognosisLogit P v) = armRisk P false v :=
      logistic_logit _ (armRisk_interior P false v).1 (armRisk_interior P false v).2
    have hl := logistic_sub_le_quarter (prognosisLogit P x) (prognosisLogit P z)
    rw [he x, he z] at hl
    linarith
  · rw [hh x, hh z]
    have hl := logistic_sub_le_quarter (prognosisLogit P x+effect P)
      (prognosisLogit P z+effect P)
    simp only [add_sub_add_right_eq_sub] at hl
    linarith

/-- [Products of probability factors have the sum of their two moduli. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:ha,hd). -/
-- @node: probability_product_sub_le
lemma probability_product_sub_le (a b c d : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    |a*b-c*d| ≤ |b-d|+|a-c| := by
  calc
    |a*b-c*d| = |a*(b-d)+(a-c)*d| := by congr 1; ring
    _ ≤ |a*(b-d)|+|(a-c)*d| := abs_add_le _ _
    _ = |a| *|b-d|+|a-c| *|d| := by rw [abs_mul, abs_mul]
    _ ≤ |b-d|+|a-c| := by
      rw [abs_of_nonneg ha.1, abs_of_nonneg hd.1]
      nlinarith [mul_le_mul_of_nonneg_right ha.2 (abs_nonneg (b-d)),
        mul_le_mul_of_nonneg_left hd.2 (abs_nonneg (a-c))]

/-- Each off-diagonal cell has unit prognosis-exponent Hölder radius. Under the stated assumptions. [The stated hypotheses](hyp:hab,hP) hold, and [the stated conclusion follows](goal). -/
-- @node: offDiagonal_holder_bounds
lemma offDiagonal_holder_bounds (P : ObservedLaw) (α β : ℝ)
    (hab : ExponentDomain α β) (hP : Model α β P) :
    holderSeminorm β (cellProbability P true false) ≤ 1 ∧
    holderSeminorm β (cellProbability P false true) ≤ 1 := by
  have he (x z : Covariate) :
      |propensity P x-propensity P z| ≤ (1/2 : ℝ)*|(x : ℝ)-(z : ℝ)|^β :=
    (propensity_holder_modulus P α hP.propensity_holder x z).trans
      (mul_le_mul_of_nonneg_left (covariate_rpow_exponent_mono x z α β hab.2.2.1.le hab.1)
        (by norm_num))
  constructor
  all_goals
    apply le_trans (holderSeminorm_le_of_pointwise β 1 _ ?_) (by norm_num)
    intro x z
  · simp only [cellProbability, Bool.false_eq_true, ↓reduceIte]
    have h := probability_product_sub_le (propensity P x) (1-armRisk P true x)
      (propensity P z) (1-armRisk P true z)
      ⟨(propensity_interior P x).1.le, (propensity_interior P x).2.le⟩
      ⟨by linarith [(armRisk_interior P true z).2],
        by linarith [(armRisk_interior P true z).1]⟩
    have hr := armRisk_holder_modulus P β hP.prognosis_holder hP.homogeneous true x z
    have he' := he x z
    rw [show (1-armRisk P true x)-(1-armRisk P true z) =
      -(armRisk P true x-armRisk P true z) by ring, abs_neg] at h
    linarith
  · simp only [cellProbability, Bool.false_eq_true, ↓reduceIte]
    have h := probability_product_sub_le (1-propensity P x) (armRisk P false x)
      (1-propensity P z) (armRisk P false z)
      ⟨by linarith [(propensity_interior P x).2],
        by linarith [(propensity_interior P x).1]⟩
      ⟨(armRisk_interior P false z).1.le, (armRisk_interior P false z).2.le⟩
    have hr := armRisk_holder_modulus P β hP.prognosis_holder hP.homogeneous false x z
    have he' := he x z
    rw [show (1-propensity P x)-(1-propensity P z) =
      -(propensity P x-propensity P z) by ring, abs_neg] at h
    linarith

/-- [The homogeneous arm-risk gap is bounded by one quarter of the scalar effect.](goal) Under [the stated assumptions](hyp:hh,x). -/
-- @node: armRisk_gap_le_effect
lemma armRisk_gap_le_effect (P : ObservedLaw) (hh : HomogeneousLogit P)
    (x : Covariate) : |armRisk P true x-armRisk P false x| ≤ (1/4 : ℝ)*|effect P| := by
  have he : logistic (prognosisLogit P x) = armRisk P false x :=
    logistic_logit _ (armRisk_interior P false x).1 (armRisk_interior P false x).2
  have hl := logistic_sub_le_quarter (prognosisLogit P x+effect P) (prognosisLogit P x)
  rw [he, ← hh x] at hl
  simpa only [add_sub_cancel_left] using hl

/-- [The marginal outcome mean has the sharper nine-sixteenths Hölder radius.](goal) Under [the stated assumptions](hyp:hab,hP). -/
-- @node: marginalMean_holder_bound
lemma marginalMean_holder_bound (P : ObservedLaw) (α β : ℝ)
    (hab : ExponentDomain α β) (hP : Model α β P) :
    holderSeminorm β (marginalMean P) ≤ ENNReal.ofReal (9/16 : ℝ) := by
  apply holderSeminorm_le_of_pointwise
  intro x z
  let D := |(x : ℝ)-(z : ℝ)|^β
  have hD : 0 ≤ D := Real.rpow_nonneg (abs_nonneg _) _
  have he := (propensity_holder_modulus P α hP.propensity_holder x z).trans
    (mul_le_mul_of_nonneg_left (covariate_rpow_exponent_mono x z α β hab.2.2.1.le hab.1)
      (by norm_num))
  have h0 := armRisk_holder_modulus P β hP.prognosis_holder hP.homogeneous false x z
  have h1 := armRisk_holder_modulus P β hP.prognosis_holder hP.homogeneous true x z
  have hgap : |armRisk P true z-armRisk P false z| ≤ (1/8 : ℝ) :=
    (armRisk_gap_le_effect P hP.homogeneous z).trans
      (by linarith [show |effect P| ≤ (1/2 : ℝ) from hP.effect_envelope])
  have hep := propensity_interior P x
  have hdecomp : marginalMean P x-marginalMean P z =
      (1-propensity P x)*(armRisk P false x-armRisk P false z)+
      propensity P x*(armRisk P true x-armRisk P true z)+
      (propensity P x-propensity P z)*(armRisk P true z-armRisk P false z) := by
    unfold marginalMean
    ring
  rw [hdecomp]
  have htri := (abs_add_le
    ((1-propensity P x)*(armRisk P false x-armRisk P false z)+
      propensity P x*(armRisk P true x-armRisk P true z))
    ((propensity P x-propensity P z)*(armRisk P true z-armRisk P false z))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  simp only [abs_mul, abs_of_nonneg (by linarith [hep.2] : 0 ≤ 1-propensity P x),
    abs_of_nonneg hep.1.le] at htri
  have hb0 := mul_le_mul_of_nonneg_left h0 (by linarith [hep.2] : 0 ≤ 1-propensity P x)
  have hb1 := mul_le_mul_of_nonneg_left h1 hep.1.le
  have hb2 := mul_le_mul he hgap (abs_nonneg _) (by positivity : 0 ≤ (1/2 : ℝ)*D)
  change |(1-propensity P x)*(armRisk P false x-armRisk P false z)+
      propensity P x*(armRisk P true x-armRisk P true z)+
      (propensity P x-propensity P z)*(armRisk P true z-armRisk P false z)| ≤ (9/16 : ℝ)*D
  change (1-propensity P x)*|armRisk P false x-armRisk P false z| ≤
    (1-propensity P x)*((1/2 : ℝ)*D) at hb0
  change propensity P x*|armRisk P true x-armRisk P true z| ≤
    propensity P x*((1/2 : ℝ)*D) at hb1
  change |propensity P x-propensity P z| *|armRisk P true z-armRisk P false z| ≤
    ((1/2 : ℝ)*D)*(1/8) at hb2
  nlinarith

end CausalSmith.Stat.LogoddsLowsmoothFrontier
