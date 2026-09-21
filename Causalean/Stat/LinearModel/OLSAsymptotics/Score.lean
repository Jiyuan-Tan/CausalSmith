/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.LinearModel.OLSAsymptotics.ScoreMomentConditions

/-! # Smooth-score regularity for heteroskedastic OLS

This module verifies the smooth Z-estimator assumptions for the linear OLS
score.  The observationwise derivative is `h ↦ -x(x′h)`, so its Lipschitz
envelope is identically zero.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {X K : Type*} [MeasurableSpace X] [Fintype K] [DecidableEq K]
  {P : Measure X}

/-- For [a regressor](hyp:x), [an outcome](hyp:y), [a coefficient](hyp:b),
and [an observation](hyp:z), the [OLS score has derivative `h ↦ -x(x′h)` at
that coefficient](goal). -/
@[fun_prop]
theorem hasFDerivAt_olsScore (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (b : EuclideanSpace ℝ K) (z : X) :
    HasFDerivAt (fun c => olsScore x y c z) (olsScoreDerivative x z) b := by
  have hlin : HasFDerivAt (olsRegressorFunctional x z)
      (olsRegressorFunctional x z) b :=
    (olsRegressorFunctional x z).hasFDerivAt
  have h := (hlin.const_sub (y z)).smul_const (x z)
  simpa [olsScore, olsResidual, olsScoreDerivative, olsRegressorFunctional,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using h

/-- For [a population law](hyp:P), [a regressor and outcome](hyp:x,y), and
[integrable OLS raw moments through degree four](hyp:hraw), [each chosen Gram
entry](hyp:i,j) [equals the expectation of the corresponding regressor
product](goal). -/
theorem olsQ_apply_eq_integral
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hraw : Integrable (olsRawMoment x y) P) (i j : K) :
    olsQ P x y i j = ∫ z, x z i * x z j ∂P := by
  have heval := (ContinuousLinearMap.proj
    (olsMomentIndex (some (some i)) (some (some j)) none none) :
      OLSMoment K →L[ℝ] ℝ).integral_comp_comm hraw
  rw [olsQ, olsQFromMoments, olsPopulationMoments]
  calc
    _ = ∫ z, olsRawMoment x y z
        (olsMomentIndex (some (some i)) (some (some j)) none none) ∂P := by
          simpa using heval.symm
    _ = _ := by
      simp [olsRawMoment, Fin.prod_univ_four, olsMomentIndex, olsAugmented]

private theorem olsR_apply_eq_integral
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hraw : Integrable (olsRawMoment x y) P) (i : K) :
    olsRFromMoments (olsPopulationMoments P x y) i =
      ∫ z, x z i * y z ∂P := by
  have heval := (ContinuousLinearMap.proj
    (olsMomentIndex (some (some i)) (some none) none none) :
      OLSMoment K →L[ℝ] ℝ).integral_comp_comm hraw
  rw [olsRFromMoments, olsPopulationMoments]
  calc
    _ = ∫ z, olsRawMoment x y z
        (olsMomentIndex (some (some i)) (some none) none none) ∂P := by
          simpa using heval.symm
    _ = _ := by
      simp [olsRawMoment, Fin.prod_univ_four, olsMomentIndex, olsAugmented]

private theorem integrable_olsQCoordinate
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hraw : Integrable (olsRawMoment x y) P) (i j : K) :
    Integrable (fun z => x z i * x z j) P := by
  have h := (ContinuousLinearMap.proj
    (olsMomentIndex (some (some i)) (some (some j)) none none) :
      OLSMoment K →L[ℝ] ℝ).integrable_comp hraw
  simpa [olsRawMoment, Fin.prod_univ_four, olsMomentIndex, olsAugmented] using h

private theorem integrable_olsRCoordinate
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hraw : Integrable (olsRawMoment x y) P) (i : K) :
    Integrable (fun z => x z i * y z) P := by
  have h := (ContinuousLinearMap.proj
    (olsMomentIndex (some (some i)) (some none) none none) :
      OLSMoment K →L[ℝ] ℝ).integrable_comp hraw
  simpa [olsRawMoment, Fin.prod_univ_four, olsMomentIndex, olsAugmented] using h

private theorem integrable_olsRawMomentCoordinate
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hraw : Integrable (olsRawMoment x y) P) (a : OLSMomentIndex K) :
    Integrable (fun z => olsRawMoment x y z a) P :=
  (ContinuousLinearMap.proj a : OLSMoment K →L[ℝ] ℝ).integrable_comp hraw

private theorem integrable_olsScoreCoordinateSq
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hraw : Integrable (olsRawMoment x y) P)
    (b : EuclideanSpace ℝ K) (i : K) :
    Integrable (fun z => (olsScore x y b z i) ^ 2) P := by
  let ayy := olsMomentIndex (some (some i)) (some (some i))
    (some none) (some none)
  let ayx := fun l => olsMomentIndex (some (some i)) (some (some i))
    (some none) (some (some l))
  let axx := fun l m => olsMomentIndex (some (some i)) (some (some i))
    (some (some l)) (some (some m))
  have hiyy := integrable_olsRawMomentCoordinate hraw ayy
  have hiyx : ∀ l, Integrable (fun z => olsRawMoment x y z (ayx l)) P :=
    fun l => integrable_olsRawMomentCoordinate hraw (ayx l)
  have hixx : ∀ l m, Integrable (fun z => olsRawMoment x y z (axx l m)) P :=
    fun l m => integrable_olsRawMomentCoordinate hraw (axx l m)
  have hpoly : Integrable (fun z =>
      olsRawMoment x y z ayy -
        2 * ∑ l, b l * olsRawMoment x y z (ayx l) +
        ∑ l, ∑ m, b l * b m * olsRawMoment x y z (axx l m)) P := by
    exact (hiyy.sub
      ((integrable_finsetSum _ fun l _ => (hiyx l).const_mul (b l)).const_mul 2)).add
        (integrable_finsetSum _ fun l _ =>
          integrable_finsetSum _ fun m _ => (hixx l m).const_mul (b l * b m))
  convert hpoly using 1
  funext z
  simp [ayy, ayx, axx, olsScore, olsResidual, olsRawMoment,
    Fin.prod_univ_four, olsMomentIndex, olsAugmented]
  rw [show (∑ l, b l * (x z i * x z i * y z * x z l)) =
      x z i * x z i * y z * ∑ l, x z l * b l by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring]
  rw [show (∑ l, ∑ m, b l * b m * (x z i * x z i * x z l * x z m)) =
      x z i * x z i * (∑ l, x z l * b l) ^ 2 by
    calc
      _ = ∑ l, (x z i * x z i * (x z l * b l)) *
            ∑ m, x z m * b m := by
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
      _ = (x z i * x z i) * (∑ l, x z l * b l) *
            (∑ m, x z m * b m) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [pow_two]; ring]
  ring

/-- For [a population law](hyp:P), [a regressor and outcome](hyp:x,y),
[integrable OLS raw moments through degree four](hyp:hraw), and [a fixed
coefficient](hyp:b), [the squared norm of the OLS score is integrable](goal). -/
@[fun_prop]
theorem integrable_sq_olsScore
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hraw : Integrable (olsRawMoment x y) P)
    (b : EuclideanSpace ℝ K) :
    Integrable (fun z => ‖olsScore x y b z‖ ^ 2) P := by
  rw [show (fun z => ‖olsScore x y b z‖ ^ 2) =
      fun z => ∑ i, (olsScore x y b z i) ^ 2 by
    funext z
    exact EuclideanSpace.real_norm_sq_eq _]
  exact integrable_finsetSum _ fun i _ => integrable_olsScoreCoordinateSq hraw b i

/-- For [a population law](hyp:P), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [integrable OLS raw moments through degree
four](hyp:hraw), and [a fixed coefficient](hyp:b), [the OLS score is
integrable](goal). -/
@[fun_prop]
theorem integrable_olsScore_of_rawMoment
    [IsFiniteMeasure P]
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (b : EuclideanSpace ℝ K) : Integrable (olsScore x y b) P := by
  have hmem : MemLp (olsScore x y b) 2 P :=
    (memLp_two_iff_integrable_sq_norm
      (measurable_olsScore hx hy b).aestronglyMeasurable).2
        (integrable_sq_olsScore hraw b)
  exact hmem.integrable (by norm_num)

/-- For [a population law](hyp:P), [measurable regressors](hyp:hx), and
[integrable OLS raw moments through degree four](hyp:hraw), [the
observationwise OLS score derivative is integrable](goal). -/
@[fun_prop]
theorem integrable_olsScoreDerivative_of_rawMoment
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hraw : Integrable (olsRawMoment x y) P) :
    Integrable (olsScoreDerivative x) P := by
  have hnormsq : Integrable (fun z => ‖x z‖ ^ 2) P := by
    rw [show (fun z => ‖x z‖ ^ 2) = fun z => ∑ i, x z i * x z i by
      funext z
      rw [EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    exact integrable_finsetSum _ fun i _ => integrable_olsQCoordinate hraw i i
  apply hnormsq.mono' (measurable_olsScoreDerivative hx).aestronglyMeasurable
  filter_upwards with z
  simp [olsScoreDerivative, olsRegressorFunctional,
    ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  rw [pow_two]

/-- Under [a finite population law](hyp:P), [measurable regressors](hyp:hx),
[a measurable outcome](hyp:hy), and [uniform regressor and outcome
bounds](hyp:hx_bdd,hy_bdd), the [OLS score at any fixed coefficient is
integrable](goal). -/
@[fun_prop]
theorem integrable_olsScore [IsFiniteMeasure P]
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hx_bdd : ∃ C, ∀ z, ‖x z‖ ≤ C)
    (hy_bdd : ∃ C, ∀ z, |y z| ≤ C)
    (b : EuclideanSpace ℝ K) : Integrable (olsScore x y b) P := by
  have hmem : MemLp (olsScore x y b) 2 P :=
    (memLp_two_iff_integrable_sq_norm
      (measurable_olsScore hx hy b).aestronglyMeasurable).2
        (integrable_sq_olsScore_of_bounded hx hy hx_bdd hy_bdd b)
  exact hmem.integrable (by norm_num)

/-- Under [a probability population law](hyp:P), [measurable
regressors](hyp:hx), [a measurable outcome](hyp:hy), [integrable OLS raw
moments through degree four](hyp:hraw), and [a positive-definite design second
moment](hyp:hQ), the [population OLS score at the projection coefficient has
mean zero](goal). -/
theorem integral_olsScore_olsBeta [IsProbabilityMeasure P]
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) :
    ∫ z, olsScore x y (olsBeta P x y) z ∂P = 0 := by
  have hscore := integrable_olsScore_of_rawMoment hx hy hraw (olsBeta P x y)
  have hdet : IsUnit (olsQ P x y).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hQ.isUnit
  have hmul : olsQ P x y * (olsQ P x y)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  ext i
  have hproj := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hscore
  change (∫ z, olsScore x y (olsBeta P x y) z ∂P) i = 0
  rw [show (∫ z, olsScore x y (olsBeta P x y) z ∂P) i =
      ∫ z, olsScore x y (olsBeta P x y) z i ∂P by simpa using hproj.symm]
  have hfun : (fun z => olsScore x y (olsBeta P x y) z i) =
      fun z => x z i * y z - ∑ j, (olsBeta P x y) j * (x z i * x z j) := by
    funext z
    simp only [olsScore, olsResidual]
    change (y z - ∑ j, x z j * (olsBeta P x y) j) * x z i =
      x z i * y z - ∑ j, (olsBeta P x y) j * (x z i * x z j)
    have hdist : (∑ j, x z j * (olsBeta P x y) j) * x z i =
        ∑ j, (x z j * (olsBeta P x y) j) * x z i := by
      exact map_sum (AddMonoidHom.mulRight (x z i)) _ Finset.univ
    rw [sub_mul, hdist]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  rw [hfun, integral_sub (integrable_olsRCoordinate hraw i)
    (integrable_finsetSum _ fun j _ =>
      (integrable_olsQCoordinate hraw i j).const_mul ((olsBeta P x y) j))]
  rw [integral_finset_sum Finset.univ (fun j _ =>
    (integrable_olsQCoordinate hraw i j).const_mul ((olsBeta P x y) j))]
  simp_rw [integral_const_mul]
  rw [← olsR_apply_eq_integral hraw i]
  simp_rw [← olsQ_apply_eq_integral hraw i]
  have hvec : olsQ P x y *ᵥ (olsBeta P x y).ofLp =
      olsRFromMoments (olsPopulationMoments P x y) := by
    rw [olsBeta, olsBetaFromMoments, Matrix.toEuclideanLin_apply]
    simp only [WithLp.ofLp_toLp]
    change olsQ P x y *ᵥ ((olsQ P x y)⁻¹ *ᵥ
      olsRFromMoments (olsPopulationMoments P x y)) = _
    rw [Matrix.mulVec_mulVec, hmul]
    simp
  have hi := congrFun hvec i
  simp only [Matrix.mulVec, dotProduct] at hi
  rw [sub_eq_zero]
  simpa [mul_comm] using hi.symm

/-- Under [a finite population law](hyp:P), [measurable regressors](hyp:hx),
and with [the outcome included in integrable OLS raw moments through degree
four](hyp:y,hraw), the [expected OLS score derivative is the negative
linear operator induced by `Q = E[xx′]`](goal). -/
theorem integral_olsScoreDerivative [IsFiniteMeasure P]
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hraw : Integrable (olsRawMoment x y) P) :
    ∫ z, olsScoreDerivative x z ∂P =
      -((olsQ P x y).toEuclideanLin.toContinuousLinearMap) := by
  have hderiv := integrable_olsScoreDerivative_of_rawMoment hx hraw
  ext h i
  have happ := (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ K) h)
    |>.integral_comp_comm hderiv
  have hdh : Integrable (fun z => olsScoreDerivative x z h) P :=
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ K) h).integrable_comp hderiv
  have hcoord := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hdh
  change ((∫ z, olsScoreDerivative x z ∂P) h) i =
    -((olsQ P x y).toEuclideanLin.toContinuousLinearMap h) i
  rw [show ((∫ z, olsScoreDerivative x z ∂P) h) i =
      ∫ z, (olsScoreDerivative x z h) i ∂P by
        have happi := congrArg (fun v : EuclideanSpace ℝ K => v i) happ
        exact happi.symm.trans (by simpa using hcoord.symm)]
  have hfun : (fun z => (olsScoreDerivative x z h) i) =
      fun z => -∑ j, h j * (x z i * x z j) := by
    funext z
    simp only [olsScoreDerivative, olsRegressorFunctional,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.neg_apply,
      neg_smul, PiLp.neg_apply, PiLp.smul_apply,
      innerSL_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      starRingEnd_apply, star_id_of_comm, smul_eq_mul]
    apply congrArg Neg.neg
    have hdist : (∑ j, h j * x z j) * x z i =
        ∑ j, (h j * x z j) * x z i := by
      exact map_sum (AddMonoidHom.mulRight (x z i)) _ Finset.univ
    rw [hdist]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfun, integral_neg]
  rw [integral_finset_sum Finset.univ (fun j _ =>
    (integrable_olsQCoordinate hraw i j).const_mul (h j))]
  simp_rw [integral_const_mul, ← olsQ_apply_eq_integral hraw i]
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, mul_comm]

private theorem olsPopulationMoment_apply_eq_integral
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hraw : Integrable (olsRawMoment x y) P) (a : OLSMomentIndex K) :
    olsPopulationMoments P x y a = ∫ z, olsRawMoment x y z a ∂P := by
  have h := (ContinuousLinearMap.proj a : OLSMoment K →L[ℝ] ℝ)
    |>.integral_comp_comm hraw
  simpa [olsPopulationMoments] using h.symm

/-- Under [a finite population law](hyp:P), for [a regressor and
outcome](hyp:x,y) with [integrable OLS raw moments through degree
four](hyp:hraw), [the `(i,j)` entry of the heteroskedastic score second-moment matrix is
the expectation `E[xᵢxⱼe²]`](goal), for [the chosen coordinates](hyp:i,j). -/
theorem olsOmega_apply_eq_integral [IsFiniteMeasure P]
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hraw : Integrable (olsRawMoment x y) P) (i j : K) :
    olsOmega P x y i j = ∫ z, x z i * x z j *
      olsResidual x y (olsBeta P x y) z ^ 2 ∂P := by
  let b := olsBeta P x y
  let ayy := olsMomentIndex (some (some i)) (some (some j))
    (some none) (some none)
  let ayx := fun l => olsMomentIndex (some (some i)) (some (some j))
    (some none) (some (some l))
  let axx := fun l m => olsMomentIndex (some (some i)) (some (some j))
    (some (some l)) (some (some m))
  have hiyy := integrable_olsRawMomentCoordinate hraw ayy
  have hiyx : ∀ l, Integrable (fun z => olsRawMoment x y z (ayx l)) P :=
    fun l => integrable_olsRawMomentCoordinate hraw (ayx l)
  have hixx : ∀ l m, Integrable (fun z => olsRawMoment x y z (axx l m)) P :=
    fun l m => integrable_olsRawMomentCoordinate hraw (axx l m)
  rw [olsOmega, olsMeatFromMoments]
  change olsPopulationMoments P x y ayy -
      2 * ∑ l, b l * olsPopulationMoments P x y (ayx l) +
      ∑ l, ∑ m, b l * b m * olsPopulationMoments P x y (axx l m) = _
  rw [olsPopulationMoment_apply_eq_integral hraw ayy]
  simp_rw [olsPopulationMoment_apply_eq_integral hraw]
  simp_rw [← integral_const_mul]
  rw [← integral_finset_sum Finset.univ
    (fun l _ => (hiyx l).const_mul (b l))]
  have hinner (l : K) :
      (∑ m, ∫ z, b l * b m * olsRawMoment x y z (axx l m) ∂P) =
      ∫ z, ∑ m, b l * b m * olsRawMoment x y z (axx l m) ∂P :=
    (integral_finset_sum Finset.univ
      (fun m _ => (hixx l m).const_mul (b l * b m))).symm
  simp_rw [hinner]
  rw [← integral_finset_sum Finset.univ (fun l _ =>
    integrable_finsetSum _ fun m _ => (hixx l m).const_mul (b l * b m))]
  rw [← integral_const_mul]
  rw [← integral_sub hiyy
    ((integrable_finsetSum _ fun l _ => (hiyx l).const_mul (b l)).const_mul 2)]
  rw [← integral_add]
  · apply integral_congr_ae
    filter_upwards with z
    simp [ayy, ayx, axx, b, olsRawMoment, Fin.prod_univ_four,
      olsMomentIndex, olsAugmented, olsResidual]
    rw [show (∑ l, (olsBeta P x y) l * (x z i * x z j * y z * x z l)) =
        x z i * x z j * y z * ∑ l, x z l * (olsBeta P x y) l by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring]
    rw [show (∑ l, ∑ m, (olsBeta P x y) l * (olsBeta P x y) m *
        (x z i * x z j * x z l * x z m)) =
        x z i * x z j * (∑ l, x z l * (olsBeta P x y) l) ^ 2 by
      calc
        _ = ∑ l, (x z i * x z j * (x z l * (olsBeta P x y) l)) *
              ∑ m, x z m * (olsBeta P x y) m := by
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m _
            ring
        _ = (x z i * x z j) * (∑ l, x z l * (olsBeta P x y) l) *
              (∑ m, x z m * (olsBeta P x y) m) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            ring
        _ = _ := by rw [pow_two]; ring]
    ring
  · exact hiyy.sub
      ((integrable_finsetSum _ fun l _ => (hiyx l).const_mul (b l)).const_mul 2)
  · exact integrable_finsetSum _ fun l _ =>
      integrable_finsetSum _ fun m _ => (hixx l m).const_mul (b l * b m)

/-- Under [a probability population law](hyp:P), [measurable
regressors](hyp:hx), [a measurable outcome](hyp:hy), [integrable OLS raw
moments through degree four](hyp:hraw), and [a positive-definite design second
moment](hyp:hQ), [the `(i,j)` second moment of the OLS influence function equals the
corresponding entry of `Q⁻¹ΩQ⁻¹`](goal), for [the chosen coordinates](hyp:i,j). -/
theorem olsInfluence_secondMoment [IsProbabilityMeasure P]
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (i j : K) :
    ∫ z, olsInfluence P x y z i * olsInfluence P x y z j ∂P =
      olsAsymptoticCovariance P x y i j := by
  let s := olsScore x y (olsBeta P x y)
  have hsmeas : Measurable s := measurable_olsScore hx hy _
  have hsquare := integrable_sq_olsScore hraw (olsBeta P x y)
  have hab : ∀ a b : K, Integrable (fun z => s z a * s z b) P := by
    intro a b
    apply hsquare.mono'
    · have hma := (PiLp.continuous_apply (2 : ℝ≥0∞)
          (fun _ : K => ℝ) a).measurable.comp hsmeas
      have hmb := (PiLp.continuous_apply (2 : ℝ≥0∞)
          (fun _ : K => ℝ) b).measurable.comp hsmeas
      exact (hma.mul hmb).aestronglyMeasurable
    · filter_upwards with z
      change ‖s z a * s z b‖ ≤ ‖s z‖ ^ 2
      rw [Real.norm_eq_abs, abs_mul, pow_two]
      have ha := PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (s z) a
      have hb := PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (s z) b
      exact mul_le_mul ha hb (by positivity) (norm_nonneg _)
  have homega : ∀ a b : K,
      ∫ z, s z a * s z b ∂P = olsOmega P x y a b := by
    intro a b
    rw [olsOmega_apply_eq_integral hraw]
    apply integral_congr_ae
    filter_upwards with z
    simp [s, olsScore]
    ring
  change ∫ z, (∑ a, (olsQ P x y)⁻¹ i a * s z a) *
      (∑ b, (olsQ P x y)⁻¹ j b * s z b) ∂P = _
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [show (fun z => ∑ a, ∑ b,
      (olsQ P x y)⁻¹ i a * s z a * ((olsQ P x y)⁻¹ j b * s z b)) =
      (fun z => ∑ a, ∑ b,
        ((olsQ P x y)⁻¹ i a * (olsQ P x y)⁻¹ j b) *
          (s z a * s z b)) by
    funext z
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring]
  rw [integral_finset_sum Finset.univ (fun a _ =>
    integrable_finsetSum _ fun b _ => (hab a b).const_mul
      ((olsQ P x y)⁻¹ i a * (olsQ P x y)⁻¹ j b))]
  simp_rw [integral_finset_sum Finset.univ
    (fun b _ => hab _ b |>.const_mul _)]
  simp_rw [integral_const_mul, homega]
  rw [olsAsymptoticCovariance]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  have hsymm : (olsQ P x y)⁻¹ j b = (olsQ P x y)⁻¹ b j := by
    have hherm := hQ.inv.isHermitian.apply b j
    simpa using hherm
  rw [hsymm]
  ring

/-- Given [a population law](hyp:P), [regressors](hyp:x), and [an
outcome](hyp:y), the [inverse OLS score Jacobian](goal) is the negative of the
linear operator induced by `Q⁻¹`. -/
def olsJacobianInverse (P : Measure X) (x : X → EuclideanSpace ℝ K)
    (y : X → ℝ) : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K :=
  -((olsQ P x y)⁻¹.toEuclideanLin.toContinuousLinearMap)

/-- Under [a probability population law](hyp:P), [measurable
regressors](hyp:hx), [a measurable outcome](hyp:hy), [integrable OLS raw
moments through degree four](hyp:hraw), and [a positive-definite population design
moment](hyp:hQ), the [linear OLS score satisfies the complete smooth
Z-estimator regularity package at the projection coefficient](goal). -/
def olsSmoothZRegularity [IsProbabilityMeasure P]
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) :
    SmoothZEstimatorRegularity (olsScore x y) (olsBeta P x y) P where
  identification := integral_olsScore_olsBeta hx hy hraw hQ
  score_meas := measurable_olsScore hx hy _
  score_finite_var := integrable_sq_olsScore hraw _
  deriv := fun _ => olsScoreDerivative x
  hasFDeriv := fun θ z => hasFDerivAt_olsScore x y θ z
  deriv_at_target_meas := measurable_olsScoreDerivative hx
  deriv_at_target_integrable := integrable_olsScoreDerivative_of_rawMoment hx hraw
  deriv_lipschitz := by
    -- The OLS score is linear in the parameter, so its derivative does not depend on `θ`
    -- at all: the zero envelope works, on a ball of any radius.
    refine ⟨1, zero_lt_one, fun _ => 0, measurable_const,
      MeasureTheory.integrable_zero X ℝ P,
      fun _ => le_rfl, ?_⟩
    intro θ _ θ' _ z
    simp
  jacobianInv := olsJacobianInverse P x y
  jacobian_inverse := by
    have hdet : IsUnit (olsQ P x y).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hQ.isUnit
    have hmul : olsQ P x y * (olsQ P x y)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hdet
    rw [integral_olsScoreDerivative hx hraw]
    ext h i
    simp [olsJacobianInverse, Matrix.toEuclideanLin_apply,
      Matrix.mulVec_mulVec, hmul]

/-- Under [a probability population law](hyp:P), [measurable
regressors](hyp:hx), [a measurable outcome](hyp:hy), [integrable OLS raw
moments through degree four](hyp:hraw), and [a positive-definite population design
moment](hyp:hQ), the [smooth Z-estimator influence function is exactly the OLS
influence function `Q⁻¹x e`](goal). -/
theorem olsSmoothZRegularity_influence_eq [IsProbabilityMeasure P]
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) :
    (olsSmoothZRegularity hx hy hraw hQ).influence =
      olsInfluence P x y := by
  funext z
  simp [SmoothZEstimatorRegularity.influence, olsSmoothZRegularity,
    olsJacobianInverse, olsInfluence]

end

end Causalean.Stat
