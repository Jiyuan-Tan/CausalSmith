/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Minimax.LeCamTwoPoint
public import Causalean.Stat.Minimax.MinimaxRisk
public import Causalean.Stat.Sample.PiTransport

/-!
# Extended-valued squared risk and Le Cam lower bounds

This module provides the standard extended-expectation formulation of squared risk. Because
the risk is an `ℝ≥0∞` lintegral, nonintegrable estimators have infinite risk rather than the
zero value assigned by the Bochner integral. It gives a no-integrability Le Cam two-point MSE
bound and deterministic affine-transport lemmas for ordinary and finite-product experiments.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory

universe uX uY uI

variable {X : Type uX} {Y : Type uY} {Iota : Type uI}
  [MeasurableSpace X] [MeasurableSpace Y]

/-- Given [a measure on an observation space](hyp:law), [a real-valued estimator](hyp:est),
and [a real target](hyp:theta), the [extended squared risk](goal) is the `ℝ≥0∞` expectation of
the estimator's squared error. Nonintegrable loss therefore has infinite, rather than zero,
risk. -/
noncomputable def sqRiskLIntegral (law : Measure X) (est : X → ℝ) (theta : ℝ) : ENNReal :=
  ∫⁻ z, ENNReal.ofReal ((est z - theta) ^ 2) ∂law

/-- Given [a measure on an observation space](hyp:law), [a real-valued estimator](hyp:est),
and [a real target](hyp:theta), the [extended absolute-error risk](goal) is the `ℝ≥0∞`
expectation of the estimator's absolute error. -/
noncomputable def l1RiskLIntegral (law : Measure X) (est : X → ℝ) (theta : ℝ) : ENNReal :=
  ∫⁻ z, ENNReal.ofReal |est z - theta| ∂law

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- If [the affine slope is nonzero](hyp:ha), then at [each source point](hyp:z), [the
extended-valued squared-loss integrand after affine pullback, multiplied by the squared slope,
equals the target-space squared-loss integrand](goal). -/
lemma ofReal_affine_sqLoss_pullback_identity {phi : X → Y} {a b theta : ℝ}
    {targetEst : Y → ℝ} (ha : a ≠ 0) (z : X) :
    ENNReal.ofReal (a ^ 2) *
        ENNReal.ofReal ((affinePullbackEstimator phi a b targetEst z - theta) ^ 2) =
      ENNReal.ofReal ((targetEst (phi z) - (a * theta + b)) ^ 2) := by
  rw [← ENNReal.ofReal_mul (sq_nonneg a)]
  congr 1
  exact affine_sqLoss_pullback_identity ha z

/-- If [the affine slope is nonzero](hyp:ha), [the observation rule is measurable](hyp:hphi),
and [the target estimator is measurable](hyp:htarget), then [extended squared risk under the
pushforward law equals the source pullback risk multiplied by the squared slope](goal). -/
theorem sqRiskLIntegral_map_affinePullback {law : Measure X} {phi : X → Y}
    {a b theta : ℝ} {targetEst : Y → ℝ} (ha : a ≠ 0)
    (hphi : Measurable phi) (htarget : Measurable targetEst) :
    ENNReal.ofReal (a ^ 2) *
        sqRiskLIntegral law (affinePullbackEstimator phi a b targetEst) theta =
      sqRiskLIntegral (law.map phi) targetEst (a * theta + b) := by
  unfold sqRiskLIntegral
  rw [← lintegral_const_mul]
  · calc
      (∫⁻ z, ENNReal.ofReal (a ^ 2) *
          ENNReal.ofReal ((affinePullbackEstimator phi a b targetEst z - theta) ^ 2) ∂law) =
          ∫⁻ z, ENNReal.ofReal ((targetEst (phi z) - (a * theta + b)) ^ 2) ∂law := by
            apply lintegral_congr
            exact fun z => ofReal_affine_sqLoss_pullback_identity ha z
      _ = ∫⁻ y, ENNReal.ofReal ((targetEst y - (a * theta + b)) ^ 2) ∂law.map phi := by
            rw [lintegral_map (by fun_prop) hphi]
  · fun_prop

/-- Given [source and target law families](hyp:P,Q), [a target parameter](hyp:theta), [an
observation map](hyp:phi), [affine coefficients](hyp:a,b), and [a source lower
bound](hyp:L), suppose [the affine slope is nonzero](hyp:ha), [the observation rule is
measurable](hyp:hphi), and [each target law is the pushforward of its source law](hyp:hQ). If
[every measurable source estimator has extended squared risk at least the bound at some
parameter](hyp:hsource), then [every measurable target estimator has extended squared risk at
least `ofReal(a²) * L` at a transformed parameter](goal). -/
theorem forall_estimator_exists_sqRiskLIntegral_ge_of_deterministic_affine_transport
    (P : Iota → Measure X) (Q : Iota → Measure Y)
    (theta : Iota → ℝ) (phi : X → Y) (a b : ℝ) (L : ENNReal)
    (ha : a ≠ 0) (hphi : Measurable phi)
    (hQ : ∀ j, Q j = (P j).map phi)
    (hsource : ∀ sourceEst : X → ℝ, Measurable sourceEst →
      ∃ j, L ≤ sqRiskLIntegral (P j) sourceEst (theta j)) :
    ∀ targetEst : Y → ℝ, Measurable targetEst →
      ∃ j, ENNReal.ofReal (a ^ 2) * L ≤
        sqRiskLIntegral (Q j) targetEst (a * theta j + b) := by
  intro targetEst htarget
  obtain ⟨j, hj⟩ := hsource (affinePullbackEstimator phi a b targetEst)
    (measurable_affinePullbackEstimator hphi htarget)
  refine ⟨j, ?_⟩
  calc
    ENNReal.ofReal (a ^ 2) * L ≤ ENNReal.ofReal (a ^ 2) *
        sqRiskLIntegral (P j) (affinePullbackEstimator phi a b targetEst) (theta j) :=
      by gcongr
    _ = sqRiskLIntegral ((P j).map phi) targetEst (a * theta j + b) :=
      sqRiskLIntegral_map_affinePullback ha hphi htarget
    _ = sqRiskLIntegral (Q j) targetEst (a * theta j + b) := by rw [hQ j]

/-- Given [a product size](hyp:n), [source and target law families](hyp:P,Q), [a target
parameter](hyp:theta), [an observation map](hyp:phi), [affine coefficients](hyp:a,b), and [a
source lower bound](hyp:L), suppose [the affine slope is nonzero](hyp:ha), [the observation map
is measurable](hyp:hphi), and [the laws satisfy the pushforward identities](hyp:hQ). If [every
measurable estimator on the source product experiment obeys the lower bound](hyp:hsource), then
[the corresponding extended squared-risk bound holds for the coordinatewise transported product
experiment](goal). -/
theorem forall_estimator_exists_sqRiskLIntegral_ge_of_deterministic_affine_transport_pi
    (n : ℕ) (P : Iota → Measure X) (Q : Iota → Measure Y)
    [∀ j, IsProbabilityMeasure (P j)]
    (theta : Iota → ℝ) (phi : X → Y) (a b : ℝ) (L : ENNReal)
    (ha : a ≠ 0) (hphi : Measurable phi)
    (hQ : ∀ j, Q j = (P j).map phi)
    (hsource : ∀ sourceEst : (Fin n → X) → ℝ, Measurable sourceEst →
      ∃ j, L ≤ sqRiskLIntegral (Measure.pi (fun _ : Fin n => P j)) sourceEst (theta j)) :
    ∀ targetEst : (Fin n → Y) → ℝ, Measurable targetEst →
      ∃ j, ENNReal.ofReal (a ^ 2) * L ≤
        sqRiskLIntegral (Measure.pi (fun _ : Fin n => Q j))
          targetEst (a * theta j + b) := by
  apply forall_estimator_exists_sqRiskLIntegral_ge_of_deterministic_affine_transport
    (P := fun j => Measure.pi (fun _ : Fin n => P j))
    (Q := fun j => Measure.pi (fun _ : Fin n => Q j))
    (theta := theta) (phi := fun z i => phi (z i))
    (a := a) (b := b) (L := L) ha (measurable_finCoordinatewise n hphi) ?_ hsource
  intro j
  calc
    Measure.pi (fun _ : Fin n => Q j) =
        Measure.pi (fun _ : Fin n => (P j).map phi) := by
      congr 1
      funext i
      exact hQ j
    _ = (Measure.pi (fun _ : Fin n => P j)).map
        (fun z : Fin n → X => fun i => phi (z i)) :=
      (map_pi_finCoordinatewise n (P j) hphi).symm

namespace Minimax

/-- **Le Cam two-point lower bound on extended `L¹` risk.** Fix [a KL budget](hyp:C) that is
[positive](hyp:_hC_pos) and [at most `1/2`](hyp:hC_small), and [a positive sample
size](hyp:n,_hn). For [two one-observation probability laws](hyp:P,Q) with [absolute
continuity](hyp:hPQ), [integrable log-likelihood ratio](hyp:hllr), and [scaled product KL at most
the budget](hyp:hKLbound), [three nonnegative-separated target values](hyp:thetaP,thetaQ,delta)
satisfying [nonnegativity and separation](hyp:hδnonneg,hδsep), and [a measurable
estimator](hyp:T,hT), [the maximum `ℝ≥0∞` absolute-error risk under the two product laws is at
least `1/8` times the separation](goal), without a loss-integrability assumption. -/
theorem leCam_two_point_L1_lintegral_lower
    {S : Type*} [MeasurableSpace S]
    (C : ℝ) (_hC_pos : 0 < C) (hC_small : C ≤ 1 / 2)
    (n : ℕ) (_hn : 1 ≤ n)
    (P Q : Measure S) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (thetaP thetaQ delta : ℝ) (hPQ : P ≪ Q)
    (hllr : Integrable (llr P Q) P)
    (hKLbound : (n : ℝ) * (InformationTheory.klDiv P Q).toReal ≤ C)
    (hδnonneg : 0 ≤ delta) (hδsep : delta ≤ |thetaP - thetaQ|)
    (T : (Fin n → S) → ℝ) (hT : Measurable T) :
    ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal delta ≤
      max (l1RiskLIntegral (Measure.pi (fun _ : Fin n => P)) T thetaP)
        (l1RiskLIntegral (Measure.pi (fun _ : Fin n => Q)) T thetaQ) := by
  let PP := Measure.pi (fun _ : Fin n => P)
  let QQ := Measure.pi (fun _ : Fin n => Q)
  have hKLprod :=
    (Causalean.Mathlib.InformationTheory.productKL_tensorization n P Q hPQ hllr).apply
  have hPinsker := Causalean.Stat.pinskerBound_pi_iid P Q hPQ hllr n
  have hsep : 2 * (delta / 2) ≤ dist thetaP thetaQ := by
    rw [Real.dist_eq]
    linarith
  have hprob := Causalean.Stat.klForm_two_point_lower_bound_of_pinsker
    (P₀ := PP) (P₁ := QQ) (Θ := ℝ) hPinsker hT hsep
  have hklprodC : (InformationTheory.klDiv PP QQ).toReal ≤ C :=
    hKLprod.trans hKLbound
  have hprobLower : (1 / 4 : ℝ) ≤
      max (PP.real {ω | delta / 2 ≤ dist (T ω) thetaP})
        (QQ.real {ω | delta / 2 ≤ dist (T ω) thetaQ}) := by
    have hkl_nonneg : 0 ≤ (InformationTheory.klDiv PP QQ).toReal := ENNReal.toReal_nonneg
    have hdiv_le : (InformationTheory.klDiv PP QQ).toReal / 2 ≤ (1 / 4 : ℝ) := by
      nlinarith
    have hsqrt_le : Real.sqrt ((InformationTheory.klDiv PP QQ).toReal / 2) ≤
        (1 / 2 : ℝ) := by
      have h := Real.sqrt_le_sqrt hdiv_le
      convert h using 1
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    exact (show (1 / 4 : ℝ) ≤
        (1 - Real.sqrt ((InformationTheory.klDiv PP QQ).toReal / 2)) / 2 by
          nlinarith).trans hprob
  have hprobLower_en : ENNReal.ofReal (1 / 4 : ℝ) ≤
      max (PP {ω | delta / 2 ≤ |T ω - thetaP|})
        (QQ {ω | delta / 2 ≤ |T ω - thetaQ|}) := by
    have h := ENNReal.ofReal_le_ofReal hprobLower
    simpa [PP, QQ, ENNReal.ofReal_max, Measure.real, Real.dist_eq] using h
  have hevent (R : Measure (Fin n → S)) [IsProbabilityMeasure R] (theta : ℝ) :
      ENNReal.ofReal (delta / 2) * R {ω | delta / 2 ≤ |T ω - theta|} ≤
        l1RiskLIntegral R T theta := by
    have hset : MeasurableSet {ω : Fin n → S | delta / 2 ≤ |T ω - theta|} := by
      simpa [Real.norm_eq_abs] using
        measurableSet_le measurable_const (hT.sub measurable_const).norm
    unfold l1RiskLIntegral
    calc
      ENNReal.ofReal (delta / 2) * R {ω | delta / 2 ≤ |T ω - theta|} =
          ∫⁻ _ω in {ω | delta / 2 ≤ |T ω - theta|},
            ENNReal.ofReal (delta / 2) ∂R := (setLIntegral_const _ _).symm
      _ = ∫⁻ ω, {ω | delta / 2 ≤ |T ω - theta|}.indicator
          (fun _ => ENNReal.ofReal (delta / 2)) ω ∂R :=
        (lintegral_indicator hset _).symm
      _ ≤ ∫⁻ ω, ENNReal.ofReal |T ω - theta| ∂R := by
        apply lintegral_mono
        intro ω
        by_cases hω : delta / 2 ≤ |T ω - theta|
        · rw [Set.indicator_of_mem (show
              ω ∈ {ω | delta / 2 ≤ |T ω - theta|} from hω)]
          exact ENNReal.ofReal_le_ofReal hω
        · rw [Set.indicator_of_notMem (show
              ω ∉ {ω | delta / 2 ≤ |T ω - theta|} from hω)]
          exact bot_le
  have hmax : ENNReal.ofReal (delta / 2) *
      max (PP {ω | delta / 2 ≤ |T ω - thetaP|})
        (QQ {ω | delta / 2 ≤ |T ω - thetaQ|}) ≤
      max (l1RiskLIntegral PP T thetaP) (l1RiskLIntegral QQ T thetaQ) := by
    rw [mul_max]
    exact max_le_max (hevent PP thetaP) (hevent QQ thetaQ)
  calc
    ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal delta =
        ENNReal.ofReal (delta / 2) * ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 8 : ℝ)),
        ← ENNReal.ofReal_mul (by linarith : 0 ≤ delta / 2)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (delta / 2) *
        max (PP {ω | delta / 2 ≤ |T ω - thetaP|})
          (QQ {ω | delta / 2 ≤ |T ω - thetaQ|}) := by gcongr
    _ ≤ max (l1RiskLIntegral PP T thetaP) (l1RiskLIntegral QQ T thetaQ) := hmax

/-- **Le Cam two-point lower bound for extended mean-squared risk.** For [a finite KL
budget](hyp:K) that is [nonnegative](hyp:hK), [two candidate laws](hyp:Q0,Q1), [their target
values](hyp:theta0,theta1), and [a measurable estimator](hyp:T), if the first law's KL
divergence from the second is at most the budget, [the maximum `ℝ≥0∞` squared risk is at least
`exp(-K)/32` times the squared parameter separation](goal), without a loss-integrability
assumption. -/
theorem le_cam_two_point_mse_lintegral (K : ℝ) (hK : 0 ≤ K) :
    ∀ {S : Type*} [MeasurableSpace S]
      (Q0 Q1 : Measure S) [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
      (theta0 theta1 : ℝ),
      InformationTheory.klDiv Q0 Q1 ≤ ENNReal.ofReal K →
      ∀ T : S → ℝ, Measurable T →
        ENNReal.ofReal (Real.exp (-K) / 32) * ENNReal.ofReal ((theta1 - theta0) ^ 2) ≤
          max (sqRiskLIntegral Q0 T theta0) (sqRiskLIntegral Q1 T theta1) := by
  intro S _ Q0 Q1 _ _ theta0 theta1 hKL T hT
  let r : ℝ := |theta1 - theta0| / 2
  have hr_nonneg : 0 ≤ r := by dsimp [r]; positivity
  have hsep_dist : 2 * r ≤ dist theta0 theta1 := by
    rw [Real.dist_eq, abs_sub_comm]
    dsimp [r]
    linarith [abs_nonneg (theta1 - theta0)]
  have hprob := Causalean.Stat.half_one_sub_tvDist_le_max_error
    (P₀ := Q0) (P₁ := Q1) (Θ := ℝ) hT hsep_dist
  have hkl_toReal_le :
      (InformationTheory.klDiv Q0 Q1).toReal ≤ (ENNReal.ofReal K).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL
  have hexp_budget :
      Real.exp (-K) ≤
        Real.exp (-(InformationTheory.klDiv Q0 Q1).toReal) :=
    Real.exp_le_exp.mpr (by rw [ENNReal.toReal_ofReal hK] at hkl_toReal_le; linarith)
  have hfin : InformationTheory.klDiv Q0 Q1 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
  have hac : Q0 ≪ Q1 := (InformationTheory.klDiv_ne_top_iff.mp hfin).1
  have hBH := Causalean.Stat.bretagnolle_huber_affinity Q0 Q1 hac hfin
  have hprob_floor :
      Real.exp (-K) / 4 ≤
        max (Q0.real {s | r ≤ |T s - theta0|})
          (Q1.real {s | r ≤ |T s - theta1|}) := by
    calc
      Real.exp (-K) / 4 ≤
          ((1 / 2 : ℝ) * Real.exp (-(InformationTheory.klDiv Q0 Q1).toReal)) / 2 := by
        nlinarith [hexp_budget, Real.exp_pos (-K),
          Real.exp_pos (-(InformationTheory.klDiv Q0 Q1).toReal)]
      _ ≤ (1 - Causalean.Stat.tvDist Q0 Q1) / 2 := by nlinarith [hBH]
      _ ≤ max (Q0.real {s | r ≤ |T s - theta0|})
          (Q1.real {s | r ≤ |T s - theta1|}) := by
        simpa only [Real.dist_eq] using hprob
  have hprob_floor_en :
      ENNReal.ofReal (Real.exp (-K) / 4) ≤
        max (Q0 {s | r ≤ |T s - theta0|}) (Q1 {s | r ≤ |T s - theta1|}) := by
    have h := ENNReal.ofReal_le_ofReal hprob_floor
    simpa [ENNReal.ofReal_max, Measure.real] using h
  have hset0 : MeasurableSet {s : S | r ^ 2 ≤ (T s - theta0) ^ 2} :=
    measurableSet_le measurable_const ((hT.sub measurable_const).pow_const 2)
  have hset1 : MeasurableSet {s : S | r ^ 2 ≤ (T s - theta1) ^ 2} :=
    measurableSet_le measurable_const ((hT.sub measurable_const).pow_const 2)
  have hevent0 : {s : S | r ≤ |T s - theta0|} =
      {s : S | r ^ 2 ≤ (T s - theta0) ^ 2} := by
    ext s
    simpa [sq_abs] using (sq_le_sq₀ hr_nonneg (abs_nonneg (T s - theta0))).symm
  have hevent1 : {s : S | r ≤ |T s - theta1|} =
      {s : S | r ^ 2 ≤ (T s - theta1) ^ 2} := by
    ext s
    simpa [sq_abs] using (sq_le_sq₀ hr_nonneg (abs_nonneg (T s - theta1))).symm
  have hmse0 : ENNReal.ofReal (r ^ 2) * Q0 {s | r ≤ |T s - theta0|} ≤
      sqRiskLIntegral Q0 T theta0 := by
    rw [hevent0]
    unfold sqRiskLIntegral
    calc
      ENNReal.ofReal (r ^ 2) * Q0 {s | r ^ 2 ≤ (T s - theta0) ^ 2} =
          ∫⁻ _s in {s | r ^ 2 ≤ (T s - theta0) ^ 2}, ENNReal.ofReal (r ^ 2) ∂Q0 :=
        (setLIntegral_const _ _).symm
      _ = ∫⁻ s, {s | r ^ 2 ≤ (T s - theta0) ^ 2}.indicator
          (fun _ => ENNReal.ofReal (r ^ 2)) s ∂Q0 := (lintegral_indicator hset0 _).symm
      _ ≤ ∫⁻ s, ENNReal.ofReal ((T s - theta0) ^ 2) ∂Q0 := by
        apply lintegral_mono
        intro s
        by_cases hs : r ^ 2 ≤ (T s - theta0) ^ 2
        · rw [Set.indicator_of_mem
            (show s ∈ {s | r ^ 2 ≤ (T s - theta0) ^ 2} from hs)]
          exact ENNReal.ofReal_le_ofReal hs
        · rw [Set.indicator_of_notMem
            (show s ∉ {s | r ^ 2 ≤ (T s - theta0) ^ 2} from hs)]
          exact bot_le
  have hmse1 : ENNReal.ofReal (r ^ 2) * Q1 {s | r ≤ |T s - theta1|} ≤
      sqRiskLIntegral Q1 T theta1 := by
    rw [hevent1]
    unfold sqRiskLIntegral
    calc
      ENNReal.ofReal (r ^ 2) * Q1 {s | r ^ 2 ≤ (T s - theta1) ^ 2} =
          ∫⁻ _s in {s | r ^ 2 ≤ (T s - theta1) ^ 2}, ENNReal.ofReal (r ^ 2) ∂Q1 :=
        (setLIntegral_const _ _).symm
      _ = ∫⁻ s, {s | r ^ 2 ≤ (T s - theta1) ^ 2}.indicator
          (fun _ => ENNReal.ofReal (r ^ 2)) s ∂Q1 := (lintegral_indicator hset1 _).symm
      _ ≤ ∫⁻ s, ENNReal.ofReal ((T s - theta1) ^ 2) ∂Q1 := by
        apply lintegral_mono
        intro s
        by_cases hs : r ^ 2 ≤ (T s - theta1) ^ 2
        · rw [Set.indicator_of_mem
            (show s ∈ {s | r ^ 2 ≤ (T s - theta1) ^ 2} from hs)]
          exact ENNReal.ofReal_le_ofReal hs
        · rw [Set.indicator_of_notMem
            (show s ∉ {s | r ^ 2 ≤ (T s - theta1) ^ 2} from hs)]
          exact bot_le
  have hmse_max : ENNReal.ofReal (r ^ 2) *
      max (Q0 {s | r ≤ |T s - theta0|}) (Q1 {s | r ≤ |T s - theta1|}) ≤
        max (sqRiskLIntegral Q0 T theta0) (sqRiskLIntegral Q1 T theta1) := by
    rw [mul_max]
    exact max_le_max hmse0 hmse1
  have hrate : ENNReal.ofReal (r ^ 2) *
      ENNReal.ofReal (Real.exp (-K) / 4) ≤
        max (sqRiskLIntegral Q0 T theta0) (sqRiskLIntegral Q1 T theta1) := by
    apply le_trans _ hmse_max
    gcongr
  have hcoef :
      ENNReal.ofReal (Real.exp (-K) / 32) *
          ENNReal.ofReal ((theta1 - theta0) ^ 2) ≤
        ENNReal.ofReal (r ^ 2) *
          ENNReal.ofReal (Real.exp (-K) / 4) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (sq_nonneg r)]
    apply ENNReal.ofReal_le_ofReal
    dsimp [r]
    nlinarith [sq_abs (theta1 - theta0), Real.exp_pos (-K)]
  exact hcoef.trans hrate

/-- **I.i.d.-product Le Cam lower bound for extended mean-squared risk.** For [probability laws
`P,Q`](hyp:P,Q) with [absolute continuity](hyp:hPQ), [integrable log-likelihood
ratio](hyp:hllr), [a one-observation KL budget](hyp:k) that is [nonnegative](hyp:hk) and
[bounds KL](hyp:hKL), [a sample size](hyp:n), [two target values](hyp:thetaP,thetaQ), and [a
measurable estimator](hyp:T,hT), [the maximum extended squared risk is at least `exp(-n*k)/32`
times the squared target separation](goal). The theorem performs KL tensorization and the
`ℝ≥0∞`/real conversion internally. -/
theorem le_cam_two_point_mse_lintegral_pi_iid
    {S : Type*} [MeasurableSpace S]
    (P Q : Measure S) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hllr : Integrable (llr P Q) P)
    (k : ℝ) (hk : 0 ≤ k) (hKL : InformationTheory.klDiv P Q ≤ ENNReal.ofReal k)
    (n : ℕ) (thetaP thetaQ : ℝ) (T : (Fin n → S) → ℝ) (hT : Measurable T) :
    ENNReal.ofReal (Real.exp (-(n : ℝ) * k) / 32) *
        ENNReal.ofReal ((thetaQ - thetaP) ^ 2) ≤
      max (sqRiskLIntegral (Measure.pi (fun _ : Fin n => P)) T thetaP)
        (sqRiskLIntegral (Measure.pi (fun _ : Fin n => Q)) T thetaQ) := by
  have htensor := Causalean.Mathlib.InformationTheory.productKL_tensorization n P Q hPQ hllr
  have hprodKL : InformationTheory.klDiv
      (Measure.pi (fun _ : Fin n => P)) (Measure.pi (fun _ : Fin n => Q)) ≤
        ENNReal.ofReal ((n : ℝ) * k) := by
    apply (ENNReal.toReal_le_toReal htensor.product_ne_top ENNReal.ofReal_ne_top).mp
    rw [Causalean.Mathlib.InformationTheory.productKL_tensorization_of_finite n P Q hPQ hllr,
      ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg n) hk)]
    have hsingle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL
    rw [ENNReal.toReal_ofReal hk] at hsingle
    exact mul_le_mul_of_nonneg_left hsingle (Nat.cast_nonneg n)
  simpa [neg_mul] using
    le_cam_two_point_mse_lintegral ((n : ℝ) * k)
      (mul_nonneg (Nat.cast_nonneg n) hk)
      (Measure.pi (fun _ : Fin n => P)) (Measure.pi (fun _ : Fin n => Q))
      thetaP thetaQ hprodKL T hT

end Minimax
end Causalean.Stat
