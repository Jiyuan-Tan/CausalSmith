/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.MinimaxFunctional
import Causalean.Stat.Minimax.ChiSquaredKernel
import Causalean.Stat.Minimax.ChiSquaredTwoPoint
import CausalSmith.Mathlib.InformationTheory.ProductChiSquared
import Causalean.Mathlib.InformationTheory.KLBind

/-! # Chi-squared control for the canonical minimax witnesses -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-- The signed Bernoulli mark kernel before translating its marks to `{0,1}`. -/
def minimaxMarkKernel {J : ℕ} (g : Fin J × ℝ → ℝ) (hg : Measurable g) :
    Kernel (Fin J × ℝ) ℝ where
  toFun := fun p => Causalean.Mathlib.Probability.twoPointMean (1 / 2) (g p)
  measurable' := (Causalean.Mathlib.Probability.measurable_twoPointMean (1 / 2)).comp hg

/-- [the stated minimax mark kernel is markov property holds](goal) for [the specified `J` input](hyp:J), [the specified `g` input](hyp:g), [the specified `hgm` input](hyp:hgm), [the specified `hg` input](hyp:hg). -/
lemma minimaxMarkKernel_isMarkov {J : ℕ} {g : Fin J × ℝ → ℝ}
    (hgm : Measurable g) (hg : ∀ p, |g p| ≤ 1 / 2) :
    IsMarkovKernel (minimaxMarkKernel g hgm) := by
  refine ⟨fun p => ?_⟩
  exact Causalean.Mathlib.Probability.twoPointMean_isProbabilityMeasure
    (by norm_num) (hg p)

/-- Retaining the design and translating the centered mark is a measurable
equivalence with the paper's observation carrier. -/
def minimaxObsEquiv (J : ℕ) : ((Fin J × ℝ) × ℝ) ≃ᵐ ClampObs J where
  toEquiv :=
    { toFun := fun p => ClampObs.mk p.1.1 p.1.2 (p.2 + 1 / 2)
      invFun := fun o => ((o.X, o.A), o.Y - 1 / 2)
      left_inv := by intro p; rcases p with ⟨⟨x, a⟩, y⟩; simp
      right_inv := by intro o; rcases o with ⟨x, a, y⟩; simp }
  measurable_toFun := by
    rw [measurable_comap_iff]
    fun_prop
  measurable_invFun := by
    let hall : Measurable (fun o : ClampObs J => (o.X, o.A, o.Y)) :=
      Measurable.of_comap_le le_rfl
    exact ((measurable_fst.comp hall).prodMk
      (measurable_fst.comp (measurable_snd.comp hall))).prodMk
        ((measurable_snd.comp (measurable_snd.comp hall)).sub measurable_const)

/-- The bind construction of the witness law is precisely the attached mark
kernel, transported through `minimaxObsEquiv`. The result uses [the `hJ` condition](hyp:hJ), [the `hkappa` condition](hyp:hkappa), [the `hg` condition](hyp:hg), [the `hgb` condition](hyp:hgb). [This is the stated conclusion](goal).
-/
lemma minimaxDataMeasure_eq_map_attachKernel {J : ℕ} {kappa : ℝ}
    {g : Fin J × ℝ → ℝ} (hJ : 0 < J) (hkappa : 0 ≤ kappa)
    (hg : Measurable g) (hgb : ∀ p, |g p| ≤ 1 / 2) :
    minimaxDataMeasure J kappa g =
      (Causalean.Stat.attachKernel (minimaxDesignMeasure J kappa)
        (minimaxMarkKernel g hg)).map (minimaxObsEquiv J) := by
  letI : IsProbabilityMeasure (minimaxDesignMeasure J kappa) :=
    minimaxDesignMeasure_isProbabilityMeasure J kappa hJ hkappa
  letI : IsMarkovKernel (minimaxMarkKernel g hg) :=
    minimaxMarkKernel_isMarkov hg hgb
  ext S hS
  have hpre : MeasurableSet ((minimaxObsEquiv J) ⁻¹' S) :=
    hS.preimage (minimaxObsEquiv J).measurable
  rw [Measure.map_apply (minimaxObsEquiv J).measurable hS]
  unfold minimaxDataMeasure
  rw [Measure.bind_apply hS (measurable_minimaxOutcomeKernel g hg).aemeasurable]
  rw [Causalean.Stat.attachKernel, Measure.compProd_apply hpre]
  apply lintegral_congr
  intro p
  change (Measure.map (fun y : ℝ => ClampObs.mk p.1 p.2 (y + 1 / 2))
      (Causalean.Mathlib.Probability.twoPointMean (1 / 2) (g p))) S = _
  rw [Measure.map_apply (by rw [measurable_comap_iff]; fun_prop) hS]
  rfl

private lemma twoPointMean_ac_center {u : ℝ} (hu : |u| < 1 / 2) :
    Causalean.Mathlib.Probability.twoPointMean (1 / 2) u ≪
      Causalean.Mathlib.Probability.twoPointMean (1 / 2) 0 := by
  let e : ℝ ≃ᵐ ℝ :=
    (affineHomeomorph (2 * (1 / 2 : ℝ)) (-(1 / 2 : ℝ)) (by norm_num)).toMeasurableEquiv
  rw [Causalean.Mathlib.Probability.twoPointMean_eq_map_bernoulli
      (1 / 2) u (by norm_num),
    Causalean.Mathlib.Probability.twoPointMean_eq_map_bernoulli
      (1 / 2) 0 (by norm_num)]
  exact (Causalean.Mathlib.Probability.bernoulliLaw_ac_of_reference_interior
    (p := (1 + u / (1 / 2)) / 2) (q := (1 + 0 / (1 / 2)) / 2)
    (by norm_num) (by norm_num)).map e.measurable

private lemma minimax_attach_sq_integrable {J : ℕ} {kappa : ℝ}
    {g : Fin J × ℝ → ℝ} (hJ : 0 < J) (hkappa : 0 ≤ kappa)
    (hg : Measurable g) (hgb : ∀ p, |g p| < 1 / 2) :
    let kg := minimaxMarkKernel g hg
    let k0 := minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const
    Integrable (fun p : (Fin J × ℝ) × ℝ =>
        ((kg.rnDeriv k0 p.1 p.2).toReal - 1) ^ 2)
      (Causalean.Stat.attachKernel (minimaxDesignMeasure J kappa) k0) := by
  dsimp only
  letI : IsProbabilityMeasure (minimaxDesignMeasure J kappa) :=
    minimaxDesignMeasure_isProbabilityMeasure J kappa hJ hkappa
  letI : IsMarkovKernel (minimaxMarkKernel g hg) :=
    minimaxMarkKernel_isMarkov hg (fun p => (hgb p).le)
  letI : IsMarkovKernel
      (minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const) :=
    minimaxMarkKernel_isMarkov (J := J) measurable_const (fun _ => by norm_num)
  let f : (Fin J × ℝ) × ℝ → ℝ := fun p =>
    (((minimaxMarkKernel g hg).rnDeriv
      (minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const)
        p.1 p.2).toReal - 1) ^ 2
  have hfmeas : AEStronglyMeasurable f
      (Causalean.Stat.attachKernel (minimaxDesignMeasure J kappa)
        (minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const)) := by
    have hrn : Measurable (fun p : (Fin J × ℝ) × ℝ =>
        (minimaxMarkKernel g hg).rnDeriv
          (minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const)
          p.1 p.2) := by fun_prop
    exact (((ENNReal.measurable_toReal.comp hrn).sub measurable_const).pow_const 2).aestronglyMeasurable
  apply (Measure.integrable_compProd_iff hfmeas).2
  constructor
  · filter_upwards with p
    change Integrable (fun y => f (p, y))
      (Causalean.Mathlib.Probability.twoPointMean (1 / 2) 0)
    unfold Causalean.Mathlib.Probability.twoPointMean
    rw [integrable_add_measure]
    constructor
    · exact Integrable.smul_measure
        (integrable_dirac (f := fun y => f (p, y)) (a := (1 / 2 : ℝ)) (by simp [enorm]))
        (by simp)
    · exact Integrable.smul_measure
        (integrable_dirac (f := fun y => f (p, y)) (a := -(1 / 2 : ℝ)) (by simp [enorm]))
        (by simp)
  · have heq : (fun p : Fin J × ℝ =>
        ∫ y, ‖f (p, y)‖ ∂(minimaxMarkKernel
          (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const) p) =
        fun p => 4 * (g p) ^ 2 := by
      funext p
      have hrn := Kernel.rnDeriv_eq_rnDeriv_measure
        (κ := minimaxMarkKernel g hg)
        (η := minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const) (a := p)
      rw [show (∫ y, ‖f (p, y)‖
            ∂(minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const) p) =
          Causalean.Stat.chiSqDiv
            ((minimaxMarkKernel g hg) p)
            ((minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const) p) by
        rw [Causalean.Stat.chiSqDiv]
        apply integral_congr_ae
        filter_upwards [hrn] with y hy
        simp [f, hy, Real.norm_of_nonneg (sq_nonneg _)]]
      exact Causalean.Stat.chiSqDiv_twoPointMean_centerHalf (hgb p)
    rw [heq]
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 4 * g p ^ 2)]
    rcases abs_lt.mp (hgb p) with ⟨hl, hr⟩
    nlinarith [sq_nonneg (g p - 1 / 2), sq_nonneg (g p + 1 / 2)]

/-- Exact one-observation chi-squared divergence for a common-design centered
Bernoulli perturbation. The result uses [the `hJ` condition](hyp:hJ), [the `hkappa` condition](hyp:hkappa), [the `hg` condition](hyp:hg), [the `hgb` condition](hyp:hgb). [This is the stated conclusion](goal).
-/
lemma minimaxDataMeasure_chiSqDiv_center (J : ℕ) (kappa : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa) (g : Fin J × ℝ → ℝ)
    (hg : Measurable g) (hgb : ∀ p, |g p| < 1 / 2) :
    Causalean.Stat.chiSqDiv (minimaxDataMeasure J kappa g)
        (minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => (0 : ℝ))) =
      ∫ p, 4 * (g p) ^ 2 ∂minimaxDesignMeasure J kappa := by
  letI : IsProbabilityMeasure (minimaxDesignMeasure J kappa) :=
    minimaxDesignMeasure_isProbabilityMeasure J kappa hJ hkappa
  letI : IsMarkovKernel (minimaxMarkKernel g hg) :=
    minimaxMarkKernel_isMarkov hg (fun p => (hgb p).le)
  letI : IsMarkovKernel
      (minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const) :=
    minimaxMarkKernel_isMarkov (J := J) measurable_const (fun _ => by norm_num)
  rw [minimaxDataMeasure_eq_map_attachKernel hJ hkappa hg (fun p => (hgb p).le),
    minimaxDataMeasure_eq_map_attachKernel hJ hkappa measurable_const (fun _ => by norm_num),
    Causalean.Stat.chiSqDiv_map_measurableEquiv]
  have hatt := Causalean.Stat.one_add_chiSqDiv_attachKernel
    (minimaxDesignMeasure J kappa) (minimaxMarkKernel g hg)
    (minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const)
    (fun p => twoPointMean_ac_center (hgb p))
    (minimax_attach_sq_integrable hJ hkappa hg hgb)
  have hatt' : 1 + Causalean.Stat.chiSqDiv
        (Causalean.Stat.attachKernel (minimaxDesignMeasure J kappa)
          (minimaxMarkKernel g hg))
        (Causalean.Stat.attachKernel (minimaxDesignMeasure J kappa)
          (minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const)) =
      ∫ p, (1 + 4 * (g p) ^ 2) ∂minimaxDesignMeasure J kappa := by
    calc
      _ = ∫ p, (1 + Causalean.Stat.chiSqDiv
          ((minimaxMarkKernel g hg) p)
          ((minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const) p))
          ∂minimaxDesignMeasure J kappa := hatt
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with p
        congr 1
        exact Causalean.Stat.chiSqDiv_twoPointMean_centerHalf (hgb p)
  rw [integral_add (integrable_const 1)
    (Integrable.of_bound (by fun_prop) 1 (by
      filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 4 * g p ^ 2)]
      rcases abs_lt.mp (hgb p) with ⟨hl, hr⟩
      nlinarith [sq_nonneg (g p - 1 / 2), sq_nonneg (g p + 1 / 2)]))] at hatt'
  have hmass : (minimaxDesignMeasure J kappa).real Set.univ = 1 := by simp
  simp only [integral_const, hmass, one_smul] at hatt'
  linarith

/-- [the stated minimax data measure ac center property holds](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `hJ` input](hyp:hJ), [the specified `hkappa` input](hyp:hkappa), [the specified `g` input](hyp:g), [the specified `hg` input](hyp:hg), [the specified `hgb` input](hyp:hgb). -/
lemma minimaxDataMeasure_ac_center (J : ℕ) (kappa : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa) (g : Fin J × ℝ → ℝ)
    (hg : Measurable g) (hgb : ∀ p, |g p| < 1 / 2) :
    minimaxDataMeasure J kappa g ≪
      minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => (0 : ℝ)) := by
  letI : IsProbabilityMeasure (minimaxDesignMeasure J kappa) :=
    minimaxDesignMeasure_isProbabilityMeasure J kappa hJ hkappa
  letI : IsMarkovKernel (minimaxMarkKernel g hg) :=
    minimaxMarkKernel_isMarkov hg (fun p => (hgb p).le)
  letI : IsMarkovKernel
      (minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const) :=
    minimaxMarkKernel_isMarkov (J := J) measurable_const (fun _ => by norm_num)
  rw [minimaxDataMeasure_eq_map_attachKernel hJ hkappa hg (fun p => (hgb p).le),
    minimaxDataMeasure_eq_map_attachKernel hJ hkappa measurable_const (fun _ => by norm_num)]
  exact (Measure.AbsolutelyContinuous.compProd_right
    (ae_of_all _ fun p => twoPointMean_ac_center (hgb p))).map
      (minimaxObsEquiv J).measurable

/-- [the stated minimax data measure sq integrable center property holds](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `hJ` input](hyp:hJ), [the specified `hkappa` input](hyp:hkappa), [the specified `g` input](hyp:g), [the specified `hg` input](hyp:hg), [the specified `hgb` input](hyp:hgb). -/
lemma minimaxDataMeasure_sq_integrable_center (J : ℕ) (kappa : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa) (g : Fin J × ℝ → ℝ)
    (hg : Measurable g) (hgb : ∀ p, |g p| < 1 / 2) :
    Integrable (fun o => (((minimaxDataMeasure J kappa g).rnDeriv
        (minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => (0 : ℝ))) o).toReal - 1) ^ 2)
      (minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => (0 : ℝ))) := by
  letI : IsProbabilityMeasure (minimaxDesignMeasure J kappa) :=
    minimaxDesignMeasure_isProbabilityMeasure J kappa hJ hkappa
  letI : IsMarkovKernel (minimaxMarkKernel g hg) :=
    minimaxMarkKernel_isMarkov hg (fun p => (hgb p).le)
  letI : IsMarkovKernel
      (minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const) :=
    minimaxMarkKernel_isMarkov (J := J) measurable_const (fun _ => by norm_num)
  let mg := Causalean.Stat.attachKernel (minimaxDesignMeasure J kappa)
    (minimaxMarkKernel g hg)
  let m0 := Causalean.Stat.attachKernel (minimaxDesignMeasure J kappa)
    (minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const)
  rw [minimaxDataMeasure_eq_map_attachKernel hJ hkappa hg (fun p => (hgb p).le),
    minimaxDataMeasure_eq_map_attachKernel hJ hkappa measurable_const (fun _ => by norm_num)]
  apply (integrable_map_equiv (minimaxObsEquiv J) _).2
  have hi := minimax_attach_sq_integrable hJ hkappa hg hgb
  refine hi.congr ?_
  have hrn := (minimaxObsEquiv J).measurableEmbedding.rnDeriv_map mg m0
  have hjoint :=
    Causalean.Mathlib.InformationTheory.Measure.rnDeriv_compProd_right_of_forall_ac
      (μ := minimaxDesignMeasure J kappa) (κ := minimaxMarkKernel g hg)
      (η := minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const)
      (ae_of_all _ fun p => twoPointMean_ac_center (hgb p))
  filter_upwards [hrn, hjoint] with p hp hj
  simp only [Function.comp_apply]
  have hj' : (mg.rnDeriv m0 p) =
      (minimaxMarkKernel g hg).rnDeriv
        (minimaxMarkKernel (fun _ : Fin J × ℝ => (0 : ℝ)) measurable_const)
        p.1 p.2 := by
    simpa [mg, m0, Causalean.Stat.attachKernel] using hj
  rw [hp, hj']

/-- Exact iid tensorization of the canonical common-design experiment. The result uses [the `hJ` condition](hyp:hJ), [the `hkappa` condition](hyp:hkappa), [the `hg` condition](hyp:hg), [the `hgb` condition](hyp:hgb). [This is the stated conclusion](goal).
-/
lemma minimaxProduct_chiSqDiv_center (J n : ℕ) (kappa : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa) (g : Fin J × ℝ → ℝ)
    (hg : Measurable g) (hgb : ∀ p, |g p| < 1 / 2) :
    1 + Causalean.Stat.chiSqDiv
        (Measure.pi (fun _ : Fin n => minimaxDataMeasure J kappa g))
        (Measure.pi (fun _ : Fin n =>
          minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => (0 : ℝ)))) =
      (1 + ∫ p, 4 * (g p) ^ 2 ∂minimaxDesignMeasure J kappa) ^ n := by
  letI : IsProbabilityMeasure (minimaxDataMeasure J kappa g) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa g hg
      (fun p => (hgb p).le)
  letI : IsProbabilityMeasure
      (minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => (0 : ℝ))) :=
    minimaxDataMeasure_isProbabilityMeasure J kappa hJ hkappa _ measurable_const
      (fun _ => by norm_num)
  rw [Causalean.Stat.one_add_chiSqDiv_pi_iid_general
    (minimaxDataMeasure J kappa g)
    (minimaxDataMeasure J kappa (fun _ : Fin J × ℝ => (0 : ℝ)))
    (minimaxDataMeasure_ac_center J kappa hJ hkappa g hg hgb)
    (minimaxDataMeasure_sq_integrable_center J kappa hJ hkappa g hg hgb) n,
    minimaxDataMeasure_chiSqDiv_center J kappa hJ hkappa g hg hgb]

/-- The squared local bump has the information-balance design integral order. The result uses [the `hJ` condition](hyp:hJ), [the `hkappa` condition](hyp:hkappa), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hamp` condition](hyp:hamp). [This is the stated conclusion](goal).
-/
lemma minimaxLocal_designIntegral_le
    (J : ℕ) (beta kappa delta h amplitude : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa) (hdelta : 0 ≤ delta)
    (hh : 0 < h) (hamp : 0 ≤ amplitude) :
    let q := fun a : ℝ => amplitude * h ^ beta *
      CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
    (∫ p, 4 * (q p.2) ^ 2 ∂minimaxDesignMeasure J kappa) ≤
      8 * (kappa + 1) * amplitude ^ 2 * h ^ (2 * beta + 1) *
        (delta + h) ^ kappa := by
  dsimp only
  let q := fun a : ℝ => amplitude * h ^ beta *
    CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
  let S : Set ℝ := Set.Icc (delta - h) (delta + h)
  have hqmeas : Measurable q := by dsimp [q]; fun_prop
  have hq0 (a : ℝ) : 0 ≤ q a := by
    dsimp [q]
    exact mul_nonneg (mul_nonneg hamp (Real.rpow_nonneg hh.le _))
      (CausalSmith.Stat.DoseResponseMinimax.doseBump_nonneg _)
  have hqle (a : ℝ) : q a ≤ amplitude * h ^ beta := by
    dsimp [q]
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one ((a - delta) / h)
    nlinarith [mul_nonneg hamp (Real.rpow_nonneg hh.le beta)]
  have hqzero (a : ℝ) (ha : a ∉ S) : q a = 0 := by
    have hu : (a - delta) / h ∉ Set.Icc (-1 : ℝ) 1 := by
      intro hu
      have hul := (le_div_iff₀ hh).mp hu.1
      have hur := (div_le_iff₀ hh).mp hu.2
      exact ha ⟨by linarith [hul], by linarith [hur]⟩
    have habs : 1 ≤ |(a - delta) / h| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · rw [abs_of_neg (by linarith : (a - delta) / h < 0)]; linarith
      · exact le_trans (by linarith : 1 ≤ (a - delta) / h) (le_abs_self _)
    simp [q, CausalSmith.Stat.DoseResponseMinimax.doseBump_eq_zero_of_one_le_abs habs]
  letI : IsProbabilityMeasure (minimaxDesignMeasure J kappa) :=
    minimaxDesignMeasure_isProbabilityMeasure J kappa hJ hkappa
  letI : Nonempty (Fin J) := Fin.pos_iff_nonempty.mp hJ
  letI : IsProbabilityMeasure (minimaxStratumMeasure J) := by
    unfold minimaxStratumMeasure
    infer_instance
  letI : IsProbabilityMeasure (minimaxTreatmentMeasure kappa) :=
    minimaxTreatmentMeasure_isProbabilityMeasure kappa hkappa
  have hint : Integrable (fun p : Fin J × ℝ => 4 * (q p.2) ^ 2)
      (minimaxDesignMeasure J kappa) := by
    refine Integrable.of_bound
      (((hqmeas.comp measurable_snd).pow_const 2).const_mul 4).aestronglyMeasurable
      (4 * (amplitude * h ^ beta) ^ 2) ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 4 * q p.2 ^ 2)]
    nlinarith [(sq_le_sq₀ (hq0 p.2)
      (mul_nonneg hamp (Real.rpow_nonneg hh.le _))).2 (hqle p.2)]
  rw [minimaxDesignMeasure, integral_prod _ hint]
  simp only [integral_const]
  rw [show (minimaxStratumMeasure J).real Set.univ = 1 by simp]
  simp only [one_smul]
  rw [minimaxTreatmentMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (by fun_prop : Measurable fun a : ℝ =>
        ENNReal.ofReal ((kappa + 1) * a ^ kappa)) (by simp)]
  simp only [smul_eq_mul]
  let T : Set ℝ := Set.Icc (0 : ℝ) 1
  have hdensity (a : ℝ) (ha : a ∈ T) : 0 ≤ (kappa + 1) * a ^ kappa :=
    mul_nonneg (by linarith) (Real.rpow_nonneg ha.1 _)
  let K : ℝ := 4 * (amplitude * h ^ beta) ^ 2 *
    ((kappa + 1) * (delta + h) ^ kappa)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hpoint : ∀ a, T.indicator
      (fun a => 4 * q a ^ 2 * ((kappa + 1) * a ^ kappa)) a ≤
      S.indicator (fun _ => K) a := by
    intro a
    by_cases haT : a ∈ T
    · simp only [Set.indicator_of_mem haT]
      by_cases haS : a ∈ S
      · simp only [Set.indicator_of_mem haS]
        have harpow : a ^ kappa ≤ (delta + h) ^ kappa :=
          Real.rpow_le_rpow haT.1 haS.2 hkappa
        have hsquare : q a ^ 2 ≤ (amplitude * h ^ beta) ^ 2 :=
          (sq_le_sq₀ (hq0 a)
            (mul_nonneg hamp (Real.rpow_nonneg hh.le _))).2 (hqle a)
        dsimp [K]
        calc
          4 * q a ^ 2 * ((kappa + 1) * a ^ kappa) ≤
              4 * (amplitude * h ^ beta) ^ 2 * ((kappa + 1) * a ^ kappa) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hsquare (by norm_num)) (hdensity a haT)
          _ ≤ 4 * (amplitude * h ^ beta) ^ 2 *
              ((kappa + 1) * (delta + h) ^ kappa) := by gcongr
      · rw [hqzero a haS]
        simp [haS]
    · by_cases haS : a ∈ S <;> simp [haT, haS, hK0]
  have hmono : (∫ a, T.indicator
      (fun a => 4 * q a ^ 2 * ((kappa + 1) * a ^ kappa)) a) ≤
      ∫ a, S.indicator (fun _ => K) a := by
    apply integral_mono_ae
    · apply IntegrableOn.integrable_indicator (s := T) (f := fun a =>
          4 * q a ^ 2 * ((kappa + 1) * a ^ kappa)) (hs := measurableSet_Icc)
      refine IntegrableOn.of_bound measure_Icc_lt_top
        (((hqmeas.pow_const 2).const_mul 4).mul
          (measurable_const.mul (measurable_id.pow_const kappa))).aestronglyMeasurable
        (4 * (amplitude * h ^ beta) ^ 2 * (kappa + 1)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hdensity a ha))]
      have haq : q a ^ 2 ≤ (amplitude * h ^ beta) ^ 2 :=
        (sq_le_sq₀ (hq0 a)
          (mul_nonneg hamp (Real.rpow_nonneg hh.le _))).2 (hqle a)
      have har : a ^ kappa ≤ 1 := by
        simpa using Real.rpow_le_one ha.1 ha.2 hkappa
      calc
        4 * q a ^ 2 * ((kappa + 1) * a ^ kappa) ≤
            4 * (amplitude * h ^ beta) ^ 2 * ((kappa + 1) * a ^ kappa) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left haq (by norm_num)) (hdensity a ha)
        _ ≤ 4 * (amplitude * h ^ beta) ^ 2 * (kappa + 1) := by
          have hdle : (kappa + 1) * a ^ kappa ≤ kappa + 1 := by
            simpa using mul_le_mul_of_nonneg_left har (by linarith : 0 ≤ kappa + 1)
          exact mul_le_mul_of_nonneg_left hdle (by positivity)
    · apply IntegrableOn.integrable_indicator (s := S) (f := fun _ : ℝ => K)
        (hs := measurableSet_Icc)
      refine IntegrableOn.of_bound measure_Icc_lt_top aestronglyMeasurable_const K ?_
      filter_upwards with a
      rw [Real.norm_eq_abs, abs_of_nonneg hK0]
    · exact Filter.Eventually.of_forall hpoint
  have hrewrite : (∫ a in Set.Icc (0 : ℝ) 1,
      (ENNReal.ofReal ((kappa + 1) * a ^ kappa)).toReal * (4 * q a ^ 2)) =
      ∫ a, T.indicator (fun a => 4 * q a ^ 2 * ((kappa + 1) * a ^ kappa)) a := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with a
    by_cases ha : a ∈ T
    · simp [T, ha, ENNReal.toReal_ofReal (hdensity a ha)]
      ring
    · simp [T, ha]
  rw [hrewrite]
  calc
    _ ≤ ∫ a, S.indicator (fun _ => K) a := hmono
    _ = K * (2 * h) := by simp [S, measureReal_def, hh.le]; ring
    _ = 8 * (kappa + 1) * amplitude ^ 2 * h ^ (2 * beta + 1) *
        (delta + h) ^ kappa := by
      dsimp [K]
      rw [show h ^ (2 * beta + 1) = h ^ beta * h ^ beta * h by
        rw [show 2 * beta + 1 = (beta + beta) + 1 by ring,
          Real.rpow_add hh, Real.rpow_add hh, Real.rpow_one]]
      ring

/-- [the stated minimax constant product chi sq bound exp four property holds](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `kappa` input](hyp:kappa), [the specified `hJ` input](hyp:hJ), [the specified `hkappa` input](hyp:hkappa), [the specified `hn` input](hyp:hn). -/
lemma minimaxConstant_productChiSq_le_exp_four
    (J n : ℕ) (kappa : ℝ) (hJ : 0 < J) (hkappa : 0 ≤ kappa)
    (hn : 5 ≤ n) :
    let eps := (n : ℝ) ^ (-(1 : ℝ) / 2)
    Causalean.Stat.chiSqDiv
      (Measure.pi (fun _ : Fin n => minimaxDataMeasure J kappa
        (fun _ : Fin J × ℝ => eps)))
      (Measure.pi (fun _ : Fin n => minimaxDataMeasure J kappa
        (fun _ : Fin J × ℝ => 0))) ≤ Real.exp 4 := by
  dsimp only
  let eps : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 2)
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have heps0 : 0 < eps := Real.rpow_pos_of_pos hnR _
  have hepslt : |eps| < 1 / 2 := by
    rw [abs_of_pos heps0]
    have hn4 : (4 : ℝ) < n := by exact_mod_cast hn
    calc
      eps < (4 : ℝ) ^ (-(1 : ℝ) / 2) := by
        dsimp [eps]
        exact Real.rpow_lt_rpow_of_neg (by norm_num) hn4 (by norm_num)
      _ = 1 / 2 := by norm_num
  have hepsSq : eps ^ 2 = (n : ℝ)⁻¹ := by
    dsimp [eps]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hneps : (n : ℝ) * eps ^ 2 = 1 := by
    rw [hepsSq]
    exact mul_inv_cancel₀ hnR.ne'
  letI : IsProbabilityMeasure (minimaxDesignMeasure J kappa) :=
    minimaxDesignMeasure_isProbabilityMeasure J kappa hJ hkappa
  have hint : (∫ p, 4 * ((fun _ : Fin J × ℝ => eps) p) ^ 2
      ∂minimaxDesignMeasure J kappa) = 4 * eps ^ 2 := by simp
  have hchiEq := minimaxProduct_chiSqDiv_center J n kappa hJ hkappa
    (fun _ : Fin J × ℝ => eps) measurable_const (fun _ => hepslt)
  rw [hint] at hchiEq
  have hbase : 1 + 4 * eps ^ 2 ≤ Real.exp (4 * eps ^ 2) := by
    simpa [add_comm] using Real.add_one_le_exp (4 * eps ^ 2)
  have hpow : (1 + 4 * eps ^ 2) ^ n ≤ Real.exp 4 := by
    calc
      _ ≤ (Real.exp (4 * eps ^ 2)) ^ n :=
        pow_le_pow_left₀ (by positivity) hbase n
      _ = Real.exp ((n : ℝ) * (4 * eps ^ 2)) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp 4 := by rw [show (n : ℝ) * (4 * eps ^ 2) = 4 by nlinarith]
  change Causalean.Stat.chiSqDiv
      (Measure.pi (fun _ : Fin n => minimaxDataMeasure J kappa
        (fun _ : Fin J × ℝ => eps)))
      (Measure.pi (fun _ : Fin n => minimaxDataMeasure J kappa
        (fun _ : Fin J × ℝ => 0))) ≤ Real.exp 4
  linarith [hchiEq, hpow]

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
