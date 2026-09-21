/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.Efficiency.LAN.Convolution.Basic

/-!
# Exponentially tilted weak limits

This module provides the uniform-integrability core of Le Cam's third lemma.  It turns joint weak
convergence plus a negligible log-weight remainder and convergence of exponential means into
convergence of bounded observables under exponential tilting.
-/

public section

namespace Causalean.Estimation.Efficiency.AsymptoticLanConvolution

open Filter MeasureTheory Topology

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

private lemma weaklyConverges_add_tendstoInProbability_norm
    {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {P : (n : ℕ) → Measure (Ω n)} {X R : (n : ℕ) → Ω n → E} {Q : Measure E}
    (hP : ∀ n, IsProbabilityMeasure (P n)) (hQ : IsProbabilityMeasure Q)
    (hX : WeaklyConverges P X Q)
    (hR : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P n {ω | ε ≤ ‖R n ω‖}) atTop (𝓝 0))
    (hRmeas : ∀ n, AEMeasurable (R n) (P n)) :
    WeaklyConverges P (fun n ω => X n ω + R n ω) Q := by
  let xPM : ℕ → ProbabilityMeasure E := fun n =>
    ⟨Measure.map (X n) (P n), Measure.isProbabilityMeasure_map (hX.1 n)⟩
  let yPM : ℕ → ProbabilityMeasure E := fun n =>
    ⟨Measure.map (fun ω => X n ω + R n ω) (P n),
      Measure.isProbabilityMeasure_map ((hX.1 n).add (hRmeas n))⟩
  let qPM : ProbabilityMeasure E := ⟨Q, hQ⟩
  have hxPM : Tendsto xPM atTop (𝓝 qPM) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simpa only [xPM, qPM, ProbabilityMeasure.coe_mk,
      integral_map (hX.1 _) f.continuous.aestronglyMeasurable] using hX.2 f
  have hyPM : Tendsto yPM atTop (𝓝 qPM) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro F hF_bounded hF_lip
    obtain ⟨M, hF_bounded⟩ := hF_bounded
    obtain ⟨L, hF_lip⟩ := hF_lip
    have hF_cont : Continuous F := hF_lip.continuous
    by_cases hL0 : L = 0
    · subst L
      simp only [LipschitzWith.zero_iff] at hF_lip
      have hconst := hF_lip 0
      simp only [← hconst, yPM, qPM, ProbabilityMeasure.coe_mk, integral_const,
        smul_eq_mul]
      have hpy n : IsProbabilityMeasure
          (Measure.map (fun ω => X n ω + R n ω) (P n)) :=
        Measure.isProbabilityMeasure_map ((hX.1 n).add (hRmeas n))
      simpa using! tendsto_const_nhds
    have hL : 0 < (L : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hL0)
    simp_rw [Metric.tendsto_nhds, Real.dist_eq]
    suffices ∀ ε > 0, ∀ᶠ n in atTop,
        |∫ ω, F ω ∂(yPM n : Measure E) - ∫ ω, F ω ∂(qPM : Measure E)| <
          (L : ℝ) * ε by
      intro ε hε
      convert! this (ε / L) (by positivity)
      field_simp
    intro ε hε
    have h_le n :
        |∫ ω, F ω ∂(yPM n : Measure E) - ∫ ω, F ω ∂(qPM : Measure E)|
          ≤ (L : ℝ) * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ ‖R n ω‖}
            + |∫ ω, F ω ∂(xPM n : Measure E) - ∫ ω, F ω ∂(qPM : Measure E)| := by
      letI := hP n
      refine (abs_sub_le (∫ ω, F ω ∂(yPM n : Measure E))
        (∫ ω, F ω ∂(xPM n : Measure E))
        (∫ ω, F ω ∂(qPM : Measure E))).trans ?_
      gcongr
      have h_int_Y : Integrable (fun ω => F (X n ω + R n ω)) (P n) := by
        refine Integrable.of_bound
          (hF_cont.aestronglyMeasurable.comp_aemeasurable ((hX.1 n).add (hRmeas n)))
          (‖F 0‖ + M) (ae_of_all _ fun a => ?_)
        specialize hF_bounded (X n a + R n a) 0
        rw [← sub_le_iff_le_add']
        exact (abs_sub_abs_le_abs_sub (F (X n a + R n a)) (F 0)).trans hF_bounded
      have h_int_X : Integrable (fun ω => F (X n ω)) (P n) := by
        refine Integrable.of_bound
          (hF_cont.aestronglyMeasurable.comp_aemeasurable (hX.1 n))
          (‖F 0‖ + M) (ae_of_all _ fun a => ?_)
        specialize hF_bounded (X n a) 0
        rw [← sub_le_iff_le_add']
        exact (abs_sub_abs_le_abs_sub (F (X n a)) (F 0)).trans hF_bounded
      have h_int_sub :
          Integrable (fun a => ‖F (X n a + R n a) - F (X n a)‖) (P n) :=
        (h_int_Y.sub h_int_X).norm
      change |∫ ω, F ω ∂Measure.map (fun ω => X n ω + R n ω) (P n) -
        ∫ ω, F ω ∂Measure.map (X n) (P n)| ≤ _
      rw [integral_map (φ := fun ω => X n ω + R n ω)
          ((hX.1 n).add (hRmeas n)) hF_cont.aestronglyMeasurable,
        integral_map (φ := X n) (hX.1 n) hF_cont.aestronglyMeasurable,
        ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
      calc
        ‖∫ a, F (X n a + R n a) - F (X n a) ∂P n‖
            ≤ ∫ a, ‖F (X n a + R n a) - F (X n a)‖ ∂P n :=
              norm_integral_le_integral_norm _
        _ = ∫ a in {x | ‖R n x‖ < ε / 2},
                ‖F (X n a + R n a) - F (X n a)‖ ∂P n
              + ∫ a in {x | ε / 2 ≤ ‖R n x‖},
                ‖F (X n a + R n a) - F (X n a)‖ ∂P n := by
            symm
            simp_rw [← not_lt]
            refine integral_add_compl₀ ?_ h_int_sub
            exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        _ ≤ ∫ a in {x | ‖R n x‖ < ε / 2}, (L : ℝ) * (ε / 2) ∂P n
              + ∫ a in {x | ε / 2 ≤ ‖R n x‖}, M ∂P n := by
            gcongr ?_ + ?_
            · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
              · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
              · intro x hx
                apply hF_lip.norm_sub_le_of_le
                simpa using hx.le
            · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a => ?_
              rw [← dist_eq_norm]
              exact hF_bounded _ _
        _ = (L : ℝ) * (ε / 2) * (P n).real {x | ‖R n x‖ < ε / 2}
              + M * (P n).real {ω | ε / 2 ≤ ‖R n ω‖} := by
            simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
              Set.univ_inter, smul_eq_mul]
            ring
        _ ≤ (L : ℝ) * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ ‖R n ω‖} := by
            rw [mul_assoc]
            gcongr
            grw [measureReal_le_one, mul_one]
    have hbadENN := hR (ε / 2) (by positivity)
    have hbadReal :
        Tendsto (fun n => (P n).real {ω | ε / 2 ≤ ‖R n ω‖}) atTop (𝓝 0) := by
      change Tendsto (fun n => ENNReal.toReal ((P n) {ω | ε / 2 ≤ ‖R n ω‖}))
        atTop (𝓝 0)
      simpa only [Function.comp_def, ENNReal.toReal_zero] using
        ((ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hbadENN)
    have h_tendsto :
        Tendsto (fun n => (L : ℝ) * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ ‖R n ω‖}
            + |∫ ω, F ω ∂(xPM n : Measure E) - ∫ ω, F ω ∂(qPM : Measure E)|)
          atTop (𝓝 ((L : ℝ) * ε / 2)) := by
      have hxF := (tendsto_iff_forall_lipschitz_integral_tendsto.mp hxPM)
        F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
      have hxabs :
          Tendsto (fun n =>
            |∫ ω, F ω ∂(xPM n : Measure E) - ∫ ω, F ω ∂(qPM : Measure E)|)
            atTop (𝓝 0) := by
        have hc : Tendsto (fun _ : ℕ => ∫ ω, F ω ∂(qPM : Measure E)) atTop
            (𝓝 (∫ ω, F ω ∂(qPM : Measure E))) := tendsto_const_nhds
        have hd := hxF.sub hc
        simpa only [Function.comp_def, sub_self, abs_zero] using
          ((continuous_abs : Continuous fun x : ℝ => |x|).tendsto
            ((∫ ω, F ω ∂(qPM : Measure E)) - ∫ ω, F ω ∂(qPM : Measure E))).comp hd
      have hc : Tendsto (fun _ : ℕ => (L : ℝ) * (ε / 2)) atTop
          (𝓝 ((L : ℝ) * (ε / 2))) := tendsto_const_nhds
      have hm : Tendsto (fun n => M * (P n).real {ω | ε / 2 ≤ ‖R n ω‖})
          atTop (𝓝 0) := by simpa using tendsto_const_nhds.mul hbadReal
      convert (hc.add hm).add hxabs using 1 <;> ring
    have h_lt : (L : ℝ) * ε / 2 < (L : ℝ) * ε := half_lt_self (by positivity)
    filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn
    exact (h_le n).trans_lt hn
  refine ⟨fun n => (hX.1 n).add (hRmeas n), ?_⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hyPM
  intro f
  have hf := hyPM f
  change Tendsto (fun n => ∫ ω, f (X n ω + R n ω) ∂P n) atTop
    (𝓝 (∫ x, f x ∂Q))
  convert hf using 1
  · funext n
    exact (integral_map (φ := fun ω => X n ω + R n ω)
      ((hX.1 n).add (hRmeas n)) f.continuous.aestronglyMeasurable).symm
  · simp [qPM]

/-- Given [probability laws in every row and in the limit](hyp:hP,hQ), [joint weak convergence](hyp:hY), [a negligible additive remainder](hyp:hR), [its measurability](hyp:hRmeas), [row integrability of the exponential weights](hyp:hweight), [integrability of the limiting weight](hyp:hlimitWeight), and [normalization of their expectations](hyp:hnormalized), [bounded complex observables converge under exponential tilting](goal). -/
theorem integral_boundedContinuous_mul_exp_tendsto_of_normalized
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
    [MeasurableSpace S] [BorelSpace S]
    {P : (n : ℕ) → Measure (Ω n)} {Y : (n : ℕ) → Ω n → S} {Q : Measure S}
    {R : (n : ℕ) → Ω n → ℝ} (a : C(S, ℝ)) (f : BoundedContinuousFunction S ℂ)
    (hP : ∀ n, IsProbabilityMeasure (P n)) (hQ : IsProbabilityMeasure Q)
    (hY : WeaklyConverges P Y Q)
    (hR : TendstoInProbability P R 0)
    (hRmeas : ∀ n, AEMeasurable (R n) (P n))
    (hweight : ∀ n, Integrable (fun ω => Real.exp (a (Y n ω) + R n ω)) (P n))
    (hlimitWeight : Integrable (fun y => Real.exp (a y)) Q)
    (hnormalized : Tendsto
      (fun n => ∫ ω, Real.exp (a (Y n ω) + R n ω) ∂P n)
      atTop (𝓝 (∫ y, Real.exp (a y) ∂Q))) :
    Tendsto (fun n => ∫ ω,
      f (Y n ω) * (Real.exp (a (Y n ω) + R n ω) : ℂ) ∂P n) atTop
      (𝓝 (∫ y, f y * (Real.exp (a y) : ℂ) ∂Q)) := by
  rw [tendstoInProbability_iff_real] at hR
  let b : S → S × ℝ := fun y => (y, a y)
  have hb : Continuous b := by fun_prop
  have hbase : WeaklyConverges P (fun n ω => b (Y n ω)) (Measure.map b Q) := by
    refine ⟨fun n => hb.aemeasurable.comp_aemeasurable (hY.1 n), ?_⟩
    intro g
    have hg := hY.2 (g.compContinuous ⟨b, hb⟩)
    simpa only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
      Function.comp_apply, integral_map hb.aemeasurable
        g.continuous.aestronglyMeasurable] using hg
  have hQb : IsProbabilityMeasure (Measure.map b Q) :=
    Measure.isProbabilityMeasure_map hb.aemeasurable
  let V : (n : ℕ) → Ω n → S × ℝ := fun n ω => (0, R n ω)
  have hVmeas (n : ℕ) : AEMeasurable (V n) (P n) :=
    aemeasurable_const.prodMk (hRmeas n)
  have hVprob : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P n {ω | ε ≤ ‖V n ω‖}) atTop (𝓝 0) := by
    intro ε hε
    convert hR ε hε using 1 with n ω
    simp [V, Real.norm_eq_abs]
  have hpair0 := weaklyConverges_add_tendstoInProbability_norm
    (E := S × ℝ) hP hQb hbase hVprob hVmeas
  have hpair : WeaklyConverges P
      (fun n ω => (Y n ω, a (Y n ω) + R n ω)) (Measure.map b Q) := by
    simpa [b, V] using hpair0
  let pairPM : ℕ → ProbabilityMeasure (S × ℝ) := fun n =>
    ⟨Measure.map (fun ω => (Y n ω, a (Y n ω) + R n ω)) (P n),
      Measure.isProbabilityMeasure_map (hpair.1 n)⟩
  let limitPM : ProbabilityMeasure (S × ℝ) := ⟨Measure.map b Q, hQb⟩
  have hpairPM : Tendsto pairPM atTop (𝓝 limitPM) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro g
    simpa only [pairPM, limitPM, ProbabilityMeasure.coe_mk,
      integral_map (hpair.1 _) g.continuous.aestronglyMeasurable] using hpair.2 g
  have hpairPM_complex :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hpairPM
  let truncWeight (K : ℕ) : S × ℝ → ℝ := fun z => min (Real.exp z.2) K
  have htruncWeight_cont (K : ℕ) : Continuous (truncWeight K) := by
    fun_prop
  have htruncWeight_nonneg (K : ℕ) (z : S × ℝ) : 0 ≤ truncWeight K z := by
    exact le_min (Real.exp_pos _).le (Nat.cast_nonneg K)
  have htruncWeight_le (K : ℕ) (z : S × ℝ) : truncWeight K z ≤ K :=
    min_le_right _ _
  let truncComplex (K : ℕ) : BoundedContinuousFunction (S × ℝ) ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun z => f z.1 * (truncWeight K z : ℂ))
      (by fun_prop) (‖f‖ * K) (fun z => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (htruncWeight_nonneg K z)]
        exact mul_le_mul (f.norm_coe_le_norm z.1) (htruncWeight_le K z)
          (htruncWeight_nonneg K z) (norm_nonneg f))
  have htrunc (K : ℕ) : Tendsto (fun n => ∫ ω,
      f (Y n ω) * (truncWeight K (Y n ω, a (Y n ω) + R n ω) : ℂ) ∂P n)
      atTop (𝓝 (∫ y, f y * (truncWeight K (y, a y) : ℂ) ∂Q)) := by
    have ht := hpairPM_complex (truncComplex K)
    change Tendsto (fun n => ∫ z, truncComplex K z ∂(pairPM n : Measure (S × ℝ)))
      atTop (𝓝 (∫ z, truncComplex K z ∂(limitPM : Measure (S × ℝ)))) at ht
    convert ht using 1
    · funext n
      rw [show (pairPM n : Measure (S × ℝ)) =
          Measure.map (fun ω => (Y n ω, a (Y n ω) + R n ω)) (P n) from rfl,
        integral_map (hpair.1 n) (truncComplex K).continuous.aestronglyMeasurable]
      rfl
    · rw [show (limitPM : Measure (S × ℝ)) = Measure.map b Q from rfl,
        integral_map hb.aemeasurable (truncComplex K).continuous.aestronglyMeasurable]
      rfl
  let truncReal (K : ℕ) : BoundedContinuousFunction (S × ℝ) ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (truncWeight K)
      (htruncWeight_cont K) K (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (htruncWeight_nonneg K z)]
        exact htruncWeight_le K z)
  have htruncMean (K : ℕ) : Tendsto (fun n => ∫ ω,
      truncWeight K (Y n ω, a (Y n ω) + R n ω) ∂P n) atTop
      (𝓝 (∫ y, truncWeight K (y, a y) ∂Q)) := by
    have ht := hpair.2 (truncReal K)
    convert ht using 1
    · rfl
    · rw [integral_map hb.aemeasurable (truncReal K).continuous.aestronglyMeasurable]
      rfl
  have hlimitTrunc : Tendsto (fun K : ℕ => ∫ y, truncWeight K (y, a y) ∂Q)
      atTop (𝓝 (∫ y, Real.exp (a y) ∂Q)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y => Real.exp (a y))
    · exact Filter.Eventually.of_forall fun K =>
        (htruncWeight_cont K).aestronglyMeasurable.comp_aemeasurable hb.aemeasurable
    · refine Filter.Eventually.of_forall fun K => ae_of_all Q fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (htruncWeight_nonneg K (y, a y))]
      exact min_le_left _ _
    · exact hlimitWeight
    · refine ae_of_all Q fun y => tendsto_const_nhds.congr' ?_
      filter_upwards
        [(tendsto_natCast_atTop_atTop.eventually_gt_atTop (Real.exp (a y)))] with K hK
      exact (min_eq_left hK.le).symm
  have htruncRowInt (n K : ℕ) : Integrable
      (fun ω => truncWeight K (Y n ω, a (Y n ω) + R n ω)) (P n) := by
    apply (hweight n).mono'
    · exact (htruncWeight_cont K).aestronglyMeasurable.comp_aemeasurable (hpair.1 n)
    · refine ae_of_all _ fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (htruncWeight_nonneg K _)]
      exact min_le_left _ _
  have htruncLimitInt (K : ℕ) : Integrable
      (fun y => truncWeight K (y, a y)) Q := by
    apply hlimitWeight.mono'
    · exact (htruncWeight_cont K).aestronglyMeasurable.comp_aemeasurable hb.aemeasurable
    · refine ae_of_all _ fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (htruncWeight_nonneg K _)]
      exact min_le_left _ _
  have hfullRowInt (n : ℕ) : Integrable
      (fun ω => f (Y n ω) * (Real.exp (a (Y n ω) + R n ω) : ℂ)) (P n) := by
    exact (hweight n).ofReal.bdd_mul
      (f.continuous.aestronglyMeasurable.comp_aemeasurable (hY.1 n))
      (ae_of_all _ fun ω => f.norm_coe_le_norm (Y n ω))
  have hfullLimitInt : Integrable
      (fun y => f y * (Real.exp (a y) : ℂ)) Q := by
    exact hlimitWeight.ofReal.bdd_mul f.continuous.aestronglyMeasurable
      (ae_of_all _ fun y => f.norm_coe_le_norm y)
  have htruncRowComplexInt (n K : ℕ) : Integrable
      (fun ω => f (Y n ω) *
        (truncWeight K (Y n ω, a (Y n ω) + R n ω) : ℂ)) (P n) := by
    exact (htruncRowInt n K).ofReal.bdd_mul
      (f.continuous.aestronglyMeasurable.comp_aemeasurable (hY.1 n))
      (ae_of_all _ fun ω => f.norm_coe_le_norm (Y n ω))
  have htruncLimitComplexInt (K : ℕ) : Integrable
      (fun y => f y * (truncWeight K (y, a y) : ℂ)) Q := by
    exact (htruncLimitInt K).ofReal.bdd_mul f.continuous.aestronglyMeasurable
      (ae_of_all _ fun y => f.norm_coe_le_norm y)
  have htailRow (n K : ℕ) :
      ‖(∫ ω, f (Y n ω) * (Real.exp (a (Y n ω) + R n ω) : ℂ) ∂P n) -
          ∫ ω, f (Y n ω) *
            (truncWeight K (Y n ω, a (Y n ω) + R n ω) : ℂ) ∂P n‖ ≤
        ‖f‖ * ((∫ ω, Real.exp (a (Y n ω) + R n ω) ∂P n) -
          ∫ ω, truncWeight K (Y n ω, a (Y n ω) + R n ω) ∂P n) := by
    rw [← integral_sub (hfullRowInt n) (htruncRowComplexInt n K)]
    calc
      ‖∫ ω, f (Y n ω) * (Real.exp (a (Y n ω) + R n ω) : ℂ) -
          f (Y n ω) *
            (truncWeight K (Y n ω, a (Y n ω) + R n ω) : ℂ) ∂P n‖
          ≤ ∫ ω, ‖f (Y n ω) * (Real.exp (a (Y n ω) + R n ω) : ℂ) -
            f (Y n ω) *
              (truncWeight K (Y n ω, a (Y n ω) + R n ω) : ℂ)‖ ∂P n :=
            norm_integral_le_integral_norm _
      _ ≤ ∫ ω, ‖f‖ * (Real.exp (a (Y n ω) + R n ω) -
            truncWeight K (Y n ω, a (Y n ω) + R n ω)) ∂P n := by
          apply integral_mono (hfullRowInt n |>.sub (htruncRowComplexInt n K) |>.norm)
            ((hweight n).sub (htruncRowInt n K) |>.const_mul ‖f‖)
          intro ω
          have hd : 0 ≤ Real.exp (a (Y n ω) + R n ω) -
              truncWeight K (Y n ω, a (Y n ω) + R n ω) :=
            sub_nonneg.mpr (min_le_left _ _)
          calc
            ‖f (Y n ω) * (Real.exp (a (Y n ω) + R n ω) : ℂ) -
                f (Y n ω) *
                  (truncWeight K (Y n ω, a (Y n ω) + R n ω) : ℂ)‖ =
                ‖f (Y n ω)‖ * (Real.exp (a (Y n ω) + R n ω) -
                  truncWeight K (Y n ω, a (Y n ω) + R n ω)) := by
              rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
                Real.norm_eq_abs, abs_of_nonneg hd]
            _ ≤ _ := mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) hd
      _ = _ := by
        rw [integral_const_mul, integral_sub (hweight n) (htruncRowInt n K)]
  have htailLimit (K : ℕ) :
      ‖(∫ y, f y * (Real.exp (a y) : ℂ) ∂Q) -
          ∫ y, f y * (truncWeight K (y, a y) : ℂ) ∂Q‖ ≤
        ‖f‖ * ((∫ y, Real.exp (a y) ∂Q) -
          ∫ y, truncWeight K (y, a y) ∂Q) := by
    rw [← integral_sub hfullLimitInt (htruncLimitComplexInt K)]
    calc
      ‖∫ y, f y * (Real.exp (a y) : ℂ) -
          f y * (truncWeight K (y, a y) : ℂ) ∂Q‖
          ≤ ∫ y, ‖f y * (Real.exp (a y) : ℂ) -
            f y * (truncWeight K (y, a y) : ℂ)‖ ∂Q :=
            norm_integral_le_integral_norm _
      _ ≤ ∫ y, ‖f‖ * (Real.exp (a y) - truncWeight K (y, a y)) ∂Q := by
          apply integral_mono (hfullLimitInt.sub (htruncLimitComplexInt K)).norm
            (hlimitWeight.sub (htruncLimitInt K) |>.const_mul ‖f‖)
          intro y
          have hd : 0 ≤ Real.exp (a y) - truncWeight K (y, a y) :=
            sub_nonneg.mpr (min_le_left _ _)
          calc
            ‖f y * (Real.exp (a y) : ℂ) -
                f y * (truncWeight K (y, a y) : ℂ)‖ =
                ‖f y‖ * (Real.exp (a y) - truncWeight K (y, a y)) := by
              rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
                Real.norm_eq_abs, abs_of_nonneg hd]
            _ ≤ _ := mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) hd
      _ = _ := by
        rw [integral_const_mul, integral_sub hlimitWeight (htruncLimitInt K)]
  by_cases hfzero : ‖f‖ = 0
  · have : f = 0 := norm_eq_zero.mp hfzero
    subst f
    simp
  have hfpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hfzero)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hD : Tendsto (fun K : ℕ =>
      (∫ y, Real.exp (a y) ∂Q) - ∫ y, truncWeight K (y, a y) ∂Q)
      atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => ∫ y, Real.exp (a y) ∂Q) atTop
        (𝓝 (∫ y, Real.exp (a y) ∂Q)) := tendsto_const_nhds
    simpa using hc.sub hlimitTrunc
  have hsmall : 0 < ε / (6 * ‖f‖) := by positivity
  have hDev : ∀ᶠ K : ℕ in atTop,
      dist ((∫ y, Real.exp (a y) ∂Q) - ∫ y, truncWeight K (y, a y) ∂Q) 0 <
        ε / (6 * ‖f‖) :=
    (Metric.tendsto_nhds.mp hD) _ hsmall
  obtain ⟨K, hKdist⟩ := hDev.exists
  have hDnonneg : 0 ≤ (∫ y, Real.exp (a y) ∂Q) -
      ∫ y, truncWeight K (y, a y) ∂Q := by
    rw [sub_nonneg]
    exact integral_mono (htruncLimitInt K) hlimitWeight fun y => min_le_left _ _
  have hKsmall : (∫ y, Real.exp (a y) ∂Q) -
      ∫ y, truncWeight K (y, a y) ∂Q < ε / (6 * ‖f‖) := by
    simpa [Real.dist_eq, abs_of_nonneg hDnonneg] using hKdist
  have hrowMean : Tendsto (fun n =>
      (∫ ω, Real.exp (a (Y n ω) + R n ω) ∂P n) -
        ∫ ω, truncWeight K (Y n ω, a (Y n ω) + R n ω) ∂P n)
      atTop (𝓝 ((∫ y, Real.exp (a y) ∂Q) -
        ∫ y, truncWeight K (y, a y) ∂Q)) :=
    hnormalized.sub (htruncMean K)
  have hcut : (∫ y, Real.exp (a y) ∂Q) -
      ∫ y, truncWeight K (y, a y) ∂Q < ε / (3 * ‖f‖) := by
    exact hKsmall.trans (by
      apply div_lt_div_of_pos_left hε (by positivity)
      nlinarith [hfpos])
  have hrowEv : ∀ᶠ n in atTop,
      (∫ ω, Real.exp (a (Y n ω) + R n ω) ∂P n) -
        ∫ ω, truncWeight K (Y n ω, a (Y n ω) + R n ω) ∂P n <
          ε / (3 * ‖f‖) :=
    hrowMean.eventually_lt_const hcut
  have htruncEv : ∀ᶠ n in atTop,
      dist (∫ ω, f (Y n ω) *
          (truncWeight K (Y n ω, a (Y n ω) + R n ω) : ℂ) ∂P n)
        (∫ y, f y * (truncWeight K (y, a y) : ℂ) ∂Q) < ε / 3 :=
    (Metric.tendsto_nhds.mp (htrunc K)) _ (by positivity)
  filter_upwards [hrowEv, htruncEv] with n hn htn
  let A := ∫ ω, f (Y n ω) * (Real.exp (a (Y n ω) + R n ω) : ℂ) ∂P n
  let Tn := ∫ ω, f (Y n ω) *
    (truncWeight K (Y n ω, a (Y n ω) + R n ω) : ℂ) ∂P n
  let T := ∫ y, f y * (truncWeight K (y, a y) : ℂ) ∂Q
  let L := ∫ y, f y * (Real.exp (a y) : ℂ) ∂Q
  have hrowTail : dist A Tn < ε / 3 := by
    rw [dist_eq_norm]
    apply (htailRow n K).trans_lt
    calc
      ‖f‖ * ((∫ ω, Real.exp (a (Y n ω) + R n ω) ∂P n) -
          ∫ ω, truncWeight K (Y n ω, a (Y n ω) + R n ω) ∂P n)
          < ‖f‖ * (ε / (3 * ‖f‖)) := mul_lt_mul_of_pos_left hn hfpos
      _ = ε / 3 := by field_simp
  have hlimitTail : dist T L < ε / 6 := by
    rw [dist_eq_norm, norm_sub_rev]
    apply (htailLimit K).trans_lt
    calc
      ‖f‖ * ((∫ y, Real.exp (a y) ∂Q) -
          ∫ y, truncWeight K (y, a y) ∂Q)
          < ‖f‖ * (ε / (6 * ‖f‖)) := mul_lt_mul_of_pos_left hKsmall hfpos
      _ = ε / 6 := by field_simp
  change dist A L < ε
  calc
    dist A L ≤ dist A Tn + dist Tn L := dist_triangle _ _ _
    _ ≤ dist A Tn + (dist Tn T + dist T L) := by
      gcongr
      exact dist_triangle _ _ _
    _ = dist A Tn + dist Tn T + dist T L := by ring
    _ < ε / 3 + ε / 3 + ε / 6 := by gcongr
    _ < ε := by linarith

end Causalean.Estimation.Efficiency.AsymptoticLanConvolution
