module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamCorrectionVariance
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamLargeBias

/-!
# Large-cell correction second moments

Pilot selection is retained in the independent three-stream product, so the
large-cell light moment decays exponentially as required by equation (18).
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

/-- Three distinct ideal streams factor integrable coordinate products. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `hf`](hyp:hf), [the specified input `hg`](hyp:hg), [the specified input `hh`](hyp:hh), [the stated mathematical conclusion holds](goal). Given [the specified input `f`](hyp:f), [the specified input `g`](hyp:g), [the specified input `h`](hyp:h), [the specified input `hfi`](hyp:hfi), [the specified input `hgi`](hyp:hgi), [the specified input `hhi`](hyp:hhi). -/
-- @node: upper_three_stream_product_moment
lemma upper_three_stream_product_moment {n d : ℕ} (P : FullLaw d)
    (f g h : FiniteSample (Obs d) → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfi : Integrable (fun streams => f (streams 1)) (fourStreamLaw n P))
    (hgi : Integrable (fun streams => g (streams 2)) (fourStreamLaw n P))
    (hhi : Integrable (fun streams => h (streams 3)) (fourStreamLaw n P)) :
    Integrable (fun streams => f (streams 1) * g (streams 2) * h (streams 3))
      (fourStreamLaw n P) ∧
    (∫ streams, f (streams 1) * g (streams 2) * h (streams 3) ∂fourStreamLaw n P) =
      (∫ streams, f (streams 1) ∂fourStreamLaw n P) *
      (∫ streams, g (streams 2) ∂fourStreamLaw n P) *
      (∫ streams, h (streams 3) ∂fourStreamLaw n P) := by
  have hi : iIndepFun (fun i (streams : Fin 4 → FiniteSample (Obs d)) => streams i)
      (fourStreamLaw n P) := by
    rw [show fourStreamLaw n P = Measure.pi (fun i : Fin 4 =>
      finitePoissonSampleLaw (observedLaw P).toMeasure
        ((n : NNReal) / 2 * uniformFourMass i)) from
      labeledStreamLaw_eq_independent _ _ _ _]
    exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h12 := (hi.indepFun (by decide : (1 : Fin 4) ≠ 2)).comp hf hg
  have h123 := (hi.indepFun_prodMk (fun i => measurable_pi_apply i) 1 2 3
    (by decide) (by decide)).comp
      (hf.comp measurable_fst |>.mul (hg.comp measurable_snd)) hh
  simp only [Function.comp_def, Pi.mul_apply] at h12 h123
  have h12i := h12.integrable_mul hfi hgi
  have h12m : Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      f (streams 1) * g (streams 2)) := by fun_prop
  constructor
  · exact h123.integrable_mul h12i hhi
  rw [h123.integral_fun_mul_eq_mul_integral h12m.aestronglyMeasurable
    (hh.comp (measurable_pi_apply 3)).aestronglyMeasurable,
    h12.integral_fun_mul_eq_mul_integral
      (hf.comp (measurable_pi_apply 1)).aestronglyMeasurable
      (hg.comp (measurable_pi_apply 2)).aestronglyMeasurable]

/-- The pilot-retained correction square factors into the missing-count
second moment, pilot probability, and branch-difference second moment. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamVG_sub_VD_second_moment_eq
lemma upper_streamVG_sub_VD_second_moment_eq {n d : ℕ} (hn : 0 < n)
    (P : FullLaw d) (x : Fin d) (a s : Bool) :
    (∫ streams, (streamV n d streams x a s *
      (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P) =
      ((missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8)) *
        streamPilotLightProb n P x a s *
        (∫ streams, (streamH n d streams x a s - streamD d streams x a s) ^ 2
          ∂fourStreamLaw n P) := by
  classical
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  let A : Set (Obs d) := {o | inCell o x a s ∧ o.RY = true}
  let M : Set (Obs d) := {o | inCell o x a s ∧ o.R = false}
  let c : FiniteSample (Obs d) → ℝ := fun z => finiteStreamCount z (fun o => o ∈ B)
  let u : FiniteSample (Obs d) → ℝ := fun z => finiteStreamCount z (fun o => o ∈ A)
  let v : FiniteSample (Obs d) → ℝ := fun z =>
    (finiteStreamCount z (fun o => o ∈ M) / ((n : ℝ) / 8)) ^ 2
  let p : FiniteSample (Obs d) → ℝ := fun z =>
    if c z ≤ polyThreshold n / 4 then 1 else 0
  let f : FiniteSample (Obs d) → ℝ := fun z =>
    (lightCorrection n (c z) (u z) - heavyCorrection (c z) (u z)) ^ 2
  have hB : MeasurableSet B := by measurability
  have hA : MeasurableSet A := by measurability
  have hM : MeasurableSet M := by measurability
  have hc : Measurable c := by unfold c; fun_prop
  have hu : Measurable u := by unfold u; fun_prop
  have hv : Measurable v := by unfold v; fun_prop
  have hp : Measurable p := by
    unfold p
    apply Measurable.ite (measurableSet_le hc measurable_const) <;> fun_prop
  have hf : Measurable f := by
    have hl : Measurable (fun z => lightCorrection n (c z) (u z)) := by
      unfold lightCorrection shiftedFalling
      fun_prop
    have hd : Measurable (fun z => heavyCorrection (c z) (u z)) := by
      unfold heavyCorrection
      apply Measurable.ite (measurableSet_lt measurable_const hc) <;> fun_prop
    exact (hl.sub hd).pow_const 2
  have hvi : Integrable (fun streams => v (streams 1)) (fourStreamLaw n P) :=
    (upper_streamV_memLp_two (n := n) P x a s).integrable_sq
  have hpi : Integrable (fun streams => p (streams 2)) (fourStreamLaw n P) := by
    apply Integrable.of_bound (hp.comp (measurable_pi_apply 2)).aestronglyMeasurable 1
    filter_upwards [] with streams
    dsimp [p]
    split_ifs <;> norm_num
  have hfi : Integrable (fun streams => f (streams 3)) (fourStreamLaw n P) :=
    (upper_streamHD_memLp_two (n := n) P x a s).integrable_sq
  have hpmean : (∫ streams, p (streams 2) ∂fourStreamLaw n P) =
      streamPilotLightProb n P x a s := by
    let E : Set (Fin 4 → FiniteSample (Obs d)) :=
      {streams | c (streams 2) ≤ polyThreshold n / 4}
    have hE : MeasurableSet E := measurableSet_le
      (hc.comp (measurable_pi_apply 2)) measurable_const
    rw [show (fun streams => p (streams 2)) = E.indicator (fun _ => (1 : ℝ)) by
      funext streams
      rfl, integral_indicator_const (1 : ℝ) hE]
    simp only [smul_eq_mul, mul_one]
    rfl
  have hpoint : (fun streams => (streamV n d streams x a s *
      (streamG n d streams x a s - streamD d streams x a s)) ^ 2) =
      (fun streams => v (streams 1) * p (streams 2) * f (streams 3)) := by
    funext streams
    dsimp [v, p, f, c, u, M, B, A]
    unfold streamG streamV streamCpilot streamH streamD streamC streamU
    split_ifs <;> simp [mul_pow]
  rw [hpoint, (upper_three_stream_product_moment P v p f hv hp hf hvi hpi hfi).2, hpmean]
  rw [show (∫ streams, v (streams 1) ∂fourStreamLaw n P) =
      (missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8) from
    upper_stream_v_second_moment hn P x a s]
  rfl

/-- Retaining the pilot improves the branch-moment bound by its selection
probability, which is essential for large cells. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamVG_sub_VD_pilot_second_moment_le
lemma upper_streamVG_sub_VD_pilot_second_moment_le {n d : ℕ} (hn : 0 < n)
    (P : FullLaw d) (x : Fin d) (a s : Bool) :
    (∫ streams, (streamV n d streams x a s *
      (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P) ≤
      ((missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8)) *
        (2 * (streamPilotLightProb n P x a s *
          (∫ streams, (streamH n d streams x a s) ^ 2 ∂fourStreamLaw n P)) +
          streamPilotLightProb n P x a s / 2) := by
  rw [upper_streamVG_sub_VD_second_moment_eq hn P x a s]
  have hw : 0 ≤ missingCellMass P x a s :=
    sub_nonneg.mpr (arrivedCellMass_le_cellMass P x a s)
  have hp := (upper_streamPilotLightProb_bounds (n := n) P x a s).1
  have hc : 0 ≤ ((missingCellMass P x a s) ^ 2 +
      missingCellMass P x a s / ((n : ℝ) / 8)) * streamPilotLightProb n P x a s :=
    by positivity
  calc
    _ ≤ ((missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8)) *
        streamPilotLightProb n P x a s *
        (2 * (∫ streams, (streamH n d streams x a s) ^ 2 ∂fourStreamLaw n P) + 1 / 2) :=
      mul_le_mul_of_nonneg_left (upper_streamHD_second_moment_le P x a s) hc
    _ = _ := by ring

/-- Equation (18), cellwise: both the light and bounded heavy contributions
are exponentially suppressed by the large-cell pilot tail. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_stream_large_correction_second_moment_le
lemma upper_stream_large_correction_second_moment_le {n d : ℕ}
    (hn : 0 < n) (hL : 128 ≤ ell n) (P : FullLaw d)
    (x : Fin d) (a s : Bool) (hzB : polyThreshold n ≤ streamZ n P x a s) :
    (∫ streams, (streamV n d streams x a s *
      (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P) ≤
      (5 / 2 : ℝ) *
        ((missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8)) *
        Real.exp (-polyThreshold n / 8) := by
  have hw : 0 ≤ missingCellMass P x a s :=
    sub_nonneg.mpr (arrivedCellMass_le_cellMass P x a s)
  have hc : 0 ≤ (missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8) :=
    by positivity
  have hB : 0 ≤ polyThreshold n := by unfold polyThreshold; linarith
  have hz0 : 0 ≤ streamZ n P x a s := hB.trans hzB
  have hlight := upper_streamH_pilot_large_second_moment_le hL P x a s hzB
  have hpilot := upper_stream_pilot_large_prob_le hL P x a s hzB
  have he := Real.exp_le_exp.mpr (show -streamZ n P x a s / 4 ≤
      -streamZ n P x a s / 8 by linarith)
  have hbranch : 2 * (streamPilotLightProb n P x a s *
      (∫ streams, (streamH n d streams x a s) ^ 2 ∂fourStreamLaw n P)) +
      streamPilotLightProb n P x a s / 2 ≤
      (5 / 2 : ℝ) * Real.exp (-streamZ n P x a s / 8) := by
    linarith [hpilot.trans he]
  calc
    _ ≤ _ := upper_streamVG_sub_VD_pilot_second_moment_le hn P x a s
    _ ≤ ((missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8)) *
        ((5 / 2 : ℝ) * Real.exp (-streamZ n P x a s / 8)) :=
      mul_le_mul_of_nonneg_left hbranch hc
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (show -streamZ n P x a s / 8 ≤
          -polyThreshold n / 8 by linarith))
        (show 0 ≤ (5 / 2 : ℝ) * ((missingCellMass P x a s) ^ 2 +
          missingCellMass P x a s / ((n : ℝ) / 8)) by positivity)
      nlinarith only [hh]

/-- The missing-count second moments sum to a dimension-free budget, using
nonnegative cell masses and their total missing-mass bound. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_missing_second_moment_sum_le
lemma upper_missing_second_moment_sum_le {n d : ℕ} {q : ℝ} (hn : 0 < n)
    (P : FullLaw d) (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      ((missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8))) ≤
      (delta q) ^ 2 + delta q / ((n : ℝ) / 8) := by
  classical
  have hw : ∀ x a s, 0 ≤ missingCellMass P x a s :=
    fun x a s => (missingCellMass_bounds P h hq x a s).1
  have hmass := sum_missingCellMass_le_delta P h hq
  have hδ : 0 ≤ delta q := by unfold delta; linarith [hq.2]
  have hm : 0 < (n : ℝ) / 8 := by positivity
  have hwδ : ∀ x a s, missingCellMass P x a s ≤ delta q := by
    intro x a s
    calc
      _ ≤ ∑ s' : Bool, missingCellMass P x a s' :=
        Finset.single_le_sum (fun s' _ => hw x a s') (Finset.mem_univ s)
      _ ≤ ∑ a' : Bool, ∑ s' : Bool, missingCellMass P x a' s' :=
        Finset.single_le_sum
          (fun a' _ => Finset.sum_nonneg (fun s' _ => hw x a' s')) (Finset.mem_univ a)
      _ ≤ ∑ x' : Fin d, ∑ a' : Bool, ∑ s' : Bool, missingCellMass P x' a' s' :=
        Finset.single_le_sum (fun x' _ => Finset.sum_nonneg
          (fun a' _ => Finset.sum_nonneg (fun s' _ => hw x' a' s'))) (Finset.mem_univ x)
      _ ≤ _ := hmass
  calc
    _ ≤ ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        (delta q * missingCellMass P x a s + missingCellMass P x a s / ((n : ℝ) / 8)) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro s hs
      have hh := mul_le_mul_of_nonneg_right (hwδ x a s) (hw x a s)
      nlinarith only [hh]
    _ = delta q * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool, missingCellMass P x a s) +
        (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool, missingCellMass P x a s) / ((n : ℝ) / 8) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hmass hδ
      have hd := div_le_div_of_nonneg_right hmass hm.le
      nlinarith only [hh, hd]

/-- Equation (18), summed over all large cells, costs only the total
missing-mass budget times the exponential pilot decay. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_stream_large_correction_second_moment_sum_le
lemma upper_stream_large_correction_second_moment_sum_le {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      if polyThreshold n < streamZ n P x a s then
        (∫ streams, (streamV n d streams x a s *
          (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P)
      else 0) ≤
      (5 / 2 : ℝ) * ((delta q) ^ 2 + delta q / ((n : ℝ) / 8)) *
        Real.exp (-polyThreshold n / 8) := by
  classical
  have hm : 0 < (n : ℝ) / 8 := by positivity
  have hcoef : 0 ≤ (5 / 2 : ℝ) * Real.exp (-polyThreshold n / 8) := by positivity
  calc
    _ ≤ ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        (5 / 2 : ℝ) * Real.exp (-polyThreshold n / 8) *
          ((missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8)) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro s hs
      split_ifs with hzB
      · have hh := upper_stream_large_correction_second_moment_le hn hL P x a s hzB.le
        nlinarith only [hh]
      · have hw := (missingCellMass_bounds P h hq x a s).1
        positivity
    _ = ((5 / 2 : ℝ) * Real.exp (-polyThreshold n / 8)) *
        (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
          ((missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8))) := by
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (upper_missing_second_moment_sum_le hn P h hq) hcoef
      nlinarith only [hh]

/-- The large-cell exponential residual is at most inverse sample size. Given [the specified input `n`](hyp:n), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_large_variance_exp_le_inv
lemma upper_large_variance_exp_le_inv {n : ℕ} (hn : 0 < n) (hL : 128 ≤ ell n) :
    Real.exp (-polyThreshold n / 8) ≤ 1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he : 0 < Real.exp (1 : ℝ) + (n : ℝ) := by positivity
  calc
    _ ≤ Real.exp (-ell n) := by
      apply Real.exp_le_exp.mpr
      unfold polyThreshold
      linarith
    _ = 1 / (Real.exp (1 : ℝ) + (n : ℝ)) := by
      rw [Real.exp_neg]
      unfold ell
      rw [Real.exp_log he, one_div]
    _ ≤ _ := one_div_le_one_div_of_le hnR (by linarith [Real.exp_pos (1 : ℝ)])

/-- Equation (18) has a universal inverse-sample-size budget, with explicit
constant 25 and no dimension dependence. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_stream_large_correction_second_moment_sum_rate
lemma upper_stream_large_correction_second_moment_sum_rate {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      if polyThreshold n < streamZ n P x a s then
        (∫ streams, (streamV n d streams x a s *
          (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P)
      else 0) ≤ 25 / (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR : 0 < (n : ℝ) := by positivity
  have hδ : 0 ≤ delta q := by unfold delta; linarith [hq.2]
  have hδ1 : delta q ≤ 1 := by unfold delta; linarith [hq.1]
  have hδsq : (delta q) ^ 2 ≤ 1 := by nlinarith
  have hdiv : delta q / ((n : ℝ) / 8) ≤ 8 := by
    rw [div_le_iff₀ (show 0 < (n : ℝ) / 8 by positivity)]
    linarith
  have hc : (5 / 2 : ℝ) * ((delta q) ^ 2 + delta q / ((n : ℝ) / 8)) ≤ 25 := by
    linarith
  calc
    _ ≤ _ := upper_stream_large_correction_second_moment_sum_le hn hL P h hq
    _ ≤ 25 * Real.exp (-polyThreshold n / 8) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ ≤ 25 * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left
      (upper_large_variance_exp_le_inv hn hL) (by norm_num)
    _ = _ := by ring

/-- The entire selected correction second moment is the sum of the small-cell
budget in (17) and the dimension-free large-cell budget in (18). Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_stream_correction_second_moment_sum_le
lemma upper_stream_correction_second_moment_sum_le {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      (∫ streams, (streamV n d streams x a s *
        (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P)) ≤
      12 * (d : ℝ) * Real.exp (ell n / 8) *
        ((4 * (delta q) ^ 2 * (polyThreshold n) ^ 2 + 2 * delta q * polyThreshold n) /
          ((n : ℝ) / 8) ^ 2) + 25 / (n : ℝ) := by
  classical
  have hs := upper_stream_small_correction_second_moment_sum_le hn hL P h hq
  have hl := upper_stream_large_correction_second_moment_sum_rate hn hL P h hq
  have hsplit : (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      (∫ streams, (streamV n d streams x a s *
        (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P)) =
      (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        if streamZ n P x a s ≤ polyThreshold n then
          (∫ streams, (streamV n d streams x a s *
            (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P)
        else 0) +
      (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        if polyThreshold n < streamZ n P x a s then
          (∫ streams, (streamV n d streams x a s *
            (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P)
        else 0) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hz : streamZ n P x a s ≤ polyThreshold n
    · simp [hz, not_lt.mpr hz]
    · simp [hz, lt_of_not_ge hz]
  rw [hsplit]
  exact add_le_add hs hl

end CausalSmith.Stat.MarNearcompleteFrontier
