module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.LightExponentialBounds

/-!
# Small-cell correction variance budget

The independent missing-count and fourth-stream correction moments bound the
pilot-selected difference from the heavy branch, as in equation (17).
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

/-- The normalized missing stream is independent of every measurable statistic
of the fourth stream. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hf`](hyp:hf), [the stated mathematical conclusion holds](goal). Given [the specified input `f`](hyp:f). -/
-- @node: upper_streamV_indep_fourth
lemma upper_streamV_indep_fourth {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) (f : FiniteSample (Obs d) → ℝ)
    (hf : Measurable f) :
    IndepFun (fun streams => streamV n d streams x a s)
      (fun streams => f (streams 3)) (fourStreamLaw n P) := by
  classical
  let M : Set (Obs d) := {o | inCell o x a s ∧ o.R = false}
  let v : FiniteSample (Obs d) → ℝ := fun z =>
    finiteStreamCount z (fun o => o ∈ M) / ((n : ℝ) / 8)
  have hM : MeasurableSet M := by measurability
  have hv : Measurable v := by
    unfold v
    fun_prop
  have hi : iIndepFun (fun i (streams : Fin 4 → FiniteSample (Obs d)) => streams i)
      (fourStreamLaw n P) := by
    rw [show fourStreamLaw n P = Measure.pi (fun i : Fin 4 =>
      finitePoissonSampleLaw (observedLaw P).toMeasure
        ((n : NNReal) / 2 * uniformFourMass i)) from
      labeledStreamLaw_eq_independent _ _ _ _]
    exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  exact (hi.indepFun (by decide : (1 : Fin 4) ≠ 3)).comp hv hf

/-- The difference between light and heavy corrections is square integrable. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamHD_memLp_two
lemma upper_streamHD_memLp_two {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    MemLp (fun streams => streamH n d streams x a s - streamD d streams x a s)
      2 (fourStreamLaw n P) := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  have hh : MemLp (fun streams => streamH n d streams x a s) 2
      (fourStreamLaw n P) := by
    exact (memLp_two_iff_integrable_sq
      (upper_measurable_streamH x a s).aestronglyMeasurable).mpr
      (upper_streamH_sq_integrable (n := n) P x a s)
  have hd : MemLp (fun streams => streamD d streams x a s) 2
      (fourStreamLaw n P) := by
    apply MemLp.of_bound (upper_measurable_streamD x a s).aestronglyMeasurable (1 / 2)
    simpa only [Real.norm_eq_abs] using upper_streamD_abs_le_half_ae (n := n) P x a s
  exact hh.sub hd

/-- Squaring the branch difference costs twice the light second moment and
one half for the bounded heavy branch. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamHD_second_moment_le
lemma upper_streamHD_second_moment_le {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    (∫ streams, (streamH n d streams x a s - streamD d streams x a s) ^ 2
      ∂fourStreamLaw n P) ≤
      2 * (∫ streams, (streamH n d streams x a s) ^ 2 ∂fourStreamLaw n P) + 1 / 2 := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  have hi := (upper_streamHD_memLp_two (n := n) P x a s).integrable_sq
  have he := ((upper_streamH_sq_integrable (n := n) P x a s).const_mul 2).add
    (integrable_const (1 / 2 : ℝ))
  calc
    _ ≤ ∫ streams, 2 * (streamH n d streams x a s) ^ 2 + (1 / 2 : ℝ)
        ∂fourStreamLaw n P := by
      apply integral_mono_ae hi he
      filter_upwards [upper_streamD_abs_le_half_ae (n := n) P x a s] with streams hd
      have hd2 : (streamD d streams x a s) ^ 2 ≤ 1 / 4 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hd 2
        norm_num [sq_abs] at this
        exact this
      change (streamH n d streams x a s - streamD d streams x a s) ^ 2 ≤
        2 * (streamH n d streams x a s) ^ 2 + 1 / 2
      nlinarith [sq_nonneg (streamH n d streams x a s + streamD d streams x a s)]
    _ = _ := by
      rw [integral_add ((upper_streamH_sq_integrable (n := n) P x a s).const_mul 2)
        (integrable_const _), integral_const_mul]
      simp

/-- Independence supplies both integrability and the exact unselected product
second moment needed to dominate the pilot-selected correction. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamVHD_second_moment
lemma upper_streamVHD_second_moment {n d : ℕ} (hn : 0 < n) (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    Integrable (fun streams =>
      (streamV n d streams x a s *
        (streamH n d streams x a s - streamD d streams x a s)) ^ 2)
      (fourStreamLaw n P) ∧
    (∫ streams, (streamV n d streams x a s *
        (streamH n d streams x a s - streamD d streams x a s)) ^ 2
      ∂fourStreamLaw n P) =
      ((missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8)) *
        (∫ streams, (streamH n d streams x a s - streamD d streams x a s) ^ 2
          ∂fourStreamLaw n P) := by
  classical
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  let A : Set (Obs d) := {o | inCell o x a s ∧ o.RY = true}
  let c : FiniteSample (Obs d) → ℝ := fun z => finiteStreamCount z (fun o => o ∈ B)
  let u : FiniteSample (Obs d) → ℝ := fun z => finiteStreamCount z (fun o => o ∈ A)
  let f : FiniteSample (Obs d) → ℝ := fun z =>
    lightCorrection n (c z) (u z) - heavyCorrection (c z) (u z)
  have hB : MeasurableSet B := by measurability
  have hA : MeasurableSet A := by measurability
  have hc : Measurable c := by unfold c; fun_prop
  have hu : Measurable u := by unfold u; fun_prop
  have hf : Measurable f := by
    have hl : Measurable (fun z => lightCorrection n (c z) (u z)) := by
      unfold lightCorrection shiftedFalling
      fun_prop
    have hd : Measurable (fun z => heavyCorrection (c z) (u z)) := by
      unfold heavyCorrection
      apply Measurable.ite (measurableSet_lt measurable_const hc) <;> fun_prop
    exact hl.sub hd
  have hind := (upper_streamV_indep_fourth (n := n) P x a s f hf).comp
    (by fun_prop : Measurable (fun v : ℝ => v ^ 2))
    (by fun_prop : Measurable (fun v : ℝ => v ^ 2))
  have hid : (fun streams => f (streams 3)) =
      (fun streams => streamH n d streams x a s - streamD d streams x a s) := rfl
  simp only [Function.comp_def, hid] at hind
  have hv := (upper_streamV_memLp_two (n := n) P x a s).integrable_sq
  have hd := (upper_streamHD_memLp_two (n := n) P x a s).integrable_sq
  constructor
  · simp_rw [mul_pow]
    exact hind.integrable_mul hv hd
  · simp only [mul_pow]
    rw [hind.integral_fun_mul_eq_mul_integral hv.aestronglyMeasurable hd.aestronglyMeasurable,
      upper_stream_v_second_moment hn P x a s]

/-- Pilot selection only removes the branch difference, so its square is
bounded by the unselected product square. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). Given [the specified input `streams`](hyp:streams). -/
-- @node: upper_streamVG_sub_VD_sq_le
lemma upper_streamVG_sub_VD_sq_le {n d : ℕ}
    (streams : Fin 4 → FiniteSample (Obs d)) (x : Fin d) (a s : Bool) :
    (streamV n d streams x a s *
      (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ≤
    (streamV n d streams x a s *
      (streamH n d streams x a s - streamD d streams x a s)) ^ 2 := by
  unfold streamG
  split_ifs
  · exact le_rfl
  · simp only [sub_self, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact sq_nonneg _

/-- The pilot-selected correction is measurable. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_measurable_streamG
@[fun_prop]
lemma upper_measurable_streamG {n d : ℕ} (x : Fin d) (a s : Bool) :
    Measurable (fun streams : Fin 4 → FiniteSample (Obs d) => streamG n d streams x a s) := by
  classical
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  have hB : MeasurableSet B := by measurability
  have hp : Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamCpilot d streams x a s) :=
    (upper_measurable_finiteStreamCount B hB).comp (measurable_pi_apply 2)
  unfold streamG
  apply Measurable.ite (measurableSet_le hp measurable_const) <;> fun_prop

/-- The selected product square is integrable by domination, without additional
regularity hypotheses on the estimator. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamVG_sub_VD_sq_integrable
lemma upper_streamVG_sub_VD_sq_integrable {n d : ℕ} (hn : 0 < n) (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    Integrable (fun streams => (streamV n d streams x a s *
      (streamG n d streams x a s - streamD d streams x a s)) ^ 2) (fourStreamLaw n P) := by
  classical
  let M : Set (Obs d) := {o | inCell o x a s ∧ o.R = false}
  have hM : MeasurableSet M := by measurability
  have hv : Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamV n d streams x a s) := by
    unfold streamV
    have hm : Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
        finiteStreamCount (streams 1) (fun o => o ∈ M)) :=
      (upper_measurable_finiteStreamCount M hM).comp (measurable_pi_apply 1)
    exact hm.div measurable_const
  have hm : Measurable (fun streams => (streamV n d streams x a s *
      (streamG n d streams x a s - streamD d streams x a s)) ^ 2) := by fun_prop
  apply (upper_streamVHD_second_moment hn P x a s).1.mono' hm.aestronglyMeasurable
  filter_upwards [] with streams
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact upper_streamVG_sub_VD_sq_le streams x a s

/-- Dropping pilot selection and factoring the independent product bounds the
actual correction second moment by the two branch moments. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamVG_sub_VD_second_moment_le
lemma upper_streamVG_sub_VD_second_moment_le {n d : ℕ} (hn : 0 < n) (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    (∫ streams, (streamV n d streams x a s *
      (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P) ≤
    ((missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8)) *
      (2 * (∫ streams, (streamH n d streams x a s) ^ 2 ∂fourStreamLaw n P) + 1 / 2) := by
  have hprod := upper_streamVHD_second_moment hn P x a s
  calc
    _ ≤ ∫ streams, (streamV n d streams x a s *
        (streamH n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P :=
      integral_mono_ae (upper_streamVG_sub_VD_sq_integrable hn P x a s) hprod.1
        (Filter.Eventually.of_forall fun streams => upper_streamVG_sub_VD_sq_le streams x a s)
    _ = _ := hprod.2
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (upper_streamHD_second_moment_le P x a s)
      have hw : 0 ≤ missingCellMass P x a s :=
        sub_nonneg.mpr (arrivedCellMass_le_cellMass P x a s)
      positivity

/-- A small cell has a uniformly small missing-count second moment, using the
arrival floor rather than any extra moment premise. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_small_missing_second_moment_le
lemma upper_small_missing_second_moment_le {n d : ℕ} {q : ℝ} (hn : 0 < n)
    (P : FullLaw d) (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (x : Fin d) (a s : Bool) (hzB : streamZ n P x a s ≤ polyThreshold n) :
    (missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8) ≤
      (4 * (delta q) ^ 2 * (polyThreshold n) ^ 2 + 2 * delta q * polyThreshold n) /
        ((n : ℝ) / 8) ^ 2 := by
  let m : ℝ := (n : ℝ) / 8
  let w := missingCellMass P x a s
  let B := polyThreshold n
  have hm : 0 < m := by dsimp [m]; positivity
  have hδ : 0 ≤ delta q := by unfold delta; linarith [hq.2]
  have hw : 0 ≤ w := (missingCellMass_bounds P h hq x a s).1
  have hwB : w * m ≤ 2 * delta q * B := by
    have hh := mul_le_mul_of_nonneg_right
      (missingCellMass_bounds P h hq x a s).2.2 hm.le
    have ht := mul_le_mul_of_nonneg_left hzB (show 0 ≤ 2 * delta q by positivity)
    dsimp [streamZ] at ht
    dsimp [w, m, B] at *
    nlinarith
  have hwbound : w ≤ 2 * delta q * B / m := (le_div_iff₀ hm).mpr hwB
  have hright : 0 ≤ 2 * delta q * B / m := hw.trans hwbound
  have hs := pow_le_pow_left₀ hw hwbound 2
  have hl := div_le_div_of_nonneg_right hwbound hm.le
  calc
    _ = w ^ 2 + w / m := rfl
    _ ≤ (2 * delta q * B / m) ^ 2 + (2 * delta q * B / m) / m := add_le_add hs hl
    _ = _ := by dsimp [B, m]; ring

/-- Equation (17), cellwise: pilot-selected correction squares in small cells
have the exponential light-moment envelope times the missing-count budget. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_stream_small_correction_second_moment_le
lemma upper_stream_small_correction_second_moment_le {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) (x : Fin d) (a s : Bool)
    (hzB : streamZ n P x a s ≤ polyThreshold n) :
    (∫ streams, (streamV n d streams x a s *
      (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P) ≤
      3 * Real.exp (ell n / 8) *
        ((4 * (delta q) ^ 2 * (polyThreshold n) ^ 2 + 2 * delta q * polyThreshold n) /
          ((n : ℝ) / 8) ^ 2) := by
  have hw : 0 ≤ missingCellMass P x a s := (missingCellMass_bounds P h hq x a s).1
  have hc : 0 ≤ (missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8) :=
    by positivity
  have he : 1 ≤ Real.exp (ell n / 8) := Real.one_le_exp (by linarith)
  have hmoment := upper_streamH_small_second_moment_le hL P x a s hzB
  have hbranch : 2 * (∫ streams, (streamH n d streams x a s) ^ 2 ∂fourStreamLaw n P) + 1 / 2 ≤
      3 * Real.exp (ell n / 8) := by linarith
  calc
    _ ≤ _ := upper_streamVG_sub_VD_second_moment_le hn P x a s
    _ ≤ ((missingCellMass P x a s) ^ 2 + missingCellMass P x a s / ((n : ℝ) / 8)) *
        (3 * Real.exp (ell n / 8)) := mul_le_mul_of_nonneg_left hbranch hc
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left
        (upper_small_missing_second_moment_le hn P h hq x a s hzB) (by positivity)

/-- Equation (17), aggregated over the at most four times d small cells. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_stream_small_correction_second_moment_sum_le
lemma upper_stream_small_correction_second_moment_sum_le {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      if streamZ n P x a s ≤ polyThreshold n then
        (∫ streams, (streamV n d streams x a s *
          (streamG n d streams x a s - streamD d streams x a s)) ^ 2 ∂fourStreamLaw n P)
      else 0) ≤
      12 * (d : ℝ) * Real.exp (ell n / 8) *
        ((4 * (delta q) ^ 2 * (polyThreshold n) ^ 2 + 2 * delta q * polyThreshold n) /
          ((n : ℝ) / 8) ^ 2) := by
  classical
  let K := 3 * Real.exp (ell n / 8) *
    ((4 * (delta q) ^ 2 * (polyThreshold n) ^ 2 + 2 * delta q * polyThreshold n) /
      ((n : ℝ) / 8) ^ 2)
  have hδ : 0 ≤ delta q := by unfold delta; linarith [hq.2]
  have hB : 0 ≤ polyThreshold n := by unfold polyThreshold; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  calc
    _ ≤ ∑ _x : Fin d, ∑ _a : Bool, ∑ _s : Bool, K := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro s hs
      split_ifs with hzB
      · exact upper_stream_small_correction_second_moment_le hn hL P h hq x a s hzB
      · exact hK
    _ = _ := by simp [K]; ring

end CausalSmith.Stat.MarNearcompleteFrontier
