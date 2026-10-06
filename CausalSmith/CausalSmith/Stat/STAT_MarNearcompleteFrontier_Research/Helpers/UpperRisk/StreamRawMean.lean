module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamLinear
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamRiskVariance
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamLargeBias

/-!
# Mean and bias of the unprojected four-stream estimator

Independence of the missing-count stream from the pilot and outcome streams
turns the correction mean into the missing-mass-weighted mean in equation (14).
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

/-- The missing-count statistic is independent of the jointly selected pilot
and outcome correction, since their stream coordinates are disjoint. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamV_indep_streamG
lemma upper_streamV_indep_streamG {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    IndepFun (fun streams => streamV n d streams x a s)
      (fun streams => streamG n d streams x a s) (fourStreamLaw n P) := by
  classical
  let v : FiniteSample (Obs d) → ℝ := fun z =>
    finiteStreamCount z (fun o => inCell o x a s ∧ o.R = false) / ((n : ℝ) / 8)
  let c : FiniteSample (Obs d) → ℝ := fun z =>
    finiteStreamCount z (fun o => inCell o x a s ∧ o.R = true)
  let u : FiniteSample (Obs d) → ℝ := fun z =>
    finiteStreamCount z (fun o => inCell o x a s ∧ o.RY = true)
  let g : FiniteSample (Obs d) × FiniteSample (Obs d) → ℝ := fun z =>
    if c z.1 ≤ polyThreshold n / 4
    then lightCorrection n (c z.2) (u z.2)
    else heavyCorrection (c z.2) (u z.2)
  have hM : MeasurableSet {o : Obs d | inCell o x a s ∧ o.R = false} := by measurability
  have hB : MeasurableSet {o : Obs d | inCell o x a s ∧ o.R = true} := by measurability
  have hA : MeasurableSet {o : Obs d | inCell o x a s ∧ o.RY = true} := by measurability
  have hv : Measurable v := (upper_measurable_finiteStreamCount _ hM).div_const _
  have hc : Measurable c := upper_measurable_finiteStreamCount _ hB
  have hu : Measurable u := upper_measurable_finiteStreamCount _ hA
  have hg : Measurable g := by
    unfold g
    apply Measurable.ite (measurableSet_le (hc.comp measurable_fst) measurable_const)
    · unfold lightCorrection shiftedFalling
      fun_prop
    · unfold heavyCorrection
      apply Measurable.ite
        (measurableSet_lt measurable_const (hc.comp measurable_snd)) <;> fun_prop
  have hi : iIndepFun (fun i (streams : Fin 4 → FiniteSample (Obs d)) => streams i)
      (fourStreamLaw n P) := by
    rw [show fourStreamLaw n P = Measure.pi (fun i : Fin 4 =>
      finitePoissonSampleLaw (observedLaw P).toMeasure
        ((n : NNReal) / 2 * uniformFourMass i)) from
      labeledStreamLaw_eq_independent _ _ _ _]
    exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  exact (hi.indepFun_prodMk (fun i => measurable_pi_apply i) 2 3 1
    (by decide) (by decide)).symm.comp hv hg

/-- Independence factors the mean of the actual selected cell product. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamVG_mean
lemma upper_streamVG_mean {n d : ℕ} (hn : 0 < n) (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    (∫ streams, streamCellCorrection n d streams x a s ∂fourStreamLaw n P) =
      missingCellMass P x a s *
        (∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) := by
  unfold streamCellCorrection
  rw [
    (upper_streamV_indep_streamG (n := n) P x a s).integral_fun_mul_eq_mul_integral
      (upper_streamV_memLp_two (n := n) P x a s).aestronglyMeasurable
      (upper_measurable_streamG (n := n) x a s).aestronglyMeasurable,
    upper_stream_v_mean hn P x a s]

/-- The finite sum defining the unprojected estimator is square integrable. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_fourStreamRawEstimate_memLp_two
lemma upper_fourStreamRawEstimate_memLp_two {n d : ℕ} (hn : 0 < n) (P : FullLaw d) :
    MemLp (fourStreamRawEstimate n d) 2 (fourStreamLaw n P) := by
  have hsum : MemLp (fun streams => ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      treatmentSign a * streamCellCorrection n d streams x a s)
      2 (fourStreamLaw n P) := by
    apply memLp_finsetSum
    intro x hx
    apply memLp_finsetSum
    intro a ha
    apply memLp_finsetSum
    intro s hs
    exact (upper_streamVG_memLp_two hn P x a s).const_mul (treatmentSign a)
  convert (upper_streamLinear_memLp_two (n := n) P).add (hsum.const_mul 2) using 1
  ext streams
  exact upper_fourStreamRawEstimate_eq_linear_add streams

/-- The exact raw-estimator bias is the signed aggregate selected-correction
bias; identification cancels the first-stream arrived component. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_fourStreamRawEstimate_bias_eq
lemma upper_fourStreamRawEstimate_bias_eq {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∫ streams, fourStreamRawEstimate n d streams ∂fourStreamLaw n P) - tau P =
      2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        treatmentSign a * missingCellMass P x a s *
          ((∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
            cellEta P x a s)) := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  have hi (x : Fin d) (a s : Bool) : Integrable (fun streams =>
      treatmentSign a * streamCellCorrection n d streams x a s) (fourStreamLaw n P) :=
    ((upper_streamVG_memLp_two hn P x a s).integrable (by norm_num)).const_mul _
  have hs : Integrable (fun streams => ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      treatmentSign a * streamCellCorrection n d streams x a s) (fourStreamLaw n P) :=
    integrable_finsetSum _ (fun x _ => integrable_finsetSum _
      (fun a _ => integrable_finsetSum _ (fun s _ => hi x a s)))
  simp_rw [upper_fourStreamRawEstimate_eq_linear_add]
  rw [integral_add ((upper_streamLinear_memLp_two (n := n) P).integrable (by norm_num))
    (hs.const_mul 2), integral_const_mul]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _
    (fun a _ => integrable_finsetSum _ (fun s _ => hi x a s)))]
  simp_rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun s _ => hi _ a s)),
    integral_finsetSum _ (fun s _ => hi _ _ s), integral_const_mul,
    upper_streamVG_mean hn P]
  rw [upper_streamLinear_mean_eq_arrived hn P, tau_eq_arrived_missing_cells P h hq]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc]
  ring

/-- The raw-estimator bias inherits equation (14), with no extra regularity
premises or independence gates. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_fourStreamRawEstimate_bias_le
lemma upper_fourStreamRawEstimate_bias_le {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    |(∫ streams, fourStreamRawEstimate n d streams ∂fourStreamLaw n P) - tau P| ≤
      268435456 * (delta q * (d : ℝ) / ((n : ℝ) * ell n)) +
      4 * delta q * Real.exp (-16 * ell n) := by
  rw [upper_fourStreamRawEstimate_bias_eq hn P h hq]
  exact upper_stream_pilot_bias_sum_rate hn hL P h hq

end CausalSmith.Stat.MarNearcompleteFrontier
