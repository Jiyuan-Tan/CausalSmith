module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.BiasVariance
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamPilot

/-!
# Deterministic aggregation of the pilot correction bias

The signed treatment contrast in equation (14) is controlled by a weighted
sum of cellwise correction biases.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory
open scoped BigOperators

-- @node: upper_cellEta_abs_le_half
/-- A centered Bernoulli outcome regression has absolute value at most one half. Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_cellEta_abs_le_half {d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    |cellEta P x a s| ≤ 1 / 2 := by
  classical
  let N : ℝ := ∑ o : Obs d,
    if o.X = x ∧ o.A = a ∧ o.S = s ∧ o.R = true ∧ o.RY = true then
      obsMass (observedLaw P) o else 0
  let D : ℝ := ∑ o : Obs d,
    if o.X = x ∧ o.A = a ∧ o.S = s ∧ o.R = true then
      obsMass (observedLaw P) o else 0
  have hN : 0 ≤ N := by
    apply Finset.sum_nonneg
    intro o ho
    split_ifs <;> simp [obsMass]
  have hD : 0 ≤ D := by
    apply Finset.sum_nonneg
    intro o ho
    split_ifs <;> simp [obsMass]
  have hND : N ≤ D := by
    apply Finset.sum_le_sum
    intro o ho
    by_cases hn : o.X = x ∧ o.A = a ∧ o.S = s ∧ o.R = true ∧ o.RY = true
    · simp [hn]
    · simp only [hn, if_false]
      split_ifs <;> simp [obsMass]
  have hratio0 : 0 ≤ N / D := div_nonneg hN hD
  have hratio1 : N / D ≤ 1 := by
    by_cases hDz : D = 0
    · have hNz : N = 0 := le_antisymm (hDz ▸ hND) hN
      simp [hNz, hDz]
    · exact (div_le_one (lt_of_le_of_ne hD (Ne.symm hDz))).2 hND
  change |N / D - 1 / 2| ≤ 1 / 2
  rw [abs_le]
  constructor <;> linarith

-- @node: upper_streamPilotLightProb_bounds
/-- The light-branch pilot selection probability lies in the unit interval. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_streamPilotLightProb_bounds {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    streamPilotLightProb n P x a s ∈ Set.Icc 0 1 := by
  classical
  let Q := (observedLaw P).toMeasure
  have hμ : fourStreamLaw n P = Measure.pi (fun i : Fin 4 =>
      Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
        Q ((n : NNReal) / 2 * uniformFourMass i)) := by
    unfold fourStreamLaw Q
    exact Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.labeledStreamLaw_eq_independent
      _ _ _ _
  letI : IsProbabilityMeasure (fourStreamLaw n P) := by
    rw [hμ]
    infer_instance
  unfold streamPilotLightProb
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

-- @node: upper_stream_pilot_bias_cell_abs_le
/-- The absolute bias of one pilot-selected correction is bounded by its
light Chebyshev remainder and heavy empty-count remainder. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_pilot_bias_cell_abs_le {n d : ℕ} {q : ℝ}
    (P : FullLaw d) (h : LawClass d q P)
    (x : Fin d) (a s : Bool) :
    |(∫ streams, streamG n d streams x a s
        ∂fourStreamLaw n P) - cellEta P x a s| ≤
      (1 / 2 : ℝ) *
        (streamPilotLightProb n P x a s *
            |(qPoly n).eval (streamZ n P x a s)| +
          (1 - streamPilotLightProb n P x a s) *
            Real.exp (-(streamZ n P x a s))) := by
  have hp := upper_streamPilotLightProb_bounds (n := n) P x a s
  have hη := upper_cellEta_abs_le_half P x a s
  have hpn : 0 ≤ 1 - streamPilotLightProb n P x a s := sub_nonneg.mpr hp.2
  have hexp : 0 ≤ Real.exp (-(streamZ n P x a s)) := Real.exp_pos _ |>.le
  have hrhs : 0 ≤
      streamPilotLightProb n P x a s *
          |(qPoly n).eval (streamZ n P x a s)| +
        (1 - streamPilotLightProb n P x a s) *
          Real.exp (-(streamZ n P x a s)) :=
    add_nonneg (mul_nonneg hp.1 (abs_nonneg _)) (mul_nonneg hpn hexp)
  rw [upper_stream_pilot_bias P h x a s, abs_mul, abs_neg]
  calc
    |cellEta P x a s| *
        |streamPilotLightProb n P x a s *
            (qPoly n).eval (streamZ n P x a s) +
          (1 - streamPilotLightProb n P x a s) *
            Real.exp (-(streamZ n P x a s))| ≤
        |cellEta P x a s| *
          (streamPilotLightProb n P x a s *
              |(qPoly n).eval (streamZ n P x a s)| +
            (1 - streamPilotLightProb n P x a s) *
              Real.exp (-(streamZ n P x a s))) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        |streamPilotLightProb n P x a s *
              (qPoly n).eval (streamZ n P x a s) +
            (1 - streamPilotLightProb n P x a s) *
              Real.exp (-(streamZ n P x a s))| ≤
            |streamPilotLightProb n P x a s *
              (qPoly n).eval (streamZ n P x a s)| +
            |(1 - streamPilotLightProb n P x a s) *
              Real.exp (-(streamZ n P x a s))| := abs_add_le _ _
        _ = streamPilotLightProb n P x a s *
              |(qPoly n).eval (streamZ n P x a s)| +
            (1 - streamPilotLightProb n P x a s) *
              Real.exp (-(streamZ n P x a s)) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hp.1,
            abs_of_nonneg hpn, abs_of_nonneg hexp]
    _ ≤ (1 / 2 : ℝ) *
          (streamPilotLightProb n P x a s *
              |(qPoly n).eval (streamZ n P x a s)| +
            (1 - streamPilotLightProb n P x a s) *
              Real.exp (-(streamZ n P x a s))) :=
      mul_le_mul_of_nonneg_right hη hrhs

-- @node: upper_stream_pilot_bias_abs_sum_le
/-- The signed aggregate pilot bias is bounded by the missing-mass-weighted
sum of the absolute cell biases. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma upper_stream_pilot_bias_abs_sum_le {n d : ℕ} {q : ℝ}
    (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    |2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      (treatmentSign a * missingCellMass P x a s *
        ((∫ streams, streamG n d streams x a s
          ∂fourStreamLaw n P) - cellEta P x a s)))| ≤
      2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        (missingCellMass P x a s *
          |(∫ streams, streamG n d streams x a s
            ∂fourStreamLaw n P) - cellEta P x a s|)) := by
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    |∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        treatmentSign a * missingCellMass P x a s *
          ((∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
            cellEta P x a s)| ≤
        ∑ x : Fin d, |∑ a : Bool, ∑ s : Bool,
          treatmentSign a * missingCellMass P x a s *
            ((∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
              cellEta P x a s)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : Fin d, ∑ a : Bool, |∑ s : Bool,
          treatmentSign a * missingCellMass P x a s *
            ((∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
              cellEta P x a s)| := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
          |treatmentSign a * missingCellMass P x a s *
            ((∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
              cellEta P x a s)| := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        missingCellMass P x a s *
          |(∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
            cellEta P x a s| := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro s hs
      have hw : 0 ≤ missingCellMass P x a s :=
        (missingCellMass_bounds P h hq x a s).1
      simp only [abs_mul, abs_of_nonneg hw]
      unfold treatmentSign
      cases a <;> simp

end CausalSmith.Stat.MarNearcompleteFrontier

