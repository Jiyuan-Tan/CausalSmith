module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.Fallback
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.Converse.Target
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.Expansion
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.Risk

/-!
# Four-stream form of the missing-membership estimator

This module identifies the run's explicit count-and-label formula with the
finite-partition Rao--Blackwell API.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteMeasurablePartition

/-- Count observations in a finite stream satisfying a condition. -/
noncomputable def finiteStreamCount {d : ℕ} (s : FiniteSample (Obs d))
    (E : Obs d → Prop) : ℝ := by
  classical
  exact ∑ i : Fin s.count, if E (s.2 i) then 1 else 0

/-- Missing-cell count from the second stream divided by its Poisson intensity. -/
noncomputable def streamV (n d : ℕ)
    (streams : Fin 4 → FiniteSample (Obs d)) (x : Fin d) (a s : Bool) : ℝ :=
  finiteStreamCount (streams 1) (fun o ↦ inCell o x a s ∧ o.R = false) /
    ((n : ℝ) / 8)

/-- Pilot arrived-cell count from the third stream. -/
noncomputable def streamCpilot (d : ℕ)
    (streams : Fin 4 → FiniteSample (Obs d)) (x : Fin d) (a s : Bool) : ℝ :=
  finiteStreamCount (streams 2) (fun o ↦ inCell o x a s ∧ o.R = true)

/-- Arrived-cell count from the fourth stream. -/
noncomputable def streamC (d : ℕ)
    (streams : Fin 4 → FiniteSample (Obs d)) (x : Fin d) (a s : Bool) : ℝ :=
  finiteStreamCount (streams 3) (fun o ↦ inCell o x a s ∧ o.R = true)

/-- Arrived-success count from the fourth stream. -/
noncomputable def streamU (d : ℕ)
    (streams : Fin 4 → FiniteSample (Obs d)) (x : Fin d) (a s : Bool) : ℝ :=
  finiteStreamCount (streams 3) (fun o ↦ inCell o x a s ∧ o.RY = true)

/-- Light-cell polynomial correction for a fourth-stream cell. -/
noncomputable def streamH (n d : ℕ)
    (streams : Fin 4 → FiniteSample (Obs d)) (x : Fin d) (a s : Bool) : ℝ :=
  lightCorrection n (streamC d streams x a s) (streamU d streams x a s)

/-- Heavy-cell plug-in correction for a fourth-stream cell. -/
noncomputable def streamD (d : ℕ)
    (streams : Fin 4 → FiniteSample (Obs d)) (x : Fin d) (a s : Bool) : ℝ :=
  heavyCorrection (streamC d streams x a s) (streamU d streams x a s)

/-- Pilot-selected correction for one cell. -/
noncomputable def streamG (n d : ℕ)
    (streams : Fin 4 → FiniteSample (Obs d)) (x : Fin d) (a s : Bool) : ℝ :=
  if streamCpilot d streams x a s ≤ polyThreshold n / 4
  then streamH n d streams x a s else streamD d streams x a s

/-- One cell's missing-membership correction written as a statistic of four streams. -/
noncomputable def streamCellCorrection (n d : ℕ)
    (streams : Fin 4 → FiniteSample (Obs d)) (x : Fin d) (a s : Bool) : ℝ :=
  streamV n d streams x a s * streamG n d streams x a s

/-- The raw, unprojected missing-membership estimate of four streams. -/
noncomputable def fourStreamRawEstimate (n d : ℕ)
    (streams : Fin 4 → FiniteSample (Obs d)) : ℝ :=
  let m : ℝ := (n : ℝ) / 8
  2 / m * (∑ i : Fin (streams 0).count,
      (if ((streams 0).2 i).A then (1 : ℝ) else -1) *
      (if ((streams 0).2 i).R then (1 : ℝ) else 0) *
      ((if ((streams 0).2 i).RY then (1 : ℝ) else 0) - 1 / 2)) +
  2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
    (if a then (1 : ℝ) else -1) * streamCellCorrection n d streams x a s)

/-- The projected missing-membership estimate as a statistic of four independent streams. -/
noncomputable def fourStreamEstimate (n d : ℕ)
    (streams : Fin 4 → FiniteSample (Obs d)) : ℝ :=
  clipUnit (fourStreamRawEstimate n d streams)

/-- Uniform masses for the four auxiliary labels. -/
noncomputable def uniformFourMass (_ : Fin 4) : ℝ≥0 := 1 / 4

-- @node: uniformFourMass_sum
/-- [the stated mathematical conclusion holds](goal). -/
lemma uniformFourMass_sum : ∑ i : Fin 4, uniformFourMass i = 1 := by
  norm_num [uniformFourMass]

-- @node: finiteStreamSum_labeledPrefix
private lemma finiteStreamSum_labeledPrefix {n d N : ℕ} (sample : Fin n → Obs d)
    (hN : N ≤ n) (labels : Fin N → Fin 4) (stream : Fin 4)
    (F : Obs d → ℝ) :
    (∑ i : Fin (((labeledPrefix sample N hN labels) stream).count),
      F (((labeledPrefix sample N hN labels) stream).2 i)) =
      ∑ i : Fin N, if labels i = stream then
        F (sample ⟨i.val, Nat.lt_of_lt_of_le i.isLt hN⟩) else 0 := by
  classical
  unfold labeledPrefix unshuffle
  change (∑ k : Fin (wordHistogram labels stream),
      F (sample ⟨(wordUnshuffleEquiv labels ⟨stream, k⟩).val,
        lt_of_lt_of_le (wordUnshuffleEquiv labels ⟨stream, k⟩).isLt hN⟩)) = _
  rw [Fintype.sum_equiv (wordFiberEquiv labels stream)
    (fun k ↦ F (sample ⟨(wordUnshuffleEquiv labels ⟨stream, k⟩).val,
      lt_of_lt_of_le (wordUnshuffleEquiv labels ⟨stream, k⟩).isLt hN⟩))
    (fun i ↦ F (sample ⟨i.val, lt_of_lt_of_le i.val.isLt hN⟩))]
  · calc
      (∑ i : {i : Fin N // labels i = stream},
          F (sample ⟨i.val.val, lt_of_lt_of_le i.val.isLt hN⟩)) =
          ∑ i ∈ Finset.univ.filter (fun i ↦ labels i = stream),
            F (sample ⟨i.val, lt_of_lt_of_le i.isLt hN⟩) := by
              symm
              exact Finset.sum_subtype _ (by simp) _
      _ = _ := by rw [Finset.sum_filter]
  · intro k
    congr 3

-- @node: finiteStreamCount_labeledPrefix
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `N`](hyp:N), [the specified input `sample`](hyp:sample), [the specified input `hN`](hyp:hN), [the specified input `labels`](hyp:labels), [the specified input `stream`](hyp:stream), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). -/
lemma finiteStreamCount_labeledPrefix {n d N : ℕ} (sample : Fin n → Obs d)
    (hN : N ≤ n) (labels : Fin N → Fin 4) (stream : Fin 4)
    (E : Obs d → Prop) :
    finiteStreamCount ((labeledPrefix sample N hN labels) stream) E =
      streamCount sample hN labels stream E := by
  classical
  calc
    finiteStreamCount ((labeledPrefix sample N hN labels) stream) E =
        ∑ i : Fin N, if labels i = stream then
          (if E (sample ⟨i.val, Nat.lt_of_lt_of_le i.isLt hN⟩) then (1 : ℝ) else 0)
          else 0 := by
            simpa only [finiteStreamCount] using
              finiteStreamSum_labeledPrefix sample hN labels stream
                (fun o ↦ if E o then (1 : ℝ) else 0)
    _ = streamCount sample hN labels stream E := by
      unfold streamCount
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : labels i = stream <;> simp [hi]

-- @node: fourStreamEstimate_labeledPrefix
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `N`](hyp:N), [the specified input `sample`](hyp:sample), [the specified input `hN`](hyp:hN), [the specified input `labels`](hyp:labels), [the stated mathematical conclusion holds](goal). -/
lemma fourStreamEstimate_labeledPrefix {n d N : ℕ} (sample : Fin n → Obs d)
    (hN : N ≤ n) (labels : Fin N → Fin 4) :
    fourStreamEstimate n d (labeledPrefix sample N hN labels) =
      randomizedEstimate sample hN labels := by
  classical
  have hmain := finiteStreamSum_labeledPrefix sample hN labels 0
    (fun o ↦
      (if o.A then (1 : ℝ) else -1) *
      (if o.R then (1 : ℝ) else 0) *
      ((if o.RY then (1 : ℝ) else 0) - 1 / 2))
  unfold fourStreamEstimate fourStreamRawEstimate randomizedEstimate
  rw [hmain]
  unfold streamCellCorrection streamV streamG streamH streamD streamCpilot streamC streamU
    cellCorrection
  simp_rw [finiteStreamCount_labeledPrefix]

-- @node: tauhatMM_nonfallback_eq_fixedStatistic
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `sample`](hyp:sample), [the specified input `hq`](hyp:hq), [the specified input `d`](hyp:d), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hreg`](hyp:hreg). -/
lemma tauhatMM_nonfallback_eq_fixedStatistic {n d : ℕ} (q : ℝ)
    (sample : Fin n → Obs d) (hq : q ≠ 1)
    (hreg : ¬(ell n < 128 ∨ (d : ℝ) ≥ (n : ℝ) * ell n)) :
    tauhatMM n d q sample =
      fixedStatistic uniformFourMass uniformFourMass_sum
        ((n : NNReal) / 2)
        sample (fourStreamEstimate n d) 0 := by
  rw [fixedStatistic_eq_finite_sum]
  simp [tauhatMM, hq, hreg, auxiliaryCountMass, conditionalStreamAverage,
    fourStreamEstimate_labeledPrefix, uniformFourMass,
    ProbabilityTheory.poissonMeasure_real_singleton]
  apply Finset.sum_congr rfl
  intro N _
  congr 1
  · ring
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro labels _
    rw [div_eq_mul_inv]
    ring

end CausalSmith.Stat.MarNearcompleteFrontier
