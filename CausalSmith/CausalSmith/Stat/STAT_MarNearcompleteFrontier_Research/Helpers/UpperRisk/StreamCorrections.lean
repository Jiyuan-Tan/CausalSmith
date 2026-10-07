module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamCorrectionsBase
-- TEMPORARY: replace with promoted Causalean nested-event ratio module after coordination.
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean

/-!
# Correction branch means for the upper-risk proof

This module proves the light polynomial and heavy ratio branch identities for
the four-stream estimator.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal BigOperators
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

private lemma upper_qPoly_comp_coeff_one (n : ℕ) :
    (((Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).comp
      (1 - Polynomial.C (2 / polyThreshold n) * Polynomial.X)).coeff 1) =
      -(2 / polyThreshold n) * (polyDegree n : ℝ) ^ 2 := by
  rw [show (((Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).comp
      (1 - Polynomial.C (2 / polyThreshold n) * Polynomial.X)).coeff 1) =
    (((Polynomial.Chebyshev.T ℝ (polyDegree n : ℤ)).comp
      (1 - Polynomial.C (2 / polyThreshold n) * Polynomial.X)).derivative.eval 0) by
      rw [← coeff_zero_eq_eval_zero, coeff_derivative]
      norm_num]
  rw [derivative_comp]
  simp [Polynomial.Chebyshev.derivative_T_eval_one]

private lemma upper_qPoly_coeff_zero (n : ℕ) : (qPoly n).coeff 0 = 1 := by
  unfold qPoly
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_divX]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_one,
    if_neg (by norm_num : (1 : ℕ) ≠ 0), zero_sub]
  rw [upper_qPoly_comp_coeff_one]
  have hB : polyThreshold n ≠ 0 := by
    have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    have he' : 1 < Real.exp (1 : ℝ) + (n : ℝ) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hl : 0 < ell n := Real.log_pos (by simpa [ell] using he')
    unfold polyThreshold
    positivity
  have hk : (polyDegree n : ℝ) ≠ 0 := by
    exact_mod_cast (show polyDegree n ≠ 0 by unfold polyDegree; omega)
  simp
  field_simp

private lemma upper_one_sub_qPoly_natDegree_lt (n : ℕ) :
    (1 - qPoly n).natDegree < polyDegree n := by
  let k := polyDegree n
  let L : ℝ[X] := 1 - Polynomial.C (2 / polyThreshold n) * Polynomial.X
  let p : ℝ[X] := 1 - (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp L
  have hk : 1 ≤ k := by unfold k polyDegree; omega
  have hL : L.natDegree ≤ 1 := by
    unfold L
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · simpa using natDegree_C_mul_le (2 / polyThreshold n) (X : ℝ[X])
  have hcomp : ((Polynomial.Chebyshev.T ℝ (k : ℤ)).comp L).natDegree ≤ k := by
    calc
      _ ≤ (Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree * L.natDegree :=
        natDegree_comp_le
      _ ≤ k * 1 := by
        rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
        exact Nat.mul_le_mul_left k hL
      _ = k := by omega
  have hp : p.natDegree ≤ k := by
    unfold p
    exact (natDegree_sub_le _ _).trans (by simpa using hcomp)
  have hdiv : p.divX.natDegree < k := by
    rw [natDegree_divX_eq_natDegree_tsub_one]
    omega
  have hq : (qPoly n).natDegree < k := by
    change (p.divX * C (polyThreshold n / (2 * (k : ℝ) ^ 2))).natDegree < k
    exact (natDegree_mul_C_le _ _).trans_lt hdiv
  exact (natDegree_sub_le _ _).trans_lt (by simpa [k] using hq)

private lemma upper_correctionCoeff_sum (n : ℕ) (z : ℝ) :
    (∑ t ∈ Finset.range (polyDegree n - 1),
      correctionCoeff n (t + 1) * z ^ (t + 1)) = (1 - qPoly n).eval z := by
  let p : ℝ[X] := 1 - qPoly n
  have hk : 1 ≤ polyDegree n := by unfold polyDegree; omega
  have hdeg : p.natDegree < polyDegree n := by
    simpa only [p] using upper_one_sub_qPoly_natDegree_lt n
  have hp0 : p.coeff 0 = 0 := by
    simp [p, upper_qPoly_coeff_zero]
  rw [Polynomial.eval_eq_sum_range' hdeg]
  rw [show polyDegree n = (polyDegree n - 1) + 1 by omega,
    Finset.sum_range_succ']
  simp only [hp0, pow_zero, zero_mul]
  rw [show polyDegree n - 1 + 1 - 1 = polyDegree n - 1 by omega]
  simp only [correctionCoeff, p, add_zero]

private lemma finiteStreamCount_eq_ratioEventCount {d : ℕ}
    (z : FiniteSample (Obs d)) (E : Obs d → Prop) :
    finiteStreamCount z E =
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount
        {o | E o} z := by
  classical
  rcases z with ⟨N, points⟩
  unfold finiteStreamCount
    Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount
    Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.iidEventCount
    FiniteSample.points FiniteSample.count
  rfl

-- @node: upper_stream_light_mean
/-- Equation (5), light branch: the mean polynomial correction is the
centered cell outcome mean times one minus the Chebyshev quotient. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `q`](hyp:q), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_light_mean {n d : ℕ} (P : FullLaw d)
    {q : ℝ} (h : LawClass d q P) (x : Fin d) (a s : Bool) :
    (∫ streams, streamH n d streams x a s ∂fourStreamLaw n P) =
      cellEta P x a s *
        (1 - (qPoly n).eval (streamZ n P x a s)) := by
  classical
  unfold streamH lightCorrection
  rw [integral_finsetSum]
  swap
  · intro t ht
    have hint := upper_stream_factorial_integrable (n := n) (v := t + 1)
      (by omega) P x a s
    have hc := hint.const_mul (correctionCoeff n (t + 1))
    convert hc using 1
    all_goals
      funext streams
      ring
  calc
    (∑ t ∈ Finset.range (polyDegree n - 1),
      ∫ streams,
        correctionCoeff n (t + 1) *
          (streamU d streams x a s - streamC d streams x a s / 2) *
          shiftedFalling (streamC d streams x a s) (t + 1)
        ∂fourStreamLaw n P) =
      ∑ t ∈ Finset.range (polyDegree n - 1),
        correctionCoeff n (t + 1) *
          (cellEta P x a s * (streamZ n P x a s) ^ (t + 1)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [show (fun streams => correctionCoeff n (t + 1) *
          (streamU d streams x a s - streamC d streams x a s / 2) *
          shiftedFalling (streamC d streams x a s) (t + 1)) =
        (fun streams => correctionCoeff n (t + 1) *
          ((streamU d streams x a s - streamC d streams x a s / 2) *
          shiftedFalling (streamC d streams x a s) (t + 1))) by
            funext streams; ring,
        integral_const_mul,
        upper_stream_factorial_moment (n := n) (v := t + 1) (by omega) P h x a s]
    _ = cellEta P x a s *
        (∑ t ∈ Finset.range (polyDegree n - 1),
          correctionCoeff n (t + 1) * (streamZ n P x a s) ^ (t + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = _ := by
      rw [upper_correctionCoeff_sum]
      simp [Polynomial.eval_sub]

-- @node: upper_stream_heavy_mean
/-- Equation (5), heavy branch: the plug-in correction has mean equal to the
centered cell outcome mean times its nonempty-count probability. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `q`](hyp:q), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_heavy_mean {n d : ℕ} (P : FullLaw d)
    {q : ℝ} (h : LawClass d q P) (x : Fin d) (a s : Bool) :
    (∫ streams, streamD d streams x a s ∂fourStreamLaw n P) =
      cellEta P x a s * (1 - Real.exp (-(streamZ n P x a s))) := by
  classical
  let Q := (observedLaw P).toMeasure
  let lam : NNReal := (n : NNReal) / 2 * uniformFourMass 3
  let A : Set (Obs d) := {o | inCell o x a s ∧ o.R = true ∧ o.RY = true}
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  let frac : Set (Obs d) → Set (Obs d) → FiniteSample (Obs d) → ℝ :=
    Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction
  have hA : MeasurableSet A := by measurability
  have hB : MeasurableSet B := by measurability
  have hAB : A ⊆ B := fun o ho => ⟨ho.1, ho.2.1⟩
  have hmap : Measure.map (fun streams => streams 3) (fourStreamLaw n P) =
      finitePoissonSampleLaw Q lam := by
    rw [show fourStreamLaw n P = Measure.pi (fun i : Fin 4 =>
        finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i)) by
      unfold fourStreamLaw Q
      exact labeledStreamLaw_eq_independent _ _ _ _]
    simpa [lam] using (measurePreserving_eval (μ := fun i : Fin 4 =>
      finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i))
      (3 : Fin 4)).map_eq
  have hpoint : ∀ᵐ streams ∂fourStreamLaw n P,
      streamD d streams x a s =
        frac A B (streams 3) - (1 / 2 : ℝ) * frac B B (streams 3) := by
    filter_upwards [streamU_eq_arrivedSuccess_ae (n := n) P x a s] with streams hs
    unfold streamD
    rw [hs]
    have hcountA := finiteStreamCount_eq_ratioEventCount (streams 3)
      (fun o => inCell o x a s ∧ o.R = true ∧ o.RY = true)
    have hcountB := finiteStreamCount_eq_ratioEventCount (streams 3)
      (fun o => inCell o x a s ∧ o.R = true)
    unfold heavyCorrection streamArrivedSuccessCount streamC frac
    rw [hcountA, hcountB]
    unfold Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction
    by_cases hzero :
        Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount B (streams 3) = 0
    · simp [B, hzero]
    · have hpos : 0 <
          Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount B (streams 3) :=
        lt_of_le_of_ne
          (Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount_bounds
            B (streams 3)).1 (Ne.symm hzero)
      simp [B, hzero, hpos]
      rfl
  have hfracInt (C D : Set (Obs d)) (hC : MeasurableSet C)
      (hD : MeasurableSet D) (hCD : C ⊆ D) :
      Integrable (fun streams => frac C D (streams 3)) (fourStreamLaw n P) := by
    apply (integrable_map_measure
      (Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.measurable_successFraction
        hC hD).aestronglyMeasurable (measurable_pi_apply 3).aemeasurable).mp
    rw [hmap]
    exact Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.integrable_successFraction
      _ hC hD hCD
  have htransfer (C D : Set (Obs d)) (hC : MeasurableSet C)
      (hD : MeasurableSet D) :
      (∫ streams, frac C D (streams 3) ∂fourStreamLaw n P) =
        ∫ z, frac C D z ∂finitePoissonSampleLaw Q lam := by
    rw [← hmap]
    exact (integral_map (measurable_pi_apply 3).aemeasurable
      (Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.measurable_successFraction
        hC hD).aestronglyMeasurable).symm
  have hDmean : (∫ streams, streamD d streams x a s ∂fourStreamLaw n P) =
      (∫ z, frac A B z ∂finitePoissonSampleLaw Q lam) -
        (1 / 2 : ℝ) * (∫ z, frac B B z ∂finitePoissonSampleLaw Q lam) := by
    calc
      _ = ∫ streams, (frac A B (streams 3) -
          (1 / 2 : ℝ) * frac B B (streams 3)) ∂fourStreamLaw n P :=
        integral_congr_ae hpoint
      _ = (∫ streams, frac A B (streams 3) ∂fourStreamLaw n P) -
          (1 / 2 : ℝ) * (∫ streams, frac B B (streams 3) ∂fourStreamLaw n P) := by
        rw [integral_sub (hfracInt A B hA hB hAB)
          ((hfracInt B B hB hB Set.Subset.rfl).const_mul (1 / 2 : ℝ)),
          integral_const_mul]
      _ = _ := by rw [htransfer A B hA hB, htransfer B B hB hB]
  have houtcome : outcomeMean (observedLaw P) x a s = (Q A).toReal / (Q B).toReal := by
    unfold outcomeMean
    rw [observed_event_mass_toReal (observedLaw P)
      (fun o => inCell o x a s ∧ o.R = true ∧ o.RY = true),
      observed_event_mass_toReal (observedLaw P)
        (fun o => inCell o x a s ∧ o.R = true)]
    simp only [inCell, and_assoc]
  have houtcomeReal : outcomeMean (observedLaw P) x a s = Q.real A / Q.real B := by
    simpa only [Measure.real] using houtcome
  have hBmass : (Q B).toReal = arrivedCellMass P x a s := by
    rw [show (Q B).toReal = ∑ o : Obs d,
        if inCell o x a s ∧ o.R = true then obsMass (observedLaw P) o else 0 by
      simpa only [Q, B] using
        observed_event_mass_toReal (observedLaw P)
          (fun o => inCell o x a s ∧ o.R = true)]
    simpa only [inCell, arrivedCellMass, and_assoc] using
      observed_arrived_mass P x a s
  have hrate : (lam : ℝ) * (Q B).toReal = streamZ n P x a s := by
    have hlam : (lam : ℝ) = (n : ℝ) / 8 := by
      norm_num [lam, uniformFourMass]
      ring
    rw [hlam, hBmass]
    unfold streamZ
    ring
  have hrateReal : (lam : ℝ) * Q.real B = streamZ n P x a s := by
    simpa only [Measure.real] using hrate
  have hexp : -(lam : ℝ) * Q.real B = -(streamZ n P x a s) := by
    rw [← hrateReal]
    ring
  rw [hDmean]
  by_cases hQB : (Q B).toReal = 0
  · have hQBmeasure : Q B = 0 :=
      (MeasureTheory.measureReal_eq_zero_iff (μ := Q) (s := B)).mp hQB
    have hzeroAB :=
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.finitePoisson_successFraction_mean_of_mass_zero
        Q lam (A := A) hB hQBmeasure
    have hzeroBB :=
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.finitePoisson_successFraction_mean_of_mass_zero
        Q lam (A := B) hB hQBmeasure
    rw [hzeroAB, hzeroBB]
    have hz : streamZ n P x a s = 0 := by rw [← hrate, hQB, mul_zero]
    rw [hz]
    simp
  · have hQBpos : 0 < Q.real B := lt_of_le_of_ne measureReal_nonneg (Ne.symm hQB)
    have hQBReal : Q.real B ≠ 0 := ne_of_gt hQBpos
    have hmeanAB :=
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.finitePoisson_successFraction_mean
        Q lam hA hB hAB hQBpos
    have hmeanBB :=
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.finitePoisson_successFraction_mean
        Q lam hB hB Set.Subset.rfl hQBpos
    rw [hmeanAB, hmeanBB, ← houtcomeReal, hexp]
    unfold cellEta
    rw [div_self hQBReal]
    ring

end CausalSmith.Stat.MarNearcompleteFrontier
