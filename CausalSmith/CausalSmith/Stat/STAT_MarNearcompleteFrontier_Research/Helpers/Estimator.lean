module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Missing-membership estimator and clipped interval

All Poisson and four-stream randomization is averaged out by a finite sum. The `N > n`
Poisson tail has value zero, so the displayed finite sum is the unconditional auxiliary
expectation. The polynomial coefficients are taken from the exact Chebyshev quotient.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators

/-- Projection onto the estimator and estimand range. -/
noncomputable def clipUnit (z : ℝ) : ℝ := max (-1) (min 1 z)

/-- The degree used in the light-cell correction. -/
noncomputable def polyDegree (n : ℕ) : ℕ := max 1 (Nat.floor (ell n / 64))

/-- The polynomial threshold. -/
noncomputable def polyThreshold (n : ℕ) : ℝ := 256 * ell n

/-- The Chebyshev quotient `Q_k`, with removable value one at zero. -/
noncomputable def qPoly (n : ℕ) : ℝ[X] :=
  let k := polyDegree n
  let B := polyThreshold n
  (1 - (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
    (1 - Polynomial.C (2 / B) * Polynomial.X)).divX *
      Polynomial.C (B / (2 * (k : ℝ) ^ 2))
  -- @realizes Cheb(first-kind Chebyshev T_k in light-cell quotient)

/-- Coefficient `a_v` of `1-Q_k`. -/
noncomputable def correctionCoeff (n v : ℕ) : ℝ :=
  (1 - qPoly n).coeff v

/-- Falling factorial `(C-1)_{v-1}` for a positive index `v`. -/
def shiftedFalling (C : ℝ) (v : ℕ) : ℝ :=
  ∏ t ∈ Finset.range (v - 1), (C - 1 - (t : ℝ))

/-- A record belongs to the specified observed cell. -/
def inCell {d : ℕ} (o : Obs d) (x : Fin d) (a s : Bool) : Prop :=
  o.X = x ∧ o.A = a ∧ o.S = s

/-- Count observations in an auxiliary stream satisfying a given condition. -/
noncomputable def streamCount {n d N : ℕ} (sample : Fin n → Obs d)
    (hN : N ≤ n) (labels : Fin N → Fin 4) (stream : Fin 4)
    (E : Obs d → Prop) : ℝ := by
  classical
  exact ∑ i : Fin N,
    if labels i = stream ∧ E (sample ⟨i.val, Nat.lt_of_lt_of_le i.isLt hN⟩)
    then 1 else 0

/-- Light-cell factorial-polynomial correction. -/
noncomputable def lightCorrection (n : ℕ) (C U : ℝ) : ℝ :=
  ∑ t ∈ Finset.range (polyDegree n - 1),
    correctionCoeff n (t + 1) * (U - C / 2) * shiftedFalling C (t + 1)

/-- Heavy-cell plug-in correction. -/
noncomputable def heavyCorrection (C U : ℝ) : ℝ :=
  if 0 < C then U / C - 1 / 2 else 0

/-- One cell's missing-membership correction using streams two through four. -/
noncomputable def cellCorrection {n d N : ℕ} (sample : Fin n → Obs d)
    (hN : N ≤ n) (labels : Fin N → Fin 4) (x : Fin d) (a s : Bool) : ℝ :=
  let m : ℝ := (n : ℝ) / 8
  let V := streamCount sample hN labels 1
    (fun o => inCell o x a s ∧ o.R = false) / m
  let Cpilot := streamCount sample hN labels 2
    (fun o => inCell o x a s ∧ o.R = true)
  let C := streamCount sample hN labels 3
    (fun o => inCell o x a s ∧ o.R = true)
  let U := streamCount sample hN labels 3
    (fun o => inCell o x a s ∧ o.RY = true)
  V * (if Cpilot ≤ polyThreshold n / 4 then lightCorrection n C U
    else heavyCorrection C U)

/-- One four-stream randomized estimate, already clipped to `[-1,1]`. -/
noncomputable def randomizedEstimate {n d N : ℕ} (sample : Fin n → Obs d)
    (hN : N ≤ n) (labels : Fin N → Fin 4) : ℝ :=
  let m : ℝ := (n : ℝ) / 8
  clipUnit (
    2 / m * (∑ i : Fin N,
      if labels i = 0 then
        (if (sample ⟨i.val, Nat.lt_of_lt_of_le i.isLt hN⟩).A then (1 : ℝ) else -1) *
        (if (sample ⟨i.val, Nat.lt_of_lt_of_le i.isLt hN⟩).R then (1 : ℝ) else 0) *
        ((if (sample ⟨i.val, Nat.lt_of_lt_of_le i.isLt hN⟩).RY then (1 : ℝ) else 0) - 1 / 2)
      else 0) +
    2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      (if a then (1 : ℝ) else -1) * cellCorrection sample hN labels x a s))

/-- Auxiliary Poisson probability for the uncapped count. -/
noncomputable def auxiliaryCountMass (n N : ℕ) : ℝ :=
  Real.exp (-(n : ℝ) / 2) * ((n : ℝ) / 2) ^ N / (Nat.factorial N : ℝ)

/-- Averaging all iid uniform four-stream assignments at a fixed count. -/
noncomputable def conditionalStreamAverage {n d : ℕ} (sample : Fin n → Obs d)
    (N : ℕ) (hN : N ≤ n) : ℝ :=
  (∑ labels : Fin N → Fin 4, randomizedEstimate sample hN labels) / (4 : ℝ) ^ N

/-- Projected complete-outcome Horvitz--Thompson randomized difference. -/
noncomputable def completeHT {n d : ℕ} (sample : Fin n → Obs d) : ℝ :=
  clipUnit (2 / (n : ℝ) * ∑ i : Fin n,
    (if (sample i).A then (1 : ℝ) else -1) *
      (if (sample i).RY then (1 : ℝ) else 0))

/-- Projected centered arrived-outcome fallback. -/
noncomputable def fallbackHT {n d : ℕ} (sample : Fin n → Obs d) : ℝ :=
  clipUnit (2 / (n : ℝ) * ∑ i : Fin n,
    (if (sample i).A then (1 : ℝ) else -1) *
      (if (sample i).R then (1 : ℝ) else 0) *
      ((if (sample i).RY then (1 : ℝ) else 0) - 1 / 2))

-- @node: def:mm-estimator
/-- [The total missing-membership estimator](goal) for [sample size](hyp:n),
[baseline dimension](hyp:d), [known arrival floor](hyp:q), and [observed sample](hyp:sample).
On the full Cartesian record space, Yobs is the supplied fifth coordinate RY. Stream four's
U count uses the supplied mark RY=true; on the observation-map support this is the
arrived-success count. The estimator averages the clipped four-stream estimate over
Poisson(n/2) counts and uniform stream labels, returning zero for N>n. Its q=1 branch is
the projected complete-outcome difference using Yobs; the small-logarithm or large-dimension
fallback is the projected centered arrived-outcome difference using R(Yobs-1/2). -/
noncomputable def tauhatMM (n d : ℕ) (q : ℝ) (sample : Fin n → Obs d) : ℝ :=
  if q = 1 then completeHT sample
  else if ell n < 128 ∨ (d : ℝ) ≥ (n : ℝ) * ell n then fallbackHT sample
  else ∑ N : Fin (n + 1),
    auxiliaryCountMass n N.val *
      conditionalStreamAverage sample N.val (Nat.le_of_lt_succ N.isLt)
  -- @realizes tauhat_MM(complete, fallback, and four-stream Poissonized branches)

/-- For [a sample size](hyp:n), [a covariate dimension](hyp:d), and [an arrival floor](hyp:q), [the missing-membership estimator is measurable as a function of the observed sample](goal). -/
lemma measurable_tauhatMM (n d : ℕ) (q : ℝ) : Measurable (tauhatMM n d q) := by
  fun_prop
/-- For [an observed sample](hyp:o), [the missing-membership estimate lies in the treatment-effect interval from minus one to one](goal). -/
lemma tauhatMM_range (n d : ℕ) (q : ℝ) (o : Fin n → Obs d) :
    tauhatMM n d q o ∈ Set.Icc (-1) 1 := by
  have clip_range (z : ℝ) : clipUnit z ∈ Set.Icc (-1) 1 := by
    simp only [clipUnit, Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  by_cases hq : q = 1
  · simp only [tauhatMM, hq, ↓reduceIte, completeHT]
    exact clip_range _
  by_cases hb : ell n < 128 ∨ (d : ℝ) ≥ (n : ℝ) * ell n
  · simp only [tauhatMM, hq, ↓reduceIte, hb, fallbackHT]
    exact clip_range _
  have hterm (N : Fin (n + 1)) : 0 ≤ auxiliaryCountMass n N.val := by
    unfold auxiliaryCountMass
    positivity
  have hsum : (∑ N : Fin (n + 1), auxiliaryCountMass n N.val) ≤ 1 := by
    let r : NNReal := ⟨(n : ℝ) / 2, by positivity⟩
    have heq (k : ℕ) : auxiliaryCountMass n k = poissonPMFReal r k := by
      change _ = Real.exp (-((n : ℝ) / 2)) * ((n : ℝ) / 2) ^ k / (Nat.factorial k : ℝ)
      simp only [auxiliaryCountMass]
      ring
    rw [Fin.sum_univ_eq_sum_range]
    simp_rw [heq]
    exact sum_le_hasSum (Finset.range (n + 1))
      (fun k _ => poissonPMFReal_nonneg) (poissonPMFRealSum r)
  have havg (N : Fin (n + 1)) :
      conditionalStreamAverage o N.val (Nat.le_of_lt_succ N.isLt) ∈ Set.Icc (-1) 1 := by
    let hN := Nat.le_of_lt_succ N.isLt
    have hp : (0 : ℝ) < 4 ^ N.val := pow_pos (by norm_num) _
    have hcount : (∑ labels : Fin N.val → Fin 4, (1 : ℝ)) = 4 ^ N.val := by
      simp [Fintype.card_fun]
    have hupper : (∑ labels : Fin N.val → Fin 4, randomizedEstimate o hN labels) ≤
        4 ^ N.val := by
      calc
        _ ≤ ∑ labels : Fin N.val → Fin 4, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro labels _
          exact (clip_range _).2
        _ = _ := hcount
    have hlower : -(4 : ℝ) ^ N.val ≤
        ∑ labels : Fin N.val → Fin 4, randomizedEstimate o hN labels := by
      calc
        _ = -(∑ labels : Fin N.val → Fin 4, (1 : ℝ)) := by rw [hcount]
        _ = ∑ labels : Fin N.val → Fin 4, (-1 : ℝ) := by simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro labels _
          exact (clip_range _).1
    change -1 ≤ (∑ labels : Fin N.val → Fin 4, randomizedEstimate o hN labels) /
        (4 : ℝ) ^ N.val ∧
      (∑ labels : Fin N.val → Fin 4, randomizedEstimate o hN labels) /
        (4 : ℝ) ^ N.val ≤ 1
    constructor
    · exact (le_div_iff₀ hp).2 (by nlinarith)
    · exact (div_le_iff₀ hp).2 (by nlinarith)
  have hlo : -(∑ N : Fin (n + 1), auxiliaryCountMass n N.val) ≤
      ∑ N : Fin (n + 1), auxiliaryCountMass n N.val *
        conditionalStreamAverage o N.val (Nat.le_of_lt_succ N.isLt) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro N _
    have h := (havg N).1
    have hp := hterm N
    nlinarith
  have hhi : (∑ N : Fin (n + 1), auxiliaryCountMass n N.val *
      conditionalStreamAverage o N.val (Nat.le_of_lt_succ N.isLt)) ≤
      ∑ N : Fin (n + 1), auxiliaryCountMass n N.val := by
    apply Finset.sum_le_sum
    intro N _
    have h := (havg N).2
    have hp := hterm N
    nlinarith
  simp only [tauhatMM, hq, ↓reduceIte, hb, Set.mem_Icc]
  constructor <;> linarith

/-- A numerical constant certifying the estimator's uniform upper risk. -/
def UpperRiskCertificate (CU : ℝ) : Prop :=
  0 < CU ∧
  ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d → q ∈ Set.Icc ((1 : ℝ) / 2) 1 →
    ∀ (P : ClassLaw d q) (μ : Measure (Fin n → Obs d)),
      IidSample P.val n μ →
      (∫ o, (tauhatMM n d q o - tau P.val) ^ 2 ∂μ) ≤ CU * rate n d q
  -- @realizes C_U(universal positive upper-risk constant)

/-- The upper-risk constant is an explicit input to the confidence radius. -/
noncomputable def intervalRadius (n d : ℕ) (q α CU : ℝ) : ℝ :=
  min 2 (Real.sqrt (CU * rate n d q / α)) -- @realizes h_alpha(min{2,sqrt(C_U r_ndq/alpha)})
  -- @realizes C_U(certified positive universal upper-risk constant)

/-- For [the specified sample size](hyp:n), [dimension](hyp:d), [arrival floor](hyp:q), [confidence level](hyp:α), and [risk constant](hyp:CU), [the confidence-interval radius is nonnegative](goal). -/
lemma intervalRadius_nonneg (n d : ℕ) (q α CU : ℝ) :
    0 ≤ intervalRadius n d q α CU := by
  unfold intervalRadius
  exact le_min (by norm_num) (Real.sqrt_nonneg _)

/-- For [the specified sample size](hyp:n), [dimension](hyp:d), [arrival floor](hyp:q), [confidence level](hyp:α), and [risk constant](hyp:CU), [the lower endpoint of the confidence interval is measurable](goal). -/
lemma measurable_intervalLo (n d : ℕ) (q α CU : ℝ) :
    Measurable (fun o : Fin n → Obs d =>
      max (-1) (tauhatMM n d q o - intervalRadius n d q α CU)) := by
  fun_prop
/-- For [the specified sample size](hyp:n), [dimension](hyp:d), [arrival floor](hyp:q), [confidence level](hyp:α), and [risk constant](hyp:CU), [the upper endpoint of the confidence interval is measurable](goal). -/
lemma measurable_intervalHi (n d : ℕ) (q α CU : ℝ) :
    Measurable (fun o : Fin n → Obs d =>
      min 1 (tauhatMM n d q o + intervalRadius n d q α CU)) := by
  fun_prop
/-- When [the interval radius is nonnegative](hyp:hr), [every resulting confidence interval is ordered and contained in the feasible treatment-effect interval](goal). -/
lemma interval_bounds (n d : ℕ) (q α CU : ℝ) (hr : 0 ≤ intervalRadius n d q α CU) :
    ∀ o : Fin n → Obs d,
      -1 ≤ max (-1) (tauhatMM n d q o - intervalRadius n d q α CU) ∧
      max (-1) (tauhatMM n d q o - intervalRadius n d q α CU) ≤
        min 1 (tauhatMM n d q o + intervalRadius n d q α CU) ∧
      min 1 (tauhatMM n d q o + intervalRadius n d q α CU) ≤ 1 := by
  intro o
  have hrange := tauhatMM_range n d q o
  rcases hrange with ⟨hlo, hhi⟩
  constructor
  · exact le_max_left _ _
  constructor
  · apply max_le
    · exact le_min (by norm_num) (by linarith)
    · exact le_min (by linarith) (by linarith)
  · exact min_le_left _ _

-- @node: def:mm-interval
/-- Clipped connected interval around the total estimator. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `CU`](hyp:CU), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α). -/
noncomputable def intervalMM (n d : ℕ) (q α CU : ℝ)
    (_hCU : UpperRiskCertificate CU) : IntervalProc n d :=
  { lo := fun o => max (-1) (tauhatMM n d q o - intervalRadius n d q α CU)
    hi := fun o => min 1 (tauhatMM n d q o + intervalRadius n d q α CU)
    lo_measurable := measurable_intervalLo n d q α CU
    hi_measurable := measurable_intervalHi n d q α CU
    bounds := interval_bounds n d q α CU (intervalRadius_nonneg n d q α CU) }
  -- @realizes Ihat_MM(clipped interval [max(-1,tauhat-h),min(1,tauhat+h)])

end CausalSmith.Stat.MarNearcompleteFrontier
