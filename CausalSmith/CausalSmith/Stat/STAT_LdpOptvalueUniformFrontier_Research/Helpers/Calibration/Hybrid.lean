module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Calibration.PilotTails

/-!
# Helpers/Calibration/Hybrid

Independent pilot/evaluation blocks, unbiased evaluation means, and exact three-branch
identities for hybrid bias and centered squared error. The C7 variance reduction, inside-window bias and second moment (C5/C8), and
degree calibration (C2) are proved. Pilot tails (C4) and nonnegative inside-window
bias and variance assembly are proved. Outside-window estimates remain open.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n m d : ℕ}
/-- [Independence factors a product of a pilot statistic and an evaluation statistic](goal). -/
-- @node: hybridMean_pilot_mul_evaluation
lemma hybridMean_pilot_mul_evaluation (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) (f g : (Fin m → Fin d → Bool) → ℝ) :
    hybridMean P eps (fun z => f z.1 * g z.2) =
      blockMean (m := m) P eps f * blockMean (m := m) P eps g := by
  letI := vectorBlockLaw_probability P eps m
  exact integral_prod_mul f g

/-- Assume [the stated t condition](hyp:hT). [The central, positive, and negative pilot events partition all outcomes, including ties](goal). -/
-- @node: hybridPilot_partition
lemma hybridPilot_partition (T u : ℝ) (hT : 0 ≤ T) :
    (if |u| ≤ T then (1 : ℝ) else 0) + (if T < u then 1 else 0) +
      (if u < -T then 1 else 0) = 1 := by
  by_cases hc : |u| ≤ T
  · have hu := abs_le.mp hc
    rw [if_pos hc, if_neg (by linarith), if_neg (by linarith)]
    norm_num
  · by_cases hp : T < u
    · rw [if_neg hc, if_pos hp, if_neg (by linarith)]
      norm_num
    · have hn : u < -T := by
        have := not_le.mp hc
        rcases le_total 0 u with hu | hu
        · rw [abs_of_nonneg hu] at this
          exact False.elim (hp this)
        · rw [abs_of_nonpos hu] at this
          linarith
      rw [if_neg hc, if_neg hp, if_pos hn]
      norm_num

/-- [The implemented hybrid is exactly its three disjoint pilot branches](goal). -/
-- @node: hybridColumn_three_branches
lemma hybridColumn_three_branches (eps : ℝ) (D : ℕ) (j : Fin d)
    (z : (Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) :
    let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    hybridColumn eps D j z =
      (if |scaledColumnMean eps j z.1| ≤ T then (1 : ℝ) else 0) *
        polynomialEstimate eps (2*T) D j z.2 +
      (if T < scaledColumnMean eps j z.1 then 1 else 0) * scaledColumnMean eps j z.2 -
      (if scaledColumnMean eps j z.1 < -T then 1 else 0) * scaledColumnMean eps j z.2 := by
  dsimp only
  have hT := hybridThreshold_nonneg (m := m) (d := d) eps
  unfold hybridColumn
  dsimp only
  by_cases hc : |scaledColumnMean eps j z.1| ≤
      4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  · have hu := abs_le.mp hc
    rw [if_pos hc, if_pos hc, if_neg (by linarith), if_neg (by linarith)]
    ring
  · by_cases hp : 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) <
        scaledColumnMean eps j z.1
    · have hpos : 0 < scaledColumnMean eps j z.1 := by linarith
      rw [if_neg hc, if_neg hc, if_pos hpos, if_pos hp, if_neg (by linarith)]
      ring
    · have hn : scaledColumnMean eps j z.1 <
          -(4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)) := by
        have := not_le.mp hc
        rcases le_total 0 (scaledColumnMean eps j z.1) with hu | hu
        · rw [abs_of_nonneg hu] at this
          exact False.elim (hp this)
        · rw [abs_of_nonpos hu] at this
          linarith
      rw [if_neg hc, if_neg hc, if_neg (by linarith), if_pos (by linarith),
        if_neg hp, if_pos hn]
      ring

/-- Assume [the stated t condition](hyp:hT). [Exact pilot branch probabilities sum to one under the finite block law](goal). -/
-- @node: hybridPilot_probability_partition
lemma hybridPilot_probability_partition (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps T : ℝ) (hT : 0 ≤ T) (j : Fin d) :
    blockMean (m := m) P eps (fun z => if |scaledColumnMean eps j z| ≤ T then (1 : ℝ) else 0) +
      blockMean (m := m) P eps (fun z => if T < scaledColumnMean eps j z then (1 : ℝ) else 0) +
      blockMean (m := m) P eps (fun z => if scaledColumnMean eps j z < -T then (1 : ℝ) else 0) = 1 := by
  letI := vectorBlockLaw_probability P eps m
  unfold blockMean
  rw [← integral_add (Integrable.of_finite) (Integrable.of_finite),
    ← integral_add (Integrable.of_finite) (Integrable.of_finite)]
  simp_rw [hybridPilot_partition T _ hT]
  simp

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), and [the stated dm condition](hyp:hDm). [Independence and moment unbiasedness give the exact signed hybrid bias identity (C3)](goal). -/
-- @node: hybridColumn_mean_error_identity
lemma hybridColumn_mean_error_identity (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (hm : 0 < m) (D : ℕ) (hDm : D ≤ m) (j : Fin d) :
    let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    let h := blockMean (m := m) P eps (fun z => if |scaledColumnMean eps j z| ≤ T then (1 : ℝ) else 0)
    let w := blockMean (m := m) P eps (fun z => if scaledColumnMean eps j z < -T then (1 : ℝ) else 0)
    hybridMean (m := m) P eps (hybridColumn eps D j) - contrast P j =
      h * ((2*T) * (chebyshevAbsPoly D).eval (contrast P j / (2*T)) - contrast P j) -
        2 * contrast P j * w := by
  letI := vectorBlockLaw_probability P eps m
  dsimp only
  have hTpos := hybridThreshold_pos eps heps hd hm
  have hfun := funext (hybridColumn_three_branches (m := m) eps D j)
  rw [hfun]
  unfold hybridMean hybridLaw
  rw [integral_sub (Integrable.of_finite) (Integrable.of_finite),
    integral_add (Integrable.of_finite) (Integrable.of_finite)]
  let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  rw [integral_prod_mul (fun z => if |scaledColumnMean eps j z| ≤ T then (1 : ℝ) else 0)
      (polynomialEstimate eps (2*T) D j),
    integral_prod_mul (fun z => if T < scaledColumnMean eps j z then (1 : ℝ) else 0)
      (scaledColumnMean eps j),
    integral_prod_mul (fun z => if scaledColumnMean eps j z < -T then (1 : ℝ) else 0)
      (scaledColumnMean eps j)]
  change blockMean (m := m) P eps _ * blockMean (m := m) P eps _ + blockMean (m := m) P eps _ * blockMean (m := m) P eps _ -
    blockMean (m := m) P eps _ * blockMean (m := m) P eps _ - _ = _
  rw [blockMean_scaledColumnMean P hP eps heps hd hm,
    blockMean_polynomialEstimate P hP eps _ heps (by dsimp [T]; positivity) hd D hDm]
  have hparts := hybridPilot_probability_partition (m := m) P eps _ hTpos.le j
  dsimp [T] at ⊢
  linear_combination (contrast P j) * hparts

/-- [Squaring the hybrid error preserves the three disjoint pilot branches](goal). -/
-- @node: hybridColumn_sq_error_branches
lemma hybridColumn_sq_error_branches (eps x : ℝ) (D : ℕ) (j : Fin d)
    (z : (Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) :
    let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    (hybridColumn eps D j z - x)^2 =
      (if |scaledColumnMean eps j z.1| ≤ T then (1 : ℝ) else 0) *
        (polynomialEstimate eps (2*T) D j z.2 - x)^2 +
      (if T < scaledColumnMean eps j z.1 then 1 else 0) * (scaledColumnMean eps j z.2 - x)^2 +
      (if scaledColumnMean eps j z.1 < -T then 1 else 0) * (-scaledColumnMean eps j z.2 - x)^2 := by
  dsimp only
  rw [hybridColumn_three_branches]
  have hT := hybridThreshold_nonneg (m := m) (d := d) eps
  by_cases hc : |scaledColumnMean eps j z.1| ≤
      4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  · have hu := abs_le.mp hc
    rw [if_pos hc, if_neg (by linarith), if_neg (by linarith)]
    ring
  · by_cases hp : 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) <
        scaledColumnMean eps j z.1
    · rw [if_neg hc, if_pos hp, if_neg (by linarith)]
      ring
    · have hn : scaledColumnMean eps j z.1 <
          -(4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)) := by
        have := not_le.mp hc
        rcases le_total 0 (scaledColumnMean eps j z.1) with hu | hu
        · rw [abs_of_nonneg hu] at this
          exact False.elim (hp this)
        · rw [abs_of_nonpos hu] at this
          linarith
      rw [if_neg hc, if_neg hp, if_pos hn]
      ring

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [positive block size](hyp:hm). [Reversing an unbiased evaluation mean adds exactly four squared contrasts to its error](goal). -/
-- @node: blockMean_negative_scaledColumn_error
lemma blockMean_negative_scaledColumn_error (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (hm : 0 < m) (j : Fin d) :
    blockMean (m := m) P eps (fun z => (-scaledColumnMean eps j z - contrast P j)^2) =
      blockVar (m := m) P eps (scaledColumnMean eps j) + 4 * (contrast P j)^2 := by
  letI := vectorBlockLaw_probability P eps m
  have hmean := blockMean_scaledColumnMean (m := m) P hP eps heps hd hm j
  unfold blockVar
  rw [hmean]
  have hexp : (fun z : Fin m → Fin d → Bool => (-scaledColumnMean eps j z - contrast P j)^2) =
      (fun z => (scaledColumnMean eps j z - contrast P j)^2 +
        4 * contrast P j * scaledColumnMean eps j z) := by
    funext z
    ring
  unfold blockMean
  rw [hexp, integral_add (Integrable.of_finite) (Integrable.of_finite), integral_const_mul]
  change _ + 4 * contrast P j * blockMean (m := m) P eps (scaledColumnMean eps j) = _
  rw [hmean]
  ring

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [positive block size](hyp:hm). [The exact centered-error identity conditions on the three pilot branches (C7 precursor)](goal). -/
-- @node: hybridColumn_centered_error_identity
lemma hybridColumn_centered_error_identity (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (hm : 0 < m) (D : ℕ) (j : Fin d) :
    let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    let h := blockMean (m := m) P eps (fun z => if |scaledColumnMean eps j z| ≤ T then (1 : ℝ) else 0)
    let w := blockMean (m := m) P eps (fun z => if scaledColumnMean eps j z < -T then (1 : ℝ) else 0)
    hybridMean (m := m) P eps (fun z => (hybridColumn eps D j z - contrast P j)^2) =
      h * blockMean (m := m) P eps (fun z => (polynomialEstimate eps (2*T) D j z - contrast P j)^2) +
        (1-h) * blockVar (m := m) P eps (scaledColumnMean eps j) + 4 * (contrast P j)^2 * w := by
  letI := vectorBlockLaw_probability P eps m
  dsimp only
  rw [funext (hybridColumn_sq_error_branches (m := m) eps (contrast P j) D j)]
  unfold hybridMean hybridLaw
  rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
    integral_add (Integrable.of_finite) (Integrable.of_finite)]
  let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  rw [integral_prod_mul (fun z => if |scaledColumnMean eps j z| ≤ T then (1 : ℝ) else 0)
      (fun z => (polynomialEstimate eps (2*T) D j z - contrast P j)^2),
    integral_prod_mul (fun z => if T < scaledColumnMean eps j z then (1 : ℝ) else 0)
      (fun z => (scaledColumnMean eps j z - contrast P j)^2),
    integral_prod_mul (fun z => if scaledColumnMean eps j z < -T then (1 : ℝ) else 0)
      (fun z => (-scaledColumnMean eps j z - contrast P j)^2)]
  have hvar : blockMean (m := m) P eps (fun z => (scaledColumnMean eps j z - contrast P j)^2) =
      blockVar (m := m) P eps (scaledColumnMean eps j) := by
    unfold blockVar
    rw [blockMean_scaledColumnMean P hP eps heps hd hm]
    rfl
  change blockMean (m := m) P eps _ * blockMean (m := m) P eps _ + blockMean (m := m) P eps _ * blockMean (m := m) P eps _ +
    blockMean (m := m) P eps _ * blockMean (m := m) P eps _ = _
  rw [hvar, blockMean_negative_scaledColumn_error P hP eps heps hd hm]
  have hparts := hybridPilot_probability_partition (m := m) P eps T
    (hybridThreshold_nonneg eps) j
  dsimp [T] at *
  linear_combination blockVar (m := m) P eps (scaledColumnMean eps j) * hparts

/-- [A pilot branch indicator has expectation between zero and one](goal). -/
-- @node: hybridPilot_central_probability_range
lemma hybridPilot_central_probability_range (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps T : ℝ) (j : Fin d) :
    blockMean (m := m) P eps (fun z => if |scaledColumnMean eps j z| ≤ T then (1 : ℝ) else 0) ∈
      Set.Icc 0 1 := by
  letI := vectorBlockLaw_probability P eps m
  constructor
  · exact integral_nonneg (fun z => by split <;> norm_num)
  · calc
      _ ≤ ∫ _z : Fin m → Fin d → Bool, (1 : ℝ) ∂vectorBlockLaw P eps m := by
        apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
        intro z
        dsimp only
        split <;> norm_num
      _ = 1 := by simp

/-- [Centering at any fixed target can only increase the hybrid second moment](goal). -/
-- @node: hybridVar_le_centered_error
lemma hybridVar_le_centered_error (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps x : ℝ) (f : ((Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) → ℝ) :
    hybridVar P eps f ≤ hybridMean P eps (fun z => (f z - x)^2) := by
  letI := hybridLaw_probability (m := m) P eps
  have h := variance_le_expectation_sq (μ := hybridLaw P eps m)
    (X := fun z => f z - x) (by fun_prop)
  rw [variance_sub_const (by fun_prop) x] at h
  rw [variance_eq_integral (by fun_prop)] at h
  exact h

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [positive block size](hyp:hm). [The exact branch identity and evaluation variance yield the roadmap's bound (C7)](goal). -/
-- @node: hybridColumn_centered_error_le
lemma hybridColumn_centered_error_le (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (hm : 0 < m) (D : ℕ) (j : Fin d) :
    let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    let h := blockMean (m := m) P eps (fun z => if |scaledColumnMean eps j z| ≤ T then (1 : ℝ) else 0)
    let w := blockMean (m := m) P eps (fun z => if scaledColumnMean eps j z < -T then (1 : ℝ) else 0)
    hybridVar (m := m) P eps (hybridColumn eps D j) ≤
      2*h * blockMean (m := m) P eps (fun z => (polynomialEstimate eps (2*T) D j z)^2) +
        2*h*(contrast P j)^2 + sigmaSquared d m eps + 4*(contrast P j)^2*w := by
  letI := vectorBlockLaw_probability P eps m
  dsimp only
  apply (hybridVar_le_centered_error P eps (contrast P j) _).trans
  rw [hybridColumn_centered_error_identity P hP eps heps hd hm D j]
  let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  let h := blockMean (m := m) P eps (fun z => if |scaledColumnMean eps j z| ≤ T then (1 : ℝ) else 0)
  have hrange := hybridPilot_central_probability_range (m := m) P eps T j
  have hpoly : blockMean (m := m) P eps
      (fun z => (polynomialEstimate eps (2*T) D j z - contrast P j)^2) ≤
      2 * blockMean (m := m) P eps (fun z => (polynomialEstimate eps (2*T) D j z)^2) +
        2 * (contrast P j)^2 := by
    calc
      _ ≤ ∫ z, 2 * (polynomialEstimate eps (2*T) D j z)^2 + 2 * (contrast P j)^2
          ∂vectorBlockLaw P eps m := by
        apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
        intro z
        nlinarith [sq_nonneg (polynomialEstimate eps (2*T) D j z + contrast P j)]
      _ = _ := by
        rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
          integral_const_mul, integral_const]
        simp [blockMean]
  have hv := blockVar_scaledColumnMean_le (m := m) P hP eps heps hd hm j
  have hfirst := mul_le_mul_of_nonneg_left hpoly hrange.1
  have hsecond := mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr hrange.2)
  have hsigma : 0 ≤ sigmaSquared d m eps := by unfold sigmaSquared; positivity
  have hthird : (1-h) * sigmaSquared d m eps ≤ sigmaSquared d m eps := by
    dsimp [h]
    nlinarith [mul_nonneg hrange.1 hsigma]
  dsimp [T, h] at *
  linarith

/-- Assume [the stated l condition](hyp:hL) and [the stated d condition](hyp:hD). [The stipulated even degree obeys both sides of the roadmap's window (C2)](goal). -/
-- @node: hybridDegree_bounds
lemma hybridDegree_bounds (L : ℝ) (hL : 4096 ≤ L) (D : ℕ)
    (hD : D = 2*⌊(1/1024 : ℝ)*L/2⌋₊) :
    Even D ∧ 2 ≤ D ∧ L/2048 ≤ (D : ℝ) ∧ (D : ℝ) ≤ L/1024 := by
  have hnonneg : 0 ≤ (1/1024 : ℝ)*L/2 := by linarith
  have hfloor := Nat.floor_le hnonneg
  have hlt := Nat.lt_floor_add_one ((1/1024 : ℝ)*L/2)
  have hcast : (D : ℝ) = 2 * (⌊(1/1024 : ℝ)*L/2⌋₊ : ℝ) := by
    exact_mod_cast hD
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨⌊(1/1024 : ℝ)*L/2⌋₊, by omega⟩
  · have : (2 : ℝ) ≤ D := by linarith
    exact_mod_cast this
  · linarith
  · linarith

/-- Assume [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), [the stated dm condition](hyp:hDm), and [the stated hx condition](hyp:hx). [Inside the pilot window, the approximation error has the explicit C5 rate](goal). -/
-- @node: hybrid_polynomial_inside_bias
lemma hybrid_polynomial_inside_bias (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hDm : D ≤ m) (j : Fin d)
    (hx : |contrast P j| ≤ 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)) :
    abs (blockMean (m := m) P eps
      (polynomialEstimate eps (8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)) D j) -
      abs (contrast P j)) ≤ 16384 * Real.sqrt (sigmaSquared d m eps) / Real.sqrt (logDim d) := by
  obtain ⟨hEven, hDtwo, hDlower, _⟩ := hybridDegree_bounds (logDim d) hL D hD
  have hLpos : 0 < logDim d := by linarith
  have hsqrt : 0 < Real.sqrt (logDim d) := Real.sqrt_pos.mpr hLpos
  have ha : 0 < 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) := by
    have ht := hybridThreshold_pos (m := m) eps heps hd hm
    linarith
  apply (radius_polynomial_bias_of_gate hCheb P hP eps _ heps ha hd D hEven hDtwo hDm j hx).trans
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < D+1) hsqrt]
  have hsq := Real.sq_sqrt hLpos.le
  have hsigma : 0 ≤ Real.sqrt (sigmaSquared d m eps) := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hsigma (show 0 ≤ 16384 * (D+1 : ℝ) - 8 * logDim d by linarith)]

/-- Assume [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), [the stated hm d condition](hyp:hmD), and [the stated hx condition](hyp:hx). [Within the approximation window, C1 gives the calibrated second moment (C8)](goal). -/
-- @node: hybrid_polynomial_inside_second_bound
lemma hybrid_polynomial_inside_second_bound (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hmD : 2*D ≤ m) (j : Fin d)
    (hx : |contrast P j| ≤ 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)) :
    let a := 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    blockMean (m := m) P eps (fun z => (polynomialEstimate eps a D j z)^2) ≤
      a^2 * Real.exp (logDim d/100) := by
  dsimp only
  let a := 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  obtain ⟨hEven, hDtwo, _, hDupper⟩ := hybridDegree_bounds (logDim d) hL D hD
  have hLpos : 0 < logDim d := by linarith
  have hsigma : 0 ≤ sigmaSquared d m eps := by unfold sigmaSquared; positivity
  have ha : 0 < a := by
    have ht := hybridThreshold_pos (m := m) eps heps hd hm
    dsimp [a]; linarith
  have ha2 : a^2 = 64 * sigmaSquared d m eps * logDim d := by
    dsimp [a]
    nlinarith [Real.sq_sqrt hsigma, Real.sq_sqrt hLpos.le]
  have hx2 : (contrast P j)^2 ≤ a^2 := by
    have hh := sq_le_sq₀ (abs_nonneg (contrast P j)) ha.le |>.mpr hx
    simpa using hh
  have hbase : max 1 (((contrast P j)^2 + 2*D*sigmaSquared d m eps) / a^2) ≤ 2 := by
    apply max_le (by norm_num)
    rw [div_le_iff₀ (sq_pos_of_pos ha)]
    have hh := mul_nonneg hsigma (show 0 ≤ 64 * logDim d - 2 * (D : ℝ) by linarith)
    nlinarith [ha2]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (max 1 (((contrast P j)^2 + 2*D*sigmaSquared d m eps) / a^2))^D ≤ Real.exp D := by
    have hh := pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) (hbase.trans htwo) D
    rw [← Real.exp_nat_mul] at hh
    simpa using hh
  calc
    _ ≤ a^2 * Real.exp (5*D) *
        (max 1 (((contrast P j)^2 + 2*D*sigmaSquared d m eps) / a^2))^D :=
      radius_polynomial_second_bound hCheb P hP eps a heps ha hd hm D hEven hDtwo hmD j
    _ ≤ a^2 * Real.exp (5*D) * Real.exp D :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = a^2 * Real.exp (6*D) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ a^2 * Real.exp (logDim d/100) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
      apply Real.exp_le_exp.mpr
      linarith

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), [the stated dm condition](hyp:hDm), [the stated hx condition](hyp:hx), and [the stated hwindow condition](hyp:hwindow). [C3, C4 and C5 assemble the hybrid bias bound for nonnegative inside-window contrasts](goal). -/
-- @node: hybrid_inside_nonneg_bias
lemma hybrid_inside_nonneg_bias (hMean : BoundedMeanConcentration)
    (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hDm : D ≤ m) (j : Fin d)
    (hx : 0 ≤ contrast P j)
    (hwindow : |contrast P j| ≤ 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)) :
    abs (hybridMean (m := m) P eps (hybridColumn eps D j) - abs (contrast P j)) ≤
      20000 * Real.sqrt (sigmaSquared d m eps) / Real.sqrt (logDim d) := by
  classical
  let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  let h := blockMean (m := m) P eps
    (fun z => if |scaledColumnMean eps j z| ≤ T then (1 : ℝ) else 0)
  let w := blockMean (m := m) P eps
    (fun z => if scaledColumnMean eps j z < -T then (1 : ℝ) else 0)
  have hwr : w = (vectorBlockLaw P eps m).real {z | scaledColumnMean eps j z < -T} := by
    simpa only [w, blockMean, Set.indicator_apply, Set.mem_setOf_eq] using
      (pilot_indicator_probability (m := m) P eps {z | scaledColumnMean eps j z < -T})
  have hw := (hybridPilot_wrong_sign_weighted hMean P hP eps heps hd hm j hx).1
  change contrast P j * (vectorBlockLaw P eps m).real
    {z | scaledColumnMean eps j z < -T} ≤ _ at hw
  rw [← hwr] at hw
  have hw' : contrast P j * w ≤ Real.sqrt (sigmaSquared d m eps) / Real.sqrt (logDim d) := by
    apply hw.trans
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left
      (pilot_exp_tail_le_inv_sqrt (logDim d) (by linarith))
      (Real.sqrt_nonneg (sigmaSquared d m eps))
  have hrange := hybridPilot_central_probability_range (m := m) P eps T j
  have hwp : 0 ≤ w := integral_nonneg (fun z => by split <;> norm_num)
  have hpoly := hybrid_polynomial_inside_bias hCheb P hP eps heps hd hm D hL hD hDm j hwindow
  have ha : 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) = 2*T := by
    dsimp [T]; ring
  rw [ha, blockMean_polynomialEstimate P hP eps _ heps
    (by have := hybridThreshold_pos (m := m) eps heps hd hm; dsimp [T]; positivity)
    hd D hDm j, abs_of_nonneg hx] at hpoly
  rw [abs_of_nonneg hx, hybridColumn_mean_error_identity P hP eps heps hd hm D hDm j]
  change abs (h * ((2*T) * (chebyshevAbsPoly D).eval (contrast P j / (2*T)) -
    contrast P j) - 2 * contrast P j * w) ≤ _
  have herr := abs_sub (h * ((2*T) * (chebyshevAbsPoly D).eval (contrast P j / (2*T)) -
    contrast P j)) (2 * contrast P j * w)
  rw [abs_mul, abs_of_nonneg hrange.1,
    abs_of_nonneg (by positivity : 0 ≤ 2 * contrast P j * w)] at herr
  have hp := mul_le_mul_of_nonneg_left hpoly hrange.1
  have hunit := mul_le_mul_of_nonneg_right hrange.2
    (show 0 ≤ 16384 * Real.sqrt (sigmaSquared d m eps) / Real.sqrt (logDim d) by positivity)
  dsimp only [h] at hp hunit herr ⊢
  have hnonneg : 0 ≤ Real.sqrt (sigmaSquared d m eps) / Real.sqrt (logDim d) := by positivity
  simp only [div_eq_mul_inv] at hw' hp hunit herr hnonneg ⊢
  nlinarith

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), [the stated hm d condition](hyp:hmD), [the stated hx condition](hyp:hx), and [the stated hwindow condition](hyp:hwindow). [C4, C7 and C8 assemble the hybrid variance bound for nonnegative inside contrasts](goal). -/
-- @node: hybrid_inside_nonneg_variance
lemma hybrid_inside_nonneg_variance (hMean : BoundedMeanConcentration)
    (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hmD : 2*D ≤ m) (j : Fin d)
    (hx : 0 ≤ contrast P j)
    (hwindow : |contrast P j| ≤ 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)) :
    hybridVar (m := m) P eps (hybridColumn eps D j) ≤
      400 * sigmaSquared d m eps * logDim d * Real.exp (logDim d/100) := by
  classical
  let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  let h := blockMean (m := m) P eps
    (fun z => if |scaledColumnMean eps j z| ≤ T then (1 : ℝ) else 0)
  let w := blockMean (m := m) P eps
    (fun z => if scaledColumnMean eps j z < -T then (1 : ℝ) else 0)
  have hs : 0 ≤ sigmaSquared d m eps := by unfold sigmaSquared; positivity
  have hT2 : (2*T)^2 = 64 * sigmaSquared d m eps * logDim d := by
    dsimp [T]
    nlinarith [Real.sq_sqrt hs, Real.sq_sqrt (show 0 ≤ logDim d by linarith)]
  have hwr : w = (vectorBlockLaw P eps m).real {z | scaledColumnMean eps j z < -T} := by
    simpa only [w, blockMean, Set.indicator_apply, Set.mem_setOf_eq] using
      (pilot_indicator_probability (m := m) P eps {z | scaledColumnMean eps j z < -T})
  have hw := (hybridPilot_wrong_sign_weighted hMean P hP eps heps hd hm j hx).2
  change (contrast P j)^2 * (vectorBlockLaw P eps m).real
    {z | scaledColumnMean eps j z < -T} ≤ _ at hw
  rw [← hwr] at hw
  have he : Real.exp (-8 * logDim d) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hw' : (contrast P j)^2 * w ≤ sigmaSquared d m eps :=
    hw.trans (by simpa using mul_le_mul_of_nonneg_left he hs)
  have hrange := hybridPilot_central_probability_range (m := m) P eps T j
  have ha : 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) = 2*T := by
    dsimp [T]; ring
  have hp := hybrid_polynomial_inside_second_bound hCheb P hP eps heps hd hm
    D hL hD hmD j hwindow
  dsimp only at hp
  rw [ha, hT2] at hp
  have hC7 := hybridColumn_centered_error_le P hP eps heps hd hm D j
  change hybridVar P eps (hybridColumn eps D j) ≤
    2*h * blockMean P eps (fun z => (polynomialEstimate eps (2*T) D j z)^2) +
    2*h*(contrast P j)^2 + sigmaSquared d m eps + 4*(contrast P j)^2*w at hC7
  have hpoly := (mul_le_mul_of_nonneg_left hp hrange.1).trans
    (by
      simpa using mul_le_mul_of_nonneg_right hrange.2
        (show 0 ≤ 64 * sigmaSquared d m eps * logDim d * Real.exp (logDim d/100) by positivity))
  have hx2 : (contrast P j)^2 ≤ 64 * sigmaSquared d m eps * logDim d := by
    have hh := sq_le_sq₀ (abs_nonneg (contrast P j))
      (show 0 ≤ 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) by positivity) |>.mpr hwindow
    rw [ha, hT2] at hh
    simpa using hh
  have hx2' := (mul_le_mul_of_nonneg_left hx2 hrange.1).trans
    (by
      simpa using mul_le_mul_of_nonneg_right hrange.2 (by positivity :
        0 ≤ 64 * sigmaSquared d m eps * logDim d))
  have he' : 1 ≤ Real.exp (logDim d/100) := Real.one_le_exp_iff.mpr (by linarith)
  have hscale : sigmaSquared d m eps * logDim d ≤
      sigmaSquared d m eps * logDim d * Real.exp (logDim d/100) := by
    simpa using mul_le_mul_of_nonneg_left he' (by positivity : 0 ≤ sigmaSquared d m eps * logDim d)
  have hsL : sigmaSquared d m eps ≤ sigmaSquared d m eps * logDim d := by
    nlinarith [mul_nonneg hs (show 0 ≤ logDim d - 1 by linarith)]
  change h * _ ≤ _ at hpoly
  change h * _ ≤ _ at hx2'
  nlinarith


end CausalSmith.Stat.LdpOptvalueUniformFrontier
