module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Calibration.Hybrid
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Calibration.Reflection

/-!
# Outside-window hybrid calibration

Polynomial growth and Gaussian pilot suppression for steps C6 and C9 of finite calibration.
Bias and variance assembly for all causal contrasts, inside and outside the window,
using reflection for negative contrasts. Combined-column MSE and the final
finite-calibration theorem are assembled in Calibration.Assembly.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {m d : ℕ}

/-- Assume [the stated hy condition](hyp:hy). [The logarithmic growth of an outside-window parameter is at most half its square](goal). -/
-- @node: hybrid_outside_log_bound
lemma hybrid_outside_log_bound (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ y^2/2 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < y by linarith)
  nlinarith [sq_nonneg (y-1)]

/-- Assume [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the stated even condition](hyp:hEven), [polynomial degree at least two](hyp:hD), and [the stated hy condition](hyp:hy). [The finite coefficient envelope bounds the polynomial beyond its approximation window](goal). -/
-- @node: hybrid_outside_polynomial_growth
lemma hybrid_outside_polynomial_growth (hCheb : CaiLowChebyshevApproximation)
    (D : ℕ) (hEven : Even D) (hD : 2 ≤ D) (y : ℝ) (hy : 1 ≤ y) :
    |(chebyshevAbsPoly D).eval y| ≤ Real.exp (3*D) * y^D := by
  classical
  have hy0 : 0 ≤ y := by linarith
  have hc (v : ℕ) (hv : v ∈ Finset.range (D+1)) :
      |(chebyshevAbsPoly D).coeff v * y^v| ≤ Real.exp (3*(D : ℝ)/2) * y^D := by
    have hvD : v ≤ D := by have := Finset.mem_range.mp hv; omega
    have hcoeff := (hCheb D hEven hD).2 v hvD
    rw [Real.rpow_def_of_pos (by norm_num)] at hcoeff
    have hlog : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at this
      exact this
    have hcoeff' : |(chebyshevAbsPoly D).coeff v| ≤ Real.exp (3*(D : ℝ)/2) :=
      hcoeff.trans (Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) D]))
    rw [abs_mul, abs_of_nonneg (pow_nonneg hy0 v)]
    exact mul_le_mul hcoeff' (pow_le_pow_right₀ hy hvD)
      (pow_nonneg hy0 v) (Real.exp_pos _).le
  rw [Polynomial.eval_eq_sum_range' (n := D+1) (by
    have := chebyshevAbsPoly_natDegree_le D; omega)]
  calc
    _ ≤ ∑ v ∈ Finset.range (D+1), |(chebyshevAbsPoly D).coeff v * y^v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ Finset.range (D+1), Real.exp (3*(D : ℝ)/2) * y^D :=
      Finset.sum_le_sum hc
    _ = (D+1 : ℝ) * (Real.exp (3*(D : ℝ)/2) * y^D) := by simp
    _ ≤ Real.exp D * (Real.exp (3*(D : ℝ)/2) * y^D) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (D : ℝ)]) (by positivity)
    _ = Real.exp ((D : ℝ)+3*D/2) * y^D := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) D]))
      (pow_nonneg hy0 D)

/-- Assume [the stated l condition](hyp:hL), [the stated hy condition](hyp:hy), and [the stated d condition](hyp:hD). [At the calibrated degree, the outside pilot tail dominates polynomial growth (C6)](goal). -/
-- @node: hybrid_outside_growth_suppression
lemma hybrid_outside_growth_suppression (L y : ℝ) (hL : 1 ≤ L) (hy : 1 ≤ y)
    (D : ℕ) (hD : (D : ℝ) ≤ L/1024) :
    Real.exp (-8*L*y^2) * (Real.exp (3*D) * y^D) ≤ Real.exp (-7*L*y^2) := by
  have hypos : 0 < y := by linarith
  have hlog := hybrid_outside_log_bound y hy
  have hy2 : 1 ≤ y^2 := by nlinarith
  have hpow : y^D = Real.exp ((D : ℝ) * Real.log y) := by
    rw [Real.exp_nat_mul, Real.exp_log hypos]
  rw [hpow, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hfirst : 3*(D : ℝ) ≤ 3*L/1024*y^2 := by
    nlinarith [mul_nonneg (show 0 ≤ L by linarith) (show 0 ≤ y^2-1 by linarith)]
  have hsecond := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) D)
  have hthird := mul_le_mul_of_nonneg_right hD (show 0 ≤ y^2/2 by positivity)
  have hLy : 0 ≤ L*y^2 := by positivity
  nlinarith

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), and [the stated hx condition](hyp:hx). [The actual outside-window pilot tail has the normalized exponent used in C6](goal). -/
-- @node: hybridPilot_central_normalized_tail
lemma hybridPilot_central_normalized_tail (hMean : BoundedMeanConcentration)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m) (j : Fin d)
    (hL : 1 ≤ logDim d)
    (hx : 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) ≤ contrast P j) :
    let a := 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    let T := a/2
    (vectorBlockLaw P eps m).real {z | |scaledColumnMean eps j z| ≤ T} ≤
      Real.exp (-8 * logDim d * (contrast P j / a)^2) := by
  dsimp only
  have hb := pilot_noiseScale_pos eps heps hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < sigmaSquared d m eps := div_pos (sq_pos_of_pos hb) hmR
  let a := 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha2 : a^2 = 64 * sigmaSquared d m eps * logDim d := by
    dsimp [a]
    nlinarith [Real.sq_sqrt hs.le, Real.sq_sqrt (show 0 ≤ logDim d by linarith)]
  have ht : a/2 = 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) := by
    dsimp [a]; ring
  change (vectorBlockLaw P eps m).real {z | |scaledColumnMean eps j z| ≤ a/2} ≤ _
  rw [ht]
  apply (hybridPilot_central_tail hMean P hP eps heps hd hm j hx).trans_eq
  congr 1
  rw [div_pow, ha2]
  field_simp
  <;> ring

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), [the stated dm condition](hyp:hDm), and [the stated hx condition](hyp:hx). [Pilot suppression times unbiased polynomial growth gives the first outside C6 bound](goal). -/
-- @node: hybrid_outside_weighted_polynomial
lemma hybrid_outside_weighted_polynomial (hMean : BoundedMeanConcentration)
    (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hDm : D ≤ m) (j : Fin d)
    (hx : 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) ≤ contrast P j) :
    let a := 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    (vectorBlockLaw P eps m).real {z | |scaledColumnMean eps j z| ≤ a/2} *
      |blockMean (m := m) P eps (polynomialEstimate eps a D j)| ≤
      a * Real.exp (-7 * logDim d * (contrast P j / a)^2) := by
  dsimp only
  let a := 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  have hb := pilot_noiseScale_pos eps heps hd
  have hs : 0 < sigmaSquared d m eps := div_pos (sq_pos_of_pos hb) (by exact_mod_cast hm)
  have ha : 0 < a := by dsimp [a]; positivity
  have hy : 1 ≤ contrast P j / a := by
    rw [le_div_iff₀ ha]; simpa [a] using hx
  have hEven : Even D := ⟨⌊(1/1024 : ℝ)*logDim d/2⌋₊, by omega⟩
  have hfloor := Nat.lt_floor_add_one ((1/1024 : ℝ)*logDim d/2)
  have hcast : (D : ℝ) = 2 * (⌊(1/1024 : ℝ)*logDim d/2⌋₊ : ℝ) := by exact_mod_cast hD
  have hDtwo : 2 ≤ D := by
    have : (2 : ℝ) ≤ D := by linarith
    exact_mod_cast this
  have hDupper : (D : ℝ) ≤ logDim d/1024 := by
    have hf := Nat.floor_le (show 0 ≤ (1/1024 : ℝ)*logDim d/2 by linarith)
    linarith
  have htail := hybridPilot_central_normalized_tail hMean P hP eps heps hd hm j (by linarith) hx
  have hgrowth := hybrid_outside_polynomial_growth hCheb D hEven hDtwo _ hy
  have hsuppress := hybrid_outside_growth_suppression (logDim d) (contrast P j/a)
    (by linarith) hy D hDupper
  rw [blockMean_polynomialEstimate P hP eps a heps ha.ne' hd D hDm j,
    abs_mul, abs_of_pos ha]
  calc
    _ ≤ Real.exp (-8 * logDim d * (contrast P j/a)^2) *
        (a * (Real.exp (3*D) * (contrast P j/a)^D)) :=
      mul_le_mul htail (mul_le_mul_of_nonneg_left hgrowth ha.le)
        (by positivity) (Real.exp_pos _).le
    _ = a * (Real.exp (-8 * logDim d * (contrast P j/a)^2) *
        (Real.exp (3*D) * (contrast P j/a)^D)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsuppress ha.le

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), and [the stated hx condition](hyp:hx). [The outside pilot tail also suppresses the first and second contrast powers in C6](goal). -/
-- @node: hybrid_outside_weighted_contrast
lemma hybrid_outside_weighted_contrast (hMean : BoundedMeanConcentration)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m) (j : Fin d)
    (hL : 4096 ≤ logDim d)
    (hx : 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) ≤ contrast P j) :
    let a := 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    let h := (vectorBlockLaw P eps m).real {z | |scaledColumnMean eps j z| ≤ a/2}
    h * contrast P j ≤ a * Real.exp (-7 * logDim d * (contrast P j/a)^2) ∧
    h * (contrast P j)^2 ≤ a^2 * Real.exp (-7 * logDim d * (contrast P j/a)^2) := by
  dsimp only
  let a := 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  let y := contrast P j/a
  let h := (vectorBlockLaw P eps m).real {z | |scaledColumnMean eps j z| ≤ a/2}
  have hb := pilot_noiseScale_pos eps heps hd
  have hs : 0 < sigmaSquared d m eps := div_pos (sq_pos_of_pos hb) (by exact_mod_cast hm)
  have ha : 0 < a := by dsimp [a]; positivity
  have hy : 1 ≤ y := by dsimp [y]; rw [le_div_iff₀ ha]; simpa [a] using hx
  have htail : h ≤ Real.exp (-8*logDim d*y^2) :=
    hybridPilot_central_normalized_tail hMean P hP eps heps hd hm j (by linarith) hx
  have hweight (k : ℕ) (hk : k ≤ 2) : h * y^k ≤ Real.exp (-7*logDim d*y^2) := by
    have hkR : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    have he : 1 ≤ Real.exp (3*k) := Real.one_le_exp_iff.mpr (by positivity)
    have hy0 : 0 ≤ y^k := pow_nonneg (by linarith) k
    calc
      _ ≤ Real.exp (-8*logDim d*y^2) * y^k := mul_le_mul_of_nonneg_right htail hy0
      _ ≤ Real.exp (-8*logDim d*y^2) * (Real.exp (3*k) * y^k) :=
        mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_right he hy0])
          (Real.exp_pos _).le
      _ ≤ _ := hybrid_outside_growth_suppression _ _ (by linarith) hy k (by linarith)
  have hxy : contrast P j = a*y := by dsimp [y]; field_simp
  change h * contrast P j ≤ a * Real.exp (-7*logDim d*y^2) ∧
    h * (contrast P j)^2 ≤ a^2 * Real.exp (-7*logDim d*y^2)
  constructor
  · have hh := mul_le_mul_of_nonneg_left (hweight 1 (by omega)) ha.le
    simpa only [pow_one, hxy, mul_left_comm] using hh
  · have hh := mul_le_mul_of_nonneg_left (hweight 2 (by omega)) (sq_nonneg a)
    rw [hxy, mul_pow]
    nlinarith [hh]

/-- Assume [the stated l condition](hyp:hL). [The exponentially small C6 residual is at most the reciprocal log dimension](goal). -/
-- @node: hybrid_outside_exp_residual
lemma hybrid_outside_exp_residual (L : ℝ) (hL : 1 ≤ L) :
    Real.exp (-7*L) ≤ 1/L := by
  have hbound : L ≤ Real.exp (7*L) := by linarith [Real.add_one_le_exp (7*L)]
  apply (le_div_iff₀ (by linarith : 0 < L)).mpr
  have hh := mul_le_mul_of_nonneg_right hbound (Real.exp_pos (-7*L)).le
  rw [← Real.exp_add] at hh
  have he : 7*L + -7*L = 0 := by ring
  simpa [he, mul_comm] using hh

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), [the stated dm condition](hyp:hDm), and [the stated hx condition](hyp:hx). [C3, C4 and C6 give the hybrid bias bound outside the window for nonnegative contrasts](goal). -/
-- @node: hybrid_outside_nonneg_bias
lemma hybrid_outside_nonneg_bias (hMean : BoundedMeanConcentration)
    (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hDm : D ≤ m) (j : Fin d)
    (hx : 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) ≤ contrast P j) :
    abs (hybridMean (m := m) P eps (hybridColumn eps D j) - abs (contrast P j)) ≤
      20000 * Real.sqrt (sigmaSquared d m eps) / Real.sqrt (logDim d) := by
  let a := 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  let T := a/2
  let h := blockMean (m := m) P eps
    (fun z => if |scaledColumnMean eps j z| ≤ T then (1 : ℝ) else 0)
  let w := blockMean (m := m) P eps
    (fun z => if scaledColumnMean eps j z < -T then (1 : ℝ) else 0)
  have ht : T = 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) := by
    dsimp [T, a]; ring
  have hprob : h = (vectorBlockLaw P eps m).real {z | |scaledColumnMean eps j z| ≤ T} := by
    simpa only [h, blockMean, Set.indicator_apply, Set.mem_setOf_eq] using
      (pilot_indicator_probability (m := m) P eps {z | |scaledColumnMean eps j z| ≤ T})
  have wprob : w = (vectorBlockLaw P eps m).real {z | scaledColumnMean eps j z < -T} := by
    simpa only [w, blockMean, Set.indicator_apply, Set.mem_setOf_eq] using
      (pilot_indicator_probability (m := m) P eps {z | scaledColumnMean eps j z < -T})
  have hx0 : 0 ≤ contrast P j := by
    have : 0 ≤ a := by dsimp [a]; positivity
    dsimp [a] at this; linarith
  have hwp : 0 ≤ w := integral_nonneg (fun z => by split <;> norm_num)
  have hrange := hybridPilot_central_probability_range (m := m) P eps T j
  have hp := hybrid_outside_weighted_polynomial hMean hCheb P hP eps heps hd hm D hL hD hDm j hx
  have hxc := (hybrid_outside_weighted_contrast hMean P hP eps heps hd hm j hL hx).1
  change _ ≤ a * Real.exp (-7 * logDim d * (contrast P j/a)^2) at hp hxc
  rw [← hprob] at hp hxc
  have hy : 1 ≤ (contrast P j/a)^2 := by
    have hb := pilot_noiseScale_pos eps heps hd
    have hs : 0 < sigmaSquared d m eps := div_pos (sq_pos_of_pos hb) (by exact_mod_cast hm)
    have ha : 0 < a := by dsimp [a]; positivity
    have hh : 1 ≤ contrast P j/a := by rw [le_div_iff₀ ha]; simpa [a] using hx
    nlinarith
  have he : Real.exp (-7 * logDim d * (contrast P j/a)^2) ≤ 1/logDim d :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans (hybrid_outside_exp_residual _ (by linarith))
  have hscale : a * (1/logDim d) = 8 * Real.sqrt (sigmaSquared d m eps)/Real.sqrt (logDim d) := by
    have hs := Real.sq_sqrt (show 0 ≤ logDim d by linarith)
    have hp : 0 < Real.sqrt (logDim d) := Real.sqrt_pos.mpr (by linarith)
    dsimp [a]
    field_simp
    nlinarith
  have hsmall := mul_le_mul_of_nonneg_left he (show 0 ≤ a by dsimp [a]; positivity)
  rw [hscale] at hsmall
  have hw := (hybridPilot_wrong_sign_weighted hMean P hP eps heps hd hm j hx0).1
  rw [← ht] at hw
  rw [← wprob] at hw
  have hw' := hw.trans (mul_le_mul_of_nonneg_left
    (pilot_exp_tail_le_inv_sqrt (logDim d) (by linarith)) (Real.sqrt_nonneg _))
  have haeq : 2 * (4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)) = a := by
    dsimp [a]; ring
  rw [abs_of_nonneg hx0, hybridColumn_mean_error_identity P hP eps heps hd hm D hDm j, haeq, ← ht]
  change abs (h * (a * (chebyshevAbsPoly D).eval (contrast P j/a) - contrast P j) -
    2 * contrast P j * w) ≤ _
  rw [blockMean_polynomialEstimate P hP eps a heps (by
    have hb := pilot_noiseScale_pos eps heps hd
    have hs : 0 < sigmaSquared d m eps := div_pos (sq_pos_of_pos hb) (by exact_mod_cast hm)
    dsimp [a]; positivity) hd D hDm j] at hp
  have hh0 : 0 ≤ h := hrange.1
  have hsplit := abs_sub (h * (a * (chebyshevAbsPoly D).eval (contrast P j/a)))
    (h * contrast P j + 2 * contrast P j * w)
  rw [abs_mul, abs_of_nonneg hrange.1,
    abs_of_nonneg (by positivity : 0 ≤ h * contrast P j + 2 * contrast P j * w)] at hsplit
  have halg : h * (a * (chebyshevAbsPoly D).eval (contrast P j/a) - contrast P j) -
      2 * contrast P j * w = h * (a * (chebyshevAbsPoly D).eval (contrast P j/a)) -
        (h * contrast P j + 2 * contrast P j * w) := by ring
  rw [halg]
  have hn : 0 ≤ Real.sqrt (sigmaSquared d m eps)/Real.sqrt (logDim d) := by positivity
  change abs (h * _ - _) ≤ h * _ + _ at hsplit
  simp only [div_eq_mul_inv] at hw' hp hxc hsplit hsmall hn ⊢
  nlinarith

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), [the stated dm condition](hyp:hDm), and [the stated hx condition](hyp:hx). [The inside and outside C6 cases cover every nonnegative contrast, including the boundary](goal). -/
-- @node: hybrid_nonneg_bias
lemma hybrid_nonneg_bias (hMean : BoundedMeanConcentration)
    (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hDm : D ≤ m) (j : Fin d)
    (hx : 0 ≤ contrast P j) :
    abs (hybridMean (m := m) P eps (hybridColumn eps D j) - abs (contrast P j)) ≤
      20000 * Real.sqrt (sigmaSquared d m eps) / Real.sqrt (logDim d) := by
  by_cases hwindow : |contrast P j| ≤ 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  · exact hybrid_inside_nonneg_bias hMean hCheb P hP eps heps hd hm D hL hD hDm j hx hwindow
  · apply hybrid_outside_nonneg_bias hMean hCheb P hP eps heps hd hm D hL hD hDm j
    rw [abs_of_nonneg hx] at hwindow
    exact (not_le.mp hwindow).le

/-- Assume [the stated l condition](hyp:hL), [the stated hy condition](hyp:hy), and [the stated d condition](hyp:hD). [Gaussian pilot suppression dominates the squared polynomial growth in C9](goal). -/
-- @node: hybrid_outside_second_growth_suppression
lemma hybrid_outside_second_growth_suppression (L y : ℝ) (hL : 1 ≤ L) (hy : 1 ≤ y)
    (D : ℕ) (hD : (D : ℝ) ≤ L/1024) :
    Real.exp (-8*L*y^2) * (Real.exp (5*D) * (2*y^2)^D) ≤
      Real.exp (-7*L*y^2) := by
  have hypos : 0 < y := by linarith
  have hy2 : 1 ≤ y^2 := by nlinarith
  have hlog := hybrid_outside_log_bound y hy
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : y^(2*D) = Real.exp ((2*D : ℝ) * Real.log y) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.exp_log hypos] using
      (Real.exp_nat_mul (Real.log y) (2*D)).symm
  have hp : (2*y^2)^D ≤ Real.exp D * Real.exp ((2*D : ℝ) * Real.log y) := by
    rw [mul_pow, ← pow_mul, hpow]
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo D
    rw [← Real.exp_nat_mul] at hh
    simpa using mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
  calc
    _ ≤ Real.exp (-8*L*y^2) * (Real.exp (5*D) *
        (Real.exp D * Real.exp ((2*D : ℝ)*Real.log y))) := by
      gcongr
    _ = Real.exp (-8*L*y^2 + (6*D + 2*D*Real.log y)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hfirst : 6*(D : ℝ) ≤ 6*L/1024*y^2 := by
        nlinarith [mul_nonneg (show 0 ≤ L by linarith) (show 0 ≤ y^2-1 by linarith)]
      have hsecond := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*(D : ℝ) by positivity)
      have hthird := mul_le_mul_of_nonneg_right hD (sq_nonneg y)
      have hLy : 0 ≤ L*y^2 := by positivity
      nlinarith

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), [the stated hm d condition](hyp:hmD), and [the stated hx condition](hyp:hx). [C1 and the actual pilot tail yield the outside-window weighted second moment (C9)](goal). -/
-- @node: hybrid_outside_weighted_second_moment
lemma hybrid_outside_weighted_second_moment (hMean : BoundedMeanConcentration)
    (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hmD : 2*D ≤ m) (j : Fin d)
    (hx : 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) ≤ contrast P j) :
    let a := 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    (vectorBlockLaw P eps m).real {z | |scaledColumnMean eps j z| ≤ a/2} *
      blockMean (m := m) P eps (fun z => (polynomialEstimate eps a D j z)^2) ≤
      a^2 * Real.exp (-7 * logDim d * (contrast P j/a)^2) := by
  dsimp only
  let a := 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  let y := contrast P j/a
  obtain ⟨hEven, hDtwo, _, hDupper⟩ := hybridDegree_bounds (logDim d) hL D hD
  have hb := pilot_noiseScale_pos eps heps hd
  have hs : 0 < sigmaSquared d m eps := div_pos (sq_pos_of_pos hb) (by exact_mod_cast hm)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha2 : a^2 = 64 * sigmaSquared d m eps * logDim d := by
    dsimp [a]
    nlinarith [Real.sq_sqrt hs.le, Real.sq_sqrt (show 0 ≤ logDim d by linarith)]
  have hy : 1 ≤ y := by dsimp [y]; rw [le_div_iff₀ ha]; simpa [a] using hx
  have hy2 : 1 ≤ y^2 := by nlinarith
  have hxy : contrast P j = a*y := by dsimp [y]; field_simp
  have hbase : max 1 (((contrast P j)^2 + 2*D*sigmaSquared d m eps)/a^2) ≤ 2*y^2 := by
    apply max_le (by linarith)
    rw [div_le_iff₀ (sq_pos_of_pos ha), hxy, mul_pow]
    have hnoise : 2*(D : ℝ)*sigmaSquared d m eps ≤ a^2 := by
      rw [ha2]
      nlinarith [mul_nonneg hs.le (show 0 ≤ 64*logDim d - 2*(D : ℝ) by linarith)]
    nlinarith [mul_nonneg (sq_nonneg a) (show 0 ≤ y^2-1 by linarith)]
  have hpoly := radius_polynomial_second_bound hCheb P hP eps a heps ha hd hm
    D hEven hDtwo hmD j
  have htail := hybridPilot_central_normalized_tail hMean P hP eps heps hd hm j (by linarith) hx
  have hp := pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hbase D
  have hg := hybrid_outside_second_growth_suppression (logDim d) y (by linarith) hy D hDupper
  have hsecond : 0 ≤ blockMean (m := m) P eps
      (fun z => (polynomialEstimate eps a D j z)^2) := integral_nonneg (fun z => sq_nonneg _)
  change _ ≤ a^2 * Real.exp (-7 * logDim d * y^2)
  calc
    _ ≤ Real.exp (-8*logDim d*y^2) * (a^2 * Real.exp (5*D) * (2*y^2)^D) :=
      mul_le_mul htail (hpoly.trans (mul_le_mul_of_nonneg_left hp (by positivity)))
        hsecond (Real.exp_pos _).le
    _ = a^2 * (Real.exp (-8*logDim d*y^2) * (Real.exp (5*D) * (2*y^2)^D)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hg (sq_nonneg a)

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), [the stated hm d condition](hyp:hmD), and [the stated hx condition](hyp:hx). [C4, C7 and C9 assemble the outside-window variance bound for nonnegative contrasts](goal). -/
-- @node: hybrid_outside_nonneg_variance
lemma hybrid_outside_nonneg_variance (hMean : BoundedMeanConcentration)
    (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hmD : 2*D ≤ m) (j : Fin d)
    (hx : 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) ≤ contrast P j) :
    hybridVar (m := m) P eps (hybridColumn eps D j) ≤
      400 * sigmaSquared d m eps * logDim d * Real.exp (logDim d/100) := by
  let a := 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  let T := a/2
  let h := blockMean (m := m) P eps
    (fun z => if |scaledColumnMean eps j z| ≤ T then (1 : ℝ) else 0)
  let w := blockMean (m := m) P eps
    (fun z => if scaledColumnMean eps j z < -T then (1 : ℝ) else 0)
  have ht : T = 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) := by
    dsimp [T, a]; ring
  have hs : 0 ≤ sigmaSquared d m eps := by unfold sigmaSquared; positivity
  have ha2 : a^2 = 64 * sigmaSquared d m eps * logDim d := by
    dsimp [a]
    nlinarith [Real.sq_sqrt hs, Real.sq_sqrt (show 0 ≤ logDim d by linarith)]
  have hx0 : 0 ≤ contrast P j := le_trans (by positivity) hx
  have hprob : h = (vectorBlockLaw P eps m).real {z | |scaledColumnMean eps j z| ≤ T} := by
    simpa only [h, blockMean, Set.indicator_apply, Set.mem_setOf_eq] using
      (pilot_indicator_probability (m := m) P eps {z | |scaledColumnMean eps j z| ≤ T})
  have wprob : w = (vectorBlockLaw P eps m).real {z | scaledColumnMean eps j z < -T} := by
    simpa only [w, blockMean, Set.indicator_apply, Set.mem_setOf_eq] using
      (pilot_indicator_probability (m := m) P eps {z | scaledColumnMean eps j z < -T})
  have hp := hybrid_outside_weighted_second_moment hMean hCheb P hP eps heps hd hm
    D hL hD hmD j hx
  have hx2 := (hybrid_outside_weighted_contrast hMean P hP eps heps hd hm j hL hx).2
  change _ ≤ a^2 * Real.exp (-7 * logDim d * (contrast P j/a)^2) at hp hx2
  rw [← hprob] at hp hx2
  have he : Real.exp (-7 * logDim d * (contrast P j/a)^2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ logDim d * (contrast P j/a)^2 := by positivity
    linarith
  have hsmall := mul_le_mul_of_nonneg_left he (sq_nonneg a)
  have hp' := hp.trans hsmall
  have hx2' := hx2.trans hsmall
  rw [ha2] at hp' hx2'
  have hw := (hybridPilot_wrong_sign_weighted hMean P hP eps heps hd hm j hx0).2
  rw [← ht, ← wprob] at hw
  have hw' : (contrast P j)^2 * w ≤ sigmaSquared d m eps := hw.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith)) hs |>.trans_eq (mul_one _))
  have hC7 := hybridColumn_centered_error_le P hP eps heps hd hm D j
  rw [← ht] at hC7
  have ha : 2*T = a := by dsimp [T]; ring
  dsimp only at hC7
  rw [ha] at hC7
  change hybridVar P eps (hybridColumn eps D j) ≤
    2*h * blockMean P eps (fun z => (polynomialEstimate eps a D j z)^2) +
    2*h*(contrast P j)^2 + sigmaSquared d m eps + 4*(contrast P j)^2*w at hC7
  have he' : 1 ≤ Real.exp (logDim d/100) := Real.one_le_exp_iff.mpr (by linarith)
  have hscale : sigmaSquared d m eps * logDim d ≤
      sigmaSquared d m eps * logDim d * Real.exp (logDim d/100) := by
    simpa using mul_le_mul_of_nonneg_left he' (by positivity : 0 ≤ sigmaSquared d m eps * logDim d)
  have hsL : sigmaSquared d m eps ≤ sigmaSquared d m eps * logDim d := by
    nlinarith [mul_nonneg hs (show 0 ≤ logDim d - 1 by linarith)]
  change h * _ ≤ _ at hp' hx2'
  nlinarith

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), [the stated hm d condition](hyp:hmD), and [the stated hx condition](hyp:hx). [C8 and C9 cover all nonnegative contrasts, including the window boundary](goal). -/
-- @node: hybrid_nonneg_variance
lemma hybrid_nonneg_variance (hMean : BoundedMeanConcentration)
    (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hmD : 2*D ≤ m) (j : Fin d)
    (hx : 0 ≤ contrast P j) :
    hybridVar (m := m) P eps (hybridColumn eps D j) ≤
      400 * sigmaSquared d m eps * logDim d * Real.exp (logDim d/100) := by
  by_cases hwindow : |contrast P j| ≤ 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  · exact hybrid_inside_nonneg_variance hMean hCheb P hP eps heps hd hm D hL hD hmD j hx hwindow
  · apply hybrid_outside_nonneg_variance hMean hCheb P hP eps heps hd hm D hL hD hmD j
    rw [abs_of_nonneg hx] at hwindow
    exact (not_le.mp hwindow).le

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), and [the stated dm condition](hyp:hDm). [Reflection extends the C3--C6 bias assembly to both signs of every causal contrast](goal). -/
-- @node: hybrid_bias_bound
lemma hybrid_bias_bound (hMean : BoundedMeanConcentration)
    (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hDm : D ≤ m) (j : Fin d) :
    abs (hybridMean (m := m) P eps (hybridColumn eps D j) - abs (contrast P j)) ≤
      20000 * Real.sqrt (sigmaSquared d m eps) / Real.sqrt (logDim d) := by
  by_cases hx : 0 ≤ contrast P j
  · exact hybrid_nonneg_bias hMean hCheb P hP eps heps hd hm D hL hD hDm j hx
  · let P' := symmetricLaw (fun j => -contrast P j)
    have hc := neg_contrast_mem_parameterCube P hP
    letI : IsProbabilityMeasure P' := symmetricLaw_probability _ hc (by omega)
    have hP' : CausalModel P' := symmetricLaw_causalModel _ hc (by omega)
    have hneg : ∀ j, contrast P' j = -contrast P j := symmetricLaw_neg_contrast P hP hd
    have h := hybrid_nonneg_bias hMean hCheb P' hP' eps heps hd hm D hL hD hDm j
      (by rw [hneg]; linarith)
    rw [hybridMean_reflection P P' hP hP' eps hd hneg, hneg j, abs_neg] at h
    exact h

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), and [the stated hm d condition](hyp:hmD). [Reflection extends the C4/C7--C9 variance assembly to both signs of every causal contrast](goal). -/
-- @node: hybrid_variance_bound
lemma hybrid_variance_bound (hMean : BoundedMeanConcentration)
    (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hmD : 2*D ≤ m) (j : Fin d) :
    hybridVar (m := m) P eps (hybridColumn eps D j) ≤
      400 * sigmaSquared d m eps * logDim d * Real.exp (logDim d/100) := by
  by_cases hx : 0 ≤ contrast P j
  · exact hybrid_nonneg_variance hMean hCheb P hP eps heps hd hm D hL hD hmD j hx
  · let P' := symmetricLaw (fun j => -contrast P j)
    have hc := neg_contrast_mem_parameterCube P hP
    letI : IsProbabilityMeasure P' := symmetricLaw_probability _ hc (by omega)
    have hP' : CausalModel P' := symmetricLaw_causalModel _ hc (by omega)
    have hneg : ∀ j, contrast P' j = -contrast P j := symmetricLaw_neg_contrast P hP hd
    have h := hybrid_nonneg_variance hMean hCheb P' hP' eps heps hd hm D hL hD hmD j
      (by rw [hneg]; linarith)
    rw [hybridVar_reflection P P' hP hP' eps hd hneg] at h
    exact h


end CausalSmith.Stat.LdpOptvalueUniformFrontier
