module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Calibration.Radius

/-!
# Hybrid block basics

Independent pilot/evaluation blocks, column means and their finite variance bounds.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n m d : ℕ}

/-- Fix [the privacy budget](hyp:eps), [the coordinate index](hyp:j), and [the function z](hyp:z). [Mean of one scaled column](goal). -/
def scaledColumnMean (eps : ℝ) (j : Fin d) (z : Fin m → Fin d → Bool) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i, scaledMessages eps z i j
/-- Fix [the probability law P](hyp:P), [the privacy budget](hyp:eps), and [the block size](hyp:m). [Independent pilot/evaluation blocks](goal). -/
def hybridLaw (P : Measure (FullRecord d)) (eps : ℝ) (m : ℕ) :
    Measure ((Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) :=
  (vectorBlockLaw P eps m).prod (vectorBlockLaw P eps m)
/-- Fix [the privacy budget](hyp:eps), [the natural-number parameter D](hyp:D), [the coordinate index](hyp:j), and [the function z](hyp:z). [Centered pilot/evaluation hybrid column statistic](goal). -/
def hybridColumn (eps : ℝ) (D : ℕ) (j : Fin d)
    (z : (Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) : ℝ :=
  let sigma := Real.sqrt (sigmaSquared d m eps)
  let threshold := 4*sigma*Real.sqrt (logDim d)
  let pilot := scaledColumnMean eps j z.1
  if |pilot| ≤ threshold then polynomialEstimate eps (2*threshold) D j z.2
  else (if 0 < pilot then 1 else if pilot < 0 then -1 else 0) * scaledColumnMean eps j z.2
/-- Fix [the probability law P](hyp:P), [the privacy budget](hyp:eps), and [the function f](hyp:f). [Hybrid expectation](goal). -/
def hybridMean (P : Measure (FullRecord d)) (eps : ℝ)
    (f : ((Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) → ℝ) : ℝ :=
  ∫ z, f z ∂(hybridLaw P eps m)
/-- Fix [the probability law P](hyp:P), [the privacy budget](hyp:eps), and [the function f](hyp:f). [Hybrid variance](goal). -/
def hybridVar (P : Measure (FullRecord d)) (eps : ℝ)
    (f : ((Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) → ℝ) : ℝ :=
  ∫ z, (f z - hybridMean (m := m) P eps f)^2 ∂(hybridLaw P eps m)

/-- [The threshold includes zero, so the sign-zero convention is never used outside it](goal). -/
-- @node: hybridThreshold_nonneg
lemma hybridThreshold_nonneg (eps : ℝ) :
    0 ≤ 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) := by
  positivity

/-- Assume [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [positive block size](hyp:hm). [Allowed positive resources give a strictly positive pilot threshold](goal). -/
-- @node: hybridThreshold_pos
lemma hybridThreshold_pos (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m) :
    0 < 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdelta : 0 < privacyDelta eps := by
    rw [privacyDelta_exp_formula]
    exact div_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr heps)) (by positivity)
  have hb : 0 < noiseScale d eps := div_pos (by linarith) hdelta
  have hs : 0 < sigmaSquared d m eps := div_pos (sq_pos_of_pos hb) hmR
  have hL : 0 < logDim d := by
    apply Real.log_pos
    have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr zero_lt_one
    nlinarith
  positivity

/-- [The independent two-block experiment is a probability measure](goal). -/
-- @node: hybridLaw_probability
lemma hybridLaw_probability (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) : IsProbabilityMeasure (hybridLaw P eps m) := by
  letI := vectorBlockLaw_probability P eps m
  unfold hybridLaw
  infer_instance

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [positive block size](hyp:hm). [The evaluation column mean is unbiased for the causal contrast](goal). -/
-- @node: blockMean_scaledColumnMean
lemma blockMean_scaledColumnMean (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (hm : 0 < m) (j : Fin d) :
    blockMean (m := m) P eps (scaledColumnMean eps j) = contrast P j := by
  have h := blockMean_privateMoment_eq_rowMean_pow (m := m) P eps 1 (by omega) j
  simp only [privateMoment_one, pow_one] at h
  exact h.trans (vectorMessageLaw_scaled_sign_integral P hP eps heps hd j)

/-- [Finite block variance is the second moment minus the squared mean](goal). -/
-- @node: blockVar_eq_secondMoment_sub_sq
lemma blockVar_eq_secondMoment_sub_sq (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) (f : (Fin m → Fin d → Bool) → ℝ) :
    blockVar (m := m) P eps f = blockMean (m := m) P eps (fun z => (f z)^2) - (blockMean (m := m) P eps f)^2 := by
  letI := vectorBlockLaw_probability P eps m
  unfold blockVar
  have hexp : (fun z => (f z - blockMean (m := m) P eps f)^2) =
      (fun z => (f z)^2 - 2 * blockMean (m := m) P eps f * f z + (blockMean (m := m) P eps f)^2) := by
    funext z
    ring
  rw [hexp, integral_add (Integrable.of_finite) (Integrable.of_finite),
    integral_sub (Integrable.of_finite) (Integrable.of_finite), integral_const_mul,
    integral_const]
  simp only [probReal_univ, one_smul]
  change blockMean (m := m) P eps (fun z => (f z)^2) -
    2 * blockMean (m := m) P eps f * blockMean (m := m) P eps f + (blockMean (m := m) P eps f)^2 = _
  ring

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [positive block size](hyp:hm). [The iid column mean has variance bounded by the declared noise variance](goal). -/
-- @node: blockVar_scaledColumnMean_le
lemma blockVar_scaledColumnMean_le (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (hm : 0 < m) (j : Fin d) :
    blockVar (m := m) P eps (scaledColumnMean eps j) ≤ sigmaSquared d m eps := by
  rw [blockVar_eq_secondMoment_sub_sq, blockMean_scaledColumnMean P hP eps heps hd hm]
  have h := blockMean_privateMoment_one_sq P hP eps heps hd hm j
  simp only [privateMoment_one] at h
  change blockMean (m := m) P eps (fun z => (scaledColumnMean eps j z)^2) = _ at h
  rw [h]
  unfold sigmaSquared
  rw [sub_div]
  have hnonneg : 0 ≤ (contrast P j)^2 / (m : ℝ) := by positivity
  linarith


end CausalSmith.Stat.LdpOptvalueUniformFrontier
