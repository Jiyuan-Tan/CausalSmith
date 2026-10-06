module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Calibration.HybridBasics

/-!
# Pilot concentration

Hoeffding bounds for actual scaled vector-message column means, including the wrong-sign
and central-window pilot events in the hybrid calibration roadmap (C4/C6).
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {m d : ℕ}

/-- Assume [a positive privacy budget](hyp:heps) and [dimension at least two](hyp:hd). [Positive privacy and dimension give a positive noise scale](goal). -/
-- @node: pilot_noiseScale_pos
lemma pilot_noiseScale_pos (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) :
    0 < noiseScale d eps := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdelta : 0 < privacyDelta eps := by
    rw [privacyDelta_exp_formula]
    exact div_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr heps)) (by positivity)
  exact div_pos hdR hdelta

/-- [A pilot column has independent rows under the product release law](goal). -/
-- @node: pilot_scaledMessages_independent
lemma pilot_scaledMessages_independent (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) (j : Fin d) :
    iIndepFun (fun i : Fin m => fun z => scaledMessages eps z i j) (vectorBlockLaw P eps m) := by
  letI := vectorMessageLaw_probability P eps
  unfold vectorBlockLaw scaledMessages
  exact iIndepFun_pi (fun _ => (show Measurable
    (fun z : Fin d → Bool => noiseScale d eps * signVal (z j)) by fun_prop).aemeasurable)

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), and [the stated hu condition](hyp:hu). [The Hoeffding gate applies to the actual pilot column, with the paper's variance scale](goal). -/
-- @node: pilot_scaledColumnMean_tails
lemma pilot_scaledColumnMean_tails (hMean : BoundedMeanConcentration)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m) (j : Fin d)
    (u : ℝ) (hu : 0 ≤ u) :
    (vectorBlockLaw P eps m).real {z | u ≤ scaledColumnMean eps j z - contrast P j} ≤
      Real.exp (-u^2 / (2 * sigmaSquared d m eps)) ∧
    (vectorBlockLaw P eps m).real {z | scaledColumnMean eps j z - contrast P j ≤ -u} ≤
      Real.exp (-u^2 / (2 * sigmaSquared d m eps)) := by
  letI := vectorBlockLaw_probability P eps m
  have hb := pilot_noiseScale_pos eps heps hd
  have hbound (i : Fin m) (z : Fin m → Fin d → Bool) :
      scaledMessages eps z i j ∈ Set.Icc (-noiseScale d eps) (noiseScale d eps) := by
    cases hz : z i j <;> simp [scaledMessages, hz, signVal] <;> linarith
  have hmean (i : Fin m) :
      (∫ z, scaledMessages eps z i j ∂vectorBlockLaw P eps m) = contrast P j := by
    exact (blockMean_scaledMessages_eq_rowMean P eps i j).trans
      (vectorMessageLaw_scaled_sign_integral P hP eps heps hd j)
  have hcenter (z : Fin m → Fin d → Bool) :
      (m : ℝ)⁻¹ * ∑ i, (scaledMessages eps z i j - contrast P j) =
        scaledColumnMean eps j z - contrast P j := by
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp [Finset.sum_sub_distrib, scaledColumnMean, mul_sub, hmR]
  have hexponent : -(m : ℝ) * u^2 / (2 * (noiseScale d eps)^2) =
      -u^2 / (2 * sigmaSquared d m eps) := by
    unfold sigmaSquared
    field_simp
  have h := hMean (vectorBlockLaw P eps m) m hm (noiseScale d eps)
    (fun i z => scaledMessages eps z i j) (pilot_scaledMessages_independent P eps j)
    (fun _ => by fun_prop) hbound u hu
  simp_rw [hmean, hcenter, hexponent] at h
  exact h

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), and [the stated hx condition](hyp:hx). [The wrong-sign pilot branch has the one-sided C4 tail, including threshold ties](goal). -/
-- @node: hybridPilot_wrong_sign_tail
lemma hybridPilot_wrong_sign_tail (hMean : BoundedMeanConcentration)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m) (j : Fin d)
    (hx : 0 ≤ contrast P j) :
    let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    (vectorBlockLaw P eps m).real {z | scaledColumnMean eps j z < -T} ≤
      Real.exp (-(contrast P j + T)^2 / (2 * sigmaSquared d m eps)) := by
  dsimp only
  letI := vectorBlockLaw_probability P eps m
  have hT := hybridThreshold_nonneg (m := m) (d := d) eps
  apply le_trans (measureReal_mono (fun z hz => ?_))
    (pilot_scaledColumnMean_tails hMean P hP eps heps hd hm j
      (contrast P j + 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d))
      (by linarith)).2
  change scaledColumnMean eps j z - contrast P j ≤ _
  change scaledColumnMean eps j z < _ at hz
  linarith

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), and [the stated hx condition](hyp:hx). [Outside the approximation radius, the central pilot event has the C6 tail](goal). -/
-- @node: hybridPilot_central_tail
lemma hybridPilot_central_tail (hMean : BoundedMeanConcentration)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m) (j : Fin d)
    (hx : 8 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d) ≤ contrast P j) :
    let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    (vectorBlockLaw P eps m).real {z | |scaledColumnMean eps j z| ≤ T} ≤
      Real.exp (-(contrast P j)^2 / (8 * sigmaSquared d m eps)) := by
  dsimp only
  letI := vectorBlockLaw_probability P eps m
  have hT := hybridThreshold_nonneg (m := m) (d := d) eps
  have hxpos : 0 ≤ contrast P j := by linarith
  have htail := (pilot_scaledColumnMean_tails hMean P hP eps heps hd hm j
    (contrast P j / 2) (by positivity)).2
  have heq : -(contrast P j / 2)^2 / (2 * sigmaSquared d m eps) =
      -(contrast P j)^2 / (8 * sigmaSquared d m eps) := by ring
  rw [heq] at htail
  apply le_trans (measureReal_mono (fun z hz => ?_)) htail
  change |scaledColumnMean eps j z| ≤ _ at hz
  have hzupper := (abs_le.mp hz).2
  change scaledColumnMean eps j z - contrast P j ≤ _
  linarith

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), and [the stated hx condition](hyp:hx). [The wrong-sign exponent separates into a Gaussian contrast factor and exp(-8L)](goal). -/
-- @node: hybridPilot_wrong_sign_factor
lemma hybridPilot_wrong_sign_factor (hMean : BoundedMeanConcentration)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m) (j : Fin d)
    (hx : 0 ≤ contrast P j) :
    let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    (vectorBlockLaw P eps m).real {z | scaledColumnMean eps j z < -T} ≤
      Real.exp (-(contrast P j)^2 / (2 * sigmaSquared d m eps)) *
        Real.exp (-8 * logDim d) := by
  dsimp only
  have hb := pilot_noiseScale_pos eps heps hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < sigmaSquared d m eps := div_pos (sq_pos_of_pos hb) hmR
  have hL : 0 ≤ logDim d := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    apply Real.log_nonneg
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hT := hybridThreshold_nonneg (m := m) (d := d) eps
  have hT2 : (4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d))^2 =
      16 * sigmaSquared d m eps * logDim d := by
    nlinarith [Real.sq_sqrt hs.le, Real.sq_sqrt hL]
  apply (hybridPilot_wrong_sign_tail hMean P hP eps heps hd hm j hx).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ (by positivity : 0 < 2 * sigmaSquared d m eps)).mpr
  have hsplit : (-(contrast P j)^2 / (2 * sigmaSquared d m eps) + -8 * logDim d) *
      (2 * sigmaSquared d m eps) = -(contrast P j)^2 - 16 * sigmaSquared d m eps * logDim d := by
    field_simp
    <;> ring
  rw [hsplit]
  nlinarith [mul_nonneg hx hT]

/-- Assume [the stated hs condition](hyp:hs). [The elementary Gaussian first-moment envelope used in C4](goal). -/
-- @node: pilot_gaussian_first_envelope
lemma pilot_gaussian_first_envelope (x sigma : ℝ) (hs : 0 < sigma) :
    x * Real.exp (-x^2 / (2 * sigma^2)) ≤ sigma := by
  have hbound : x / sigma ≤ Real.exp ((x / sigma)^2 / 2) := by
    nlinarith [Real.add_one_le_exp ((x / sigma)^2 / 2), sq_nonneg (x / sigma - 1)]
  have h := mul_le_mul_of_nonneg_right hbound
    (Real.exp_pos (-((x / sigma)^2 / 2))).le
  rw [← Real.exp_add] at h
  have he : (x / sigma)^2 / 2 + -((x / sigma)^2 / 2) = 0 := by ring
  rw [he, Real.exp_zero] at h
  have he' : -((x / sigma)^2 / 2) = -x^2 / (2 * sigma^2) := by ring
  rw [he'] at h
  have hh := mul_le_mul_of_nonneg_right h hs.le
  have heq : x / sigma * Real.exp (-x^2 / (2 * sigma^2)) * sigma =
      x * Real.exp (-x^2 / (2 * sigma^2)) := by field_simp
  simpa only [heq, one_mul] using hh

/-- Assume [the stated hs condition](hyp:hs). [The elementary Gaussian second-moment envelope used in C4](goal). -/
-- @node: pilot_gaussian_second_envelope
lemma pilot_gaussian_second_envelope (x sigma : ℝ) (hs : 0 < sigma) :
    x^2 * Real.exp (-x^2 / (2 * sigma^2)) ≤ sigma^2 := by
  have hexp : 2 * Real.exp (-1) ≤ (1 : ℝ) := by
    have hh := Real.add_one_le_exp (1 : ℝ)
    rw [Real.exp_neg]
    have h := mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr (Real.exp_pos 1).le)
    norm_num at h ⊢
    exact h
  have h := Real.mul_exp_neg_le_exp_neg_one (x^2 / (2 * sigma^2))
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * sigma^2 by positivity)
  have heq : 2 * sigma^2 * (x^2 / (2 * sigma^2) * Real.exp (-(x^2 / (2 * sigma^2)))) =
      x^2 * Real.exp (-x^2 / (2 * sigma^2)) := by
    field_simp
  rw [heq] at hh
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hexp (sq_nonneg sigma)])

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), and [the stated hx condition](hyp:hx). [Both contrast-weighted wrong-sign bounds in C4 hold for the actual pilot](goal). -/
-- @node: hybridPilot_wrong_sign_weighted
lemma hybridPilot_wrong_sign_weighted (hMean : BoundedMeanConcentration)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m) (j : Fin d)
    (hx : 0 ≤ contrast P j) :
    let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
    let w := (vectorBlockLaw P eps m).real {z | scaledColumnMean eps j z < -T}
    contrast P j * w ≤ Real.sqrt (sigmaSquared d m eps) * Real.exp (-8 * logDim d) ∧
    (contrast P j)^2 * w ≤ sigmaSquared d m eps * Real.exp (-8 * logDim d) := by
  dsimp only
  have hb := pilot_noiseScale_pos eps heps hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < sigmaSquared d m eps := div_pos (sq_pos_of_pos hb) hmR
  have hsqrt := Real.sq_sqrt hs.le
  have hfirst := pilot_gaussian_first_envelope (contrast P j)
    (Real.sqrt (sigmaSquared d m eps)) (Real.sqrt_pos.mpr hs)
  have hsecond := pilot_gaussian_second_envelope (contrast P j)
    (Real.sqrt (sigmaSquared d m eps)) (Real.sqrt_pos.mpr hs)
  rw [hsqrt] at hfirst hsecond
  have hw := hybridPilot_wrong_sign_factor hMean P hP eps heps hd hm j hx
  constructor
  · calc
      _ ≤ contrast P j * (Real.exp (-(contrast P j)^2 / (2 * sigmaSquared d m eps)) *
          Real.exp (-8 * logDim d)) := mul_le_mul_of_nonneg_left hw hx
      _ = (contrast P j * Real.exp (-(contrast P j)^2 / (2 * sigmaSquared d m eps))) *
          Real.exp (-8 * logDim d) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfirst (Real.exp_pos _).le
  · calc
      _ ≤ (contrast P j)^2 * (Real.exp (-(contrast P j)^2 / (2 * sigmaSquared d m eps)) *
          Real.exp (-8 * logDim d)) := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = ((contrast P j)^2 * Real.exp (-(contrast P j)^2 / (2 * sigmaSquared d m eps))) *
          Real.exp (-8 * logDim d) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsecond (Real.exp_pos _).le

/-- [The indicator expectation equals the probability of the pilot event](goal). -/
-- @node: pilot_indicator_probability
lemma pilot_indicator_probability (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) (E : Set (Fin m → Fin d → Bool)) :
    blockMean (m := m) P eps (E.indicator (fun _ => (1 : ℝ))) =
      (vectorBlockLaw P eps m).real E := by
  classical
  have hE : MeasurableSet E := Set.toFinite E |>.measurableSet
  exact integral_indicator_one hE

/-- Assume [the stated l condition](hyp:hL). [At log dimension at least one, the C4 residual is bounded by inverse root dimension](goal). -/
-- @node: pilot_exp_tail_le_inv_sqrt
lemma pilot_exp_tail_le_inv_sqrt (L : ℝ) (hL : 1 ≤ L) :
    Real.exp (-8 * L) ≤ 1 / Real.sqrt L := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  have hs2 := Real.sq_sqrt (show 0 ≤ L by linarith)
  have hsle : Real.sqrt L ≤ L := by nlinarith [Real.sqrt_nonneg L]
  have hbound : Real.sqrt L ≤ Real.exp (8 * L) := by
    linarith [Real.add_one_le_exp (8 * L)]
  apply (le_div_iff₀ hs).mpr
  have h := mul_le_mul_of_nonneg_right hbound (Real.exp_pos (-8 * L)).le
  rw [← Real.exp_add] at h
  have he : 8 * L + -8 * L = 0 := by ring
  rw [he, Real.exp_zero] at h
  simpa [mul_comm] using h

end CausalSmith.Stat.LdpOptvalueUniformFrontier
