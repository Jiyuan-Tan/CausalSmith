module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.Calibration

/-!
Finite-pool size, intensity, overflow, and logarithmic rate calibration for the hybrid upper bound.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory

/-- [Under the stated inputs and conditions](hyp:n,eps,heps,hS), The large-information branch has at least twelve complete records.  This gives [the stated result](goal).-/
-- @node: hybrid_large_sample_size
lemma hybrid_large_sample_size (n : Nat) (eps : Real)
    (heps : eps ≤ 1 / 4) (hS : Real.exp 4096 ≤ (n : Real) * eps) :
    12 ≤ n := by
  have hexp := Real.add_one_le_exp (4096 : Real)
  have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
  have hlarge : (12 : Real) ≤ n := by nlinarith
  exact_mod_cast hlarge

/-- [Under the stated inputs and conditions](hyp:eps,hn,n,m), The prescribed splits retain positive pools and comparable marginal pool lengths.  This gives [the stated result](goal).-/
-- @node: hybrid_finite_pool_sizes
lemma hybrid_finite_pool_sizes (n m : Nat) (eps : Real) (hn : 12 ≤ n) :
    n ≤ 4 * (hybridTuning n m eps).h0 ∧
    n + m ≤ 8 * (hybridTuning n m eps).Mp ∧
    n + m ≤ 8 * (hybridTuning n m eps).Mf ∧
    1 ≤ (hybridTuning n m eps).h0 ∧
    1 ≤ (hybridTuning n m eps).Mp ∧
    1 ≤ (hybridTuning n m eps).Mf ∧
    (hybridTuning n m eps).Mp ≤ (hybridTuning n m eps).Mf ∧
    (hybridTuning n m eps).Mf ≤ 3 * (hybridTuning n m eps).Mp := by
  dsimp [hybridTuning]
  omega

/-- [Under the stated inputs and conditions](hyp:eps,hn,n,m), Pool intensities satisfy exactly the hypotheses of the uniform hybrid arm theorem.  This gives [the stated result](goal).-/
-- @node: hybrid_finite_pool_intensities
lemma hybrid_finite_pool_intensities (n m : Nat) (eps : Real) (hn : 12 ≤ n) :
    (n : Real) / 32 ≤ (hybridTuning n m eps).u ∧
    ((n : Real) + m) / 64 ≤ (hybridTuning n m eps).tp ∧
    ((n : Real) + m) / 64 ≤ (hybridTuning n m eps).t ∧
    0 < (hybridTuning n m eps).tp ∧
    1 / 3 ≤ (hybridTuning n m eps).t / (hybridTuning n m eps).tp ∧
    (hybridTuning n m eps).t / (hybridTuning n m eps).tp ≤ 3 := by
  obtain ⟨h0, hp, hf, _, hppos, _, hpf, hfp⟩ := hybrid_finite_pool_sizes n m eps hn
  have h0' : (n : Real) ≤ 4 * (hybridTuning n m eps).h0 := by exact_mod_cast h0
  have hp' : (n : Real) + m ≤ 8 * (hybridTuning n m eps).Mp := by exact_mod_cast hp
  have hf' : (n : Real) + m ≤ 8 * (hybridTuning n m eps).Mf := by exact_mod_cast hf
  have hpos : (0 : Real) < (hybridTuning n m eps).Mp := by exact_mod_cast hppos
  have hpf' : ((hybridTuning n m eps).Mp : Real) ≤ (hybridTuning n m eps).Mf := by
    exact_mod_cast hpf
  have hfp' : ((hybridTuning n m eps).Mf : Real) ≤ 3 * (hybridTuning n m eps).Mp := by
    exact_mod_cast hfp
  have htp : 0 < (hybridTuning n m eps).tp := by dsimp [hybridTuning] at hpos ⊢; positivity
  refine ⟨?_, ?_, ?_, htp, (le_div_iff₀ htp).2 ?_, (div_le_iff₀ htp).2 ?_⟩ <;>
    dsimp [hybridTuning] at * <;> linarith

/-- [Under the stated inputs and conditions](hyp:h,hh), Each positive capacity has an exponential overflow cost bounded by its reciprocal.  This gives [the stated result](goal).-/
-- @node: hybrid_capacity_exp_bound
lemma hybrid_capacity_exp_bound (h : Nat) (hh : 0 < h) :
    Real.exp (-(h : Real)) ≤ 1 / (h : Real) := by
  have hp : (0 : Real) < h := by exact_mod_cast hh
  rw [Real.exp_neg, one_div]
  exact (inv_le_inv₀ (Real.exp_pos _) hp).2
    (by linarith [Real.add_one_le_exp (h : Real)])

/-- [Under the stated inputs and conditions](hyp:eps,hn,heps,heps4,n,m), The three overflow costs are absorbed by the rare-label inverse-information rate.  This gives [the stated result](goal).-/
-- @node: hybrid_finite_overflow_rate
lemma hybrid_finite_overflow_rate (n m : Nat) (eps : Real) (hn : 12 ≤ n)
    (heps : 0 < eps) (heps4 : eps ≤ 1 / 4) :
    Real.exp (-((hybridTuning n m eps).h0 : Real)) +
      Real.exp (-((hybridTuning n m eps).Mp : Real)) +
      Real.exp (-((hybridTuning n m eps).Mf : Real)) ≤
      5 / ((n : Real) * eps) := by
  obtain ⟨h0, hp, hf, h0pos, hppos, hfpos, _, _⟩ := hybrid_finite_pool_sizes n m eps hn
  have hnpos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hcap (h : Nat) (hh : 1 ≤ h) (hb : n ≤ 8 * h) :
      Real.exp (-(h : Real)) ≤ 8 / (n : Real) := by
    have hhpos : (0 : Real) < h := by exact_mod_cast hh
    have hb' : (n : Real) ≤ 8 * h := by exact_mod_cast hb
    exact (hybrid_capacity_exp_bound h (by omega)).trans
      ((div_le_div_iff₀ hhpos hnpos).2 (by nlinarith))
  have hzero : Real.exp (-((hybridTuning n m eps).h0 : Real)) ≤ 4 / (n : Real) := by
    have hhpos : (0 : Real) < (hybridTuning n m eps).h0 := by exact_mod_cast h0pos
    have hb : (n : Real) ≤ 4 * (hybridTuning n m eps).h0 := by exact_mod_cast h0
    exact (hybrid_capacity_exp_bound _ (by omega)).trans
      ((div_le_div_iff₀ hhpos hnpos).2 (by nlinarith))
  have hpilot := hcap _ hppos (by omega)
  have hfactorial := hcap _ hfpos (by omega)
  have hrate : 20 / (n : Real) ≤ 5 / ((n : Real) * eps) := by
    apply (div_le_div_iff₀ hnpos (mul_pos hnpos heps)).2
    nlinarith
  calc
    _ ≤ 4 / (n : Real) + 8 / (n : Real) + 8 / (n : Real) :=
      add_le_add (add_le_add hzero hpilot) hfactorial
    _ = 20 / (n : Real) := by ring
    _ ≤ _ := hrate

/-- [Under the stated inputs and conditions](hyp:S,hS), The degree calibrated to log S also controls the frontier logarithm.  This gives [the stated result](goal).-/
-- @node: hybrid_frontier_log_degree
lemma hybrid_frontier_log_degree (S : Real) (hS : Real.exp 4096 ≤ S) :
    Real.log (Real.exp 1 + S) ≤
      1281 * (Nat.floor (Real.log S / 1024) : Real) := by
  obtain ⟨hL, hy, _, _⟩ := hybrid_degree_calibration S hS
  have hSp : 0 < S := (Real.exp_pos _).trans_le hS
  have hStwo : 2 ≤ S := by linarith [Real.add_one_le_exp (4096 : Real)]
  have hetwo : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : Real)]
  have hlog : Real.log (Real.exp 1 + S) ≤ Real.log S + 1 := by
    apply (Real.log_le_iff_le_exp (by positivity)).2
    rw [Real.exp_add, Real.exp_log hSp]
    nlinarith
  have hL' : (4 : Real) ≤ Nat.floor (Real.log S / 1024) := by exact_mod_cast hL
  linarith

/-- [Under the stated inputs and conditions](hyp:eps,heps,hS,n,d,m), Converting from the polynomial degree to the frontier logarithm costs a numerical factor.  This gives [the stated result](goal).-/
-- @node: hybrid_finite_degree_rate
lemma hybrid_finite_degree_rate (n m d : Nat) (eps : Real)
    (heps : 0 < eps) (hS : Real.exp 4096 ≤ (n : Real) * eps) :
    1 / ((n : Real) * eps) +
      ((d : Real) / (((n : Real) + m) * eps * (hybridTuning n m eps).L)) ^ 2 ≤
    (1281 : Real) ^ 2 * (1 / ((n : Real) * eps) +
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2) := by
  have hSp : 0 < (n : Real) * eps := (Real.exp_pos _).trans_le hS
  have hn : (0 : Real) < n := by
    by_contra hh
    have hz : (n : Real) = 0 := le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg n)
    simp [hz] at hSp
  have hN : 0 < ((n : Real) + m) * eps :=
    mul_pos (by linarith [(Nat.cast_nonneg m : (0 : Real) ≤ m)]) heps
  have hL := (hybrid_degree_calibration _ hS).1
  have hLp : (0 : Real) < (hybridTuning n m eps).L := by
    dsimp [hybridTuning]
    exact_mod_cast (show 0 < Nat.floor (Real.log ((n : Real) * eps) / 1024) by omega)
  have hell : 0 < logScale n eps := by
    dsimp [logScale, labelScale]
    apply Real.log_pos
    linarith [Real.add_one_le_exp (1 : Real)]
  have hlog : logScale n eps ≤ 1281 * (hybridTuning n m eps).L :=
    hybrid_frontier_log_degree _ hS
  have hratio : (d : Real) / (((n : Real) + m) * eps * (hybridTuning n m eps).L) ≤
      1281 * ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (mul_pos hN hLp) (mul_pos hN hell)).2
    convert mul_le_mul_of_nonneg_left hlog
      (mul_nonneg (Nat.cast_nonneg d) hN.le) using 1 <;> ring
  have hsquare := mul_self_le_mul_self (by positivity :
    0 ≤ (d : Real) / (((n : Real) + m) * eps * (hybridTuning n m eps).L)) hratio
  nlinarith [one_div_pos.mpr hSp]

/-- [Under the stated inputs and conditions](hyp:eps,P,hsmall,n,m,d), The exact zero branch has risk at most one.  This gives [the stated result](goal).-/
-- @node: hybrid_small_information_risk
lemma hybrid_small_information_risk (n m d : Nat) (eps : Real) (P : DiscreteLaw d)
    (hsmall : (n : Real) * eps < Real.exp 4096) :
    ruleRisk (liftRule (hybridEstimator n m d eps)) P ≤ 1 := by
  let : IsProbabilityMeasure (obsLaw P) := by unfold obsLaw; infer_instance
  let : IsProbabilityMeasure seedLaw := ⟨by
    norm_num [seedLaw, Real.volume_Icc]⟩
  let : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw
    infer_instance
  have ht := ateFunctional_mem_Icc P
  have hrisk : ruleRisk (liftRule (hybridEstimator n m d eps)) P =
      (ateFunctional P) ^ 2 := by
    simp [ruleRisk, liftRule, hybridEstimator, hsmall, integral_const,
      Measure.real_def]
  rw [hrisk]
  nlinarith [ht.1, ht.2]

/-- [Under the stated inputs and conditions](hyp:eps,hn,heps,hsmall,n,m,d), The frontier rate absorbs the zero-branch risk with a universal numerical constant.  This gives [the stated result](goal).-/
-- @node: hybrid_small_information_rate
lemma hybrid_small_information_rate (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (heps : 0 < eps) (hsmall : (n : Real) * eps < Real.exp 4096) :
    1 ≤ Real.exp 4096 * frontierRate n m d eps := by
  have hnpos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hSp := mul_pos hnpos heps
  have hinv : 1 / Real.exp 4096 ≤ 1 / ((n : Real) * eps) :=
    one_div_le_one_div_of_le hSp hsmall.le
  have hunit : 1 / Real.exp 4096 ≤ 1 := by
    apply (div_le_iff₀ (Real.exp_pos _)).2
    linarith [Real.add_one_le_exp (4096 : Real)]
  have hrate : 1 / Real.exp 4096 ≤ frontierRate n m d eps :=
    le_min hunit (hinv.trans (le_add_of_nonneg_right (sq_nonneg _)))
  exact (div_le_iff₀ (Real.exp_pos _)).mp hrate |>.trans_eq (mul_comm _ _)

end CausalSmith.Stat.AnnotationRarearmFrontier
