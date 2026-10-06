module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.PhaseAlgebra

/-!
The capped frontier has oracle order exactly when the dimension is bounded by the
marginal information divided by the square root of the label information.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open Filter Asymptotics

/-- [Under the stated inputs and conditions](hyp:hD,hS,d,D,S,K), A positive dimension bound can be expressed as a bound on its normalized ratio.  This gives [the stated result](goal).-/
-- @node: phase_dimension_bound_iff
lemma phase_dimension_bound_iff (d D S K : Real) (hD : 0 < D) (hS : 0 < S) :
    d ≤ K * (D / Real.sqrt S) ↔ (d / D) * Real.sqrt S ≤ K := by
  have hs := Real.sqrt_pos.mpr hS
  rw [← mul_div_assoc, le_div_iff₀ hs, div_mul_eq_mul_div, div_le_iff₀ hD]

/-- [Under the stated inputs and conditions](hyp:v,Rr,hc,hC,hcmp,hdiverge,c,C), Uniform frontier comparisons turn bounded oracle risk ratios into the dimension condition.  This gives [the stated result](goal).-/
-- @node: oracle_of_frontier_comparison
lemma oracle_of_frontier_comparison (v : ExperimentSeq) (Rr : Nat → Real)
    (c C : Real) (hc : 0 < c) (hC : 0 < C)
    (hcmp : ∀ k, c * frontierRate (v k).n (v k).m (v k).d (v k).eps ≤ Rr k ∧
      Rr k ≤ C * frontierRate (v k).n (v k).m (v k).d (v k).eps)
    (hdiverge : Tendsto (fun k => labelScale (v k).n (v k).eps) atTop atTop) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun k => Rr k / labelBenchmark (v k).n (v k).eps) ↔
    (fun k => ((v k).d : Real)) =O[atTop]
      (fun k => (((v k).n : Real) + (v k).m) * (v k).eps *
        logScale (v k).n (v k).eps / Real.sqrt (labelScale (v k).n (v k).eps)) := by
  let S : Nat → Real := fun k => labelScale (v k).n (v k).eps
  let D : Nat → Real := fun k =>
    (((v k).n : Real) + (v k).m) * (v k).eps * logScale (v k).n (v k).eps
  let x : Nat → Real := fun k => ((v k).d : Real) / D k
  let r : Nat → Real := fun k => frontierRate (v k).n (v k).m (v k).d (v k).eps
  have hS (k) : 0 < S k := mul_pos (by exact_mod_cast (v k).n_pos) (v k).eps_pos
  have hD (k) : 0 < D k :=
    mul_pos (mul_pos (by
      have hn : (0 : Real) < (v k).n := by exact_mod_cast (v k).n_pos
      positivity) (v k).eps_pos)
      (phase_logScale_pos _ _ (v k).n_pos (v k).eps_pos)
  have hx (k) : 0 ≤ x k := div_nonneg (Nat.cast_nonneg _) (hD k).le
  have hbench : ∀ᶠ k in atTop, labelBenchmark (v k).n (v k).eps = 1 / S k := by
    filter_upwards [hdiverge.eventually (eventually_ge_atTop 1)] with k hk
    exact (min_eq_right (inv_le_one_of_one_le₀ hk)).trans (by rw [one_div])
  constructor
  · intro hbounded
    obtain ⟨M, hM⟩ := hbounded.eventually_le
    let K : Real := max M 1 / c
    have hK : 0 < K := div_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hc
    have hrate : ∀ᶠ k in atTop, r k ≤ K / S k := by
      filter_upwards [hbench, hM] with k hb hm
      have hupper : Rr k ≤ max M 1 / S k := by
        have ht := (div_le_iff₀ (one_div_pos.mpr (hS k))).mp (by simpa only [hb] using hm)
        calc
          Rr k ≤ M * (1 / S k) := ht
          _ ≤ max M 1 * (1 / S k) := mul_le_mul_of_nonneg_right
            (le_max_left _ _) (one_div_pos.mpr (hS k)).le
          _ = max M 1 / S k := by ring
      apply (mul_le_mul_iff_right₀ hc).mp
      calc
        c * r k ≤ Rr k := (hcmp k).1
        _ ≤ max M 1 / S k := hupper
        _ = c * (K / S k) := by dsimp [K]; field_simp
    apply isBigO_iff.mpr
    refine ⟨Real.sqrt K, ?_⟩
    filter_upwards [hrate, hdiverge.eventually (eventually_gt_atTop K)] with k hr hk
    have hcap : r k = 1 / S k + x k ^ 2 := by
      have hlt : r k < 1 := hr.trans_lt ((div_lt_one (hS k)).mpr hk)
      exact min_eq_right (le_of_lt (by
        simpa only [r, frontierRate, S, x, D, min_lt_iff, lt_self_iff_false, false_or] using hlt))
    have hsquare : (x k * Real.sqrt (S k)) ^ 2 ≤ K := by
      have ht := (le_div_iff₀ (hS k)).mp (by simpa only [hcap] using hr)
      rw [mul_pow, Real.sq_sqrt (hS k).le]
      have hid : (1 / S k + x k ^ 2) * S k = 1 + x k ^ 2 * S k := by
        field_simp [(hS k).ne']
      rw [hid] at ht
      linarith
    have hnorm : x k * Real.sqrt (S k) ≤ Real.sqrt K := by
      have hsK := Real.sq_sqrt hK.le
      have hn := Real.sqrt_nonneg K
      nlinarith
    have hdim := (phase_dimension_bound_iff ((v k).d : Real) (D k) (S k)
      (Real.sqrt K) (hD k) (hS k)).mpr hnorm
    change ‖((v k).d : Real)‖ ≤ Real.sqrt K * ‖D k / Real.sqrt (S k)‖
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (v k).d : (0 : Real) ≤ _),
      abs_of_nonneg (div_nonneg (hD k).le (Real.sqrt_nonneg _))] using hdim
  · intro hbig
    obtain ⟨K, hK, hdim⟩ := isBigO_iff'.mp hbig
    apply isBoundedUnder_of_eventually_le (a := C * (1 + K ^ 2))
    filter_upwards [hbench, hdim] with k hb hd
    have hdim' : ((v k).d : Real) ≤ K * (D k / Real.sqrt (S k)) := by
      change ‖((v k).d : Real)‖ ≤ K * ‖D k / Real.sqrt (S k)‖ at hd
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (v k).d : (0 : Real) ≤ _),
        abs_of_nonneg (div_nonneg (hD k).le (Real.sqrt_nonneg _))] using hd
    have hnorm := (phase_dimension_bound_iff ((v k).d : Real) (D k) (S k)
      K (hD k) (hS k)).mp hdim'
    have hsquare : x k ^ 2 * S k ≤ K ^ 2 := by
      have hn : 0 ≤ x k * Real.sqrt (S k) := mul_nonneg (hx k) (Real.sqrt_nonneg _)
      have ht : (x k * Real.sqrt (S k)) ^ 2 ≤ K ^ 2 := by nlinarith
      simpa only [mul_pow, Real.sq_sqrt (hS k).le] using ht
    have hrate : r k ≤ (1 + K ^ 2) / S k := by
      apply (min_le_right _ _).trans
      apply (le_div_iff₀ (hS k)).mpr
      have hid : (1 / S k + x k ^ 2) * S k = 1 + x k ^ 2 * S k := by field_simp [(hS k).ne']
      change (1 / S k + x k ^ 2) * S k ≤ 1 + K ^ 2
      rw [hid]
      linarith
    rw [hb]
    apply (div_le_iff₀ (one_div_pos.mpr (hS k))).mpr
    calc
      Rr k ≤ C * r k := (hcmp k).2
      _ ≤ C * ((1 + K ^ 2) / S k) := mul_le_mul_of_nonneg_left hrate hC.le
      _ = C * (1 + K ^ 2) * (1 / S k) := by ring

/-- [Under the stated inputs and conditions](hyp:n,eps,hn,heps), On the supervised slice, the oracle dimension scale is exactly square-root label information.  This gives [the stated result](goal).-/
-- @node: phase_supervised_oracle_scale
lemma phase_supervised_oracle_scale (n : Nat) (eps : Real) (hn : 1 ≤ n) (heps : 0 < eps) :
    (n : Real) * eps * logScale n eps / Real.sqrt (labelScale n eps) =
      Real.sqrt (labelScale n eps) * logScale n eps := by
  have hS : 0 < labelScale n eps := mul_pos (by exact_mod_cast hn) heps
  apply (div_eq_iff (Real.sqrt_pos.mpr hS).ne').mpr
  have hs := Real.sq_sqrt hS.le
  change labelScale n eps * logScale n eps = _
  calc
    labelScale n eps * logScale n eps =
        (Real.sqrt (labelScale n eps)) ^ 2 * logScale n eps := by rw [hs]
    _ = _ := by ring

/-- [Under the stated inputs and conditions](hyp:ha,hS,d,N,a,S,K), Positive factors convert the dimension condition into the marginal-budget condition.  This gives [the stated result](goal).-/
-- @node: phase_budget_bound_iff
lemma phase_budget_bound_iff (d N a S K : Real) (ha : 0 < a) (hS : 0 < S) :
    d ≤ K * (N * a / Real.sqrt S) ↔ d * Real.sqrt S / a ≤ K * N := by
  rw [← mul_div_assoc, le_div_iff₀ (Real.sqrt_pos.mpr hS), div_le_iff₀ ha]
  rw [mul_assoc]

/-- [Under the stated inputs and conditions](hyp:v), The dimension and marginal-budget big-O conditions use exactly the same eventual constants.  This gives [the stated result](goal).-/
-- @node: phase_dimension_budget_iff
lemma phase_dimension_budget_iff (v : ExperimentSeq) :
    (fun k => ((v k).d : Real)) =O[atTop]
      (fun k => (((v k).n : Real) + (v k).m) * (v k).eps *
        logScale (v k).n (v k).eps / Real.sqrt (labelScale (v k).n (v k).eps)) ↔
    (fun k => ((v k).d : Real) * Real.sqrt (labelScale (v k).n (v k).eps) /
      ((v k).eps * logScale (v k).n (v k).eps)) =O[atTop]
      (fun k => ((v k).n : Real) + (v k).m) := by
  have hS (k) : 0 < labelScale (v k).n (v k).eps :=
    mul_pos (by exact_mod_cast (v k).n_pos) (v k).eps_pos
  have ha (k) : 0 < (v k).eps * logScale (v k).n (v k).eps :=
    mul_pos (v k).eps_pos (phase_logScale_pos _ _ (v k).n_pos (v k).eps_pos)
  have hN (k) : 0 ≤ ((v k).n : Real) + (v k).m := by positivity
  have hequiv (k : Nat) (K : Real) :
      ‖((v k).d : Real)‖ ≤ K * ‖(((v k).n : Real) + (v k).m) * (v k).eps *
        logScale (v k).n (v k).eps / Real.sqrt (labelScale (v k).n (v k).eps)‖ ↔
      ‖((v k).d : Real) * Real.sqrt (labelScale (v k).n (v k).eps) /
        ((v k).eps * logScale (v k).n (v k).eps)‖ ≤ K * ‖((v k).n : Real) + (v k).m‖ := by
    rw [mul_assoc]
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg (v k).d : (0 : Real) ≤ _),
      abs_of_nonneg (hN k),
      abs_of_nonneg (div_nonneg (mul_nonneg (hN k) (ha k).le) (Real.sqrt_nonneg _)),
      abs_of_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) (ha k).le)]
    exact phase_budget_bound_iff _ _ _ _ _ (ha k) (hS k)
  constructor
  · intro h
    obtain ⟨K, hK⟩ := isBigO_iff.mp h
    exact isBigO_iff.mpr ⟨K, hK.mono (fun k hk => (hequiv k K).mp hk)⟩
  · intro h
    obtain ⟨K, hK⟩ := isBigO_iff.mp h
    exact isBigO_iff.mpr ⟨K, hK.mono (fun k hk => (hequiv k K).mpr hk)⟩

end CausalSmith.Stat.AnnotationRarearmFrontier
