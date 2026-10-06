module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Basic

/-! # Elementary bounds for the binomial clone-collision envelope. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

-- @node: descFactorial_collision_bound
/-- The chance that `r` independent uniform coordinates contain a repeat is at
most the number of pairs divided by the coordinate count. -/
lemma descFactorial_collision_bound (m : Nat) (hm : 1 ≤ m) (r : Nat) :
    1 - (Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r ≤
      (r.choose 2 : ℝ) / (m : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hpow : 0 < (m : ℝ) ^ r := pow_pos hmpos _
    have hfac : (Nat.descFactorial m r : ℝ) ≤ (m : ℝ) ^ r := by
      exact_mod_cast Nat.descFactorial_le_pow m r
    have hq0 : 0 ≤ (Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r := by positivity
    have hq1 : (Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r ≤ 1 := by
      exact (div_le_iff₀ hpow).2 (by simpa using hfac)
    have hsub : (m : ℝ) - r ≤ (m - r : Nat) := by
      by_cases h : r ≤ m
      · rw [Nat.cast_sub h]
      · have : (m : ℝ) ≤ r := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge h))
        simp only [Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge h)), Nat.cast_zero]
        linarith
    have hsub0 : (0 : ℝ) ≤ (m - r : Nat) := Nat.cast_nonneg _
    have hsub1 : ((m - r : Nat) : ℝ) ≤ m := by
      exact_mod_cast Nat.sub_le m r
    have hrec : (Nat.descFactorial m (r + 1) : ℝ) / (m : ℝ) ^ (r + 1) =
        ((m - r : Nat) : ℝ) / (m : ℝ) *
          ((Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r) := by
      rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
      ring
    have hchoose : ((r + 1).choose 2 : ℝ) = (r.choose 2 : ℝ) + r := by
      rw [Nat.choose_succ_succ']
      simp
      ring
    rw [hrec, hchoose]
    have hratio0 : 0 ≤ 1 - ((m - r : Nat) : ℝ) / (m : ℝ) := by
      apply sub_nonneg.mpr
      exact (div_le_iff₀ hmpos).2 (by simpa using hsub1)
    have hratio : 1 - ((m - r : Nat) : ℝ) / (m : ℝ) ≤ (r : ℝ) / (m : ℝ) := by
      apply (le_div_iff₀ hmpos).2
      have : (1 - ((m - r : Nat) : ℝ) / (m : ℝ)) * (m : ℝ) =
          (m : ℝ) - (m - r : Nat) := by field_simp
      rw [this]
      linarith
    have hmul : (1 - ((m - r : Nat) : ℝ) / (m : ℝ)) *
        ((Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r) ≤ (r : ℝ) / (m : ℝ) := by
      calc
        _ ≤ 1 - ((m - r : Nat) : ℝ) / (m : ℝ) := by nlinarith
        _ ≤ _ := hratio
    have hstep : 1 - ((m - r : Nat) : ℝ) / (m : ℝ) *
        ((Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r) ≤
        (1 - (Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r) + r / (m : ℝ) := by
      nlinarith [hmul]
    exact hstep.trans (by have := add_le_add_right ih (r / (m : ℝ));
                           simpa [add_div] using this)

-- @node: descFactorial_exp_bound
/-- The no-repeat probability is at most the exponential pair bound. -/
lemma descFactorial_exp_bound (m : Nat) (hm : 1 ≤ m) (r : Nat) :
    (Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r ≤
      Real.exp (-(r * (r - 1) : ℝ) / (2 * m : ℝ)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have haux : ∀ r : Nat,
      (Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r ≤
        Real.exp (-((r.choose 2 : Nat) : ℝ) / m) := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      by_cases h : r < m
      · have hcast : ((m - r : Nat) : ℝ) = (m : ℝ) - r := by
          exact Nat.cast_sub h.le
        have hfactor : ((m - r : Nat) : ℝ) / m ≤
            Real.exp (-(r : ℝ) / m) := by
          rw [hcast]
          have hbasic := Real.one_sub_le_exp_neg ((r : ℝ) / m)
          have heq : ((m : ℝ) - r) / m = 1 - (r : ℝ) / m := by
            field_simp
          rw [heq]
          simpa only [neg_div] using hbasic
        have hrec : (Nat.descFactorial m (r + 1) : ℝ) / (m : ℝ) ^ (r + 1) =
            ((m - r : Nat) : ℝ) / m *
              ((Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r) := by
          rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
          ring
        have hchoose : ((r + 1).choose 2 : ℝ) = (r.choose 2 : ℝ) + r := by
          rw [Nat.choose_succ_succ']
          simp
          ring
        rw [hrec, hchoose]
        calc
          _ ≤ Real.exp (-(r : ℝ) / m) *
              ((Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r) :=
            mul_le_mul_of_nonneg_right hfactor (by positivity)
          _ ≤ Real.exp (-(r : ℝ) / m) *
              Real.exp (-((r.choose 2 : Nat) : ℝ) / m) :=
            mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
          _ = Real.exp (-(((r.choose 2 : Nat) : ℝ) + r) / m) := by
            rw [← Real.exp_add]
            congr 1
            ring
      · have hzero : m - r = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)
        simpa [Nat.descFactorial_succ, hzero] using
          (Real.exp_nonneg (-(((r + 1).choose 2 : Nat) : ℝ) / m))
  have h := haux r
  rw [Nat.cast_choose_two] at h
  convert h using 1
  congr 1
  ring

-- @node: collisionLowerEnvelope_le_collisionEnvelope
/-- Averaging the exponential no-repeat bound over the audit count. -/
lemma collisionLowerEnvelope_le_collisionEnvelope (T m : Nat) (hm : 1 ≤ m)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    collisionLowerEnvelope T eta m ≤ collisionEnvelope T eta m := by
  unfold collisionLowerEnvelope collisionEnvelope
  apply Finset.sum_le_sum
  intro r hr
  have hw : 0 ≤ (Nat.choose T r : ℝ) * eta ^ r * (1 - eta) ^ (T - r) := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg heta.1 _))
      (pow_nonneg (sub_nonneg.mpr heta.2) _)
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (descFactorial_exp_bound m hm r) 1) hw

-- @node: binomialWeightedSum
/-- The binomial averaging operator on functions of the audit count. -/
noncomputable def binomialWeightedSum (T : Nat) (eta : ℝ) (f : Nat → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (T + 1),
    (Nat.choose T r : ℝ) * eta ^ r * (1 - eta) ^ (T - r) * f r

-- @node: binomialWeightedSum_succ
/-- Adding one Bernoulli trial either leaves the count fixed or increments it. -/
lemma binomialWeightedSum_succ (T : Nat) (eta : ℝ) (f : Nat → ℝ) :
    binomialWeightedSum (T + 1) eta f =
      (1 - eta) * binomialWeightedSum T eta f +
        eta * binomialWeightedSum T eta (fun r => f (r + 1)) := by
  unfold binomialWeightedSum
  conv_lhs =>
    arg 2
    ext r
    rw [show (Nat.choose (T + 1) r : ℝ) * eta ^ r *
          (1 - eta) ^ (T + 1 - r) * f r =
        (Nat.choose (T + 1) r : ℝ) *
          (eta ^ r * (1 - eta) ^ (T + 1 - r) * f r) by ring]
  rw [Finset.sum_choose_succ_mul
    (fun i j : Nat => eta ^ i * (1 - eta) ^ j * f i) T]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hindex : T + 1 - r = (T - r) + 1 := by
      have := Finset.mem_range.mp hr
      omega
    rw [hindex, pow_succ]
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [pow_succ]
    ring

-- @node: binomialWeightedSum_add
/-- Binomial averaging is linear in the function being averaged. -/
lemma binomialWeightedSum_add (T : Nat) (eta : ℝ) (f g : Nat → ℝ) :
    binomialWeightedSum T eta (fun r => f r + g r) =
      binomialWeightedSum T eta f + binomialWeightedSum T eta g := by
  unfold binomialWeightedSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

-- @node: binomialWeightedSum_one
/-- The binomial audit-count weights sum to one. -/
lemma binomialWeightedSum_one (T : Nat) (eta : ℝ) :
    binomialWeightedSum T eta (fun _ => 1) = 1 := by
  induction T with
  | zero => simp [binomialWeightedSum]
  | succ T ih =>
    rw [binomialWeightedSum_succ]
    simpa [ih] using (show (1 - eta) * 1 + eta * 1 = (1 : ℝ) by ring)

-- @node: binomialWeightedSum_count
/-- The expected number of Bernoulli audits is `T * eta`. -/
lemma binomialWeightedSum_count (T : Nat) (eta : ℝ) :
    binomialWeightedSum T eta (fun r => (r : ℝ)) = T * eta := by
  induction T with
  | zero => simp [binomialWeightedSum]
  | succ T ih =>
    have hshift : binomialWeightedSum T eta (fun r => ((r + 1 : Nat) : ℝ)) =
        binomialWeightedSum T eta (fun r => (r : ℝ)) +
          binomialWeightedSum T eta (fun _ => 1) := by
      rw [← binomialWeightedSum_add]
      congr 1
      funext r
      push_cast
      ring
    rw [binomialWeightedSum_succ, hshift, ih, binomialWeightedSum_one]
    push_cast
    ring

-- @node: binomialWeightedSum_pairs
/-- The expected number of unordered pairs of audited epochs. -/
lemma binomialWeightedSum_pairs (T : Nat) (eta : ℝ) :
    binomialWeightedSum T eta (fun r => (r.choose 2 : ℝ)) =
      (T.choose 2 : ℝ) * eta ^ 2 := by
  induction T with
  | zero => simp [binomialWeightedSum]
  | succ T ih =>
    have hshift : binomialWeightedSum T eta (fun r => ((r + 1).choose 2 : ℝ)) =
        binomialWeightedSum T eta (fun r => (r.choose 2 : ℝ)) +
          binomialWeightedSum T eta (fun r => (r : ℝ)) := by
      rw [← binomialWeightedSum_add]
      congr 1
      funext r
      rw [Nat.choose_succ_succ']
      simp
      ring
    rw [binomialWeightedSum_succ, hshift, ih, binomialWeightedSum_count]
    rw [Nat.choose_succ_succ']
    simp
    ring

-- @node: collisionEnvelope_pair_bound
/-- A union bound over audited pairs controls the collision envelope. -/
lemma collisionEnvelope_pair_bound (T m : Nat) (hm : 1 ≤ m)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    collisionEnvelope T eta m ≤ eta ^ 2 * T * (T - 1) / (2 * m : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : collisionEnvelope T eta m ≤
      binomialWeightedSum T eta (fun r => (r.choose 2 : ℝ) / m) := by
    unfold collisionEnvelope binomialWeightedSum
    apply Finset.sum_le_sum
    intro r hr
    have hw : 0 ≤ (Nat.choose T r : ℝ) * eta ^ r * (1 - eta) ^ (T - r) := by
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg heta.1 _))
        (pow_nonneg (sub_nonneg.mpr heta.2) _)
    exact mul_le_mul_of_nonneg_left (descFactorial_collision_bound m hm r) hw
  have hscale : binomialWeightedSum T eta (fun r => (r.choose 2 : ℝ) / m) =
      binomialWeightedSum T eta (fun r => (r.choose 2 : ℝ)) / m := by
    unfold binomialWeightedSum
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hscale, binomialWeightedSum_pairs] at hsum
  calc
    collisionEnvelope T eta m ≤ (T.choose 2 : ℝ) * eta ^ 2 / m := hsum
    _ = eta ^ 2 * T * (T - 1) / (2 * m : ℝ) := by
      rw [Nat.cast_choose_two]
      ring

end CausalSmith.Stat.PomdpStateauditMinimax
