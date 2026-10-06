module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.PhaseAlgebra
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.TLocalCovarianceBias
public import Mathlib.Algebra.Order.Field.GeomSum

/-! Geometric truncation and covariance ledgers for the public upper procedure. -/
public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- Taking a real power of one dyadic refinement multiplies by the fixed scale ratio. -/
-- @node: upper_cell_power_step
lemma upper_cell_power_step (h : ℝ) (hh : 0 < h) (j : ℕ) (s : ℝ) :
    cellLen h (j+1)^s = cellLen h j^s * (2 : ℝ)^(-s) := by
  have hc : 0 < cellLen h j := div_pos hh (by positivity)
  have he : cellLen h (j+1) = cellLen h j / 2 := by
    unfold cellLen
    rw [pow_succ]
    ring
  rw [he, Real.div_rpow hc.le (by norm_num), Real.rpow_neg (by norm_num)]
  ring

/-- The positive-power dyadic ledger is bounded by its infinite geometric envelope. -/
-- @node: upper_cell_positive_sum
lemma upper_cell_positive_sum (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (s : ℝ) (hs : 0 < s) (J : ℕ) :
    (∑ j ∈ Finset.range J, cellLen h (j+1)^s) ≤ 1/(1-(2 : ℝ)^(-s)) := by
  let r : ℝ := (2 : ℝ)^(-s)
  have hr : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have he (j : ℕ) : cellLen h (j+1)^s = h^s * r^(j+1) := by
    induction j with
    | zero => simpa [cellLen, r] using upper_cell_power_step h hh.1 0 s
    | succ j hj => rw [upper_cell_power_step h hh.1, hj, pow_succ]; ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hgeom : (∑ j ∈ Finset.range J, r^(j+1)) ≤ 1/(1-r) := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, r^j := by
        apply Finset.sum_le_sum
        intro j _
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hr _) hr1.le
      _ ≤ 1/(1-r) := by
        simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hr hr1)
  have hhpow := Real.rpow_le_one hh.1.le hh.2 hs.le
  exact (mul_le_mul_of_nonneg_left hgeom (Real.rpow_nonneg hh.1.le s)).trans
    (mul_le_of_le_one_left (by positivity) hhpow)

/-- Summing negative powers backwards from the finest mesh gives the uncapped envelope. -/
-- @node: upper_cell_negative_sum
lemma upper_cell_negative_sum (h : ℝ) (hh : 0 < h) (s : ℝ) (hs : 0 < s) (J : ℕ) :
    (∑ j ∈ Finset.range J, cellLen h (j+1)^(-s)) ≤
      cellLen h J^(-s)/(1-(2 : ℝ)^(-s)) := by
  let r : ℝ := (2 : ℝ)^(-s)
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hd : 0 < 1-r := sub_pos.mpr hr1
  induction J with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact div_nonneg (Real.rpow_nonneg (by unfold cellLen; positivity) _) hd.le
  | succ J hJ =>
    have hstep : cellLen h J^(-s) = r * cellLen h (J+1)^(-s) := by
      rw [upper_cell_power_step h hh J (-s)]
      dsimp [r]
      rw [neg_neg, mul_left_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      simp
    rw [Finset.sum_range_succ]
    calc
      _ ≤ cellLen h J^(-s)/(1-r) + cellLen h (J+1)^(-s) := add_le_add hJ le_rfl
      _ = cellLen h (J+1)^(-s)/(1-r) := by rw [hstep]; field_simp; ring

/-- The uncapped per-level truncation bias is a single negative mesh power. -/
-- @node: upper_uncapped_bias_identity
lemma upper_uncapped_bias_identity (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (j : ℕ) :
    cellLen (upperH κ n) j^effectiveA κ *
      (((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) j^(1+2*effectiveA κ))^(1/κ.p))^(1-κ.p) =
    ((n : ℝ)^2*upperH κ n)^(-qExp κ) * cellLen (upperH κ n) j^(-effectiveD κ) := by
  have hh := (upper_bandwidth_certificate κ hκ n hn).1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hc : 0 < cellLen (upperH κ n) j := div_pos hh (by positivity)
  have hp : κ.p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hκ.1.1)
  rw [← Real.rpow_mul (by positivity)]
  have hq : (1/κ.p)*(1-κ.p) = -qExp κ := by unfold qExp; field_simp; ring
  rw [hq, Real.mul_rpow (by positivity) (Real.rpow_nonneg hc.le _),
    ← Real.rpow_mul hc.le]
  rw [mul_left_comm, ← Real.rpow_add hc]
  congr 1
  unfold effectiveD qExp
  field_simp
  ring

/-- Raising the finest interaction budget to its negative moment exponent bounds the bias. -/
-- @node: upper_uncapped_finest_bias
lemma upper_uncapped_finest_bias (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (hJ : 0 < upperJ κ n) :
    ((n : ℝ)^2*upperH κ n)^(-qExp κ) *
      cellLen (upperH κ n) (upperJ κ n)^(-effectiveD κ) ≤
    cellLen (upperH κ n) (upperJ κ n)^effectiveS κ := by
  have hh := (upper_bandwidth_certificate κ hκ n hn).1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hc : 0 < cellLen (upperH κ n) (upperJ κ n) := div_pos hh (by positivity)
  have hp : 0 < κ.p := lt_trans (by norm_num) hκ.1.1
  have hq : 0 < qExp κ := div_pos (sub_pos.mpr hκ.1.1) hp
  have hb := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
    (upper_finest_budget κ hκ n hn hJ) (neg_nonpos.mpr hq.le)
  rw [Real.one_rpow, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hc.le] at hb
  have he : -effectiveD κ =
      (1+2*effectiveA κ+κ.β/qExp κ)*(-qExp κ)+effectiveS κ := by
    unfold effectiveD effectiveS
    field_simp [hq.ne', hp.ne']
    unfold qExp
    field_simp
    ring
  rw [he, Real.rpow_add hc, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hc.le _)).trans_eq (one_mul _)

/-- The coarse threshold contributes precisely the bandwidth moment scale. -/
-- @node: upper_coarse_bias_identity
lemma upper_coarse_bias_identity (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) :
    upperT κ n 0^(1-κ.p) = ((n : ℝ)*upperH κ n)^(-qExp κ) := by
  have hh := (upper_bandwidth_certificate κ hκ n hn).1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hp : κ.p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hκ.1.1)
  simp only [upperT, Fin.val_zero, ↓reduceIte]
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  unfold qExp
  field_simp
  ring

/-- A capped threshold is controlled by the sum of its coarse and uncapped bias envelopes.
This allows both geometric envelopes to be summed without any independence across levels. -/
-- @node: upper_level_bias_envelope
lemma upper_level_bias_envelope (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (j : Fin (upperJ κ n)) :
    cellLen (upperH κ n) (j.val+1)^effectiveA κ * upperT κ n j.succ^(1-κ.p) ≤
      cellLen (upperH κ n) (j.val+1)^effectiveA κ * ((n : ℝ)*upperH κ n)^(-qExp κ) +
      ((n : ℝ)^2*upperH κ n)^(-qExp κ) * cellLen (upperH κ n) (j.val+1)^(-effectiveD κ) := by
  have hid := upper_uncapped_bias_identity κ hκ n hn (j.val+1)
  rw [← hid, ← upper_coarse_bias_identity κ hκ n hn]
  have hc : 0 ≤ cellLen (upperH κ n) (j.val+1)^effectiveA κ :=
    Real.rpow_nonneg (by unfold cellLen; positivity [(upper_bandwidth_certificate κ hκ n hn).1.1]) _
  have hh := (upper_bandwidth_certificate κ hκ n hn).1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h0 : 0 ≤ upperT κ n 0^(1-κ.p) := by
    apply Real.rpow_nonneg
    linarith [upper_threshold_positive κ hκ n hn 0]
  have hu : 0 ≤
      (((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) (j.val+1)^(1+2*effectiveA κ))^(1/κ.p))^(1-κ.p) := by
    apply Real.rpow_nonneg
    unfold cellLen
    positivity
  simp only [upperT, Fin.val_succ, Fin.val_zero, ↓reduceIte, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceIte]
  rcases le_total (((n : ℝ)*upperH κ n)^(1/κ.p))
    (((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) (j.val+1)^(1+2*effectiveA κ))^(1/κ.p)) with h | h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (mul_nonneg hc hu)
  · rw [min_eq_right h]
    exact le_add_of_nonneg_left (mul_nonneg hc h0)

/-- Both geometric envelopes sum to the exact public multiscale bias budget. -/
-- @node: upper_multiscale_bias_ledger
lemma upper_multiscale_bias_ledger (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) :
    (∑ j : Fin (upperJ κ n), cellLen (upperH κ n) (j.val+1)^effectiveA κ *
      upperT κ n j.succ^(1-κ.p)) ≤
    rate κ n / constantA κ + 4*rate κ n / constantE κ := by
  have hphase := phase_algebra κ hκ
  have ha := hphase.2.2.1
  have hd := hphase.2.2.2.1
  have hA := hphase.2.2.2.2.1
  have hE := hphase.2.2.2.2.2.1
  have ht := upper_tuning κ hκ n hn
  have hh : 0 < upperH κ n := ht.1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hforward := upper_cell_positive_sum (upperH κ n) ht.1 (effectiveA κ) ha (upperJ κ n)
  have hbackward := upper_cell_negative_sum (upperH κ n) ht.1.1 (effectiveD κ) hd (upperJ κ n)
  rw [Finset.sum_range] at hforward hbackward
  have hcoarse : (∑ j : Fin (upperJ κ n), cellLen (upperH κ n) (j.val+1)^effectiveA κ *
      ((n : ℝ)*upperH κ n)^(-qExp κ)) ≤ rate κ n / constantA κ := by
    rw [← Finset.sum_mul]
    have hu : 0 ≤ ((n : ℝ)*upperH κ n)^(-qExp κ) := Real.rpow_nonneg (by positivity) _
    calc
      _ ≤ (1/constantA κ) * ((n : ℝ)*upperH κ n)^(-qExp κ) :=
        mul_le_mul_of_nonneg_right hforward hu
      _ ≤ (1/constantA κ) * rate κ n :=
        mul_le_mul_of_nonneg_left ht.2.2.1 (by positivity)
      _ = _ := by ring
  have huncapped : (∑ j : Fin (upperJ κ n), ((n : ℝ)^2*upperH κ n)^(-qExp κ) *
      cellLen (upperH κ n) (j.val+1)^(-effectiveD κ)) ≤ 4*rate κ n / constantE κ := by
    by_cases hJ : upperJ κ n = 0
    · have hzero : (∑ j : Fin (upperJ κ n), ((n : ℝ)^2*upperH κ n)^(-qExp κ) *
          cellLen (upperH κ n) (j.val+1)^(-effectiveD κ)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hj := j.isLt
        omega
      rw [hzero]
      have hr : 0 ≤ rate κ n := le_trans (by positivity) ht.2.2.1
      positivity
    · have hJpos : 0 < upperJ κ n := Nat.pos_of_ne_zero hJ
      rw [← Finset.mul_sum]
      have hu : 0 ≤ ((n : ℝ)^2*upperH κ n)^(-qExp κ) := Real.rpow_nonneg (by positivity) _
      calc
        _ ≤ ((n : ℝ)^2*upperH κ n)^(-qExp κ) *
            (cellLen (upperH κ n) (upperJ κ n)^(-effectiveD κ)/constantE κ) :=
          mul_le_mul_of_nonneg_left hbackward hu
        _ = (((n : ℝ)^2*upperH κ n)^(-qExp κ) *
            cellLen (upperH κ n) (upperJ κ n)^(-effectiveD κ))/constantE κ := by ring
        _ ≤ cellLen (upperH κ n) (upperJ κ n)^effectiveS κ / constantE κ :=
          div_le_div_of_nonneg_right (upper_uncapped_finest_bias κ hκ n hn hJpos) hE.le
        _ ≤ 4*rate κ n / constantE κ := div_le_div_of_nonneg_right ht.2.2.2.2.1 hE.le
  calc
    _ ≤ ∑ j : Fin (upperJ κ n),
        (cellLen (upperH κ n) (j.val+1)^effectiveA κ * ((n : ℝ)*upperH κ n)^(-qExp κ) +
        ((n : ℝ)^2*upperH κ n)^(-qExp κ) * cellLen (upperH κ n) (j.val+1)^(-effectiveD κ)) :=
      Finset.sum_le_sum (fun j _ => upper_level_bias_envelope κ hκ n hn j)
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add hcoarse huncapped

/-- The raw truncation-bias expression is bounded by the public rate with its geometric constants. -/
-- @node: upper_truncation_bias_ledger
lemma upper_truncation_bias_ledger (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) :
    20 * upperT κ n 0^(1-κ.p) +
      400 * (∑ j : Fin (upperJ κ n), cellLen (upperH κ n) (j.val+1)^effectiveA κ *
        upperT κ n j.succ^(1-κ.p)) ≤
    (20+400/constantA κ+1600/constantE κ)*rate κ n := by
  rw [upper_coarse_bias_identity κ hκ n hn]
  have ht := upper_tuning κ hκ n hn
  have hs := upper_multiscale_bias_ledger κ hκ n hn
  calc
    _ ≤ 20*rate κ n + 400*(rate κ n/constantA κ+4*rate κ n/constantE κ) :=
      add_le_add (mul_le_mul_of_nonneg_left ht.2.2.1 (by norm_num))
        (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ = _ := by ring

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
