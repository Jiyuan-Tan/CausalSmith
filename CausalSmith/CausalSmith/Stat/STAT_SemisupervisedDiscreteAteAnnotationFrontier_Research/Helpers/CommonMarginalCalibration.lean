module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalPrior

/-! Arithmetic closure of the common-marginal C55 calibration. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

/-- The logarithmic schedule is positive at every nonempty sample size.  [the stated conditions](hyp:hn) [the stated conclusion](goal). -/
lemma commonMarginal_logEN_pos (n : Nat) (hn : 1 ≤ n) : 0 < logEN n := by
  rw [logEN]
  apply Real.log_pos
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  nlinarith
/-- [the stated conditions](hyp:hn) establishes [the stated conclusion](goal). -/

lemma commonMarginal_one_le_logEN (n : Nat) (hn : 1 ≤ n) : 1 ≤ logEN n := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : Real) := Real.log_nonneg (by exact_mod_cast hn)
  rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
  linarith

/-- The logarithmic schedule is at most twice the square-root scale.  [the stated conditions](hyp:hn) [the stated conclusion](goal). -/
lemma commonMarginal_logEN_le_two_sqrt (n : Nat) (hn : 1 ≤ n) :
    logEN n ≤ 2 * Real.sqrt n := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (n : Real) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hnR)
  rw [Real.log_sqrt hnR.le] at hlog
  rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
  nlinarith

/-- The logarithmic schedule is at most the sample size.  [the stated conditions](hyp:hn) [the stated conclusion](goal). -/
lemma commonMarginal_logEN_le_nat (n : Nat) (hn : 1 ≤ n) :
    logEN n ≤ n := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hlog := Real.log_le_sub_one_of_pos hnR
  rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
  linarith

/-- Above one, taking a natural floor preserves at least half the input.  [the stated conditions](hyp:hx) [the stated conclusion](goal). -/
lemma commonMarginal_half_le_floor {x : Real} (hx : 1 ≤ x) :
    x / 2 ≤ (Nat.floor x : Real) := by
  by_cases hx2 : x ≤ 2
  · have hfloor : 1 ≤ Nat.floor x := Nat.le_floor (by simpa using hx)
    have hfloorR : (1 : Real) ≤ Nat.floor x := by exact_mod_cast hfloor
    linarith
  · have hfloor := Nat.sub_one_lt_floor x
    linarith

/-- A ceiling of the calibrated logarithmic degree costs at most one extra
copy of the logarithmic schedule.  [the stated conditions](hyp:hn,hL) [the stated conclusion](goal). -/
lemma commonMarginal_degree_upper {eps : Real}
    (calibration : CommonMarginalCalibration eps) (n L : Nat) (hn : 1 ≤ n)
    (hL : L = Nat.ceil (calibration.degreeConstant * logEN n)) :
    (L : Real) ≤ (calibration.degreeConstant + 1) * logEN n := by
  have hlog := commonMarginal_one_le_logEN n hn
  have hx : 0 ≤ calibration.degreeConstant * logEN n :=
    mul_nonneg calibration.degreeConstant_pos.le (by linarith)
  have hc := Nat.ceil_lt_add_one hx
  rw [← hL] at hc
  nlinarith

/-- The canonical degree is at least two.  [the stated conditions](hyp:hn,hL) [the stated conclusion](goal). -/
lemma commonMarginal_degree_lower {eps : Real}
    {calibration : CommonMarginalCalibration eps} {C rho : Real}
    (closure : CommonMarginalCalibrationClosure calibration C rho)
    (n L : Nat) (hn : 1 ≤ n)
    (hL : L = Nat.ceil (calibration.degreeConstant * logEN n)) : 2 ≤ L := by
  have hlog := commonMarginal_one_le_logEN n hn
  have hx : (2 : Real) ≤ calibration.degreeConstant * logEN n := by
    have hm := mul_le_mul_of_nonneg_left hlog calibration.degreeConstant_pos.le
    have hm' : calibration.degreeConstant ≤
        calibration.degreeConstant * logEN n := by simpa only [mul_one] using hm
    exact closure.degreeFloor.trans hm'
  rw [hL]
  exact_mod_cast (hx.trans (Nat.le_ceil _))

set_option maxHeartbeats 1000000 in
/-- Outside the parametric regime, the capped rare-cell count dominates the
square of the approximation degree at the variance-absorption scale.  [the stated conditions](hyp:hC,hn,hd,hL,hk,hnon) [the stated conclusion](goal). -/
lemma commonMarginal_rareCount_degree_lower {eps : Real}
    {calibration : CommonMarginalCalibration eps} {C rho : Real}
    (hC : 0 < C) (closure : CommonMarginalCalibrationClosure calibration C rho)
    (n m d L k : Nat) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (hL : L = Nat.ceil (calibration.degreeConstant * logEN n))
    (hk : k = min (d - 1)
      ⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊)
    (hnon : ¬commonMarginalParametricRegime calibration n m d) :
    (L : Real) ^ 2 /
        ((1 / (65536 * C)) * calibration.dualGap ^ 2 * calibration.gamma) ≤ k := by
  let K : Real := (1 / (65536 * C)) * calibration.dualGap ^ 2 * calibration.gamma
  let N : Real := (n + m : Nat)
  let ell : Real := logEN n
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (mul_pos (div_pos (by norm_num) (mul_pos (by norm_num) hC))
      (sq_pos_of_pos calibration.dualGap_pos)) calibration.gamma_pos
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hN : (0 : Real) < N := by dsimp [N]; positivity
  have hNn : (n : Real) ≤ N := by
    dsimp [N]
    exact_mod_cast Nat.le_add_right n m
  have hell : 0 < ell := by exact commonMarginal_logEN_pos n hn
  have hLtwo := commonMarginal_degree_lower closure n L hn hL
  have hLpos : (0 : Real) < L := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
      hLtwo)
  have hLupper : (L : Real) ≤ (calibration.degreeConstant + 1) * ell := by
    exact commonMarginal_degree_upper calibration n L hn hL
  have hellN : ell ≤ N :=
    (commonMarginal_logEN_le_nat n hn).trans hNn
  have hrK : 4 * (calibration.degreeConstant + 1) / K ≤
      calibration.rareCountConstant := by
    simpa [K] using closure.rareCountLower
  have hxone : 1 ≤ calibration.rareCountConstant * N * L := by
    have hr : (4 : Real) ≤ calibration.rareCountConstant := closure.rareCountFloor
    have hN1 : (1 : Real) ≤ N := by
      dsimp [N]
      exact_mod_cast (show 1 ≤ n + m by omega)
    have hrN : (4 : Real) ≤ calibration.rareCountConstant * N := by
      nlinarith [mul_le_mul hr hN1 (by norm_num : (0 : Real) ≤ 1)
        calibration.rareCountConstant_pos.le]
    have hL1 : (1 : Real) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
    have hm := mul_le_mul_of_nonneg_right hrN (by positivity : (0 : Real) ≤ L)
    nlinarith
  have hfloorHalf :
      calibration.rareCountConstant * N * L / 2 ≤
        (⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊ : Real) := by
    simpa [N] using commonMarginal_half_le_floor hxone
  subst k
  by_cases hcap : d - 1 ≤
      ⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊
  · rw [min_eq_left hcap]
    have hkcast : ((d - 1 : Nat) : Real) = (d : Real) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hdR : (2 : Real) ≤ d := by exact_mod_cast hd
    have hkhalf : (d : Real) / 2 ≤ (d - 1 : Nat) := by
      rw [hkcast]
      linarith
    have hreg : calibration.regimeConstant / (n : Real) <
        (d : Real) ^ 2 / (N ^ 2 * ell ^ 2) := by
      have h := lt_of_not_ge hnon
      exact lt_of_lt_of_le h (min_le_right _ _)
    have hq : (4 * (calibration.degreeConstant + 1) ^ 2 / K) ^ 2 ≤
        calibration.regimeConstant := by
      simpa [K] using closure.regimeScale
    have hlogSqrt := commonMarginal_logEN_le_two_sqrt n hn
    have hsqrt : 0 < Real.sqrt (n : Real) := Real.sqrt_pos.2 hnR
    have hsqrtSq : Real.sqrt (n : Real) ^ 2 = n := Real.sq_sqrt hnR.le
    have hcross :
        (4 * (calibration.degreeConstant + 1) ^ 2 / K * N * ell) ^ 2 <
          ((d : Real) * Real.sqrt n) ^ 2 := by
      have hden2 : 0 < N ^ 2 * ell ^ 2 := mul_pos (sq_pos_of_pos hN) (sq_pos_of_pos hell)
      rw [div_lt_div_iff₀ hnR hden2] at hreg
      nlinarith [mul_nonneg (sq_nonneg N) (sq_nonneg ell), hq]
    have hcross' :
        4 * (calibration.degreeConstant + 1) ^ 2 / K * N * ell <
          (d : Real) * Real.sqrt n := by
      have hl0 : 0 ≤ 4 * (calibration.degreeConstant + 1) ^ 2 / K * N * ell := by
        positivity
      have hr0 : 0 ≤ (d : Real) * Real.sqrt n := by positivity
      exact (sq_lt_sq₀ hl0 hr0).mp hcross
    have htarget : 2 * (L : Real) ^ 2 / K ≤ d := by
      have hellS : ell * Real.sqrt n ≤ 2 * n := by
        nlinarith
      have hLN : ell * Real.sqrt n ≤ 2 * N := hellS.trans (by nlinarith)
      have hLU : (L : Real) ^ 2 ≤
          (calibration.degreeConstant + 1) ^ 2 * ell ^ 2 := by
        nlinarith [sq_nonneg
          ((calibration.degreeConstant + 1) * ell - (L : Real))]
      have hD1 : 0 < calibration.degreeConstant + 1 := by
        linarith [calibration.degreeConstant_pos]
      have hmul := mul_le_mul_of_nonneg_left hLN
        (mul_nonneg (mul_nonneg (by positivity : (0 : Real) ≤ 2)
          (sq_nonneg (calibration.degreeConstant + 1))) hell.le)
      have hcrossK :
          4 * (calibration.degreeConstant + 1) ^ 2 * N * ell <
            (d : Real) * Real.sqrt n * K := by
        have := mul_lt_mul_of_pos_right hcross' hK
        field_simp [ne_of_gt hK] at this
        simpa only [mul_assoc, mul_comm, mul_left_comm] using this
      have hLs : 2 * (L : Real) ^ 2 * Real.sqrt n ≤
          4 * (calibration.degreeConstant + 1) ^ 2 * N * ell := by
        nlinarith [mul_nonneg (sq_nonneg (L : Real)) hsqrt.le]
      have hLK : 2 * (L : Real) ^ 2 * Real.sqrt n <
          (d : Real) * Real.sqrt n * K := hLs.trans_lt hcrossK
      have hLK' : (2 * (L : Real) ^ 2) * Real.sqrt n <
          ((d : Real) * K) * Real.sqrt n := by
        convert hLK using 1 <;> ring
      have := lt_of_mul_lt_mul_right hLK' hsqrt.le
      exact le_of_lt ((div_lt_iff₀ hK).2 (by nlinarith [this]))
    change (L : Real) ^ 2 / K ≤ ((d - 1 : Nat) : Real)
    calc
      (L : Real) ^ 2 / K ≤ (d : Real) / 2 := by
        have ht' : 2 * ((L : Real) ^ 2 / K) ≤ (d : Real) := by
          calc
            2 * ((L : Real) ^ 2 / K) = 2 * (L : Real) ^ 2 / K := by ring
            _ ≤ (d : Real) := htarget
        calc
          (L : Real) ^ 2 / K = (2 * ((L : Real) ^ 2 / K)) / 2 := by ring
          _ ≤ (d : Real) / 2 :=
            div_le_div_of_nonneg_right ht' (by norm_num)
      _ ≤ ((d - 1 : Nat) : Real) := hkhalf
  · rw [min_eq_right (Nat.le_of_not_ge hcap)]
    have hscale : (L : Real) ^ 2 / K ≤
        calibration.rareCountConstant * N * L / 2 := by
      have hrare : 4 * (calibration.degreeConstant + 1) / K * N ≤
          calibration.rareCountConstant * N :=
        mul_le_mul_of_nonneg_right hrK hN.le
      have hLN : (L : Real) ≤ (calibration.degreeConstant + 1) * N :=
        hLupper.trans (mul_le_mul_of_nonneg_left hellN
          (by linarith [calibration.degreeConstant_pos]))
      have hrare' : 4 * (calibration.degreeConstant + 1) * N / K ≤
          calibration.rareCountConstant * N := by
        convert hrare using 1 <;> ring
      have htwo : 2 * (L : Real) / K ≤
          calibration.rareCountConstant * N := by
        have hLK : 2 * (L : Real) ≤
            4 * (calibration.degreeConstant + 1) * N := by nlinarith
        have := (div_le_div_iff_of_pos_right hK).2 hLK
        exact this.trans hrare'
      have hm := mul_le_mul_of_nonneg_right htwo hLpos.le
      calc
        (L : Real) ^ 2 / K = (2 * (L : Real) / K * L) / 2 := by ring
        _ ≤ (calibration.rareCountConstant * N * L) / 2 :=
          div_le_div_of_nonneg_right hm (by norm_num)
    exact hscale.trans hfloorHalf

set_option maxHeartbeats 1000000 in
/-- Either side of the capped rare-cell count supplies the corresponding
dimension-rate lower bound.  [the stated conditions](hyp:hn,hd,hL,hk,ha) [the stated conclusion](goal). -/
lemma commonMarginal_dimension_absorption {eps : Real}
    {calibration : CommonMarginalCalibration eps} {C rho : Real}
    (closure : CommonMarginalCalibrationClosure calibration C rho)
    (n m d L k : Nat) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (hL : L = Nat.ceil (calibration.degreeConstant * logEN n))
    (hk : k = min (d - 1)
      ⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊)
    (a : Real)
    (ha : a = calibration.gamma *
      (calibration.bandwidthConstant * L / (n + m : Nat)) / (L : Real) ^ 2) :
    calibration.dimensionConstant * commonMarginalDimensionTerm n m d ≤
      (calibration.dualGap * k * a) ^ 2 := by
  let N : Real := (n + m : Nat)
  let ell : Real := logEN n
  have hN : 0 < N := by dsimp [N]; positivity
  have hell : 0 < ell := commonMarginal_logEN_pos n hn
  have hLtwo := commonMarginal_degree_lower closure n L hn hL
  have hLpos : (0 : Real) < L := by exact_mod_cast (show 0 < L by omega)
  have hLupper := commonMarginal_degree_upper calibration n L hn hL
  have hxone : 1 ≤ calibration.rareCountConstant * N * L := by
    have hr := closure.rareCountFloor
    have hN1 : (1 : Real) ≤ N := by
      dsimp [N]
      exact_mod_cast (show 1 ≤ n + m by omega)
    have hrN : (4 : Real) ≤ calibration.rareCountConstant * N := by
      nlinarith [mul_le_mul hr hN1 (by norm_num : (0 : Real) ≤ 1)
        calibration.rareCountConstant_pos.le]
    have hL1 : (1 : Real) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
    have hm := mul_le_mul_of_nonneg_right hrN (by positivity : (0 : Real) ≤ L)
    nlinarith
  have hfloorHalf :
      calibration.rareCountConstant * N * L / 2 ≤
        (⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊ : Real) := by
    simpa [N] using commonMarginal_half_le_floor hxone
  have ha' : a = calibration.gamma * calibration.bandwidthConstant / (N * L) := by
    rw [ha]
    dsimp [N]
    field_simp [ne_of_gt hLpos, ne_of_gt hN]
  subst k
  by_cases hcap : d - 1 ≤
      ⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊
  · rw [min_eq_left hcap]
    have hkcast : ((d - 1 : Nat) : Real) = (d : Real) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hdR : (2 : Real) ≤ d := by exact_mod_cast hd
    have hkhalf : (d : Real) / 2 ≤ (d - 1 : Nat) := by
      rw [hkcast]
      linarith
    have hterm : commonMarginalDimensionTerm n m d ≤
        (d : Real) ^ 2 / (N ^ 2 * ell ^ 2) := by
      exact min_le_right _ _
    have hdim := closure.dimensionBranch
    rw [ha']
    have hD1 : 0 < calibration.degreeConstant + 1 := by
      linarith [calibration.degreeConstant_pos]
    have hdim0 : 0 ≤ calibration.dimensionConstant :=
      calibration.dimensionConstant_pos.le
    have hterm0 : 0 ≤ commonMarginalDimensionTerm n m d := by
      unfold commonMarginalDimensionTerm
      positivity
    calc
      calibration.dimensionConstant * commonMarginalDimensionTerm n m d ≤
          calibration.dimensionConstant *
            ((d : Real) ^ 2 / (N ^ 2 * ell ^ 2)) :=
        mul_le_mul_of_nonneg_left hterm hdim0
      _ ≤ (calibration.dualGap * calibration.gamma *
            calibration.bandwidthConstant /
              (2 * (calibration.degreeConstant + 1))) ^ 2 *
            ((d : Real) ^ 2 / (N ^ 2 * ell ^ 2)) :=
        mul_le_mul_of_nonneg_right hdim
          (div_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      _ ≤ (calibration.dualGap * (d - 1 : Nat) *
            (calibration.gamma * calibration.bandwidthConstant / (N * L))) ^ 2 := by
        have hdle : (d : Real) ≤ 2 * ((d - 1 : Nat) : Real) := by
          nlinarith [hkhalf]
        have hbase :
            calibration.dualGap * calibration.gamma *
                calibration.bandwidthConstant * (d : Real) /
                  (2 * (calibration.degreeConstant + 1) * N * ell) ≤
              calibration.dualGap * ((d - 1 : Nat) : Real) *
                (calibration.gamma * calibration.bandwidthConstant / (N * L)) := by
          rw [show calibration.dualGap * calibration.gamma *
                calibration.bandwidthConstant * (d : Real) /
                  (2 * (calibration.degreeConstant + 1) * N * ell) =
              (calibration.dualGap * calibration.gamma *
                calibration.bandwidthConstant * (d : Real)) /
                  ((2 * (calibration.degreeConstant + 1)) * (N * ell)) by ring,
            show calibration.dualGap * ((d - 1 : Nat) : Real) *
              (calibration.gamma * calibration.bandwidthConstant / (N * L)) =
            (calibration.dualGap * ((d - 1 : Nat) : Real) *
              (calibration.gamma * calibration.bandwidthConstant)) / (N * L) by ring]
          apply (div_le_div_iff₀
            (show 0 < (2 * (calibration.degreeConstant + 1)) * (N * ell) by
              exact mul_pos (mul_pos (by norm_num) hD1) (mul_pos hN hell))
            (mul_pos hN hLpos)).2
          have hcore : (d : Real) * L ≤
              (2 * ((d - 1 : Nat) : Real)) *
                ((calibration.degreeConstant + 1) * ell) :=
            mul_le_mul hdle hLupper (Nat.cast_nonneg _) (by positivity)
          have hm := mul_le_mul_of_nonneg_left hcore
            (mul_nonneg (mul_nonneg calibration.dualGap_pos.le
              calibration.gamma_pos.le) calibration.bandwidthConstant_pos.le)
          nlinarith
        have hbase0 : 0 ≤ calibration.dualGap * calibration.gamma *
            calibration.bandwidthConstant * (d : Real) /
              (2 * (calibration.degreeConstant + 1) * N * ell) := by
          exact div_nonneg (mul_nonneg (mul_nonneg
            (mul_nonneg calibration.dualGap_pos.le calibration.gamma_pos.le)
              calibration.bandwidthConstant_pos.le) (Nat.cast_nonneg _))
            (mul_nonneg (mul_nonneg
              (mul_nonneg (by norm_num : (0 : Real) ≤ 2) hD1.le) hN.le)
              hell.le)
        have hbaseR0 : 0 ≤ calibration.dualGap * ((d - 1 : Nat) : Real) *
            (calibration.gamma * calibration.bandwidthConstant / (N * L)) := by
          exact mul_nonneg
            (mul_nonneg calibration.dualGap_pos.le (Nat.cast_nonneg _))
            (div_nonneg (mul_nonneg calibration.gamma_pos.le
              calibration.bandwidthConstant_pos.le)
              (mul_nonneg hN.le hLpos.le))
        have hs := (sq_le_sq₀ hbase0 hbaseR0).2 hbase
        calc
          (calibration.dualGap * calibration.gamma *
                calibration.bandwidthConstant /
                  (2 * (calibration.degreeConstant + 1))) ^ 2 *
              ((d : Real) ^ 2 / (N ^ 2 * ell ^ 2)) =
              (calibration.dualGap * calibration.gamma *
                calibration.bandwidthConstant * (d : Real) /
                  (2 * (calibration.degreeConstant + 1) * N * ell)) ^ 2 := by
            field_simp [ne_of_gt hN, ne_of_gt hell, ne_of_gt hD1]
          _ ≤ _ := hs
  · rw [min_eq_right (Nat.le_of_not_ge hcap), ha']
    have hgap : calibration.dualGap ^ 2 / 4 ≤
        calibration.dualGap *
          (⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊ : Real) *
            (calibration.gamma * calibration.bandwidthConstant / (N * L)) := by
      rw [closure.rareCountIdentity]
      rw [closure.rareCountIdentity] at hfloorHalf
      have hgp := calibration.gamma_pos
      have hbp := calibration.bandwidthConstant_pos
      let t : Real := 2 * calibration.dualGap * calibration.gamma *
        calibration.bandwidthConstant / (N * L)
      have ht : 0 ≤ t := by
        dsimp [t]
        exact div_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg (by norm_num : (0 : Real) ≤ 2)
            calibration.dualGap_pos.le) calibration.gamma_pos.le)
          calibration.bandwidthConstant_pos.le)
          (mul_nonneg hN.le hLpos.le)
      have hm := mul_le_mul_of_nonneg_right hfloorHalf ht
      dsimp [t] at hm
      field_simp [ne_of_gt hN, ne_of_gt hLpos, ne_of_gt hgp,
        ne_of_gt hbp, ne_of_gt calibration.dualGap_pos] at hm ⊢
      nlinarith
    have hgap0 : 0 ≤ calibration.dualGap ^ 2 / 4 := by positivity
    have hright0 : 0 ≤ calibration.dualGap *
        (⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊ : Real) *
          (calibration.gamma * calibration.bandwidthConstant / (N * L)) := by
      exact mul_nonneg
        (mul_nonneg calibration.dualGap_pos.le (Nat.cast_nonneg _))
        (div_nonneg (mul_nonneg calibration.gamma_pos.le
          calibration.bandwidthConstant_pos.le)
          (mul_nonneg hN.le hLpos.le))
    have hsquare := (sq_le_sq₀ hgap0 hright0).2 hgap
    have hterm : commonMarginalDimensionTerm n m d ≤ 1 := min_le_left _ _
    calc
      calibration.dimensionConstant * commonMarginalDimensionTerm n m d ≤
          calibration.dimensionConstant * 1 :=
        mul_le_mul_of_nonneg_left hterm calibration.dimensionConstant_pos.le
      _ ≤ calibration.dualGap ^ 4 / 16 := by simpa using closure.dimensionRare
      _ = (calibration.dualGap ^ 2 / 4) ^ 2 := by ring
      _ ≤ _ := hsquare

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
