module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.EndpointCoordinates

/-! # Literal endpoint radius enclosures

Negative powers on the public exponent rectangle have derivative bounded by the
integer base. Primitive endpoint excess and exact scaling then give the two
bias-and-noise radius widths in the fixed-budget roadmap.
-/
@[expose] public section
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Negative exponent ranges have variation at most the base times their width.](goal) Under [the stated assumptions](hyp:hk,hhi). -/
-- @node: endpoint_negative_power_range_width
lemma endpoint_negative_power_range_width (k : ℕ) (hk : 1 ≤ k) (I : RatInterval)
    (hhi : I.hi ≤ 0) :
    (k : ℝ)^(I.hi : ℝ) - (k : ℝ)^(I.lo : ℝ) ≤
      (k : ℝ) * (I.width : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
  have ho : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.lo_le_hi
  have hh : (I.hi : ℝ) ≤ 0 := by exact_mod_cast hhi
  have hb (v : ℝ) (hv : v ∈ Set.Icc (I.lo : ℝ) I.hi) :
      ‖(k : ℝ)^v * Real.log k‖ ≤ k := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hk0.le _)
      (Real.log_nonneg hk1))]
    have hp : (k : ℝ)^v ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1 (hv.2.trans hh)
    have hl : Real.log (k : ℝ) ≤ k :=
      (Real.log_le_sub_one_of_pos hk0).trans (by linarith)
    calc
      _ ≤ 1 * (k : ℝ) := mul_le_mul hp hl (Real.log_nonneg hk1) (by norm_num)
      _ = _ := one_mul _
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun v : ℝ => (k : ℝ)^v) (f' := fun v => (k : ℝ)^v * Real.log k)
    (fun v _ => by
      simpa [mul_comm] using ((hasDerivAt_id v).const_rpow hk0).hasDerivWithinAt)
    hb (convex_Icc (I.lo : ℝ) I.hi) ⟨le_rfl, ho⟩ ⟨ho, le_rfl⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ho)] at h
  exact (le_abs_self _).trans (by simpa [RatInterval.width] using h)

/-- [The power primitive adds at most two endpoint errors on a negative exponent box.](goal) Under [the stated assumptions](hyp:hE,hk,hlo,hhi). -/
-- @node: endpoint_negative_power_width
lemma endpoint_negative_power_width (E : ArithmeticEngine) (hE : E.Admissible)
    (q k : ℕ) (hk : 1 ≤ k) (I : RatInterval) (hlo : -3 ≤ I.lo) (hhi : I.hi ≤ 0) :
    ((E.powBox q k I).width : ℝ) ≤ (k : ℝ)*(I.width : ℝ)+2*precisionError q := by
  have h := hE.2.2.2.2.2.1 q k I hk hlo (hhi.trans (by norm_num))
  have hw := endpoint_negative_power_range_width k hk I hhi
  have hl := h.1.2.2.1
  have hr := h.1.2.2.2.2
  simp only [RatInterval.width, Rat.cast_sub] at *
  linarith

/-- [The variance quantity in the literal radius tree is an exact nonnegative rational.](goal) Under [the stated assumptions](hyp:hn). -/
-- @node: endpoint_variance_rational
lemma endpoint_variance_rational (n k : ℕ) (hn : 2 ≤ n) :
    0 ≤ (20 * (10/(n : ℚ)+4*k/((n : ℚ)*((n : ℚ)-1)))) ∧
    ((20 * (10/(n : ℚ)+4*k/((n : ℚ)*((n : ℚ)-1))) : ℚ) : ℝ) =
      20 * varianceRadius n k := by
  have hn' : (1 : ℚ) < n := by exact_mod_cast (show 1 < n by omega)
  constructor
  · positivity
  · simp [varianceRadius]

/-- [An exact nonnegative input has a square-root enclosure of width at most two errors.](goal) Under [the stated assumptions](hyp:hE,hn). -/
-- @node: endpoint_noise_enclosure
lemma endpoint_noise_enclosure (E : ArithmeticEngine) (hE : E.Admissible)
    (q n k : ℕ) (hn : 2 ≤ n) (xs : List RatInterval) :
    ∃ B : RatInterval,
      (BoxExpr.sqrt (.constant (20 * (10/(n : ℚ)+4*k/((n : ℚ)*((n : ℚ)-1)))))).eval E q xs = some B ∧
      B.Contains (Real.sqrt (20 * varianceRadius n k)) ∧
      (B.width : ℝ) ≤ 2*precisionError q := by
  let a : ℚ := 20 * (10/(n : ℚ)+4*k/((n : ℚ)*((n : ℚ)-1)))
  obtain ⟨ha, haReal⟩ := endpoint_variance_rational n k hn
  have hc := hE.2.2.2.2.1 q (RatInterval.point a) ha
  refine ⟨E.sqrtBox q (RatInterval.point a), ?_, ?_, ?_⟩
  · simp [BoxExpr.eval, a, RatInterval.point, ha]
  · rw [← haReal]
    exact hc.1.1 _ (RatInterval.point_sound a)
  · have hl := hc.1.2.2.1
    have hr := hc.1.2.2.2.2
    change Real.sqrt (a : ℝ) - (E.sqrtBox q (RatInterval.point a)).lo ≤ precisionError q at hl
    change (E.sqrtBox q (RatInterval.point a)).hi - Real.sqrt (a : ℝ) ≤ precisionError q at hr
    simp only [RatInterval.width, Rat.cast_sub]
    linarith

/-- [A successful power expression and its exact noise term assemble a scaled radius.](goal) Under [the stated assumptions](hyp:hE,hn,hk,he,hv,hlo,hhi,ha). Under [the stated assumptions](hyp:hw). -/
-- @node: endpoint_radius_enclosure
lemma endpoint_radius_enclosure (E : ArithmeticEngine) (hE : E.Admissible)
    (q n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (xs : List RatInterval)
    (e : BoxExpr) (I : RatInterval) (v : ℝ)
    (he : e.eval E q xs = some I) (hv : I.Contains v)
    (hlo : -3 ≤ I.lo) (hhi : I.hi ≤ 0)
    (hw : (I.width : ℝ) ≤ 2*precisionError q) (a : ℚ) (ha : 0 ≤ a) :
    ∃ B : RatInterval,
      (BoxExpr.add (.mul (.constant a) (.power k e))
        (.sqrt (.constant (20 * (10/(n : ℚ)+4*k/((n : ℚ)*((n : ℚ)-1))))))).eval E q xs = some B ∧
      B.Contains ((a : ℝ)*(k : ℝ)^v+Real.sqrt (20*varianceRadius n k)) ∧
      (B.width : ℝ) ≤ ((a : ℝ)*(2*(k : ℝ)+2)+2)*precisionError q := by
  let P := E.powBox q k I
  have hP := hE.2.2.2.2.2.1 q k I hk hlo (hhi.trans (by norm_num))
  have hPW := endpoint_negative_power_width E hE q k hk I hlo hhi
  obtain ⟨S, hS, hvS, hwS⟩ := endpoint_noise_enclosure E hE q n k hn xs
  refine ⟨((RatInterval.point a).mul P).add S, ?_, ?_, ?_⟩
  · have hdom : 1 ≤ k ∧ -3 ≤ I.lo ∧ I.hi ≤ 3 := ⟨hk, hlo, hhi.trans (by norm_num)⟩
    have hPower : (BoxExpr.power k e).eval E q xs = some P := by
      simp [BoxExpr.eval, he, hdom, P]
    have hMul : (BoxExpr.mul (.constant a) (.power k e)).eval E q xs =
        some ((RatInterval.point a).mul P) := by
      change (do let A ← some (RatInterval.point a); let B ← (BoxExpr.power k e).eval E q xs; pure (A.mul B)) = _
      rw [hPower]
      rfl
    change (do let A ← (BoxExpr.mul (.constant a) (.power k e)).eval E q xs
               let B ← (BoxExpr.sqrt (.constant (20 * (10/(n : ℚ)+4*k/((n : ℚ)*((n : ℚ)-1)))))).eval E q xs
               pure (A.add B)) = _
    rw [hMul, hS]
    rfl
  · exact RatInterval.add_sound
      (RatInterval.mul_sound (RatInterval.point_sound a) (hP.1.1 v hv)) hvS
  · rw [RatInterval.width_add, (endpoint_point_scale_width P a ha).2]
    push_cast
    have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
    have hPw : (P.width : ℝ) ≤ (2*(k : ℝ)+2)*precisionError q := by
      calc
        _ ≤ (k : ℝ)*(I.width : ℝ)+2*precisionError q := hPW
        _ ≤ (k : ℝ)*(2*precisionError q)+2*precisionError q := by gcongr
        _ = _ := by ring
    calc
      _ ≤ (a : ℝ)*((2*(k : ℝ)+2)*precisionError q)+2*precisionError q :=
        add_le_add (mul_le_mul_of_nonneg_left hPw ha') hwS
      _ = _ := by ring

/-- [The endpoint precision bounds the positive exponent overhang even after
multiplication by either retained rank. [the documented result](goal) -/
lemma endpoint_precision_rank_product (n kC kS : ℕ) :
    (max kC kS : ℕ)*precisionError (qEnd n kC kS) ≤ (1/16 : ℝ) := by
  have hk : ((max kC kS : ℕ) : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 (max kC kS+1)) := by
    have h : ((max kC kS : ℕ) : ℝ)+1 ≤ (2 : ℝ)^(Nat.clog 2 (max kC kS+1)) := by
      exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (max kC kS+1)
    linarith
  have hq : 4 + Nat.clog 2 (max kC kS+1) ≤ qEnd n kC kS := by unfold qEnd; omega
  have hp : 16*((max kC kS : ℕ) : ℝ) ≤ (2 : ℝ)^qEnd n kC kS := by
    calc
      _ ≤ (2 : ℝ)^4*(2 : ℝ)^(Nat.clog 2 (max kC kS+1)) := by
        simpa only [show (2 : ℝ)^4 = 16 by norm_num] using
          mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 16)
      _ = (2 : ℝ)^(4 + Nat.clog 2 (max kC kS+1)) := (pow_add _ _ _).symm
      _ ≤ _ := by gcongr; norm_num
  rw [precisionError, zpow_neg, zpow_natCast]
  have h := (mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ ((2 : ℝ)^qEnd n kC kS)⁻¹)).trans_eq
    (mul_inv_cancel₀ (by positivity))
  nlinarith

/-- A precision-sized positive overhang leaves the integer-base derivative bound
unchanged when the rank times the precision error is at most one sixteenth. [the documented result](goal) Under [the stated assumptions](hyp:hhi,hbudget). Under [the stated assumptions](hyp:hk). -/
-- @node: endpoint_raw_power_range_width
lemma endpoint_raw_power_range_width (k : ℕ) (hk : 1 ≤ k) (q : ℕ) (I : RatInterval)
    (hhi : (I.hi : ℝ) ≤ 2*precisionError q)
    (hbudget : (k : ℝ)*precisionError q ≤ 1/16) :
    (k : ℝ)^(I.hi : ℝ) - (k : ℝ)^(I.lo : ℝ) ≤
      (k : ℝ)*(I.width : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
  have ho : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.lo_le_hi
  have hb (v : ℝ) (hv : v ∈ Set.Icc (I.lo : ℝ) I.hi) :
      ‖(k : ℝ)^v * Real.log k‖ ≤ k := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hk0.le _)
      (Real.log_nonneg hk1))]
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hlogHalf := Real.log_le_sub_one_of_pos (by positivity : 0 < (k : ℝ)/2)
    have hlogSplit : Real.log (k : ℝ) = Real.log ((k : ℝ)/2) + Real.log 2 := by
      rw [← Real.log_mul (by positivity : (k : ℝ)/2 ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      ring
    have hlog : Real.log (k : ℝ) ≤ (k : ℝ)/2 := by linarith
    have hlog2Lower : (1/2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)
      rw [Real.log_inv] at h
      norm_num at h
      linarith
    have heps : 0 ≤ precisionError q := by unfold precisionError; positivity
    have hexp : Real.log (k : ℝ)*v ≤ Real.log 2 := by
      have hvUpper := hv.2.trans hhi
      have h₁ := mul_le_mul_of_nonneg_left hvUpper (Real.log_nonneg hk1)
      have h₂ := mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ 2*precisionError q)
      nlinarith
    have hpow : (k : ℝ)^v ≤ 2 := by
      rw [Real.rpow_def_of_pos hk0]
      exact (Real.exp_le_exp.mpr hexp).trans_eq (Real.exp_log (by norm_num))
    calc
      _ ≤ 2 * ((k : ℝ)/2) := mul_le_mul hpow hlog (Real.log_nonneg hk1) (by norm_num)
      _ = _ := by ring
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun v : ℝ => (k : ℝ)^v) (f' := fun v => (k : ℝ)^v * Real.log k)
    (fun v _ => by
      simpa [mul_comm] using ((hasDerivAt_id v).const_rpow hk0).hasDerivWithinAt)
    hb (convex_Icc (I.lo : ℝ) I.hi) ⟨le_rfl, ho⟩ ⟨ho, le_rfl⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ho)] at h
  exact (le_abs_self _).trans (by simpa [RatInterval.width] using h)


/-- [The primitive endpoint errors add twice the precision to the raw power range.](goal) Under [the stated assumptions](hyp:hE,hk,hlo,hq). Under [the stated assumptions](hyp:hk,hlo,hhi,hq,hbudget). -/
lemma endpoint_raw_power_width (E : ArithmeticEngine) (hE : E.Admissible)
    (q k : ℕ) (hk : 1 ≤ k) (I : RatInterval) (hlo : -3 ≤ I.lo)
    (hhi : (I.hi : ℝ) ≤ 2*precisionError q) (hq : precisionError q ≤ 1/4)
    (hbudget : (k : ℝ)*precisionError q ≤ 1/16) :
    ((E.powBox q k I).width : ℝ) ≤ (k : ℝ)*(I.width : ℝ)+2*precisionError q := by
  have hdom : I.hi ≤ 3 := by
    have h : (I.hi : ℝ) ≤ 3 := by linarith
    exact_mod_cast h
  have h := hE.2.2.2.2.2.1 q k I hk hlo hdom
  have hw := endpoint_raw_power_range_width k hk q I hhi hbudget
  have hl := h.1.2.2.1
  have hr := h.1.2.2.2.2
  simp only [RatInterval.width, Rat.cast_sub] at *
  linarith

/-- [The raw power expression and exact noise term assemble the same scaled radius.](goal) Under [the stated assumptions](hyp:hE,hn,hk,he,hv,hlo,hq,ha). Under [the stated assumptions](hyp:hn,hk,he,hv,hlo,hhi,hq,hbudget,hw,ha). -/
lemma endpoint_raw_radius_enclosure (E : ArithmeticEngine) (hE : E.Admissible)
    (q n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (xs : List RatInterval)
    (e : BoxExpr) (I : RatInterval) (v : ℝ)
    (he : e.eval E q xs = some I) (hv : I.Contains v)
    (hlo : -3 ≤ I.lo) (hhi : (I.hi : ℝ) ≤ 2*precisionError q)
    (hq : precisionError q ≤ 1/4)
    (hbudget : (k : ℝ)*precisionError q ≤ 1/16)
    (hw : (I.width : ℝ) ≤ 2*precisionError q) (a : ℚ) (ha : 0 ≤ a) :
    ∃ B : RatInterval,
      (BoxExpr.add (.mul (.constant a) (.power k e))
        (.sqrt (.constant (20 * (10/(n : ℚ)+4*k/((n : ℚ)*((n : ℚ)-1))))))).eval E q xs = some B ∧
      B.Contains ((a : ℝ)*(k : ℝ)^v+Real.sqrt (20*varianceRadius n k)) ∧
      (B.width : ℝ) ≤ ((a : ℝ)*(2*(k : ℝ)+2)+2)*precisionError q := by
  let P := E.powBox q k I
  have hdomHi : I.hi ≤ 3 := by
    have h : (I.hi : ℝ) ≤ 3 := by linarith
    exact_mod_cast h
  have hP := hE.2.2.2.2.2.1 q k I hk hlo hdomHi
  have hPW := endpoint_raw_power_width E hE q k hk I hlo hhi hq hbudget
  obtain ⟨S, hS, hvS, hwS⟩ := endpoint_noise_enclosure E hE q n k hn xs
  refine ⟨((RatInterval.point a).mul P).add S, ?_, ?_, ?_⟩
  · have hdom : 1 ≤ k ∧ -3 ≤ I.lo ∧ I.hi ≤ 3 := ⟨hk, hlo, hdomHi⟩
    have hPower : (BoxExpr.power k e).eval E q xs = some P := by
      simp [BoxExpr.eval, he, hdom, P]
    have hMul : (BoxExpr.mul (.constant a) (.power k e)).eval E q xs =
        some ((RatInterval.point a).mul P) := by
      change (do let A ← some (RatInterval.point a); let B ← (BoxExpr.power k e).eval E q xs; pure (A.mul B)) = _
      rw [hPower]
      rfl
    change (do let A ← (BoxExpr.mul (.constant a) (.power k e)).eval E q xs
               let B ← (BoxExpr.sqrt (.constant (20 * (10/(n : ℚ)+4*k/((n : ℚ)*((n : ℚ)-1)))))).eval E q xs
               pure (A.add B)) = _
    rw [hMul, hS]
    rfl
  · exact RatInterval.add_sound
      (RatInterval.mul_sound (RatInterval.point_sound a) (hP.1.1 v hv)) hvS
  · rw [RatInterval.width_add, (endpoint_point_scale_width P a ha).2]
    push_cast
    have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
    have hPw : (P.width : ℝ) ≤ (2*(k : ℝ)+2)*precisionError q := by
      calc
        _ ≤ (k : ℝ)*(I.width : ℝ)+2*precisionError q := hPW
        _ ≤ (k : ℝ)*(2*precisionError q)+2*precisionError q := by gcongr
        _ = _ := by ring
    calc
      _ ≤ (a : ℝ)*((2*(k : ℝ)+2)*precisionError q)+2*precisionError q :=
        add_le_add (mul_le_mul_of_nonneg_left hPw ha') hwS
      _ = _ := by ring

/-- [Successful endpoint queries retain the raw public exponent boxes with their
containment, widths, and precision-sized overhang beyond the public rectangle. [the documented result](goal) Under [the stated assumptions](hyp:hab,hInputs). Under [the stated assumptions](hyp:hN). -/
lemma endpoint_exponent_inputs (N : NamingPolicy) (hN : N.Admissible)
    (n : ℕ) (α β : ℝ) (hab : ExponentDomain α β) (o : Fin n → Record)
    (q : ℕ) (xs : List RatInterval) (hInputs : endpointInputs N n α β o q = some xs) :
    ∃ a b : RatInterval, xs[0]? = some a ∧ xs[1]? = some b ∧
      a.Contains α ∧ b.Contains β ∧
      -precisionError q ≤ (a.lo : ℝ) ∧ (a.hi : ℝ) ≤ 1 + precisionError q ∧
      -precisionError q ≤ (b.lo : ℝ) ∧ (b.hi : ℝ) ≤ 1/4 + precisionError q ∧
      (a.width : ℝ) ≤ precisionError q ∧ (b.width : ℝ) ≤ precisionError q := by
  have haName := ((hN.1 n α β).1.1 q).2.2
  have hbName := ((hN.1 n α β).2.1 q).2.2
  have haBounds := endpoint_raw_box_bounds _ α 0 1 (precisionError q)
    haName.1 (hab.1.trans hab.2.2.1).le hab.2.2.2 haName.2
  have hbBounds := endpoint_raw_box_bounds _ β 0 (1/4) (precisionError q)
    hbName.1 hab.1.le hab.2.1.le hbName.2
  simp only [endpointInputs, Option.some.injEq] at hInputs
  subst xs
  exact ⟨_, _, rfl, rfl, haName.1, hbName.1,
    by simpa using haBounds.1, haBounds.2,
    by simpa using hbBounds.1, hbBounds.2, haName.2, hbName.2⟩

/-- [The raw exponent trees remain in the primitive domain, with a two-error positive overhang.](goal) Under [the stated assumptions](hyp:ha,hb,haC,hbC,hq). Under [the stated assumptions](hyp:hb,haC,hbC,halo,hahi,hblo,hbhi,hq,haW,hbW). -/
lemma endpoint_bias_exponents (E : ArithmeticEngine) (q : ℕ) (xs : List RatInterval)
    (a b : RatInterval) (α β : ℝ) (ha : xs[0]? = some a) (hb : xs[1]? = some b)
    (haC : a.Contains α) (hbC : b.Contains β)
    (halo : -precisionError q ≤ (a.lo : ℝ)) (hahi : (a.hi : ℝ) ≤ 1 + precisionError q)
    (hblo : -precisionError q ≤ (b.lo : ℝ)) (hbhi : (b.hi : ℝ) ≤ 1/4 + precisionError q)
    (hq : precisionError q ≤ 1/4)
    (haW : (a.width : ℝ) ≤ precisionError q) (hbW : (b.width : ℝ) ≤ precisionError q) :
    ∃ I J : RatInterval,
      (BoxExpr.sub (.constant 0) (.add (.input 0) (.input 1))).eval E q xs = some I ∧
      (BoxExpr.mul (.constant (-2)) (.input 1)).eval E q xs = some J ∧
      I.Contains (-(α+β)) ∧ J.Contains (-2*β) ∧
      -3 ≤ I.lo ∧ (I.hi : ℝ) ≤ 2*precisionError q ∧
      -3 ≤ J.lo ∧ (J.hi : ℝ) ≤ 2*precisionError q ∧
      (I.width : ℝ) ≤ 2*precisionError q ∧ (J.width : ℝ) ≤ 2*precisionError q := by
  let I := (RatInterval.point 0).sub (a.add b)
  let J := (RatInterval.point (-2)).mul b
  have hJlo : J.lo = -2*b.hi := by
    have h := mul_le_mul_of_nonpos_left b.lo_le_hi (by norm_num : (-2 : ℚ) ≤ 0)
    simp [J, RatInterval.mul, RatInterval.point, min_eq_right h, max_eq_left h, b.lo_le_hi]
  have hJhi : J.hi = -2*b.lo := by
    have h := mul_le_mul_of_nonpos_left b.lo_le_hi (by norm_num : (-2 : ℚ) ≤ 0)
    simp [J, RatInterval.mul, RatInterval.point, min_eq_right h, max_eq_left h, b.lo_le_hi]
  refine ⟨I, J, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [BoxExpr.eval, ha, hb, I]
  · simp [BoxExpr.eval, hb, J]
  · simpa using RatInterval.sub_sound (RatInterval.point_sound 0) (RatInterval.add_sound haC hbC)
  · simpa only [Rat.cast_neg, Rat.cast_ofNat] using
      RatInterval.mul_sound (RatInterval.point_sound (-2)) hbC
  · dsimp [I, RatInterval.sub, RatInterval.neg, RatInterval.add, RatInterval.point]
    simp only [zero_add]
    have h : (-3 : ℝ) ≤ -((a.hi : ℝ)+(b.hi : ℝ)) := by linarith
    exact_mod_cast h
  · dsimp [I, RatInterval.sub, RatInterval.neg, RatInterval.add, RatInterval.point]
    push_cast
    linarith
  · rw [hJlo]
    have h : (-3 : ℝ) ≤ -2*(b.hi : ℝ) := by linarith
    exact_mod_cast h
  · rw [hJhi]
    push_cast
    linarith
  · simp only [I, RatInterval.width_sub, RatInterval.width_add]
    simp only [RatInterval.width, RatInterval.point, sub_self, zero_add, Rat.cast_add]
    simpa [RatInterval.width] using (show (a.width : ℝ)+(b.width : ℝ) ≤ 2*precisionError q by linarith)
  · have hJW : J.width = 2*b.width := by
      rw [RatInterval.width, hJlo, hJhi]
      dsimp [RatInterval.width]; ring
    rw [hJW]
    push_cast
    linarith

/-- [The two bias-and-noise subtrees used verbatim by the literal endpoint expressions. -/
-- @node: endpointRadiusExpressions
def endpointRadiusExpressions (n kC kS : ℕ) : BoxExpr × BoxExpr :=
  (.add (.mul (.constant 8) (.power kC (.sub (.constant 0) (.add (.input 0) (.input 1)))))
      (.sqrt (.constant (20 * (10/(n : ℚ)+4*kC/((n : ℚ)*((n : ℚ)-1)))))),
   .add (.mul (.constant 25) (.power kS (.mul (.constant (-2)) (.input 1))))
      (.sqrt (.constant (20 * (10/(n : ℚ)+4*kS/((n : ℚ)*((n : ℚ)-1)))))))

/-- At the actual endpoint inputs both radius subtrees terminate and have the roadmap widths. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hE,hN,hn,hkC,hkS,hab,hInputs) hold, and [the stated conclusion follows](goal). -/
-- @node: endpoint_radii_budget_contract
lemma endpoint_radii_budget_contract (E : ArithmeticEngine) (hE : E.Admissible)
    (N : NamingPolicy) (hN : N.Admissible) (n kC kS : ℕ) (hn : 2 ≤ n)
    (hkC : 1 ≤ kC) (hkS : 1 ≤ kS) (α β : ℝ) (hab : ExponentDomain α β)
    (o : Fin n → Record) (xs : List RatInterval)
    (hInputs : endpointInputs N n α β o (qEnd n kC kS) = some xs) :
    ∃ BC BS : RatInterval,
      (endpointRadiusExpressions n kC kS).1.eval E (qEnd n kC kS) xs = some BC ∧
      (endpointRadiusExpressions n kC kS).2.eval E (qEnd n kC kS) xs = some BS ∧
      BC.Contains (8*(kC : ℝ)^(-(α+β))+Real.sqrt (20*varianceRadius n kC)) ∧
      BS.Contains (25*(kS : ℝ)^(-2*β)+Real.sqrt (20*varianceRadius n kS)) ∧
      (BC.width : ℝ) ≤ 34*(max kC kS : ℕ)*precisionError (qEnd n kC kS) ∧
      (BS.width : ℝ) ≤ 102*(max kC kS : ℕ)*precisionError (qEnd n kC kS) := by
  have hq := endpoint_precision_small n kC kS
  have hbudget := endpoint_precision_rank_product n kC kS
  have hbudgetC : (kC : ℝ)*precisionError (qEnd n kC kS) ≤ 1/16 := by
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left kC kS)
      (by unfold precisionError; positivity)).trans hbudget
  have hbudgetS : (kS : ℝ)*precisionError (qEnd n kC kS) ≤ 1/16 := by
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right kC kS)
      (by unfold precisionError; positivity)).trans hbudget
  obtain ⟨a, b, ha, hb, haC, hbC, halo, hahi, hblo, hbhi, haW, hbW⟩ :=
    endpoint_exponent_inputs N hN n α β hab o _ xs hInputs
  obtain ⟨I, J, heI, heJ, hvI, hvJ, hloI, hhiI, hloJ, hhiJ, hwI, hwJ⟩ :=
    endpoint_bias_exponents E _ xs a b α β ha hb haC hbC halo hahi hblo hbhi hq haW hbW
  obtain ⟨BC, heBC, hvBC, hwBC⟩ := endpoint_raw_radius_enclosure E hE _ n kC hn hkC xs
    _ I _ heI hvI hloI hhiI hq hbudgetC hwI 8 (by norm_num)
  obtain ⟨BS, heBS, hvBS, hwBS⟩ := endpoint_raw_radius_enclosure E hE _ n kS hn hkS xs
    _ J _ heJ hvJ hloJ hhiJ hq hbudgetS hwJ 25 (by norm_num)
  have hkC' : (1 : ℝ) ≤ kC := by exact_mod_cast hkC
  have hkS' : (1 : ℝ) ≤ kS := by exact_mod_cast hkS
  have hKC : (kC : ℝ) ≤ (max kC kS : ℕ) := by exact_mod_cast le_max_left kC kS
  have hKS : (kS : ℝ) ≤ (max kC kS : ℕ) := by exact_mod_cast le_max_right kC kS
  have herr : 0 ≤ precisionError (qEnd n kC kS) := by unfold precisionError; positivity
  refine ⟨BC, BS, heBC, heBS, ?_, ?_, ?_, ?_⟩
  · simpa only [Rat.cast_ofNat] using hvBC
  · simpa only [Rat.cast_ofNat] using hvBS
  · apply hwBC.trans
    apply mul_le_mul_of_nonneg_right _ herr
    norm_num only [Rat.cast_ofNat]
    linarith
  · apply hwBS.trans
    apply mul_le_mul_of_nonneg_right _ herr
    norm_num only [Rat.cast_ofNat]
    linarith

/-- [The literal denominator clipping is safe for division and preserves the incoming width.](goal) Under [the stated assumptions](hyp:he,hv). Under [the stated assumptions](hyp:hw). -/
-- @node: endpoint_denominator_clip
lemma endpoint_denominator_clip (E : ArithmeticEngine) (q : ℕ) (xs : List RatInterval)
    (e : BoxExpr) (B : RatInterval) (v w : ℝ)
    (he : e.eval E q xs = some B) (hv : B.Contains v) (hw : (B.width : ℝ) ≤ w) :
    ∃ D : RatInterval,
      (BoxExpr.max (.constant (1/512)) (.min (.constant 1) e)).eval E q xs = some D ∧
      D.Contains (clip denominatorFloor 1 v) ∧
      1/512 ≤ D.lo ∧ D.hi ≤ 1 ∧ (D.width : ℝ) ≤ w := by
  let A := boxMin (RatInterval.point 1) B
  let D := boxMax (RatInterval.point (1/512)) A
  have hAc := (endpoint_min_max_contains (RatInterval.point 1) B 1 v
    (by norm_num [RatInterval.Contains, RatInterval.point]) hv).1
  have hDc := (endpoint_min_max_contains (RatInterval.point (1/512)) A (1/512) (min 1 v)
    (by norm_num [RatInterval.Contains, RatInterval.point]) hAc).2
  have hA := endpoint_min_max_endpoints (RatInterval.point 1) B
  have hD := endpoint_min_max_endpoints (RatInterval.point (1/512)) A
  have hB0 : (0 : ℝ) ≤ B.width := by exact_mod_cast B.width_nonneg
  have hw0 : (0 : ℝ) ≤ w := hB0.trans hw
  have hAW : (A.width : ℝ) ≤ w := by
    have h := (endpoint_min_max_width (RatInterval.point 1) B).1
    simp only [RatInterval.width, RatInterval.point, sub_self] at h
    have h' : (A.width : ℝ) ≤ max 0 (B.width : ℝ) := by
      exact_mod_cast h
    exact h'.trans (max_le hw0 hw)
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · simp [BoxExpr.eval, he, D, A]
  · simpa only [clip, denominatorFloor] using hDc
  · change 1/512 ≤ (boxMax (RatInterval.point (1/512)) A).lo
    rw [hD.2.2.1]
    exact le_max_left _ _
  · change (boxMax (RatInterval.point (1/512)) A).hi ≤ 1
    rw [hD.2.2.2]
    apply max_le (by norm_num [RatInterval.point])
    change (boxMin (RatInterval.point 1) B).hi ≤ 1
    rw [hA.2.1]
    exact min_le_left _ _
  · have h := (endpoint_min_max_width (RatInterval.point (1/512)) A).2
    simp only [RatInterval.width, RatInterval.point, sub_self] at h
    have h' : (D.width : ℝ) ≤ max 0 (A.width : ℝ) := by exact_mod_cast h
    exact h'.trans (max_le hw0 hAW)

/-- [Both literal denominator corners stay positive and have the roadmap's joint width.](goal) Under [the stated assumptions](hyp:hkS). Under [the stated assumptions](hyp:hS,hBS,hvS,hvBS,hwS,hwBS). -/
-- @node: endpoint_denominator_corners
lemma endpoint_denominator_corners (E : ArithmeticEngine) (q n kC kS : ℕ)
    (hkS : 1 ≤ kS) (xs : List RatInterval) (o : Fin n → Record) (β : ℝ)
    (S BS : RatInterval)
    (hS : (coordinateExpressions n kC kS o).2.eval E q xs = some S)
    (hBS : (endpointRadiusExpressions n kC kS).2.eval E q xs = some BS)
    (hvS : S.Contains (sHat n kS o))
    (hvBS : BS.Contains (25*(kS : ℝ)^(-2*β)+Real.sqrt (20*varianceRadius n kS)))
    (hwS : (S.width : ℝ) ≤ 160*(kS : ℝ)^2*precisionError q)
    (hwBS : (BS.width : ℝ) ≤ 102*(max kC kS : ℕ)*precisionError q) :
    ∃ Dm Dp : RatInterval,
      (BoxExpr.max (.constant (1/512)) (.min (.constant 1)
        (.sub (coordinateExpressions n kC kS o).2 (endpointRadiusExpressions n kC kS).2))).eval E q xs = some Dm ∧
      (BoxExpr.max (.constant (1/512)) (.min (.constant 1)
        (.add (coordinateExpressions n kC kS o).2 (endpointRadiusExpressions n kC kS).2))).eval E q xs = some Dp ∧
      Dm.Contains (clip denominatorFloor 1
        (sHat n kS o-(25*(kS : ℝ)^(-2*β)+Real.sqrt (20*varianceRadius n kS)))) ∧
      Dp.Contains (clip denominatorFloor 1
        (sHat n kS o+(25*(kS : ℝ)^(-2*β)+Real.sqrt (20*varianceRadius n kS)))) ∧
      1/512 ≤ Dm.lo ∧ Dm.hi ≤ 1 ∧ 1/512 ≤ Dp.lo ∧ Dp.hi ≤ 1 ∧
      (Dm.width : ℝ) ≤ 300*(max kC kS : ℕ)^2*precisionError q ∧
      (Dp.width : ℝ) ≤ 300*(max kC kS : ℕ)^2*precisionError q := by
  have hm : (BoxExpr.sub (coordinateExpressions n kC kS o).2
      (endpointRadiusExpressions n kC kS).2).eval E q xs = some (S.sub BS) := by
    change (do let A ← (coordinateExpressions n kC kS o).2.eval E q xs
               let B ← (endpointRadiusExpressions n kC kS).2.eval E q xs
               pure (A.sub B)) = _
    rw [hS, hBS]; rfl
  have hp : (BoxExpr.add (coordinateExpressions n kC kS o).2
      (endpointRadiusExpressions n kC kS).2).eval E q xs = some (S.add BS) := by
    change (do let A ← (coordinateExpressions n kC kS o).2.eval E q xs
               let B ← (endpointRadiusExpressions n kC kS).2.eval E q xs
               pure (A.add B)) = _
    rw [hS, hBS]; rfl
  have herr : 0 ≤ precisionError q := by unfold precisionError; positivity
  have hK : (1 : ℝ) ≤ (max kC kS : ℕ) := by exact_mod_cast hkS.trans (le_max_right kC kS)
  have hk : (kS : ℝ) ≤ (max kC kS : ℕ) := by exact_mod_cast le_max_right kC kS
  have hw : (S.width : ℝ)+(BS.width : ℝ) ≤
      300*(max kC kS : ℕ)^2*precisionError q := by
    calc
      _ ≤ (160*(kS : ℝ)^2+102*(max kC kS : ℕ))*precisionError q := by nlinarith [hwS, hwBS]
      _ ≤ (300*(max kC kS : ℕ)^2)*precisionError q := by
        apply mul_le_mul_of_nonneg_right _ herr
        have hk2 : (kS : ℝ)^2 ≤ ((max kC kS : ℕ) : ℝ)^2 := by gcongr
        nlinarith [sq_nonneg (((max kC kS : ℕ) : ℝ)-1)]
  have hwm : ((S.sub BS).width : ℝ) ≤ 300*(max kC kS : ℕ)^2*precisionError q := by
    rw [RatInterval.width_sub, Rat.cast_add]; exact hw
  have hwp : ((S.add BS).width : ℝ) ≤ 300*(max kC kS : ℕ)^2*precisionError q := by
    rw [RatInterval.width_add, Rat.cast_add]; exact hw
  obtain ⟨Dm, heDm, hvDm, hloDm, hhiDm, hwDm⟩ := endpoint_denominator_clip E q xs _
    _ _ _ hm (RatInterval.sub_sound hvS hvBS) hwm
  obtain ⟨Dp, heDp, hvDp, hloDp, hhiDp, hwDp⟩ := endpoint_denominator_clip E q xs _
    _ _ _ hp (RatInterval.add_sound hvS hvBS) hwp
  exact ⟨Dm, Dp, heDm, heDp, hvDm, hvDp, hloDm, hhiDm, hloDp, hhiDp, hwDm, hwDp⟩

end CausalSmith.Stat.LogoddsLowsmoothFrontier
