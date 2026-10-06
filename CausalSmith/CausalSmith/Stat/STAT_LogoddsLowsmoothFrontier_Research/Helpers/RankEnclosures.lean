module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.Upper
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Domain safety and containment for the represented rank computation

Valid exponent names intersect the public rectangle. Positive affine denominators
produce exponent boxes in [0,2]. A derivative bound for integer-base powers and the
cubic precision budget then give unit-width enclosures for both exact rank targets.
-/
public section
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [A shared real point certifies that the literal rational intersection succeeds.](goal) Under [the stated assumptions](hyp:x,hI,hJ). -/
-- @node: boxIntersection_exists_contains
lemma boxIntersection_exists_contains (I J : RatInterval) (x : ℝ)
    (hI : I.Contains x) (hJ : J.Contains x) :
    ∃ B, boxIntersection I J = some B ∧ B.Contains x ∧ B.Subinterval J := by
  have hlo : ((max I.lo J.lo : ℚ) : ℝ) ≤ x := by
    push_cast
    exact max_le hI.1 hJ.1
  have hhi : x ≤ ((min I.hi J.hi : ℚ) : ℝ) := by
    push_cast
    exact le_min hI.2 hJ.2
  have horder : max I.lo J.lo ≤ min I.hi J.hi := by exact_mod_cast hlo.trans hhi
  refine ⟨⟨max I.lo J.lo, min I.hi J.hi, horder⟩, ?_, ⟨hlo, hhi⟩,
    ⟨le_max_right _ _, min_le_right _ _⟩⟩
  simp [boxIntersection, horder]

/-- [Multiplication by a nonnegative point is the exact monotone endpoint operation.](goal) Under [the stated assumptions](hyp:ha). -/
-- @node: rank_point_mul_endpoints
lemma rank_point_mul_endpoints (a : ℚ) (ha : 0 ≤ a) (I : RatInterval) :
    ((RatInterval.point a).mul I).lo = a * I.lo ∧
    ((RatInterval.point a).mul I).hi = a * I.hi := by
  have h := mul_le_mul_of_nonneg_left I.lo_le_hi ha
  simp [RatInterval.mul, RatInterval.point, min_eq_left h, max_eq_right h]

/-- [A positive denominator above one gives a safe exponent box in [0,2].](goal) Under [the stated assumptions](hyp:hD,hd). -/
-- @node: rank_division_safe
lemma rank_division_safe (D : RatInterval) (hD : 1 ≤ D.lo) (d : ℝ)
    (hd : D.Contains d) :
    ∃ C, boxDiv (RatInterval.point 2) D = some C ∧
      C.Contains (2/d) ∧ 0 ≤ C.lo ∧ C.hi ≤ 2 ∧ C.width ≤ 2*D.width := by
  have hpos : 0 < D.lo := lt_of_lt_of_le (by norm_num) hD
  let C := (RatInterval.point 2).div D (Or.inr hpos)
  have he := rank_point_mul_endpoints 2 (by norm_num) (D.inv (Or.inr hpos))
  have hlo : C.lo = 2 * D.hi⁻¹ := he.1
  have hhi : C.hi = 2 * D.lo⁻¹ := he.2
  refine ⟨C, ?_, RatInterval.div_sound (Or.inr hpos) (by norm_num [RatInterval.Contains,
    RatInterval.point]) hd, ?_, ?_, ?_⟩
  · simp [boxDiv, hpos, C]
  · rw [hlo]
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (hpos.le.trans D.lo_le_hi))
  · rw [hhi]
    have hi : D.lo⁻¹ ≤ (1 : ℚ) := by
      simpa using (inv_le_inv₀ hpos (by norm_num : (0 : ℚ) < 1)).2 hD
    linarith

  · have hdhi : 0 < D.hi := hpos.trans_le D.lo_le_hi
    have hdprod : 1 ≤ D.lo * D.hi := by nlinarith [D.lo_le_hi]
    have hdelta : 0 ≤ D.hi - D.lo := sub_nonneg.mpr D.lo_le_hi
    rw [RatInterval.width, hlo, hhi]
    change 2 * D.lo⁻¹ - 2 * D.hi⁻¹ ≤ 2*(D.hi-D.lo)
    have hid : D.lo⁻¹ - D.hi⁻¹ = (D.hi-D.lo)/(D.lo*D.hi) := by
      field_simp
      <;> ring
    have hle : (D.hi-D.lo)/(D.lo*D.hi) ≤ D.hi-D.lo := by
      apply (div_le_iff₀ (mul_pos hpos hdhi)).2
      nlinarith
    linarith

/-- [The derivative bound on [0,2] controls the exact power range before primitive excess.](goal) Under [the stated assumptions](hyp:hn,hlo,hhi). -/
-- @node: rank_power_range_width
lemma rank_power_range_width (n : ℕ) (hn : 1 ≤ n) (I : RatInterval)
    (hlo : 0 ≤ I.lo) (hhi : I.hi ≤ 2) :
    (n : ℝ)^(I.hi : ℝ) - (n : ℝ)^(I.lo : ℝ) ≤
      (n : ℝ)^3 * (I.width : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hl : (0 : ℝ) ≤ I.lo := by exact_mod_cast hlo
  have hh : (I.hi : ℝ) ≤ 2 := by exact_mod_cast hhi
  have ho : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.lo_le_hi
  have hb (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 2) :
      ‖(n : ℝ)^v * Real.log n‖ ≤ (n : ℝ)^3 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hn0.le _)
      (Real.log_nonneg hn1))]
    have hp : (n : ℝ)^v ≤ (n : ℝ)^2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hn1 hv.2
    have hlog : Real.log (n : ℝ) ≤ n :=
      (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
    calc
      (n : ℝ)^v * Real.log n ≤ (n : ℝ)^2 * (n : ℝ) :=
        mul_le_mul hp hlog (Real.log_nonneg hn1) (by positivity)
      _ = (n : ℝ)^3 := by ring
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun v : ℝ => (n : ℝ)^v) (f' := fun v => (n : ℝ)^v * Real.log n)
    (fun v _ => by
      simpa [mul_comm] using ((hasDerivAt_id v).const_rpow hn0).hasDerivWithinAt)
    hb (convex_Icc (0 : ℝ) 2) ⟨hl, ho.trans hh⟩ ⟨hl.trans ho, hh⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ho)] at h
  exact (le_abs_self _).trans (by simpa [RatInterval.width] using h)

/-- [Power endpoint excess adds at most two precision errors to the exact range width.](goal) Under [the stated assumptions](hyp:hE,hn,hlo,hhi). -/
-- @node: rank_engine_power_width
lemma rank_engine_power_width (E : ArithmeticEngine) (hE : E.Admissible)
    (q n : ℕ) (hn : 1 ≤ n) (I : RatInterval) (hlo : 0 ≤ I.lo) (hhi : I.hi ≤ 2) :
    ((E.powBox q n I).width : ℝ) ≤ (n : ℝ)^3 * (I.width : ℝ) + 2*precisionError q := by
  have h := hE.2.2.2.2.2.1 q n I hn (by linarith) (by linarith)
  have hw := rank_power_range_width n hn I hlo hhi
  have hleft := h.1.2.2.1
  have hright := h.1.2.2.2.2
  simp only [RatInterval.width, Rat.cast_sub] at *
  linarith

/-- [The prescribed rank precision satisfies the cubic sample-size error budget. [the stated conclusion](goal) holds. -/
-- @node: rank_precision_cubic_bound
lemma rank_precision_cubic_bound (n : ℕ) :
    (128 : ℝ) * (n : ℝ)^3 * precisionError (qRank n) ≤ 1 := by
  have hpow : (n : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 n) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) n
  have hc : (n : ℝ)^3 ≤ ((2 : ℝ)^(Nat.clog 2 n))^3 := by gcongr
  rw [precisionError, qRank, zpow_neg, zpow_natCast]
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num))
    (by positivity)).trans
  apply le_of_eq
  rw [pow_add, pow_mul]
  norm_num
  field_simp
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

/-- Both rank computations succeed, contain their exact targets, and have width at most
one at the prescribed budget, uniformly over admissible engines and naming policies. [the documented result](goal) Under [the stated assumptions](hyp:hN,hn,hab). Under [the stated assumptions](hyp:hE). -/
-- @node: rankBoxes_rank_budget_contract
lemma rankBoxes_rank_budget_contract (E : ArithmeticEngine) (hE : E.Admissible)
    (N : NamingPolicy) (hN : N.Admissible) (n : ℕ) (hn : 1 ≤ n)
    (α β : ℝ) (hab : ExponentDomain α β) :
    ∃ c s, rankBoxes E N n α β = some (c,s) ∧
      c.Contains ((n : ℝ)^(2/(2*α+2*β+1))) ∧
      s.Contains ((n : ℝ)^(2/(4*β+1))) ∧ c.width ≤ 1 ∧ s.width ≤ 1 := by
  have hα : 0 < α := hab.1.trans hab.2.2.1
  have hβ : 0 < β := hab.1
  have haName := ((hN.1 n α β).1.1 (qRank n)).2.2.1
  have hbName := ((hN.1 n α β).2.1 (qRank n)).2.2.1
  have haPublic : (rationalBox 0 1).Contains α := by
    norm_num [rationalBox, RatInterval.Contains]
    exact ⟨hα.le, hab.2.2.2⟩
  have hbPublic : (rationalBox 0 (1/4)).Contains β := by
    norm_num [rationalBox, RatInterval.Contains]
    exact ⟨hβ.le, hab.2.1.le⟩
  obtain ⟨a, ha, haC, haS⟩ := boxIntersection_exists_contains _ _ α haName haPublic
  obtain ⟨b, hb, hbC, hbS⟩ := boxIntersection_exists_contains _ _ β hbName hbPublic
  have ha0 : 0 ≤ a.lo := by simpa [rationalBox] using haS.1
  have hb0 : 0 ≤ b.lo := by simpa [rationalBox] using hbS.1
  let DC := ((RatInterval.point 2).mul a |>.add ((RatInterval.point 2).mul b)
    |>.add (RatInterval.point 1))
  let DS := ((RatInterval.point 4).mul b).add (RatInterval.point 1)
  have hDC : 1 ≤ DC.lo := by
    change 1 ≤ ((RatInterval.point 2).mul a).lo +
      ((RatInterval.point 2).mul b).lo + 1
    rw [(rank_point_mul_endpoints 2 (by norm_num) a).1,
      (rank_point_mul_endpoints 2 (by norm_num) b).1]
    linarith
  have hDS : 1 ≤ DS.lo := by
    change 1 ≤ ((RatInterval.point 4).mul b).lo + 1
    rw [(rank_point_mul_endpoints 4 (by norm_num) b).1]
    linarith
  have hDCc : DC.Contains (2*α+2*β+1) := by
    exact RatInterval.add_sound (RatInterval.add_sound
      (RatInterval.mul_sound (by norm_num [RatInterval.Contains, RatInterval.point]) haC)
      (RatInterval.mul_sound (by norm_num [RatInterval.Contains, RatInterval.point]) hbC))
      (by norm_num [RatInterval.Contains, RatInterval.point])
  have hDSc : DS.Contains (4*β+1) := by
    exact RatInterval.add_sound
      (RatInterval.mul_sound (by norm_num [RatInterval.Contains, RatInterval.point]) hbC)
      (by norm_num [RatInterval.Contains, RatInterval.point])
  obtain ⟨C, hc, hCc, hC0, hC2, hCW⟩ := rank_division_safe DC hDC _ hDCc
  obtain ⟨S, hs, hSc, hS0, hS2, hSW⟩ := rank_division_safe DS hDS _ hDSc
  have hcPow := hE.2.2.2.2.2.1 (qRank n) n C hn (by linarith) (by linarith)
  have hsPow := hE.2.2.2.2.2.1 (qRank n) n S hn (by linarith) (by linarith)
  have haW : (a.width : ℝ) ≤ precisionError (qRank n) := by
    have haS' : a.Subinterval (N.alphaName n α β (qRank n)) := by
      unfold boxIntersection at ha
      split at ha
      · cases ha
        exact ⟨le_max_left _ _, min_le_left _ _⟩
      · cases ha
    have hw : (a.width : ℝ) ≤ (N.alphaName n α β (qRank n)).width := by
      exact_mod_cast RatInterval.width_mono haS'
    exact hw.trans (((hN.1 n α β).1.1 (qRank n)).2.2.2)
  have hbW : (b.width : ℝ) ≤ precisionError (qRank n) := by
    have hbS' : b.Subinterval (N.betaName n α β (qRank n)) := by
      unfold boxIntersection at hb
      split at hb
      · cases hb
        exact ⟨le_max_left _ _, min_le_left _ _⟩
      · cases hb
    have hw : (b.width : ℝ) ≤ (N.betaName n α β (qRank n)).width := by
      exact_mod_cast RatInterval.width_mono hbS'
    exact hw.trans (((hN.1 n α β).2.1 (qRank n)).2.2.2)
  have hDCW : (DC.width : ℝ) ≤ 4*precisionError (qRank n) := by
    have hEq : DC.width = 2*a.width + 2*b.width := by
      simp only [DC, RatInterval.width_add]
      simp only [RatInterval.width,
        (rank_point_mul_endpoints 2 (by norm_num) a).1,
        (rank_point_mul_endpoints 2 (by norm_num) a).2,
        (rank_point_mul_endpoints 2 (by norm_num) b).1,
        (rank_point_mul_endpoints 2 (by norm_num) b).2]
      simp only [RatInterval.point]
      ring
    rw [hEq]
    push_cast
    linarith
  have hDSW : (DS.width : ℝ) ≤ 4*precisionError (qRank n) := by
    have hEq : DS.width = 4*b.width := by
      simp only [DS, RatInterval.width_add]
      simp only [RatInterval.width,
        (rank_point_mul_endpoints 4 (by norm_num) b).1,
        (rank_point_mul_endpoints 4 (by norm_num) b).2]
      simp only [RatInterval.point]
      ring
    rw [hEq]
    push_cast
    linarith
  have hCW' : (C.width : ℝ) ≤ 8*precisionError (qRank n) := by
    have hw : (C.width : ℝ) ≤ 2*(DC.width : ℝ) := by exact_mod_cast hCW
    linarith
  have hSW' : (S.width : ℝ) ≤ 8*precisionError (qRank n) := by
    have hw : (S.width : ℝ) ≤ 2*(DS.width : ℝ) := by exact_mod_cast hSW
    linarith
  have hbudget : 8*(n : ℝ)^3*precisionError (qRank n) +
      2*precisionError (qRank n) ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn3 : (1 : ℝ) ≤ (n : ℝ)^3 := one_le_pow₀ hn1
    have he : 0 ≤ precisionError (qRank n) := by unfold precisionError; positivity
    have hp := rank_precision_cubic_bound n
    nlinarith
  refine ⟨E.powBox (qRank n) n C, E.powBox (qRank n) n S, ?_,
    hcPow.1.1 _ hCc, hsPow.1.1 _ hSc, ?_, ?_⟩
  · simp only [rankBoxes, ha, hb, Option.bind_some, hc, hs, pure]
    change (do
      let c ← boxDiv (RatInterval.point 2) DC
      let s ← boxDiv (RatInterval.point 2) DS
      pure (E.powBox (qRank n) n c, E.powBox (qRank n) n s)) = _
    rw [hc, hs]
    rfl
  · have hw := rank_engine_power_width E hE (qRank n) n hn C hC0 hC2
    have hr : ((E.powBox (qRank n) n C).width : ℝ) ≤ 1 :=
      hw.trans ((by gcongr : (n : ℝ)^3*(C.width : ℝ)+2*precisionError (qRank n) ≤
        (n : ℝ)^3*(8*precisionError (qRank n))+2*precisionError (qRank n)).trans
        (by nlinarith [hbudget]))
    exact_mod_cast hr
  · have hw := rank_engine_power_width E hE (qRank n) n hn S hS0 hS2
    have hr : ((E.powBox (qRank n) n S).width : ℝ) ≤ 1 :=
      hw.trans ((by gcongr : (n : ℝ)^3*(S.width : ℝ)+2*precisionError (qRank n) ≤
        (n : ℝ)^3*(8*precisionError (qRank n))+2*precisionError (qRank n)).trans
        (by nlinarith [hbudget]))
    exact_mod_cast hr
end CausalSmith.Stat.LogoddsLowsmoothFrontier
