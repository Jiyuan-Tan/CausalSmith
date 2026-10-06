module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.RankEnclosures

/-! # Range operations for the fixed endpoint budget

Exact minimum and maximum ranges preserve containment and the larger input width.
Product ranges obey the cross-product variation inequality used in the endpoint
roadmap. These estimates concern literal rational operations, not ideal ranges.
-/
public section
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Ordered input endpoints remain ordered after taking either minimum or maximum. [the stated conclusion](goal) holds. -/
-- @node: endpoint_min_max_endpoints
lemma endpoint_min_max_endpoints (I J : RatInterval) :
    (boxMin I J).lo = min I.lo J.lo ∧ (boxMin I J).hi = min I.hi J.hi ∧
    (boxMax I J).lo = max I.lo J.lo ∧ (boxMax I J).hi = max I.hi J.hi := by
  have hmin := min_le_min I.lo_le_hi J.lo_le_hi
  have hmax := max_le_max I.lo_le_hi J.lo_le_hi
  simp [boxMin, boxMax, rationalBox, min_eq_left hmin, max_eq_right hmin,
    min_eq_left hmax, max_eq_right hmax]

/-- Exact minimum and maximum ranges contain the corresponding real operations. Under the stated assumptions. [The stated hypotheses](hyp:hx,hy) hold, and [the stated conclusion follows](goal). -/
-- @node: endpoint_min_max_contains
lemma endpoint_min_max_contains (I J : RatInterval) (x y : ℝ)
    (hx : I.Contains x) (hy : J.Contains y) :
    (boxMin I J).Contains (min x y) ∧ (boxMax I J).Contains (max x y) := by
  obtain ⟨hml, hmh, hxl, hxh⟩ := endpoint_min_max_endpoints I J
  simp only [RatInterval.Contains, hml, hmh, hxl, hxh, Rat.cast_min, Rat.cast_max]
  exact ⟨⟨min_le_min hx.1 hy.1, min_le_min hx.2 hy.2⟩,
    ⟨max_le_max hx.1 hy.1, max_le_max hx.2 hy.2⟩⟩

/-- [Minimum and maximum ranges have width at most the larger input width. [the stated conclusion](goal) holds. -/
-- @node: endpoint_min_max_width
lemma endpoint_min_max_width (I J : RatInterval) :
    (boxMin I J).width ≤ max I.width J.width ∧
    (boxMax I J).width ≤ max I.width J.width := by
  obtain ⟨hml, hmh, hxl, hxh⟩ := endpoint_min_max_endpoints I J
  have hI : I.hi ≤ I.lo + max I.width J.width := by
    have := le_max_left I.width J.width
    change I.hi - I.lo ≤ max I.width J.width at this
    linarith
  have hJ : J.hi ≤ J.lo + max I.width J.width := by
    have := le_max_right I.width J.width
    change J.hi - J.lo ≤ max I.width J.width at this
    linarith
  have hm := min_le_min hI hJ
  have hx := max_le_max hI hJ
  rw [min_add_add_right] at hm
  rw [max_add_add_right] at hx
  change (boxMin I J).hi - (boxMin I J).lo ≤ max I.width J.width ∧
    (boxMax I J).hi - (boxMax I J).lo ≤ max I.width J.width
  rw [hml, hmh, hxl, hxh]
  constructor <;> linarith

/-- Inserting the cross product bounds product variation by two coordinate variations. Under the stated assumptions. [The stated hypotheses](hyp:hB₁,hB₂,hx,hy,hdx,hdy) hold, and [the stated conclusion follows](goal). -/
-- @node: endpoint_product_variation
lemma endpoint_product_variation (x x' y y' B₁ B₂ w₁ w₂ : ℚ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hx : |x'| ≤ B₁) (hy : |y| ≤ B₂)
    (hdx : |x - x'| ≤ w₁) (hdy : |y - y'| ≤ w₂) :
    x*y-x'*y' ≤ B₂*w₁+B₁*w₂ := by
  calc
    x*y-x'*y' ≤ |x*y-x'*y'| := le_abs_self _
    _ = |y*(x-x')+x'*(y-y')| := by congr 1; ring
    _ ≤ |y*(x-x')|+|x'*(y-y')| := abs_add_le _ _
    _ = |y| *|x - x'|+|x'| *|y - y'| := by rw [abs_mul, abs_mul]
    _ ≤ B₂*w₁+B₁*w₂ := add_le_add
      (mul_le_mul hy hdx (abs_nonneg _) hB₂)
      (mul_le_mul hx hdy (abs_nonneg _) hB₁)

/-- [Two points of a rational range differ by at most its width.](goal) Under [the stated assumptions](hyp:x,hx,hx'). -/
-- @node: endpoint_range_difference
lemma endpoint_range_difference (I : RatInterval) (x x' : ℚ)
    (hx : I.lo ≤ x ∧ x ≤ I.hi) (hx' : I.lo ≤ x' ∧ x' ≤ I.hi) :
    |x - x'| ≤ I.width := by
  rw [abs_le]
  dsimp [RatInterval.width]
  constructor <;> linarith [hx.1, hx.2, hx'.1, hx'.2]

/-- [A uniform magnitude bound on both endpoints bounds every point of the range.](goal) Under [the stated assumptions](hyp:x,hlo,hhi,hx). -/
-- @node: endpoint_range_abs
lemma endpoint_range_abs (I : RatInterval) (B x : ℚ)
    (hlo : |I.lo| ≤ B) (hhi : |I.hi| ≤ B)
    (hx : I.lo ≤ x ∧ x ≤ I.hi) : |x| ≤ B := by
  rw [abs_le] at hlo hhi ⊢
  exact ⟨hlo.1.trans hx.1, hx.2.trans hhi.2⟩

/-- [The literal four-corner product has the cross-product width bound.](goal) Under [the stated assumptions](hyp:hB₁,hB₂,hIlo,hIhi,hJlo,hJhi). -/
-- @node: endpoint_product_width
lemma endpoint_product_width (I J : RatInterval) (B₁ B₂ : ℚ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hIlo : |I.lo| ≤ B₁) (hIhi : |I.hi| ≤ B₁)
    (hJlo : |J.lo| ≤ B₂) (hJhi : |J.hi| ≤ B₂) :
    (I.mul J).width ≤ B₂*I.width+B₁*J.width := by
  have h (x x' y y' : ℚ)
      (hx : I.lo ≤ x ∧ x ≤ I.hi) (hx' : I.lo ≤ x' ∧ x' ≤ I.hi)
      (hy : J.lo ≤ y ∧ y ≤ J.hi) (hy' : J.lo ≤ y' ∧ y' ≤ J.hi) :
      x*y-x'*y' ≤ B₂*I.width+B₁*J.width :=
    endpoint_product_variation x x' y y' B₁ B₂ I.width J.width hB₁ hB₂
      (endpoint_range_abs I B₁ x' hIlo hIhi hx')
      (endpoint_range_abs J B₂ y hJlo hJhi hy)
      (endpoint_range_difference I x x' hx hx')
      (endpoint_range_difference J y y' hy hy')
  have hIl : I.lo ≤ I.lo ∧ I.lo ≤ I.hi := ⟨le_rfl, I.lo_le_hi⟩
  have hIh : I.lo ≤ I.hi ∧ I.hi ≤ I.hi := ⟨I.lo_le_hi, le_rfl⟩
  have hJl : J.lo ≤ J.lo ∧ J.lo ≤ J.hi := ⟨le_rfl, J.lo_le_hi⟩
  have hJh : J.lo ≤ J.hi ∧ J.hi ≤ J.hi := ⟨J.lo_le_hi, le_rfl⟩
  dsimp [RatInterval.width] at h ⊢
  simp only [RatInterval.mul]
  rw [sub_le_iff_le_add]
  simp only [max_le_iff, ← min_add_add_left, le_min_iff]
  repeat' apply And.intro
  all_goals first
    | linarith only [h _ _ _ _ hIl hIl hJl hJl ]
    | linarith only [h _ _ _ _ hIl hIl hJl hJh ]
    | linarith only [h _ _ _ _ hIl hIl hJh hJl ]
    | linarith only [h _ _ _ _ hIl hIl hJh hJh ]
    | linarith only [h _ _ _ _ hIl hIh hJl hJl ]
    | linarith only [h _ _ _ _ hIl hIh hJl hJh ]
    | linarith only [h _ _ _ _ hIl hIh hJh hJl ]
    | linarith only [h _ _ _ _ hIl hIh hJh hJh ]
    | linarith only [h _ _ _ _ hIh hIl hJl hJl ]
    | linarith only [h _ _ _ _ hIh hIl hJl hJh ]
    | linarith only [h _ _ _ _ hIh hIl hJh hJl ]
    | linarith only [h _ _ _ _ hIh hIl hJh hJh ]
    | linarith only [h _ _ _ _ hIh hIh hJl hJl ]
    | linarith only [h _ _ _ _ hIh hIh hJl hJh ]
    | linarith only [h _ _ _ _ hIh hIh hJh hJl ]

/-- Uniform endpoint magnitudes multiply under the literal four-corner product. Under the stated assumptions. [The stated hypotheses](hyp:hB₁,_hB₂,hIlo,hIhi,hJlo,hJhi) hold, and [the stated conclusion follows](goal). -/
-- @node: endpoint_product_abs
lemma endpoint_product_abs (I J : RatInterval) (B₁ B₂ : ℚ)
    (hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (hIlo : |I.lo| ≤ B₁) (hIhi : |I.hi| ≤ B₁)
    (hJlo : |J.lo| ≤ B₂) (hJhi : |J.hi| ≤ B₂) :
    |(I.mul J).lo| ≤ B₁*B₂ ∧ |(I.mul J).hi| ≤ B₁*B₂ := by
  have hll : |I.lo * J.lo| ≤ B₁*B₂ := by
    rw [abs_mul]; exact mul_le_mul hIlo hJlo (abs_nonneg _) hB₁
  have hlh : |I.lo * J.hi| ≤ B₁*B₂ := by
    rw [abs_mul]; exact mul_le_mul hIlo hJhi (abs_nonneg _) hB₁
  have hhl : |I.hi * J.lo| ≤ B₁*B₂ := by
    rw [abs_mul]; exact mul_le_mul hIhi hJlo (abs_nonneg _) hB₁
  have hhh : |I.hi * J.hi| ≤ B₁*B₂ := by
    rw [abs_mul]; exact mul_le_mul hIhi hJhi (abs_nonneg _) hB₁
  rw [abs_le] at hll hlh hhl hhh
  simp only [RatInterval.mul, abs_le, le_min_iff, max_le_iff]
  constructor
  · constructor
    · exact ⟨⟨hll.1, hlh.1⟩, hhl.1, hhh.1⟩
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans hll.2)
  · constructor
    · exact (hll.1.trans (le_max_left _ _)).trans (le_max_left _ _)
    · exact ⟨⟨hll.2, hlh.2⟩, hhl.2, hhh.2⟩

/-- [Every admissible engine supplies a two-error-width pi box in [3,4].](goal) Under [the stated assumptions](hyp:hE). -/
-- @node: endpoint_pi_contract
lemma endpoint_pi_contract (E : ArithmeticEngine) (hE : E.Admissible) (q : ℕ) :
    ((E.piBox q).width : ℝ) ≤ 2*precisionError q ∧
    |(E.piBox q).lo| ≤ 4 ∧ |(E.piBox q).hi| ≤ 4 := by
  obtain ⟨hContains, hlo, hhi, hlerr, hherr⟩ := hE.2.1 q
  refine ⟨?_, ?_, ?_⟩
  · simp only [RatInterval.width, Rat.cast_sub]
    linarith
  · rw [abs_le]
    constructor <;> linarith [(E.piBox q).lo_le_hi]
  · rw [abs_le]
    constructor <;> linarith [(E.piBox q).lo_le_hi]

/-- [The cosine primitive encloses its exact image, stays in [-1,1], and
adds only two precision errors to the argument width. [the documented result](goal) Under [the stated assumptions](hyp:hE). -/
-- @node: endpoint_cos_contract
lemma endpoint_cos_contract (E : ArithmeticEngine) (hE : E.Admissible)
    (q : ℕ) (I : RatInterval) :
    (∀ x, I.Contains x → (E.cosBox q I).Contains (Real.cos x)) ∧
    |(E.cosBox q I).lo| ≤ 1 ∧ |(E.cosBox q I).hi| ≤ 1 ∧
    ((E.cosBox q I).width : ℝ) ≤ (I.width : ℝ)+2*precisionError q := by
  obtain ⟨hContains, a, b, ha, hb, hae, hbe, hal, hbh, hlo, hhi, hw⟩ :=
    hE.2.2.2.2.2.2 q I
  have hl : -1 ≤ (E.cosBox q I).lo := by rw [hlo]; exact le_max_left _ _
  have hh : (E.cosBox q I).hi ≤ 1 := by rw [hhi]; exact min_le_left _ _
  refine ⟨hContains, abs_le.mpr ⟨hl, (E.cosBox q I).lo_le_hi.trans hh⟩,
    abs_le.mpr ⟨hl.trans (E.cosBox q I).lo_le_hi, hh⟩, ?_⟩
  simp only [RatInterval.width, Rat.cast_sub] at hw ⊢
  linarith

/-- [The square-root-of-two primitive has width at most two precision errors;
when the error is at most one quarter its entire range has magnitude at most two. [the documented result](goal) Under [the stated assumptions](hyp:hq). Under [the stated assumptions](hyp:hE). -/
-- @node: endpoint_sqrt_two_contract
lemma endpoint_sqrt_two_contract (E : ArithmeticEngine) (hE : E.Admissible)
    (q : ℕ) (hq : precisionError q ≤ 1 / 4) :
    (E.sqrtBox q (RatInterval.point 2)).Contains (Real.sqrt 2) ∧
    ((E.sqrtBox q (RatInterval.point 2)).width : ℝ) ≤ 2*precisionError q ∧
    |(E.sqrtBox q (RatInterval.point 2)).lo| ≤ 2 ∧
    |(E.sqrtBox q (RatInterval.point 2)).hi| ≤ 2 := by
  obtain ⟨hc, hlo⟩ := hE.2.2.2.2.1 q (RatInterval.point 2) (by norm_num [RatInterval.point])
  have hContains := hc.1 _ (RatInterval.point_sound 2)
  have hLower := hc.2.1
  have hLowerErr := hc.2.2.1
  have hUpper := hc.2.2.2.1
  have hUpperErr := hc.2.2.2.2
  have hsqrt : Real.sqrt 2 ≤ 3/2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  change 0 ≤ Real.sqrt 2 - (E.sqrtBox q (RatInterval.point 2)).lo at hLower
  change Real.sqrt 2 - (E.sqrtBox q (RatInterval.point 2)).lo ≤ precisionError q at hLowerErr
  change 0 ≤ (E.sqrtBox q (RatInterval.point 2)).hi - Real.sqrt 2 at hUpper
  change (E.sqrtBox q (RatInterval.point 2)).hi - Real.sqrt 2 ≤ precisionError q at hUpperErr
  have hhi : (E.sqrtBox q (RatInterval.point 2)).hi ≤ 2 := by
    have : ((E.sqrtBox q (RatInterval.point 2)).hi : ℝ) ≤ 2 := by linarith
    exact_mod_cast this
  refine ⟨hContains, ?_, ?_, ?_⟩
  · simp only [RatInterval.width, Rat.cast_sub]
    linarith
  · rw [abs_of_nonneg hlo]
    exact (E.sqrtBox q (RatInterval.point 2)).lo_le_hi.trans hhi
  · rw [abs_of_nonneg (hlo.trans (E.sqrtBox q (RatInterval.point 2)).lo_le_hi)]
    exact hhi

/-- [Multiplication on the right by a nonnegative point scales both endpoints exactly.](goal) Under [the stated assumptions](hyp:ha). -/
-- @node: endpoint_mul_point_endpoints
lemma endpoint_mul_point_endpoints (I : RatInterval) (a : ℚ) (ha : 0 ≤ a) :
    (I.mul (RatInterval.point a)).lo = I.lo*a ∧
    (I.mul (RatInterval.point a)).hi = I.hi*a := by
  have h := mul_le_mul_of_nonneg_right I.lo_le_hi ha
  simp [RatInterval.mul, RatInterval.point, min_eq_left h, max_eq_right h]

/-- [The literal cosine basis tree terminates, contains its exact value, has
magnitude at most two, and has width at most twenty times the index plus one
precision errors, uniformly over engines and covariate enclosures. [the documented result](goal) Under [the stated assumptions](hyp:hq,hinput,x,hx,hXlo,hXhi,hXW). Under [the stated assumptions](hyp:hE). -/
lemma endpoint_basis_enclosure (E : ArithmeticEngine) (hE : E.Admissible)
    (q : ℕ) (hq : precisionError q ≤ 1 / 4) (j i : ℕ) (xs : List RatInterval)
    (X : RatInterval) (hinput : xs[2 + i]? = some X) (x : Covariate)
    (hx : X.Contains (x : ℝ)) (hXlo : -precisionError q ≤ (X.lo : ℝ))
    (hXhi : (X.hi : ℝ) ≤ 1 + precisionError q)
    (hXW : (X.width : ℝ) ≤ precisionError q) :
    ∃ B : RatInterval, (basisExpression j i).eval E q xs = some B ∧
      B.Contains (cosineBasis j x) ∧ |B.lo| ≤ 2 ∧ |B.hi| ≤ 2 ∧
      (B.width : ℝ) ≤ 20*((j : ℝ)+1)*precisionError q := by
  have herr : 0 ≤ precisionError q := by unfold precisionError; positivity
  by_cases hj : j = 0
  · subst j
    refine ⟨RatInterval.point 1, ?_, ?_, ?_, ?_, ?_⟩
    · simp [basisExpression, BoxExpr.eval]
    · simp [cosineBasis]
    · norm_num [RatInterval.point]
    · norm_num [RatInterval.point]
    · simp only [RatInterval.width, RatInterval.point]
      push_cast
      nlinarith
  · let P := (E.piBox q).mul (RatInterval.point (j : ℚ))
    let A := P.mul X
    let C := E.cosBox q A
    let S := E.sqrtBox q (RatInterval.point 2)
    let B := S.mul C
    obtain ⟨hπW, hπl, hπh⟩ := endpoint_pi_contract E hE q
    obtain ⟨hSl, hSW, hSlo, hShi⟩ := endpoint_sqrt_two_contract E hE q hq
    obtain ⟨hPl, hPh⟩ := endpoint_mul_point_endpoints (E.piBox q) (j : ℚ) (by positivity)
    have hPW : (P.width : ℝ) ≤ 2*(j : ℝ)*precisionError q := by
      have heq : P.width = (E.piBox q).width*(j : ℚ) := by
        change P.hi - P.lo = ((E.piBox q).hi - (E.piBox q).lo)*(j : ℚ)
        dsimp only [P]
        rw [hPl, hPh]
        ring
      rw [heq]
      push_cast
      nlinarith
    have hPlo : |P.lo| ≤ 4*(j : ℚ) := by
      dsimp only [P]; rw [hPl, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ j)]
      exact mul_le_mul_of_nonneg_right hπl (by positivity)
    have hPhi : |P.hi| ≤ 4*(j : ℚ) := by
      dsimp only [P]; rw [hPh, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ j)]
      exact mul_le_mul_of_nonneg_right hπh (by positivity)
    have hXorder : (X.lo : ℝ) ≤ X.hi := by exact_mod_cast X.lo_le_hi
    have hXl : |X.lo| ≤ 5/4 := by
      have h : |(X.lo : ℝ)| ≤ ((5/4 : ℚ) : ℝ) := by
        norm_num; rw [abs_le]; constructor <;> linarith
      exact_mod_cast h
    have hXh : |X.hi| ≤ 5/4 := by
      have h : |(X.hi : ℝ)| ≤ ((5/4 : ℚ) : ℝ) := by
        norm_num; rw [abs_le]; constructor <;> linarith
      exact_mod_cast h
    have hAW : (A.width : ℝ) ≤ (13/2)*(j : ℝ)*precisionError q := by
      have hw := endpoint_product_width P X (4*(j : ℚ)) (5/4) (by positivity)
        (by norm_num) hPlo hPhi hXl hXh
      have hw' : (A.width : ℝ) ≤ ((5/4 : ℚ) : ℝ)*(P.width : ℝ)+
          ((4*(j : ℚ) : ℚ) : ℝ)*(X.width : ℝ) := by exact_mod_cast hw
      norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] at hw'
      nlinarith
    obtain ⟨hCos, hClo, hChi, hCW⟩ := endpoint_cos_contract E hE q A
    have hBlo : |B.lo| ≤ 2 := by
      simpa only [mul_one] using
        (endpoint_product_abs S C 2 1 (by norm_num) (by norm_num) hSlo hShi hClo hChi).1
    have hBhi : |B.hi| ≤ 2 := by
      simpa only [mul_one] using
        (endpoint_product_abs S C 2 1 (by norm_num) (by norm_num) hSlo hShi hClo hChi).2
    refine ⟨B, ?_, ?_, hBlo, hBhi, ?_⟩
    · simp [basisExpression, hj, BoxExpr.eval, hinput, B, S, C, A, P, RatInterval.point]
    · have hArg : A.Contains (Real.pi*(j : ℝ)*(x : ℝ)) :=
        RatInterval.mul_sound (RatInterval.mul_sound (hE.2.1 q).1
          (RatInterval.point_sound (j : ℚ))) hx
      have hb := RatInterval.mul_sound hSl (hCos _ hArg)
      simpa only [cosineBasis, if_neg hj] using hb
    · have hw := endpoint_product_width S C 2 1 (by norm_num) (by norm_num)
        hSlo hShi hClo hChi
      have hw' : (B.width : ℝ) ≤ (S.width : ℝ)+2*(C.width : ℝ) := by
        simp only [one_mul] at hw
        exact_mod_cast hw
      change (C.width : ℝ) ≤ (A.width : ℝ)+2*precisionError q at hCW
      change (S.width : ℝ) ≤ 2*precisionError q at hSW
      nlinarith

/-- [A finite expression sum terminates and contains the exact sum whenever each
summand does; its width is bounded by the sum of the summand width bounds. [the documented result](goal) Under [the stated assumptions](hyp:f,h). -/
-- @node: endpoint_expressionSum_enclosure
lemma endpoint_expressionSum_enclosure (E : ArithmeticEngine) (q : ℕ)
    (xs : List RatInterval) (f : ℕ → BoxExpr) (v w : ℕ → ℝ) (js : List ℕ)
    (h : ∀ j ∈ js, ∃ B : RatInterval, (f j).eval E q xs = some B ∧
      B.Contains (v j) ∧ (B.width : ℝ) ≤ w j) :
    ∃ B : RatInterval, (expressionSum (js.map f)).eval E q xs = some B ∧
      B.Contains ((js.map v).sum) ∧ (B.width : ℝ) ≤ (js.map w).sum := by
  induction js with
  | nil =>
    refine ⟨RatInterval.point 0, ?_, ?_, ?_⟩
    · rfl
    · simp
    · simp [RatInterval.width, RatInterval.point]
  | cons j js ih =>
    obtain ⟨A, hA, hvA, hwA⟩ := h j (by simp)
    obtain ⟨B, hB, hvB, hwB⟩ := ih (fun l hl => h l (by simp [hl]))
    refine ⟨A.add B, ?_, ?_, ?_⟩
    · change (BoxExpr.add (f j) (expressionSum (js.map f))).eval E q xs = some (A.add B)
      simp [BoxExpr.eval, hA, hB]
    · simpa only [List.map_cons, List.sum_cons] using RatInterval.add_sound hvA hvB
    · rw [RatInterval.width_add]
      push_cast
      simpa only [List.map_cons, List.sum_cons] using add_le_add hwA hwB

/-- [The actual finite cosine-kernel expression terminates, encloses the exact
projection kernel, and has width at most 160 k squared precision errors. [the documented result](goal) Under [the stated assumptions](hyp:hq,l,hXi,hZl,x,hx,hz,hXlo,hXhi,hZlo,hZhi,hXW,hZW). Under [the stated assumptions](hyp:hE). -/
lemma endpoint_kernel_enclosure (E : ArithmeticEngine) (hE : E.Admissible)
    (q : ℕ) (hq : precisionError q ≤ 1 / 4) (k i l : ℕ) (xs : List RatInterval)
    (X Z : RatInterval) (hXi : xs[2 + i]? = some X) (hZl : xs[2 + l]? = some Z)
    (x z : Covariate) (hx : X.Contains (x : ℝ)) (hz : Z.Contains (z : ℝ))
    (hXlo : -precisionError q ≤ (X.lo : ℝ))
    (hXhi : (X.hi : ℝ) ≤ 1 + precisionError q) (hZlo : -precisionError q ≤ (Z.lo : ℝ))
    (hZhi : (Z.hi : ℝ) ≤ 1 + precisionError q)
    (hXW : (X.width : ℝ) ≤ precisionError q) (hZW : (Z.width : ℝ) ≤ precisionError q) :
    ∃ B : RatInterval, (kernelExpression k i l).eval E q xs = some B ∧
      B.Contains (projectionKernel k x z) ∧
      (B.width : ℝ) ≤ 160*(k : ℝ)^2*precisionError q := by
  have herr : 0 ≤ precisionError q := by unfold precisionError; positivity
  have hTerm (j : ℕ) (_ : j ∈ List.range k) :
      ∃ B : RatInterval,
        (BoxExpr.mul (basisExpression j i) (basisExpression j l)).eval E q xs = some B ∧
        B.Contains (cosineBasis j x * cosineBasis j z) ∧
        (B.width : ℝ) ≤ 80*((j : ℝ)+1)*precisionError q := by
    obtain ⟨A, hA, hvA, haL, haH, hwA⟩ :=
      endpoint_basis_enclosure E hE q hq j i xs X hXi x hx hXlo hXhi hXW
    obtain ⟨B, hB, hvB, hbL, hbH, hwB⟩ :=
      endpoint_basis_enclosure E hE q hq j l xs Z hZl z hz hZlo hZhi hZW
    refine ⟨A.mul B, ?_, RatInterval.mul_sound hvA hvB, ?_⟩
    · simp [BoxExpr.eval, hA, hB]
    · have hw := endpoint_product_width A B 2 2 (by norm_num) (by norm_num) haL haH hbL hbH
      have hw' : ((A.mul B).width : ℝ) ≤ 2*(A.width : ℝ)+2*(B.width : ℝ) := by
        exact_mod_cast hw
      linarith
  obtain ⟨B, hB, hvB, hwB⟩ := endpoint_expressionSum_enclosure E q xs
    (fun j => BoxExpr.mul (basisExpression j i) (basisExpression j l))
    (fun j => cosineBasis j x * cosineBasis j z)
    (fun j : ℕ => 80*((j : ℝ)+1)*precisionError q) (List.range k) hTerm
  refine ⟨B, hB, ?_, hwB.trans ?_⟩
  · simpa only [projectionKernel, ← List.sum_toFinset _ (List.nodup_range (n := k)),
      List.toFinset_range] using hvB
  · have hsum : ((List.range k).map (fun j : ℕ => 80*((j : ℝ)+1)*precisionError q)).sum =
        ∑ j ∈ Finset.range k, 80*((j : ℝ)+1)*precisionError q := by
      rw [← List.sum_toFinset _ (List.nodup_range (n := k)), List.toFinset_range]
    rw [hsum]
    calc
      _ ≤ ∑ _j ∈ Finset.range k, 80*(k : ℝ)*precisionError q := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk : (j : ℝ)+1 ≤ k := by exact_mod_cast Finset.mem_range.mp hj
        gcongr
      _ = 80*(k : ℝ)^2*precisionError q := by simp; ring
      _ ≤ 160*(k : ℝ)^2*precisionError q := by nlinarith [sq_nonneg (k : ℝ)]

/-- [The prescribed endpoint precision is small enough for the square-root basis
range bound, for every sample size and every selected pair of ranks. [the documented result](goal) -/
-- @node: endpoint_precision_small
lemma endpoint_precision_small (n kC kS : ℕ) :
    precisionError (qEnd n kC kS) ≤ 1/4 := by
  have hq : 2 ≤ qEnd n kC kS := by unfold qEnd; omega
  have hp : (4 : ℝ) ≤ (2 : ℝ)^(qEnd n kC kS) := by
    calc
      _ = (2 : ℝ)^2 := by norm_num
      _ ≤ (2 : ℝ)^(qEnd n kC kS) := by gcongr; norm_num
  rw [precisionError, zpow_neg, zpow_natCast]
  have h := (inv_le_inv₀ (by positivity : (0 : ℝ) < (2 : ℝ)^qEnd n kC kS) (by norm_num)).mpr hp
  simpa only [one_div] using h

/-- Containment and width bound the overhang of an unchanged input box. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hv,hl,hu,hw) hold, and [the stated conclusion follows](goal). -/
lemma endpoint_raw_box_bounds (I : RatInterval) (v l u w : ℝ)
    (hv : I.Contains v) (hl : l ≤ v) (hu : v ≤ u) (hw : (I.width : ℝ) ≤ w) :
    l-w ≤ (I.lo : ℝ) ∧ (I.hi : ℝ) ≤ u+w := by
  have hwidth : (I.hi : ℝ)-(I.lo : ℝ) ≤ w := by simpa [RatInterval.width] using hw
  constructor <;> linarith [hv.1, hv.2]

/-- [Intersecting a valid covariate name with the public unit interval succeeds,
retains its exact covariate, and does not enlarge the name width. [the documented result](goal) Under [the stated assumptions](hyp:hN). -/
-- @node: endpoint_covariate_box
lemma endpoint_covariate_box (N : NamingPolicy) (hN : N.Admissible)
    (n : ℕ) (α β : ℝ) (o : Fin n → Record) (i : Fin n) (q : ℕ) :
    ∃ X : RatInterval,
      boxIntersection (N.covariateName n α β o i q) (rationalBox 0 1) = some X ∧
      X.Contains (covariate (o i)) ∧ 0 ≤ X.lo ∧ X.hi ≤ 1 ∧
      (X.width : ℝ) ≤ precisionError q := by
  have hName := (hN.2.1 n α β o i).1 q
  have hPublic : (rationalBox 0 1).Contains (covariate (o i)) := by
    norm_num [rationalBox, RatInterval.Contains]
    exact ⟨unitInterval.nonneg _, unitInterval.le_one _⟩
  obtain ⟨X, hX, hContains, hSub⟩ := boxIntersection_exists_contains
    (N.covariateName n α β o i q) (rationalBox 0 1) _ hName.2.2.1 hPublic
  have hSubName : X.Subinterval (N.covariateName n α β o i q) := by
    unfold boxIntersection at hX
    split at hX
    · cases hX
      exact ⟨le_max_left _ _, min_le_left _ _⟩
    · cases hX
  refine ⟨X, hX, hContains, ?_, ?_, ?_⟩
  · simpa [rationalBox] using hSub.1
  · simpa [rationalBox] using hSub.2
  · have hw : (X.width : ℝ) ≤ (N.covariateName n α β o i q).width := by
      exact_mod_cast RatInterval.width_mono hSubName
    exact hw.trans hName.2.2.2

end CausalSmith.Stat.LogoddsLowsmoothFrontier
