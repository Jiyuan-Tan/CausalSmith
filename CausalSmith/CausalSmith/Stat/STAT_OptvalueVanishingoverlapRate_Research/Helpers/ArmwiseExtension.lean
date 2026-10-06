module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Armwise anchored four-cell extension
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open scoped BigOperators

/-- For the displayed parameters, armMassVecFormula is the object specified by this definition. For [the displayed parameters](hyp:u,a), [armMassVecFormula](goal) is the defined object. -/
def armMassVecFormula (u : Fin 4 → ℝ) (a : Bool) : ℝ :=
  u (cellIdx a false) + u (cellIdx a true)

/-- For the displayed parameters, totalMassVecFormula is the object specified by this definition. For [the displayed parameters](hyp:u), [totalMassVecFormula](goal) is the defined object. -/
def totalMassVecFormula (u : Fin 4 → ℝ) : ℝ :=
  armMassVecFormula u false + armMassVecFormula u true

/-- For the displayed parameters, anchoredDenomFormula is the object specified by this definition. For [the displayed parameters](hyp:ε,u,a), [anchoredDenomFormula](goal) is the defined object. -/
def anchoredDenomFormula (ε : ℝ) (u : Fin 4 → ℝ) (a : Bool) : ℝ :=
  max (armMassVecFormula u a) (ε * totalMassVecFormula u)

/-- For the displayed parameters, armDelta is the object specified by this definition. For [the displayed parameters](hyp:u,v,a), [armDelta](goal) is the defined object. -/
def armDelta (u v : Fin 4 → ℝ) (a : Bool) : ℝ :=
  ∑ y : Bool, |u (cellIdx a y) - v (cellIdx a y)|
  -- @realizes \(\Delta_a\)(armwise perturbation) @realizes \(v\)(anchor)

/-- Ambient formula used by the analytic API; its paper domain is pinned below. -/
noncomputable def armwiseExtensionFormula (ε : ℝ) (u : Fin 4 → ℝ) : ℝ :=
  if u = 0 then 0 else
    max (totalMassVecFormula u * u (cellIdx false true) / anchoredDenomFormula ε u false)
        (totalMassVecFormula u * u (cellIdx true true) / anchoredDenomFormula ε u true)

/-- The coordinatewise nonnegative four-vector domain of the armwise construction. -/
def NonnegativeFourVector (u : Fin 4 → ℝ) : Prop :=
  ∀ j, 0 ≤ u j
  -- @realizes \(u\)(domain ℝ_+^4) @realizes \(v\)(domain ℝ_+^4)

-- @env: S3
variable (u v : Fin 4 → ℝ) (ε : ℝ)
variable (hu : NonnegativeFourVector u) (hv : NonnegativeFourVector v)

/-- Arm mass on the nonnegative four-vector domain. -/
def armMassVec (u : Fin 4 → ℝ) (_hu : NonnegativeFourVector u) (a : Bool) : ℝ :=
  u (cellIdx a false) + u (cellIdx a true)
  -- @realizes \(s_a(u)\)(arm mass on ℝ_+^4)

/-- Total mass on the nonnegative four-vector domain. -/
def totalMassVec (u : Fin 4 → ℝ) (hu : NonnegativeFourVector u) : ℝ :=
  armMassVec u hu false + armMassVec u hu true
  -- @realizes \(s(u)\)(total mass on ℝ_+^4)

/-- Anchored denominator on the nonnegative four-vector domain. -/
def anchoredDenom (ε : ℝ) (u : Fin 4 → ℝ) (hu : NonnegativeFourVector u)
    (a : Bool) : ℝ :=
  max (armMassVec u hu a) (ε * totalMassVec u hu)
  -- @realizes \(D_a(u)\)(anchored denominator on ℝ_+^4)

-- @node: def:armwise-extension
/-- For the displayed parameters, armwiseExtension is the object specified by this definition. For [the displayed parameters](hyp:ε,u,hu), [armwiseExtension](goal) is the defined object. -/
noncomputable def armwiseExtension (ε : ℝ) (u : Fin 4 → ℝ)
    (hu : NonnegativeFourVector u) : ℝ :=
  if u = 0 then 0 else
    max (totalMassVec u hu * u (cellIdx false true) / anchoredDenom ε u hu false)
        (totalMassVec u hu * u (cellIdx true true) / anchoredDenom ε u hu true)
  -- @realizes \(F_\epsilon(u)\)(anchored extension on ℝ_+^4; zero branch retained)

/-- Observed atom masses supply the construction's domain without an extra assumption. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma cellVector_nonnegative {d : ℕ} (P : DiscreteLaw d) (x : Fin d) :
    NonnegativeFourVector (cellVector P x) := by
  intro j
  exact ENNReal.toReal_nonneg

-- @node: sqrt_pair_le_sqrt_twice_sum
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hx,hy), the [stated conclusion](goal) holds. -/
lemma sqrt_pair_le_sqrt_twice_sum {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt x + Real.sqrt y ≤ Real.sqrt (2 * (x + y)) := by
  have hsq : (Real.sqrt x + Real.sqrt y) ^ 2 ≤ 2 * (x + y) := by
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y),
      Real.sq_sqrt hx, Real.sq_sqrt hy]
  nlinarith [Real.sq_sqrt (show 0 ≤ 2 * (x + y) by positivity),
    Real.sqrt_nonneg (2 * (x + y)), Real.sqrt_nonneg x, Real.sqrt_nonneg y]

-- @node: weighted_sqrt_pair_bound
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp,hε,hse,hq₀,hq₁,hsum), the [stated conclusion](goal) holds. -/
lemma weighted_sqrt_pair_bound {p s q₀ q₁ ε : ℝ}
    (hp : 0 < p) (hε : 0 < ε) (hse : ε * p ≤ s)
    (hq₀ : 0 ≤ q₀) (hq₁ : 0 ≤ q₁) (hsum : q₀ + q₁ = s) :
    p / s * (Real.sqrt q₀ + Real.sqrt q₁) ≤ Real.sqrt (2 * p / ε) := by
  have hs : 0 < s := lt_of_lt_of_le (mul_pos hε hp) hse
  have hA := sqrt_pair_le_sqrt_twice_sum hq₀ hq₁
  rw [hsum] at hA
  have hA0 : 0 ≤ Real.sqrt q₀ + Real.sqrt q₁ := by positivity
  have hB0 : 0 ≤ Real.sqrt (2 * p / ε) := Real.sqrt_nonneg _
  have hAsq : (Real.sqrt q₀ + Real.sqrt q₁) ^ 2 ≤ 2 * s := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * s by positivity)]
  have hBsq : (Real.sqrt (2 * p / ε)) ^ 2 = 2 * p / ε :=
    Real.sq_sqrt (by positivity)
  have h1 : 0 ≤ p ^ 2 * (2 * s - (Real.sqrt q₀ + Real.sqrt q₁) ^ 2) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hAsq)
  calc
    p / s * (Real.sqrt q₀ + Real.sqrt q₁) =
        (p * (Real.sqrt q₀ + Real.sqrt q₁)) / s := by ring
    _ ≤ Real.sqrt (2 * p / ε) := by
      apply (div_le_iff₀ hs).2
      have htarget : (p * (Real.sqrt q₀ + Real.sqrt q₁)) ^ 2 ≤
          (Real.sqrt (2 * p / ε) * s) ^ 2 := by
        calc
          _ ≤ 2 * p ^ 2 * s := by nlinarith [h1]
          _ ≤ (2 * p / ε) * s ^ 2 := by
            calc
              _ = (2 * p * s / ε) * (ε * p) := by field_simp
              _ ≤ (2 * p * s / ε) * s :=
                mul_le_mul_of_nonneg_left hse (by positivity)
              _ = _ := by ring
          _ = _ := by rw [mul_pow, hBsq]
      nlinarith [mul_nonneg (le_of_lt hp) hA0, mul_nonneg hB0 (le_of_lt hs)]

-- @node: observed_armwise_sqrt_bound
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp), the [stated conclusion](goal) holds. -/
lemma observed_armwise_sqrt_bound (d : ℕ) (ε : ℝ) (P : DiscreteLaw d)
    (hε : 0 < ε) (hP : ObservedClass ε P) (x : Fin d)
    (hp : 0 < cellMass P x) :
    (∑ a : Bool, cellMass P x / armMass P a x *
      (∑ y : Bool, Real.sqrt (jointMass P x a y))) ≤
      2 * Real.sqrt 2 * Real.sqrt (cellMass P x / ε) := by
  have hq (a y : Bool) : 0 ≤ jointMass P x a y := ENNReal.toReal_nonneg
  have hcell : cellMass P x = armMass P false x + armMass P true x := by
    simp [cellMass, armMass]
    ring
  have htrue : cellMass P x * propensity P x = armMass P true x := by
    rw [propensity]
    field_simp [ne_of_gt hp]
  have hfalse : cellMass P x * (1 - propensity P x) = armMass P false x := by
    rw [mul_sub, mul_one, htrue, hcell]
    ring
  obtain ⟨hlo, hhi⟩ := hP.overlap x hp
  have hfalsefloor : ε * cellMass P x ≤ armMass P false x := by
    have h : ε ≤ 1 - propensity P x := by linarith
    calc
      ε * cellMass P x = cellMass P x * ε := by ring
      _ ≤ cellMass P x * (1 - propensity P x) :=
        mul_le_mul_of_nonneg_left h (le_of_lt hp)
      _ = armMass P false x := hfalse
  have htruefloor : ε * cellMass P x ≤ armMass P true x := by
    rw [← htrue]
    nlinarith [mul_nonneg (le_of_lt hp) (sub_nonneg.mpr hlo)]
  have hb (a : Bool) :
      cellMass P x / armMass P a x *
        (∑ y : Bool, Real.sqrt (jointMass P x a y)) ≤
          Real.sqrt (2 * cellMass P x / ε) := by
    cases a with
    | false =>
        simpa [armMass, Fintype.sum_bool, add_comm] using
          (weighted_sqrt_pair_bound hp hε hfalsefloor
            (hq false false) (hq false true)
            (by simp [armMass, add_comm]))
    | true =>
        simpa [armMass, Fintype.sum_bool, add_comm] using
          (weighted_sqrt_pair_bound hp hε htruefloor
            (hq true false) (hq true true)
            (by simp [armMass, add_comm]))
  have hsum : (∑ a : Bool, cellMass P x / armMass P a x *
      (∑ y : Bool, Real.sqrt (jointMass P x a y))) ≤
        2 * Real.sqrt (2 * cellMass P x / ε) := by
    simpa [Fintype.sum_bool, two_mul] using add_le_add (hb true) (hb false)
  calc
    _ ≤ 2 * Real.sqrt (2 * cellMass P x / ε) := hsum
    _ = 2 * Real.sqrt 2 * Real.sqrt (cellMass P x / ε) := by
      rw [show 2 * cellMass P x / ε = 2 * (cellMass P x / ε) by ring,
        Real.sqrt_mul (by norm_num)]
      ring

-- @node: armwise_ratio_bound
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hr,ht,hz,hzr,_hc,_hct), the [stated conclusion](goal) holds. -/
lemma armwise_ratio_bound {r t z c : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hz : 0 ≤ z) (hzr : z ≤ r) (_hc : 0 ≤ c) (_hct : c ≤ t) :
    |z / r - c / t| ≤ (|z - c| + |r - t|) / t := by
  have hrt : 0 < r * t := mul_pos hr ht
  have hmain : |t * z - r * c| ≤ r * (|z - c| + |r - t|) := by
    apply abs_le.mpr
    rcases le_total r t with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      constructor <;> nlinarith [le_abs_self (z - c), neg_le_abs (z - c),
        mul_nonneg (sub_nonneg.mpr h) hz,
        mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hzr)]
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      constructor <;> nlinarith [le_abs_self (z - c), neg_le_abs (z - c),
        mul_nonneg (sub_nonneg.mpr h) _hc,
        mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr _hct)]
  have halg : z / r - c / t = (t * z - r * c) / (r * t) := by
    field_simp
  rw [halg, abs_div, abs_of_pos hrt]
  apply (div_le_div_iff₀ hrt ht).2
  nlinarith [hmain]

-- @node: armwise_coordinate_ratio_bound
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hru,hrv,hzu,hzru,hzv,hzrv,hsv,hδ,hδa), the [stated conclusion](goal) holds. -/
lemma armwise_coordinate_ratio_bound {su sv zu zv ru rv δ δa : ℝ}
    (hru : 0 < ru) (hrv : 0 < rv) (hzu : 0 ≤ zu) (hzru : zu ≤ ru)
    (hzv : 0 ≤ zv) (hzrv : zv ≤ rv) (hsv : 0 ≤ sv)
    (hδ : |su - sv| ≤ δ) (hδa : |zu - zv| ≤ δa) :
    |su * zu / ru - sv * zv / rv| ≤
      δ + sv / rv * (δa + |ru - rv|) := by
  have hquot : 0 ≤ zu / ru := div_nonneg hzu (le_of_lt hru)
  have hquot1 : zu / ru ≤ 1 := (div_le_one hru).2 hzru
  have hr := armwise_ratio_bound hru hrv hzu hzru hzv hzrv
  have hid : su * zu / ru - sv * zv / rv =
      (su - sv) * (zu / ru) + sv * (zu / ru - zv / rv) := by ring
  rw [hid]
  calc
    _ ≤ |su - sv| * (zu / ru) + sv * |zu / ru - zv / rv| := by
      simpa [abs_mul, abs_of_nonneg hquot, abs_of_nonneg hsv] using
        (abs_add_le ((su - sv) * (zu / ru)) (sv * (zu / ru - zv / rv)))
    _ ≤ δ + sv / rv * (δa + |ru - rv|) := by
      have h1 : |su - sv| * (zu / ru) ≤ δ := by
        calc
          _ ≤ δ * (zu / ru) := mul_le_mul_of_nonneg_right hδ hquot
          _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hquot1
            (le_trans (abs_nonneg _) hδ)
          _ = δ := mul_one _
      have h2 : sv * |zu / ru - zv / rv| ≤
          sv / rv * (|zu - zv| + |ru - rv|) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left hr hsv)
      have h3 := mul_le_mul_of_nonneg_left hδa (show 0 ≤ sv / rv by positivity)
      nlinarith

/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hw,hne), the [stated conclusion](goal) holds. -/
lemma totalMassVec_pos_of_nonzero {w : Fin 4 → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hne : w ≠ 0) : 0 < totalMassVecFormula w := by
  have h0 := hw (cellIdx false false)
  have h1 := hw (cellIdx false true)
  have h2 := hw (cellIdx true false)
  have h3 := hw (cellIdx true true)
  have hsum : 0 ≤ totalMassVecFormula w := by
    dsimp [totalMassVecFormula, armMassVecFormula]
    positivity
  rcases eq_or_lt_of_le hsum with hz | hz
  · exfalso
    apply hne
    funext j
    fin_cases j <;> simp [totalMassVecFormula, armMassVecFormula, cellIdx] at hz h0 h1 h2 h3 ⊢ <;>
      linarith
  · exact hz

/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hw), the [stated conclusion](goal) holds. -/
lemma armwiseExtension_nonneg_le_totalMassVec {ε : ℝ} (hε : 0 < ε)
    {w : Fin 4 → ℝ} (hw : ∀ j, 0 ≤ w j) :
    0 ≤ armwiseExtensionFormula ε w ∧ armwiseExtensionFormula ε w ≤ totalMassVecFormula w := by
  by_cases hzero : w = 0
  · subst w
    simp [armwiseExtensionFormula, totalMassVecFormula, armMassVecFormula]
  · have hs := totalMassVec_pos_of_nonzero hw hzero
    have ha (a : Bool) :
        0 ≤ totalMassVecFormula w * w (cellIdx a true) / anchoredDenomFormula ε w a ∧
        totalMassVecFormula w * w (cellIdx a true) / anchoredDenomFormula ε w a ≤
          totalMassVecFormula w := by
      have hd : 0 < anchoredDenomFormula ε w a := by
        unfold anchoredDenomFormula
        exact lt_of_lt_of_le (mul_pos hε hs) (le_max_right _ _)
      have hwa := hw (cellIdx a false)
      have hwb := hw (cellIdx a true)
      have hle : w (cellIdx a true) ≤ anchoredDenomFormula ε w a := by
        unfold anchoredDenomFormula armMassVecFormula
        exact le_trans (by linarith) (le_max_left _ _)
      constructor
      · positivity
      · apply (div_le_iff₀ hd).2
        exact mul_le_mul_of_nonneg_left hle (le_of_lt hs)
    simp only [armwiseExtensionFormula, if_neg hzero]
    exact ⟨le_max_of_le_left (ha false).1,
      max_le (ha false).2 (ha true).2⟩

/-- Analytic extension of the modulus; the paper realization below restricts its domain. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma armwise_modulus_extension :
    (∀ ε : ℝ, 0 < ε → ∀ u v : Fin 4 → ℝ,
      (∀ j, 0 ≤ u j) → (∀ j, 0 ≤ v j) → v ≠ 0 →
      |armwiseExtensionFormula ε u - armwiseExtensionFormula ε v| ≤
        2 * (∑ a : Bool, armDelta u v a) +
        2 * (∑ a : Bool, totalMassVecFormula v / anchoredDenomFormula ε v a * armDelta u v a)) ∧
    (∀ (d : ℕ) (ε : ℝ) (P : DiscreteLaw d),
      0 < ε → ObservedClass ε P → ∀ x : Fin d, 0 < cellMass P x →
        (∑ a : Bool, cellMass P x / armMass P a x *
          (∑ y : Bool, Real.sqrt (jointMass P x a y))) ≤
          2 * Real.sqrt 2 * Real.sqrt (cellMass P x / ε)) := by
  constructor
  · intro ε hε u v hu hv hv0
    let δ : ℝ := ∑ a : Bool, armDelta u v a
    have hδa (a : Bool) : 0 ≤ armDelta u v a := by
      simp only [armDelta, Fintype.sum_bool]
      positivity
    have hδ : 0 ≤ δ := Finset.sum_nonneg (fun a _ => hδa a)
    have hMass (a : Bool) :
        |armMassVecFormula u a - armMassVecFormula v a| ≤ armDelta u v a := by
      simpa [armMassVecFormula, armDelta, Fintype.sum_bool, sub_add_sub_comm, add_comm] using
        (abs_add_le (u (cellIdx a false) - v (cellIdx a false))
          (u (cellIdx a true) - v (cellIdx a true)))
    have hTotal : |totalMassVecFormula u - totalMassVecFormula v| ≤ δ := by
      have h := abs_add_le
        (armMassVecFormula u false - armMassVecFormula v false)
        (armMassVecFormula u true - armMassVecFormula v true)
      have hf := hMass false
      have ht := hMass true
      simpa [totalMassVecFormula, δ, Fintype.sum_bool, sub_add_sub_comm, add_comm] using
        (le_trans h (add_le_add hf ht))
    have hsv : 0 < totalMassVecFormula v := totalMassVec_pos_of_nonzero hv hv0
    have hdv (a : Bool) : 0 < anchoredDenomFormula ε v a := by
      unfold anchoredDenomFormula
      exact lt_of_lt_of_le (mul_pos hε hsv) (le_max_right _ _)
    have hw (a : Bool) : 0 ≤ totalMassVecFormula v / anchoredDenomFormula ε v a := by
      exact div_nonneg (le_of_lt hsv) (le_of_lt (hdv a))
    have hdenom (a : Bool) :
        |anchoredDenomFormula ε u a - anchoredDenomFormula ε v a| ≤
          armDelta u v a + ε * δ := by
      have hmax := abs_max_sub_max_le_max
        (armMassVecFormula u a) (ε * totalMassVecFormula u)
        (armMassVecFormula v a) (ε * totalMassVecFormula v)
      have hscaled : |ε * totalMassVecFormula u - ε * totalMassVecFormula v| ≤ ε * δ := by
        rw [← mul_sub, abs_mul, abs_of_pos hε]
        exact mul_le_mul_of_nonneg_left hTotal (le_of_lt hε)
      have hmaxbound :
          max |armMassVecFormula u a - armMassVecFormula v a|
            |ε * totalMassVecFormula u - ε * totalMassVecFormula v| ≤
            armDelta u v a + ε * δ := by
        apply max_le
        · linarith [hMass a, mul_nonneg (le_of_lt hε) hδ]
        · linarith [hδa a]
      exact le_trans (by simpa [anchoredDenomFormula] using hmax) hmaxbound
    by_cases hu0 : u = 0
    · have hFv := armwiseExtension_nonneg_le_totalMassVec hε hv
      have htot : totalMassVecFormula v ≤ δ := by
        have h := hTotal
        have hzero : totalMassVecFormula (0 : Fin 4 → ℝ) = 0 := by
          simp [totalMassVecFormula, armMassVecFormula]
        rw [hu0, hzero, zero_sub, abs_neg, abs_of_nonneg (le_of_lt hsv)] at h
        exact h
      have hweighted : 0 ≤ ∑ a : Bool,
          totalMassVecFormula v / anchoredDenomFormula ε v a * armDelta u v a :=
        Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) (hδa a))
      rw [show armwiseExtensionFormula ε u = 0 by simp [armwiseExtensionFormula, hu0],
        zero_sub, abs_neg, abs_of_nonneg hFv.1]
      change armwiseExtensionFormula ε v ≤
        2 * δ + 2 * (∑ a : Bool,
          totalMassVecFormula v / anchoredDenomFormula ε v a * armDelta u v a)
      linarith
    · have hsu := totalMassVec_pos_of_nonzero hu hu0
      have hdu (a : Bool) : 0 < anchoredDenomFormula ε u a := by
        unfold anchoredDenomFormula
        exact lt_of_lt_of_le (mul_pos hε hsu) (le_max_right _ _)
      have harm (a : Bool) :
          |totalMassVecFormula u * u (cellIdx a true) / anchoredDenomFormula ε u a -
            totalMassVecFormula v * v (cellIdx a true) / anchoredDenomFormula ε v a| ≤
          2 * δ + 2 * (totalMassVecFormula v / anchoredDenomFormula ε v a) * armDelta u v a := by
        have hzu := hu (cellIdx a true)
        have hzv := hv (cellIdx a true)
        have hzu_le : u (cellIdx a true) ≤ anchoredDenomFormula ε u a := by
          exact le_trans (by dsimp [armMassVecFormula]; linarith [hu (cellIdx a false)])
            (le_max_left _ _)
        have hzv_le : v (cellIdx a true) ≤ anchoredDenomFormula ε v a := by
          exact le_trans (by dsimp [armMassVecFormula]; linarith [hv (cellIdx a false)])
            (le_max_left _ _)
        have hcoord : |u (cellIdx a true) - v (cellIdx a true)| ≤ armDelta u v a := by
          simp only [armDelta, Fintype.sum_bool]
          exact le_add_of_nonneg_right (abs_nonneg _)
        have hbase := armwise_coordinate_ratio_bound (hdu a) (hdv a)
          hzu hzu_le hzv hzv_le (le_of_lt hsv) hTotal hcoord
        have he : (totalMassVecFormula v / anchoredDenomFormula ε v a) * ε ≤ 1 := by
          have he' : ε * totalMassVecFormula v ≤ anchoredDenomFormula ε v a :=
            le_max_right _ _
          calc
            _ = (ε * totalMassVecFormula v) / anchoredDenomFormula ε v a := by ring
            _ ≤ 1 := (div_le_one (hdv a)).2 he'
        have hmul := mul_le_mul_of_nonneg_left (hdenom a) (hw a)
        nlinarith [mul_nonneg (sub_nonneg.mpr he) hδ,
          mul_nonneg (hw a) (hδa a)]
      have hmax := abs_max_sub_max_le_max
        (totalMassVecFormula u * u (cellIdx false true) / anchoredDenomFormula ε u false)
        (totalMassVecFormula u * u (cellIdx true true) / anchoredDenomFormula ε u true)
        (totalMassVecFormula v * v (cellIdx false true) / anchoredDenomFormula ε v false)
        (totalMassVecFormula v * v (cellIdx true true) / anchoredDenomFormula ε v true)
      have hsum :
          max (2 * δ + 2 * (totalMassVecFormula v / anchoredDenomFormula ε v false) *
              armDelta u v false)
            (2 * δ + 2 * (totalMassVecFormula v / anchoredDenomFormula ε v true) *
              armDelta u v true) ≤
          2 * δ + 2 * (∑ a : Bool,
            totalMassVecFormula v / anchoredDenomFormula ε v a * armDelta u v a) := by
        simp only [Fintype.sum_bool]
        apply max_le <;> nlinarith [mul_nonneg (hw false) (hδa false),
          mul_nonneg (hw true) (hδa true)]
      simpa [armwiseExtensionFormula, hu0, hv0, δ] using
        (le_trans hmax (le_trans (max_le_max (harm false) (harm true)) hsum))
  · intro d ε P hε hP x hp
    exact observed_armwise_sqrt_bound d ε P hε hP x hp
  -- @realizes \(C_\star\)(explicit universal modulus constant)

-- @node: lem:armwise-modulus
/-- In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma armwise_modulus :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ u v : Fin 4 → ℝ,
      (hu : NonnegativeFourVector u) → (hv : NonnegativeFourVector v) → v ≠ 0 →
      |armwiseExtension ε u hu - armwiseExtension ε v hv| ≤
        2 * (∑ a : Bool, armDelta u v a) +
        2 * (∑ a : Bool, totalMassVec v hv / anchoredDenom ε v hv a * armDelta u v a)) ∧
    (∀ (d : ℕ) (ε : ℝ) (P : DiscreteLaw d),
      2 ≤ d → 0 < ε → ε ≤ 1 / 2 → ObservedClass ε P →
      ∀ x : Fin d, 0 < cellMass P x →
        (∑ a : Bool, cellMass P x / armMass P a x *
          (∑ y : Bool, Real.sqrt (jointMass P x a y))) ≤
          2 * Real.sqrt 2 * Real.sqrt (cellMass P x / ε)) := by
  exact ⟨fun ε hε _ => armwise_modulus_extension.1 ε hε,
    fun d ε P _ hε _ => armwise_modulus_extension.2 d ε P hε⟩

end CausalSmith.Stat.OptvalueVanishingoverlapRate
