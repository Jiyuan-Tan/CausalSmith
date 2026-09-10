import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Certified finite mesh extrema

This module provides rational rectangles for complex values and finite uniform
mesh enclosures for the infimum and supremum of a real function.  A supplied
Lipschitz bound turns rational node enclosures into global enclosures with an
explicit mesh-error allowance.
-/

open scoped BigOperators Interval
open MeasureTheory Set intervalIntegral

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- A rational rectangle in the complex plane consists of [a rational interval enclosing the real
coordinate](hyp:re) and [a rational interval enclosing the imaginary coordinate](hyp:im). -/
@[ext]
structure ComplexRatInterval where
  /-- The rational interval enclosing the real coordinate. -/
  re : RatInterval
  /-- The rational interval enclosing the imaginary coordinate. -/
  im : RatInterval

namespace ComplexRatInterval

/-- Given [a rational rectangle](hyp:I) and [a complex number](hyp:z), [rectangle membership](goal) means that both the real and imaginary coordinates of the number lie in their respective rational intervals. -/
def Contains (I : ComplexRatInterval) (z : ℂ) : Prop :=
  I.re.Contains z.re ∧ I.im.Contains z.im

/-- Given [two rational rectangles in the complex plane](hyp:I,J), [the refinement relation](goal) holds exactly when each coordinate interval of the first is contained in the corresponding coordinate interval of the second. -/
def Subinterval (I J : ComplexRatInterval) : Prop :=
  I.re.Subinterval J.re ∧ I.im.Subinterval J.im

/-- For [two rational rectangles in the complex plane](hyp:I,J), [their sum rectangle](goal) is obtained by adding their real-coordinate intervals and their imaginary-coordinate intervals separately. -/
def add (I J : ComplexRatInterval) : ComplexRatInterval :=
  ⟨I.re.add J.re, I.im.add J.im⟩

/-- For [a rational scalar](hyp:q) and [a rational rectangle in the complex plane](hyp:I), [the scalar-multiple rectangle](goal) is obtained by multiplying each coordinate interval by that scalar. -/
def smulRat (q : ℚ) (I : ComplexRatInterval) : ComplexRatInterval :=
  ⟨(RatInterval.point q).mul I.re, (RatInterval.point q).mul I.im⟩

/-- For [a rational rectangle in the complex plane](hyp:I), [a rational error allowance](hyp:e), and [the condition that this allowance is nonnegative](hyp:he), [the expanded rectangle](goal) widens each coordinate interval by that allowance. -/
def expand (I : ComplexRatInterval) (e : ℚ) (he : 0 ≤ e) : ComplexRatInterval :=
  ⟨I.re.expand e he, I.im.expand e he⟩

/-- [The zero rectangle](goal) is the rational rectangle whose real and imaginary coordinate intervals are both the singleton interval containing zero. -/
def zero : ComplexRatInterval := ⟨RatInterval.point 0, RatInterval.point 0⟩

/-- Complex rectangle addition encloses sums of enclosed complex numbers. -/
theorem add_sound {I J : ComplexRatInterval} {z w : ℂ}
    (hz : I.Contains z) (hw : J.Contains w) : (I.add J).Contains (z + w) := by
  exact ⟨RatInterval.add_sound hz.1 hw.1, RatInterval.add_sound hz.2 hw.2⟩

/-- Rational scalar multiplication encloses the corresponding complex scalar multiple. -/
theorem smulRat_sound {I : ComplexRatInterval} {z : ℂ} (q : ℚ)
    (hz : I.Contains z) : (smulRat q I).Contains ((q : ℂ) * z) := by
  constructor
  · simpa [smulRat] using RatInterval.mul_sound (RatInterval.point_sound q) hz.1
  · simpa [smulRat] using RatInterval.mul_sound (RatInterval.point_sound q) hz.2

/-- Coordinatewise widening preserves containment. -/
theorem expand_contains {I : ComplexRatInterval} {z : ℂ} {e : ℚ}
    (he : 0 ≤ e) (hz : I.Contains z) : (I.expand e he).Contains z := by
  have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
  constructor <;> constructor <;>
    simp only [expand, RatInterval.expand, RatInterval.Contains, Rat.cast_sub,
      Rat.cast_add] <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]

end ComplexRatInterval

namespace CircleMesh

/-- For [a mesh size](hyp:n) and [a node index](hyp:k), [the mesh point](goal) is the real number $k/n$. -/
noncomputable def meshPoint (n k : ℕ) : ℝ := (k : ℝ) / n

/-- For [a complex center](hyp:c), [a real radius](hyp:r), and [a real parameter](hyp:u), [the circle point](goal) is $c+r\exp(2\pi u i)$. -/
noncomputable def circleMap (c : ℂ) (r : ℝ) (u : ℝ) : ℂ :=
  c + r * Complex.exp ((2 * Real.pi * u) * Complex.I)

/-- For [a real radius](hyp:r) and [a real parameter](hyp:u), [the circle tangent](goal) is $2\pi i r\exp(2\pi u i)$. -/
noncomputable def circleTangent (r : ℝ) (u : ℝ) : ℂ :=
  ((2 * Real.pi) * Complex.I) * r * Complex.exp ((2 * Real.pi * u) * Complex.I)

/-- For [a complex-valued function](hyp:f), [a complex center](hyp:c), [a real radius](hyp:r), and [a real parameter](hyp:u), [the parameterized contour integrand](goal) is the value of the function at the corresponding circle point multiplied by the circle tangent there. -/
noncomputable def circleIntegrand (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (u : ℝ) : ℂ :=
  f (circleMap c r u) * circleTangent r u

/-- For [a complex-valued function](hyp:f), [a complex center](hyp:c), and [a real radius](hyp:r), [the circle contour integral](goal) is the integral from $0$ to $1$ of the parameterized contour integrand. -/
noncomputable def circleContourIntegral (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..1, circleIntegrand f c r u

/-- Given [a sequence of rational intervals](hyp:nodes), [the minimum lower endpoint up to a terminal node index](goal) is computed recursively: [at index zero it is the lower endpoint of the initial interval](step:1), and [at each successor index it is the smaller of the preceding result and the new lower endpoint](step:2).

The value is computed by primitive recursion. -/
def minLoUpTo (nodes : ℕ → RatInterval) : ℕ → ℚ
  | 0 => (nodes 0).lo
  | n + 1 => min (minLoUpTo nodes n) (nodes (n + 1)).lo

/-- Given [a sequence of rational intervals](hyp:nodes), [the minimum upper endpoint up to a terminal node index](goal) is computed recursively: [at index zero it is the upper endpoint of the initial interval](step:1), and [at each successor index it is the smaller of the preceding result and the new upper endpoint](step:2).

The value is computed by primitive recursion. -/
def minHiUpTo (nodes : ℕ → RatInterval) : ℕ → ℚ
  | 0 => (nodes 0).hi
  | n + 1 => min (minHiUpTo nodes n) (nodes (n + 1)).hi

/-- Given [a sequence of rational intervals](hyp:nodes), [the maximum lower endpoint up to a terminal node index](goal) is computed recursively: [at index zero it is the lower endpoint of the initial interval](step:1), and [at each successor index it is the larger of the preceding result and the new lower endpoint](step:2).

The value is computed by primitive recursion. -/
def maxLoUpTo (nodes : ℕ → RatInterval) : ℕ → ℚ
  | 0 => (nodes 0).lo
  | n + 1 => max (maxLoUpTo nodes n) (nodes (n + 1)).lo

/-- Given [a sequence of rational intervals](hyp:nodes), [the maximum upper endpoint up to a terminal node index](goal) is computed recursively: [at index zero it is the upper endpoint of the initial interval](step:1), and [at each successor index it is the larger of the preceding result and the new upper endpoint](step:2).

The value is computed by primitive recursion. -/
def maxHiUpTo (nodes : ℕ → RatInterval) : ℕ → ℚ
  | 0 => (nodes 0).hi
  | n + 1 => max (maxHiUpTo nodes n) (nodes (n + 1)).hi

private theorem minEndpoints_le (nodes : ℕ → RatInterval) (n : ℕ) :
    minLoUpTo nodes n ≤ minHiUpTo nodes n := by
  induction n with
  | zero => exact (nodes 0).lo_le_hi
  | succ n ih =>
      simp only [minLoUpTo, minHiUpTo]
      exact min_le_min ih (nodes (n + 1)).lo_le_hi

private theorem maxEndpoints_le (nodes : ℕ → RatInterval) (n : ℕ) :
    maxLoUpTo nodes n ≤ maxHiUpTo nodes n := by
  induction n with
  | zero => exact (nodes 0).lo_le_hi
  | succ n ih =>
      simp only [maxLoUpTo, maxHiUpTo]
      exact max_le (ih.trans (le_max_left _ _))
        ((nodes (n + 1)).lo_le_hi.trans (le_max_right _ _))

private theorem minLoUpTo_le (nodes : ℕ → RatInterval) {k n : ℕ} (hk : k ≤ n) :
    minLoUpTo nodes n ≤ (nodes k).lo := by
  induction n with
  | zero => simp_all [minLoUpTo]
  | succ n ih =>
      simp only [minLoUpTo]
      rcases Nat.eq_or_lt_of_le hk with rfl | hk'
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (ih (Nat.le_of_lt_succ hk'))

private theorem minHiUpTo_le (nodes : ℕ → RatInterval) {k n : ℕ} (hk : k ≤ n) :
    minHiUpTo nodes n ≤ (nodes k).hi := by
  induction n with
  | zero => simp_all [minHiUpTo]
  | succ n ih =>
      simp only [minHiUpTo]
      rcases Nat.eq_or_lt_of_le hk with rfl | hk'
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (ih (Nat.le_of_lt_succ hk'))

private theorem lo_le_maxLoUpTo (nodes : ℕ → RatInterval) {k n : ℕ} (hk : k ≤ n) :
    (nodes k).lo ≤ maxLoUpTo nodes n := by
  induction n with
  | zero => simp_all [maxLoUpTo]
  | succ n ih =>
      simp only [maxLoUpTo]
      rcases Nat.eq_or_lt_of_le hk with rfl | hk'
      · exact le_max_right _ _
      · exact (ih (Nat.le_of_lt_succ hk')).trans (le_max_left _ _)

private theorem hi_le_maxHiUpTo (nodes : ℕ → RatInterval) {k n : ℕ} (hk : k ≤ n) :
    (nodes k).hi ≤ maxHiUpTo nodes n := by
  induction n with
  | zero => simp_all [maxHiUpTo]
  | succ n ih =>
      simp only [maxHiUpTo]
      rcases Nat.eq_or_lt_of_le hk with rfl | hk'
      · exact le_max_right _ _
      · exact (ih (Nat.le_of_lt_succ hk')).trans (le_max_left _ _)

private theorem exists_minLoUpTo (nodes : ℕ → RatInterval) (n : ℕ) :
    ∃ k ≤ n, minLoUpTo nodes n = (nodes k).lo := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
      simp only [minLoUpTo]
      by_cases h : minLoUpTo nodes n ≤ (nodes (n + 1)).lo
      · obtain ⟨k, hk, heq⟩ := ih
        exact ⟨k, hk.trans n.le_succ, by rw [min_eq_left h, heq]⟩
      · exact ⟨n + 1, le_rfl, min_eq_right (le_of_not_ge h)⟩

private theorem exists_minHiUpTo (nodes : ℕ → RatInterval) (n : ℕ) :
    ∃ k ≤ n, minHiUpTo nodes n = (nodes k).hi := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
      simp only [minHiUpTo]
      by_cases h : minHiUpTo nodes n ≤ (nodes (n + 1)).hi
      · obtain ⟨k, hk, heq⟩ := ih
        exact ⟨k, hk.trans n.le_succ, by rw [min_eq_left h, heq]⟩
      · exact ⟨n + 1, le_rfl, min_eq_right (le_of_not_ge h)⟩

private theorem exists_maxLoUpTo (nodes : ℕ → RatInterval) (n : ℕ) :
    ∃ k ≤ n, maxLoUpTo nodes n = (nodes k).lo := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
      simp only [maxLoUpTo]
      by_cases h : (nodes (n + 1)).lo ≤ maxLoUpTo nodes n
      · obtain ⟨k, hk, heq⟩ := ih
        exact ⟨k, hk.trans n.le_succ, by rw [max_eq_left h, heq]⟩
      · exact ⟨n + 1, le_rfl, max_eq_right (le_of_not_ge h)⟩

private theorem exists_maxHiUpTo (nodes : ℕ → RatInterval) (n : ℕ) :
    ∃ k ≤ n, maxHiUpTo nodes n = (nodes k).hi := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
      simp only [maxHiUpTo]
      by_cases h : (nodes (n + 1)).hi ≤ maxHiUpTo nodes n
      · obtain ⟨k, hk, heq⟩ := ih
        exact ⟨k, hk.trans n.le_succ, by rw [max_eq_left h, heq]⟩
      · exact ⟨n + 1, le_rfl, max_eq_right (le_of_not_ge h)⟩

/-- A node of a nonempty uniform mesh lies in the unit parameter interval. -/
theorem meshPoint_mem {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    meshPoint n k ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [meshPoint, div_le_one (by exact_mod_cast hn)]
    exact_mod_cast hk

private theorem exists_near_meshPoint {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ k ≤ n, |x - meshPoint n k| ≤ 1 / (n : ℝ) := by
  let k := ⌊(n : ℝ) * x⌋₊
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg hn'.le hx.1
  have hkx : (k : ℝ) ≤ (n : ℝ) * x := Nat.floor_le hnx
  have hxk : (n : ℝ) * x < k + 1 := Nat.lt_floor_add_one _
  have hk : k ≤ n := by
    have hk' : (k : ℝ) ≤ n := by nlinarith [hx.2]
    exact_mod_cast hk'
  refine ⟨k, hk, ?_⟩
  have heq : x - (k : ℝ) / n = ((n : ℝ) * x - k) / n := by
    field_simp
  rw [meshPoint, heq, abs_of_nonneg (div_nonneg (by linarith) hn'.le)]
  exact div_le_div_of_nonneg_right (by linarith) hn'.le

/-- A function satisfying a finite Lipschitz bound on the unit interval is continuous there. -/
theorem continuousOn_of_lipschitz_bound {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖g s - g t‖ ≤ C * |s - t|) : ContinuousOn g (Icc (0 : ℝ) 1) := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / (C + 1), div_pos hε (by linarith), ?_⟩
  intro y hy hyx
  change ‖y - x‖ < ε / (C + 1) at hyx
  rw [dist_eq_norm]
  rw [Real.norm_eq_abs] at hyx
  by_cases hC0 : C = 0
  · have hzle : ‖g y - g x‖ ≤ 0 := by simpa [hC0] using h y hy x hx
    exact (le_antisymm hzle (norm_nonneg _)).trans_lt hε
  calc
    ‖g y - g x‖ ≤ C * |y - x| := h y hy x hx
    _ < C * (ε / (C + 1)) := by
      exact mul_lt_mul_of_pos_left hyx (lt_of_le_of_ne hC (Ne.symm hC0))
    _ < ε := by
      rw [mul_div_assoc']
      exact (div_lt_iff₀ (by linarith : 0 < C + 1)).2 (by nlinarith)

/-- Given [a sequence of rational node intervals](hyp:nodes), [a rational Lipschitz constant](hyp:L), [the condition that the constant is nonnegative](hyp:hL), [a mesh size](hyp:n), and [the condition that the mesh size is positive](hyp:hn), [the infimum enclosure](goal) has lower endpoint equal to the minimum node lower endpoint minus $L/n$ and upper endpoint equal to the minimum node upper endpoint. -/
def infEnclosure (nodes : ℕ → RatInterval) (L : ℚ) (hL : 0 ≤ L)
    (n : ℕ) (hn : 0 < n) : RatInterval :=
  ⟨minLoUpTo nodes n - L / n, minHiUpTo nodes n, by
    have hdiv : 0 ≤ L / (n : ℚ) := div_nonneg hL (by positivity)
    linarith [minEndpoints_le nodes n]⟩

/-- Given [a sequence of rational node intervals](hyp:nodes), [a rational Lipschitz constant](hyp:L), [the condition that the constant is nonnegative](hyp:hL), [a mesh size](hyp:n), and [the condition that the mesh size is positive](hyp:hn), [the supremum enclosure](goal) has lower endpoint equal to the maximum node lower endpoint and upper endpoint equal to the maximum node upper endpoint plus $L/n$. -/
def supEnclosure (nodes : ℕ → RatInterval) (L : ℚ) (hL : 0 ≤ L)
    (n : ℕ) (hn : 0 < n) : RatInterval :=
  ⟨maxLoUpTo nodes n, maxHiUpTo nodes n + L / n, by
    have hdiv : 0 ≤ L / (n : ℚ) := div_nonneg hL (by positivity)
    linarith [maxEndpoints_le nodes n]⟩

/-- **Certified infimum enclosure on the unit mesh.** Fix [a nonnegative Lipschitz
constant](hyp:hL) and [a positive number of mesh nodes](hyp:hn), and suppose [the real function
is Lipschitz on `[0, 1]` with that constant](hyp:hLip) and [each rational node interval contains
the function's value at the corresponding mesh point](hyp:hnodes). Then [the infimum enclosure
built from those node intervals contains the true infimum of the function over
`[0, 1]`](goal). -/
theorem infEnclosure_sound {f : ℝ → ℝ} {nodes : ℕ → RatInterval}
    {L : ℚ} (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n)
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |f s - f t| ≤ (L : ℝ) * |s - t|)
    (hnodes : ∀ k ≤ n, (nodes k).Contains (f (meshPoint n k))) :
    (infEnclosure nodes L hL n hn).Contains (sInf (f '' Icc (0 : ℝ) 1)) := by
  have hL' : (0 : ℝ) ≤ L := by exact_mod_cast hL
  have hcont : ContinuousOn f (Icc (0 : ℝ) 1) :=
    continuousOn_of_lipschitz_bound hL' (by simpa [Real.norm_eq_abs] using hLip)
  have hbdd : BddBelow (f '' Icc (0 : ℝ) 1) := isCompact_Icc.bddBelow_image hcont
  have hne : (f '' Icc (0 : ℝ) 1).Nonempty :=
    ⟨f 0, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩
  constructor
  · simp only [infEnclosure, RatInterval.Contains, Rat.cast_sub, Rat.cast_div,
      Rat.cast_natCast]
    apply le_csInf hne
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hdist⟩ := exists_near_meshPoint hn hx
    have hm := hnodes k hk
    have hmesh := meshPoint_mem hn hk
    have hlip := hLip x hx (meshPoint n k) hmesh
    have hLo : ((minLoUpTo nodes n : ℚ) : ℝ) ≤ (nodes k).lo := by
      exact_mod_cast minLoUpTo_le nodes hk
    have : f (meshPoint n k) - (L : ℝ) / n ≤ f x := by
      have hdist' : |x - meshPoint n k| ≤ (n : ℝ)⁻¹ := by
        simpa [one_div] using hdist
      have habs : |f x - f (meshPoint n k)| ≤ (L : ℝ) / n :=
        by simpa [div_eq_mul_inv] using
          hlip.trans (mul_le_mul_of_nonneg_left hdist' hL')
      linarith [neg_le_of_abs_le habs]
    linarith [hm.1]
  · simp only [infEnclosure, RatInterval.Contains]
    obtain ⟨k, hk, heq⟩ := exists_minHiUpTo nodes n
    have hs : sInf (f '' Icc (0 : ℝ) 1) ≤ f (meshPoint n k) :=
      csInf_le hbdd ⟨meshPoint n k, meshPoint_mem hn hk, rfl⟩
    have hhi := (hnodes k hk).2
    rw [heq]
    exact hs.trans hhi

/-- Rational node enclosures and a Lipschitz bound enclose the supremum of a
real function on the unit mesh interval. -/
theorem supEnclosure_sound {f : ℝ → ℝ} {nodes : ℕ → RatInterval}
    {L : ℚ} (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n)
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |f s - f t| ≤ (L : ℝ) * |s - t|)
    (hnodes : ∀ k ≤ n, (nodes k).Contains (f (meshPoint n k))) :
    (supEnclosure nodes L hL n hn).Contains (sSup (f '' Icc (0 : ℝ) 1)) := by
  have hL' : (0 : ℝ) ≤ L := by exact_mod_cast hL
  have hcont : ContinuousOn f (Icc (0 : ℝ) 1) :=
    continuousOn_of_lipschitz_bound hL' (by simpa [Real.norm_eq_abs] using hLip)
  have hbdd : BddAbove (f '' Icc (0 : ℝ) 1) := isCompact_Icc.bddAbove_image hcont
  have hne : (f '' Icc (0 : ℝ) 1).Nonempty :=
    ⟨f 0, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩
  constructor
  · simp only [supEnclosure, RatInterval.Contains]
    obtain ⟨k, hk, heq⟩ := exists_maxLoUpTo nodes n
    have hs : f (meshPoint n k) ≤ sSup (f '' Icc (0 : ℝ) 1) :=
      le_csSup hbdd ⟨meshPoint n k, meshPoint_mem hn hk, rfl⟩
    have hlo := (hnodes k hk).1
    rw [heq]
    exact hlo.trans hs
  · simp only [supEnclosure, RatInterval.Contains, Rat.cast_add, Rat.cast_div,
      Rat.cast_natCast]
    apply csSup_le hne
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hdist⟩ := exists_near_meshPoint hn hx
    have hm := hnodes k hk
    have hmesh := meshPoint_mem hn hk
    have hlip := hLip x hx (meshPoint n k) hmesh
    have hHi : ((nodes k).hi : ℝ) ≤ maxHiUpTo nodes n := by
      exact_mod_cast hi_le_maxHiUpTo nodes hk
    have hdist' : |x - meshPoint n k| ≤ (n : ℝ)⁻¹ := by simpa [one_div] using hdist
    have habs : |f x - f (meshPoint n k)| ≤ (L : ℝ) / n := by
      simpa [div_eq_mul_inv] using hlip.trans (mul_le_mul_of_nonneg_left hdist' hL')
    linarith [hm.2, le_abs_self (f x - f (meshPoint n k))]

/-- The infimum enclosure width is at most one mesh error plus the uniform node-enclosure width. -/
theorem width_infEnclosure {nodes : ℕ → RatInterval} {w L : ℚ}
    (hw : 0 ≤ w) (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n)
    (hnodes : ∀ k ≤ n, (nodes k).width ≤ w) :
    (infEnclosure nodes L hL n hn).width ≤ w + L / n := by
  obtain ⟨k, hk, heq⟩ := exists_minLoUpTo nodes n
  have hhi := minHiUpTo_le nodes hk
  have hwk := hnodes k hk
  simp only [infEnclosure, RatInterval.width]
  rw [heq]
  unfold RatInterval.width at hwk
  linarith

/-- The supremum enclosure width is at most one mesh error plus the uniform node-enclosure width. -/
theorem width_supEnclosure {nodes : ℕ → RatInterval} {w L : ℚ}
    (hw : 0 ≤ w) (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n)
    (hnodes : ∀ k ≤ n, (nodes k).width ≤ w) :
    (supEnclosure nodes L hL n hn).width ≤ w + L / n := by
  obtain ⟨k, hk, heq⟩ := exists_maxHiUpTo nodes n
  have hlo := lo_le_maxLoUpTo nodes hk
  have hwk := hnodes k hk
  simp only [supEnclosure, RatInterval.width]
  rw [heq]
  unfold RatInterval.width at hwk
  linarith

end CircleMesh
end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
