module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Construction
/-! Explicit endpoints and measurability for the affine acceptance-set inversion. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign
variable (n : ℕ) (epsilon h : ℝ) (k : ℕ)
/-- Positive denominators turn the affine acceptance inequality into two explicit endpoints. The result uses [the stated assumptions](hyp:hb,hr) and establishes [the displayed conclusion](goal). -/
-- @node: affine_acceptance_positive
lemma affine_acceptance_positive (b z r : ℝ) (hb : 0 < b) (hr : 0 ≤ r) :
    {x : ℝ | x ∈ Icc (-1) 1 ∧ |clip (-b) b z - x*b| ≤ r*b} =
      Icc (max (-1) (clip (-b) b z / b - r))
        (min 1 (clip (-b) b z / b + r)) := by
  ext x
  simp only [mem_setOf_eq, mem_Icc, max_le_iff, le_min_iff, abs_le]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, h0, h1⟩
    refine ⟨⟨hx0, ?_⟩, hx1, ?_⟩
    · have : clip (-b) b z / b ≤ x + r :=
        (div_le_iff₀ hb).mpr (by nlinarith)
      linarith
    · have : x - r ≤ clip (-b) b z / b :=
        (le_div_iff₀ hb).mpr (by nlinarith)
      linarith
  · rintro ⟨⟨hx0, hxlo⟩, hx1, hxhi⟩
    have hlo : clip (-b) b z ≤ (x+r)*b :=
      (div_le_iff₀ hb).mp (by linarith)
    have hhi : (x-r)*b ≤ clip (-b) b z :=
      (le_div_iff₀ hb).mp (by linarith)
    exact ⟨⟨hx0, hx1⟩, by nlinarith, by nlinarith⟩

/-- Clipping places the center inside the target range, so the truncated endpoints are ordered.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:b,z,r,hb,hr). -/
-- @node: affine_acceptance_endpoints_ordered
lemma affine_acceptance_endpoints_ordered (b z r : ℝ) (hb : 0 < b) (hr : 0 ≤ r) :
    max (-1) (clip (-b) b z / b - r) ≤ min 1 (clip (-b) b z / b + r) := by
  have hlo : -b ≤ clip (-b) b z := le_max_left _ _
  have hhi : clip (-b) b z ≤ b := by
    unfold clip
    exact max_le (by linarith) (min_le_left _ _)
  have hc0 : -1 ≤ clip (-b) b z / b := (le_div_iff₀ hb).mpr (by linarith)
  have hc1 : clip (-b) b z / b ≤ 1 := (div_le_iff₀ hb).mpr (by linarith)
  simp only [max_le_iff, le_min_iff]
  constructor <;> constructor <;> linarith

/-- A nonpositive denominator gives the full range at zero, a singleton at zero radius,
or an empty acceptance set. The result uses [the stated assumptions](hyp:hb,hr) and establishes [the displayed conclusion](goal). -/
-- @node: affine_acceptance_nonpositive
lemma affine_acceptance_nonpositive (b z r : ℝ) (hb : b ≤ 0) (hr : 0 ≤ r) :
    {x : ℝ | x ∈ Icc (-1) 1 ∧ |clip (-b) b z - x*b| ≤ r*b} =
      if b = 0 then Icc (-1) 1 else if r = 0 then Icc (-1) (-1) else ∅ := by
  have hc : clip (-b) b z = -b := by
    unfold clip
    exact max_eq_left (by have := min_le_left b z; linarith)
  rw [hc]
  split_ifs with hb0 hr0
  · subst b
    ext x
    simp
  · have hbneg : b < 0 := lt_of_le_of_ne hb hb0
    subst r
    ext x
    simp only [mem_setOf_eq, mem_Icc, zero_mul, abs_le]
    constructor
    · rintro ⟨⟨hx0, hx1⟩, he⟩
      have : x = -1 := by nlinarith [he.1, he.2]
      simp [this]
    · rintro ⟨hx0, hx1⟩
      have : x = -1 := by linarith
      subst x
      constructor
      · constructor <;> norm_num
      · simp
  · have hbneg : b < 0 := lt_of_le_of_ne hb hb0
    have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    ext x
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro hx ha
    have := abs_nonneg (-b - x*b)
    have := mul_neg_of_pos_of_neg hrpos hbneg
    linarith

-- @realizes vartheta(candidate effect in [-1,1] and affine acceptance inequality)
open Classical in
/-- The inversion accepts exactly the target-range candidates satisfying the specified floored and
clipped affine inequality. -/
def acceptedSet (v : Fin 2 → ℝ) : Set ℝ :=
  let bd := max (d0 n h k) (v 1)
  let bn := clip (-bd) bd (v 0)
  {vartheta | vartheta ∈ Icc (-1) 1 ∧
    |bn - vartheta*bd| ≤ Real.sqrt (10*Vbound n epsilon h k)*bd}
open Classical in
/-- The inversion returns the closed interval hull of the accepted set, with the prescribed full-
range fallback. -/
def inversionMap (v : Fin 2 → ℝ) : IntervalCode :=
  if (acceptedSet n epsilon h k v).Nonempty then
    closedInterval (sInf (acceptedSet n epsilon h k v)) (sSup (acceptedSet n epsilon h k v))
  else closedInterval (-1) 1
/-- The interval hull inversion has explicit endpoints on every denominator branch.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:v). -/
-- @node: inversionMap_eq_endpoints
lemma inversionMap_eq_endpoints (v : Fin 2 → ℝ) :
    inversionMap n epsilon h k v =
      if 0 < max (d0 n h k) (v 1) then
        closedInterval
          (max (-1) (clip (-(max (d0 n h k) (v 1))) (max (d0 n h k) (v 1)) (v 0) /
            max (d0 n h k) (v 1) - Real.sqrt (10*Vbound n epsilon h k)))
          (min 1 (clip (-(max (d0 n h k) (v 1))) (max (d0 n h k) (v 1)) (v 0) /
            max (d0 n h k) (v 1) + Real.sqrt (10*Vbound n epsilon h k)))
      else if max (d0 n h k) (v 1) = 0 then closedInterval (-1) 1
      else if Real.sqrt (10*Vbound n epsilon h k) = 0 then closedInterval (-1) (-1)
      else closedInterval (-1) 1 := by
  classical
  let b := max (d0 n h k) (v 1)
  let r := Real.sqrt (10*Vbound n epsilon h k)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  change inversionMap n epsilon h k v = if 0 < b then _ else _
  by_cases hb : 0 < b
  · rw [if_pos hb]
    have hs : acceptedSet n epsilon h k v =
        Icc (max (-1) (clip (-b) b (v 0) / b - r))
          (min 1 (clip (-b) b (v 0) / b + r)) :=
      affine_acceptance_positive b (v 0) r hb hr
    have ho := affine_acceptance_endpoints_ordered b (v 0) r hb hr
    simp only [inversionMap, hs, nonempty_Icc.mpr ho, ↓reduceIte, csInf_Icc ho, csSup_Icc ho]
    rfl
  · rw [if_neg hb]
    have hs := affine_acceptance_nonpositive b (v 0) r (le_of_not_gt hb) hr
    change acceptedSet n epsilon h k v = _ at hs
    by_cases hb0 : b = 0
    · rw [if_pos hb0]
      have hs' : acceptedSet n epsilon h k v = Icc (-1) 1 := by simpa [hb0] using hs
      simp [inversionMap, hs', csInf_Icc, csSup_Icc]
    · rw [if_neg hb0]
      by_cases hr0 : r = 0
      · rw [if_pos hr0]
        have hs' : acceptedSet n epsilon h k v = Icc (-1) (-1) := by
          simpa [hb0, hr0] using hs
        simp [inversionMap, hs', csInf_Icc, csSup_Icc]
      · rw [if_neg hr0]
        have hs' : acceptedSet n epsilon h k v = ∅ := by simpa [hb0, hr0] using hs
        simp [inversionMap, hs']

/-- The explicit inversion is measurable, including the zero and negative denominator cases. [The displayed conclusion](goal) follows. -/
-- @node: measurable_inversionMap
@[fun_prop] lemma measurable_inversionMap :
    Measurable (inversionMap n epsilon h k) := by
  have heq := funext (inversionMap_eq_endpoints n epsilon h k)
  rw [heq]
  have hb : Measurable (fun v : Fin 2 → ℝ => max (d0 n h k) (v 1)) := by fun_prop
  apply Measurable.ite
  · exact measurableSet_lt measurable_const hb
  · unfold closedInterval clip
    fun_prop
  · apply Measurable.ite
    · exact measurableSet_eq_fun hb measurable_const
    · exact measurable_const
    · by_cases hr : Real.sqrt (10*Vbound n epsilon h k) = 0 <;>
        simp only [hr, ↓reduceIte] <;> exact measurable_const

-- @node: def:interval-handle
-- @realizes Iopt(explicit inversion and interval hull with fallback)
open Classical in
/-- The publicly tuned inversion uses the same single joint release and returns the full target
range in the constant branch. -/
def optimalIntervalHandle : Kernel (Dataset n) IntervalCode :=
  if 1/8 ≤ rate n epsilon then Kernel.const _ (Measure.dirac (closedInterval (-1) 1))
  else (privateRatioRelease n epsilon (tunedH n epsilon) (tunedK n epsilon)).mapOfMeasurable
    (inversionMap n epsilon (tunedH n epsilon) (tunedK n epsilon))
    (measurable_inversionMap n epsilon (tunedH n epsilon) (tunedK n epsilon))
-- @realizes ell(optimal numerical interval scale)
open Classical in
/-- The numerical interval scale output is the benchmark. -/
def ell : ℝ := rate n epsilon
-- @realizes cI(fixed interval lower constant)
open Classical in
/-- The fixed interval lower constant is two to the power minus twenty. -/
def cI : ℝ := (2 : ℝ)^(-20 : ℤ)
-- @realizes CI(fixed interval upper constant)
open Classical in
/-- The fixed interval upper constant is two to the power twenty-two. -/
def CI : ℝ := 2^22


end CausalSmith.Stat.PrivateCateRoughdesign
