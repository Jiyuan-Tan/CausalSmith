module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Int.Interval
/-! Localized cosine frames and their exact squared partition identity, including lattice
and macro support boundaries. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign

-- @env: S4
variable (hL : ℝ) -- @realizes hL(lower-family real radius)
variable (hhL : 0 < hL ∧ hL ≤ 1 / 4) -- @realizes hL(radius range)
-- @realizes deltaL(lower-family micro radius)
/-- The lower-family micro radius is the fifth power of its macro radius. -/
def deltaL : ℝ := hL^5
-- @realizes kappa(fixed amplitude constant)
/-- The amplitude constant is two to the power minus twelve. -/
def kappa : ℝ := (2 : ℝ)^(-12 : ℤ)
-- @realizes t(lower-family target separation)
/-- The target separation is the amplitude constant times the macro radius. -/
def separation : ℝ := kappa*hL
-- @realizes g(localized squared-cosine macro envelope)
open Classical in
/-- The macro envelope is the squared cosine inside the localization window and zero outside. -/
def envelope (x : Covariate) : ℝ :=
  if |(x : ℝ) - x0| ≤ hL then (Real.cos (Real.pi*((x : ℝ)-x0)/(2*hL)))^2 else 0
-- @realizes q(effect bump = g squared)
/-- The effect bump squares the macro envelope. -/
def bump (x : Covariate) : ℝ := (envelope hL x)^2
-- @realizes phi(overlapping cosine frame)
open Classical in
/-- Each overlapping cosine frame element is supported within one micro radius of its integer
center. -/
def frame (j : ℤ) (x : Covariate) : ℝ :=
  if |(x : ℝ) - j*deltaL hL| ≤ deltaL hL then
    Real.cos (Real.pi*((x : ℝ)-j*deltaL hL)/(2*deltaL hL)) else 0
/-- The localized macro envelope is Borel measurable, including its boundary convention. [The displayed conclusion](goal) follows. -/
-- @node: measurable_envelope
@[fun_prop] lemma measurable_envelope : Measurable (envelope hL) := by
  unfold envelope
  apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const) <;> fun_prop

/-- Squaring the macro envelope preserves measurability. [The displayed conclusion](goal) follows. -/
-- @node: measurable_bump
@[fun_prop] lemma measurable_bump : Measurable (bump hL) := by
  unfold bump
  fun_prop

/-- Each localized cosine frame is Borel measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_frame
@[fun_prop] lemma measurable_frame (j : ℤ) : Measurable (frame hL j) := by
  unfold frame
  apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const) <;> fun_prop

/-- The squared-cosine envelope takes values between zero and one.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: envelope_range
lemma envelope_range (x : Covariate) : envelope hL x ∈ Icc 0 1 := by
  unfold envelope
  split
  · exact ⟨sq_nonneg _, Real.cos_sq_le_one _⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- The effect bump also takes values between zero and one.  [the theorem's stated inputs and assumptions](hyp:x), and [the asserted conclusion follows](goal). -/
-- @node: bump_range
lemma bump_range (x : Covariate) : bump hL x ∈ Icc 0 1 := by
  have hg := envelope_range hL x
  unfold bump
  constructor
  · exact sq_nonneg _
  · nlinarith [mul_nonneg hg.1 (sub_nonneg.mpr hg.2)]

-- @realizes Jsign(finite active integer supports; strict intersection)
open Classical in
/-- The finite active integer indices have frame interiors intersecting the interior of the macro
window. -/
def activeSigns : Finset ℤ :=
  (Finset.Icc (⌊((x0 : ℝ)-hL)/deltaL hL⌋-1)
    (⌈((x0 : ℝ)+hL)/deltaL hL⌉+1)).filter (fun j =>
      (j : ℝ)*deltaL hL - deltaL hL < (x0 : ℝ)+hL ∧
        (x0 : ℝ)-hL < (j : ℝ)*deltaL hL + deltaL hL)
-- @realizes lambda(uniform binary encoding of the sign vector)
/-- The latent signs are binary encodings of minus one and one on the active index set. -/
abbrev SignVector (hL : ℝ) := (activeSigns hL) → Bool
include hhL in
/-- The finite index construction selects exactly the strict support intersections for every legal
macro radius. [The displayed conclusion](goal) follows. -/
-- @node: mem_activeSigns
lemma mem_activeSigns (j : ℤ) : j ∈ activeSigns hL ↔
    ((j : ℝ)*deltaL hL-deltaL hL < (x0 : ℝ)+hL ∧
      (x0 : ℝ)-hL < (j : ℝ)*deltaL hL+deltaL hL) := by
  classical
  unfold activeSigns
  rw [Finset.mem_filter]
  constructor
  · exact fun hj => hj.2
  · intro hj
    refine ⟨?_, hj⟩
    rw [Finset.mem_Icc]
    have hd : 0 < deltaL hL := pow_pos hhL.1 5
    have hlo := Int.floor_le (((x0 : ℝ) - hL) / deltaL hL)
    have hhi := Int.le_ceil (((x0 : ℝ) + hL) / deltaL hL)
    have hl : (((x0 : ℝ) - hL) / deltaL hL) < (j : ℝ) + 1 := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith [hj.2]
    have hu : (j : ℝ) - 1 < (((x0 : ℝ) + hL) / deltaL hL) := by
      apply (lt_div_iff₀ hd).mpr
      nlinarith [hj.1]
    constructor
    · have : (⌊((x0 : ℝ) - hL) / deltaL hL⌋ : ℝ) - 1 ≤ (j : ℝ) := by
        linarith
      exact_mod_cast this
    · have : (j : ℝ) ≤ (⌈((x0 : ℝ) + hL) / deltaL hL⌉ : ℝ) + 1 := by
        linarith
      exact_mod_cast this


include hhL in
/-- A frame vanishes at either support endpoint and beyond it.  [the theorem's stated inputs and assumptions](hyp:hx,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:j). -/
-- @node: frame_zero_of_radius_le
lemma frame_zero_of_radius_le (j : ℤ) (x : Covariate)
    (hx : deltaL hL ≤ |(x : ℝ) - j * deltaL hL|) : frame hL j x = 0 := by
  have hd : 0 < deltaL hL := pow_pos hhL.1 5
  unfold frame
  split
  · rename_i hin
    have he := le_antisymm hin hx
    rcases (abs_eq (le_of_lt hd)).mp he with he | he
    · rw [he]
      have : Real.pi * deltaL hL / (2 * deltaL hL) = Real.pi / 2 := by
        field_simp <;> ring
      rw [this, Real.cos_pi_div_two]
    · rw [he]
      have : Real.pi * (-deltaL hL) / (2 * deltaL hL) = -(Real.pi / 2) := by
        field_simp <;> ring
      rw [this, Real.cos_neg, Real.cos_pi_div_two]
  · rfl

include hhL in
/-- The macro envelope vanishes at its endpoints as well as outside its support.  [the theorem's stated inputs and assumptions](hyp:hx,x), and [the asserted conclusion follows](goal). -/
-- @node: envelope_zero_of_radius_le
lemma envelope_zero_of_radius_le (x : Covariate)
    (hx : hL ≤ |(x : ℝ) - x0|) : envelope hL x = 0 := by
  unfold envelope
  split
  · rename_i hin
    have he := le_antisymm hin hx
    rcases (abs_eq hhL.1.le).mp he with he | he
    · rw [he]
      have : Real.pi * hL / (2 * hL) = Real.pi / 2 := by field_simp [hhL.1.ne'] <;> ring
      rw [this, Real.cos_pi_div_two]; norm_num
    · rw [he]
      have : Real.pi * (-hL) / (2 * hL) = -(Real.pi / 2) := by field_simp [hhL.1.ne'] <;> ring
      rw [this, Real.cos_neg, Real.cos_pi_div_two]; norm_num
  · rfl

include hhL in
/-- An index omitted from the active frame set contributes zero after localization.  [the theorem's stated inputs and assumptions](hyp:hj), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:j,x). -/
-- @node: inactive_weighted_frame_zero
lemma inactive_weighted_frame_zero (j : ℤ) (x : Covariate)
    (hj : j ∉ activeSigns hL) : bump hL x * (frame hL j x)^2 = 0 := by
  by_cases hg : hL ≤ |(x : ℝ) - x0|
  · rw [bump, envelope_zero_of_radius_le hL hhL x hg]; ring
  · have hd : 0 < deltaL hL := pow_pos hhL.1 5
    have hx := abs_lt.mp (lt_of_not_ge hg)
    have hnj := mt (mem_activeSigns hL hhL j).mpr hj
    push_neg at hnj
    have hf : deltaL hL ≤ |(x : ℝ) - j * deltaL hL| := by
      by_cases hl : (j : ℝ) * deltaL hL - deltaL hL < (x0 : ℝ) + hL
      · have hu := hnj hl
        rw [abs_of_nonneg (by linarith : 0 ≤ (x : ℝ) - j * deltaL hL)]
        linarith [hx.1]
      · rw [abs_of_nonpos (by linarith : (x : ℝ) - j * deltaL hL ≤ 0)]
        linarith [hx.2]
    rw [frame_zero_of_radius_le hL hhL j x hf]; ring

include hhL in
/-- On a lattice interval the two neighboring frame squares sum to one. The result uses [the stated assumptions](hyp:hl,hu) and establishes [the displayed conclusion](goal). -/
-- @node: neighboring_frame_squares
lemma neighboring_frame_squares (q : ℤ) (x : Covariate)
    (hl : (q : ℝ) * deltaL hL ≤ x)
    (hu : (x : ℝ) ≤ (q + 1 : ℤ) * deltaL hL) :
    (frame hL q x)^2 + (frame hL (q + 1) x)^2 = 1 := by
  have hd : 0 < deltaL hL := pow_pos hhL.1 5
  have hqc : ((q + 1 : ℤ) : ℝ) = (q : ℝ) + 1 := by push_cast; rfl
  have h0 : |(x : ℝ) - q * deltaL hL| ≤ deltaL hL := by
    rw [abs_of_nonneg (by linarith)]
    rw [hqc] at hu; nlinarith
  have h1 : |(x : ℝ) - (q + 1 : ℤ) * deltaL hL| ≤ deltaL hL := by
    rw [abs_of_nonpos (by linarith)]
    rw [hqc]; nlinarith
  simp only [frame, h0, h1, if_true]
  have hang : Real.pi * ((x : ℝ) - (q + 1 : ℤ) * deltaL hL) / (2 * deltaL hL) =
      Real.pi * ((x : ℝ) - q * deltaL hL) / (2 * deltaL hL) - Real.pi / 2 := by
    rw [hqc]; field_simp <;> ring
  rw [hang, Real.cos_sub_pi_div_two, Real.cos_sq_add_sin_sq]

include hhL in
/-- All frames except the two neighboring indices vanish on a lattice interval. The result uses [the stated assumptions](hyp:hl,hu,hj0,hj1) and establishes [the displayed conclusion](goal). -/
-- @node: frame_zero_off_neighbors
lemma frame_zero_off_neighbors (q j : ℤ) (x : Covariate)
    (hl : (q : ℝ) * deltaL hL ≤ x)
    (hu : (x : ℝ) ≤ (q + 1 : ℤ) * deltaL hL)
    (hj0 : j ≠ q) (hj1 : j ≠ q + 1) : frame hL j x = 0 := by
  have hd : 0 < deltaL hL := pow_pos hhL.1 5
  apply frame_zero_of_radius_le hL hhL
  by_cases hj : j < q
  · have hgap : (j : ℝ) + 1 ≤ q := by exact_mod_cast (show j + 1 ≤ q by omega)
    rw [abs_of_nonneg (by nlinarith : 0 ≤ (x : ℝ) - j * deltaL hL)]
    nlinarith
  · have hgap : (q : ℝ) + 2 ≤ j := by exact_mod_cast (show q + 2 ≤ j by omega)
    have huc : (x : ℝ) ≤ ((q : ℝ) + 1) * deltaL hL := by simpa using hu
    rw [abs_of_nonpos (by nlinarith : (x : ℝ) - j * deltaL hL ≤ 0)]
    nlinarith

include hhL in
/-- Localizing the finite frame square sum gives exactly the effect bump everywhere.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: weighted_frame_square_partition
lemma weighted_frame_square_partition (x : Covariate) :
    bump hL x * ∑ j : activeSigns hL, (frame hL j x)^2 = bump hL x := by
  classical
  let q : ℤ := ⌊(x : ℝ) / deltaL hL⌋
  have hd : 0 < deltaL hL := pow_pos hhL.1 5
  have hl : (q : ℝ) * deltaL hL ≤ x := (le_div_iff₀ hd).mp (Int.floor_le _)
  have hu : (x : ℝ) ≤ (q + 1 : ℤ) * deltaL hL := by
    have hu := (div_lt_iff₀ hd).mp (Int.lt_floor_add_one ((x : ℝ) / deltaL hL))
    simpa [q] using hu.le
  let f : ℤ → ℝ := fun j => bump hL x * (frame hL j x)^2
  have hfinite : (∑ j ∈ activeSigns hL, f j) = ∑ j ∈ activeSigns hL ∪ {q, q+1}, f j := by
    apply Finset.sum_subset (Finset.subset_union_left)
    intro j hj hnot
    exact inactive_weighted_frame_zero hL hhL j x hnot
  have hpair : (∑ j ∈ ({q, q+1} : Finset ℤ), f j) =
      ∑ j ∈ activeSigns hL ∪ {q, q+1}, f j := by
    apply Finset.sum_subset (Finset.subset_union_right)
    intro j hj hnot
    have hj0 : j ≠ q := by intro he; subst j; simp at hnot
    have hj1 : j ≠ q+1 := by intro he; subst j; simp at hnot
    dsimp [f]
    rw [frame_zero_off_neighbors hL hhL q j x hl hu hj0 hj1]; ring
  rw [Finset.mul_sum]
  change (∑ j ∈ (activeSigns hL).attach, f j) = _
  rw [Finset.sum_attach, hfinite, ← hpair]
  simp only [Finset.sum_insert (by simp : q ∉ ({q+1} : Finset ℤ)), Finset.sum_singleton]
  dsimp [f]
  rw [← mul_add, neighboring_frame_squares hL hhL q x hl hu, mul_one]

end CausalSmith.Stat.PrivateCateRoughdesign
