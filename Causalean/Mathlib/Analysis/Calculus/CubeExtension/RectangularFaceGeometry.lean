module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularAffine
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionOperator

/-!
# Geometry of normalized rectangular face collars

The affine normalizer of a nondegenerate box also identifies its lower-face
collar with the corresponding normalized cube collar. These elementary facts
isolate the geometry needed for quantitative reflection transport.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- [The lower corner of the left collar](goal) of [the box with corners lo and
hi](hyp:lo,hi), for [derivative order m](hyp:m) and [coordinate i](hyp:i), agrees
with lo except in coordinate i, where it is lowered by the fraction
1/(2(m + 1)) of the side length hi_i − lo_i. -/
noncomputable def rectLeftLower {d : ℕ} (lo hi : Fin d → ℝ) (m : ℕ)
    (i : Fin d) : Fin d → ℝ :=
  fun j => if j = i then
    lo j - (hi j - lo j) / (2 * ((m : ℝ) + 1)) else lo j

/-- [The left collar](goal) of [the box with corners lo and hi](hyp:lo,hi), for
[derivative order m](hyp:m) and [coordinate i](hyp:i), is the closed box that
extends the original box past its lower face in coordinate i only, by the
fraction 1/(2(m + 1)) of that coordinate's side length. -/
def rectLeftCollar {d : ℕ} (lo hi : Fin d → ℝ) (m : ℕ)
    (i : Fin d) : Set (Fin d → ℝ) :=
  rectBox (rectLeftLower lo hi m i) hi

/-- If [the box with corners lo, hi has positive side lengths](hyp:hbox), then
[at every point x, the affine map sending the left collar of the box in
coordinate i onto the left collar of the normalized cube coincides with the
affine map sending the original box onto the normalized cube](goal). -/
theorem rectAffine_leftCollar_eq_normalize {d : ℕ}
    (lo hi : Fin d → ℝ) (m : ℕ) (i : Fin d)
    (hbox : ∀ j, lo j < hi j) (x : Fin d → ℝ) :
    rectAffine (rectLeftLower lo hi m i) hi
      (fun j => if j = i then -1 - (1 : ℝ) / ((m : ℝ) + 1) else -1)
      (fun _ => 1) x =
    rectAffine lo hi (fun _ => -1) (fun _ => 1) x := by
  funext j
  by_cases hji : j = i
  · subst j
    have hp : 0 < hi i - lo i := sub_pos.mpr (hbox i)
    have hw : hi i - lo i ≠ 0 := ne_of_gt hp
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    have hw' : hi i - (lo i - (hi i - lo i) / (2 * ((m : ℝ) + 1))) ≠ 0 := by
      have hpos : 0 < (hi i - lo i) / (2 * ((m : ℝ) + 1)) := by positivity
      exact ne_of_gt (by linarith)
    have hslope :
        (1 - (-1 - (1 : ℝ) / ((m : ℝ) + 1))) /
          (hi i - (lo i - (hi i - lo i) / (2 * ((m : ℝ) + 1)))) =
        2 / (hi i - lo i) := by
      apply (div_eq_iff hw').2
      field_simp [hw, hm]
      ring
    simp only [rectAffine, rectLeftLower, ↓reduceIte]
    rw [hslope]
    field_simp [hw, hm]
    ring
  · simp only [rectAffine, rectLeftLower, hji, ↓reduceIte]

/-- If [the box with corners lo, hi has positive side lengths](hyp:hbox), then
[the affine normalization of the box onto the normalized cube maps the box's
left collar in coordinate i exactly onto the normalized cube's left collar in
coordinate i](goal), in the sense that the collar is the preimage of the cube's
collar. -/
theorem rectAffine_preimage_leftCubeCollar {d : ℕ}
    (lo hi : Fin d → ℝ) (m : ℕ) (i : Fin d)
    (hbox : ∀ j, lo j < hi j) :
    rectAffine lo hi (fun _ => -1) (fun _ => 1) ⁻¹'
      leftCubeCollar d m i = rectLeftCollar lo hi m i := by
  let lower : Fin d → ℝ := fun j => if j = i then
    -1 - (1 : ℝ) / ((m : ℝ) + 1) else -1
  have hsource : ∀ j, rectLeftLower lo hi m i j < hi j := by
    intro j
    by_cases hji : j = i
    · subst j
      have hp : 0 < hi i - lo i := sub_pos.mpr (hbox i)
      have hpos : 0 < (hi i - lo i) / (2 * ((m : ℝ) + 1)) := by positivity
      simp only [rectLeftLower, ↓reduceIte]
      linarith
    · simpa [rectLeftLower, hji] using hbox j
  have htarget : ∀ j, lower j < (1 : ℝ) := by
    intro j
    by_cases hji : j = i
    · simp only [lower, hji, ↓reduceIte]
      have : 0 < (1 : ℝ) / ((m : ℝ) + 1) := by positivity
      linarith
    · simp [lower, hji]
  have hcollar : leftCubeCollar d m i = rectBox lower (fun _ => 1) := by
    ext x
    simp only [leftCubeCollar, rectBox, Set.mem_ofPred_eq]
    constructor <;> intro hx j
    · by_cases hji : j = i
      · have hj := hx j
        simp only [hji, ↓reduceIte, Set.mem_Icc] at hj
        simp only [lower, hji, ↓reduceIte, Set.mem_Icc]
        exact hj
      · have hj := hx j
        simp only [hji, ↓reduceIte, Set.mem_Icc] at hj
        simp only [lower, hji, ↓reduceIte, Set.mem_Icc]
        exact hj
    · by_cases hji : j = i
      · have hj := hx j
        simp only [lower, hji, ↓reduceIte, Set.mem_Icc] at hj
        simp only [hji, ↓reduceIte, Set.mem_Icc]
        exact hj
      · have hj := hx j
        simp only [lower, hji, ↓reduceIte, Set.mem_Icc] at hj
        simp only [hji, ↓reduceIte, Set.mem_Icc]
        exact hj
  rw [hcollar]
  have hmap : rectAffine lo hi (fun _ => -1) (fun _ => 1) =
      rectAffine (rectLeftLower lo hi m i) hi lower (fun _ => 1) := by
    funext x
    simpa [lower] using (rectAffine_leftCollar_eq_normalize lo hi m i hbox x).symm
  rw [hmap, rectAffine_preimage_rectBox _ _ _ _ hsource htarget]
  rfl

/-- If [the box with corners lo, hi has positive side lengths](hyp:hbox), then
[mapping a point from the normalized cube's coordinates to the box's
coordinates and back returns the original point](goal), for every point of the
ambient space. -/
theorem rectAffine_normalize_denormalize {d : ℕ}
    (lo hi : Fin d → ℝ) (hbox : ∀ j, lo j < hi j)
    (x : Fin d → ℝ) :
    rectAffine lo hi (fun _ => -1) (fun _ => 1)
      (rectAffine (fun _ => -1) (fun _ => 1) lo hi x) = x := by
  funext j
  have hw : hi j - lo j ≠ 0 := ne_of_gt (sub_pos.mpr (hbox j))
  simp only [rectAffine]
  field_simp [hw]
  ring

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
