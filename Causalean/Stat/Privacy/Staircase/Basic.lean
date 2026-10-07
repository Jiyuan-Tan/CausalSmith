module
public import Causalean.Stat.Privacy.Staircase.CubeWeights

/-!
# Four-input local privacy cone

This module fixes the fourteen nonconstant staircase patterns for four inputs and states the
finite cone and measurable-selection facts needed to refine a private output density.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Causalean.Stat.Privacy.Staircase

/-- A staircase ray is indexed by a nonempty proper subset of the four inputs. -/
abbrev RayIndex := {S : Finset (Fin 4) // S.Nonempty ∧ S ≠ Finset.univ}

instance : MeasurableSpace RayIndex := ⊤

/-- There are exactly fourteen nonconstant staircase rays on four inputs. -/
theorem card_rayIndex : Fintype.card RayIndex = 14 := by
  decide

/-- The staircase pattern equals `r` on its indexing subset and one elsewhere. -/
def ray (r : ℝ) (S : RayIndex) (i : Fin 4) : ℝ :=
  if i ∈ S.val then r else 1

/-- A vector of four real coordinates belongs to the nonnegative four-input local-privacy cone
at ratio `r` when every coordinate is nonnegative and every coordinate is at most `r` times
every other coordinate. -/
def PrivateCone (r : ℝ) (f : Fin 4 → ℝ) : Prop :=
  (∀ i, 0 ≤ f i) ∧ ∀ i j, f i ≤ r * f j

/-- The first fixed ray used to replace the two constant cube patterns: the ray indexed by
the subset containing only the first of the four inputs. -/
def distinguishedRay : RayIndex := ⟨{0}, by decide, by decide⟩

/-- The complementary fixed ray used to replace the two constant cube patterns: the ray
indexed by the subset of the last three of the four inputs. -/
def complementaryRay : RayIndex := ⟨{1, 2, 3}, by decide, by decide⟩

/-- The coefficient of a nonconstant ray in the product-weight cube expansion.
The two constant patterns contribute a common additional coefficient
`(cubeWeight t ∅ + r * cubeWeight t univ) / (r + 1)` to the fixed complementary pair. -/
def cubeRayCoeff (r : ℝ) (t : Fin 4 → ℝ) (S : RayIndex) : ℝ :=
  cubeWeight t S.val +
    if S = distinguishedRay then
      (cubeWeight t ∅ + r * cubeWeight t Finset.univ) / (r + 1)
    else if S = complementaryRay then
      (cubeWeight t ∅ + r * cubeWeight t Finset.univ) / (r + 1)
    else 0

/-- Every coefficient in the explicit fourteen-ray cube expansion is nonnegative
when the cube coordinates lie in the unit interval and the privacy ratio exceeds one. -/
theorem cubeRayCoeff_nonneg (r : ℝ) (hr : 1 < r) (t : Fin 4 → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (S : RayIndex) :
    0 ≤ cubeRayCoeff r t S := by
  have hr0 : 0 ≤ r := by linarith
  have hden : 0 ≤ (cubeWeight t ∅ + r * cubeWeight t Finset.univ) / (r + 1) := by
    apply div_nonneg
    · exact add_nonneg (cubeWeight_nonneg t ht ∅)
        (mul_nonneg hr0 (cubeWeight_nonneg t ht Finset.univ))
    · linarith
  unfold cubeRayCoeff
  split_ifs <;> apply add_nonneg (cubeWeight_nonneg t ht S.val) <;>
    first | exact hden | positivity

/-- The explicit fourteen-ray coefficients reconstruct each coordinate of the
privacy-scaled cube, including zero weights and tied coordinates.

Proof plan: use `cubeWeight_sum` and `cubeWeight_coordinate` for the sixteen-pattern
expansion. The empty and full patterns together contribute the constant
`cubeWeight t ∅ + r * cubeWeight t univ`. The distinguished complementary rays sum
coordinatewise to `r + 1`, so their shared extra coefficient gives that constant. -/
theorem cubeRayCoeff_coordinate (r : ℝ) (hr : 1 < r) (t : Fin 4 → ℝ)
    (i : Fin 4) :
    1 + (r - 1) * t i = ∑ S, cubeRayCoeff r t S * ray r S i := by
  classical
  let s : Finset (Finset (Fin 4)) := (Finset.univ.erase ∅).erase Finset.univ
  have hs (S : Finset (Fin 4)) : S ∈ s ↔ S.Nonempty ∧ S ≠ Finset.univ := by
    simp [s, Finset.nonempty_iff_ne_empty, and_comm]
  have hsum (f : Finset (Fin 4) → ℝ) :
      (∑ S : RayIndex, f S.val) =
        (∑ S : Finset (Fin 4), f S) - f ∅ - f Finset.univ := by
    have h := Finset.sum_subtype (F := inferInstanceAs (Fintype RayIndex)) s hs f
    rw [← h]
    change (∑ S ∈ (Finset.univ.erase ∅).erase Finset.univ, f S) =
      (∑ S : Finset (Fin 4), f S) - f ∅ - f Finset.univ
    rw [Finset.sum_erase_eq_sub (by decide : (Finset.univ : Finset (Fin 4)) ∈
      (Finset.univ.erase ∅))]
    rw [Finset.sum_erase_eq_sub (by simp : (∅ : Finset (Fin 4)) ∈ Finset.univ)]
  let k : ℝ := (cubeWeight t ∅ + r * cubeWeight t Finset.univ) / (r + 1)
  have hpair : ray r distinguishedRay i + ray r complementaryRay i = r + 1 := by
    fin_cases i <;> simp [ray, distinguishedRay, complementaryRay] <;> ring
  have hf (S : Finset (Fin 4)) :
      cubeWeight t S * (if i ∈ S then r else 1) =
        cubeWeight t S + (r - 1) * (cubeWeight t S * (if i ∈ S then 1 else 0)) := by
    split_ifs <;> ring
  have hall :
      (∑ S : Finset (Fin 4), cubeWeight t S * (if i ∈ S then r else 1)) =
        1 + (r - 1) * t i := by
    simp_rw [hf]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, cubeWeight_sum, cubeWeight_coordinate]
  have hbase :
      (∑ S : RayIndex, cubeWeight t S.val * ray r S i) =
        1 + (r - 1) * t i - cubeWeight t ∅ - r * cubeWeight t Finset.univ := by
    rw [show (∑ S : RayIndex, cubeWeight t S.val * ray r S i) =
      ∑ S : RayIndex, cubeWeight t S.val * (if i ∈ S.val then r else 1) from rfl]
    rw [hsum (fun S => cubeWeight t S * (if i ∈ S then r else 1)), hall]
    simp
    ring
  have hcorr :
      (∑ S : RayIndex,
        ((if S = distinguishedRay then k * ray r S i else 0) +
        (if S = complementaryRay then k * ray r S i else 0))) =
        cubeWeight t ∅ + r * cubeWeight t Finset.univ := by
    rw [Finset.sum_add_distrib, Fintype.sum_ite_eq', Fintype.sum_ite_eq']
    rw [← mul_add, hpair]
    dsimp [k]
    field_simp
  have hterm (S : RayIndex) :
      cubeRayCoeff r t S * ray r S i =
        cubeWeight t S.val * ray r S i +
        ((if S = distinguishedRay then k * ray r S i else 0) +
        (if S = complementaryRay then k * ray r S i else 0)) := by
    have hdc : distinguishedRay ≠ complementaryRay := by decide
    by_cases hd : S = distinguishedRay
    · subst S
      simp [cubeRayCoeff, k, hdc]
      ring
    · by_cases hc : S = complementaryRay
      · subst S
        simp [cubeRayCoeff, k, hdc.symm]
        ring
      · simp [cubeRayCoeff, hd, hc]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, hbase, hcorr]
  ring

/-- Every point of the four-dimensional unit cube yields a nonnegative combination
of the fourteen nonconstant staircase rays equal to `1 + (r - 1) * t` coordinatewise.

Proof plan: use `cubeRayCoeff_nonneg` and `cubeRayCoeff_coordinate`. The shared
extra coefficient on the complementary pair is the constant-pattern contribution
divided by `r + 1`. -/
theorem cube_ray_decomposition (r : ℝ) (hr : 1 < r) (t : Fin 4 → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    ∃ c : RayIndex → ℝ,
      (∀ S, 0 ≤ c S) ∧
      ∀ i, 1 + (r - 1) * t i = ∑ S, c S * ray r S i := by
  exact ⟨cubeRayCoeff r t, cubeRayCoeff_nonneg r hr t ht,
    cubeRayCoeff_coordinate r hr t⟩

/-- The least of the four coordinates supplies the scale for a vector in the
four-input local-privacy cone. -/
def coneBase (f : Fin 4 → ℝ) : ℝ :=
  min (f 0) (min (f 1) (min (f 2) (f 3)))

/-- Normalize a privacy-cone vector to a cube coordinate: the coordinate divided by the least
coordinate, minus one, all divided by `r - 1`; the value is zero whenever the least coordinate
is zero, which for a vector in the cone happens only at the zero vector. The formula is
evaluated for arbitrary real vectors as well. -/
def coneCubeCoord (r : ℝ) (f : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  if coneBase f = 0 then 0 else (f i / coneBase f - 1) / (r - 1)

/-- For a private nonnegative vector, its least coordinate is nonnegative,
bounds every coordinate between itself and `r` times itself, and can vanish
only when the whole vector vanishes.

Proof plan: split the finite minimum into four cases; apply pairwise privacy
with an input attaining the minimum. -/
theorem coneBase_geometry (r : ℝ) (f : Fin 4 → ℝ)
    (hf : PrivateCone r f) :
    0 ≤ coneBase f ∧
      (∀ i, coneBase f ≤ f i ∧ f i ≤ r * coneBase f) ∧
      (coneBase f = 0 → ∀ i, f i = 0) := by
  have hnonneg : ∀ i, 0 ≤ f i := hf.1
  have hmin : ∃ j : Fin 4, coneBase f = f j := by
    unfold coneBase
    simp only [min_def]
    split_ifs <;>
      first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩
  have hle : ∀ i, coneBase f ≤ f i := by
    intro i
    fin_cases i <;> simp [coneBase, min_le_left, min_le_right]
  obtain ⟨j, hj⟩ := hmin
  have hupper (i : Fin 4) : f i ≤ r * coneBase f := by
    rw [hj]
    exact hf.2 i j
  refine ⟨?_, fun i => ⟨hle i, hupper i⟩, ?_⟩
  · rw [hj]
    exact hnonneg j
  · intro hzero i
    have hi := hupper i
    rw [hzero, mul_zero] at hi
    exact le_antisymm hi (hnonneg i)

/-- Normalizing a private vector by its least coordinate puts each coordinate
in the unit interval, including the zero vector.

Proof plan: use `coneBase_geometry`; in the positive-base case, multiply the
two desired quotient inequalities by the positive base and by `r - 1`. -/
theorem coneCubeCoord_bounds (r : ℝ) (hr : 1 < r) (f : Fin 4 → ℝ)
    (hf : PrivateCone r f) :
    ∀ i, 0 ≤ coneCubeCoord r f i ∧ coneCubeCoord r f i ≤ 1 := by
  obtain ⟨hb0, hbounds, _⟩ := coneBase_geometry r f hf
  intro i
  by_cases hbase : coneBase f = 0
  · simp [coneCubeCoord, hbase]
  have hbpos : 0 < coneBase f := lt_of_le_of_ne hb0 (Ne.symm hbase)
  have hlo : 1 ≤ f i / coneBase f :=
    (le_div_iff₀ hbpos).2 (by simpa using (hbounds i).1)
  have hhi : f i / coneBase f ≤ r :=
    (div_le_iff₀ hbpos).2 (hbounds i).2
  unfold coneCubeCoord
  rw [if_neg hbase]
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · exact (div_le_iff₀ (by linarith : 0 < r - 1)).2 (by linarith)

/-- Scaling the normalized cube coordinate by the least private-cone coordinate
recovers the original coordinate, including when the entire vector is zero.

Proof plan: in the zero-base case use `coneBase_geometry`; otherwise unfold
`coneCubeCoord` and cancel the nonzero base and `r - 1`. -/
theorem coneCubeCoord_scale (r : ℝ) (hr : 1 < r) (f : Fin 4 → ℝ)
    (hf : PrivateCone r f) (i : Fin 4) :
    f i = coneBase f * (1 + (r - 1) * coneCubeCoord r f i) := by
  by_cases hbase : coneBase f = 0
  · have hzero := (coneBase_geometry r f hf).2.2 hbase i
    simp [coneCubeCoord, hbase, hzero]
  · have hrne : r - 1 ≠ 0 := by linarith
    simp only [coneCubeCoord, if_neg hbase]
    field_simp
    ring

/-- The explicit coefficient of a privacy-cone vector is its least coordinate
times the corresponding fourteen-ray coefficient of its normalized cube point. -/
def coneRayCoeff (r : ℝ) (f : Fin 4 → ℝ) (S : RayIndex) : ℝ :=
  coneBase f * cubeRayCoeff r (coneCubeCoord r f) S

/-- Each explicit ray coefficient is a measurable function of the four input
densities, including where the least coordinate is zero.

Proof plan: the four coordinate projections and their finite minimum are
measurable; division and the zero-base `ite` are measurable; `cubeWeight` is a
finite product. -/
theorem measurable_coneRayCoeff (r : ℝ) (S : RayIndex) :
    Measurable fun f : Fin 4 → ℝ => coneRayCoeff r f S := by
  have hcoord (i : Fin 4) : Measurable (fun f : Fin 4 → ℝ => f i) :=
    measurable_pi_apply i
  have hbase : Measurable (fun f : Fin 4 → ℝ => coneBase f) := by
    unfold coneBase
    exact (hcoord 0).min ((hcoord 1).min ((hcoord 2).min (hcoord 3)))
  have hcube (i : Fin 4) :
      Measurable (fun f : Fin 4 → ℝ => coneCubeCoord r f i) := by
    unfold coneCubeCoord
    apply Measurable.ite (measurableSet_eq_fun hbase measurable_const)
    · exact measurable_const
    · exact (((hcoord i).div hbase).sub measurable_const).div measurable_const
  have hweight (T : Finset (Fin 4)) :
      Measurable (fun f : Fin 4 → ℝ => cubeWeight (coneCubeCoord r f) T) := by
    unfold cubeWeight
    apply Finset.measurable_prod
    intro i hi
    by_cases hit : i ∈ T <;> simp [hit] <;> fun_prop
  have hcoeff : Measurable (fun f : Fin 4 → ℝ => cubeRayCoeff r (coneCubeCoord r f) S) := by
    unfold cubeRayCoeff
    split_ifs
    · exact (hweight S.val).add
        (((hweight ∅).add (measurable_const.mul (hweight Finset.univ))).div measurable_const)
    · exact (hweight S.val).add
        (((hweight ∅).add (measurable_const.mul (hweight Finset.univ))).div measurable_const)
    · exact (hweight S.val).add measurable_const
  unfold coneRayCoeff
  exact hbase.mul hcoeff

/-- The explicit measurable coefficients reconstruct every vector in the
four-input privacy cone as a nonnegative fourteen-ray combination.

Proof plan: use `coneBase_geometry` and `coneCubeCoord_bounds`; when the base is
zero, every coordinate and coefficient vanishes. Otherwise multiply
`cubeRayCoeff_coordinate` by the base and simplify the quotient. -/
theorem coneRayCoeff_decomposition (r : ℝ) (hr : 1 < r) (f : Fin 4 → ℝ)
    (hf : PrivateCone r f) :
    (∀ S, 0 ≤ coneRayCoeff r f S) ∧
      ∀ i, f i = ∑ S, coneRayCoeff r f S * ray r S i := by
  constructor
  · intro S
    unfold coneRayCoeff
    exact mul_nonneg (coneBase_geometry r f hf).1
      (cubeRayCoeff_nonneg r hr (coneCubeCoord r f)
        (coneCubeCoord_bounds r hr f hf) S)
  · intro i
    calc
      f i = coneBase f * (1 + (r - 1) * coneCubeCoord r f i) :=
        coneCubeCoord_scale r hr f hf i
      _ = coneBase f * ∑ S, cubeRayCoeff r (coneCubeCoord r f) S * ray r S i := by
        rw [cubeRayCoeff_coordinate r hr (coneCubeCoord r f) i]
      _ = ∑ S, coneRayCoeff r f S * ray r S i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S _
        unfold coneRayCoeff
        ring

/-- With [a privacy ratio greater than one](hyp:hr) for [the supplied ratio](hyp:r), the
[measurable ray selector](goal) exists: a single rule assigning fourteen ray coefficients to
every real four-vector, each coefficient a measurable function of the vector, such that for
every vector in the four-input privacy cone the coefficients are nonnegative and the vector
equals the corresponding combination of the fourteen nonconstant staircase rays.

Every vector in the four-input privacy cone is a nonnegative combination of the
fourteen nonconstant staircase rays. The coefficients can be selected measurably as a
function of the vector, including at ties and at the zero vector.

Proof plan: use `coneRayCoeff`, `measurable_coneRayCoeff`, and
`coneRayCoeff_decomposition`. -/
theorem measurable_ray_selector (r : ℝ) (hr : 1 < r) :
    ∃ c : (Fin 4 → ℝ) → RayIndex → ℝ,
      (∀ S, Measurable fun f => c f S) ∧
      ∀ f, PrivateCone r f →
        (∀ S, 0 ≤ c f S) ∧
        ∀ i, f i = ∑ S, c f S * ray r S i := by
  exact ⟨coneRayCoeff r, measurable_coneRayCoeff r,
    fun f hf => coneRayCoeff_decomposition r hr f hf⟩

end Causalean.Stat.Privacy.Staircase
