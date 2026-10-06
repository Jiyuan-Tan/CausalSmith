module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentPartition
/-! Geometric support restrictions and rooted integration bounds for shared-sign trees.
Each child is integrated in its parent's micro neighborhood; the root is in the macro window. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- A nonzero localized frame is strictly inside both the macro and micro supports.  [the theorem's stated inputs and assumptions](hyp:j,x,hx), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: weighted_frame_nonzero_radii
lemma weighted_frame_nonzero_radii (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (j : ℤ) (x : Covariate) (hx : envelope hL x * frame hL j x ≠ 0) :
    |(x : ℝ) - x0| < hL ∧ |(x : ℝ) - j * deltaL hL| < deltaL hL := by
  constructor
  · by_contra h
    exact hx (by rw [envelope_zero_of_radius_le hL hhL x (le_of_not_gt h), zero_mul])
  · by_contra h
    exact hx (by rw [frame_zero_of_radius_le hL hhL j x (le_of_not_gt h), mul_zero])

/-- Two points sharing a localized sign are separated by less than two micro radii.  [the theorem's stated inputs and assumptions](hyp:j,x,y,hx,hy), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: shared_frame_distance_lt
lemma shared_frame_distance_lt (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (j : ℤ) (x y : Covariate)
    (hx : envelope hL x * frame hL j x ≠ 0)
    (hy : envelope hL y * frame hL j y ≠ 0) :
    |(x : ℝ) - y| < 2 * deltaL hL := by
  have hx' := (weighted_frame_nonzero_radii hL hhL j x hx).2
  have hy' := (weighted_frame_nonzero_radii hL hhL j y hy).2
  calc
    _ = |((x : ℝ) - j * deltaL hL) - ((y : ℝ) - j * deltaL hL)| := by congr 1; ring
    _ ≤ |(x : ℝ) - j * deltaL hL| + |(y : ℝ) - j * deltaL hL| := abs_sub _ _
    _ < _ := by linarith

/-- Every shared-sign edge has both endpoints in the open macro window and short length.  [the theorem's stated inputs and assumptions](hyp:n,x,i,l,hi), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: sharedAdj_geometric_restrictions
lemma sharedAdj_geometric_restrictions (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (i l : Fin n) (hi : sharedAdj hL n x i l) :
    |(x i : ℝ) - x0| < hL ∧ |(x l : ℝ) - x0| < hL ∧
      |(x i : ℝ) - x l| < 2 * deltaL hL := by
  obtain ⟨_, j, _, hij, hlj⟩ := hi
  exact ⟨(weighted_frame_nonzero_radii hL hhL j (x i) hij).1,
    (weighted_frame_nonzero_radii hL hhL j (x l) hlj).1,
    shared_frame_distance_lt hL hhL j (x i) (x l) hij hlj⟩

/-- A record on or outside the macro boundary has no shared-sign neighbor.  [the theorem's stated inputs and assumptions](hyp:n,x,i,l,hi,x,i), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: not_sharedAdj_of_macro_boundary
lemma not_sharedAdj_of_macro_boundary (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (i l : Fin n)
    (hi : hL ≤ |(x i : ℝ) - x0|) : ¬ sharedAdj hL n x i l := by
  intro hedge
  exact (not_lt_of_ge hi) (sharedAdj_geometric_restrictions hL hhL n x i l hedge).1

/-- Any subset of a real-radius neighborhood in the unit interval has volume at most its length. [The displayed conclusion](goal) follows. -/
-- @node: volume_covariate_neighborhood_le
lemma volume_covariate_neighborhood_le (c r : ℝ) :
    (volume : Measure Covariate) {x | |(x : ℝ) - c| < r} ≤ ENNReal.ofReal (2 * r) := by
  rw [unitInterval.volume_apply]
  calc
    _ ≤ (volume : Measure ℝ) (Ioo (c-r) (c+r)) := by
      apply measure_mono
      rintro z ⟨x, hx, rfl⟩
      have hx' := abs_lt.mp (show |(x : ℝ) - c| < r from hx)
      constructor <;> linarith
    _ = _ := by rw [Real.volume_Ioo]; congr 1; ring

/-- The potential child region of a frozen parent has length at most four micro radii. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: volume_tree_child_region_le
lemma volume_tree_child_region_le (hL : ℝ) (x : Covariate) :
    (volume : Measure Covariate) {y | |(y : ℝ) - x| < 2 * deltaL hL} ≤
      ENNReal.ofReal (4 * deltaL hL) := by
  simpa only [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using
    volume_covariate_neighborhood_le (x : ℝ) (2 * deltaL hL)

/-- The root region has length at most two macro radii. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: volume_tree_root_region_le
lemma volume_tree_root_region_le (hL : ℝ) :
    (volume : Measure Covariate) {x | |(x : ℝ) - x0| < hL} ≤ ENNReal.ofReal (2 * hL) :=
  volume_covariate_neighborhood_le x0 hL

/-- The exact rooted-order integral for successive children constrained to their parent's
neighborhood. The parent selector reads only the already sampled covariates. -/
-- @node: treeExtensionVolume
def treeExtensionVolume (d : ℝ) (parent : List Covariate → Covariate) :
    ℕ → List Covariate → ℝ≥0∞
  | 0, _ => 1
  | m+1, xs => ∫⁻ y : Covariate,
      {y : Covariate | |(y : ℝ) - parent xs| < 2 * d}.indicator
        (fun y => treeExtensionVolume d parent m (xs ++ [y])) y

/-- Each newly integrated child costs at most four micro radii, regardless of the previous
covariates or the choice of its parent among them. [The displayed conclusion](goal) follows. -/
-- @node: treeExtensionVolume_le
lemma treeExtensionVolume_le (d : ℝ) (parent : List Covariate → Covariate)
    (m : ℕ) (xs : List Covariate) :
    treeExtensionVolume d parent m xs ≤ (ENNReal.ofReal (4 * d)) ^ m := by
  classical
  induction m generalizing xs with
  | zero => simp [treeExtensionVolume]
  | succ m ih =>
    rw [treeExtensionVolume]
    calc
      _ ≤ ∫⁻ y : Covariate,
          {y : Covariate | |(y : ℝ) - parent xs| < 2 * d}.indicator
            (fun _ => (ENNReal.ofReal (4 * d)) ^ m) y := by
        apply lintegral_mono
        intro y
        exact Set.indicator_le_indicator (ih _)
      _ = (ENNReal.ofReal (4 * d)) ^ m *
          (volume : Measure Covariate) {y | |(y : ℝ) - parent xs| < 2 * d} :=
        lintegral_indicator_const (measurableSet_lt (by fun_prop) measurable_const) _
      _ ≤ (ENNReal.ofReal (4 * d)) ^ m * ENNReal.ofReal (4 * d) := by
        apply mul_le_mul' le_rfl
        simpa only [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using
          volume_covariate_neighborhood_le (parent xs : ℝ) (2 * d)
      _ = _ := (pow_succ _ m).symm

/-- Integrating the root and then the children gives the roadmap's specified-tree envelope.  [the theorem's stated inputs and assumptions](hyp:m), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:h,d,parent). -/
-- @node: rooted_tree_iterated_volume_le
lemma rooted_tree_iterated_volume_le (h d : ℝ) (parent : List Covariate → Covariate)
    (m : ℕ) :
    (∫⁻ x : Covariate, {x : Covariate | |(x : ℝ) - x0| < h}.indicator
      (fun x => treeExtensionVolume d parent m [x]) x) ≤
      ENNReal.ofReal (2 * h) * (ENNReal.ofReal (4 * d)) ^ m := by
  classical
  calc
    _ ≤ ∫⁻ x : Covariate, {x : Covariate | |(x : ℝ) - x0| < h}.indicator
        (fun _ => (ENNReal.ofReal (4 * d)) ^ m) x := by
      apply lintegral_mono
      intro x
      exact Set.indicator_le_indicator (treeExtensionVolume_le d parent m _)
    _ = (ENNReal.ofReal (4 * d)) ^ m *
        (volume : Measure Covariate) {x | |(x : ℝ) - x0| < h} :=
      lintegral_indicator_const (measurableSet_lt (by fun_prop) measurable_const) _
    _ ≤ (ENNReal.ofReal (4 * d)) ^ m * ENNReal.ofReal (2 * h) :=
      mul_le_mul' le_rfl (volume_tree_root_region_le h)
    _ = _ := mul_comm _ _

end CausalSmith.Stat.PrivateCateRoughdesign
