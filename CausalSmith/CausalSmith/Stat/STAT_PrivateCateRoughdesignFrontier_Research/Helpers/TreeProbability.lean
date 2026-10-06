module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.TreeGeometry
/-! Product-measure bounds for rooted trees enumerated in parent-before-child order. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- Appending an independent uniform child multiplies any prefix event's probability by at
most four micro radii. The selector can be any measurable function of the prefix.  [the theorem's stated inputs and assumptions](hyp:A,hA,parent,hp), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:m,d). -/
-- @node: uniform_child_extension_volume_le
lemma uniform_child_extension_volume_le (m : ℕ) (d : ℝ)
    (A : Set (Fin m → Covariate)) (hA : MeasurableSet A)
    (parent : (Fin m → Covariate) → Covariate) (hp : Measurable parent) :
    ((volume : Measure Covariate).prod
      (Measure.pi (fun _ : Fin m => (volume : Measure Covariate))))
      {yx | yx.2 ∈ A ∧ |(yx.1 : ℝ) - parent yx.2| < 2 * d} ≤
      ENNReal.ofReal (4 * d) *
        (Measure.pi (fun _ : Fin m => (volume : Measure Covariate))) A := by
  classical
  have hS : MeasurableSet {yx : Covariate × (Fin m → Covariate) |
      yx.2 ∈ A ∧ |(yx.1 : ℝ) - parent yx.2| < 2 * d} := by
    exact (hA.preimage measurable_snd).inter
      (measurableSet_lt (show Measurable (fun yx : Covariate × (Fin m → Covariate) =>
        |(yx.1 : ℝ) - parent yx.2|) by fun_prop) measurable_const)
  rw [Measure.prod_apply_symm hS]
  calc
    _ ≤ ∫⁻ x : Fin m → Covariate, A.indicator (fun _ => ENNReal.ofReal (4 * d)) x
        ∂(Measure.pi (fun _ : Fin m => (volume : Measure Covariate))) := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx]
        have he : (fun y : Covariate => (y, x)) ⁻¹'
            {yx | yx.2 ∈ A ∧ |(yx.1 : ℝ) - parent yx.2| < 2 * d} =
            {y : Covariate | |(y : ℝ) - parent x| < 2 * d} := by ext y; simp [hx]
        rw [he]
        simpa only [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using
          volume_covariate_neighborhood_le (parent x : ℝ) (2 * d)
      · simp [hx]
    _ = _ := lintegral_indicator_const hA _

/-- An independent last coordinate obeys the child-extension bound in the original finite
product space, without introducing a conditional probability version.  [the theorem's stated inputs and assumptions](hyp:A,hA,parent,hp), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:m,d). -/
-- @node: pi_uniform_child_extension_volume_le
lemma pi_uniform_child_extension_volume_le (m : ℕ) (d : ℝ)
    (A : Set (Fin m → Covariate)) (hA : MeasurableSet A)
    (parent : (Fin m → Covariate) → Covariate) (hp : Measurable parent) :
    (Measure.pi (fun _ : Fin (m + 1) => (volume : Measure Covariate)))
      {x | (fun i : Fin m => x i.castSucc) ∈ A ∧
        |(x (Fin.last m) : ℝ) - parent (fun i : Fin m => x i.castSucc)| < 2 * d} ≤
      ENNReal.ofReal (4 * d) *
        (Measure.pi (fun _ : Fin m => (volume : Measure Covariate))) A := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Covariate) (Fin.last m)
  have hS : MeasurableSet {yx : Covariate × (Fin m → Covariate) |
      yx.2 ∈ A ∧ |(yx.1 : ℝ) - parent yx.2| < 2 * d} := by
    exact (hA.preimage measurable_snd).inter
      (measurableSet_lt (show Measurable (fun yx : Covariate × (Fin m → Covariate) =>
        |(yx.1 : ℝ) - parent yx.2|) by fun_prop) measurable_const)
  have hmap := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) => (volume : Measure Covariate)) (Fin.last m)).map_eq
  have he : e ⁻¹' {yx : Covariate × (Fin m → Covariate) |
      yx.2 ∈ A ∧ |(yx.1 : ℝ) - parent yx.2| < 2 * d} =
      {x | (fun i : Fin m => x i.castSucc) ∈ A ∧
        |(x (Fin.last m) : ℝ) - parent (fun i : Fin m => x i.castSucc)| < 2 * d} := by
    ext x
    simp [e, MeasurableEquiv.piFinSuccAbove, Fin.init_def]
  have hm : (Measure.pi (fun _ : Fin (m + 1) => (volume : Measure Covariate)))
      (e ⁻¹' {yx : Covariate × (Fin m → Covariate) |
        yx.2 ∈ A ∧ |(yx.1 : ℝ) - parent yx.2| < 2 * d}) =
      ((volume : Measure Covariate).prod
        (Measure.pi (fun _ : Fin m => (volume : Measure Covariate))))
        {yx | yx.2 ∈ A ∧ |(yx.1 : ℝ) - parent yx.2| < 2 * d} := by
    rw [← hmap, Measure.map_apply e.measurable hS]
  rw [he] at hm
  rw [hm]
  exact uniform_child_extension_volume_le m d A hA parent hp

/-- The rooted geometric event obtained by successively adding a child whose parent is a
function of the earlier covariates. Coordinate projections give ordinary ordered labeled trees. -/
-- @node: orderedTreeRegion
def orderedTreeRegion (h d : ℝ)
    (parent : (m : ℕ) → (Fin (m + 1) → Covariate) → Covariate) :
    (m : ℕ) → Set (Fin (m + 1) → Covariate)
  | 0 => {x | |(x 0 : ℝ) - x0| < h}
  | m+1 => {x | (fun i : Fin (m + 1) => x i.castSucc) ∈ orderedTreeRegion h d parent m ∧
      |(x (Fin.last (m + 1)) : ℝ) - parent m (fun i : Fin (m + 1) => x i.castSucc)| < 2 * d}

/-- The ordered rooted-tree event is Borel whenever each parent selector is Borel.  [the theorem's stated inputs and assumptions](hyp:parent,m,hp,m), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:h,d). -/
-- @node: measurableSet_orderedTreeRegion
lemma measurableSet_orderedTreeRegion (h d : ℝ)
    (parent : (m : ℕ) → (Fin (m + 1) → Covariate) → Covariate)
    (hp : ∀ m, Measurable (parent m)) (m : ℕ) :
    MeasurableSet (orderedTreeRegion h d parent m) := by
  induction m with
  | zero => exact measurableSet_lt (by fun_prop) measurable_const
  | succ m ih =>
    change MeasurableSet {x : Fin (m + 2) → Covariate |
      (fun i : Fin (m + 1) => x i.castSucc) ∈ orderedTreeRegion h d parent m ∧
      |(x (Fin.last (m + 1)) : ℝ) - parent m (fun i : Fin (m + 1) => x i.castSucc)| < 2 * d}
    exact (ih.preimage (by fun_prop)).inter
      (measurableSet_lt (show Measurable (fun x : Fin (m + 2) → Covariate =>
        |(x (Fin.last (m + 1)) : ℝ) - parent m (fun i : Fin (m + 1) => x i.castSucc)|)
        by fun_prop) measurable_const)

/-- Under iid uniform design, any parent-before-child rooted tree has probability bounded by
its root length times one child length per edge.  [the theorem's stated inputs and assumptions](hyp:parent,m,hp,m), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:h,d). -/
-- @node: orderedTreeRegion_volume_le
lemma orderedTreeRegion_volume_le (h d : ℝ)
    (parent : (m : ℕ) → (Fin (m + 1) → Covariate) → Covariate)
    (hp : ∀ m, Measurable (parent m)) (m : ℕ) :
    (Measure.pi (fun _ : Fin (m + 1) => (volume : Measure Covariate)))
      (orderedTreeRegion h d parent m) ≤
      ENNReal.ofReal (2 * h) * (ENNReal.ofReal (4 * d)) ^ m := by
  induction m with
  | zero =>
    have he : orderedTreeRegion h d parent 0 =
        Set.pi Set.univ (fun _ : Fin 1 => {x : Covariate | |(x : ℝ) - x0| < h}) := by
      ext x
      simp [orderedTreeRegion, Set.mem_pi, Fin.forall_fin_one]
    rw [he, Measure.pi_pi]
    simpa using volume_tree_root_region_le h
  | succ m ih =>
    calc
      _ ≤ ENNReal.ofReal (4 * d) *
          (Measure.pi (fun _ : Fin (m + 1) => (volume : Measure Covariate)))
            (orderedTreeRegion h d parent m) :=
        pi_uniform_child_extension_volume_le (m + 1) d _
          (measurableSet_orderedTreeRegion h d parent hp m) (parent m) (hp m)
      _ ≤ ENNReal.ofReal (4 * d) *
          (ENNReal.ofReal (2 * h) * (ENNReal.ofReal (4 * d)) ^ m) :=
        mul_le_mul' le_rfl ih
      _ = _ := by rw [pow_succ]; ac_rfl

/-- A labeled tree event in a fixed parent-before-child enumeration. The zero-edge event
imposes no root restriction; the first shared-sign edge supplies localization. -/
-- @node: orderedSharedTreeEvent
def orderedSharedTreeEvent (hL : ℝ) (p : (m : ℕ) → Fin (m + 1)) :
    (m : ℕ) → Set (Fin (m + 1) → Covariate)
  | 0 => Set.univ
  | m+1 => {x | (fun i : Fin (m + 1) => x i.castSucc) ∈ orderedSharedTreeEvent hL p m ∧
      sharedAdj hL (m + 2) x (Fin.last (m + 1)) (p m).castSucc}

/-- The first edge localizes the root, and each later edge supplies its child's geometric
constraint. No isolation restrictions are needed for this event inclusion.  [the theorem's stated inputs and assumptions](hyp:p,m,m), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: orderedSharedTreeEvent_subset_region
lemma orderedSharedTreeEvent_subset_region (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (p : (m : ℕ) → Fin (m + 1)) (m : ℕ) :
    orderedSharedTreeEvent hL p (m + 1) ⊆
      orderedTreeRegion hL (deltaL hL) (fun k x => x (p k)) (m + 1) := by
  induction m with
  | zero =>
    intro x hx
    obtain ⟨_, hedge⟩ := hx
    have hg := sharedAdj_geometric_restrictions hL hhL 2 x
      (Fin.last 1) (p 0).castSucc hedge
    have hp0 : p 0 = 0 := by apply Fin.ext; have := (p 0).isLt; simp only [Fin.val_zero]; omega
    change (|(x ((0 : Fin 1).castSucc) : ℝ) - x0| < hL) ∧ _
    constructor
    · simpa [hp0] using hg.2.1
    · exact hg.2.2
  | succ m ih =>
    intro x hx
    obtain ⟨hprefix, hedge⟩ := hx
    exact ⟨ih hprefix,
      (sharedAdj_geometric_restrictions hL hhL _ x _ _ hedge).2.2⟩

/-- A specified shared-sign tree on at least two iid uniform covariates has probability at
most two macro radii times four micro radii for every edge.  [the theorem's stated inputs and assumptions](hyp:p,m,m,hm), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: orderedSharedTreeEvent_volume_le
lemma orderedSharedTreeEvent_volume_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (p : (m : ℕ) → Fin (m + 1)) (m : ℕ) (hm : 1 ≤ m) :
    (Measure.pi (fun _ : Fin (m + 1) => (volume : Measure Covariate)))
      (orderedSharedTreeEvent hL p m) ≤
      ENNReal.ofReal (2 * hL * (4 * deltaL hL) ^ m) := by
  have hh : 0 < hL := hhL.1
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  calc
    _ ≤ (Measure.pi (fun _ : Fin (k + 1 + 1) => (volume : Measure Covariate)))
        (orderedTreeRegion hL (deltaL hL) (fun j x => x (p j)) (k + 1)) :=
      measure_mono (orderedSharedTreeEvent_subset_region hL hhL p k)
    _ ≤ ENNReal.ofReal (2 * hL) * (ENNReal.ofReal (4 * deltaL hL)) ^ (k + 1) :=
      orderedTreeRegion_volume_le hL (deltaL hL) (fun j x => x (p j))
        (by intro j; fun_prop) (k + 1)
    _ = _ := by
      rw [← ENNReal.ofReal_pow (show 0 ≤ 4 * deltaL hL by unfold deltaL; positivity)]
      exact (ENNReal.ofReal_mul (show 0 ≤ 2 * hL by positivity)).symm

end CausalSmith.Stat.PrivateCateRoughdesign
