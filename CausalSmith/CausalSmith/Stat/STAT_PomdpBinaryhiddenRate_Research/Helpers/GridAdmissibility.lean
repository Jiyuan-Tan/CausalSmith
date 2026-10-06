module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Constructions
public import Causalean.Mathlib.Probability.Certified.Existence

/-!
# Admissibility of the finite stable-grid estimator

The finite candidate set contains a reset kernel. Its selected matrix is
stochastic, its stationary reward is bounded, and selection is measurable
because it depends on finitely many measurable comparisons.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory
open scoped BigOperators
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

/-- Every enumerated candidate has simplex transition rows. [Under the listed formal conditions](hyp:hc), [the stated conclusion holds](goal).-/
-- @node: gridCandidates_row
lemma gridCandidates_row {M : Nat} {alpha : ℝ} {c : GridCode M}
    (hc : c ∈ gridCandidates M alpha) (i : Fin 4) :
    IsGridRow M (c.2.1 i) := by
  classical
  obtain ⟨nu, hnu, R, hR, r, hr, heq⟩ := by
    simpa only [gridCandidates, Finset.mem_filter, gridCandidateUniverse,
      Finset.mem_biUnion, Finset.mem_image] using (Finset.mem_filter.mp hc).1
  cases heq
  obtain ⟨rows, hrows, hEq⟩ := Finset.mem_image.mp hR
  rw [← hEq]
  have hi := (Finset.mem_pi.mp hrows) i (Finset.mem_univ i)
  exact (Finset.mem_filter.mp hi).2

/-- A point-mass row repeated four times supplies a grid candidate. [Under the listed formal conditions](hyp:hα), [the stated conclusion holds](goal).-/
-- @node: gridCandidates_nonempty
lemma gridCandidates_nonempty (M : Nat) (alpha : ℝ) (hα : 0 ≤ alpha) :
    (gridCandidates M alpha).Nonempty := by
  classical
  let u : Fin 4 → Fin (M + 1) := fun i => if i = 0 then ⟨M, by omega⟩ else 0
  have hu : u ∈ simplexGrid M := by
    simp [simplexGrid, IsGridRow, u, Fin.sum_univ_succ]
  let R : Fin 4 → Fin 4 → Fin (M + 1) := fun _ => u
  have hR : R ∈ gridMatrixRows M := by
    apply Finset.mem_image.mpr
    refine ⟨fun _ _ => u, ?_, rfl⟩
    exact Finset.mem_pi.mpr (fun _ _ => hu)
  let c : GridCode M := (u, R, fun _ => 0)
  refine ⟨c, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨u, hu, Finset.mem_biUnion.mpr ⟨R, hR, ?_⟩⟩
    exact Finset.mem_image.mpr ⟨fun _ => 0, Finset.mem_univ _, rfl⟩
  · have hz : gridDobrushin (gridR c) = 0 := by
      simp [gridDobrushin, gridR, c, R]
    rw [hz]
    positivity

/-- Both stages of minimization retain membership in the candidate set. [Under the listed formal conditions](hyp:hα), [the stated conclusion holds](goal).-/
-- @node: selectGridCode_mem
lemma selectGridCode_mem {T M : Nat} (alpha : ℝ) (hα : 0 ≤ alpha)
    (b e : Policy 2) (w : ObsView T 2) :
    selectGridCode (M := M) alpha b e w ∈ gridCandidates M alpha := by
  classical
  unfold selectGridCode
  rw [dif_pos (gridCandidates_nonempty M alpha hα)]
  dsimp only
  split_ifs with hm
  · exact (Finset.mem_filter.mp
      (Classical.choose_spec (Finset.exists_min_image _ gridLexCode hm)).1).1
  · exact (Classical.choose_spec (Finset.exists_min_image _ _
      (gridCandidates_nonempty M alpha hα))).1

/-- Positive-resolution simplex grid rows decode to a stochastic matrix. [Under the listed formal conditions](hyp:hM,hc), [the stated conclusion holds](goal).-/
-- @node: gridR_stochastic
lemma gridR_stochastic {M : Nat} (hM : 0 < M) {alpha : ℝ} {c : GridCode M}
    (hc : c ∈ gridCandidates M alpha) : IsStochasticMatrix (gridR c) := by
  constructor
  · intro i j
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro i
    simp only [gridR, ← Finset.sum_div]
    have hi : (∑ j : Fin 4, ((c.2.1 i j).val : ℝ)) = M := by
      exact_mod_cast gridCandidates_row hc i
    rw [hi, div_self (by positivity : (M : ℝ) ≠ 0)]

/-- Mixing a stochastic grid matrix with a positive reset gives a stationary law. [Under the listed formal conditions](hyp:hM,hα,hc), [the stated conclusion holds](goal).-/
-- @node: stabilizedGridMatrix_stationary
lemma stabilizedGridMatrix_stationary {M : Nat} (hM : 0 < M)
    {alpha : ℝ} (hα : 0 < alpha) {c : GridCode M}
    (hc : c ∈ gridCandidates M alpha) :
    IsStationary (stabilizedGridMatrix alpha c)
      (stationaryLaw (stabilizedGridMatrix alpha c)) := by
  have hR := gridR_stochastic hM hc
  let lam := alpha / (alpha + 6 / (M : ℝ))
  have hden : 0 < alpha + 6 / (M : ℝ) := by positivity
  have hlam0 : 0 ≤ lam := by dsimp [lam]; positivity
  have hlam1 : lam < 1 := by
    dsimp [lam]
    apply (div_lt_one hden).mpr
    have : 0 < 6 / (M : ℝ) := by positivity
    linarith
  have hP : IsStochasticMatrix (stabilizedGridMatrix alpha c) := by
    constructor
    · intro i j
      change 0 ≤ lam * gridR c i j + (1 - lam) / 4
      exact add_nonneg (mul_nonneg hlam0 (hR.1 i j)) (by positivity)
    · intro i
      dsimp only [stabilizedGridMatrix]
      change (∑ j : Fin 4, (lam * gridR c i j + (1 - lam) / 4)) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hR.2 i]
      simp
      ring
  have hminor : Minorizes (stabilizedGridMatrix alpha c) (1 - lam)
      (fun _ : Fin 4 => (1 / 4 : ℝ)) := by
    refine ⟨⟨by intro i; norm_num, by norm_num⟩, by linarith, by linarith, ?_⟩
    intro i j
    change (1 - lam) * (1 / 4) ≤ lam * gridR c i j + (1 - lam) / 4
    nlinarith [mul_nonneg hlam0 (hR.1 i j)]
  have hcontract := contractsL1_of_minorization hP hminor
  have hex := existsUnique_stationary_of_contractsL1 hP
    (show 0 ≤ 1 - (1 - lam) by linarith)
    (show 1 - (1 - lam) < 1 by linarith) hcontract
  exact stationaryLaw_isStationary_of_exists hex.exists

/-- Every selected candidate has a stationary reward between zero and one. [Under the listed formal conditions](hyp:_ht0,hT), [the stated conclusion holds](goal).-/
-- @node: stableGridEstimator_range
lemma stableGridEstimator_range (T : Nat) (t0 : ℝ)
    (_ht0 : 0 < t0) (hT : 12 ≤ T) (b e : Policy 2) (w : ObsView T 2) :
    stableGridEstimator T t0 b e w ∈ Set.Icc (0 : ℝ) 1 := by
  have hα : 0 < mixingAlpha t0 := Real.exp_pos _
  have hsize : 0 < gridSize T (mixingAlpha t0) := by
    unfold gridSize
    apply Nat.ceil_pos.mpr
    have : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
    positivity
  let c := selectGridCode (M := gridSize T (mixingAlpha t0)) (mixingAlpha t0) b e w
  have hc : c ∈ gridCandidates (gridSize T (mixingAlpha t0)) (mixingAlpha t0) :=
    selectGridCode_mem _ hα.le b e w
  have hp := (stabilizedGridMatrix_stationary hsize hα hc).1
  have hr (i : Fin 4) : gridReward c i ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · apply (div_le_one (by exact_mod_cast hsize :
          (0 : ℝ) < gridSize T (mixingAlpha t0))).mpr
      exact_mod_cast (Nat.le_of_lt_succ (c.2.2 i).isLt)
  change (∑ i, stationaryLaw (stabilizedGridMatrix (mixingAlpha t0) c) i *
      gridReward c i) ∈ Set.Icc (0 : ℝ) 1
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp.1 i) (hr i).1)
  · calc
      _ ≤ ∑ i, stationaryLaw (stabilizedGridMatrix (mixingAlpha t0) c) i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_of_le_one_right (hp.1 i) (hr i).2
      _ = 1 := hp.2

/-- A fixed-window score satisfies the [measurability conclusion](goal). -/
-- @node: score_measurable
@[fun_prop] lemma score_measurable {T : Nat} (k : Nat) (b e : Policy 2) (t : Fin T) :
    Measurable (fun w : ObsView T 2 => score k b e w t) := by
  unfold score
  have hratio : Measurable (fun z : Fin 2 × Bool => ratio b e z.1 z.2) :=
    measurable_of_finite _
  apply Measurable.mul (by fun_prop)
  apply Finset.measurable_prod
  intro j hj
  exact hratio.comp (show Measurable
    (fun w : ObsView T 2 => ((w j).1, (w j).2.1)) by fun_prop)

/-- Each empirical moment satisfies the [measurability conclusion](goal). -/
-- @node: empiricalMoment_measurable
@[fun_prop] lemma empiricalMoment_measurable {T : Nat} (k : Nat) (b e : Policy 2) :
    Measurable (empiricalMoment (T := T) k b e) := by
  unfold empiricalMoment
  fun_prop

/-- The seven-moment maximum discrepancy satisfies the [measurability conclusion](goal). -/
-- @node: gridObjective_measurable
@[fun_prop] lemma gridObjective_measurable {T M : Nat} (alpha : ℝ)
    (b e : Policy 2) (c : GridCode M) :
    Measurable (fun w : ObsView T 2 => gridObjective alpha b e w c) := by
  unfold gridObjective
  apply Measurable.iSup
  intro k
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using
    ((empiricalMoment_measurable k.val b e).sub
      (measurable_const (a :=  ∑ s : Fin 4,
        (Matrix.vecMul (gridNu c) ((stabilizedGridMatrix alpha c) ^ k.val)) s *
          gridReward c s))).norm

/-- Choosing a minimum depends only on the pairwise order of the objectives. [Under the listed formal conditions](hyp:hs,h), [the stated conclusion holds](goal).-/
-- @node: grid_min_choose_congr
lemma grid_min_choose_congr {C : Type*} (s : Finset C) (hs : s.Nonempty)
    (f g : C → ℝ) (h : ∀ c d, f c ≤ f d ↔ g c ≤ g d) :
    Classical.choose (Finset.exists_min_image s f hs) =
      Classical.choose (Finset.exists_min_image s g hs) := by
  have heq : (fun c => c ∈ s ∧ ∀ d ∈ s, f c ≤ f d) =
      (fun c => c ∈ s ∧ ∀ d ∈ s, g c ≤ g d) := by
    funext c
    apply propext
    simp_rw [h]
  generalize hp : (Finset.exists_min_image s f hs) = p
  generalize hq : (Finset.exists_min_image s g hs) = q
  change @Classical.choose C (fun c => c ∈ s ∧ ∀ d ∈ s, f c ≤ f d) p =
    @Classical.choose C (fun c => c ∈ s ∧ ∀ d ∈ s, g c ≤ g d) q
  congr 1

/-- The selected code is constant whenever all objective comparisons agree. [Under the listed formal conditions](hyp:h), [the stated conclusion holds](goal).-/
-- @node: selectGridCode_order_congr
lemma selectGridCode_order_congr {T M : Nat} (alpha : ℝ)
    (b e : Policy 2) (w w' : ObsView T 2)
    (h : ∀ c d : GridCode M,
      gridObjective alpha b e w c ≤ gridObjective alpha b e w d ↔
      gridObjective alpha b e w' c ≤ gridObjective alpha b e w' d) :
    selectGridCode (M := M) alpha b e w = selectGridCode alpha b e w' := by
  classical
  let s := gridCandidates M alpha
  let f : GridCode M → ℝ := gridObjective alpha b e w
  let g : GridCode M → ℝ := gridObjective alpha b e w'
  by_cases hs : s.Nonempty
  · let a := Classical.choose (Finset.exists_min_image s f hs)
    let a' := Classical.choose (Finset.exists_min_image s g hs)
    have ha : a = a' := grid_min_choose_congr s hs f g h
    let sf := s.filter (fun c => f c = f a)
    let sg := s.filter (fun c => g c = g a')
    have hsg : sf = sg := by
      apply Finset.ext
      intro c
      simp only [sf, sg, Finset.mem_filter, ha, le_antisymm_iff, f, g, h]
    unfold selectGridCode
    dsimp only
    rw [dif_pos hs, dif_pos hs]
    change (if hm : sf.Nonempty then
        Classical.choose (Finset.exists_min_image sf gridLexCode hm) else a) =
      (if hm : sg.Nonempty then
        Classical.choose (Finset.exists_min_image sg gridLexCode hm) else a')
    have hsf : sf.Nonempty := by
      refine ⟨a, Finset.mem_filter.mpr ⟨?_, rfl⟩⟩
      exact (Classical.choose_spec (Finset.exists_min_image s f hs)).1
    have hsg' : sg.Nonempty := hsg ▸ hsf
    rw [dif_pos hsf, dif_pos hsg']
    congr 1
    funext c
    rw [hsg]
  · unfold selectGridCode
    dsimp only
    rw [dif_neg hs, dif_neg hs]

/-- Finite measurable comparisons give a selected code satisfying the [measurability conclusion](goal). -/
-- @node: selectGridCode_measurable
@[fun_prop] lemma selectGridCode_measurable {T M : Nat} (alpha : ℝ)
    (b e : Policy 2) :
    Measurable (fun w : ObsView T 2 => selectGridCode (M := M) alpha b e w) := by
  classical
  let table : ObsView T 2 → (GridCode M × GridCode M → Bool) :=
    fun w cd => decide (gridObjective alpha b e w cd.1 ≤
      gridObjective alpha b e w cd.2)
  have htable : Measurable table := by
    apply measurable_pi_lambda
    intro cd
    apply measurable_to_bool
    simpa only [table, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
      measurableSet_le (gridObjective_measurable alpha b e cd.1)
        (gridObjective_measurable alpha b e cd.2)
  let decode : (GridCode M × GridCode M → Bool) → GridCode M := fun q =>
    if hq : ∃ w, table w = q then selectGridCode alpha b e (Classical.choose hq)
    else default
  have hdecode : Measurable decode := measurable_of_finite _
  have hfactor : (fun w : ObsView T 2 => selectGridCode (M := M) alpha b e w) =
      decode ∘ table := by
    funext w
    dsimp only [Function.comp_def, decode]
    rw [dif_pos (show ∃ w', table w' = table w from ⟨w, rfl⟩)]
    apply selectGridCode_order_congr
    intro c d
    have hq := Classical.choose_spec (show ∃ w', table w' = table w from ⟨w, rfl⟩)
    have hcd := congrFun hq (c, d)
    simpa only [table, decide_eq_decide] using hcd.symm
  rw [hfactor]
  exact hdecode.comp htable

/-- Composing the selected code with its stationary reward satisfies the [measurability conclusion](goal). -/
-- @node: stableGridEstimator_measurable
@[fun_prop] lemma stableGridEstimator_measurable (T : Nat) (t0 : ℝ)
    (b e : Policy 2) : Measurable (stableGridEstimator T t0 b e) := by
  let value : GridCode (gridSize T (mixingAlpha t0)) → ℝ := fun c =>
    ∑ s : Fin 4,
      stationaryLaw (stabilizedGridMatrix (mixingAlpha t0) c) s * gridReward c s
  exact (measurable_of_finite value).comp
    (selectGridCode_measurable (mixingAlpha t0) b e)

/-- The finite-grid construction gives a unit-interval-valued measurable
procedure for every supplied pair of policies in the theorem's regime. [Under the listed formal conditions](hyp:ht0,hT), [the stated conclusion holds](goal).-/
-- @node: stableGridEstimator_admissible
lemma stableGridEstimator_admissible (T : Nat) (t0 : ℝ)
    (ht0 : 0 < t0) (hT : 12 ≤ T) :
    (∀ b e w, stableGridEstimator T t0 b e w ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ b e, Measurable (stableGridEstimator T t0 b e)) := by
  exact ⟨stableGridEstimator_range T t0 ht0 hT,
    stableGridEstimator_measurable T t0⟩

end CausalSmith.Stat.PomdpBinaryhiddenRate
