module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingPhaseSums
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingRank

/-! # Predictable selection of actual rounding moves

Seed-history events select zero-padded phase increments without changing their
conditional means. Their finite second moments add exactly, and their coordinate
variance is the corresponding selected norm-energy expenditure. Random interval
masks telescope pathwise, so a phase's endpoint bound can be applied before
integrating. The construction of the actual phase intervals is separate.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ A seed-history event can select a centered fresh increment without bias.](goal) Under [the stated conditions](hyp:hignore,hmean). -/
-- @node: cube_predictable_indicator_mean
lemma cube_predictable_indicator_mean {m : ℕ} (j : Fin m)
    (E : Set (Cube m)) (D : Cube m → ℝ)
    (hignore : ∀ x t, Function.update x j t ∈ E ↔ x ∈ E)
    (hmean : ∀ x, (∫ t, D (Function.update x j t)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 0) :
    ∀ x, (∫ t, E.indicator D (Function.update x j t)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 0 := by
  classical
  intro x
  by_cases hx : x ∈ E
  · simp only [Set.indicator, hignore, hx, if_true]
    exact hmean x
  · simp only [Set.indicator, hignore, hx, if_false, integral_zero]

/-- [ A predictable selected increment is orthogonal to any preceding square-integrable
statistic, including a preceding selected partial sum.](goal) Under [the stated conditions](hyp:hE,hA,hD,hignoreA,hignoreE,hmean). -/
-- @node: cube_predictable_indicator_orthogonal
lemma cube_predictable_indicator_orthogonal {m : ℕ} (j : Fin m)
    (E : Set (Cube m)) (A D : Cube m → ℝ) (hE : MeasurableSet E)
    (hA : MemLp A 2 (cubeMeasure m)) (hD : MemLp D 2 (cubeMeasure m))
    (hignoreA : ∀ x t, A (Function.update x j t) = A x)
    (hignoreE : ∀ x t, Function.update x j t ∈ E ↔ x ∈ E)
    (hmean : ∀ x, (∫ t, D (Function.update x j t)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 0) :
    (∫ x, A x * E.indicator D x ∂cubeMeasure m) = 0 := by
  exact cube_fresh_increment_orthogonal j A (E.indicator D) hA
    (hD.indicator hE) hignoreA
    (cube_predictable_indicator_mean j E D hignoreE hmean)

variable {n : ℕ}

/-- [ Earlier actual row increments ignore every seed at or after the current move.](goal) Under [the stated conditions](hyp:hl,hj). -/
-- @node: roundingIteration_past_row_increment_update
lemma roundingIteration_past_row_increment_update (a : Fin (n / 4) → Fin n → ℝ)
    (c : Fin n → ℝ) (seeds : RoundingSeeds n) (k l : ℕ)
    (hl : l < k) (j : Fin (3 * n)) (hj : 2 * k ≤ j.val) (t : ℝ) :
    rowDot c (roundingIteration a (Function.update seeds j t) (l + 1)).1 -
      rowDot c (roundingIteration a (Function.update seeds j t) l).1 =
    rowDot c (roundingIteration a seeds (l + 1)).1 -
      rowDot c (roundingIteration a seeds l).1 := by
  rw [roundingIteration_update_future a seeds (l + 1) j t (by omega),
    roundingIteration_update_future a seeds l j t (by omega)]

/-- [ Measurable phase membership preserves the actual increment's second moment domain.](goal) Under [the stated conditions](hyp:hE). -/
-- @node: roundingIteration_masked_row_increment_memLp
lemma roundingIteration_masked_row_increment_memLp (a : Fin (n / 4) → Fin n → ℝ)
    (c : Fin n → ℝ) (k : ℕ) (E : Set (RoundingSeeds n)) (hE : MeasurableSet E) :
    MemLp (E.indicator (fun seeds =>
      rowDot c (roundingIteration a seeds (k + 1)).1 -
        rowDot c (roundingIteration a seeds k).1)) 2 (roundingSeedLaw n) :=
  ((roundingIteration_row_memLp a c (k + 1)).sub
    (roundingIteration_row_memLp a c k)).indicator hE

/-- [ The actual next coin centers every predictably selected row increment.](goal) Under [the stated conditions](hyp:hk,hE). -/
-- @node: roundingIteration_masked_row_increment_mean
lemma roundingIteration_masked_row_increment_mean (a : Fin (n / 4) → Fin n → ℝ)
    (c : Fin n → ℝ) (k : ℕ) (hk : k < n) (E : Set (RoundingSeeds n))
    (hE : ∀ seeds t, Function.update seeds ⟨2 * k + 1, by omega⟩ t ∈ E ↔ seeds ∈ E) :
    ∀ seeds, (∫ t, E.indicator (fun seeds =>
      rowDot c (roundingIteration a seeds (k + 1)).1 -
        rowDot c (roundingIteration a seeds k).1)
      (Function.update seeds ⟨2 * k + 1, by omega⟩ t)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 0 := by
  apply cube_predictable_indicator_mean _ _ _ hE
  intro seeds
  simp_rw [show ∀ u v : Fin n → ℝ, rowDot c u - rowDot c v = rowDot c (u - v)
    from fun u v => (dotProduct_sub c u v).symm]
  exact roundingIteration_next_row_increment_mean a c seeds k hk

/-- [ The zero-padded moves in any predictable phase have additive second moments.
Membership may depend on all preceding seeds; no deterministic phase lengths are assumed.](goal) Under [the stated conditions](hyp:hm,hE,hpast). -/
-- @node: roundingIteration_masked_row_second_moment_sum
lemma roundingIteration_masked_row_second_moment_sum
    (a : Fin (n / 4) → Fin n → ℝ) (c : Fin n → ℝ)
    (E : ℕ → Set (RoundingSeeds n)) (m : ℕ) (hm : m ≤ n)
    (hE : ∀ k < m, MeasurableSet (E k))
    (hpast : ∀ k < m, ∀ seeds (j : Fin (3 * n)) t,
      2 * k ≤ j.val → (Function.update seeds j t ∈ E k ↔ seeds ∈ E k)) :
    (∫ seeds, (∑ k ∈ Finset.range m, (E k).indicator (fun seeds =>
      rowDot c (roundingIteration a seeds (k + 1)).1 -
        rowDot c (roundingIteration a seeds k).1) seeds) ^ 2 ∂roundingSeedLaw n) =
    ∑ k ∈ Finset.range m, ∫ seeds, ((E k).indicator (fun seeds =>
      rowDot c (roundingIteration a seeds (k + 1)).1 -
        rowDot c (roundingIteration a seeds k).1) seeds) ^ 2 ∂roundingSeedLaw n := by
  classical
  apply finite_orthogonal_increment_second_moment
  · intro k hk
    exact roundingIteration_masked_row_increment_memLp a c k (E k) (hE k hk)
  · intro k hk
    apply cube_fresh_increment_orthogonal ⟨2 * k + 1, by omega⟩
    · exact memLp_finsetSum _ (fun l hl =>
        roundingIteration_masked_row_increment_memLp a c l (E l)
          (hE l (by have := Finset.mem_range.mp hl; omega)))
    · exact roundingIteration_masked_row_increment_memLp a c k (E k) (hE k hk)
    · intro seeds t
      apply Finset.sum_congr rfl
      intro l hl
      have hlk := Finset.mem_range.mp hl
      simp only [Set.indicator,
        hpast l (by omega) seeds ⟨2 * k + 1, by omega⟩ t (by dsimp; omega),
        roundingIteration_past_row_increment_update a c seeds k l hlk
          ⟨2 * k + 1, by omega⟩ (by dsimp; omega) t]
    · exact roundingIteration_masked_row_increment_mean a c k (by omega) (E k)
        (fun seeds t => hpast k hk seeds _ t (by dsimp; omega))

/-- [ A selected actual move remains orthogonal to the current fractional coordinate.](goal) Under [the stated conditions](hyp:hk,hE,hpast). -/
-- @node: roundingIteration_masked_coordinate_orthogonal
lemma roundingIteration_masked_coordinate_orthogonal
    (a : Fin (n / 4) → Fin n → ℝ) (k : ℕ) (hk : k < n) (i : Fin n)
    (E : Set (RoundingSeeds n)) (hE : MeasurableSet E)
    (hpast : ∀ seeds t,
      Function.update seeds ⟨2 * k + 1, by omega⟩ t ∈ E ↔ seeds ∈ E) :
    (∫ seeds, (roundingIteration a seeds k).1 i * E.indicator (fun seeds =>
      (roundingIteration a seeds (k + 1)).1 i - (roundingIteration a seeds k).1 i) seeds
      ∂roundingSeedLaw n) = 0 := by
  apply cube_predictable_indicator_orthogonal ⟨2 * k + 1, by omega⟩ E
  · exact hE
  · exact roundingIteration_coordinate_memLp a k i
  · exact (roundingIteration_coordinate_memLp a (k + 1) i).sub
      (roundingIteration_coordinate_memLp a k i)
  · intro seeds t
    rw [roundingIteration_update_future a seeds k _ t (by dsimp; omega)]
  · exact hpast
  · intro seeds
    exact roundingIteration_next_coordinate_increment_mean a seeds k hk i

/-- [ The selected coordinate variance is exactly its selected square-energy increment.](goal) Under [the stated conditions](hyp:hk,hE,hpast). -/
-- @node: roundingIteration_masked_coordinate_energy
lemma roundingIteration_masked_coordinate_energy
    (a : Fin (n / 4) → Fin n → ℝ) (k : ℕ) (hk : k < n) (i : Fin n)
    (E : Set (RoundingSeeds n)) (hE : MeasurableSet E)
    (hpast : ∀ seeds t,
      Function.update seeds ⟨2 * k + 1, by omega⟩ t ∈ E ↔ seeds ∈ E) :
    (∫ seeds, (E.indicator (fun seeds =>
      (roundingIteration a seeds (k + 1)).1 i - (roundingIteration a seeds k).1 i) seeds) ^ 2
      ∂roundingSeedLaw n) =
    ∫ seeds, E.indicator (fun seeds => (roundingIteration a seeds (k + 1)).1 i ^ 2 -
      (roundingIteration a seeds k).1 i ^ 2) seeds ∂roundingSeedLaw n := by
  classical
  let u (seeds : RoundingSeeds n) := (roundingIteration a seeds k).1 i
  let v (seeds : RoundingSeeds n) := (roundingIteration a seeds (k + 1)).1 i
  have hu : MemLp u 2 (roundingSeedLaw n) := roundingIteration_coordinate_memLp a k i
  have hv : MemLp v 2 (roundingSeedLaw n) := roundingIteration_coordinate_memLp a (k + 1) i
  have hd : MemLp (E.indicator (fun seeds => v seeds - u seeds)) 2 (roundingSeedLaw n) :=
    (hv.sub hu).indicator hE
  have hi : Integrable (E.indicator (fun seeds => v seeds ^ 2 - u seeds ^ 2))
      (roundingSeedLaw n) := (hv.integrable_sq.sub hu.integrable_sq).indicator hE
  have hp : Integrable (fun seeds => u seeds *
      E.indicator (fun seeds => v seeds - u seeds) seeds) (roundingSeedLaw n) := by
    convert hu.integrable_mul hd using 1
    funext seeds
    exact (Pi.mul_apply _ _ seeds).symm
  have hexp (seeds : RoundingSeeds n) :
      (E.indicator (fun seeds => v seeds - u seeds) seeds) ^ 2 =
      E.indicator (fun seeds => v seeds ^ 2 - u seeds ^ 2) seeds -
      2 * (u seeds * E.indicator (fun seeds => v seeds - u seeds) seeds) := by
    by_cases hs : seeds ∈ E
    · simp only [Set.indicator_of_mem hs]
      ring
    · simp [Set.indicator_of_notMem hs]
  change (∫ seeds, (E.indicator (fun seeds => v seeds - u seeds) seeds) ^ 2
    ∂roundingSeedLaw n) = _
  simp_rw [hexp]
  have ht : Integrable (fun seeds => 2 * (u seeds *
      E.indicator (fun seeds => v seeds - u seeds) seeds)) (roundingSeedLaw n) := hp.const_mul 2
  rw [integral_sub hi ht, integral_const_mul]
  have hz := roundingIteration_masked_coordinate_orthogonal a k hk i E hE hpast
  change (∫ seeds, u seeds * E.indicator (fun seeds => v seeds - u seeds) seeds
    ∂roundingSeedLaw n) = 0 at hz
  rw [hz, mul_zero, sub_zero]

/-- [ No boundary move changes an already inactive coordinate, even with an empty basis.](goal) Under [the stated conditions](hyp:hi). -/
-- @node: roundingStep_inactive_fixed
lemma roundingStep_inactive_fixed (a : Fin (n / 4) → Fin n → ℝ) (q : ℕ)
    (u : Fin n → ℝ) (seed₁ seed₂ : ℝ) (i : Fin n) (hi : ¬ |u i| < 1) :
    roundingStep a q u seed₁ seed₂ i = u i := by
  let bs := nullspaceBasis a q u
  let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
  let v := inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) seed₁
  have hz : v i = 0 := by
    by_cases he : bs = []
    · simp [v, he, ws, inverseCDF]
    · exact nullspaceBasis_active_support a q u v
        (rounding_selected_direction_mem a q u seed₁ he) i hi
  simp only [roundingStep, ite_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  change (if seed₂ < boundaryMinus u v / (boundaryPlus u v + boundaryMinus u v)
    then u i + boundaryPlus u v * v i else u i - boundaryMinus u v * v i) = u i
  simp [hz]

/-- [ Phase changes and terminal moves also preserve all inactive coordinates.](goal) Under [the stated conditions](hyp:hi). -/
-- @node: phaseMove_inactive_fixed
lemma phaseMove_inactive_fixed (a : Fin (n / 4) → Fin n → ℝ)
    (st : RoundingState n) (seed₁ seed₂ : ℝ) (i : Fin n) (hi : ¬ |st.1 i| < 1) :
    (phaseMove a st seed₁ seed₂).1 i = st.1 i := by
  by_cases hsmall : (activeIndices st.1).length ≤ st.2.1 ∧
      (activeIndices st.1).length ≤ 3
  · simp only [phaseMove, if_pos hsmall]
    cases he : activeIndices st.1 with
    | nil => rfl
    | cons j js =>
      have hj : j ∈ activeIndices st.1 := by rw [he]; simp
      have hne : i ≠ j := by
        intro hij
        subst j
        exact hi ((mem_activeIndices st.1 i).mp hj)
      simp [Function.update_of_ne hne]
  · simpa only [phaseMove, if_neg hsmall] using
      roundingStep_inactive_fixed a _ st.1 seed₁ seed₂ i hi

/-- [ Once a coordinate is inactive, every later actual state retains it.](goal) Under [the stated conditions](hyp:hkl,hi). -/
-- @node: roundingIteration_inactive_fixed
lemma roundingIteration_inactive_fixed (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k l : ℕ) (hkl : k ≤ l) (i : Fin n)
    (hi : ¬ |(roundingIteration a seeds k).1 i| < 1) :
    (roundingIteration a seeds l).1 i = (roundingIteration a seeds k).1 i := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hkl
  clear hkl
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show k + (b + 1) = (k + b) + 1 by omega, roundingIteration]
    rw [phaseMove_inactive_fixed a _ _ _ i (by simpa only [ih] using hi), ih]

/-- [ Every actual interval can spend at most its initially active count in endpoint energy.](goal) Under [the stated conditions](hyp:hkl). -/
-- @node: roundingIteration_interval_endpoint_energy_le
lemma roundingIteration_interval_endpoint_energy_le
    (a : Fin (n / 4) → Fin n → ℝ) (seeds : RoundingSeeds n) (k l : ℕ) (hkl : k ≤ l) :
    rowDot (roundingIteration a seeds l).1 (roundingIteration a seeds l).1 -
      rowDot (roundingIteration a seeds k).1 (roundingIteration a seeds k).1 ≤
      (activeIndices (roundingIteration a seeds k).1).length := by
  exact active_endpoint_energy_le _ _ (roundingIteration_cube_and_count a seeds l).1
    (fun i hi => roundingIteration_inactive_fixed a seeds k l hkl i hi)

/-- [ A finite interval mask telescopes even when the interval is empty.](goal) Under [the stated conditions](hyp:hKH,hHm). -/
-- @node: finite_interval_increment_sum
lemma finite_interval_increment_sum (f : ℕ → ℝ) (m K H : ℕ)
    (hKH : K ≤ H) (hHm : H ≤ m) :
    (∑ k ∈ Finset.range m, if K ≤ k ∧ k < H then f (k + 1) - f k else 0) =
      f H - f K := by
  induction m generalizing K H with
  | zero =>
    have hH : H = 0 := by omega
    have hK : K = 0 := by omega
    simp [hH, hK]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    by_cases hH : H ≤ m
    · rw [ih K H hKH hH, if_neg (by omega)]
      simp
    · have he : H = m + 1 := by omega
      subst H
      by_cases hK : K ≤ m
      · have hs : (∑ k ∈ Finset.range m,
            if K ≤ k ∧ k < m + 1 then f (k + 1) - f k else 0) =
          ∑ k ∈ Finset.range m, if K ≤ k ∧ k < m then f (k + 1) - f k else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkm := Finset.mem_range.mp hk
          simp only [hkm, Nat.lt_succ_of_lt hkm, and_true]
        rw [hs, ih K m hK (by omega), if_pos (by omega)]
        ring
      · have he : K = m + 1 := by omega
        subst K
        have hs : (∑ k ∈ Finset.range m,
            if m + 1 ≤ k ∧ k < m + 1 then f (k + 1) - f k else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          rw [if_neg (by omega)]
        rw [hs, if_neg (by omega)]
        simp

/-- [ Summing the selected coordinate variances gives the selected norm-energy expenditure.](goal) Under [the stated conditions](hyp:hk,hE,hpast). -/
-- @node: roundingIteration_masked_norm_energy
lemma roundingIteration_masked_norm_energy
    (a : Fin (n / 4) → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (E : Set (RoundingSeeds n)) (hE : MeasurableSet E)
    (hpast : ∀ seeds t,
      Function.update seeds ⟨2 * k + 1, by omega⟩ t ∈ E ↔ seeds ∈ E) :
    (∑ i : Fin n, ∫ seeds, (E.indicator (fun seeds =>
      (roundingIteration a seeds (k + 1)).1 i - (roundingIteration a seeds k).1 i) seeds) ^ 2
      ∂roundingSeedLaw n) =
    ∫ seeds, E.indicator (fun seeds =>
      rowDot (roundingIteration a seeds (k + 1)).1 (roundingIteration a seeds (k + 1)).1 -
      rowDot (roundingIteration a seeds k).1 (roundingIteration a seeds k).1) seeds
      ∂roundingSeedLaw n := by
  classical
  simp_rw [roundingIteration_masked_coordinate_energy a k hk _ E hE hpast]
  have hi (i : Fin n) : Integrable (E.indicator (fun seeds =>
      (roundingIteration a seeds (k + 1)).1 i ^ 2 -
      (roundingIteration a seeds k).1 i ^ 2)) (roundingSeedLaw n) := by
    have hraw : Integrable (fun seeds =>
        (roundingIteration a seeds (k + 1)).1 i ^ 2 -
        (roundingIteration a seeds k).1 i ^ 2) (roundingSeedLaw n) := by
      convert (roundingIteration_coordinate_memLp a (k + 1) i).integrable_sq.sub
        (roundingIteration_coordinate_memLp a k i).integrable_sq using 1
      funext seeds
      exact (Pi.sub_apply
        (fun seeds : RoundingSeeds n => (roundingIteration a seeds (k + 1)).1 i ^ 2)
        (fun seeds : RoundingSeeds n => (roundingIteration a seeds k).1 i ^ 2) seeds).symm
    exact hraw.indicator hE
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [] with seeds
  by_cases hs : seeds ∈ E
  · simp only [Set.indicator_of_mem hs, rowDot, ← Finset.sum_sub_distrib, pow_two]
  · simp [Set.indicator_of_notMem hs]

/-- [ Predictable random intervals inherit the exact norm-energy telescope of actual states.](goal) Under [the stated conditions](hyp:hKH,hH,hE,hpast). -/
-- @node: roundingIteration_interval_variance_energy
lemma roundingIteration_interval_variance_energy
    (a : Fin (n / 4) → Fin n → ℝ) (K H : RoundingSeeds n → ℕ)
    (hKH : ∀ seeds, K seeds ≤ H seeds) (hH : ∀ seeds, H seeds ≤ n)
    (hE : ∀ k < n, MeasurableSet {seeds | K seeds ≤ k ∧ k < H seeds})
    (hpast : ∀ (k : ℕ) (hk : k < n), ∀ seeds t,
      (K (Function.update seeds ⟨2 * k + 1, by omega⟩ t) ≤ k ∧
        k < H (Function.update seeds ⟨2 * k + 1, by omega⟩ t)) ↔
      (K seeds ≤ k ∧ k < H seeds)) :
    (∑ k ∈ Finset.range n, ∑ i : Fin n, ∫ seeds,
      ({seeds | K seeds ≤ k ∧ k < H seeds}.indicator (fun seeds =>
        (roundingIteration a seeds (k + 1)).1 i - (roundingIteration a seeds k).1 i) seeds) ^ 2
      ∂roundingSeedLaw n) =
    ∫ seeds, rowDot (roundingIteration a seeds (H seeds)).1
        (roundingIteration a seeds (H seeds)).1 -
      rowDot (roundingIteration a seeds (K seeds)).1 (roundingIteration a seeds (K seeds)).1
      ∂roundingSeedLaw n := by
  classical
  have hi (k : ℕ) (hk : k < n) : Integrable
      ({seeds | K seeds ≤ k ∧ k < H seeds}.indicator (fun seeds =>
        rowDot (roundingIteration a seeds (k + 1)).1 (roundingIteration a seeds (k + 1)).1 -
        rowDot (roundingIteration a seeds k).1 (roundingIteration a seeds k).1))
      (roundingSeedLaw n) := by
    have hu (l : ℕ) : Integrable (fun seeds =>
        rowDot (roundingIteration a seeds l).1 (roundingIteration a seeds l).1)
        (roundingSeedLaw n) := by
      unfold rowDot
      apply integrable_finsetSum
      intro i _
      exact (roundingIteration_coordinate_memLp a l i).integrable_mul
        (roundingIteration_coordinate_memLp a l i)
    exact ((hu (k + 1)).sub (hu k)).indicator (hE k hk)
  calc
    _ = ∑ k ∈ Finset.range n, ∫ seeds,
        {seeds | K seeds ≤ k ∧ k < H seeds}.indicator (fun seeds =>
          rowDot (roundingIteration a seeds (k + 1)).1 (roundingIteration a seeds (k + 1)).1 -
          rowDot (roundingIteration a seeds k).1 (roundingIteration a seeds k).1) seeds
          ∂roundingSeedLaw n := by
      apply Finset.sum_congr rfl
      intro k hk
      exact roundingIteration_masked_norm_energy a k (Finset.mem_range.mp hk) _
        (hE k (Finset.mem_range.mp hk)) (hpast k (Finset.mem_range.mp hk))
    _ = ∫ seeds, ∑ k ∈ Finset.range n,
        {seeds | K seeds ≤ k ∧ k < H seeds}.indicator (fun seeds =>
          rowDot (roundingIteration a seeds (k + 1)).1 (roundingIteration a seeds (k + 1)).1 -
          rowDot (roundingIteration a seeds k).1 (roundingIteration a seeds k).1) seeds
          ∂roundingSeedLaw n := by
      rw [integral_finsetSum _ (fun k hk => hi k (Finset.mem_range.mp hk))]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with seeds
      simp only [Set.indicator, Set.mem_ofPred_eq]
      exact finite_interval_increment_sum
        (fun k => rowDot (roundingIteration a seeds k).1 (roundingIteration a seeds k).1)
        n (K seeds) (H seeds) (hKH seeds) (hH seeds)

/-- [ Evaluating an actual coordinate at any measurable integer time is Borel. This uses [the hK hypothesis](hyp:hK), [the stated conclusion](goal). -/
@[fun_prop]
-- @node: roundingIteration_random_time_coordinate_measurable
lemma roundingIteration_random_time_coordinate_measurable
    (a : Fin (n / 4) → Fin n → ℝ) (K : RoundingSeeds n → ℕ) (hK : Measurable K)
    (i : Fin n) : Measurable (fun seeds => (roundingIteration a seeds (K seeds)).1 i) := by
  have hm : Measurable (fun x : RoundingSeeds n × ℕ =>
      (roundingIteration a x.1 x.2).1 i) :=
    measurable_from_prod_countable_left (fun k => roundingIteration_coordinate_measurable a k i)
  exact hm.comp (measurable_id.prodMk hK)

/-- A measurable random endpoint still has square-integrable coordinates, by cube preservation.](goal) Under [the stated conditions](hyp:hK). This uses [the stated conclusion](goal). -/
-- @node: roundingIteration_random_time_coordinate_memLp
lemma roundingIteration_random_time_coordinate_memLp
    (a : Fin (n / 4) → Fin n → ℝ) (K : RoundingSeeds n → ℕ) (hK : Measurable K)
    (i : Fin n) : MemLp (fun seeds => (roundingIteration a seeds (K seeds)).1 i)
      2 (roundingSeedLaw n) := by
  have : IsFiniteMeasure (roundingSeedLaw n) := by
    unfold roundingSeedLaw cubeMeasure
    infer_instance
  apply MemLp.of_bound
    (roundingIteration_random_time_coordinate_measurable a K hK i).aestronglyMeasurable 1
  filter_upwards [] with seeds
  simpa only [Real.norm_eq_abs] using
    (roundingIteration_cube_and_count a seeds (K seeds)).1 i

/-- [ Random-endpoint norm energy is integrable; no stopping-time theorem is needed.](goal) Under [the stated conditions](hyp:hK). -/
-- @node: roundingIteration_random_time_energy_integrable
lemma roundingIteration_random_time_energy_integrable
    (a : Fin (n / 4) → Fin n → ℝ) (K : RoundingSeeds n → ℕ) (hK : Measurable K) :
    Integrable (fun seeds => rowDot (roundingIteration a seeds (K seeds)).1
      (roundingIteration a seeds (K seeds)).1) (roundingSeedLaw n) := by
  unfold rowDot
  apply integrable_finsetSum
  intro i _
  exact (roundingIteration_random_time_coordinate_memLp a K hK i).integrable_mul
    (roundingIteration_random_time_coordinate_memLp a K hK i)

/-- [ The initial active-count allowance at a measurable random phase start is integrable.](goal) Under [the stated conditions](hyp:hK). -/
-- @node: roundingIteration_random_time_active_count_integrable
lemma roundingIteration_random_time_active_count_integrable
    (a : Fin (n / 4) → Fin n → ℝ) (K : RoundingSeeds n → ℕ) (hK : Measurable K) :
    Integrable (fun seeds => ((activeIndices (roundingIteration a seeds (K seeds)).1).length : ℝ))
      (roundingSeedLaw n) := by
  have : IsFiniteMeasure (roundingSeedLaw n) := by
    unfold roundingSeedLaw cubeMeasure
    infer_instance
  have hu : Measurable (fun seeds => (roundingIteration a seeds (K seeds)).1) := by
    apply measurable_pi_lambda
    intro i
    exact roundingIteration_random_time_coordinate_measurable a K hK i
  have hc : Measurable (fun seeds =>
      ((activeIndices (roundingIteration a seeds (K seeds)).1).length : ℝ)) :=
    activeIndices_consumer_measurable _ hu (fun _ cs => (cs.length : ℝ))
      (fun _ => measurable_const)
  apply Integrable.of_bound hc.aestronglyMeasurable (n : ℝ)
  filter_upwards [] with seeds
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact_mod_cast (roundingIteration_cube_and_count a seeds (K seeds)).2.trans (Nat.sub_le _ _)

/-- [ The predictable random phase's total coordinate variance is bounded by its
expected initial active count. This is the conditional energy budget integrated
over the phase-start history, for the actual finite rounding iteration.](goal) Under [the stated conditions](hyp:hK,hH,hKH,hHn,hpast). -/
-- @node: roundingIteration_interval_coordinate_variance_le
lemma roundingIteration_interval_coordinate_variance_le
    (a : Fin (n / 4) → Fin n → ℝ) (K H : RoundingSeeds n → ℕ)
    (hK : Measurable K) (hH : Measurable H)
    (hKH : ∀ seeds, K seeds ≤ H seeds) (hHn : ∀ seeds, H seeds ≤ n)
    (hpast : ∀ (k : ℕ) (hk : k < n), ∀ seeds t,
      (K (Function.update seeds ⟨2 * k + 1, by omega⟩ t) ≤ k ∧
        k < H (Function.update seeds ⟨2 * k + 1, by omega⟩ t)) ↔
      (K seeds ≤ k ∧ k < H seeds)) :
    (∑ k ∈ Finset.range n, ∑ i : Fin n, ∫ seeds,
      ({seeds | K seeds ≤ k ∧ k < H seeds}.indicator (fun seeds =>
        (roundingIteration a seeds (k + 1)).1 i - (roundingIteration a seeds k).1 i) seeds) ^ 2
      ∂roundingSeedLaw n) ≤
    ∫ seeds, ((activeIndices (roundingIteration a seeds (K seeds)).1).length : ℝ)
      ∂roundingSeedLaw n := by
  have hE (k : ℕ) (_hk : k < n) :
      MeasurableSet {seeds | K seeds ≤ k ∧ k < H seeds} := by
    exact (measurableSet_le hK measurable_const).inter
      (measurableSet_lt measurable_const hH)
  rw [roundingIteration_interval_variance_energy a K H hKH hHn hE hpast]
  apply integral_mono
    ((roundingIteration_random_time_energy_integrable a H hH).sub
      (roundingIteration_random_time_energy_integrable a K hK))
    (roundingIteration_random_time_active_count_integrable a K hK)
  intro seeds
  exact roundingIteration_interval_endpoint_energy_le a seeds (K seeds) (H seeds) (hKH seeds)

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
