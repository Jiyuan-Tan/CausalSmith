module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingCrossingTimes

/-! # Row variance budgets for the actual rounding moves

The phase metadata keeps twice the retained count below the stopping count.
Thus each live move has a uniform row-to-energy comparison, including refreshes
and terminal single-coordinate moves.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
variable {n : ℕ}

/-- [ Phase refreshes preserve the stronger rank invariant needed for energy comparison.](goal) Under [the stated conditions](hyp:hq). -/
-- @node: phaseMove_twice_retained_le_stop
lemma phaseMove_twice_retained_le_stop (a : Fin (n / 4) → Fin n → ℝ)
    (st : RoundingState n) (seed₁ seed₂ : ℝ) (hq : 2 * st.2.2 ≤ st.2.1) :
    2 * (phaseMove a st seed₁ seed₂).2.2 ≤ (phaseMove a st seed₁ seed₂).2.1 := by
  dsimp only [phaseMove]
  split_ifs with hsmall hstart
  · cases activeIndices st.1 with
    | nil => exact hq
    | cons i is => simp
  · dsimp only
    omega
  · exact hq

/-- Every actual state carries the stronger retained-count invariant. [The asserted mathematical result follows](goal). -/
-- @node: roundingIteration_twice_retained_le_stop
lemma roundingIteration_twice_retained_le_stop (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k : ℕ) :
    2 * (roundingIteration a seeds k).2.2 ≤ (roundingIteration a seeds k).2.1 := by
  induction k with
  | zero => simp [roundingIteration]
  | succ k ih => exact phaseMove_twice_retained_le_stop a _ _ _ ih

/-- Any move retaining at most half the active count has a uniform row-to-energy bound. Under [the stated conditions](hyp:hc,hq), [the asserted mathematical result follows](goal). -/
-- @node: roundingStep_half_rank_variance_energy_le
lemma roundingStep_half_rank_variance_energy_le (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u c : Fin n → ℝ) (Λ : ℝ) (hc : ∀ i, |c i| ≤ Λ)
    (hq : 2 * q < (activeIndices u).length) :
    (∫ seed₁, ∫ seed₂, rowDot c (roundingStep a q u seed₁ seed₂ - u) ^ 2
      ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) ≤
      4 * Λ ^ 2 * (∫ seed₁, ∫ seed₂,
        rowDot (roundingStep a q u seed₁ seed₂) (roundingStep a q u seed₁ seed₂) - rowDot u u
        ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) := by
  have hne := nullspaceBasis_nonempty_of_active_count a q u (by omega)
  have hk : 0 < ((nullspaceBasis a q u).length : ℝ) := by
    exact_mod_cast List.length_pos_iff.mpr hne
  have hr := nullspaceBasis_rank_lower_bound a q u
  have ha : ((activeIndices u).length : ℝ) ≤ 4 * (nullspaceBasis a q u).length := by
    exact_mod_cast (show (activeIndices u).length ≤ 4 * (nullspaceBasis a q u).length by omega)
  have he : 0 ≤ (∫ seed₁, ∫ seed₂,
      rowDot (roundingStep a q u seed₁ seed₂) (roundingStep a q u seed₁ seed₂) - rowDot u u
      ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [roundingStep_lottery_energy_increment a q u hne]
    exact mul_nonneg (inv_nonneg.mpr
      (nullspaceBasis_boundary_weight_sum_pos a q u hne).le) hk.le
  have hb := roundingStep_row_variance_energy_le a q u c Λ hc hne
  have hm := mul_le_mul_of_nonneg_left ha (mul_nonneg (sq_nonneg Λ) he)
  nlinarith

/-- [ Actual metadata gives the row-to-energy comparison on every move, including
phase refreshes, terminal coins, and identity padding.](goal) Under [the stated conditions](hyp:hc,hu,hq). -/
-- @node: phaseMove_row_variance_energy_le
lemma phaseMove_row_variance_energy_le (a : Fin (n / 4) → Fin n → ℝ)
    (st : RoundingState n) (c : Fin n → ℝ) (Λ : ℝ)
    (hc : ∀ i, |c i| ≤ Λ) (hu : ∀ i, |st.1 i| ≤ 1)
    (hq : 2 * st.2.2 ≤ st.2.1) :
    (∫ seed₁, ∫ seed₂, rowDot c ((phaseMove a st seed₁ seed₂).1 - st.1) ^ 2
      ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) ≤
    4 * Λ ^ 2 * (∫ seed₁, ∫ seed₂,
      rowDot (phaseMove a st seed₁ seed₂).1 (phaseMove a st seed₁ seed₂).1 - rowDot st.1 st.1
      ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  by_cases hs : (activeIndices st.1).length ≤ st.2.1 ∧ (activeIndices st.1).length ≤ 3
  · cases he : activeIndices st.1 with
    | nil => simp [phaseMove, hs, he, rowDot]
    | cons i is =>
      have hs' : (i :: is).length ≤ st.2.1 ∧ (i :: is).length ≤ 3 := by
        simpa only [he] using hs
      simp only [phaseMove, he, if_pos hs']
      have hb := terminal_seed_row_variance_energy_le st.1 c i Λ (hu i) (hc i)
      have hnonneg : 0 ≤ 1 - st.1 i ^ 2 := by
        have hh := mul_self_le_mul_self (abs_nonneg (st.1 i)) (hu i)
        simp only [← pow_two, sq_abs, one_pow] at hh
        linarith
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      apply hb.trans
      rw [terminal_seed_energy_increment]
      nlinarith [mul_nonneg (sq_nonneg Λ) hnonneg]

  · simp only [phaseMove, if_neg hs]
    by_cases hstart : (activeIndices st.1).length ≤ st.2.1
    · simp only [if_pos hstart]
      apply roundingStep_half_rank_variance_energy_le a _ st.1 c Λ hc
      omega
    · simp only [if_neg hstart]
      apply roundingStep_half_rank_variance_energy_le a _ st.1 c Λ hc
      omega

/-- [ Averaging a fresh cube coordinate preserves measurability. This uses [the hf hypothesis](hyp:hf), [the stated conclusion](goal). -/
@[fun_prop]
-- @node: cube_coordinate_average_measurable
lemma cube_coordinate_average_measurable {m : ℕ} (j : Fin m)
    (f : Cube m → ℝ) (hf : Measurable f) :
    Measurable (fun x => ∫ t, f (Function.update x j t)
      ∂volume.restrict (Icc (0 : ℝ) 1)) := by
  have hm : Measurable (fun p : Cube m × ℝ => f (Function.update p.1 j p.2)) := by
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- A uniform bound survives averaging one independent cube coordinate.](goal) Under [the stated conditions](hyp:hC). This uses [the stated conclusion](goal). -/
-- @node: cube_coordinate_average_bound
lemma cube_coordinate_average_bound {m : ℕ} (j : Fin m)
    (f : Cube m → ℝ) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : Cube m) :
    ‖∫ t, f (Function.update x j t) ∂volume.restrict (Icc (0 : ℝ) 1)‖ ≤ C := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const
      (μ := volume.restrict (Icc (0 : ℝ) 1))
      (f := fun t => f (Function.update x j t))
      (Filter.Eventually.of_forall (fun t => hC _))

/-- [ Independent coordinate averaging preserves the full cube integral.](goal) Under [the stated conditions](hyp:hf,hC). -/
-- @node: cube_integral_coordinate_average
lemma cube_integral_coordinate_average {m : ℕ} (j : Fin m)
    (f : Cube m → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂cubeMeasure m) = ∫ x, ∫ t, f (Function.update x j t)
      ∂volume.restrict (Icc (0 : ℝ) 1) ∂cubeMeasure m := by
  have : IsFiniteMeasure (cubeMeasure m) := by unfold cubeMeasure; infer_instance
  apply cube_integral_eq_of_fresh_coordinate j
  · exact Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  · exact Integrable.of_bound (cube_coordinate_average_measurable j f hf).aestronglyMeasurable C
      (Filter.Eventually.of_forall (cube_coordinate_average_bound j f C hC))
  · intro x; rfl
  · intro x t
    simp only [Function.update_idem]

/-- [ A bounded two-fresh-coordinate comparison integrates over all preceding history.](goal) Under [the stated conditions](hyp:hf,hg,hC,hD,hle). -/
-- @node: cube_integral_le_of_two_fresh_coordinates
lemma cube_integral_le_of_two_fresh_coordinates {m : ℕ} (j l : Fin m)
    (f g : Cube m → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖g x‖ ≤ D)
    (hle : ∀ x,
      (∫ s, ∫ t, f (Function.update (Function.update x j s) l t)
        ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) ≤
      ∫ s, ∫ t, g (Function.update (Function.update x j s) l t)
        ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) :
    (∫ x, f x ∂cubeMeasure m) ≤ ∫ x, g x ∂cubeMeasure m := by
  have : IsFiniteMeasure (cubeMeasure m) := by unfold cubeMeasure; infer_instance
  rw [cube_integral_coordinate_average l f hf C hC,
    cube_integral_coordinate_average l g hg D hD]
  rw [cube_integral_coordinate_average j _ (cube_coordinate_average_measurable l f hf) C
      (cube_coordinate_average_bound l f C hC),
    cube_integral_coordinate_average j _ (cube_coordinate_average_measurable l g hg) D
      (cube_coordinate_average_bound l g D hD)]
  apply integral_mono
  · exact Integrable.of_bound
      (cube_coordinate_average_measurable j _ (cube_coordinate_average_measurable l f hf)).aestronglyMeasurable
      C (Filter.Eventually.of_forall
        (cube_coordinate_average_bound j _ C (cube_coordinate_average_bound l f C hC)))
  · exact Integrable.of_bound
      (cube_coordinate_average_measurable j _ (cube_coordinate_average_measurable l g hg)).aestronglyMeasurable
      D (Filter.Eventually.of_forall
        (cube_coordinate_average_bound j _ D (cube_coordinate_average_bound l g D hD)))
  · exact hle

/-- [ A cube-valued state has a uniformly bounded deterministic row evaluation.](goal) Under [the stated conditions](hyp:hu). -/
-- @node: rowDot_cube_abs_le
lemma rowDot_cube_abs_le (c u : Fin n → ℝ) (hu : ∀ i, |u i| ≤ 1) :
    |rowDot c u| ≤ ∑ i, |c i| := by
  unfold rowDot
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left (hu i) (abs_nonneg (c i))

/-- [ Cube-valued states have norm energy between zero and the ambient count.](goal) Under [the stated conditions](hyp:hu). -/
-- @node: rowDot_cube_energy_bounds
lemma rowDot_cube_energy_bounds (u : Fin n → ℝ) (hu : ∀ i, |u i| ≤ 1) :
    0 ≤ rowDot u u ∧ rowDot u u ≤ n := by
  refine ⟨Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i)), ?_⟩
  have hi (i : Fin n) : u i * u i ≤ 1 := by
    have hh := mul_self_le_mul_self (abs_nonneg (u i)) (hu i)
    simpa only [mul_one, ← pow_two, sq_abs, one_pow] using hh
  simpa only [rowDot, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)

/-- [ Averaging a predictably selected actual move compares its row variance with
its norm-energy expenditure, after integrating both fresh seeds.](goal) Under [the stated conditions](hyp:hc,hk,hE,hpast). -/
-- @node: roundingIteration_masked_row_variance_energy_le
lemma roundingIteration_masked_row_variance_energy_le
    (a : Fin (n / 4) → Fin n → ℝ) (c : Fin n → ℝ) (Λ : ℝ)
    (hc : ∀ i, |c i| ≤ Λ) (k : ℕ) (hk : k < n)
    (E : Set (RoundingSeeds n)) (hE : MeasurableSet E)
    (hpast : ∀ seeds (j : Fin (3 * n)) t, 2 * k ≤ j.val →
      (Function.update seeds j t ∈ E ↔ seeds ∈ E)) :
    (∫ seeds, (E.indicator (fun seeds =>
      rowDot c (roundingIteration a seeds (k + 1)).1 -
        rowDot c (roundingIteration a seeds k).1) seeds) ^ 2 ∂roundingSeedLaw n) ≤
    4 * Λ ^ 2 * (∫ seeds, E.indicator (fun seeds =>
      rowDot (roundingIteration a seeds (k + 1)).1 (roundingIteration a seeds (k + 1)).1 -
      rowDot (roundingIteration a seeds k).1 (roundingIteration a seeds k).1) seeds
      ∂roundingSeedLaw n) := by
  classical
  let f (seeds : RoundingSeeds n) := (E.indicator (fun seeds =>
    rowDot c (roundingIteration a seeds (k + 1)).1 -
      rowDot c (roundingIteration a seeds k).1) seeds) ^ 2
  let g (seeds : RoundingSeeds n) := 4 * Λ ^ 2 * E.indicator (fun seeds =>
    rowDot (roundingIteration a seeds (k + 1)).1 (roundingIteration a seeds (k + 1)).1 -
    rowDot (roundingIteration a seeds k).1 (roundingIteration a seeds k).1) seeds
  rw [← integral_const_mul]
  change (∫ seeds, f seeds ∂cubeMeasure (3 * n)) ≤ ∫ seeds, g seeds ∂cubeMeasure (3 * n)
  have hf : Measurable f := by
    apply Measurable.pow_const
    apply Measurable.indicator _ hE
    unfold rowDot
    fun_prop
  have hg : Measurable g := by
    apply Measurable.const_mul
    apply Measurable.indicator _ hE
    unfold rowDot
    fun_prop
  apply cube_integral_le_of_two_fresh_coordinates
    (⟨2 * k, by omega⟩ : Fin (3 * n)) ⟨2 * k + 1, by omega⟩ f g hf hg
    ((2 * ∑ i, |c i|) ^ 2) (|4 * Λ ^ 2| * (2 * n))
  · intro seeds
    have hb (l : ℕ) := rowDot_cube_abs_le c (roundingIteration a seeds l).1
      (roundingIteration_cube_and_count a seeds l).1
    have hd : |rowDot c (roundingIteration a seeds (k + 1)).1 -
        rowDot c (roundingIteration a seeds k).1| ≤ 2 * ∑ i, |c i| := by
      have hh := abs_sub_le (rowDot c (roundingIteration a seeds (k + 1)).1)
        0 (rowDot c (roundingIteration a seeds k).1)
      simp only [sub_zero, zero_sub, abs_neg] at hh
      linarith [hb (k + 1), hb k]
    by_cases hs : seeds ∈ E
    · simp only [f, Set.indicator_of_mem hs, Real.norm_eq_abs, abs_sq]
      simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg _) hd
    · simp [f, Set.indicator_of_notMem hs, sq_nonneg]
  · intro seeds
    have hb (l : ℕ) := rowDot_cube_energy_bounds (roundingIteration a seeds l).1
      (roundingIteration_cube_and_count a seeds l).1
    have hd : |rowDot (roundingIteration a seeds (k + 1)).1 (roundingIteration a seeds (k + 1)).1 -
        rowDot (roundingIteration a seeds k).1 (roundingIteration a seeds k).1| ≤ 2 * n := by
      apply abs_le.mpr
      constructor <;> linarith [hb (k + 1), hb k]
    by_cases hs : seeds ∈ E
    · simp only [g, Set.indicator_of_mem hs, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left hd (by positivity)
    · simp [g, Set.indicator_of_notMem hs]; positivity
  · intro seeds
    have hfirst : 2 * k < 3 * n := by omega
    have hsecond : 2 * k + 1 < 3 * n := by omega
    have hne : (⟨2 * k, hfirst⟩ : Fin (3 * n)) ≠ ⟨2 * k + 1, hsecond⟩ := by
      intro he; have hh := congrArg Fin.val he; dsimp at hh; omega
    have hprev (s t : ℝ) :
        roundingIteration a (Function.update (Function.update seeds ⟨2 * k, hfirst⟩ s)
          ⟨2 * k + 1, hsecond⟩ t) k = roundingIteration a seeds k := by
      rw [roundingIteration_update_future a _ k _ t (by dsimp; omega),
        roundingIteration_update_future a seeds k _ s (by dsimp; omega)]
    have hnext (s t : ℝ) :
        roundingIteration a (Function.update (Function.update seeds ⟨2 * k, hfirst⟩ s)
          ⟨2 * k + 1, hsecond⟩ t) (k + 1) =
        phaseMove a (roundingIteration a seeds k) s t := by
      simp only [roundingIteration, hprev, roundingSeed, dif_pos hfirst, dif_pos hsecond,
        Function.update_of_ne hne, Function.update_self]
    have hevent (s t : ℝ) :
        Function.update (Function.update seeds ⟨2 * k, hfirst⟩ s)
          ⟨2 * k + 1, hsecond⟩ t ∈ E ↔ seeds ∈ E := by
      rw [hpast _ _ t (by dsimp; omega), hpast _ _ s (by dsimp; omega)]
    by_cases hs : seeds ∈ E
    · simp only [f, g, Set.indicator, hevent, hs, if_true, hnext, hprev]
      simp_rw [show ∀ u v : Fin n → ℝ, rowDot c u - rowDot c v = rowDot c (u - v)
        from fun u v => (dotProduct_sub c u v).symm]
      simp_rw [integral_const_mul]
      exact phaseMove_row_variance_energy_le a (roundingIteration a seeds k) c Λ hc
        (roundingIteration_cube_and_count a seeds k).1
        (roundingIteration_twice_retained_le_stop a seeds k)
    · simp only [f, g, Set.indicator, hevent, hs, if_false, zero_pow (by decide : 2 ≠ 0),
        mul_zero, integral_zero, le_refl]

/-- [ The variance-to-energy comparison sums over any predictable family of move masks.](goal) Under [the stated conditions](hyp:hc,hE,hpast). -/
-- @node: roundingIteration_masked_row_variance_sum_le
lemma roundingIteration_masked_row_variance_sum_le
    (a : Fin (n / 4) → Fin n → ℝ) (c : Fin n → ℝ) (Λ : ℝ)
    (hc : ∀ i, |c i| ≤ Λ) (E : ℕ → Set (RoundingSeeds n))
    (hE : ∀ k < n, MeasurableSet (E k))
    (hpast : ∀ k < n, ∀ seeds (j : Fin (3 * n)) t, 2 * k ≤ j.val →
      (Function.update seeds j t ∈ E k ↔ seeds ∈ E k)) :
    (∑ k ∈ Finset.range n, ∫ seeds, ((E k).indicator (fun seeds =>
      rowDot c (roundingIteration a seeds (k + 1)).1 -
        rowDot c (roundingIteration a seeds k).1) seeds) ^ 2 ∂roundingSeedLaw n) ≤
    4 * Λ ^ 2 * (∑ k ∈ Finset.range n, ∑ i : Fin n, ∫ seeds,
      ((E k).indicator (fun seeds =>
        (roundingIteration a seeds (k + 1)).1 i - (roundingIteration a seeds k).1 i) seeds) ^ 2
      ∂roundingSeedLaw n) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkn := Finset.mem_range.mp hk
  rw [roundingIteration_masked_norm_energy a k hkn (E k) (hE k hkn)
    (fun seeds t => hpast k hkn seeds _ t (by dsimp; omega))]
  exact roundingIteration_masked_row_variance_energy_le a c Λ hc k hkn (E k) (hE k hkn)
    (hpast k hkn)

/-- [ Energy spent after the first loss of row protection is bounded by the active
count at that crossing, hence by four times the smaller of the row number and n.](goal) Under [the stated conditions](hyp:hh). -/
-- @node: roundingIteration_unprotected_coordinate_variance_sum_le
lemma roundingIteration_unprotected_coordinate_variance_sum_le
    (a : Fin (n / 4) → Fin n → ℝ) (h : ℕ) (hh : 1 ≤ h) :
    (∑ k ∈ Finset.range n, ∑ i : Fin n, ∫ seeds,
      ({seeds | (activeIndices (roundingIteration a seeds k).1).length < 4 * h}.indicator
        (fun seeds => (roundingIteration a seeds (k + 1)).1 i -
          (roundingIteration a seeds k).1 i) seeds) ^ 2 ∂roundingSeedLaw n) ≤
    4 * (min h n : ℕ) := by
  let K := roundingUnprotectedTime a h
  have hK : Measurable K := roundingUnprotectedTime_measurable a h
  have he (k : ℕ) (hk : k < n) :
      {seeds | K seeds ≤ k ∧ k < n} =
        {seeds | (activeIndices (roundingIteration a seeds k).1).length < 4 * h} := by
    ext seeds
    simp only [Set.mem_setOf_eq, hk, and_true, K, roundingUnprotectedTime_le_iff a h hh]
  have hb := roundingIteration_interval_coordinate_variance_le a K (fun _ => n) hK
    measurable_const (roundingUnprotectedTime_le_horizon a h) (fun _ => le_rfl)
    (roundingUnprotectedTime_interval_predictable a h hh)
  apply le_trans (b := ∫ seeds, ((activeIndices (roundingIteration a seeds (K seeds)).1).length : ℝ)
    ∂roundingSeedLaw n)
  · convert hb using 1 <;> try rfl
    apply Finset.sum_congr rfl
    intro k hk
    rw [he k (Finset.mem_range.mp hk)]
  · letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
      ⟨by simp [Real.volume_Icc]⟩
    letI : IsProbabilityMeasure (roundingSeedLaw n) := by
      unfold roundingSeedLaw cubeMeasure
      infer_instance
    have hcount (seeds : RoundingSeeds n) :
        ((activeIndices (roundingIteration a seeds (K seeds)).1).length : ℝ) ≤
          4 * (min h n : ℕ) := by
      have hs := roundingUnprotectedTime_active_bound a h hh seeds
      exact_mod_cast (show (activeIndices (roundingIteration a seeds (K seeds)).1).length ≤
        4 * min h n by dsimp only [K]; omega)
    calc
      _ ≤ ∫ _ : RoundingSeeds n, (4 * (min h n : ℕ) : ℝ) ∂roundingSeedLaw n :=
        integral_mono (roundingIteration_random_time_active_count_integrable a K hK)
          (integrable_const _) hcount
      _ = _ := by simp
/-- [ Actual rounding signs satisfy the paper's row bound by predictable move
orthogonality, the rank comparison, and the crossing-time energy telescope.](goal) Under [the stated conditions](hyp:hrows,hh). -/
-- @node: orderedBoundaryRounding_row_bound
lemma orderedBoundaryRounding_row_bound (rows : ℕ → Fin n → ℝ) (Λ : ℝ)
    (hrows : ∀ h i, 1 ≤ h → |rows h i| ≤ Λ) (h : ℕ) (hh : 1 ≤ h) :
    (∫ seeds, (∑ i, rows h i * sgn (orderedBoundaryRounding n (rowPrefix rows) seeds i)) ^ 2
      ∂roundingSeedLaw n) ≤ 32 * Λ ^ 2 * (min h n : ℕ) := by
  let E (k : ℕ) := {seeds | (activeIndices (roundingIteration (rowPrefix rows) seeds k).1).length < 4 * h}
  have hb := roundingIteration_masked_row_variance_sum_le (rowPrefix rows) (rows h) Λ
    (fun i => hrows h i hh) E
    (fun k _ => roundingIteration_unprotected_event_measurable (rowPrefix rows) k h)
    (fun k _ seeds j t hj => roundingIteration_unprotected_event_predictable
      (rowPrefix rows) k h j hj seeds t)
  have he := roundingIteration_unprotected_coordinate_variance_sum_le (rowPrefix rows) h hh
  have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4 * Λ ^ 2)
  rw [orderedBoundaryRounding_unprotected_second_moment_sum rows h hh]
  have hid (u v : Fin n → ℝ) : rowDot (rows h) u - rowDot (rows h) v =
      rowDot (rows h) (fun i => u i - v i) := (dotProduct_sub _ _ _).symm
  simp only [hid] at hb
  change _ ≤ 4 * Λ ^ 2 * _ at hb
  have hn' : (0 : ℝ) ≤ (min h n : ℕ) := by positivity
  nlinarith [mul_nonneg (sq_nonneg Λ) hn']

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
