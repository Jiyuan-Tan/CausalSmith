module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingPhaseTrace

/-! # Bounded crossing times of the actual rounding trace

The first active-count crossing after a measurable starting time is bounded by
n. Its interval mask depends only on the current history. In particular, the
first loss of row protection is a measurable, predictable crossing, with an
actual starting active count below 4h. Successive halving crossings give
measurable intervals ending at the terminal state and the pathwise 8 min(h,n)
active-count allowance. These intervals refine the move trace and need not
coincide with metadata refreshes.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
variable {n : ℕ}

/-- [ The terminal state supplies a crossing for every nonnegative active threshold.](goal) -/
-- @node: roundingIteration_crossing_exists
lemma roundingIteration_crossing_exists (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (K R : ℕ) :
    ∃ k, min K n ≤ k ∧ (activeIndices (roundingIteration a seeds k).1).length ≤ R := by
  refine ⟨n, Nat.min_le_right _ _, ?_⟩
  simp [roundingIteration_no_active]

/-- [ First active-count crossing after the clipped starting time, on the actual trace. -/
-- @node: roundingCrossingTime
def roundingCrossingTime (a : Fin (n / 4) → Fin n → ℝ)
    (K R : RoundingSeeds n → ℕ) (seeds : RoundingSeeds n) : ℕ :=
  Nat.find (roundingIteration_crossing_exists a seeds (K seeds) (R seeds))

/-- The crossing respects its starting time and attains the prescribed active bound. This uses [the stated conclusion](goal). -/
-- @node: roundingCrossingTime_spec
lemma roundingCrossingTime_spec (a : Fin (n / 4) → Fin n → ℝ)
    (K R : RoundingSeeds n → ℕ) (seeds : RoundingSeeds n) :
    min (K seeds) n ≤ roundingCrossingTime a K R seeds ∧
      (activeIndices (roundingIteration a seeds (roundingCrossingTime a K R seeds)).1).length ≤
        R seeds := Nat.find_spec (roundingIteration_crossing_exists a seeds (K seeds) (R seeds))

/-- Every crossing lies within the deterministic move horizon.](goal) This uses [the stated conclusion](goal). -/
-- @node: roundingCrossingTime_le_horizon
lemma roundingCrossingTime_le_horizon (a : Fin (n / 4) → Fin n → ℝ)
    (K R : RoundingSeeds n → ℕ) (seeds : RoundingSeeds n) :
    roundingCrossingTime a K R seeds ≤ n := by
  apply Nat.find_min'
  exact ⟨Nat.min_le_right _ _, by simp [roundingIteration_no_active]⟩

/-- [ By monotonicity, a crossing has not occurred exactly when the start is still
in the future or the current active count is above the threshold.](goal) -/
-- @node: roundingCrossingTime_before_iff
lemma roundingCrossingTime_before_iff (a : Fin (n / 4) → Fin n → ℝ)
    (K R : RoundingSeeds n → ℕ) (seeds : RoundingSeeds n) (k : ℕ) :
    k < roundingCrossingTime a K R seeds ↔
      k < min (K seeds) n ∨ R seeds < (activeIndices (roundingIteration a seeds k).1).length := by
  constructor
  · intro hk
    by_contra h
    have hstart : min (K seeds) n ≤ k := by omega
    have hcount : (activeIndices (roundingIteration a seeds k).1).length ≤ R seeds := by omega
    have he : roundingCrossingTime a K R seeds ≤ k := Nat.find_min' _ ⟨hstart, hcount⟩
    omega
  · intro h
    by_contra hk
    have he : roundingCrossingTime a K R seeds ≤ k := by omega
    have hs := roundingCrossingTime_spec a K R seeds
    have hm := roundingIteration_active_count_antitone a seeds he
    dsimp only at hm
    omega

/-- [ A crossing has occurred precisely when its start has occurred and the
current active count is at or below the threshold.](goal) -/
-- @node: roundingCrossingTime_le_iff
lemma roundingCrossingTime_le_iff (a : Fin (n / 4) → Fin n → ℝ)
    (K R : RoundingSeeds n → ℕ) (seeds : RoundingSeeds n) (k : ℕ) :
    roundingCrossingTime a K R seeds ≤ k ↔
      min (K seeds) n ≤ k ∧ (activeIndices (roundingIteration a seeds k).1).length ≤ R seeds := by
  have hh := roundingCrossingTime_before_iff a K R seeds k
  omega

/-- Measurable random starts and active thresholds give a measurable first crossing. This uses [the hK hypothesis](hyp:hK), [the hR hypothesis](hyp:hR), [the stated conclusion](goal). -/
@[fun_prop]
-- @node: roundingCrossingTime_measurable
lemma roundingCrossingTime_measurable (a : Fin (n / 4) → Fin n → ℝ)
    (K R : RoundingSeeds n → ℕ) (hK : Measurable K) (hR : Measurable R) :
    Measurable (roundingCrossingTime a K R) := by
  apply measurable_find
  intro k
  exact (measurableSet_le (hK.min measurable_const) measurable_const).inter
    (measurableSet_le (roundingIteration_active_count_measurable a k) hR)

/-- Inside the horizon, the crossing interval is decided by the current active
count and the event that the random start has occurred. Under [the stated conditions](hyp:hk), [the asserted mathematical result follows](goal). -/
-- @node: roundingCrossingTime_interval_iff
lemma roundingCrossingTime_interval_iff (a : Fin (n / 4) → Fin n → ℝ)
    (K R : RoundingSeeds n → ℕ) (seeds : RoundingSeeds n) (k : ℕ) (hk : k < n) :
    (K seeds ≤ k ∧ k < roundingCrossingTime a K R seeds) ↔
      (K seeds ≤ k ∧ R seeds < (activeIndices (roundingIteration a seeds k).1).length) := by
  rw [roundingCrossingTime_before_iff]
  omega

/-- [ Crossing intervals are predictable when their start event and threshold are
unchanged by the fresh coin. The end time itself need not be unchanged.](goal) Under [the stated conditions](hyp:hk,hK,hR). -/
-- @node: roundingCrossingTime_interval_predictable
lemma roundingCrossingTime_interval_predictable (a : Fin (n / 4) → Fin n → ℝ)
    (K R : RoundingSeeds n → ℕ) (k : ℕ) (hk : k < n)
    (hK : ∀ seeds t, K (Function.update seeds ⟨2 * k + 1, by omega⟩ t) ≤ k ↔ K seeds ≤ k)
    (hR : ∀ seeds t, R (Function.update seeds ⟨2 * k + 1, by omega⟩ t) = R seeds)
    (seeds : RoundingSeeds n) (t : ℝ) :
    (K (Function.update seeds ⟨2 * k + 1, by omega⟩ t) ≤ k ∧
      k < roundingCrossingTime a K R (Function.update seeds ⟨2 * k + 1, by omega⟩ t)) ↔
    (K seeds ≤ k ∧ k < roundingCrossingTime a K R seeds) := by
  rw [roundingCrossingTime_interval_iff a K R _ k hk,
    roundingCrossingTime_interval_iff a K R _ k hk, hK, hR,
    roundingIteration_update_future a seeds k _ t (by dsimp; omega)]

/-- The first unprotected move is the crossing of the integer threshold 4h-1. -/
-- @node: roundingUnprotectedTime
def roundingUnprotectedTime (a : Fin (n / 4) → Fin n → ℝ) (h : ℕ) :
    RoundingSeeds n → ℕ := roundingCrossingTime a (fun _ => 0) (fun _ => 4 * h - 1)

/-- The row's first unprotected time is Borel. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: roundingUnprotectedTime_measurable
lemma roundingUnprotectedTime_measurable (a : Fin (n / 4) → Fin n → ℝ) (h : ℕ) :
    Measurable (roundingUnprotectedTime a h) := by
  exact roundingCrossingTime_measurable a _ _ measurable_const measurable_const

/-- An unprotected-time crossing always occurs before or at the terminal state. [The asserted mathematical result follows](goal). -/
-- @node: roundingUnprotectedTime_le_horizon
lemma roundingUnprotectedTime_le_horizon (a : Fin (n / 4) → Fin n → ℝ)
    (h : ℕ) (seeds : RoundingSeeds n) : roundingUnprotectedTime a h seeds ≤ n :=
  roundingCrossingTime_le_horizon a _ _ seeds

/-- Loss of protection occurs exactly on the terminal interval starting at the crossing. Under [the stated conditions](hyp:hh), [the asserted mathematical result follows](goal). -/
-- @node: roundingUnprotectedTime_le_iff
lemma roundingUnprotectedTime_le_iff (a : Fin (n / 4) → Fin n → ℝ)
    (h : ℕ) (hh : 1 ≤ h) (seeds : RoundingSeeds n) (k : ℕ) :
    roundingUnprotectedTime a h seeds ≤ k ↔
      (activeIndices (roundingIteration a seeds k).1).length < 4 * h := by
  have he := roundingCrossingTime_before_iff a (fun _ => 0) (fun _ => 4 * h - 1) seeds k
  change k < roundingUnprotectedTime a h seeds ↔ _ at he
  simp only [min_def, Nat.zero_le, if_true, Nat.not_lt_zero, false_or] at he
  omega

/-- [ The crossing starts with fewer than 4h active coordinates and at most n.](goal) Under [the stated conditions](hyp:hh). -/
-- @node: roundingUnprotectedTime_active_bound
lemma roundingUnprotectedTime_active_bound (a : Fin (n / 4) → Fin n → ℝ)
    (h : ℕ) (hh : 1 ≤ h) (seeds : RoundingSeeds n) :
    (activeIndices
      (roundingIteration a seeds (roundingUnprotectedTime a h seeds)).1).length <
      4 * h ∧
    (activeIndices (roundingIteration a seeds (roundingUnprotectedTime a h seeds)).1).length ≤ n := by
  refine ⟨(roundingUnprotectedTime_le_iff a h hh seeds _).mp le_rfl, ?_⟩
  exact (roundingIteration_cube_and_count a seeds _).2.trans (Nat.sub_le _ _)

/-- [ Membership in the unprotected terminal interval is predictable before the next coin.](goal) Under [the stated conditions](hyp:hh,hk). -/
-- @node: roundingUnprotectedTime_interval_predictable
lemma roundingUnprotectedTime_interval_predictable (a : Fin (n / 4) → Fin n → ℝ)
    (h : ℕ) (hh : 1 ≤ h) (k : ℕ) (hk : k < n)
    (seeds : RoundingSeeds n) (t : ℝ) :
    (roundingUnprotectedTime a h (Function.update seeds ⟨2 * k + 1, by omega⟩ t) ≤ k ∧ k < n) ↔
      (roundingUnprotectedTime a h seeds ≤ k ∧ k < n) := by
  rw [roundingUnprotectedTime_le_iff a h hh, roundingUnprotectedTime_le_iff a h hh,
    roundingIteration_update_future a seeds k _ t (by dsimp; omega)]

/-- The active count at a measurable random time is measurable. This uses [the hK hypothesis](hyp:hK), [the stated conclusion](goal). -/
@[fun_prop]
-- @node: roundingIteration_random_time_active_count_measurable
lemma roundingIteration_random_time_active_count_measurable
    (a : Fin (n / 4) → Fin n → ℝ) (K : RoundingSeeds n → ℕ) (hK : Measurable K) :
    Measurable (fun seeds => (activeIndices (roundingIteration a seeds (K seeds)).1).length) := by
  have hu : Measurable (fun seeds => (roundingIteration a seeds (K seeds)).1) := by
    apply measurable_pi_lambda
    intro i
    exact roundingIteration_random_time_coordinate_measurable a K hK i
  exact activeIndices_consumer_measurable _ hu (fun _ cs => cs.length)
    (fun _ => measurable_const)

/-- Starting at a clipped time, repeatedly stop at the first halving of the
actual active count. Empty intervals pad the trace once every coordinate is fixed. -/
-- @node: roundingHalvingTimes
def roundingHalvingTimes (a : Fin (n / 4) → Fin n → ℝ)
    (K : RoundingSeeds n → ℕ) : ℕ → RoundingSeeds n → ℕ
  | 0 => fun seeds => min (K seeds) n
  | j + 1 => roundingCrossingTime a (roundingHalvingTimes a K j)
      (fun seeds => (activeIndices
        (roundingIteration a seeds (roundingHalvingTimes a K j seeds)).1).length / 2)

/-- Every realized halving endpoint lies within the finite move horizon. [The asserted mathematical result follows](goal). -/
-- @node: roundingHalvingTimes_le_horizon
lemma roundingHalvingTimes_le_horizon (a : Fin (n / 4) → Fin n → ℝ)
    (K : RoundingSeeds n → ℕ) (j : ℕ) (seeds : RoundingSeeds n) :
    roundingHalvingTimes a K j seeds ≤ n := by
  cases j with
  | zero => exact Nat.min_le_right _ _
  | succ j => exact roundingCrossingTime_le_horizon a _ _ seeds

/-- [ Successive realized halving intervals occur in chronological order.](goal) -/
-- @node: roundingHalvingTimes_step_le
lemma roundingHalvingTimes_step_le (a : Fin (n / 4) → Fin n → ℝ)
    (K : RoundingSeeds n → ℕ) (j : ℕ) (seeds : RoundingSeeds n) :
    roundingHalvingTimes a K j seeds ≤ roundingHalvingTimes a K (j + 1) seeds := by
  have hs := (roundingCrossingTime_spec a (roundingHalvingTimes a K j)
    (fun seeds => (activeIndices
      (roundingIteration a seeds (roundingHalvingTimes a K j seeds)).1).length / 2) seeds).1
  rw [roundingHalvingTimes]
  simpa only [min_eq_left (roundingHalvingTimes_le_horizon a K j seeds)] using hs

/-- [ The starting active counts of consecutive actual intervals at least halve.](goal) -/
-- @node: roundingHalvingTimes_active_halves
lemma roundingHalvingTimes_active_halves (a : Fin (n / 4) → Fin n → ℝ)
    (K : RoundingSeeds n → ℕ) (j : ℕ) (seeds : RoundingSeeds n) :
    2 * (activeIndices (roundingIteration a seeds (roundingHalvingTimes a K (j + 1) seeds)).1).length ≤
      (activeIndices (roundingIteration a seeds (roundingHalvingTimes a K j seeds)).1).length := by
  have hs := (roundingCrossingTime_spec a (roundingHalvingTimes a K j)
    (fun seeds => (activeIndices
      (roundingIteration a seeds (roundingHalvingTimes a K j seeds)).1).length / 2) seeds).2
  change (activeIndices (roundingIteration a seeds
    (roundingHalvingTimes a K (j + 1) seeds)).1).length ≤ _ at hs
  omega

/-- [ Each halving time is a measurable function of the original finite seed list. This uses [the hK hypothesis](hyp:hK), [the stated conclusion](goal). -/
@[fun_prop]
-- @node: roundingHalvingTimes_measurable
lemma roundingHalvingTimes_measurable (a : Fin (n / 4) → Fin n → ℝ)
    (K : RoundingSeeds n → ℕ) (hK : Measurable K) (j : ℕ) :
    Measurable (roundingHalvingTimes a K j) := by
  induction j with
  | zero => exact hK.min measurable_const
  | succ j ih =>
    apply roundingCrossingTime_measurable a _ _ ih
    exact (roundingIteration_random_time_active_count_measurable a _ ih).div_const 2

/-- After j halving intervals, at most n-j coordinates remain active.](goal) This uses [the stated conclusion](goal). -/
-- @node: roundingHalvingTimes_active_count_le
lemma roundingHalvingTimes_active_count_le (a : Fin (n / 4) → Fin n → ℝ)
    (K : RoundingSeeds n → ℕ) (j : ℕ) (seeds : RoundingSeeds n) :
    (activeIndices (roundingIteration a seeds (roundingHalvingTimes a K j seeds)).1).length ≤ n - j := by
  induction j with
  | zero =>
    exact (roundingIteration_cube_and_count a seeds _).2.trans (Nat.sub_le _ _)
  | succ j ih =>
    have hh := roundingHalvingTimes_active_halves a K j seeds
    omega

/-- [ Padding to n intervals includes every nonzero actual increment: the last
endpoint already has no active coordinates.](goal) -/
-- @node: roundingHalvingTimes_no_active
lemma roundingHalvingTimes_no_active (a : Fin (n / 4) → Fin n → ℝ)
    (K : RoundingSeeds n → ℕ) (seeds : RoundingSeeds n) :
    activeIndices (roundingIteration a seeds (roundingHalvingTimes a K n seeds)).1 = [] := by
  have hh := roundingHalvingTimes_active_count_le a K n seeds
  have hz : (activeIndices
      (roundingIteration a seeds (roundingHalvingTimes a K n seeds)).1).length = 0 := by omega
  simpa using hz

/-- [ The padded endpoint is the same actual state as the final output signing.](goal) -/
-- @node: roundingHalvingTimes_terminal_state
lemma roundingHalvingTimes_terminal_state (a : Fin (n / 4) → Fin n → ℝ)
    (K : RoundingSeeds n → ℕ) (seeds : RoundingSeeds n) :
    (roundingIteration a seeds (roundingHalvingTimes a K n seeds)).1 =
      (roundingIteration a seeds n).1 := by
  funext i
  symm
  apply roundingIteration_inactive_fixed a seeds _ n (roundingHalvingTimes_le_horizon a K n seeds) i
  intro hi
  have hm := (mem_activeIndices _ i).mpr hi
  rw [roundingHalvingTimes_no_active a K seeds] at hm
  simpa using hm

/-- Starting the realized intervals when a row loses protection gives the
paper's deterministic geometric active-count allowance on every seed realization. Under [the stated conditions](hyp:hh), [the asserted mathematical result follows](goal). -/
-- @node: roundingHalvingTimes_unprotected_count_sum_le
lemma roundingHalvingTimes_unprotected_count_sum_le
    (a : Fin (n / 4) → Fin n → ℝ) (h : ℕ) (hh : 1 ≤ h)
    (m : ℕ) (seeds : RoundingSeeds n) :
    (∑ j ∈ Finset.range m, (activeIndices (roundingIteration a seeds
      (roundingHalvingTimes a (roundingUnprotectedTime a h) j seeds)).1).length) ≤
      8 * min h n := by
  apply unprotected_phase_sum_le
    (fun j => (activeIndices (roundingIteration a seeds
      (roundingHalvingTimes a (roundingUnprotectedTime a h) j seeds)).1).length) m n h
  · intro j _
    exact roundingHalvingTimes_active_halves a _ j seeds
  · exact (roundingIteration_cube_and_count a seeds _).2.trans (Nat.sub_le _ _)
  · have he : roundingHalvingTimes a (roundingUnprotectedTime a h) 0 seeds =
        roundingUnprotectedTime a h seeds :=
      min_eq_left (roundingUnprotectedTime_le_horizon a h seeds)
    rw [he]
    exact (roundingUnprotectedTime_active_bound a h hh seeds).1

/-- [ Equal sublevel events up to k determine the same time clipped at k+1.](goal) Under [the stated conditions](hyp:h). -/
-- @node: nat_min_succ_eq_of_sublevels
lemma nat_min_succ_eq_of_sublevels (u v k : ℕ)
    (h : ∀ l ≤ k, u ≤ l ↔ v ≤ l) : min u (k + 1) = min v (k + 1) := by
  by_cases hu : u ≤ k
  · have hv := (h k le_rfl).mp hu
    have huv := (h u hu).mp le_rfl
    have hvu := (h v hv).mpr le_rfl
    omega
  · have hv : ¬v ≤ k := by simpa only [h k le_rfl] using hu
    omega

/-- [ The first unprotected time, clipped just after the current move, ignores
all seed coordinates that have not yet been read.](goal) Under [the stated conditions](hyp:hh,hidx). -/
-- @node: roundingUnprotectedTime_update_future_clipped
lemma roundingUnprotectedTime_update_future_clipped
    (a : Fin (n / 4) → Fin n → ℝ) (h : ℕ) (hh : 1 ≤ h) (k : ℕ)
    (idx : Fin (3 * n)) (hidx : 2 * k ≤ idx.val) (seeds : RoundingSeeds n) (t : ℝ) :
    min (roundingUnprotectedTime a h (Function.update seeds idx t)) (k + 1) =
      min (roundingUnprotectedTime a h seeds) (k + 1) := by
  apply nat_min_succ_eq_of_sublevels
  intro l hl
  rw [roundingUnprotectedTime_le_iff a h hh, roundingUnprotectedTime_le_iff a h hh,
    roundingIteration_update_future a seeds l idx t (by omega)]

/-- [ Realized halving endpoints are stopping times for the finite seed history:
only their part up to the current move can be observed before the fresh seeds.](goal) Under [the stated conditions](hyp:hh,hidx). -/
-- @node: roundingHalvingTimes_update_future_clipped
lemma roundingHalvingTimes_update_future_clipped
    (a : Fin (n / 4) → Fin n → ℝ) (h : ℕ) (hh : 1 ≤ h) (j k : ℕ)
    (idx : Fin (3 * n)) (hidx : 2 * k ≤ idx.val)
    (seeds : RoundingSeeds n) (t : ℝ) :
    min (roundingHalvingTimes a (roundingUnprotectedTime a h) j
      (Function.update seeds idx t)) (k + 1) =
    min (roundingHalvingTimes a (roundingUnprotectedTime a h) j seeds) (k + 1) := by
  induction j with
  | zero =>
    simp only [roundingHalvingTimes,
      min_eq_left (roundingUnprotectedTime_le_horizon a h _)]
    exact roundingUnprotectedTime_update_future_clipped a h hh k idx hidx seeds t
  | succ j ih =>
    apply nat_min_succ_eq_of_sublevels
    intro l hl
    simp only [roundingHalvingTimes, roundingCrossingTime_le_iff,
      min_eq_left (roundingHalvingTimes_le_horizon a _ j _)]
    have hstart :
        roundingHalvingTimes a (roundingUnprotectedTime a h) j
          (Function.update seeds idx t) ≤ l ↔
        roundingHalvingTimes a (roundingUnprotectedTime a h) j seeds ≤ l := by omega
    by_cases hs : roundingHalvingTimes a (roundingUnprotectedTime a h) j seeds ≤ l
    · have hs' := hstart.mpr hs
      have he : roundingHalvingTimes a (roundingUnprotectedTime a h) j
          (Function.update seeds idx t) =
          roundingHalvingTimes a (roundingUnprotectedTime a h) j seeds := by omega
      rw [he, roundingIteration_update_future a seeds l idx t (by omega),
        roundingIteration_update_future a seeds
          (roundingHalvingTimes a (roundingUnprotectedTime a h) j seeds) idx t (by omega)]
    · have hs' : ¬roundingHalvingTimes a (roundingUnprotectedTime a h) j
          (Function.update seeds idx t) ≤ l := by simpa only [hstart] using hs
      simp only [hs, hs', false_and]

/-- [ Each realized halving interval has a predictable move mask, including empty
intervals after the terminal state.](goal) Under [the stated conditions](hyp:hh,hidx). -/
-- @node: roundingHalvingTimes_interval_predictable
lemma roundingHalvingTimes_interval_predictable
    (a : Fin (n / 4) → Fin n → ℝ) (h : ℕ) (hh : 1 ≤ h) (j k : ℕ)
    (idx : Fin (3 * n)) (hidx : 2 * k ≤ idx.val)
    (seeds : RoundingSeeds n) (t : ℝ) :
    (roundingHalvingTimes a (roundingUnprotectedTime a h) j
        (Function.update seeds idx t) ≤ k ∧
      k < roundingHalvingTimes a (roundingUnprotectedTime a h) (j + 1)
        (Function.update seeds idx t)) ↔
    (roundingHalvingTimes a (roundingUnprotectedTime a h) j seeds ≤ k ∧
      k < roundingHalvingTimes a (roundingUnprotectedTime a h) (j + 1) seeds) := by
  have hstart := roundingHalvingTimes_update_future_clipped a h hh j k
    idx hidx seeds t
  have hend := roundingHalvingTimes_update_future_clipped a h hh (j + 1) k
    idx hidx seeds t
  omega

/-- [ The actual halving interval has the integrated coordinate-variance budget
of its realized starting active count, with no extra stopping-time premises.](goal) Under [the stated conditions](hyp:hh). -/
-- @node: roundingHalvingTimes_coordinate_variance_le
lemma roundingHalvingTimes_coordinate_variance_le
    (a : Fin (n / 4) → Fin n → ℝ) (h : ℕ) (hh : 1 ≤ h) (j : ℕ) :
    let T := roundingHalvingTimes a (roundingUnprotectedTime a h)
    (∑ k ∈ Finset.range n, ∑ i : Fin n, ∫ seeds,
      ({seeds | T j seeds ≤ k ∧ k < T (j + 1) seeds}.indicator (fun seeds =>
        (roundingIteration a seeds (k + 1)).1 i - (roundingIteration a seeds k).1 i) seeds) ^ 2
      ∂roundingSeedLaw n) ≤
    ∫ seeds, ((activeIndices (roundingIteration a seeds (T j seeds)).1).length : ℝ)
      ∂roundingSeedLaw n := by
  dsimp only
  apply roundingIteration_interval_coordinate_variance_le
  · exact roundingHalvingTimes_measurable a _ (roundingUnprotectedTime_measurable a h) j
  · exact roundingHalvingTimes_measurable a _ (roundingUnprotectedTime_measurable a h) (j + 1)
  · exact roundingHalvingTimes_step_le a _ j
  · exact roundingHalvingTimes_le_horizon a _ (j + 1)
  · intro k hk seeds t
    exact roundingHalvingTimes_interval_predictable a h hh j k
      ⟨2 * k + 1, by omega⟩ (by dsimp; omega) seeds t

/-- [ The realized interval row increment has exactly the sum of its move second
moments. This combines the crossing-time mask with the actual martingale telescope.](goal) Under [the stated conditions](hyp:hh). -/
-- @node: roundingHalvingTimes_row_second_moment_sum
lemma roundingHalvingTimes_row_second_moment_sum
    (a : Fin (n / 4) → Fin n → ℝ) (h : ℕ) (hh : 1 ≤ h) (j : ℕ) (c : Fin n → ℝ) :
    let T := roundingHalvingTimes a (roundingUnprotectedTime a h)
    (∫ seeds, (rowDot c (roundingIteration a seeds (T (j + 1) seeds)).1 -
        rowDot c (roundingIteration a seeds (T j seeds)).1) ^ 2 ∂roundingSeedLaw n) =
    ∑ k ∈ Finset.range n, ∫ seeds,
      ({seeds | T j seeds ≤ k ∧ k < T (j + 1) seeds}.indicator (fun seeds =>
        rowDot c (roundingIteration a seeds (k + 1)).1 -
          rowDot c (roundingIteration a seeds k).1) seeds) ^ 2 ∂roundingSeedLaw n := by
  classical
  let T := roundingHalvingTimes a (roundingUnprotectedTime a h)
  have hm (l : ℕ) : Measurable (T l) :=
    roundingHalvingTimes_measurable a _ (roundingUnprotectedTime_measurable a h) l
  have he (k : ℕ) : MeasurableSet {seeds | T j seeds ≤ k ∧ k < T (j + 1) seeds} :=
    (measurableSet_le (hm j) measurable_const).inter
      (measurableSet_lt measurable_const (hm (j + 1)))
  have hs := roundingIteration_masked_row_second_moment_sum a c
    (fun k => {seeds | T j seeds ≤ k ∧ k < T (j + 1) seeds}) n le_rfl
    (fun k _ => he k) (fun k _ seeds idx t hidx =>
      roundingHalvingTimes_interval_predictable a h hh j k idx hidx seeds t)
  have ht (seeds : RoundingSeeds n) :
      (∑ k ∈ Finset.range n,
        ({seeds | T j seeds ≤ k ∧ k < T (j + 1) seeds}.indicator (fun seeds =>
          rowDot c (roundingIteration a seeds (k + 1)).1 -
            rowDot c (roundingIteration a seeds k).1) seeds)) =
        rowDot c (roundingIteration a seeds (T (j + 1) seeds)).1 -
          rowDot c (roundingIteration a seeds (T j seeds)).1 := by
    simp only [Set.indicator, Set.mem_setOf_eq]
    exact finite_interval_increment_sum
      (fun k => rowDot c (roundingIteration a seeds k).1) n _ _
      (roundingHalvingTimes_step_le a _ j seeds)
      (roundingHalvingTimes_le_horizon a _ (j + 1) seeds)
  simpa only [ht] using hs

/-- [ Integrating the realized geometric count allowance preserves the paper's
8 min(h,n) budget; each random count is bounded and measurable.](goal) Under [the stated conditions](hyp:hh). -/
-- @node: roundingHalvingTimes_unprotected_expected_count_sum_le
lemma roundingHalvingTimes_unprotected_expected_count_sum_le
    (a : Fin (n / 4) → Fin n → ℝ) (h : ℕ) (hh : 1 ≤ h) (m : ℕ) :
    (∑ j ∈ Finset.range m, ∫ seeds,
      ((activeIndices (roundingIteration a seeds
        (roundingHalvingTimes a (roundingUnprotectedTime a h) j seeds)).1).length : ℝ)
      ∂roundingSeedLaw n) ≤ 8 * (min h n : ℕ) := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  have : IsProbabilityMeasure (roundingSeedLaw n) := by
    unfold roundingSeedLaw cubeMeasure
    infer_instance
  have hi (j : ℕ) := roundingIteration_random_time_active_count_integrable a
    (roundingHalvingTimes a (roundingUnprotectedTime a h) j)
    (roundingHalvingTimes_measurable a _ (roundingUnprotectedTime_measurable a h) j)
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  calc
    _ ≤ ∫ _ : RoundingSeeds n, (8 * (min h n : ℕ) : ℝ) ∂roundingSeedLaw n := by
      apply integral_mono (integrable_finsetSum _ (fun j _ => hi j)) (integrable_const _)
      intro seeds
      change (∑ j ∈ Finset.range m,
        ((activeIndices (roundingIteration a seeds
          (roundingHalvingTimes a (roundingUnprotectedTime a h) j seeds)).1).length : ℝ)) ≤
        8 * (min h n : ℕ)
      exact_mod_cast roundingHalvingTimes_unprotected_count_sum_le a h hh m seeds
    _ = _ := by simp

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
