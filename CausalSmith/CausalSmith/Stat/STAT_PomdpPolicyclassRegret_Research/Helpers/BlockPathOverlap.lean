module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockCovariance
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockPathWeights

/-!
# Overlapping PHIW windows on generated paths

Chronological shifts retain the successor state at the start of a later window.
The product of two window weights is dominated by the ordinary ratio over their
union, with one factor of `L` for each shared action. Integrating the union ratio
proves roadmap equation (7), without independence of rewards and successors.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open scoped ENNReal NNReal
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- Evaluate a path functional after an unweighted chronological prefix. -/
-- @node: phiwPathShift
noncomputable def phiwPathShift {S : Type*}
    (f : S → List (Bool × ℝ × S) → ℝ) : Nat → S → List (Bool × ℝ × S) → ℝ
  | 0, s, path => f s path
  | r + 1, s, path =>
      let step := path.getD 0 (false, 0, s)
      phiwPathShift f r step.2.2 (path.drop 1)

/-- Shifting a measurable full-state path functional preserves measurability. For
[the index subset](hyp:S), [the f](hyp:f), [the f assumption](hyp:hf), and
[the reward symbol](hyp:r), this establishes
[the partial-history importance-weighted path shift measurability result](goal). -/
@[fun_prop]
-- @node: phiwPathShift_measurable
lemma phiwPathShift_measurable {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S]
    (f : S → List (Bool × ℝ × S) → ℝ)
    (hf : Measurable (fun p : S × List (Bool × ℝ × S) ↦ f p.1 p.2)) (r : Nat) :
    Measurable (fun p : S × List (Bool × ℝ × S) ↦ phiwPathShift f r p.1 p.2) := by
  induction r with
  | zero => exact hf
  | succ r ih =>
    apply measurable_from_prod_countable_right
    intro s
    have hg := segment_list_getD_measurable 0 (false, (0 : ℝ), s)
    exact ih.comp (hg.snd.snd.prodMk (segment_list_drop_measurable 1))

/-- A chronological shift preserves uniform pointwise order. For [the index subset](hyp:S),
[the f](hyp:f), [the g](hyp:g), [the fg assumption](hyp:hfg), [the reward symbol](hyp:r),
[the state](hyp:s), and [the path](hyp:path), this establishes
[the partial-history importance-weighted path shift mono result](goal). -/
-- @node: phiwPathShift_mono
lemma phiwPathShift_mono {S : Type*}
    (f g : S → List (Bool × ℝ × S) → ℝ) (hfg : ∀ s path, f s path ≤ g s path)
    (r : Nat) (s : S) (path : List (Bool × ℝ × S)) :
    phiwPathShift f r s path ≤ phiwPathShift g r s path := by
  induction r generalizing s path with
  | zero => exact hfg s path
  | succ r ih => exact ih (path.getD 0 (false, 0, s)).2.2 (path.drop 1)

/-- A chronological shift preserves the nonnegative bounded range of a score. For
[the index subset](hyp:S), [the f](hyp:f), [the second event](hyp:B),
[the f assumption](hyp:hf), [the reward symbol](hyp:r), [the state](hyp:s), and
[the path](hyp:path), this establishes
[the partial-history importance-weighted path shift bounds result](goal). -/
-- @node: phiwPathShift_bounds
lemma phiwPathShift_bounds {S : Type*}
    (f : S → List (Bool × ℝ × S) → ℝ) (B : ℝ)
    (hf : ∀ s path, 0 ≤ f s path ∧ f s path ≤ B)
    (r : Nat) (s : S) (path : List (Bool × ℝ × S)) :
    0 ≤ phiwPathShift f r s path ∧ phiwPathShift f r s path ≤ B := by
  induction r generalizing s path with
  | zero => exact hf s path
  | succ r ih => exact ih (path.getD 0 (false, 0, s)).2.2 (path.drop 1)

/-- Bounded measurable shifted scores are in every Lp space under a generated finite behavior
segment; the construction supplies integrability for free. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the f](hyp:f), [the f assumption](hyp:hf),
[the second event](hyp:B), [the second event assumption](hyp:hB), [the reward symbol](hyp:r),
[the sample size](hyp:n), [the state](hyp:s), and [the policy](hyp:p), this establishes
[the partial-history importance-weighted path shift membership lp result](goal). -/
-- @node: phiwPathShift_memLp
lemma phiwPathShift_memLp {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b)
    (f : JointState m.nX m.nH → List (Bool × ℝ × JointState m.nX m.nH) → ℝ)
    (hf : Measurable (fun p : JointState m.nX m.nH ×
      List (Bool × ℝ × JointState m.nX m.nH) ↦ f p.1 p.2))
    (B : ℝ) (hB : ∀ s path, 0 ≤ f s path ∧ f s path ≤ B)
    (r n : Nat) (s : JointState m.nX m.nH) (p : ℝ≥0∞) :
    MemLp (phiwPathShift f r s) p (segmentFrom m n s) := by
  have : IsProbabilityMeasure (segmentFrom m n s) := segmentFrom_isProbability m hb n s
  apply memLp_of_bounded (a := 0) (b := B)
  · exact Filter.Eventually.of_forall (phiwPathShift_bounds f B hB r s)
  · exact ((phiwPathShift_measurable f hf r).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable

/-- Normalization of a window ratio is unchanged by an unused future tail. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the sample size](hyp:n),
[the extra](hyp:extra), and [the state](hyp:s), this establishes
[the partial-history importance-weighted path weight integral one horizon result](goal). -/
-- @node: phiwPathWeight_integral_one_horizon
lemma phiwPathWeight_integral_one_horizon {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (n extra : Nat) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathWeight m j n s path ∂segmentFrom m (n + extra) s) = 1 := by
  induction n generalizing s with
  | zero =>
    have : IsProbabilityMeasure (segmentFrom m extra s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 extra s
    simp [phiwPathWeight]
  | succ n ih =>
    have : IsProbabilityMeasure (segmentFrom m ((n + extra) + 1) s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
    have hi := phiwPathShift_memLp m hClass.sequential_ignorability.1
      (phiwPathWeight m j (n + 1)) (phiwPathWeight_measurable m j (n + 1))
      (policyFactor zeta ^ (n + 1)) (phiwPathWeight_bounds t0 zeta C m hClass j (n + 1))
      0 ((n + extra) + 1) s 1
    change MemLp (phiwPathWeight m j (n + 1) s) 1
      (segmentFrom m ((n + extra) + 1) s) at hi
    rw [show n + 1 + extra = (n + extra) + 1 by omega,
      segmentFrom_integral_succ m hClass.sequential_ignorability.1 (n + extra) s _
        (hi.integrable le_rfl)]
    simp only [phiwPathWeight, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]
    simp_rw [integral_const_mul, ih, mul_one]
    exact phiw_segmentStep_ratio_mean_one t0 zeta C m hClass j s

/-- An unweighted prefix and an unused future tail do not affect normalization of the
chronological ratio in the intervening window. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the reward symbol](hyp:r),
[the sample size](hyp:n), [the extra](hyp:extra), and [the state](hyp:s), this establishes
[the partial-history importance-weighted path shift weight integral one result](goal). -/
-- @node: phiwPathShift_weight_integral_one
lemma phiwPathShift_weight_integral_one {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (r n extra : Nat) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathShift (phiwPathWeight m j n) r s path
      ∂segmentFrom m (r + (n + extra)) s) = 1 := by
  induction r generalizing s with
  | zero =>
    simpa only [phiwPathShift, Nat.zero_add] using
      phiwPathWeight_integral_one_horizon t0 zeta C m hClass j n extra s
  | succ r ih =>
    have : IsProbabilityMeasure (segmentFrom m ((r + (n + extra)) + 1) s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
    have hi := phiwPathShift_memLp m hClass.sequential_ignorability.1
      (phiwPathWeight m j n) (phiwPathWeight_measurable m j n)
      (policyFactor zeta ^ n) (phiwPathWeight_bounds t0 zeta C m hClass j n)
      (r + 1) ((r + (n + extra)) + 1) s 1
    rw [show r + 1 + (n + extra) = (r + (n + extra)) + 1 by omega,
      segmentFrom_integral_succ m hClass.sequential_ignorability.1 (r + (n + extra)) s _
        (hi.integrable le_rfl)]
    simp only [phiwPathShift, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]
    simp_rw [ih]
    have : IsProbabilityMeasure (segmentStepLaw m s) :=
      segmentStepLaw_isProbability m hClass.sequential_ignorability.1 s
    simp

/-- Every shifted weighted reward has mean at most one, for any full-state start, by domination
by its normalized ordinary window ratio. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the reward symbol](hyp:r),
[the history length](hyp:k), [the extra](hyp:extra), and [the state](hyp:s), this establishes
[the partial-history importance-weighted path shift reward integral bound one result](goal). -/
-- @node: phiwPathShift_reward_integral_le_one
lemma phiwPathShift_reward_integral_le_one {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (r k extra : Nat) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathShift (phiwPathReward m j k) r s path
      ∂segmentFrom m (r + ((k + 1) + extra)) s) ≤ 1 := by
  have : IsProbabilityMeasure (segmentFrom m (r + ((k + 1) + extra)) s) :=
    segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
  have hX := phiwPathShift_memLp m hClass.sequential_ignorability.1
    (phiwPathReward m j k) (phiwPathReward_measurable m j k)
    (policyFactor zeta ^ (k + 1)) (phiwPathReward_bounds t0 zeta C m hClass j k)
    r (r + ((k + 1) + extra)) s 1
  have hW := phiwPathShift_memLp m hClass.sequential_ignorability.1
    (phiwPathWeight m j (k + 1)) (phiwPathWeight_measurable m j (k + 1))
    (policyFactor zeta ^ (k + 1)) (phiwPathWeight_bounds t0 zeta C m hClass j (k + 1))
    r (r + ((k + 1) + extra)) s 1
  calc
    _ ≤ ∫ path, phiwPathShift (phiwPathWeight m j (k + 1)) r s path
        ∂segmentFrom m (r + ((k + 1) + extra)) s :=
      integral_mono (hX.integrable le_rfl) (hW.integrable le_rfl)
        (phiwPathShift_mono _ _ (phiwPathReward_le_pathWeight t0 zeta C m hClass j k) r s)
    _ = 1 := phiwPathShift_weight_integral_one t0 zeta C m hClass j r (k + 1) extra s

/-- Removing repeated ratios on the shared part leaves an ordinary ratio on the union of the two
windows, with one factor of `L` per shared step. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the sample size](hyp:n),
[the stated assumption](hyp:h), [the l](hyp:l), [the h assumption](hyp:hh), [the state](hyp:s),
and [the path](hyp:path), this establishes
[the partial-history importance-weighted path weight overlap pointwise result](goal). -/
-- @node: phiwPathWeight_overlap_pointwise
lemma phiwPathWeight_overlap_pointwise {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (n h l : Nat) (hh : h ≤ n) (s : JointState m.nX m.nH)
    (path : List (Bool × ℝ × JointState m.nX m.nH)) :
    phiwPathWeight m j n s path * phiwPathShift (phiwPathWeight m j l) h s path ≤
      policyFactor zeta ^ (n - h) * phiwPathWeight m j (h + l) s path := by
  induction h generalizing n s path with
  | zero =>
    simpa only [phiwPathShift, Nat.sub_zero, Nat.zero_add] using
      mul_le_mul_of_nonneg_right
      (phiwPathWeight_bounds t0 zeta C m hClass j n s path).2
      (phiwPathWeight_bounds t0 zeta C m hClass j l s path).1
  | succ h ih =>
    cases n with
    | zero => omega
    | succ n =>
      let step := path.getD 0 (false, (0 : ℝ), s)
      have hr := (ratio_mem hClass.sequential_ignorability.1 (hClass.action_overlap j).1
        (hClass.action_overlap j).2 (Real.exp_nonneg zeta) s.1 step.1).1
      change 0 ≤ ratio m.Mx.b (m.Mx.E j) s.1 step.1 at hr
      have ht := mul_le_mul_of_nonneg_left
        (ih n (by omega) step.2.2 (path.drop 1)) hr
      simpa only [phiwPathWeight, phiwPathShift, Nat.succ_sub_succ_eq_sub,
        Nat.succ_add, mul_assoc, mul_left_comm, step] using ht

/-- Weighted rewards are bounded by their two window weights before any integration; clipping
only enforces the kernel's unit-reward support. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the history length](hyp:k),
[the stated assumption](hyp:h), [the h assumption](hyp:hh), [the state](hyp:s), and
[the path](hyp:path), this establishes
[the partial-history importance-weighted path reward overlap pointwise result](goal). -/
-- @node: phiwPathReward_overlap_pointwise
lemma phiwPathReward_overlap_pointwise {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (k h : Nat) (hh : h ≤ k + 1) (s : JointState m.nX m.nH)
    (path : List (Bool × ℝ × JointState m.nX m.nH)) :
    phiwPathReward m j k s path * phiwPathShift (phiwPathReward m j k) h s path ≤
      policyFactor zeta ^ (k + 1 - h) * phiwPathWeight m j (h + (k + 1)) s path := by
  have hshift := phiwPathShift_mono (phiwPathReward m j k)
    (phiwPathWeight m j (k + 1))
    (phiwPathReward_le_pathWeight t0 zeta C m hClass j k) h s path
  have hnonneg := (phiwPathShift_bounds (phiwPathReward m j k)
    (policyFactor zeta ^ (k + 1)) (phiwPathReward_bounds t0 zeta C m hClass j k)
    h s path).1
  exact (mul_le_mul (phiwPathReward_le_pathWeight t0 zeta C m hClass j k s path)
    hshift hnonneg (phiwPathWeight_bounds t0 zeta C m hClass j (k + 1) s path).1).trans
      (phiwPathWeight_overlap_pointwise t0 zeta C m hClass j (k + 1) h (k + 1) hh s path)

/-- The overlapping-window cross moment satisfies roadmap equation (7) under the actual
generated behavior law, by normalization of the union ratio. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the history length](hyp:k),
[the stated assumption](hyp:h), [the h assumption](hyp:hh), and [the state](hyp:s), this
establishes
[the partial-history importance-weighted path reward overlap cross moment bound result](goal). -/
-- @node: phiwPathReward_overlap_cross_moment_le
lemma phiwPathReward_overlap_cross_moment_le {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (k h : Nat) (hh : h ≤ k + 1) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathReward m j k s path *
        phiwPathShift (phiwPathReward m j k) h s path
      ∂segmentFrom m (h + (k + 1)) s) ≤ policyFactor zeta ^ (k + 1 - h) := by
  have : IsProbabilityMeasure (segmentFrom m (h + (k + 1)) s) :=
    segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
  have hX := phiwPathReward_memLp t0 zeta C m hClass j k (h + (k + 1)) s 2
  have hY := phiwPathShift_memLp m hClass.sequential_ignorability.1
    (phiwPathReward m j k) (phiwPathReward_measurable m j k)
    (policyFactor zeta ^ (k + 1)) (phiwPathReward_bounds t0 zeta C m hClass j k)
    h (h + (k + 1)) s 2
  have hW := (phiwPathWeight_memLp t0 zeta C m hClass j (h + (k + 1)) s 1).integrable le_rfl
  calc
    _ ≤ ∫ path, policyFactor zeta ^ (k + 1 - h) *
        phiwPathWeight m j (h + (k + 1)) s path ∂segmentFrom m (h + (k + 1)) s :=
      integral_mono (hX.integrable_mul hY) (hW.const_mul _)
        (phiwPathReward_overlap_pointwise t0 zeta C m hClass j k h hh s)
    _ = policyFactor zeta ^ (k + 1 - h) := by
      rw [integral_const_mul, phiwPathWeight_integral_one t0 zeta C m hClass, mul_one]

/-- The overlapping-window covariance envelope in roadmap equation (8) holds on a generated
path. The proof uses the cross moment and normalization, rather than the much larger product of
the two supremum bounds. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the policy-overlap scale assumption](hyp:hzeta), [the candidate index](hyp:j),
[the history length](hyp:k), [the stated assumption](hyp:h), [the h assumption](hyp:hh), and
[the state](hyp:s), this establishes
[the partial-history importance-weighted path reward overlap covariance bound result](goal). -/
-- @node: phiwPathReward_overlap_covariance_le
lemma phiwPathReward_overlap_covariance_le {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (hzeta : 0 ≤ zeta)
    (j : Fin M) (k h : Nat) (hh : h ≤ k + 1) (s : JointState m.nX m.nH) :
    |ProbabilityTheory.covariance (phiwPathReward m j k s)
        (phiwPathShift (phiwPathReward m j k) h s)
        (segmentFrom m (h + (k + 1)) s)| ≤ policyFactor zeta ^ (k + 1 - h) := by
  have : IsProbabilityMeasure (segmentFrom m (h + (k + 1)) s) :=
    segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
  have hX := phiwPathReward_memLp t0 zeta C m hClass j k (h + (k + 1)) s 2
  have hY := phiwPathShift_memLp m hClass.sequential_ignorability.1
    (phiwPathReward m j k) (phiwPathReward_measurable m j k)
    (policyFactor zeta ^ (k + 1)) (phiwPathReward_bounds t0 zeta C m hClass j k)
    h (h + (k + 1)) s 2
  apply phiw_overlap_covariance_of_cross_moment _ _ _ hX hY
  · exact Filter.Eventually.of_forall fun path ↦
      (phiwPathReward_bounds t0 zeta C m hClass j k s path).1
  · exact Filter.Eventually.of_forall fun path ↦
      (phiwPathShift_bounds _ _ (phiwPathReward_bounds t0 zeta C m hClass j k) h s path).1
  · simpa only [phiwPathShift, Nat.zero_add, Nat.add_comm] using
      phiwPathShift_reward_integral_le_one t0 zeta C m hClass j 0 k h s
  · simpa only [Nat.add_zero] using
      phiwPathShift_reward_integral_le_one t0 zeta C m hClass j h k 0 s
  · exact Real.one_le_exp_iff.mpr hzeta
  · exact phiwPathReward_overlap_cross_moment_le t0 zeta C m hClass j k h hh s

end CausalSmith.Stat.PomdpPolicyclassRegret
