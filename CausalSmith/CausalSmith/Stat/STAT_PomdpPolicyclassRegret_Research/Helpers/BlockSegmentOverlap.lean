module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockSegmentMoments

/-!
# Observable PHIW overlapping-window moments

Chronological domination by the normalized union ratio transfers the sharp
cross-moment bound to arbitrary-start observable segments. Nonnegative means
at most one then give the covariance bound, including the diagonal.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators ENNReal

/-- A chronological prefix commutes with pointwise multiplication. For
[the index subset](hyp:S), [the f](hyp:f), [the g](hyp:g), [the reward symbol](hyp:r),
[the state](hyp:s), and [the path](hyp:path), this establishes
[the partial-history importance-weighted path shift mul result](goal). -/
-- @node: phiwPathShift_mul
lemma phiwPathShift_mul {S : Type*}
    (f g : S → List (Bool × ℝ × S) → ℝ) (r : Nat) (s : S)
    (path : List (Bool × ℝ × S)) :
    phiwPathShift (fun u p ↦ f u p * g u p) r s path =
      phiwPathShift f r s path * phiwPathShift g r s path := by
  induction r generalizing s path with
  | zero => rfl
  | succ r ih => exact ih _ _

/-- A constant is unaffected by a chronological prefix. For [the index subset](hyp:S),
[the c](hyp:c), [the reward symbol](hyp:r), [the state](hyp:s), and [the path](hyp:path), this
establishes [the partial-history importance-weighted path shift const result](goal). -/
-- @node: phiwPathShift_const
lemma phiwPathShift_const {S : Type*} (c : ℝ) (r : Nat) (s : S)
    (path : List (Bool × ℝ × S)) :
    phiwPathShift (fun _ _ ↦ c) r s path = c := by
  induction r generalizing s path with
  | zero => rfl
  | succ r ih => exact ih _ _

/-- Successive chronological prefixes add their lengths. For [the index subset](hyp:S),
[the f](hyp:f), [the reward symbol](hyp:r), [the stated assumption](hyp:h), [the state](hyp:s),
and [the path](hyp:path), this establishes
[the partial-history importance-weighted path shift add result](goal). -/
-- @node: phiwPathShift_add
lemma phiwPathShift_add {S : Type*}
    (f : S → List (Bool × ℝ × S) → ℝ) (r h : Nat) (s : S)
    (path : List (Bool × ℝ × S)) :
    phiwPathShift (phiwPathShift f h) r s path = phiwPathShift f (r + h) s path := by
  induction r generalizing s path with
  | zero => simp only [phiwPathShift, Nat.zero_add]
  | succ r ih =>
    simpa only [Nat.succ_add, phiwPathShift] using
      ih (path.getD 0 (false, 0, s)).2.2 (path.drop 1)

/-- Equation (7) allows both an unweighted prefix and an unused future suffix. The union ratio
still integrates to one. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), [the reward symbol](hyp:r), [the history length](hyp:k),
[the stated assumption](hyp:h), [the extra](hyp:extra), [the h assumption](hyp:hh), and
[the state](hyp:s), this establishes
[the partial-history importance-weighted path shift overlap cross moment horizon result](goal). -/
-- @node: phiwPathShift_overlap_cross_moment_horizon
lemma phiwPathShift_overlap_cross_moment_horizon {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (r k h extra : Nat) (hh : h ≤ k + 1) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathShift (phiwPathReward m j k) r s path *
      phiwPathShift (phiwPathReward m j k) (r + h) s path
      ∂segmentFrom m (r + ((h + (k + 1)) + extra)) s) ≤
      policyFactor zeta ^ (k + 1 - h) := by
  let n := r + ((h + (k + 1)) + extra)
  have : IsProbabilityMeasure (segmentFrom m n s) :=
    segmentFrom_isProbability m hClass.sequential_ignorability.1 n s
  have hX := phiwPathShift_memLp m hClass.sequential_ignorability.1
    (phiwPathReward m j k) (phiwPathReward_measurable m j k)
    _ (phiwPathReward_bounds t0 zeta C m hClass j k) r n s 2
  have hY := phiwPathShift_memLp m hClass.sequential_ignorability.1
    (phiwPathReward m j k) (phiwPathReward_measurable m j k)
    _ (phiwPathReward_bounds t0 zeta C m hClass j k) (r + h) n s 2
  have hW := phiwPathShift_memLp m hClass.sequential_ignorability.1
    (phiwPathWeight m j (h + (k + 1))) (phiwPathWeight_measurable m j _)
    _ (phiwPathWeight_bounds t0 zeta C m hClass j _) r n s 1
  calc
    _ ≤ ∫ path, policyFactor zeta ^ (k + 1 - h) *
        phiwPathShift (phiwPathWeight m j (h + (k + 1))) r s path
        ∂segmentFrom m n s := by
      apply integral_mono (hX.integrable_mul hY) ((hW.integrable le_rfl).const_mul _)
      intro path
      have hp := phiwPathShift_mono _ _
        (phiwPathReward_overlap_pointwise t0 zeta C m hClass j k h hh) r s path
      simpa only [phiwPathShift_mul, phiwPathShift_add, phiwPathShift_const,
        Pi.mul_apply] using hp
    _ = _ := by
      rw [integral_const_mul, phiwPathShift_weight_integral_one t0 zeta C m hClass, mul_one]

/-- A supported observable window is nonnegative, also after mixing starts. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the sample size](hyp:n),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), [the initial distribution](hyp:nu), [the reward symbol](hyp:r),
[the history length](hyp:k), and [the epoch index assumption](hyp:ht), this establishes
[the partial-history importance-weighted score observed segment nonnegativity result](goal). -/
-- @node: phiwScore_observedSegment_nonneg
lemma phiwScore_observedSegment_nonneg {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (r k : Nat) (ht : r + k < n) :
    ∀ᵐ w ∂((segmentLaw m hClass.finite_state nu n).map obsProj),
      0 ≤ phiwScore k m.Mx.b (m.Mx.E j) w ⟨r + k, ht⟩ := by
  rw [observedSegmentLaw_eq_sum_fixed_start, ae_finsetSum_measure_iff]
  intro s _
  apply Measure.ae_smul_measure
  apply (ae_map_iff (by fun_prop)
    ((phiwScore_measurable k m.Mx.b (m.Mx.E j) _) measurableSet_Ici)).2
  filter_upwards [phiwScore_decodeSegment_ae_eq_path_reward m
    hClass.sequential_ignorability.1 j _ s r k ht] with path hp
  rw [hp]
  exact (phiwPathShift_bounds _ _ (phiwPathReward_bounds t0 zeta C m hClass j k)
    r s path).1

/-- The mean of an observable window is at most one by chronological ratio normalization, rather
than its much larger pointwise envelope. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the reward symbol](hyp:r), [the history length](hyp:k), and
[the epoch index assumption](hyp:ht), this establishes
[the partial-history importance-weighted score observed segment mean bound one result](goal). -/
-- @node: phiwScore_observedSegment_mean_le_one
lemma phiwScore_observedSegment_mean_le_one {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (r k : Nat) (ht : r + k < n) :
    (∫ w, phiwScore k m.Mx.b (m.Mx.E j) w ⟨r + k, ht⟩
      ∂((segmentLaw m hClass.finite_state nu n).map obsProj)) ≤ 1 := by
  have hi : ∀ s, Integrable (fun path ↦ phiwScore k m.Mx.b (m.Mx.E j)
      (obsProj (decodeSegment (n := n)
        (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, path)))
      ⟨r + k, ht⟩) (segmentFrom m n s) := by
    intro s
    have : IsProbabilityMeasure (segmentFrom m n s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 n s
    exact (phiwScore_decodeSegment_memLp t0 zeta C m hClass j _ s r k ht 1).integrable le_rfl
  rw [observedSegment_integral_eq_sum_fixed_start m hClass.finite_state nu hnu _
    (phiwScore_measurable _ _ _ _) hi]
  calc
    _ ≤ ∑ s, nu s * 1 := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (hnu.1 s)
      rw [integral_congr_ae (phiwScore_decodeSegment_ae_eq_path_reward m
        hClass.sequential_ignorability.1 j _ s r k ht)]
      obtain ⟨extra, hn⟩ : ∃ extra, n = r + ((k + 1) + extra) :=
        ⟨n - (r + k + 1), by omega⟩
      subst n
      exact phiwPathShift_reward_integral_le_one t0 zeta C m hClass j r k extra s
    _ = 1 := by simpa only [mul_one] using hnu.2

/-- The sharp overlapping cross moment holds under the actual observable law with an arbitrary
initial distribution. Mixing is applied to cross moments. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the reward symbol](hyp:r), [the history length](hyp:k), [the stated assumption](hyp:h),
[the h assumption](hyp:hh), and [the epoch index assumption](hyp:ht), this establishes
[the partial-history importance-weighted score observed segment overlap cross moment result](goal). -/
-- @node: phiwScore_observedSegment_overlap_cross_moment
lemma phiwScore_observedSegment_overlap_cross_moment {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (r k h : Nat) (hh : h ≤ k + 1) (ht : r + h + k < n) :
    (∫ w, phiwScore k m.Mx.b (m.Mx.E j) w ⟨r + k, by omega⟩ *
      phiwScore k m.Mx.b (m.Mx.E j) w ⟨r + h + k, ht⟩
      ∂((segmentLaw m hClass.finite_state nu n).map obsProj)) ≤
      policyFactor zeta ^ (k + 1 - h) := by
  have hi : ∀ s, Integrable (fun path ↦
      phiwScore k m.Mx.b (m.Mx.E j)
        (obsProj (decodeSegment (n := n)
          (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, path)))
        ⟨r + k, by omega⟩ *
      phiwScore k m.Mx.b (m.Mx.E j)
        (obsProj (decodeSegment (n := n)
          (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, path)))
        ⟨r + h + k, ht⟩) (segmentFrom m n s) := by
    intro s
    exact (phiwScore_decodeSegment_memLp t0 zeta C m hClass j _ s r k
      (by omega) 2).integrable_mul
        (phiwScore_decodeSegment_memLp t0 zeta C m hClass j _ s (r + h) k ht 2)
  rw [observedSegment_integral_eq_sum_fixed_start m hClass.finite_state nu hnu _
    (by fun_prop) hi]
  calc
    _ ≤ ∑ s, nu s * policyFactor zeta ^ (k + 1 - h) := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (hnu.1 s)
      have heq : (fun path ↦
          phiwScore k m.Mx.b (m.Mx.E j)
            (obsProj (decodeSegment (n := n)
              (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, path)))
            ⟨r + k, by omega⟩ *
          phiwScore k m.Mx.b (m.Mx.E j)
            (obsProj (decodeSegment (n := n)
              (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, path)))
            ⟨r + h + k, ht⟩) =ᵐ[segmentFrom m n s]
          (fun path ↦ phiwPathShift (phiwPathReward m j k) r s path *
            phiwPathShift (phiwPathReward m j k) (r + h) s path) := by
        filter_upwards [phiwScore_decodeSegment_ae_eq_path_reward m
          hClass.sequential_ignorability.1 j _ s r k (by omega),
          phiwScore_decodeSegment_ae_eq_path_reward m
          hClass.sequential_ignorability.1 j _ s (r + h) k ht] with path hx hy
        rw [hx, hy]
      rw [integral_congr_ae heq]
      obtain ⟨extra, hn⟩ : ∃ extra, n = r + ((h + (k + 1)) + extra) :=
        ⟨n - (r + h + k + 1), by omega⟩
      subst n
      exact phiwPathShift_overlap_cross_moment_horizon t0 zeta C m hClass j r k h extra hh s
    _ = policyFactor zeta ^ (k + 1 - h) := by
      rw [← Finset.sum_mul, hnu.2, one_mul]

/-- Equation (8) for observable windows, including a zero lag for the diagonal. Nonnegative
means at most one convert the cross-moment envelope to covariance. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the sample size](hyp:n),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the policy-overlap scale assumption](hyp:hzeta), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the reward symbol](hyp:r), [the history length](hyp:k), [the stated assumption](hyp:h),
[the h assumption](hyp:hh), and [the epoch index assumption](hyp:ht), this establishes
[the partial-history importance-weighted score observed segment overlap covariance result](goal). -/
-- @node: phiwScore_observedSegment_overlap_covariance
lemma phiwScore_observedSegment_overlap_covariance {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (hzeta : 0 ≤ zeta)
    (j : Fin M) (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (r k h : Nat) (hh : h ≤ k + 1) (ht : r + h + k < n) :
    |covariance (fun w ↦ phiwScore k m.Mx.b (m.Mx.E j) w ⟨r + k, by omega⟩)
      (fun w ↦ phiwScore k m.Mx.b (m.Mx.E j) w ⟨r + h + k, ht⟩)
      ((segmentLaw m hClass.finite_state nu n).map obsProj)| ≤
      policyFactor zeta ^ (k + 1 - h) := by
  have : IsProbabilityMeasure ((segmentLaw m hClass.finite_state nu n).map obsProj) :=
    observedSegmentLaw_isProbability m hClass.sequential_ignorability.1
      hClass.finite_state nu hnu n
  exact phiw_overlap_covariance_of_cross_moment _ _ _
    (phiwScore_observedSegment_memLp t0 zeta C m hClass j nu hnu r k (by omega) 2)
    (phiwScore_observedSegment_memLp t0 zeta C m hClass j nu hnu (r + h) k ht 2)
    (phiwScore_observedSegment_nonneg t0 zeta C m hClass j nu r k (by omega))
    (phiwScore_observedSegment_nonneg t0 zeta C m hClass j nu (r + h) k ht)
    (phiwScore_observedSegment_mean_le_one t0 zeta C m hClass j nu hnu r k (by omega))
    (phiwScore_observedSegment_mean_le_one t0 zeta C m hClass j nu hnu (r + h) k ht)
    _ (Real.one_le_exp_iff.mpr hzeta) k h
    (phiwScore_observedSegment_overlap_cross_moment t0 zeta C m hClass j nu hnu r k h hh ht)

/-- Equation (6) under the observable law is the zero-lag union-ratio bound. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the sample size](hyp:n),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), [the initial distribution](hyp:nu),
[the initial distribution assumption](hyp:hnu), [the reward symbol](hyp:r),
[the history length](hyp:k), and [the epoch index assumption](hyp:ht), this establishes
[the partial-history importance-weighted score observed segment second moment result](goal). -/
-- @node: phiwScore_observedSegment_second_moment
lemma phiwScore_observedSegment_second_moment {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (r k : Nat) (ht : r + k < n) :
    (∫ w, (phiwScore k m.Mx.b (m.Mx.E j) w ⟨r + k, ht⟩) ^ 2
      ∂((segmentLaw m hClass.finite_state nu n).map obsProj)) ≤
      policyFactor zeta ^ (k + 1) := by
  simpa only [Nat.add_zero, Nat.sub_zero, pow_two] using
    phiwScore_observedSegment_overlap_cross_moment t0 zeta C m hClass j nu hnu
      r k 0 (by omega) (by omega)

/-- The diagonal term in the block variance expansion is bounded by the sharp window second
moment, for every observable arbitrary-start window. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the reward symbol](hyp:r), [the history length](hyp:k), and
[the epoch index assumption](hyp:ht), this establishes
[the partial-history importance-weighted score observed segment variance result](goal). -/
-- @node: phiwScore_observedSegment_variance
lemma phiwScore_observedSegment_variance {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (r k : Nat) (ht : r + k < n) :
    variance (fun w ↦ phiwScore k m.Mx.b (m.Mx.E j) w ⟨r + k, ht⟩)
      ((segmentLaw m hClass.finite_state nu n).map obsProj) ≤
      policyFactor zeta ^ (k + 1) := by
  have : IsProbabilityMeasure ((segmentLaw m hClass.finite_state nu n).map obsProj) :=
    observedSegmentLaw_isProbability m hClass.sequential_ignorability.1
      hClass.finite_state nu hnu n
  exact (variance_le_expectation_sq
    (phiwScore_measurable k m.Mx.b (m.Mx.E j) _).aestronglyMeasurable).trans
      (phiwScore_observedSegment_second_moment t0 zeta C m hClass j nu hnu r k ht)

end CausalSmith.Stat.PomdpPolicyclassRegret
