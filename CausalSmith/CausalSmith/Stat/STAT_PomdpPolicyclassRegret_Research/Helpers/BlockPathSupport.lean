module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockDecodedWindows

/-!
# Support of structurally generated behavior paths

Every generated list has its prescribed horizon and unit-interval rewards.
Consequently decoded PHIW windows agree almost everywhere with the bounded
chronological path functionals, without extra regularity assumptions.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators ENNReal


/-- Presence of a list coordinate is measurable in the coordinate sigma algebra. For
[the first event](hyp:A) and [the i](hyp:i), this establishes
[the segment list length gt measurability set result](goal). -/
-- @node: segment_list_length_gt_measurableSet
lemma segment_list_length_gt_measurableSet {A : Type*} [MeasurableSpace A]
    (i : Nat) : MeasurableSet {path : List A | i < path.length} := by
  have h : MeasurableSet {path : List A | ∃ a ∈ (Set.univ : Set A), path[i]? = some a} :=
    MeasurableSpace.measurableSet_generateFrom ⟨i, Set.univ, MeasurableSet.univ, rfl⟩
  convert h using 1
  ext path
  simp [List.getElem?_eq_some_iff]

/-- Exact list horizons are measurable, including the empty segment. For
[the first event](hyp:A) and [the sample size](hyp:n), this establishes
[the segment list length equality measurability set result](goal). -/
-- @node: segment_list_length_eq_measurableSet
lemma segment_list_length_eq_measurableSet {A : Type*} [MeasurableSpace A]
    (n : Nat) : MeasurableSet {path : List A | path.length = n} := by
  cases n with
  | zero =>
    convert (segment_list_length_gt_measurableSet (A := A) 0).compl using 1
    ext path
    simp
  | succ n =>
    convert (segment_list_length_gt_measurableSet (A := A) n).inter
      (segment_list_length_gt_measurableSet (A := A) (n + 1)).compl using 1
    ext path
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    omega

/-- The horizon and all padded reward-coordinate support conditions are measurable. For
[the index subset](hyp:S), [the fallback state](hyp:fallback), and [the sample size](hyp:n),
this establishes [the segment path support measurability set result](goal). -/
-- @node: segment_path_support_measurableSet
lemma segment_path_support_measurableSet {S : Type*} [MeasurableSpace S]
    (fallback : S) (n : Nat) : MeasurableSet
    {path : List (Bool × ℝ × S) | path.length = n ∧
      ∀ i, (path.getD i (false, 0, fallback)).2.1 ∈ Set.Icc (0 : ℝ) 1} := by
  have hreward : MeasurableSet {path : List (Bool × ℝ × S) |
      ∀ i, (path.getD i (false, 0, fallback)).2.1 ∈ Set.Icc (0 : ℝ) 1} := by
    have heq : {path : List (Bool × ℝ × S) |
        ∀ i, (path.getD i (false, 0, fallback)).2.1 ∈ Set.Icc (0 : ℝ) 1} =
        ⋂ i : Nat, {path : List (Bool × ℝ × S) |
          (path.getD i (false, 0, fallback)).2.1 ∈ Set.Icc (0 : ℝ) 1} := by
      ext path
      simp
    rw [heq]
    exact MeasurableSet.iInter (fun i : Nat ↦
      (segment_list_getD_measurable i (false, 0, fallback)).snd.fst measurableSet_Icc)
  exact (segment_list_length_eq_measurableSet n).inter hreward


/-- A measurable mixed law inherits measurable support from its fibers. For
[the first event](hyp:A), [the second event](hyp:B), [the measure](hyp:μ), [the kernel](hyp:κ),
[the kernel assumption](hyp:hκ), [the policy](hyp:p), [the policy assumption](hyp:hp), and
[the stated assumption](hyp:h), this establishes
[the partial-history importance-weighted ae bind of ae result](goal). -/
-- @node: phiw_ae_bind_of_ae
lemma phiw_ae_bind_of_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (κ : A → Measure B) (hκ : Measurable κ) (p : B → Prop)
    (hp : MeasurableSet {x | p x}) (h : ∀ᵐ a ∂μ, ∀ᵐ x ∂κ a, p x) :
    ∀ᵐ x ∂μ.bind κ, p x := by
  exact Measure.ae_comp_of_ae_ae (κ := ⟨κ, hκ⟩) hp h

/-- Behavior mixing preserves the common kernel's unit reward support. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m), and
[the state](hyp:s), this establishes [the segment step law reward ae unit result](goal). -/
-- @node: segmentStepLaw_reward_ae_unit
lemma segmentStepLaw_reward_ae_unit {T M : Nat} (m : ModelIndex T M)
    (s : JointState m.nX m.nH) :
    ∀ᵐ step ∂segmentStepLaw m s, step.2.1 ∈ Set.Icc (0 : ℝ) 1 := by
  rw [segmentStepLaw, ae_finsetSum_measure_iff]
  intro a _
  apply Measure.ae_smul_measure
  apply (ae_map_iff (by fun_prop) (measurable_snd.fst measurableSet_Icc)).2
  exact phiw_kernel_reward_ae_unit m s a

/-- Generated behavior paths have their exact horizon and supported rewards. Padding has reward
zero, so the support statement holds for every coordinate. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the fallback state](hyp:fallback),
[the sample size](hyp:n), and [the state](hyp:s), this establishes
[the segment from ae path support result](goal). -/
-- @node: segmentFrom_ae_path_support
lemma segmentFrom_ae_path_support {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (fallback : JointState m.nX m.nH)
    (n : Nat) (s : JointState m.nX m.nH) :
    ∀ᵐ path ∂segmentFrom m n s, path.length = n ∧
      ∀ i, (path.getD i (false, 0, fallback)).2.1 ∈ Set.Icc (0 : ℝ) 1 := by
  induction n generalizing s with
  | zero =>
    rw [segmentFrom, ae_dirac_iff (segment_path_support_measurableSet fallback 0)]
    simp [List.getD]
  | succ n ih =>
    rw [segmentFrom]
    apply phiw_ae_bind_of_ae _ _ (segmentFrom_cons_family_measurable m hb n) _
      (segment_path_support_measurableSet fallback (n + 1))
    filter_upwards [segmentStepLaw_reward_ae_unit m s] with step hstep
    apply (ae_map_iff
      (segment_list_cons_measurable.comp (measurable_prodMk_left (x := step))).aemeasurable
      (segment_path_support_measurableSet fallback (n + 1))).2
    filter_upwards [ih step.2.2] with tail htail
    change (step :: tail).length = n + 1 ∧
      ∀ i, ((step :: tail).getD i (false, 0, fallback)).2.1 ∈ Set.Icc (0 : ℝ) 1
    refine ⟨by simp [htail.1], ?_⟩
    intro i
    cases i with
    | zero => simpa only [List.getD_cons_zero] using hstep
    | succ i => simpa only [List.getD_cons_succ] using htail.2 i

/-- Each decoded observable window agrees with its generated-path score almost everywhere under
the actual segment law. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the sample size](hyp:n), [the model](hyp:m), [the behavior policy assumption](hyp:hb),
[the candidate index](hyp:j), [the fallback state](hyp:fallback), [the state](hyp:s),
[the reward symbol](hyp:r), [the history length](hyp:k), and
[the epoch index assumption](hyp:ht), this establishes
[the partial-history importance-weighted score decode segment ae equality path reward result](goal). -/
-- @node: phiwScore_decodeSegment_ae_eq_path_reward
lemma phiwScore_decodeSegment_ae_eq_path_reward {T M n : Nat}
    (m : ModelIndex T M) (hb : PolicyVector m.Mx.b) (j : Fin M)
    (fallback s : JointState m.nX m.nH) (r k : Nat) (ht : r + k < n) :
    (fun path ↦ phiwScore k m.Mx.b (m.Mx.E j)
      (obsProj (decodeSegment (n := n) fallback (s, path))) ⟨r + k, ht⟩) =ᵐ[segmentFrom m n s]
      phiwPathShift (phiwPathReward m j k) r s := by
  filter_upwards [segmentFrom_ae_path_support m hb fallback n s] with path hpath
  exact phiwScore_decodeSegment_eq_path_reward m j fallback s path r k ht
    hpath.1 (hpath.2 (r + k))

/-- The decoded window inherits every finite-path Lp bound from its chronological functional.
Kernel reward support supplies regularity for free. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the fallback state](hyp:fallback), [the state](hyp:s), [the reward symbol](hyp:r),
[the history length](hyp:k), [the epoch index assumption](hyp:ht), and [the policy](hyp:p), this
establishes
[the partial-history importance-weighted score decode segment membership lp result](goal). -/
-- @node: phiwScore_decodeSegment_memLp
lemma phiwScore_decodeSegment_memLp {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (fallback s : JointState m.nX m.nH) (r k : Nat) (ht : r + k < n) (p : ℝ≥0∞) :
    MemLp (fun path ↦ phiwScore k m.Mx.b (m.Mx.E j)
      (obsProj (decodeSegment (n := n) fallback (s, path))) ⟨r + k, ht⟩)
      p (segmentFrom m n s) := by
  have h : MemLp (phiwPathShift (phiwPathReward m j k) r s) p (segmentFrom m n s) :=
    phiwPathShift_memLp m hClass.sequential_ignorability.1
    (phiwPathReward m j k) (phiwPathReward_measurable m j k)
    (policyFactor zeta ^ (k + 1)) (phiwPathReward_bounds t0 zeta C m hClass j k)
    r n s p
  exact MemLp.ae_eq (phiwScore_decodeSegment_ae_eq_path_reward m
    hClass.sequential_ignorability.1 j fallback s r k ht).symm h

/-- Equation (1) directly for a decoded observable window and a fixed full-state start, with any
unused suffix of the generated segment. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the fallback state](hyp:fallback), [the state](hyp:s), [the reward symbol](hyp:r),
[the history length](hyp:k), and [the extra](hyp:extra), this establishes
[the partial-history importance-weighted score decode segment integral equality behavior iterate result](goal). -/
-- @node: phiwScore_decodeSegment_integral_eq_behavior_iterate
lemma phiwScore_decodeSegment_integral_eq_behavior_iterate {T M : Nat}
    (t0 zeta C : ℝ) (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (fallback s : JointState m.nX m.nH) (r k extra : Nat) :
    (∫ path, phiwScore k m.Mx.b (m.Mx.E j)
      (obsProj (decodeSegment (n := r + ((k + 1) + extra)) fallback (s, path)))
      ⟨r + k, by omega⟩ ∂segmentFrom m (r + ((k + 1) + extra)) s) =
      Causalean.Mathlib.Probability.FiniteMarkovOscillation.markovOperatorIter
        (listPolicyKernel m m.Mx.b) r (phiwChronologicalMean m j k) s := by
  calc
    _ = ∫ path, phiwPathShift (phiwPathReward m j k) r s path
        ∂segmentFrom m (r + ((k + 1) + extra)) s :=
      integral_congr_ae (phiwScore_decodeSegment_ae_eq_path_reward m
        hClass.sequential_ignorability.1 j fallback s r k (by omega))
    _ = _ := phiwPathShift_reward_integral_eq_behavior_iterate t0 zeta C m hClass j r k extra s

/-- The decoded-window version of equation (4) averages the actual path integrals over an
arbitrary initial probability vector. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the fallback state](hyp:fallback), [the initial distribution](hyp:nu),
[the initial distribution assumption](hyp:hnu), [the reward symbol](hyp:r),
[the history length](hyp:k), and [the extra](hyp:extra), this establishes
[the partial-history importance-weighted score decode segment initial bias result](goal). -/
-- @node: phiwScore_decodeSegment_initial_bias
lemma phiwScore_decodeSegment_initial_bias {T M : Nat}
    (t0 zeta C : ℝ) (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (fallback : JointState m.nX m.nH)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) (r k extra : Nat) :
    |(∑ s, nu s * ∫ path, phiwScore k m.Mx.b (m.Mx.E j)
      (obsProj (decodeSegment (n := r + ((k + 1) + extra)) fallback (s, path)))
      ⟨r + k, by omega⟩ ∂segmentFrom m (r + ((k + 1) + extra)) s) - policyValue m j| ≤
      mixingAlpha t0 ^ k * (overlapRadius C + mixingAlpha t0 ^ r) := by
  have heq : (∑ s, nu s * ∫ path, phiwScore k m.Mx.b (m.Mx.E j)
      (obsProj (decodeSegment (n := r + ((k + 1) + extra)) fallback (s, path)))
      ⟨r + k, by omega⟩ ∂segmentFrom m (r + ((k + 1) + extra)) s) =
      ∑ s, nu s * ∫ path, phiwPathShift (phiwPathReward m j k) r s path
        ∂segmentFrom m (r + ((k + 1) + extra)) s := by
    apply Finset.sum_congr rfl
    intro s _
    congr 1
    exact integral_congr_ae (phiwScore_decodeSegment_ae_eq_path_reward m
      hClass.sequential_ignorability.1 j fallback s r k (by omega))
  rw [heq]
  exact phiwPathShift_reward_initial_bias t0 zeta C m hClass j nu hnu r k extra

end CausalSmith.Stat.PomdpPolicyclassRegret
