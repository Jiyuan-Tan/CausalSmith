module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import CausalSmith.Mathlib.MeasurableList
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Arbitrary-start block PHIW moments

The segment law is generated structurally from the common kernel, behavior
policy, and an arbitrary full-state initialization vector.
-/

@[expose] public section

set_option linter.style.longLine false

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open CausalSmith.Stat.PomdpLatentOverlapMinimax
/-- [the segment step law object](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), and [the state](hyp:s). -/

noncomputable def segmentStepLaw {T M : Nat} (m : ModelIndex T M)
    (s : JointState m.nX m.nH) :
    Measure (Bool × ℝ × JointState m.nX m.nH) :=
  ∑ a : Bool, ENNReal.ofReal (m.Mx.b s.1 a) •
    (m.Mx.K s a).map (fun ys ↦ (a, ys.1, ys.2))

/-- Structural, finite-horizon iteration of the behavior transition law. -/
noncomputable def segmentFrom {T M : Nat} (m : ModelIndex T M) :
    (n : Nat) → JointState m.nX m.nH →
      Measure (List (Bool × ℝ × JointState m.nX m.nH))
  | 0, _ => Measure.dirac []
  | n + 1, s =>
      (segmentStepLaw m s).bind (fun step ↦
        (segmentFrom m n step.2.2).map (fun tail ↦ step :: tail))
/-- [the decode segment object](goal) is defined from [the sample size](hyp:n),
[the observed-state count](hyp:nX), [the hidden-state count](hyp:nH),
[the fallback state](hyp:fallback), and [the path](hyp:path). -/

def decodeSegment {n nX nH : Nat} (fallback : JointState nX nH)
    (path : JointState nX nH × List (Bool × ℝ × JointState nX nH)) :
    FullTrajectory n nX nH :=
  ((fun i ↦ if i.val = 0 then path.1 else
      (path.2.getD (i.val - 1) (false, 0, fallback)).2.2),
    fun t ↦ let step := path.2.getD t.val (false, 0, fallback)
      (step.1, step.2.1))
/-- [the initial state law object](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), and [the initial distribution](hyp:nu). -/

noncomputable def initialStateLaw {T M : Nat} (m : ModelIndex T M)
    (nu : JointState m.nX m.nH → ℝ) : Measure (JointState m.nX m.nH) :=
  ∑ s, ENNReal.ofReal (nu s) • Measure.dirac s

/-- Behavior-driven `n`-epoch segment begun from the arbitrary law `nu`. -/
noncomputable def segmentLaw {T M : Nat} (m : ModelIndex T M)
    (hFinite : FiniteState m) (nu : JointState m.nX m.nH → ℝ) (n : Nat) :
    Measure (FullTrajectory n m.nX m.nH) :=
  let fallback : JointState m.nX m.nH :=
    (⟨0, hFinite.1⟩, ⟨0, hFinite.2⟩)
  ((initialStateLaw m nu).bind (fun s ↦
      (segmentFrom m n s).map (fun path ↦ (s, path)))).map
    (decodeSegment fallback)

/-- Prepending a step respects the coordinate-generated list sigma algebra. For
[the first event](hyp:A), this establishes [the segment list cons measurability result](goal). -/
@[fun_prop]
-- @node: segment_list_cons_measurable
lemma segment_list_cons_measurable {A : Type*} [MeasurableSpace A] :
    Measurable (fun p : A × List A ↦ p.1 :: p.2) := by
  apply measurable_generateFrom
  rintro _ ⟨k, B, hB, rfl⟩
  cases k with
  | zero =>
    convert measurable_fst hB using 1
    ext p
    simp
  | succ k =>
    have hcoord : MeasurableSet {l : List A | ∃ a ∈ B, l[k]? = some a} :=
      MeasurableSpace.measurableSet_generateFrom ⟨k, B, hB, rfl⟩
    convert measurable_snd hcoord using 1
    ext p
    simp

/-- Reading a padded coordinate is measurable even for a short path. For
[the first event](hyp:A), [the history length](hyp:k), and [the fallback state](hyp:fallback),
this establishes [the segment list get d measurability result](goal). -/
@[fun_prop]
-- @node: segment_list_getD_measurable
lemma segment_list_getD_measurable {A : Type*} [MeasurableSpace A]
    (k : Nat) (fallback : A) : Measurable (fun l : List A ↦ l.getD k fallback) := by
  intro B hB
  have hcoord : MeasurableSet {l : List A | ∃ a ∈ B, l[k]? = some a} :=
    MeasurableSpace.measurableSet_generateFrom ⟨k, B, hB, rfl⟩
  have hpresent : MeasurableSet {l : List A | ∃ a ∈ (Set.univ : Set A), l[k]? = some a} :=
    MeasurableSpace.measurableSet_generateFrom ⟨k, Set.univ, MeasurableSet.univ, rfl⟩
  by_cases hf : fallback ∈ B
  · have heq : (fun l : List A ↦ l.getD k fallback) ⁻¹' B =
        {l : List A | ∃ a ∈ B, l[k]? = some a} ∪
          {l : List A | ∃ a ∈ (Set.univ : Set A), l[k]? = some a}ᶜ := by
      ext l
      simp only [Set.mem_preimage, List.getD, Set.mem_union, Set.mem_ofPred_eq,
        Set.mem_compl_iff, Set.mem_univ, true_and]
      cases l[k]? <;> simp [hf]
    rw [heq]
    exact hcoord.union hpresent.compl
  · have heq : (fun l : List A ↦ l.getD k fallback) ⁻¹' B =
        {l : List A | ∃ a ∈ B, l[k]? = some a} := by
      ext l
      simp only [Set.mem_preimage, List.getD, Set.mem_ofPred_eq]
      cases l[k]? <;> simp [hf]
    rw [heq]
    exact hcoord

/-- Decoding the structural segment preserves measurable observations. For
[the sample size](hyp:n), [the observed-state count](hyp:nX), [the hidden-state count](hyp:nH),
and [the fallback state](hyp:fallback), this establishes
[the decode segment measurability result](goal). -/
@[fun_prop]
-- @node: decodeSegment_measurable
lemma decodeSegment_measurable {n nX nH : Nat} (fallback : JointState nX nH) :
    Measurable (decodeSegment (n := n) fallback) := by
  unfold decodeSegment
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    split_ifs <;> fun_prop
  · apply measurable_pi_lambda
    intro t
    fun_prop

/-- The arbitrary initial vector defines a probability measure. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), [the initial distribution](hyp:nu), and
[the initial distribution assumption](hyp:hnu), this establishes
[the initial state law is probability result](goal). -/
-- @node: initialStateLaw_isProbability
lemma initialStateLaw_isProbability {T M : Nat} (m : ModelIndex T M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) :
    IsProbabilityMeasure (initialStateLaw m nu) := by
  constructor
  simp only [initialStateLaw, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ ↦ hnu.1 s), hnu.2]
  simp

/-- The common reward-transition kernel mixed under behavior has unit mass. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), and [the state](hyp:s), this establishes
[the segment step law is probability result](goal). -/
-- @node: segmentStepLaw_isProbability
lemma segmentStepLaw_isProbability {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (s : JointState m.nX m.nH) :
    IsProbabilityMeasure (segmentStepLaw m s) := by
  have hmap : ∀ a : Bool, IsProbabilityMeasure
      ((m.Mx.K s a).map (fun ys ↦ (a, ys.1, ys.2))) := by
    intro a
    have : IsProbabilityMeasure (m.Mx.K s a) := m.kernel_law.1 s a
    apply Measure.isProbabilityMeasure_map
    fun_prop
  constructor
  simp only [segmentStepLaw, Measure.finsetSum_apply, Measure.smul_apply,
    @measure_univ _ _ _ (hmap _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ (hb s.1).1 a), (hb s.1).2]
  simp

/-- Every structurally generated future segment has unit mass. The proof integrates the joint
reward and successor law, allowing their dependence. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the sample size](hyp:n), and [the state](hyp:s), this
establishes [the segment from is probability result](goal). -/
-- @node: segmentFrom_isProbability
lemma segmentFrom_isProbability {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (n : Nat) (s : JointState m.nX m.nH) :
    IsProbabilityMeasure (segmentFrom m n s) := by
  induction n generalizing s with
  | zero => simp only [segmentFrom]; infer_instance
  | succ n ih =>
    let κ : Kernel (Bool × ℝ × JointState m.nX m.nH)
        (List (Bool × ℝ × JointState m.nX m.nH)) :=
      ⟨fun step ↦ segmentFrom m n step.2.2,
        (measurable_of_countable (segmentFrom m n)).comp measurable_snd.snd⟩
    have : IsMarkovKernel κ := ⟨fun step ↦ ih step.2.2⟩
    have hfuture : Measurable (fun step : Bool × ℝ × JointState m.nX m.nH ↦
        (segmentFrom m n step.2.2).map (fun tail ↦ step :: tail)) := by
      apply Measure.measurable_of_measurable_coe
      intro B hB
      have hcons : MeasurableSet
          ((fun p : (Bool × ℝ × JointState m.nX m.nH) ×
            List (Bool × ℝ × JointState m.nX m.nH) ↦ p.1 :: p.2) ⁻¹' B) :=
        segment_list_cons_measurable hB
      convert Kernel.measurable_kernel_prodMk_left (κ := κ) hcons using 1
      funext step
      exact Measure.map_apply
        (segment_list_cons_measurable.comp (measurable_prodMk_left (x := step))) hB
    have : IsProbabilityMeasure (segmentStepLaw m s) := segmentStepLaw_isProbability m hb s
    constructor
    rw [segmentFrom, Measure.bind_apply MeasurableSet.univ hfuture.aemeasurable]
    have hmass : ∀ step : Bool × ℝ × JointState m.nX m.nH,
        ((segmentFrom m n step.2.2).map (fun tail ↦ step :: tail)) Set.univ = 1 := by
      intro step
      have : IsProbabilityMeasure (segmentFrom m n step.2.2) := ih step.2.2
      have hc : Measurable (fun tail : List (Bool × ℝ × JointState m.nX m.nH) ↦
          step :: tail) := segment_list_cons_measurable.comp measurable_prodMk_left
      rw [Measure.map_apply hc MeasurableSet.univ]
      simp
    simp_rw [hmass]
    simp

/-- The arbitrary-start full trajectory law is probabilistic. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the finite assumption](hyp:hFinite),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu), and
[the sample size](hyp:n), this establishes [the segment law is probability result](goal). -/
-- @node: segmentLaw_isProbability
lemma segmentLaw_isProbability {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (hFinite : FiniteState m)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) (n : Nat) :
    IsProbabilityMeasure (segmentLaw m hFinite nu n) := by
  have : IsProbabilityMeasure (initialStateLaw m nu) := initialStateLaw_isProbability m nu hnu
  have hbind : IsProbabilityMeasure
      ((initialStateLaw m nu).bind (fun s ↦
        (segmentFrom m n s).map (fun path ↦ (s, path)))) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    have hmass : ∀ s : JointState m.nX m.nH,
        ((segmentFrom m n s).map (fun path ↦ (s, path))) Set.univ = 1 := by
      intro s
      have : IsProbabilityMeasure (segmentFrom m n s) := segmentFrom_isProbability m hb n s
      rw [Measure.map_apply (measurable_prodMk_left (x := s)) MeasurableSet.univ]
      simp
    simp_rw [hmass]
    simp
  exact Measure.isProbabilityMeasure_map (decodeSegment_measurable _).aemeasurable

/-- The observed segment law also has unit mass. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the finite assumption](hyp:hFinite),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu), and
[the sample size](hyp:n), this establishes
[the observed segment law is probability result](goal). -/
-- @node: observedSegmentLaw_isProbability
lemma observedSegmentLaw_isProbability {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (hFinite : FiniteState m)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) (n : Nat) :
    IsProbabilityMeasure ((segmentLaw m hFinite nu n).map obsProj) := by
  have : IsProbabilityMeasure (segmentLaw m hFinite nu n) :=
    segmentLaw_isProbability m hb hFinite nu hnu n
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  unfold obsProj curState actionAt rewardAt
  apply measurable_pi_lambda
  intro t
  exact ((measurable_pi_apply t.castSucc).comp measurable_fst).fst.prodMk
    (((measurable_pi_apply t).comp measurable_snd).fst.prodMk
      ((measurable_pi_apply t).comp measurable_snd).snd)

/-- A behavior action contributes at most one factor of `L` to the second moment of a
target-to-behavior likelihood ratio. The zero-cell convention is valid because domination forces
the target mass there to vanish. For [the observed-state count](hyp:nX),
[the behavior policy](hyp:b), [the target policy](hyp:e),
[the behavior policy assumption](hyp:hb), [the target policy assumption](hyp:he),
[the action-overlap factor](hyp:L), [the action-overlap factor assumption](hyp:hL),
[the dom assumption](hyp:hdom), and [the observed state](hyp:x), this establishes
[the partial-history importance-weighted ratio action second moment result](goal). -/
-- @node: phiw_ratio_action_second_moment
lemma phiw_ratio_action_second_moment {nX : Nat} (b e : Policy nX)
    (hb : PolicyVector b) (he : PolicyVector e) (L : ℝ)
    (hL : 0 ≤ L) (hdom : ∀ x a, e x a ≤ L * b x a)
    (x : Fin nX) :
    (∑ a : Bool, b x a * (ratio b e x a) ^ 2) ≤ L := by
  have hcell : ∀ a : Bool, b x a * ratio b e x a = e x a := by
    intro a
    unfold ratio
    split_ifs with hz
    · have he0 : e x a = 0 := by
        have hle : e x a ≤ 0 := by simpa [hz] using hdom x a
        exact le_antisymm hle ((he x).1 a)
      simp [hz, he0]
    · exact mul_div_cancel₀ _ hz
  have hratio : ∀ a : Bool, 0 ≤ ratio b e x a ∧ ratio b e x a ≤ L := by
    intro a
    unfold ratio
    split_ifs with hz
    · exact ⟨le_refl _, hL⟩
    · have hbpos : 0 < b x a := lt_of_le_of_ne ((hb x).1 a) (Ne.symm hz)
      exact ⟨div_nonneg ((he x).1 a) (le_of_lt hbpos),
        (div_le_iff₀ hbpos).2 (hdom x a)⟩
  calc
    ∑ a : Bool, b x a * (ratio b e x a) ^ 2 ≤
        ∑ a : Bool, L * e x a := by
      apply Finset.sum_le_sum
      intro a _
      have hsquare : (ratio b e x a) ^ 2 ≤ L * ratio b e x a := by
        nlinarith [(hratio a).1, (hratio a).2]
      calc
        b x a * (ratio b e x a) ^ 2 ≤
            b x a * (L * ratio b e x a) :=
          mul_le_mul_of_nonneg_left hsquare ((hb x).1 a)
        _ = L * e x a := by rw [← hcell a]; ring
    _ = L := by rw [← Finset.mul_sum, (he x).2, mul_one]

/-- The one-step second-moment estimate for every candidate in the model class. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), and
[the observed state](hyp:x), this establishes
[the partial-history importance-weighted model ratio action second moment result](goal). -/
-- @node: phiw_model_ratio_action_second_moment
lemma phiw_model_ratio_action_second_moment {T M : Nat}
    (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) (j : Fin M) (x : Fin m.nX) :
    (∑ a : Bool, m.Mx.b x a *
        (ratio m.Mx.b (m.Mx.E j) x a) ^ 2) ≤ policyFactor zeta := by
  have hoverlap := hClass.action_overlap j
  exact phiw_ratio_action_second_moment m.Mx.b (m.Mx.E j)
    hClass.sequential_ignorability.1 hoverlap.1 (policyFactor zeta)
    (le_of_lt (Real.exp_pos zeta)) hoverlap.2 x

/-- Stationary overlap supplies at least `1 / C` common mass. This is the finite-state estimate
used to control the PHIW bias. For [the index subset](hyp:S), [the behavior policy](hyp:b),
[the code dimension](hyp:d), [the latent-overlap radius](hyp:C),
[the latent-overlap radius assumption](hyp:hC), [the code dimension assumption](hyp:hd),
[the sum assumption](hyp:hsum), and [the overlap assumption](hyp:hoverlap), this establishes
[the stationary overlap common mass result](goal). -/
-- @node: stationaryOverlap_commonMass
lemma stationaryOverlap_commonMass {S : Type*} [Fintype S]
    (b d : S → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hd : ∀ s, 0 ≤ d s) (hsum : ∑ s, d s = 1)
    (hoverlap : ∀ s, d s ≤ C * b s) :
    1 / C ≤ ∑ s, min (d s) (b s) := by
  have hCpos : 0 < C := by linarith
  have hpoint : ∀ s, d s / C ≤ min (d s) (b s) := by
    intro s
    apply le_min
    · exact div_le_self (hd s) hC
    · exact (div_le_iff₀ hCpos).2 (by simpa [mul_comm] using hoverlap s)
  have hsum_le := Finset.sum_le_sum (s := Finset.univ)
    (fun s _ ↦ hpoint s)
  simpa [← Finset.sum_div, hsum] using hsum_le

/-- Pointwise stationary overlap bounds the total-variation norm by `1 - 1 / C`, in its
finite-state `L¹` form. For [the index subset](hyp:S), [the behavior policy](hyp:b),
[the code dimension](hyp:d), [the latent-overlap radius](hyp:C),
[the latent-overlap radius assumption](hyp:hC), [the code dimension assumption](hyp:hd),
[the bsum assumption](hyp:hbsum), [the dsum assumption](hyp:hdsum), and
[the overlap assumption](hyp:hoverlap), this establishes
[the stationary overlap l1 result](goal). -/
-- @node: stationaryOverlap_l1
lemma stationaryOverlap_l1 {S : Type*} [Fintype S]
    (b d : S → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hd : ∀ s, 0 ≤ d s) (hbsum : ∑ s, b s = 1)
    (hdsum : ∑ s, d s = 1)
    (hoverlap : ∀ s, d s ≤ C * b s) :
    ∑ s, |d s - b s| ≤ 2 * (1 - 1 / C) := by
  have hmass := stationaryOverlap_commonMass b d C hC hd hdsum hoverlap
  have hpoint : ∀ s, |d s - b s| = d s + b s - 2 * min (d s) (b s) := by
    intro s
    rcases le_total (d s) (b s) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  simp_rw [hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [hdsum, hbsum]
  linarith

/-- A row bound on the covariance matrix gives the variance bound for a block average. This is
the final summation step of the PHIW moment proof. For [the sample space](hyp:Ω),
[the measure](hyp:μ), [the effective sample size](hyp:N),
[the effective sample size assumption](hyp:hN), [the x](hyp:X), [the x assumption](hyp:hX),
[the second event](hyp:B), and [the row assumption](hyp:hrow), this establishes
[the variance average bound of covariance rows result](goal). -/
-- @node: variance_average_le_of_covariance_rows
lemma variance_average_le_of_covariance_rows {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (N : Nat) (hN : 0 < N)
    (X : Fin N → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (B : ℝ) (hrow : ∀ i, ∑ j, ProbabilityTheory.covariance (X i) (X j) μ ≤ B) :
    ProbabilityTheory.variance (fun ω ↦ (∑ i, X i ω) / (N : ℝ)) μ ≤
      B / (N : ℝ) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hvar := ProbabilityTheory.variance_fun_sum hX
  have hsum : (∑ i : Fin N, ∑ j : Fin N,
      ProbabilityTheory.covariance (X i) (X j) μ) ≤ (N : ℝ) * B := by
    calc
      _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum (fun i _ ↦ hrow i)
      _ = (N : ℝ) * B := by simp [mul_comm]
  rw [show (fun ω ↦ (∑ i, X i ω) / (N : ℝ)) =
      (fun ω ↦ ((N : ℝ)⁻¹ * ∑ i, X i ω)) by funext ω; simp [div_eq_mul_inv, mul_comm]]
  rw [ProbabilityTheory.variance_const_mul, hvar]
  calc
    (N : ℝ)⁻¹ ^ 2 *
        (∑ i : Fin N, ∑ j : Fin N, ProbabilityTheory.covariance (X i) (X j) μ) ≤
      (N : ℝ)⁻¹ ^ 2 * ((N : ℝ) * B) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = B / (N : ℝ) := by field_simp

/-- Averaging the pointwise transient and stationary-overlap errors gives the arbitrary-start
bias rate in (5) of the PHIW calculation. For [the effective sample size](hyp:N),
[the history length](hyp:k), [the effective sample size assumption](hyp:hN),
[the contraction coefficient](hyp:α), [the q](hyp:q), [the parameter](hyp:θ),
[the α0 assumption](hyp:hα0), [the α1 assumption](hyp:hα1), [the x](hyp:X), and
[the point assumption](hyp:hpoint), this establishes
[the partial-history importance-weighted average bias of pointwise result](goal). -/
-- @node: phiw_average_bias_of_pointwise
lemma phiw_average_bias_of_pointwise (N k : Nat) (hN : 0 < N)
    (α q θ : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (X : Nat → ℝ)
    (hpoint : ∀ r < N, |X r - θ| ≤ α ^ k * (q + α ^ r)) :
    |(∑ r ∈ Finset.range N, X r) / (N : ℝ) - θ| ≤
      α ^ k * (q + 1 / ((N : ℝ) * (1 - α))) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hgeom : (∑ r ∈ Finset.range N, α ^ r) ≤ 1 / (1 - α) := by
    simpa [Nat.Ico_zero_eq_range] using
      (geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hα0 hα1)
  have hsum : (∑ r ∈ Finset.range N, |X r - θ|) ≤
      α ^ k * ((N : ℝ) * q + ∑ r ∈ Finset.range N, α ^ r) := by
    calc
      _ ≤ ∑ r ∈ Finset.range N, α ^ k * (q + α ^ r) := by
        apply Finset.sum_le_sum
        intro r hr
        exact hpoint r (Finset.mem_range.mp hr)
      _ = α ^ k * ((N : ℝ) * q + ∑ r ∈ Finset.range N, α ^ r) := by
        simp [Finset.sum_add_distrib, mul_add, ← Finset.mul_sum]
        ring
  have hsum' : (∑ r ∈ Finset.range N, |X r - θ|) ≤
      α ^ k * ((N : ℝ) * q + 1 / (1 - α)) := by
    exact hsum.trans (mul_le_mul_of_nonneg_left (add_le_add_right hgeom _) (pow_nonneg hα0 _))
  have hsplit : (∑ r ∈ Finset.range N, X r) / (N : ℝ) - θ =
      (∑ r ∈ Finset.range N, (X r - θ)) / (N : ℝ) := by
    simp [Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul]
    field_simp
  rw [hsplit, abs_div, abs_of_pos hNr]
  have htri : |∑ r ∈ Finset.range N, (X r - θ)| ≤
      ∑ r ∈ Finset.range N, |X r - θ| := Finset.abs_sum_le_sum_abs _ _
  have hbound := htri.trans hsum'
  apply (div_le_iff₀ hNr).2
  calc
    |∑ r ∈ Finset.range N, (X r - θ)| ≤
        α ^ k * ((N : ℝ) * q + 1 / (1 - α)) := hbound
    _ = α ^ k * (q + 1 / ((N : ℝ) * (1 - α))) * (N : ℝ) := by
      field_simp

/-- The overlapping-window covariances form the geometric part of the arbitrary-start variance
estimate. For [the history length](hyp:k), [the action-overlap factor](hyp:L), and
[the action-overlap factor assumption](hyp:hL), this establishes
[the partial-history importance-weighted overlap lag sum bound result](goal). -/
-- @node: phiw_overlap_lag_sum_le
lemma phiw_overlap_lag_sum_le (k : Nat) (L : ℝ) (hL : 1 < L) :
    (∑ h ∈ Finset.Ico 1 (k + 1), L ^ (k + 1 - h)) ≤ L ^ (k + 1) / (L - 1) := by
  have hreflect :
      (∑ h ∈ Finset.Ico 1 (k + 1), L ^ (k + 1 - h)) =
        ∑ h ∈ Finset.Ico 1 (k + 1), L ^ h := by
    simpa using (Finset.sum_Ico_reflect (fun j : Nat ↦ L ^ j) 1
      (show k + 1 ≤ (k + 1) + 1 by omega))
  rw [hreflect, geom_sum_Ico (by linarith : L ≠ 1) (show 1 ≤ k + 1 by omega)]
  exact (div_le_div_iff₀ (by linarith : 0 < L - 1)
    (by linarith : 0 < L - 1)).2 (by nlinarith [pow_nonneg (by linarith : 0 ≤ L) (k + 1)])

/-- The disjoint-window covariance tail is bounded independently of the block length. Its index
starts at `k` after shifting the lag by one. For [the history length](hyp:k),
[the effective sample size](hyp:N), [the contraction coefficient](hyp:α),
[the α0 assumption](hyp:hα0), and [the α1 assumption](hyp:hα1), this establishes
[the partial-history importance-weighted disjoint lag sum bound result](goal). -/
-- @node: phiw_disjoint_lag_sum_le
lemma phiw_disjoint_lag_sum_le (k N : Nat) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∑ h ∈ Finset.Ico k N, α ^ h) ≤ 1 / (1 - α) := by
  have hsum := geom_sum_Ico_le_of_lt_one (m := k) (n := N) hα0 hα1
  have hpow : α ^ k ≤ 1 := pow_le_one₀ hα0 hα1.le
  exact hsum.trans ((div_le_div_iff₀ (by linarith : 0 < 1 - α)
    (by linarith : 0 < 1 - α)).2 (by nlinarith))

/-- Numerical assembly of the diagonal, overlapping-window, and disjoint-window covariance
bounds in the arbitrary-start PHIW proof. For [the history length](hyp:k),
[the effective sample size](hyp:N), [the action-overlap factor](hyp:L),
[the contraction coefficient](hyp:α), [the action-overlap factor assumption](hyp:hL),
[the α0 assumption](hyp:hα0), and [the α1 assumption](hyp:hα1), this establishes
[the partial-history importance-weighted variance lag numeric bound result](goal). -/
-- @node: phiw_variance_lag_numeric_bound
lemma phiw_variance_lag_numeric_bound (k N : Nat) (L α : ℝ)
    (hL : 1 < L) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    L ^ (k + 1) +
        2 * (∑ h ∈ Finset.Ico 1 (k + 1), L ^ (k + 1 - h)) +
        4 * (∑ h ∈ Finset.Ico k N, α ^ h) ≤
      (1 + 2 / (L - 1) + 4 / (1 - α)) * L ^ (k + 1) := by
  have hoverlap := phiw_overlap_lag_sum_le k L hL
  have hdisjoint := phiw_disjoint_lag_sum_le k N α hα0 hα1
  have hpow : 1 ≤ L ^ (k + 1) := one_le_pow₀ (le_of_lt hL)
  have htail : 0 ≤ 4 / (1 - α) := by positivity
  have htailMul : 4 / (1 - α) ≤ 4 / (1 - α) * L ^ (k + 1) := by
    nlinarith [mul_nonneg htail (sub_nonneg.mpr hpow)]
  have hO := mul_le_mul_of_nonneg_left hoverlap (by norm_num : (0 : ℝ) ≤ 2)
  have hD := mul_le_mul_of_nonneg_left hdisjoint (by norm_num : (0 : ℝ) ≤ 4)
  have hD' : 4 * (∑ h ∈ Finset.Ico k N, α ^ h) ≤ 4 / (1 - α) := by
    simpa only [one_div, div_eq_mul_inv, one_mul] using hD
  calc
    _ ≤ L ^ (k + 1) + 2 * (L ^ (k + 1) / (L - 1)) +
        4 / (1 - α) := by linarith [hO, hD']
    _ ≤ L ^ (k + 1) + 2 * (L ^ (k + 1) / (L - 1)) +
        4 / (1 - α) * L ^ (k + 1) := by linarith
    _ = (1 + 2 / (L - 1) + 4 / (1 - α)) * L ^ (k + 1) := by ring


end CausalSmith.Stat.PomdpPolicyclassRegret
