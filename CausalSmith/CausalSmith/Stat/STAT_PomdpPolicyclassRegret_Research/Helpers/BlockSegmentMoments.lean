module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockPathSupport

/-!
# Arbitrary-start observable PHIW means

Finite mixing transfers the chronological window identities to the decoded
segment law. Averaging these actual observable expectations gives the block
bias bound, with regularity derived from the generated reward support.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators ENNReal

/-- The arbitrary-start segment is a finite mixture of decoded fixed-start paths. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the finite assumption](hyp:hFinite), [the initial distribution](hyp:nu), and
[the sample size](hyp:n), this establishes
[the segment law equality sum fixed start result](goal). -/
-- @node: segmentLaw_eq_sum_fixed_start
lemma segmentLaw_eq_sum_fixed_start {T M : Nat} (m : ModelIndex T M)
    (hFinite : FiniteState m) (nu : JointState m.nX m.nH → ℝ) (n : Nat) :
    segmentLaw m hFinite nu n =
      ∑ s, ENNReal.ofReal (nu s) • (segmentFrom m n s).map
        (fun path ↦ decodeSegment (n := n) (⟨0, hFinite.1⟩, ⟨0, hFinite.2⟩) (s, path)) := by
  unfold segmentLaw initialStateLaw
  rw [← Measure.sum_fintype, Measure.bind_sum _ _ (measurable_of_countable _).aemeasurable]
  simp_rw [Measure.bind_smul, Measure.dirac_bind (measurable_of_countable _)]
  rw [Measure.map_sum (decodeSegment_measurable _).aemeasurable, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro s _
  rw [Measure.map_smul, Measure.map_map (decodeSegment_measurable _)
    (measurable_prodMk_left (x := s))]
  rfl

/-- Observing a full segment is a measurable coordinate projection. For
[the sample size](hyp:n), [the observed-state count](hyp:nX), and
[the hidden-state count](hyp:nH), this establishes
[the partial-history importance-weighted obs proj measurability result](goal). -/
@[fun_prop]
-- @node: phiw_obsProj_measurable
lemma phiw_obsProj_measurable {n nX nH : Nat} :
    Measurable (obsProj (T := n) (nX := nX) (nH := nH)) := by
  unfold obsProj curState actionAt rewardAt
  apply measurable_pi_lambda
  intro t
  fun_prop

/-- Each observable PHIW window is measurable. For [the sample size](hyp:n),
[the observed-state count](hyp:nX), [the history length](hyp:k), [the behavior policy](hyp:b),
[the target policy](hyp:e), and [the epoch index](hyp:t), this establishes
[the partial-history importance-weighted score measurability result](goal). -/
@[fun_prop]
-- @node: phiwScore_measurable
lemma phiwScore_measurable {n nX : Nat} (k : Nat) (b e : Policy nX) (t : Fin n) :
    Measurable (fun w : ObsView n nX ↦ phiwScore k b e w t) := by
  unfold phiwScore
  apply Measurable.mul
  · fun_prop
  · apply Finset.measurable_prod
    intro i _
    exact (measurable_of_finite (fun p : Fin nX × Bool ↦ ratio b e p.1 p.2)).comp
      (((measurable_pi_apply i).fst).prodMk ((measurable_pi_apply i).snd.fst))

/-- Observing the finite mixture commutes with each fixed-start decoding map. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the finite assumption](hyp:hFinite), [the initial distribution](hyp:nu), and
[the sample size](hyp:n), this establishes
[the observed segment law equality sum fixed start result](goal). -/
-- @node: observedSegmentLaw_eq_sum_fixed_start
lemma observedSegmentLaw_eq_sum_fixed_start {T M : Nat} (m : ModelIndex T M)
    (hFinite : FiniteState m) (nu : JointState m.nX m.nH → ℝ) (n : Nat) :
    (segmentLaw m hFinite nu n).map obsProj =
      ∑ s, ENNReal.ofReal (nu s) • (segmentFrom m n s).map
        (fun path ↦ obsProj (decodeSegment (n := n)
          (⟨0, hFinite.1⟩, ⟨0, hFinite.2⟩) (s, path))) := by
  rw [segmentLaw_eq_sum_fixed_start, ← Measure.sum_fintype,
    Measure.map_sum phiw_obsProj_measurable.aemeasurable, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro s _
  rw [Measure.map_smul, Measure.map_map phiw_obsProj_measurable
    (by fun_prop)]
  rfl

/-- Window Lp regularity under the actual arbitrary-start observable law. All exponents are
allowed since the supported score is bounded. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the reward symbol](hyp:r), [the history length](hyp:k), [the epoch index assumption](hyp:ht),
and [the policy](hyp:p), this establishes
[the partial-history importance-weighted score observed segment membership lp result](goal). -/
-- @node: phiwScore_observedSegment_memLp
lemma phiwScore_observedSegment_memLp {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (r k : Nat) (ht : r + k < n) (p : ℝ≥0∞) :
    MemLp (fun w ↦ phiwScore k m.Mx.b (m.Mx.E j) w ⟨r + k, ht⟩) p
      ((segmentLaw m hClass.finite_state nu n).map obsProj) := by
  have : IsProbabilityMeasure ((segmentLaw m hClass.finite_state nu n).map obsProj) :=
    observedSegmentLaw_isProbability m hClass.sequential_ignorability.1
      hClass.finite_state nu hnu n
  apply memLp_of_bounded (a := 0) (b := policyFactor zeta ^ (k + 1))
  · rw [observedSegmentLaw_eq_sum_fixed_start, ae_finsetSum_measure_iff]
    intro s _
    apply Measure.ae_smul_measure
    apply (ae_map_iff (by fun_prop)
      ((phiwScore_measurable k m.Mx.b (m.Mx.E j) ⟨r + k, ht⟩) measurableSet_Icc)).2
    filter_upwards [phiwScore_decodeSegment_ae_eq_path_reward m
      hClass.sequential_ignorability.1 j
      (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) s r k ht] with path hp
    rw [hp]
    exact phiwPathShift_bounds _ _ (phiwPathReward_bounds t0 zeta C m hClass j k)
      r s path
  · exact (phiwScore_measurable k m.Mx.b (m.Mx.E j) _).aestronglyMeasurable

/-- Expanding an actual observable expectation into its fixed-start path integrals. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the sample size](hyp:n),
[the model](hyp:m), [the finite assumption](hyp:hFinite), [the initial distribution](hyp:nu),
[the initial distribution assumption](hyp:hnu), [the f](hyp:f), [the f assumption](hyp:hf), and
[the int assumption](hyp:hint), this establishes
[the observed segment integral equality sum fixed start result](goal). -/
-- @node: observedSegment_integral_eq_sum_fixed_start
lemma observedSegment_integral_eq_sum_fixed_start {T M n : Nat} (m : ModelIndex T M)
    (hFinite : FiniteState m) (nu : JointState m.nX m.nH → ℝ)
    (hnu : ProbabilityVector nu) (f : ObsView n m.nX → ℝ) (hf : Measurable f)
    (hint : ∀ s, Integrable (fun path ↦ f (obsProj (decodeSegment (n := n)
      (⟨0, hFinite.1⟩, ⟨0, hFinite.2⟩) (s, path)))) (segmentFrom m n s)) :
    (∫ w, f w ∂((segmentLaw m hFinite nu n).map obsProj)) =
      ∑ s, nu s * ∫ path, f (obsProj (decodeSegment (n := n)
        (⟨0, hFinite.1⟩, ⟨0, hFinite.2⟩) (s, path))) ∂segmentFrom m n s := by
  rw [observedSegmentLaw_eq_sum_fixed_start, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro s _
    rw [integral_smul_measure, integral_map (by fun_prop) hf.aestronglyMeasurable,
      ENNReal.toReal_ofReal (hnu.1 s)]
    rfl
  · intro s _
    apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
    exact (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).2 (hint s)

/-- Equation (4) for a window under the arbitrary-start observable segment law. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the reward symbol](hyp:r), [the history length](hyp:k), and [the extra](hyp:extra), this
establishes [the partial-history importance-weighted score observed segment bias result](goal). -/
-- @node: phiwScore_observedSegment_bias
lemma phiwScore_observedSegment_bias {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) (r k extra : Nat) :
    |(∫ w, phiwScore k m.Mx.b (m.Mx.E j) w ⟨r + k, by omega⟩
      ∂((segmentLaw m hClass.finite_state nu (r + ((k + 1) + extra))).map obsProj))
      - policyValue m j| ≤
      mixingAlpha t0 ^ k * (overlapRadius C + mixingAlpha t0 ^ r) := by
  have hi : ∀ s, Integrable (fun path ↦ phiwScore k m.Mx.b (m.Mx.E j)
      (obsProj (decodeSegment (n := r + ((k + 1) + extra))
        (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩) (s, path)))
      ⟨r + k, by omega⟩) (segmentFrom m (r + ((k + 1) + extra)) s) := by
    intro s
    have : IsProbabilityMeasure (segmentFrom m (r + ((k + 1) + extra)) s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
    exact (phiwScore_decodeSegment_memLp t0 zeta C m hClass j _ s r k
      (by omega) 1).integrable le_rfl
  rw [observedSegment_integral_eq_sum_fixed_start m hClass.finite_state nu hnu _
    (phiwScore_measurable _ _ _ _) hi]
  exact phiwScore_decodeSegment_initial_bias t0 zeta C m hClass j _ nu hnu r k extra

/-- Fixed-start window means at any containing horizon, including an unused suffix. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the sample size](hyp:n),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), [the fallback state](hyp:fallback), [the state](hyp:s),
[the reward symbol](hyp:r), [the history length](hyp:k), and
[the epoch index assumption](hyp:ht), this establishes
[the partial-history importance-weighted score decode segment integral horizon result](goal). -/
-- @node: phiwScore_decodeSegment_integral_horizon
lemma phiwScore_decodeSegment_integral_horizon {T M n : Nat}
    (t0 zeta C : ℝ) (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (fallback s : JointState m.nX m.nH) (r k : Nat) (ht : r + k < n) :
    (∫ path, phiwScore k m.Mx.b (m.Mx.E j)
      (obsProj (decodeSegment (n := n) fallback (s, path))) ⟨r + k, ht⟩
      ∂segmentFrom m n s) =
      Causalean.Mathlib.Probability.FiniteMarkovOscillation.markovOperatorIter
        (listPolicyKernel m m.Mx.b) r (phiwChronologicalMean m j k) s := by
  obtain ⟨extra, hn⟩ : ∃ extra, n = r + ((k + 1) + extra) :=
    ⟨n - (r + k + 1), by omega⟩
  subst n
  exact phiwScore_decodeSegment_integral_eq_behavior_iterate t0 zeta C m hClass
    j fallback s r k extra

/-- Actual observable window expectation equals the chronological mean averaged under the
behavior-propagated initial law, as in roadmap equation (1). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the reward symbol](hyp:r), [the history length](hyp:k), and
[the epoch index assumption](hyp:ht), this establishes
[the partial-history importance-weighted score observed segment integral equality mean result](goal). -/
-- @node: phiwScore_observedSegment_integral_eq_mean
lemma phiwScore_observedSegment_integral_eq_mean {T M n : Nat}
    (t0 zeta C : ℝ) (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (r k : Nat) (ht : r + k < n) :
    (∫ w, phiwScore k m.Mx.b (m.Mx.E j) w ⟨r + k, ht⟩
      ∂((segmentLaw m hClass.finite_state nu n).map obsProj)) =
      ∑ s, Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.markovIterate
        (listPolicyKernel m m.Mx.b) nu r s * phiwChronologicalMean m j k s := by
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
  simp_rw [phiwScore_decodeSegment_integral_horizon t0 zeta C m hClass]
  exact phiw_markovIterate_operator_duality _ _ _ r

/-- Reindex the valid block windows by their unweighted prefix length. For
[the sample size](hyp:n), [the history length](hyp:k), [the f](hyp:f), [the g](hyp:g), and
[the fg assumption](hyp:hfg), this establishes
[the partial-history importance-weighted sum valid windows equality range result](goal). -/
-- @node: phiw_sum_valid_windows_eq_range
lemma phiw_sum_valid_windows_eq_range {n : Nat} (k : Nat) (f : Fin n → ℝ)
    (g : Nat → ℝ) (hfg : ∀ t : Fin n, k ≤ t.val → f t = g (t.val - k)) :
    (∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ k ≤ t.val), f t) =
      ∑ r ∈ Finset.range (n - k), g r := by
  classical
  apply Finset.sum_bij (fun t _ ↦ t.val - k)
  · intro t ht
    have hk := (Finset.mem_filter.mp ht).2
    apply Finset.mem_range.mpr
    omega
  · intro t ht u hu heq
    have hkt := (Finset.mem_filter.mp ht).2
    have hku := (Finset.mem_filter.mp hu).2
    apply Fin.ext
    omega
  · intro r hr
    have hrn := Finset.mem_range.mp hr
    refine ⟨⟨r + k, by omega⟩, ?_, ?_⟩
    · simp
    · simp
  · intro t ht
    exact hfg t (Finset.mem_filter.mp ht).2

/-- The observable raw block expectation is exactly the average of the chronological means;
finite-sum linearity uses the derived window integrability. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu), and
[the history length](hyp:k), this establishes
[the partial-history importance-weighted raw observed segment integral equality mean result](goal). -/
-- @node: phiwRaw_observedSegment_integral_eq_mean
lemma phiwRaw_observedSegment_integral_eq_mean {T M n : Nat}
    (t0 zeta C : ℝ) (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) (k : Nat) :
    (∫ w, phiwRaw k m.Mx.b (m.Mx.E j) w
      ∂((segmentLaw m hClass.finite_state nu n).map obsProj)) =
      (∑ r ∈ Finset.range (n - k), ∑ s,
        Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.markovIterate
          (listPolicyKernel m m.Mx.b) nu r s * phiwChronologicalMean m j k s) /
        (n - k : Nat) := by
  have : IsProbabilityMeasure ((segmentLaw m hClass.finite_state nu n).map obsProj) :=
    observedSegmentLaw_isProbability m hClass.sequential_ignorability.1
      hClass.finite_state nu hnu n
  have hi : ∀ t ∈ Finset.univ.filter (fun t : Fin n ↦ k ≤ t.val),
      Integrable (fun w ↦ phiwScore k m.Mx.b (m.Mx.E j) w t)
        ((segmentLaw m hClass.finite_state nu n).map obsProj) := by
    intro t ht
    have hk := (Finset.mem_filter.mp ht).2
    have heq : t.val - k + k = t.val := by omega
    have h := (phiwScore_observedSegment_memLp (n := n) t0 zeta C m hClass j nu hnu
      (t.val - k) k (by omega) 1).integrable le_rfl
    simpa only [heq, Fin.eta] using h
  simp only [phiwRaw, integral_const_mul]
  rw [integral_finsetSum _ hi]
  have hs := phiw_sum_valid_windows_eq_range k
    (fun t : Fin n ↦ ∫ w, phiwScore k m.Mx.b (m.Mx.E j) w t
      ∂((segmentLaw m hClass.finite_state nu n).map obsProj))
    (fun r ↦ ∑ s,
      Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.markovIterate
        (listPolicyKernel m m.Mx.b) nu r s * phiwChronologicalMean m j k s) (by
      intro t ht
      have heq : t.val - k + k = t.val := by omega
      have h := phiwScore_observedSegment_integral_eq_mean (n := n)
        t0 zeta C m hClass j nu hnu (t.val - k) k (by omega)
      simpa only [heq, Fin.eta] using h)
  rw [hs]
  simp [div_eq_mul_inv, mul_comm]

/-- The bias half of the frozen block-moment lemma, under its actual arbitrary-start observable
segment law. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the sample size](hyp:n), [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), [the initial distribution](hyp:nu),
[the initial distribution assumption](hyp:hnu), [the history length](hyp:k), and
[the history length assumption](hyp:hk), this establishes
[the partial-history importance-weighted raw observed segment bias result](goal). -/
-- @node: phiwRaw_observedSegment_bias
lemma phiwRaw_observedSegment_bias {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (k : Nat) (hk : k < n) :
    |(∫ w, phiwRaw k m.Mx.b (m.Mx.E j) w
      ∂((segmentLaw m hClass.finite_state nu n).map obsProj)) - policyValue m j| ≤
      mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) := by
  rw [phiwRaw_observedSegment_integral_eq_mean t0 zeta C m hClass j nu hnu]
  exact phiwChronologicalMean_average_bias t0 zeta C m hClass j nu hnu (n - k) k (by omega)

/-- The complete raw block average has every Lp regularity needed for variance assembly;
supported bounded windows supply it without a new premise. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the history length](hyp:k), and [the policy](hyp:p), this establishes
[the partial-history importance-weighted raw observed segment membership lp result](goal). -/
-- @node: phiwRaw_observedSegment_memLp
lemma phiwRaw_observedSegment_memLp {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) (k : Nat) (p : ℝ≥0∞) :
    MemLp (phiwRaw k m.Mx.b (m.Mx.E j)) p
      ((segmentLaw m hClass.finite_state nu n).map obsProj) := by
  have hi : ∀ t ∈ Finset.univ.filter (fun t : Fin n ↦ k ≤ t.val),
      MemLp (fun w ↦ phiwScore k m.Mx.b (m.Mx.E j) w t) p
        ((segmentLaw m hClass.finite_state nu n).map obsProj) := by
    intro t ht
    have hk := (Finset.mem_filter.mp ht).2
    have heq : t.val - k + k = t.val := by omega
    have h := phiwScore_observedSegment_memLp (n := n) t0 zeta C m hClass j nu hnu
      (t.val - k) k (by omega) p
    simpa only [heq, Fin.eta] using h
  unfold phiwRaw
  simpa only [Finset.sum_apply] using
    (memLp_finsetSum' _ hi).const_mul (((n - k : Nat) : ℝ)⁻¹)

end CausalSmith.Stat.PomdpPolicyclassRegret
