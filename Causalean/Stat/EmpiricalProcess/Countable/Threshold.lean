module
public import Causalean.Stat.EmpiricalProcess.Countable.Basic
public import Causalean.Stat.EmpiricalProcess.Countable.OneSidedSkeleton
public import Causalean.Stat.EmpiricalProcess.Countable.PopulationRange

/-!
# Atom-safe population-centered localized thresholds

An affine threshold integrand is an offset plus a marked closed-threshold
indicator. This covers both orientations, signed comparison scores, and fixed
oracle subtraction. One-sided approximation is pointwise at EVERY score,
including all marginal atoms and observed scores. Dominated convergence also
approximates the population centers. A skeleton is chosen INSIDE the actual
eligible cutoff set, preserving localization exactly, including its boundary.
No atomlessness, loss continuity, or sample-dependent class is assumed.
Constants and finitely many extra policies may be adjoined to this countable
class; this does not change its measurability or symmetrization requirements.
For laws supported on a measurable observation subset, use its subtype as
the observation space. Mathlib's integral_subtype_comap identifies its
population centers with restricted integrals, which equal the original
integrals when the law is supported there. Thus the global pointwise bound
is only needed on the actual support.
-/

@[expose] public section

noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- [The affine closed-threshold integrand](goal) with [orientation
flag](hyp:upper), [score, offset, and mark functions](hyp:score,offset,mark),
and [cutoff t](hyp:t), evaluated at [an observation x](hyp:x), is [the
offset at x, plus the mark at x when the score at x is at most t (flag
true) or at least t (flag false)](step:1). -/
def thresholdFunction {Ω : Type*} (upper : Bool) (score offset mark : Ω → ℝ)
    (t : ℝ) (x : Ω) : ℝ :=
  offset x + if (if upper then score x ≤ t else t ≤ score x) then mark x else 0

/-- [The localized threshold supremum](goal) on [a sample x](hyp:x),
relative to [a population law μ](hyp:μ), with [orientation
flag](hyp:upper), [score, offset, and mark
functions](hyp:score,offset,mark), [an admissible cutoff set T](hyp:T), [a
deterministic population loss](hyp:loss), and [a radius z](hyp:z), is [the
centered supremum of the threshold integrands over the cutoffs in T whose
loss is at most z](step:1): each empirical average is centered by its own
population integral. -/
def localizedThresholdSup {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (upper : Bool) (score offset mark : Ω → ℝ) (T : Set ℝ)
    (loss : ℝ → ℝ) (z : ℝ) {n : ℕ} (x : Fin n → Ω) : ℝ :=
  centeredSup μ (fun t : {t : ℝ // t ∈ T ∧ loss t ≤ z} =>
    thresholdFunction upper score offset mark t.1) x

/-- If [the score](hyp:hs), [offset](hyp:ho), and [mark](hyp:hm) are
measurable, then [the affine closed-threshold integrand is measurable at
every fixed cutoff and either orientation](goal). -/
@[fun_prop] theorem thresholdFunction_measurable {Ω : Type*} [MeasurableSpace Ω]
    (upper : Bool) (score offset mark : Ω → ℝ)
    (hs : Measurable score) (ho : Measurable offset) (hm : Measurable mark) (t : ℝ) :
    Measurable (thresholdFunction upper score offset mark t) := by
  cases upper
  · exact ho.add (hm.ite (measurableSet_le measurable_const hs) measurable_const)
  · exact ho.add (hm.ite (measurableSet_le hs measurable_const) measurable_const)

/-- If [a sequence of cutoffs approaches the cutoff t from the side given
by the orientation](hyp:s,t,hs), then [at every observation the affine
closed-threshold integrand at the sequence's cutoffs converges to its value
at t](goal), with exact behavior retained at ties. -/
theorem thresholdFunction_tendsto {Ω : Type*} (upper : Bool)
    (score offset mark : Ω → ℝ) (s : ℕ → ℝ) (t : ℝ)
    (hs : OneSidedApproximates upper s t) (x : Ω) :
    Tendsto (fun k => thresholdFunction upper score offset mark (s k) x)
      atTop (nhds (thresholdFunction upper score offset mark t x)) := by
  -- At score x = t all indicators agree exactly by the one-sided condition.
  -- Away from that tie, convergence of s makes the indicator eventually constant.
  classical
  apply Tendsto.congr' (f₁ := fun _ => thresholdFunction upper score offset mark t x)
    ?_ tendsto_const_nhds
  cases upper
  · by_cases h : t ≤ score x
    · exact Eventually.of_forall fun k => by
        simp [thresholdFunction, h, (hs.1 k).trans h]
    · have he := hs.2.eventually (isOpen_Ioi.mem_nhds (lt_of_not_ge h))
      filter_upwards [he] with k hk
      simp [thresholdFunction, h, not_le_of_gt hk]
  · by_cases h : score x ≤ t
    · exact Eventually.of_forall fun k => by
        simp [thresholdFunction, h, h.trans (hs.1 k)]
    · have he := hs.2.eventually (isOpen_Iio.mem_nhds (lt_of_not_ge h))
      filter_upwards [he] with k hk
      simp [thresholdFunction, h, not_le_of_gt hk]

/-- If [the score is measurable](hyp:hscore), [the offset](hyp:hoffset)
and [the mark are integrable under μ](hyp:μ,hmark), and [a sequence of
cutoffs approaches the cutoff t from the side given by the
orientation](hyp:s,t,hs), then [the population integrals of the affine
closed-threshold integrand at the sequence's cutoffs converge to its
population integral at t](goal). -/
theorem thresholdFunction_integral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (upper : Bool) (score offset mark : Ω → ℝ)
    (hscore : Measurable score) (hoffset : Integrable offset μ)
    (hmark : Integrable mark μ) (s : ℕ → ℝ) (t : ℝ)
    (hs : OneSidedApproximates upper s t) :
    Tendsto (fun k => ∫ x, thresholdFunction upper score offset mark (s k) x ∂μ)
      atTop (nhds (∫ x, thresholdFunction upper score offset mark t x ∂μ)) := by
  -- Dominate by |offset| + |mark|. Integrability supplies AE strong
  -- measurability of those functions, so full offset/mark measurability is unnecessary.
  classical
  have hmeas (u : ℝ) : AEStronglyMeasurable
      (thresholdFunction upper score offset mark u) μ := by
    cases upper
    · exact hoffset.aestronglyMeasurable.add
        (hmark.aestronglyMeasurable.restrict.piecewise
          (measurableSet_le measurable_const hscore) aestronglyMeasurable_zero)
    · exact hoffset.aestronglyMeasurable.add
        (hmark.aestronglyMeasurable.restrict.piecewise
          (measurableSet_le hscore measurable_const) aestronglyMeasurable_zero)
  apply tendsto_integral_of_dominated_convergence
    (fun x => |offset x| + |mark x|) (fun k => hmeas (s k))
    (hoffset.abs.add hmark.abs)
  · intro k
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs]
    unfold thresholdFunction
    split_ifs <;> first
    | exact abs_add_le _ _
    | simpa only [add_zero] using le_add_of_nonneg_right (abs_nonneg (mark x))
  · exact ae_of_all _ (thresholdFunction_tendsto upper score offset mark s t hs)

/-- If [the score is measurable](hyp:hscore), and [the offset](hyp:hoffset)
and [the mark are integrable under μ](hyp:μ,hmark), then for [any admissible
cutoff set](hyp:T), [population loss](hyp:loss), and [radius z](hyp:z),
[there is a countable set of eligible cutoffs (those in the admissible set
with loss at most z) that contains the one-sided boundary of the eligible
set, approximates every eligible cutoff from the correct side both pointwise
and in population integral, and gives exactly the same localized threshold
supremum as the full eligible set for every finite sample](goal). -/
theorem localizedThreshold_countable_reduction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (upper : Bool) (score offset mark : Ω → ℝ)
    (hscore : Measurable score) (hoffset : Integrable offset μ)
    (hmark : Integrable mark μ) (T : Set ℝ) (loss : ℝ → ℝ) (z : ℝ) :
    ∃ D : Set ℝ, D.Countable ∧ D ⊆ {t ∈ T | loss t ≤ z} ∧
      oneSidedBoundary upper {t ∈ T | loss t ≤ z} ⊆ D ∧
      (∀ t ∈ T, loss t ≤ z → ∃ s : ℕ → ℝ,
        (∀ k, s k ∈ D) ∧ OneSidedApproximates upper s t ∧
        (∀ x, Tendsto (fun k => thresholdFunction upper score offset mark (s k) x)
          atTop (nhds (thresholdFunction upper score offset mark t x))) ∧
        Tendsto (fun k => ∫ x, thresholdFunction upper score offset mark (s k) x ∂μ)
          atTop (nhds (∫ x, thresholdFunction upper score offset mark t x ∂μ))) ∧
      (∀ (n : ℕ) (x : Fin n → Ω), localizedThresholdSup μ upper score offset mark
        T loss z x = centeredSup μ (fun t : D =>
          thresholdFunction upper score offset mark t.1) x) := by
  -- Apply exists_countable_oneSided_skeleton to the already-localized set.
  -- Bound all real suprema by the sample offset/mark absolute sums and
  -- their population absolute integrals. Finite sums, subtraction and abs
  -- preserve the pointwise/integral limits, giving both supremum inequalities.
  classical
  let E : Set ℝ := {t ∈ T | loss t ≤ z}
  obtain ⟨D, hD, hDE, hboundary, happrox⟩ :=
    exists_countable_oneSided_skeleton upper E
  refine ⟨D, hD, hDE, hboundary, ?_, ?_⟩
  · intro t ht hz
    obtain ⟨s, hsD, hs⟩ := happrox t ⟨ht, hz⟩
    exact ⟨s, hsD, hs, thresholdFunction_tendsto upper score offset mark s t hs,
      thresholdFunction_integral_tendsto μ upper score offset mark hscore hoffset hmark
        s t hs⟩
  · intro n x
    let F : ℝ → ℝ := fun t =>
      |Causalean.Stat.Concentration.centeredEmpiricalAverage μ x
        (thresholdFunction upper score offset mark t)|
    let G : Ω → ℝ := fun y => |offset y| + |mark y|
    have hG : Integrable G μ := hoffset.abs.add hmark.abs
    have hbound (t : ℝ) (y : Ω) : |thresholdFunction upper score offset mark t y| ≤ G y := by
      unfold thresholdFunction G
      split_ifs <;> first
      | exact abs_add_le _ _
      | simpa only [add_zero] using le_add_of_nonneg_right (abs_nonneg (mark y))
    have hF (t : ℝ) : F t ≤ |(n : ℝ)⁻¹| * ∑ j, G (x j) + ∫ y, G y ∂μ := by
      have hint : |∫ y, thresholdFunction upper score offset mark t y ∂μ| ≤
          ∫ y, G y ∂μ := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_of_norm_le (f := thresholdFunction upper score offset mark t)
            hG (ae_of_all _ (fun y => by
            simpa only [Real.norm_eq_abs] using hbound t y))
      calc
        F t ≤ |(n : ℝ)⁻¹ * ∑ j, thresholdFunction upper score offset mark t (x j)| +
            |∫ y, thresholdFunction upper score offset mark t y ∂μ| := by
          simpa only [F, Causalean.Stat.Concentration.centeredEmpiricalAverage,
            sub_eq_add_neg, abs_neg] using abs_add_le
              ((n : ℝ)⁻¹ * ∑ j, thresholdFunction upper score offset mark t (x j))
              (-(∫ y, thresholdFunction upper score offset mark t y ∂μ))
        _ ≤ |(n : ℝ)⁻¹| * ∑ j, G (x j) + ∫ y, G y ∂μ := by
          rw [abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left
            ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun j _ => hbound t (x j))) (abs_nonneg _)) hint
    have hbed : BddAbove (range (fun t : D => F t.1)) :=
      ⟨_, by rintro _ ⟨t, rfl⟩; exact hF t⟩
    have hbee : BddAbove (range (fun t : E => F t.1)) :=
      ⟨_, by rintro _ ⟨t, rfl⟩; exact hF t⟩
    change (⨆ t : E, F t.1) = ⨆ t : D, F t.1
    rcases isEmpty_or_nonempty E with hempty | hnonempty
    · have : IsEmpty D := ⟨fun t => isEmptyElim (⟨t.1, hDE t.2⟩ : E)⟩
      simp only [iSup_of_empty']
    · have : Nonempty E := hnonempty
      obtain ⟨t⟩ := hnonempty
      obtain ⟨s, hsD, hs⟩ := happrox t.1 t.2
      have : Nonempty D := ⟨⟨s 0, hsD 0⟩⟩
      apply le_antisymm
      · apply ciSup_le
        intro t
        obtain ⟨s, hsD, hs⟩ := happrox t.1 t.2
        have hlim : Tendsto (fun k => F (s k)) atTop (nhds (F t.1)) := by
          apply Tendsto.abs
          apply Tendsto.sub
          · apply Tendsto.const_mul
            apply tendsto_finsetSum
            intro j _
            exact thresholdFunction_tendsto upper score offset mark s t.1 hs (x j)
          · exact thresholdFunction_integral_tendsto μ upper score offset mark
              hscore hoffset hmark s t.1 hs
        exact le_of_tendsto hlim (Eventually.of_forall fun k =>
          le_ciSup hbed (⟨s k, hsD k⟩ : D))
      · exact ciSup_le fun t => le_ciSup hbee (⟨t.1, hDE t.2⟩ : E)

/-- If [the score](hyp:hscore), [offset](hyp:hoffset), and [mark are
measurable](hyp:hmark) and [the offset](hyp:hoint) and [the mark are
integrable under μ](hyp:μ,hmint), then for [any admissible cutoff
set](hyp:T), [population loss](hyp:loss), [radius](hyp:z), and [sample
size](hyp:n), [the localized threshold supremum is a measurable function of
the sample](goal).

The offset and mark may be unbounded at exceptional observation points.
-/
@[fun_prop] theorem localizedThresholdSup_measurable_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (upper : Bool)
    (score offset mark : Ω → ℝ) (hscore : Measurable score)
    (hoffset : Measurable offset) (hmark : Measurable mark)
    (hoint : Integrable offset μ) (hmint : Integrable mark μ)
    (T : Set ℝ) (loss : ℝ → ℝ) (z : ℝ) (n : ℕ) :
    Measurable (localizedThresholdSup μ upper score offset mark T loss z (n := n)) := by
  -- Obtain a fixed eligible D from localizedThreshold_countable_reduction.
  -- Each centered empirical evaluation on D is measurable: it is a
  -- finite measurable sum minus a fixed population integral. Measurable.iSup
  -- applies even if D is empty. The pointwise sample envelopes used in
  -- the reduction need not be uniformly bounded across observation points.
  classical
  obtain ⟨D, hD, _, _, _, heq⟩ := localizedThreshold_countable_reduction
    μ upper score offset mark hscore hoint hmint T loss z
  have : Countable D := hD.to_subtype
  have hm : Measurable (fun x : Fin n → Ω => centeredSup μ
      (fun t : D => thresholdFunction upper score offset mark t.1) x) := by
    apply Measurable.iSup
    intro t
    apply continuous_abs.measurable.comp
    apply Measurable.sub _ measurable_const
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro j _
    exact (thresholdFunction_measurable upper score offset mark hscore hoffset hmark t.1).comp
      (measurable_pi_apply j)
  have heqfun := funext (heq n)
  rw [heqfun]
  exact hm

/-- Under [a probability law μ](hyp:μ), if [the score](hyp:hscore),
[offset](hyp:hoffset), and [mark are measurable](hyp:hmark) and [the sum of
the absolute offset and absolute mark is bounded everywhere](hyp:hb) by [a
nonnegative constant K](hyp:K,hK), then for [any admissible cutoff
set](hyp:T), [population loss](hyp:loss), [radius](hyp:z), and [sample
size](hyp:n), [the localized threshold supremum is a measurable function of
the sample](goal).

This holds even at atoms of the score and at the localization boundary.
-/
@[fun_prop] theorem localizedThresholdSup_measurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (upper : Bool)
    (score offset mark : Ω → ℝ) (hscore : Measurable score)
    (hoffset : Measurable offset) (hmark : Measurable mark) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ x, |offset x| + |mark x| ≤ K) (T : Set ℝ) (loss : ℝ → ℝ)
    (z : ℝ) (n : ℕ) :
    Measurable (localizedThresholdSup μ upper score offset mark T loss z (n := n)) := by
  have hKabs : |K| = K := abs_of_nonneg hK
  apply localizedThresholdSup_measurable_of_integrable μ upper score offset mark
    hscore hoffset hmark ?_ ?_ T loss z n
  · exact Integrable.of_bound hoffset.aestronglyMeasurable |K|
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, hKabs]
        exact (le_add_of_nonneg_right (abs_nonneg (mark x))).trans (hb x)))
  · exact Integrable.of_bound hmark.aestronglyMeasurable |K|
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, hKabs]
        exact (le_add_of_nonneg_left (abs_nonneg (offset x))).trans (hb x)))

end Causalean.Stat.EmpiricalProcess.Countable
