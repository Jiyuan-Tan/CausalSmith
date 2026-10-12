module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.ReferenceLaw
public import Mathlib.Probability.Independence.Integration

/-!
# Conditional likelihood-ratio bit moments

The true-arrow moment is the next nonedge moment. Bounded likelihood ratios
control it by the nonedge moment, uniformly at the perfect-sensitivity endpoint.
Distinct report coordinates factor, and the planted marginal integrates as a
finite average of fixed-matching acquisition laws.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

/-- The explicit moment under a Bernoulli report probability. -/
-- @node: reportBitMoment
def reportBitMoment (p q r : ℝ) (a : ℕ) : ℝ :=
  p * edgeRatio q r true ^ a + (1-p) * edgeRatio q r false ^ a

/-- Given [the stated assumptions](hyp:hr,hr1,hrq), [Every likelihood ratio is bounded by the positive-report ratio.](goal) -/
-- @node: edgeRatio_le_positive_ratio
lemma edgeRatio_le_positive_ratio (q r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hrq : r ≤ q) (b : Bool) : edgeRatio q r b ≤ q/r := by
  have he : ¬(r = 1 ∧ q = 1) := by intro h; linarith [h.1]
  cases b
  · simp only [edgeRatio, if_neg (ne_of_gt hr), if_neg he, Bool.coe_false, if_false]
    apply (div_le_div_iff₀ (sub_pos.mpr hr1) hr).mpr
    nlinarith
  · simp [edgeRatio, ne_of_gt hr, he]

/-- Given [the stated assumptions](hyp:hr,hr1), [Changing a nonedge to a true edge shifts the likelihood-ratio moment order.](goal) -/
-- @node: reportBitMoment_true_shift
lemma reportBitMoment_true_shift (q r : ℝ) (hr : 0 < r) (hr1 : r < 1) (a : ℕ) :
    reportBitMoment q q r a = reportBitMoment r q r (a+1) := by
  have he : ¬(r = 1 ∧ q = 1) := by intro h; linarith [h.1]
  have ht : r * edgeRatio q r true = q := by
    simp only [edgeRatio, if_neg (ne_of_gt hr), if_neg he, if_true]
    exact mul_div_cancel₀ _ (ne_of_gt hr)
  have hf : (1-r) * edgeRatio q r false = 1-q := by
    simp only [edgeRatio, if_neg (ne_of_gt hr), if_neg he, Bool.coe_false, if_false]
    exact mul_div_cancel₀ _ (ne_of_gt (sub_pos.mpr hr1))
  simp only [reportBitMoment, pow_succ]
  calc
    _ = (r * edgeRatio q r true) * edgeRatio q r true ^ a +
      ((1-r) * edgeRatio q r false) * edgeRatio q r false ^ a := by rw [ht, hf]
    _ = _ := by ring

/-- Given [the stated assumptions](hyp:hr,hr1,hrq,hq), [A true-edge moment is bounded by B times the corresponding nonedge moment.](goal) -/
-- @node: reportBitMoment_true_le
lemma reportBitMoment_true_le (q r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hrq : r ≤ q) (hq : q ≤ 1) (a : ℕ) :
    reportBitMoment q q r a ≤ (q/r) * reportBitMoment r q r a := by
  rw [reportBitMoment_true_shift q r hr hr1 a]
  have hw (b : Bool) := edgeRatio_nonneg q r ⟨hr.le, hrq, hq⟩ b
  have hb (b : Bool) := edgeRatio_le_positive_ratio q r hr hr1 hrq b
  unfold reportBitMoment
  simp only [pow_succ]
  have ht := mul_le_mul_of_nonneg_left (hb true)
    (mul_nonneg hr.le (pow_nonneg (hw true) a))
  have hf := mul_le_mul_of_nonneg_left (hb false)
    (mul_nonneg (sub_nonneg.mpr hr1.le) (pow_nonneg (hw false) a))
  nlinarith

/-- Given [the stated assumptions](hyp:hp,hqr), [All report moments on admissible channels are nonnegative.](goal) -/
-- @node: reportBitMoment_nonneg
lemma reportBitMoment_nonneg (p q r : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hqr : ChannelDomain q r) (a : ℕ) : 0 ≤ reportBitMoment p q r a := by
  exact add_nonneg (mul_nonneg hp.1 (pow_nonneg (edgeRatio_nonneg q r hqr true) a))
    (mul_nonneg (sub_nonneg.mpr hp.2) (pow_nonneg (edgeRatio_nonneg q r hqr false) a))

/-- Given [the stated assumptions](hyp:hp), [The Bernoulli integral equals its two explicit report contributions.](goal) -/
-- @node: integral_edgeRatio_power_bit
lemma integral_edgeRatio_power_bit (p q r : ℝ) (hp : p ∈ Set.Icc 0 1) (a : ℕ) :
    (∫ b, edgeRatio q r b ^ a
      ∂CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw p) =
      reportBitMoment p q r a := by
  rw [show CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw p =
    Causalean.Mathlib.Probability.bernoulliBool p from add_comm _ _]
  rw [Causalean.Mathlib.Probability.bernoulliBool_integral hp.1 hp.2]
  rfl

/-- Given [the stated assumptions](hyp:hp,hf), [Distinct acquisition coordinates factor into explicit one-bit moments.](goal) -/
-- @node: integral_edgeRatio_power_pi
lemma integral_edgeRatio_power_pi {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (hp : ∀ i, p i ∈ Set.Icc 0 1) (q r : ℝ)
    (f : κ → ι) (hf : Function.Injective f) (s : Finset κ) (a : κ → ℕ) :
    (∫ H, ∏ e ∈ s, edgeRatio q r (H (f e)) ^ a e
      ∂Measure.pi (fun i => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (p i))) =
      ∏ e ∈ s, reportBitMoment (p (f e)) q r (a e) := by
  let μ := fun i => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (p i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability _ (hp i)
  have hind : iIndepFun (fun (e : s) (H : ι → Bool) => H (f e)) (Measure.pi μ) := by
    exact (iIndepFun_pi (X := fun (_ : ι) (b : Bool) => b)
      (by intro i; fun_prop)).precomp (hf.comp Subtype.val_injective)
  simp_rw [← Finset.prod_coe_sort s]
  rw [hind.integral_fun_prod_comp (f := fun (e : s) (b : Bool) => edgeRatio q r b ^ a e) (fun e => (measurable_pi_apply (f e)).aemeasurable) (by intro e; fun_prop)]
  apply Finset.prod_congr rfl
  intro e _
  rw [integral_comp_eval (μ := μ) (i := f e) (f := fun b : Bool => edgeRatio q r b ^ a e) (by fun_prop)]
  exact integral_edgeRatio_power_bit _ q r (hp _) _

/-- [Merge two edge products, retaining multiplicity two on their intersection.](goal) -/
-- @node: edge_products_merge
lemma edge_products_merge {ι : Type*} [DecidableEq ι] (s t : Finset ι) (w : ι → ℝ) :
    (∏ e ∈ s, w e) * (∏ e ∈ t, w e) =
      ∏ e ∈ s ∪ t, w e ^ (if e ∈ s ∩ t then 2 else 1) := by
  calc
    _ = (∏ e ∈ s ∪ t, w e) * ∏ e ∈ s ∩ t, w e :=
      Finset.prod_union_inter.symm
    _ = ∏ e ∈ s ∪ t, w e * (if e ∈ s ∩ t then w e else 1) := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_filter]
      have hfilter : (s ∪ t).filter (fun e => e ∈ s ∩ t) = s ∩ t := by
        ext e; simp; tauto
      rw [hfilter]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro e he
      split_ifs <;> simp [pow_two]

/-- Given [the stated assumptions](hyp:hfit,hqr), [A planted graph integral is a finite average over its legal fixed matchings.](goal) -/
-- @node: integral_plantedGraphLaw
lemma integral_plantedGraphLaw (n m : ℕ) (hfit : 2 * m ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) (g : Acq (Fin n) → ℝ) :
    (∫ H, g H ∂plantedGraphLaw n m hfit q r) =
      ∑ M : Matching m, matchingPriorMass m M *
        ∫ H, g H ∂acquisitionLaw (matchingGraphSchedule n m hfit M) q r := by
  have hmix : plantedGraphLaw n m hfit q r =
      ∑ M : Matching m, ENNReal.ofReal (matchingPriorMass m M) •
        acquisitionLaw (matchingGraphSchedule n m hfit M) q r := by
    unfold plantedGraphLaw matchingPrior
    rw [← Measure.sum_fintype, Measure.bind_sum _ _ Measurable.of_discrete.aemeasurable, Measure.sum_fintype]
    simp_rw [Measure.bind_smul, Measure.dirac_bind (f := fun M => acquisitionLaw (matchingGraphSchedule n m hfit M) q r) Measurable.of_discrete]
  have hprob (M : Matching m) :=
    acquisitionLaw_probability q r hqr (matchingGraphSchedule n m hfit M)
  rw [hmix, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro M _
    rw [integral_smul_measure, ENNReal.toReal_ofReal (matchingPriorMass_nonneg m M)]
    rfl
  · intro M _
    let := hprob M
    exact (Integrable.of_finite (μ := acquisitionLaw (matchingGraphSchedule n m hfit M) q r)
      (f := g)).smul_measure ENNReal.ofReal_ne_top

end CausalSmith.Experimentation.NoisygraphTtePrecision
