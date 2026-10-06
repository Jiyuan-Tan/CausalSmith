module
public import Causalean.Stat.Concentration.TailBounds.McDiarmid
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.CategoricalLaw
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.DesignAlgebra
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Occupancy

/-! # Uniform lower tail for within-cell treatment variation

The conditional Gram identity and uniform occupancy bound imply mean Gram at
least epsilon(1-epsilon)n/4 for n≥2 and at most n available cells. Replacing a
coordinate changes the Gram by at most one. McDiarmid gives an exponential
lower tail, weakened to an explicit 1/n bound valid for every positive n.
The n=1 case uses probability≤1 and the explicit constant, since its Gram is zero.

Primary formal reference: [FoML McDiarmid](https://github.com/auto-res/lean-rademacher/blob/main/FoML/Probability/McDiarmid.lean),
re-exported by Causalean.Stat.Concentration.TailBounds.McDiarmid. Its lower-tail
theorem uses a nonnegative deviation and t times the sum of squared oscillations
at most one; here the oscillations are one and t=1/n.
-/

@[expose] public section

noncomputable section

namespace Causalean.Stat.Sample.Stratified.TreatmentRegression

open MeasureTheory Set
open scoped BigOperators

/-- [The good-design Gram threshold per observation](goal) at [overlap margin ε](hyp:epsilon) is
ε(1 − ε)/8. -/
def gramThreshold (epsilon : ℝ) : ℝ := epsilon * (1 - epsilon) / 8

/-- [The uniform Gram lower-tail constant](goal) at [overlap margin ε](hyp:epsilon) is the
reciprocal of twice the squared good-design threshold, 1/(2·(ε(1 − ε)/8)²). -/
def gramTailConstant (epsilon : ℝ) : ℝ := 1 / (2 * gramThreshold epsilon ^ 2)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- Let the design be [n iid draws from a joint probability law ν of a cell and a Boolean
treatment](hyp:n,ν). If [there are at least two observations](hyp:hn),
[the number of cells is at most n](hyp:hcard), [the overlap margin ε is
positive](hyp:epsilon,hepsilon) and [at most one half](hyp:hhalf), and [every cell of positive
probability has propensity between ε and 1 − ε](hyp:hoverlap), then [the expected Gram
denominator is at least twice the good-design threshold times n, that is
ε(1 − ε)n/4](goal).

Sum integral_gram_labelFiber over label vectors, discarding zero-weight
fibers before applying overlap; transport repeatCount to the cell marginal
and apply integral_repeatCount_lower. -/
theorem integral_gram_lower (n : ℕ) (ν : Measure (κ × Bool)) [IsProbabilityMeasure ν]
    (hn : 2 ≤ n) (hcard : Fintype.card κ ≤ n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hhalf : epsilon ≤ 1 / 2)
    (hoverlap : ∀ k, 0 < cellProbability ν k →
      epsilon ≤ propensity ν k ∧ propensity ν k ≤ 1 - epsilon) :
    2 * gramThreshold epsilon * n ≤ ∫ d : Fin n → κ × Bool, gram d
      ∂Measure.pi (fun _ : Fin n => ν) := by
  classical
  let P := Measure.pi (fun _ : Fin n => ν)
  let Q := ν.map Prod.fst
  have hQ : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hfiber (F : (Fin n → κ × Bool) → ℝ) :
      (∫ d, F d ∂P) = ∑ x : Fin n → κ, ∫ d in labelFiber x, F d ∂P := by
    simp_rw [← integral_indicator (Set.to_countable _ |>.measurableSet)]
    rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    apply integral_congr_ae
    filter_upwards with d
    have hx (x : Fin n → κ) : d ∈ labelFiber x ↔ x = fun i => (d i).1 := by
      simp only [labelFiber, mem_ofPred_eq]
      exact ⟨fun h => funext (fun i => (h i).symm), fun h i => congrFun h.symm i⟩
    simp [Set.indicator, hx]
  have hmass (k : κ) : (Q {k}).toReal = cellProbability ν k := by
    dsimp only [Q]
    rw [Measure.map_apply measurable_fst (measurableSet_singleton k)]
    rfl
  have hrepeat :
      (∫ x : Fin n → κ, (repeatCount x : ℝ) ∂Measure.pi (fun _ : Fin n => Q)) =
        ∑ x : Fin n → κ, labelWeight ν x * (repeatCount x : ℝ) := by
    rw [integral_fintype Integrable.of_finite]
    simp [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod, hmass, labelWeight]
  have hlower (x : Fin n → κ) :
      epsilon * (1 - epsilon) * (labelWeight ν x * (repeatCount x : ℝ)) ≤
        ∫ d in labelFiber x, gram d ∂P := by
    have hw : 0 ≤ labelWeight ν x := Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
    by_cases hx : 0 < labelWeight ν x
    · have h := conditional_gram_mean_lower n ν x hx epsilon hepsilon hhalf hoverlap
      have h' := (le_div_iff₀ hx).mp h
      simpa [P, mul_assoc, mul_left_comm, mul_comm] using h'
    · have hz : labelWeight ν x = 0 := le_antisymm (le_of_not_gt hx) hw
      simp [P, integral_gram_labelFiber, hz]
  have hoc := integral_repeatCount_lower n Q hn hcard
  have hp : 0 ≤ epsilon * (1 - epsilon) := mul_nonneg hepsilon.le (by linarith)
  calc
    2 * gramThreshold epsilon * n = epsilon * (1 - epsilon) * ((n : ℝ) / 4) := by
      unfold gramThreshold
      ring
    _ ≤ epsilon * (1 - epsilon) *
        (∫ x : Fin n → κ, (repeatCount x : ℝ) ∂Measure.pi (fun _ : Fin n => Q)) :=
      mul_le_mul_of_nonneg_left hoc hp
    _ = ∑ x : Fin n → κ, epsilon * (1 - epsilon) *
        (labelWeight ν x * (repeatCount x : ℝ)) := by rw [hrepeat, Finset.mul_sum]
    _ ≤ ∑ x : Fin n → κ, ∫ d in labelFiber x, gram d ∂P :=
      Finset.sum_le_sum (fun x _ => hlower x)
    _ = ∫ d, gram d ∂P := (hfiber gram).symm

/-- Let the design be [n iid draws from a joint probability law ν of a cell and a Boolean
treatment](hyp:n,ν). If [there are at least two observations](hyp:hn),
[the number of cells is at most n](hyp:hcard), [the overlap margin ε is
positive](hyp:epsilon,hepsilon) and [at most one half](hyp:hhalf), and [every cell of positive
probability has propensity between ε and 1 − ε](hyp:hoverlap), then [the probability that the
Gram denominator falls below the good-design threshold times n is at most
exp(−2·(ε(1 − ε)/8)²·n)](goal), uniformly over all such laws.

The primary source also supplies mcdiarmid_inequality_neg_iid_of_const;
instantiate X'=id, c=1, deviation=gramThreshold epsilon*n, t=1/n.
Obtain Nonempty (κ × Bool) from the probability law rather than adding an
assumption. Use integral_gram_lower to include the strict bad event in its
nonstrict centered-deviation event; apply ENNReal.toReal_mono since all
probabilities are finite. Normalize the exponent after cancelling positive n. -/
theorem gram_lower_tail_exp (n : ℕ) (ν : Measure (κ × Bool)) [IsProbabilityMeasure ν]
    (hn : 2 ≤ n) (hcard : Fintype.card κ ≤ n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hhalf : epsilon ≤ 1 / 2)
    (hoverlap : ∀ k, 0 < cellProbability ν k →
      epsilon ≤ propensity ν k ∧ propensity ν k ≤ 1 - epsilon) :
    ((Measure.pi (fun _ : Fin n => ν)) {d | gram d < gramThreshold epsilon * n}).toReal ≤
      Real.exp (-2 * gramThreshold epsilon ^ 2 * n) := by
  classical
  have : Nonempty (κ × Bool) := nonempty_of_isProbabilityMeasure ν
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hgpos : 0 < gramThreshold epsilon := by
    unfold gramThreshold
    exact div_pos (mul_pos hepsilon (by linarith)) (by norm_num)
  let P := Measure.pi (fun _ : Fin n => ν)
  have hmean := integral_gram_lower n ν hn hcard epsilon hepsilon hhalf hoverlap
  have ht : (1 / (n : ℝ)) * ∑ _ : Fin n, (1 : ℝ) ^ 2 ≤ 1 := by
    simp [ne_of_gt hnpos]
  have hmc := mcdiarmid_inequality_neg (μ := P)
    (fun (i : Fin n) (d : Fin n → κ × Bool) => d i)
    (fun i => measurable_pi_apply i)
    (pi_comp_eval_iIndepFun (μ := ν) (ι := Fin n) measurable_id)
    gram (fun _ => (1 : ℝ))
    (fun i d v => gram_update_oscillation d i v)
    (measurable_designStatistic gram)
    (gramThreshold epsilon * n) (mul_nonneg hgpos.le hnpos.le)
    (1 / n) ht
  have hmc' :
      (P {d | gram d - (∫ d, gram d ∂P) ≤ -(gramThreshold epsilon * n)}).toReal ≤
        Real.exp (-2 * (gramThreshold epsilon * n) ^ 2 * (1 / n)) := by
    exact hmc
  have hsub : {d : Fin n → κ × Bool | gram d < gramThreshold epsilon * n} ⊆
      {d | gram d - (∫ d, gram d ∂P) ≤ -(gramThreshold epsilon * n)} := by
    intro d hd
    dsimp only [mem_ofPred_eq] at *
    change 2 * gramThreshold epsilon * n ≤ ∫ d, gram d ∂P at hmean
    linarith
  calc
    _ ≤ (P {d | gram d - (∫ d, gram d ∂P) ≤ -(gramThreshold epsilon * n)}).toReal :=
      ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
    _ ≤ Real.exp (-2 * (gramThreshold epsilon * n) ^ 2 * (1 / n)) := hmc'
    _ = _ := by
      congr 1
      field_simp


/-- Let the design be [n iid draws from a joint probability law ν of a cell and a Boolean
treatment](hyp:n,ν). If [there is at least one observation](hyp:hn),
[the number of cells is at most n](hyp:hcard), [the overlap margin ε is
positive](hyp:epsilon,hepsilon) and [at most one half](hyp:hhalf), and [every cell of positive
probability has propensity between ε and 1 − ε](hyp:hoverlap), then [the probability that the
Gram denominator falls below the good-design threshold times n is at most the uniform Gram
lower-tail constant divided by n](goal), including the one-observation case.

For n≥2 weaken the exponential bound with exp(-u)≤1/u for u>0, where
u=2*gramThreshold epsilon^2*n. For n=1 use probability≤1 and bound the
explicit constant from epsilon≤1/2. No occupancy assertion holds at n=1. -/
theorem gram_lower_tail (n : ℕ) (ν : Measure (κ × Bool)) [IsProbabilityMeasure ν]
    (hn : 0 < n) (hcard : Fintype.card κ ≤ n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hhalf : epsilon ≤ 1 / 2)
    (hoverlap : ∀ k, 0 < cellProbability ν k →
      epsilon ≤ propensity ν k ∧ propensity ν k ≤ 1 - epsilon) :
    ((Measure.pi (fun _ : Fin n => ν)) {d | gram d < gramThreshold epsilon * n}).toReal ≤
      gramTailConstant epsilon / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hgpos : 0 < gramThreshold epsilon := by
    unfold gramThreshold
    exact div_pos (mul_pos hepsilon (by linarith)) (by norm_num)
  by_cases hn2 : 2 ≤ n
  · have hu : 0 < 2 * gramThreshold epsilon ^ 2 * (n : ℝ) := by positivity
    have hexp : Real.exp (-(2 * gramThreshold epsilon ^ 2 * (n : ℝ))) ≤
        1 / (2 * gramThreshold epsilon ^ 2 * (n : ℝ)) := by
      rw [Real.exp_neg, ← one_div]
      apply one_div_le_one_div_of_le hu
      linarith [Real.add_one_le_exp (2 * gramThreshold epsilon ^ 2 * (n : ℝ))]
    calc
      _ ≤ Real.exp (-2 * gramThreshold epsilon ^ 2 * n) :=
        gram_lower_tail_exp n ν hn2 hcard epsilon hepsilon hhalf hoverlap
      _ ≤ 1 / (2 * gramThreshold epsilon ^ 2 * (n : ℝ)) := by
        simpa only [neg_mul] using hexp
      _ = gramTailConstant epsilon / n := by
        unfold gramTailConstant
        rw [div_div]
  · have hn1 : n = 1 := by omega
    subst n
    have hgsmall : gramThreshold epsilon ≤ 1 / 8 := by
      unfold gramThreshold
      nlinarith [sq_nonneg epsilon]
    have hdpos : 0 < 2 * gramThreshold epsilon ^ 2 := by positivity
    have hdsmall : 2 * gramThreshold epsilon ^ 2 ≤ 1 := by
      nlinarith
    calc
      _ ≤ 1 := by
        exact ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one)
      _ ≤ gramTailConstant epsilon / (1 : ℕ) := by
        simp only [Nat.cast_one, div_one, gramTailConstant]
        exact (le_div_iff₀ hdpos).mpr (by simpa using hdsmall)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Draw [n iid observations from a probability law μ](hyp:n,μ) carrying [a measurable cell
label X](hyp:X,hX) and [a measurable Boolean treatment A](hyp:A,hA). If [there is at least one
observation](hyp:hn), [the number of cells is at most n](hyp:hcard), [the overlap margin ε is
positive](hyp:epsilon,hepsilon) and [at most one half](hyp:hhalf), and [every cell of positive
probability under the joint law of (X, A) has propensity between ε and 1 − ε](hyp:hoverlap),
then [the probability that the Gram denominator of the observed design falls below the
good-design threshold times n is at most the uniform Gram lower-tail constant divided by
n](goal).

The Gram lower-tail estimate transports to any iid observed probability
law with measurable categorical labels and Boolean treatment and overlap only
in positive-mass cells. No condition is imposed on null cells.

Use observed_design_pushforward and Measure.map_apply with the measurable
bad-design set, then apply gram_lower_tail to the observed joint law. -/
theorem observed_gram_lower_tail (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (hX : Measurable X) (hA : Measurable A)
    (hn : 0 < n) (hcard : Fintype.card κ ≤ n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hhalf : epsilon ≤ 1 / 2)
    (hoverlap : ∀ k, 0 < cellProbability (μ.map (fun ω => (X ω, A ω))) k →
      epsilon ≤ propensity (μ.map (fun ω => (X ω, A ω))) k ∧
        propensity (μ.map (fun ω => (X ω, A ω))) k ≤ 1 - epsilon) :
    ((Measure.pi (fun _ : Fin n => μ))
      {z | gram (Causalean.Stat.sampleDesign X A z) < gramThreshold epsilon * n}).toReal ≤
      gramTailConstant epsilon / n := by
  let ν := μ.map (fun ω => (X ω, A ω))
  have hν : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (hX.prodMk hA).aemeasurable
  have hbad : MeasurableSet {d : Fin n → κ × Bool |
      gram d < gramThreshold epsilon * n} :=
    measurableSet_lt (measurable_designStatistic gram) measurable_const
  have hmap := observed_design_pushforward n μ X A hX hA
  have hevent :
      (Measure.pi (fun _ : Fin n => μ))
        {z | gram (Causalean.Stat.sampleDesign X A z) < gramThreshold epsilon * n} =
      (Measure.pi (fun _ : Fin n => ν)) {d | gram d < gramThreshold epsilon * n} := by
    rw [← hmap, Measure.map_apply
      (Causalean.Stat.measurable_sampleDesign X A hX hA) hbad]
    rfl
  rw [hevent]
  exact gram_lower_tail n ν hn hcard epsilon hepsilon hhalf hoverlap

end Causalean.Stat.Sample.Stratified.TreatmentRegression
