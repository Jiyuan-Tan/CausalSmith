module
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.TreatmentMoments

/-! # Categorical conditioning, including null cells

An arbitrary joint law of a finite cell and a Boolean treatment is disintegrated
by explicit finite sums. Treatment propensity is guarded at zero cell mass;
zero-mass label vectors have zero product weight. The fixed-label Gram identity
is consequently a genuine conditional expectation statement on every occupied
label fiber, without requiring overlap in null cells.
-/

@[expose] public section

noncomputable section

namespace Causalean.Stat.Sample.Stratified.TreatmentRegression

open MeasureTheory Set
open scoped BigOperators

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- [The cell probability](goal) of [a cell k](hyp:k) under [a joint law ν of a cell and a Boolean
treatment](hyp:ν) is the mass ν assigns to that cell, summed over both treatment values, as a real
number. -/
def cellProbability (ν : Measure (κ × Bool)) (k : κ) : ℝ :=
  (ν {v | v.1 = k}).toReal

/-- [The treatment propensity](goal) of [a cell k](hyp:k) under [a joint law ν of a cell and a
Boolean treatment](hyp:ν) is the mass of the treated pair (k, true) divided by the cell
probability of k, with value zero in a null cell. -/
def propensity (ν : Measure (κ × Bool)) (k : κ) : ℝ :=
  if cellProbability ν k = 0 then 0 else (ν {(k, true)}).toReal / cellProbability ν k

/-- [The product weight](goal) of [a fixed vector x of n cell labels](hyp:n,x) under
[a joint law ν of a cell and a Boolean treatment](hyp:ν) is the product of the cell
probabilities of its labels. -/
def labelWeight {n : ℕ} (ν : Measure (κ × Bool)) (x : Fin n → κ) : ℝ :=
  ∏ i, cellProbability ν (x i)

/-- [The label fiber](goal) of [a vector x of n cell labels](hyp:n,x) is the set of designs of n
cell-treatment pairs whose cell coordinates equal x. -/
def labelFiber {n : ℕ} (x : Fin n → κ) : Set (Fin n → κ × Bool) :=
  {d | ∀ i, (d i).1 = x i}

omit [Fintype κ] [DecidableEq κ] in
/-- Under [a joint probability law ν of a cell and a Boolean treatment](hyp:ν),
[the mass of each pair of a cell k and a treatment value a](hyp:k,a) [equals the cell probability
of k times the guarded propensity of k when a is true, or times one minus it when a is
false](goal); both sides vanish in null cells. -/
lemma singleton_probability_factor (ν : Measure (κ × Bool)) [IsProbabilityMeasure ν]
    (k : κ) (a : Bool) :
    (ν {(k, a)}).toReal = cellProbability ν k *
      (if a then propensity ν k else 1 - propensity ν k) := by
  have hsubset (b : Bool) : ({(k, b)} : Set (κ × Bool)) ⊆ {v | v.1 = k} := by
    rintro v rfl
    rfl
  have hle (b : Bool) : (ν {(k, b)}).toReal ≤ cellProbability ν k :=
    ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (hsubset b))
  have hsum : cellProbability ν k = (ν {(k, false)}).toReal +
      (ν {(k, true)}).toReal := by
    have hs : {v : κ × Bool | v.1 = k} = {(k, false)} ∪ {(k, true)} := by
      ext v
      rcases v with ⟨j, b⟩
      cases b <;> simp
    rw [cellProbability, hs, measure_union (by simp) (measurableSet_singleton _),
      ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _)]
  by_cases hk : cellProbability ν k = 0
  · have ha : (ν {(k, a)}).toReal = 0 :=
      le_antisymm (by simpa [hk] using hle a) ENNReal.toReal_nonneg
    simp [ha, hk]
  · cases a <;> simp only [Bool.false_eq_true, if_false, if_true, propensity, hk]
    · field_simp
      linarith [hsum]
    · field_simp

omit [Fintype κ] [DecidableEq κ] in
/-- Under [a joint probability law ν of a cell and a Boolean treatment](hyp:ν),
[the guarded propensity of every cell k](hyp:k) [lies between zero and one](goal), including at
null cells. -/
lemma propensity_mem_Icc (ν : Measure (κ × Bool)) [IsProbabilityMeasure ν] (k : κ) :
    propensity ν k ∈ Icc (0 : ℝ) 1 := by
  have hle : (ν {(k, true)}).toReal ≤ cellProbability ν k := by
    apply ENNReal.toReal_mono (measure_ne_top ν _)
    apply measure_mono
    rintro v rfl
    rfl
  by_cases hk : cellProbability ν k = 0
  · simp [propensity, hk]
  · have hp : 0 < cellProbability ν k :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hk)
    simp only [propensity, hk, if_false, mem_Icc]
    exact ⟨div_nonneg ENNReal.toReal_nonneg hp.le, (div_le_one hp).mpr hle⟩

omit [Fintype κ] [DecidableEq κ] in
/-- Under [the n-fold product of a joint probability law ν of a cell and a Boolean
treatment](hyp:n,ν), [the integral of any real statistic F of the design](hyp:F) over
[the label fiber of a fixed label vector x](hyp:x) [equals the product weight of x times the sum,
over all Boolean treatment assignments, of the assignment's conditional weight under the
propensities of ν times F evaluated at the design pairing x with that assignment](goal).

The cell type is not required to be finite in this bridge. Express the fiber
as the finite image of Boolean vectors, use setIntegral_finset and
Measure.pi_singleton, then apply singleton_probability_factor. No overlap
assumption and no positive fiber mass are needed for this unnormalized identity. -/
theorem integral_labelFiber (n : ℕ) (ν : Measure (κ × Bool)) [IsProbabilityMeasure ν]
    (x : Fin n → κ) (F : (Fin n → κ × Bool) → ℝ) :
    (∫ d in labelFiber x, F d ∂Measure.pi (fun _ : Fin n => ν)) =
      labelWeight ν x * ∑ a : Fin n → Bool,
        assignmentWeight (propensity ν) x a * F (fun i => (x i, a i)) := by
  classical
  let g : (Fin n → Bool) → (Fin n → κ × Bool) := fun a i => (x i, a i)
  have hg : Function.Injective g := by
    intro a b h
    funext i
    exact congrArg Prod.snd (congrFun h i)
  let s := Finset.univ.image g
  have hs : labelFiber x = (s : Set (Fin n → κ × Bool)) := by
    ext d
    constructor
    · intro hd
      apply Finset.mem_image.mpr
      refine ⟨fun i => (d i).2, Finset.mem_univ _, ?_⟩
      funext i
      exact Prod.ext (hd i).symm rfl
    · intro hd
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hd
      intro i
      rfl
  rw [hs, setIntegral_finset s IntegrableOn.finset]
  rw [Finset.sum_image (fun a _ b _ h => hg h)]
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod,
    smul_eq_mul, g, singleton_probability_factor]
  simp only [labelWeight, assignmentWeight, Finset.prod_mul_distrib,
    Finset.mul_sum, mul_assoc]

omit [Fintype κ] [DecidableEq κ] in
/-- Under [the n-fold product of a joint probability law ν of a cell and a Boolean
treatment](hyp:n,ν), [the mass of the label fiber of a fixed label vector x](hyp:x)
[equals the product weight of x, the product of its cell probabilities](goal). -/
lemma probability_labelFiber (n : ℕ) (ν : Measure (κ × Bool)) [IsProbabilityMeasure ν]
    (x : Fin n → κ) :
    ((Measure.pi (fun _ : Fin n => ν)) (labelFiber x)).toReal = labelWeight ν x := by
  simpa [sum_assignmentWeight, measureReal_def] using
    integral_labelFiber n ν x (fun _ => (1 : ℝ))

/-- Under [the n-fold product of a joint probability law ν of a cell and a Boolean
treatment](hyp:n,ν), [the integral of the Gram denominator over the label fiber of a fixed label
vector x](hyp:x) [equals the product weight of x times the sum over cells of (N − 1)₊·π(1 − π),
where N is the cell count in x and π the propensity of the cell](goal); this holds also for null
label fibers. -/
theorem integral_gram_labelFiber (n : ℕ) (ν : Measure (κ × Bool))
    [IsProbabilityMeasure ν] (x : Fin n → κ) :
    (∫ d in labelFiber x, gram d ∂Measure.pi (fun _ : Fin n => ν)) =
      labelWeight ν x * ∑ k, (cellCount x k - 1 : ℕ) *
        propensity ν k * (1 - propensity ν k) := by
  rw [integral_labelFiber, assignment_gram_mean]

/-- Under [the n-fold product of a joint probability law ν of a cell and a Boolean
treatment](hyp:n,ν), if [a fixed label vector x has positive product weight](hyp:x,hx), then
[the conditional mean of the Gram denominator given the labels x — its integral over the label
fiber divided by the fiber's weight — equals the sum over cells of (N − 1)₊·π(1 − π), where N is
the cell count in x and π the propensity of the cell](goal). -/
theorem conditional_gram_mean (n : ℕ) (ν : Measure (κ × Bool))
    [IsProbabilityMeasure ν] (x : Fin n → κ) (hx : 0 < labelWeight ν x) :
    (∫ d in labelFiber x, gram d ∂Measure.pi (fun _ : Fin n => ν)) /
        labelWeight ν x =
      ∑ k, (cellCount x k - 1 : ℕ) * propensity ν k * (1 - propensity ν k) := by
  rw [integral_gram_labelFiber]
  field_simp [ne_of_gt hx]

/-- Under [the n-fold product of a joint probability law ν of a cell and a Boolean
treatment](hyp:n,ν), if [a fixed label vector x has positive product weight](hyp:x,hx),
[ε is an overlap margin](hyp:epsilon) and
[every cell of positive probability has propensity between ε and 1 − ε](hyp:hoverlap), then
[the conditional mean of the Gram denominator given the labels x is at least ε(1 − ε) times the
repeat count of x](goal).

Occupied-cell overlap lower bounds the conditional Gram mean on every
positive-mass label fiber by epsilon(1-epsilon) times its repeat count. -/
theorem conditional_gram_mean_lower (n : ℕ) (ν : Measure (κ × Bool))
    [IsProbabilityMeasure ν] (x : Fin n → κ) (hx : 0 < labelWeight ν x)
    (epsilon : ℝ)
    (hoverlap : ∀ k, 0 < cellProbability ν k →
      epsilon ≤ propensity ν k ∧ propensity ν k ≤ 1 - epsilon) :
    epsilon * (1 - epsilon) * (repeatCount x : ℝ) ≤
      (∫ d in labelFiber x, gram d ∂Measure.pi (fun _ : Fin n => ν)) / labelWeight ν x := by
  have hocc : ∀ k, 0 < cellCount x k →
      epsilon ≤ propensity ν k ∧ propensity ν k ≤ 1 - epsilon := by
    intro k hk
    have hex : ∃ i, x i = k := by
      by_contra h
      have hz : cellCount x k = 0 := by
        simp [cellCount, not_exists.mp h]
      omega
    obtain ⟨i, hi⟩ := hex
    have hn : ∀ j : Fin n, cellProbability ν (x j) ≠ 0 := by
      intro j
      exact (Finset.prod_ne_zero_iff.mp (ne_of_gt hx)) j (Finset.mem_univ j)
    apply hoverlap k
    rw [← hi]
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm (hn i))
  rw [conditional_gram_mean n ν x hx, ← assignment_gram_mean]
  exact assignment_gram_mean_lower (propensity ν) x epsilon hocc

end Causalean.Stat.Sample.Stratified.TreatmentRegression
