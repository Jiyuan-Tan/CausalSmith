module
public import Causalean.Mathlib.Probability.Certified.FiniteKernel
public import Causalean.Mathlib.Probability.Kernel.FiniteHistory.Expectation

/-!
# Likelihood-weighted finite sequential expectations

This module defines zero-on-null likelihood ratios and transfers bounded weighted history scores
through repeated Markov-kernel extensions to finite-state matrix expressions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Mathlib.Probability.Kernel.FiniteHistory

/-- A [behavior kernel](hyp:behavior), [target kernel](hyp:target), [state](hyp:s), and [action](hyp:a) determine [the zero-on-null likelihood ratio](goal), [given by zero on a behavior-null action and otherwise by the target-to-behavior atom-mass ratio](step:1). -/
noncomputable def actionLikelihood
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype A]
    (behavior target : Kernel S A) (s : S) (a : A) : ℝ :=
  if (behavior s) {a} = 0 then 0
  else ((target s) {a}).toReal / ((behavior s) {a}).toReal

/-- The [behavior kernel](hyp:behavior) and [target kernel](hyp:target) make [their zero-on-null likelihood ratio jointly measurable](goal). -/
@[fun_prop] theorem actionLikelihood_measurable
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype A]
    (behavior target : Kernel S A) :
    Measurable fun z : S × A => actionLikelihood behavior target z.1 z.2 := by
  -- Partition the finite action space into singleton cells. For fixed `a`,
  -- kernel evaluation on `{a}` is measurable in the state.
  apply measurable_from_prod_countable_left
  intro a
  unfold actionLikelihood
  have hb : Measurable (fun s => (behavior s) {a}) :=
    Kernel.measurable_coe behavior (MeasurableSet.singleton a)
  have ht : Measurable (fun s => (target s) {a}) :=
    Kernel.measurable_coe target (MeasurableSet.singleton a)
  exact Measurable.ite (hb (measurableSet_singleton 0)) measurable_const
    (ht.ennreal_toReal.div hb.ennreal_toReal)

/-- Markov [behavior and target kernels](hyp:behavior,target) with [target absolute continuity relative to behavior](hyp:hAC) transform the [action score](hyp:g) at [the selected state](hyp:s) into [the stated likelihood-weighted expectation identity](goal). -/
theorem integral_actionLikelihood
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype A]
    (behavior target : Kernel S A)
    [IsMarkovKernel behavior] [IsMarkovKernel target]
    (hAC : ∀ s, target s ≪ behavior s)
    (s : S) (g : A → ℝ) :
    ∫ a, actionLikelihood behavior target s a * g a ∂behavior s =
      ∫ a, g a ∂target s := by
  -- Convert both integrals into finite sums of atom masses. On a behavior-null
  -- atom, `hAC s` makes the target atom null too; on other atoms cancel the
  -- denominator after converting finite ENNReal masses to real numbers.
  have hbint : Integrable (fun a => actionLikelihood behavior target s a * g a)
      (behavior s) := Integrable.of_finite
  have htint : Integrable g (target s) := Integrable.of_finite
  rw [integral_fintype hbint, integral_fintype htint]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Measure.real, smul_eq_mul]
  by_cases hb : (behavior s) {a} = 0
  · have ht : (target s) {a} = 0 := hAC s hb
    simp [actionLikelihood, hb, ht]
  · have hb' : ((behavior s) {a}).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hb, measure_ne_top _ _⟩
    simp only [actionLikelihood, hb, if_false]
    field_simp

/-- A [kernel](hyp:K), [history append map](hyp:append), [one-step weight](hyp:w), [number of steps](hyp:n), and [terminal score](hyp:f) determine [the iterated weighted value](goal), given by the terminal score at zero steps and by one weighted kernel integration at each successor step. -/
noncomputable def weightedValue
    {H B : Type*} [MeasurableSpace H] [MeasurableSpace B]
    (K : Kernel H B) (append : H → B → H) (w : H → B → ℝ)
    (n : ℕ) (f : H → ℝ) : H → ℝ :=
  match n with
  | 0 => f
  | n + 1 => fun h => ∫ b, w h b * weightedValue K append w n f (append h b) ∂K h

/-- A [transition matrix](hyp:P), [number of steps](hyp:n), and [terminal reward vector](hyp:reward) determine [the finite-state matrix value](goal), given by the reward at zero steps and by one matrix multiplication at each successor step. -/
def matrixValue {S : Type*} [Fintype S]
    (P : Matrix S S ℝ) (n : ℕ) (reward : S → ℝ) : S → ℝ :=
  match n with
  | 0 => reward
  | n + 1 => fun s => ∑ t, P s t * matrixValue P n reward t

private theorem weightedValue_measurable_bounded_aux
    {H B : Type*} [MeasurableSpace H] [MeasurableSpace B]
    (K : Kernel H B) [IsMarkovKernel K]
    (append : H → B → H) (happend : Measurable fun z : H × B => append z.1 z.2)
    (w : H → B → ℝ) (hw : Measurable fun z : H × B => w z.1 z.2)
    (Cw : ℝ) (hw_bound : ∀ h b, |w h b| ≤ Cw)
    (f : H → ℝ) (hf : Measurable f)
    (Cf : ℝ) (hf_bound : ∀ h, |f h| ≤ Cf) :
    ∀ n, Measurable (weightedValue K append w n f) ∧
      ∃ C : ℝ, ∀ h, |weightedValue K append w n f h| ≤ C := by
  intro n
  induction n with
  | zero => exact ⟨hf, Cf, hf_bound⟩
  | succ n ih =>
    rcases ih with ⟨hm, C, hb⟩
    let D : ℝ := max 0 Cw * max 0 C
    have hprod : Measurable (fun z : H × B =>
        w z.1 z.2 * weightedValue K append w n f (append z.1 z.2)) :=
      hw.mul (hm.comp happend)
    have hprod_bound : ∀ h b,
        |w h b * weightedValue K append w n f (append h b)| ≤ D := by
      intro h b
      rw [abs_mul]
      dsimp [D]
      apply mul_le_mul
      · exact (hw_bound h b).trans (le_max_right _ _)
      · exact (hb (append h b)).trans (le_max_right _ _)
      · exact abs_nonneg _
      · exact le_max_left _ _
    constructor
    · change Measurable (fun h => ∫ b,
        w h b * weightedValue K append w n f (append h b) ∂K h)
      exact (hprod.stronglyMeasurable.integral_kernel_prod_right').measurable
    · refine ⟨D, ?_⟩
      intro h
      change |∫ b, w h b * weightedValue K append w n f (append h b) ∂K h| ≤ D
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
        (norm_integral_le_of_norm_le_const (μ := K h)
          (f := fun b => w h b * weightedValue K append w n f (append h b))
          (C := D) (Filter.Eventually.of_forall fun b => by
            simpa only [Real.norm_eq_abs] using hprod_bound h b))

/-- A Markov [kernel](hyp:K), measurable [append map](hyp:append,happend), measurable [weight](hyp:w,hw) with [a uniform bound](hyp:Cw,hw_bound), and measurable [terminal score](hyp:f,hf) with [a uniform bound](hyp:Cf,hf_bound) make [the specified finite weighted value](hyp:n) [measurable](goal). -/
theorem weightedValue_measurable
    {H B : Type*} [MeasurableSpace H] [MeasurableSpace B]
    (K : Kernel H B) [IsMarkovKernel K]
    (append : H → B → H) (happend : Measurable fun z : H × B => append z.1 z.2)
    (w : H → B → ℝ) (hw : Measurable fun z : H × B => w z.1 z.2)
    (Cw : ℝ) (hw_bound : ∀ h b, |w h b| ≤ Cw)
    (f : H → ℝ) (hf : Measurable f)
    (Cf : ℝ) (hf_bound : ∀ h, |f h| ≤ Cf) (n : ℕ) :
    Measurable (weightedValue K append w n f) := by
  -- Induct on `n`; the bound gives integrability of each kernel section and
  -- Mathlib's measurable kernel integral handles the induction step.
  exact (weightedValue_measurable_bounded_aux K append happend w hw Cw hw_bound
    f hf Cf hf_bound n).1

/-- A Markov [kernel](hyp:K), measurable [append map](hyp:append,happend), measurable [weight](hyp:w,hw) with [a uniform bound](hyp:Cw,hw_bound), and measurable [terminal score](hyp:f,hf) with [a uniform bound](hyp:Cf,hf_bound) at [horizon](hyp:n) give [a uniform bound for the specified finite weighted value](goal). -/
theorem weightedValue_bounded
    {H B : Type*} [MeasurableSpace H] [MeasurableSpace B]
    (K : Kernel H B) [IsMarkovKernel K]
    (append : H → B → H) (happend : Measurable fun z : H × B => append z.1 z.2)
    (w : H → B → ℝ) (hw : Measurable fun z : H × B => w z.1 z.2)
    (Cw : ℝ) (hw_bound : ∀ h b, |w h b| ≤ Cw)
    (f : H → ℝ) (hf : Measurable f)
    (Cf : ℝ) (hf_bound : ∀ h, |f h| ≤ Cf) (n : ℕ) :
    ∃ C : ℝ, ∀ h, |weightedValue K append w n f h| ≤ C := by
  -- The bound `Cf * max 1 Cw ^ n` suffices; use the Markov integral bound.
  exact (weightedValue_measurable_bounded_aux K append happend w hw Cw hw_bound
    f hf Cf hf_bound n).2

private theorem weightedValue_succ_right
    {H B : Type*} [MeasurableSpace H] [MeasurableSpace B]
    (K : Kernel H B) (append : H → B → H) (w : H → B → ℝ)
    (n : ℕ) (f : H → ℝ) (h : H) :
    weightedValue K append w n (weightedValue K append w 1 f) h =
      weightedValue K append w (n + 1) f h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [weightedValue]
    congr 1
    funext b
    congr 1
    exact ih (append h b)

private theorem integral_weighted_history_step
    {H B : Type*} [MeasurableSpace H] [MeasurableSpace B]
    (K : Kernel H B) [IsMarkovKernel K]
    (append : H → B → H) (happend : Measurable fun z : H × B => append z.1 z.2)
    (w : H → B → ℝ) (hw : Measurable fun z : H × B => w z.1 z.2)
    (Cw : ℝ) (hw_bound : ∀ h b, |w h b| ≤ Cw)
    (μ : ℕ → Measure H) (hμprob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ : ∀ n, μ (n + 1) = (μ n ⊗ₘ K).map (fun z => append z.1 z.2))
    (weight : ℕ → H → ℝ) (hweight_meas : ∀ n, Measurable (weight n))
    (hweight_bound : ∀ n, ∃ C : ℝ, ∀ h, |weight n h| ≤ C)
    (hweight_step : ∀ n h b, weight (n + 1) (append h b) = weight n h * w h b)
    (g : H → ℝ) (hg : Measurable g)
    (Cg : ℝ) (hg_bound : ∀ h, |g h| ≤ Cg) (k : ℕ) :
    ∫ h, weight (k + 1) h * g h ∂μ (k + 1) =
      ∫ h, weight k h * weightedValue K append w 1 g h ∂μ k := by
  letI := hμprob k
  obtain ⟨Ck, hk_bound⟩ := hweight_bound k
  have hp : Measurable (fun z : H × B =>
      weight k z.1 * (w z.1 z.2 * g (append z.1 z.2))) :=
    ((hweight_meas k).comp measurable_fst).mul (hw.mul (hg.comp happend))
  have hbound : ∀ z : H × B,
      |weight k z.1 * (w z.1 z.2 * g (append z.1 z.2))| ≤
        max 0 Ck * (max 0 Cw * max 0 Cg) := by
    intro z
    simp only [abs_mul]
    gcongr
    · exact (hk_bound z.1).trans (le_max_right _ _)
    · exact (hw_bound z.1 z.2).trans (le_max_right _ _)
    · exact (hg_bound (append z.1 z.2)).trans (le_max_right _ _)
  calc
    ∫ h, weight (k + 1) h * g h ∂μ (k + 1) =
        ∫ z : H × B, weight (k + 1) (append z.1 z.2) * g (append z.1 z.2)
          ∂(μ k ⊗ₘ K) := by
      rw [hμ k]
      exact integral_map_of_stronglyMeasurable happend
        ((hweight_meas (k + 1)).mul hg).stronglyMeasurable
    _ = ∫ z : H × B, weight k z.1 * (w z.1 z.2 * g (append z.1 z.2))
          ∂(μ k ⊗ₘ K) := by
      congr 1
      funext z
      rw [hweight_step]
      ring
    _ = ∫ h, ∫ b, weight k h * (w h b * g (append h b)) ∂K h ∂μ k := by
      exact integral_compProd_bounded (μ k) K (μ k ⊗ₘ K) rfl _ hp _ hbound
    _ = ∫ h, weight k h * weightedValue K append w 1 g h ∂μ k := by
      congr 1
      funext h
      rw [integral_const_mul]
      rfl

/-- A Markov [kernel](hyp:K), measurable [append map](hyp:append,happend), measurable bounded [weight](hyp:w,hw,Cw,hw_bound), a probability [history-law sequence](hyp:μ,hμprob) satisfying [its extension identity](hyp:hμ), measurable bounded [path weights](hyp:weight,hweight_meas,hweight_bound) satisfying [their initial and recursive identities](hyp:hweight0,hweight_step), and a measurable bounded [terminal score](hyp:f,hf,Cf,hf_bound) at [the selected horizon](hyp:n) identify [the weighted terminal expectation](goal). -/
theorem integral_weighted_history
    {H B : Type*} [MeasurableSpace H] [MeasurableSpace B]
    (K : Kernel H B) [IsMarkovKernel K]
    (append : H → B → H) (happend : Measurable fun z : H × B => append z.1 z.2)
    (w : H → B → ℝ) (hw : Measurable fun z : H × B => w z.1 z.2)
    (Cw : ℝ) (hw_bound : ∀ h b, |w h b| ≤ Cw)
    (μ : ℕ → Measure H) (hμprob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ : ∀ n, μ (n + 1) = (μ n ⊗ₘ K).map (fun z => append z.1 z.2))
    (weight : ℕ → H → ℝ) (hweight_meas : ∀ n, Measurable (weight n))
    (hweight_bound : ∀ n, ∃ C : ℝ, ∀ h, |weight n h| ≤ C)
    (hweight0 : ∀ h, weight 0 h = 1)
    (hweight_step : ∀ n h b, weight (n + 1) (append h b) = weight n h * w h b)
    (f : H → ℝ) (hf : Measurable f)
    (Cf : ℝ) (hf_bound : ∀ h, |f h| ≤ Cf) (n : ℕ) :
    ∫ h, weight n h * f h ∂μ n = ∫ h, weightedValue K append w n f h ∂μ 0 := by
  -- Prove the stronger induction statement starting at an arbitrary time `k`.
  -- At a successor use `integral_map` and `integral_compProd_bounded`, then
  -- `hweight_step`. The resulting operator is `T f := weightedValue ... 1 f`.
  -- Its powers satisfy `T ^ (n+1) f = T ^ n (T f)`; this semigroup fact needs
  -- a separate induction because `weightedValue` recurses on the left.
  have hmain : ∀ m k (g : H → ℝ), Measurable g →
      ∀ Cg : ℝ, (∀ h, |g h| ≤ Cg) →
      ∫ h, weight (k + m) h * g h ∂μ (k + m) =
        ∫ h, weight k h * weightedValue K append w m g h ∂μ k := by
    intro m
    induction m with
    | zero =>
      intro k g hg Cg hg_bound
      simp only [Nat.add_zero, weightedValue]
    | succ m ih =>
      intro k g hg Cg hg_bound
      obtain ⟨D, hD⟩ := weightedValue_bounded K append happend w hw Cw hw_bound
        g hg Cg hg_bound 1
      have hgm := weightedValue_measurable K append happend w hw Cw hw_bound
        g hg Cg hg_bound 1
      calc
        ∫ h, weight (k + (m + 1)) h * g h ∂μ (k + (m + 1)) =
            ∫ h, weight ((k + m) + 1) h * g h ∂μ ((k + m) + 1) := by
          rw [Nat.add_succ]
        _ = ∫ h, weight (k + m) h * weightedValue K append w 1 g h ∂μ (k + m) :=
          integral_weighted_history_step K append happend w hw Cw hw_bound
            μ hμprob hμ weight hweight_meas hweight_bound hweight_step g hg Cg hg_bound (k + m)
        _ = ∫ h, weight k h * weightedValue K append w m
            (weightedValue K append w 1 g) h ∂μ k := ih k _ hgm D hD
        _ = ∫ h, weight k h * weightedValue K append w (m + 1) g h ∂μ k := by
          congr 1
          funext h
          rw [weightedValue_succ_right]
  have hresult := hmain n 0 f hf Cf hf_bound
  simpa only [Nat.zero_add, hweight0, one_mul] using hresult

/-- A Markov [kernel](hyp:K), [append map](hyp:append), [weight](hyp:w), [state projection](hyp:state), [target matrix](hyp:P), [supplied weighted action-kernel identity](hyp:hweighted), and [reward](hyp:reward) identify [the weighted value after the selected number of steps](hyp:n) at [the selected history](hyp:h) with [the matrix value](goal). -/
theorem weightedValue_eq_matrixValue
    {H B S : Type*} [MeasurableSpace H] [MeasurableSpace B]
    [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
    (K : Kernel H B) [IsMarkovKernel K]
    (append : H → B → H)
    (w : H → B → ℝ)
    (state : H → S)
    (P : Matrix S S ℝ)
    (hweighted : ∀ (v : S → ℝ), Measurable v → ∀ h,
      (∫ b, w h b * v (state (append h b)) ∂K h) =
        ∑ s, P (state h) s * v s)
    (reward : S → ℝ) (n : ℕ) (h : H) :
    weightedValue K append w n (reward ∘ state) h =
      matrixValue P n reward (state h) := by
  -- Induct on `n`, rewrite the recursive value using the induction hypothesis,
  -- then apply `hweighted` to `matrixValue P n reward`.
  have hm : ∀ m : ℕ, Measurable (matrixValue P m reward) := by
    intro m
    exact measurable_of_finite _
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [weightedValue, matrixValue]
    have heq : (fun b => w h b * weightedValue K append w n (reward ∘ state) (append h b)) =
        (fun b => w h b * matrixValue P n reward (state (append h b))) := by
      funext b
      rw [ih (append h b)]
    rw [heq]
    exact hweighted (matrixValue P n reward) (hm n) h

/-- Let [K be a Markov kernel from histories to increments](hyp:K), with [a jointly measurable map appending an increment to a history](hyp:append,happend) and [a jointly measurable one-step weight bounded in absolute value by a constant](hyp:w,hw,Cw,hw_bound). Let [the step-indexed history laws be probability measures](hyp:μ,hμprob) such that [each next law is the law of the appended history when the history is drawn from the current law and the increment from K](hyp:hμ), and let [the step-indexed path weights be measurable and each bounded](hyp:weight,hweight_meas,hweight_bound), [equal to one at step zero and multiplied by the one-step weight whenever an increment is appended](hyp:hweight0,hweight_step). Suppose [a measurable map sends each history to its current state in a finite state space](hyp:state,hstate) and, for [a matrix P indexed by states](hyp:P), [the K-integral of the one-step weight times any function of the next state equals the P-row average of that function at the current state, for every history](hyp:hweighted). Then for [a reward on states bounded in absolute value by a constant](hyp:reward,hreward,Cr,hreward_bound) and [every number of steps n](hyp:n), [the step-n expectation of the path weight times the reward at the current state equals the step-zero expectation of the n-fold application of P to the reward, evaluated at the initial state](goal). -/
theorem integral_weighted_reward_eq_matrix
    {H B S : Type*} [MeasurableSpace H] [MeasurableSpace B]
    [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
    (K : Kernel H B) [IsMarkovKernel K]
    (append : H → B → H) (happend : Measurable fun z : H × B => append z.1 z.2)
    (w : H → B → ℝ) (hw : Measurable fun z : H × B => w z.1 z.2)
    (Cw : ℝ) (hw_bound : ∀ h b, |w h b| ≤ Cw)
    (μ : ℕ → Measure H) (hμprob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ : ∀ n, μ (n + 1) = (μ n ⊗ₘ K).map (fun z => append z.1 z.2))
    (weight : ℕ → H → ℝ) (hweight_meas : ∀ n, Measurable (weight n))
    (hweight_bound : ∀ n, ∃ C : ℝ, ∀ h, |weight n h| ≤ C)
    (hweight0 : ∀ h, weight 0 h = 1)
    (hweight_step : ∀ n h b, weight (n + 1) (append h b) = weight n h * w h b)
    (state : H → S) (hstate : Measurable state) (P : Matrix S S ℝ)
    (hweighted : ∀ (v : S → ℝ), Measurable v → ∀ h,
      (∫ b, w h b * v (state (append h b)) ∂K h) =
        ∑ s, P (state h) s * v s)
    (reward : S → ℝ) (hreward : Measurable reward)
    (Cr : ℝ) (hreward_bound : ∀ s, |reward s| ≤ Cr) (n : ℕ) :
    ∫ h, weight n h * reward (state h) ∂μ n =
      ∫ h, matrixValue P n reward (state h) ∂μ 0 := by
  -- Compose `integral_weighted_history` and `weightedValue_eq_matrixValue`.
  have hhist := integral_weighted_history K append happend w hw Cw hw_bound μ hμprob hμ
    weight hweight_meas hweight_bound hweight0 hweight_step
    (reward ∘ state) (hreward.comp hstate) Cr (fun h => hreward_bound (state h)) n
  simp only [Function.comp_apply] at hhist
  rw [hhist]
  congr 1
  funext h
  exact weightedValue_eq_matrixValue K append w
    state P hweighted reward n h

end Causalean.Mathlib.Probability.Kernel.FiniteHistory
