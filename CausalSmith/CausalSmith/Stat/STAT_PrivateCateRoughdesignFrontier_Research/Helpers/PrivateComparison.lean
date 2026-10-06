module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
/-! Private Hamming comparison, unrestricted Markov contraction, and finite-chi-square TV bounds. -/
public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign
/-- A composed probability kernel evaluates an event by averaging its row probabilities.  [the theorem's stated inputs and assumptions](hyp:K,Q,E,hE), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:α,β). -/
-- @node: kernel_comp_real
lemma kernel_comp_real {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α β) [IsMarkovKernel K] (Q : Measure α) [IsProbabilityMeasure Q]
    (E : Set β) (hE : MeasurableSet E) :
    (K ∘ₘ Q).real E = ∫ x, (K x).real E ∂Q := by
  rw [measureReal_def, Measure.bind_apply hE K.aemeasurable]
  exact (integral_toReal (K.measurable_coe hE).aemeasurable
    (Filter.Eventually.of_forall fun x => measure_lt_top (K x) E)).symm

/-- Averaging a Markov kernel contracts total variation, by the bounded-function dual bound.  [the theorem's stated inputs and assumptions](hyp:K,Q,Q'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:α,β). -/
-- @node: kernel_TV_contraction
lemma kernel_TV_contraction {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α β) [IsMarkovKernel K] (Q Q' : Measure α)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] :
    TV (K ∘ₘ Q) (K ∘ₘ Q') ≤ TV Q Q' := by
  refine ciSup_le fun E => ?_
  rw [kernel_comp_real K Q E.1 E.2, kernel_comp_real K Q' E.1 E.2]
  simpa using Causalean.Stat.tvDist_integral_range Q Q'
    (fun x => (K x).real E.1) (K.measurable_coe E.2).ennreal_toReal
    0 1 (by norm_num) (fun x => ⟨measureReal_nonneg, by simp [measureReal_le_one]⟩)

/-- Finite squared density deviation supplies the integrability needed for the chi-square TV bound.  [the theorem's stated inputs and assumptions](hyp:Q,Q',hac,hf), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:α). -/
-- @node: TV_le_sqrt_chiSq_of_finite
lemma TV_le_sqrt_chiSq_of_finite {α : Type*} [MeasurableSpace α]
    (Q Q' : Measure α) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (hac : Q ≪ Q')
    (hf : (∫⁻ z, ENNReal.ofReal (((Q.rnDeriv Q' z).toReal - 1)^2) ∂Q') < ⊤) :
    TV Q Q' ≤ 1/2 * Real.sqrt (Causalean.Stat.chiSqDiv Q Q') := by
  apply Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv Q Q' hac
  apply (lintegral_ofReal_ne_top_iff_integrable
    (((Q.measurable_rnDeriv Q').ennreal_toReal.sub_const 1).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => sq_nonneg _)).mp
  exact hf.ne

/-- Convexity on the unit interval bounds the privacy exponential increment.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:epsilon,he). -/
-- @node: exp_privacy_increment_le
lemma exp_privacy_increment_le (epsilon : ℝ) (he : 0 ≤ epsilon ∧ epsilon ≤ 1) :
    Real.exp epsilon - 1 ≤ 2 * epsilon := by
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (show 0 ≤ 1 - epsilon by linarith) he.1 (show 1 - epsilon + epsilon = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at hc
  nlinarith [Real.exp_one_lt_three]

/-- Privacy in both directions bounds the event-probability change on an adjacent pair.  [the theorem's stated inputs and assumptions](hyp:he,B,M,hM,D,D',hadj,E,hE), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon). -/
-- @node: private_adjacent_event_bound
lemma private_adjacent_event_bound (n : ℕ) (epsilon : ℝ)
    (he : 0 < epsilon ∧ epsilon ≤ 1) {B : Type*} [MeasurableSpace B]
    (M : Kernel (Dataset n) B) [IsMarkovKernel M]
    (hM : PrivateKernel n epsilon M) (D D' : Dataset n)
    (hadj : dHam n D D' = 1) (E : Set B) (hE : MeasurableSet E) :
    |(M D).real E - (M D').real E| ≤ 2 * epsilon := by
  have hf := hM.pure_privacy D D' hadj E hE
  have hr := hM.pure_privacy D' D (by simpa [dHam, hammingDist_comm] using hadj) E hE
  have hc : 0 ≤ Real.exp epsilon - 1 := sub_nonneg.mpr (Real.one_le_exp he.1.le)
  have hD := mul_le_mul_of_nonneg_left
    (measureReal_le_one (μ := M D) (s := E)) hc
  have hD' := mul_le_mul_of_nonneg_left
    (measureReal_le_one (μ := M D') (s := E)) hc
  have hexp := exp_privacy_increment_le epsilon ⟨he.1.le, he.2⟩
  rw [abs_le]
  constructor <;> nlinarith

/-- A one-coordinate oscillation bound sums along the finite Hamming replacement path.  [the theorem's stated inputs and assumptions](hyp:hstep,D,D'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,f,c,hc). -/
-- @node: event_bound_of_hamming_path
lemma event_bound_of_hamming_path (n : ℕ) (f : Dataset n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ D D', dHam n D D' = 1 → |f D - f D'| ≤ c)
    (D D' : Dataset n) : |f D - f D'| ≤ c * dHam n D D' := by
  classical
  have hfinite (s : Finset (Fin n)) : ∀ D D' : Dataset n,
      (∀ i, i ∉ s → D i = D' i) → |f D - f D'| ≤ c * s.card := by
    induction s using Finset.induction_on with
    | empty =>
      intro D D' h
      have heq : D = D' := funext fun i => h i (by simp)
      simp [heq]
    | @insert i s hi ih =>
      intro D D' h
      let Dmid := Function.update D i (D' i)
      have hagree : ∀ j, j ∉ s → Dmid j = D' j := by
        intro j hj
        by_cases hji : j = i
        · subst j; simp [Dmid]
        · simp only [Dmid, Function.update_of_ne hji]
          exact h j (by simp [hj, hji])
      have hrest := ih Dmid D' hagree
      have hfirst : |f D - f Dmid| ≤ c := by
        by_cases heq : D i = D' i
        · have hm : Dmid = D := by simp [Dmid, ← heq]
          simpa [hm] using hc
        · apply hstep D Dmid
          have hfilter : Finset.univ.filter (fun j => D j ≠ Dmid j) = {i} := by
            ext j
            by_cases hji : j = i
            · subst j; simp [Dmid, heq]
            · simp [Dmid, Function.update_of_ne hji, hji]
          simp [dHam, hammingDist, hfilter]
      calc
        |f D - f D'| ≤ |f D - f Dmid| + |f Dmid - f D'| := abs_sub_le _ _ _
        _ ≤ c + c * s.card := add_le_add hfirst hrest
        _ = c * (insert i s).card := by rw [Finset.card_insert_of_notMem hi]; push_cast; ring
  exact hfinite (Finset.univ.filter (fun i => D i ≠ D' i)) D D'
    (by intro i hi; simpa using hi)

/-- Pure privacy controls every event along the Hamming path, including out-of-model datasets.  [the theorem's stated inputs and assumptions](hyp:he,B,M,hM,D,D',E,hE), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon). -/
-- @node: private_hamming_event_bound
lemma private_hamming_event_bound (n : ℕ) (epsilon : ℝ)
    (he : 0 < epsilon ∧ epsilon ≤ 1) {B : Type*} [MeasurableSpace B]
    (M : Kernel (Dataset n) B) [IsMarkovKernel M]
    (hM : PrivateKernel n epsilon M) (D D' : Dataset n)
    (E : Set B) (hE : MeasurableSet E) :
    |(M D).real E - (M D').real E| ≤ 2 * epsilon * dHam n D D' := by
  exact event_bound_of_hamming_path n (fun D => (M D).real E) (2 * epsilon)
    (mul_nonneg (by norm_num) he.1.le) (fun D D' h => private_adjacent_event_bound n epsilon he M hM D D' h E hE)
    D D'

/-- Integrating the Hamming event bound against any coupling controls output total variation.  [the theorem's stated inputs and assumptions](hyp:he,B,M,hM,Q,Q',γ,hγ), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon). -/
-- @node: private_TV_le_coupling_cost
lemma private_TV_le_coupling_cost (n : ℕ) (epsilon : ℝ)
    (he : 0 < epsilon ∧ epsilon ≤ 1) {B : Type*} [MeasurableSpace B]
    (M : Kernel (Dataset n) B) [IsMarkovKernel M]
    (hM : PrivateKernel n epsilon M) (Q Q' : Measure (Dataset n))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (γ : Measure (Dataset n × Dataset n)) (hγ : Causalean.Stat.IsCoupling γ Q Q') :
    ENNReal.ofReal (TV (M ∘ₘ Q) (M ∘ₘ Q')) ≤
      ENNReal.ofReal (2 * epsilon) * ∫⁻ z, (dHam n z.1 z.2 : ℝ≥0∞) ∂γ := by
  letI := hγ.isProbabilityMeasure
  have hcost : (∫⁻ z, (dHam n z.1 z.2 : ℝ≥0∞) ∂γ) ≤ (n : ℝ≥0∞) := by
    calc
      _ ≤ ∫⁻ _z, (n : ℝ≥0∞) ∂γ := lintegral_mono fun z => by
        exact Nat.cast_le.mpr (show dHam n z.1 z.2 ≤ n from by
          simpa [dHam] using (hammingDist_le_card_fintype (x := z.1) (y := z.2)))
      _ = n := by simp
  have hfin : ENNReal.ofReal (2 * epsilon) *
      (∫⁻ z, (dHam n z.1 z.2 : ℝ≥0∞) ∂γ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top (by simp) hcost)
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mpr
  refine ciSup_le fun E => ?_
  let f : Dataset n → ℝ := fun D => (M D).real E.1
  have hf : Measurable f := (M.measurable_coe E.2).ennreal_toReal
  have hbound : ∀ D, ‖f D‖ ≤ 1 := fun D => by
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hi1 : Integrable (fun z => f z.1) γ :=
    Integrable.of_bound (hf.comp measurable_fst).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => hbound z.1)
  have hi2 : Integrable (fun z => f z.2) γ :=
    Integrable.of_bound (hf.comp measurable_snd).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => hbound z.2)
  rw [kernel_comp_real M Q E.1 E.2, kernel_comp_real M Q' E.1 E.2]
  change |(∫ D, f D ∂Q) - ∫ D, f D ∂Q'| ≤ _
  rw [← hγ.map_fst, ← hγ.map_snd,
    integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
  calc
    ENNReal.ofReal |(∫ z, f z.1 ∂γ) - ∫ z, f z.2 ∂γ| ≤
        ∫⁻ z, ENNReal.ofReal |f z.1 - f z.2| ∂γ := by
      simpa only [edist_dist, Real.dist_eq] using edist_integral_le_lintegral_edist hi1 hi2
    _ ≤ ∫⁻ z, ENNReal.ofReal (2 * epsilon) * (dHam n z.1 z.2 : ℝ≥0∞) ∂γ := by
      apply lintegral_mono
      intro z
      simpa only [f, ENNReal.ofReal_mul (show 0 ≤ 2 * epsilon from
        mul_nonneg (by norm_num) he.1.le),
        ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal
        (private_hamming_event_bound n epsilon he M hM z.1 z.2 E.1 E.2)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Replacement privacy contracts expected Hamming transport. Ordinary Markov contraction needs
no privacy, and finite chi-square divergence gives the square-root TV bound.  [the theorem's stated inputs and assumptions](hyp:B,M,hM,Q,Q'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon,he). -/
-- @node: lem:private-kernel-comparison
lemma private_kernel_comparison (n : ℕ) (epsilon : ℝ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    {B : Type*} [MeasurableSpace B]
    [StandardBorelSpace B] -- @realizes B(standard Borel output space)
    (M : Kernel (Dataset n) B)
    [IsMarkovKernel M] -- @realizes M(everywhere probability-valued kernel)
    (hM : PrivateKernel n epsilon M)
    (Q Q' : Measure (Dataset n)) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] :
    ENNReal.ofReal (TV (M ∘ₘ Q) (M ∘ₘ Q')) ≤ ENNReal.ofReal (2*epsilon) * WH n Q Q' ∧
    (∀ K : Kernel (Dataset n) B, IsMarkovKernel K →
      TV (K ∘ₘ Q) (K ∘ₘ Q') ≤ TV Q Q') ∧
    (Q ≪ Q' → (∫⁻ z, ENNReal.ofReal (((Q.rnDeriv Q' z).toReal - 1)^2) ∂Q') < ⊤ →
      TV Q Q' ≤ 1/2 * Real.sqrt (Causalean.Stat.chiSqDiv Q Q')) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [WH, ENNReal.mul_iInf_of_ne
      (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos (by norm_num) he.1)) ENNReal.ofReal_ne_top]
    apply le_iInf
    intro γ
    rw [ENNReal.mul_iInf_of_ne
      (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos (by norm_num) he.1)) ENNReal.ofReal_ne_top]
    apply le_iInf
    intro hγ
    exact private_TV_le_coupling_cost n epsilon he M hM Q Q' γ hγ
  · intro K hK
    letI := hK
    exact kernel_TV_contraction K Q Q'
  · exact TV_le_sqrt_chiSq_of_finite Q Q'

end CausalSmith.Stat.PrivateCateRoughdesign
