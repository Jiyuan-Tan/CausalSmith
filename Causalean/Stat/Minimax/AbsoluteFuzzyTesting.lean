module
public import Causalean.Stat.Minimax.MarkovKernelTransport
public import Causalean.Stat.Minimax.SharpHellinger
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Tactic.Linarith

/-!
# Absolute-loss fuzzy testing

This module gives a common-prior fuzzy-testing lower bound for absolute loss, with the constant inherited from the sharp Hellinger bound on total variation. It supplies finite iid experiment kernels, threshold tests that do not require target measurability, and the corresponding model-supremum lower bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Causalean.Stat.Minimax

variable {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]

/-- The [iid observation experiment](goal) for [a sample size](hyp:v) and
[a kernel](hyp:K) applies its independent product to the constant vector of latent indices. -/
noncomputable def iidExperimentKernel (v : ℕ) (K : Kernel Z X) :
    Kernel Z (Fin v → X) :=
  (Causalean.Stat.finProductKernel v K).comap (fun z _ => z)
    (measurable_pi_lambda _ fun _ => measurable_id)

/-- Every fibre of the iid experiment is [the independent finite product of its
one-observation law](goal). -/
theorem iidExperimentKernel_apply (v : ℕ) (K : Kernel Z X) [IsMarkovKernel K] (z : Z) :
    iidExperimentKernel v K z = Measure.pi (fun _ : Fin v => K z) := by
  exact Causalean.Stat.finProductKernel_apply v K (fun _ => z)

/-- The iid product, at [any sample size](hyp:v), of [a Markov kernel](hyp:K) is [again a Markov
kernel](goal). -/
instance instIsMarkovKernelIidExperimentKernel (v : ℕ) (K : Kernel Z X)
    [IsMarkovKernel K] : IsMarkovKernel (iidExperimentKernel v K) := by
  unfold iidExperimentKernel
  infer_instance

/-- Finite iid laws of a Markov kernel [vary measurably with the latent index](goal). -/
@[fun_prop]
theorem measurable_iid_laws (v : ℕ) (K : Kernel Z X) [IsMarkovKernel K] :
    Measurable (fun z => Measure.pi (fun _ : Fin v => K z)) := by
  have heq : (fun z => Measure.pi (fun _ : Fin v => K z)) =
      ⇑(iidExperimentKernel v K) := by
    funext z
    exact (iidExperimentKernel_apply v K z).symm
  rw [heq]
  exact (iidExperimentKernel v K).measurable

/-- Mixing a Markov kernel against a probability prior gives [a probability law](goal). -/
theorem isProbabilityMeasure_bind (ω : Measure Z) [IsProbabilityMeasure ω]
    (K : Kernel Z X) [IsMarkovKernel K] : IsProbabilityMeasure (ω.bind K) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ K.aemeasurable]
  simp

/-- The probability of a [measurable event](hyp:hE) under a mixture is [the prior
lower integral of component event probabilities](goal). -/
theorem bind_event_eq (ω : Measure Z) (K : Kernel Z X)
    {E : Set X} (hE : MeasurableSet E) :
    (ω.bind K) E = ∫⁻ z, K z E ∂ω := by
  exact Measure.bind_apply hE K.aemeasurable

/-- The event probability of an iid mixture for a [measurable event](hyp:hE) is
[the prior integral of product-law event probabilities](goal). -/
theorem bind_iid_event_eq (v : ℕ) (ω : Measure Z) (K : Kernel Z X) [IsMarkovKernel K]
    {E : Set (Fin v → X)} (hE : MeasurableSet E) :
    (ω.bind (fun z => Measure.pi (fun _ : Fin v => K z))) E =
      ∫⁻ z, (Measure.pi (fun _ : Fin v => K z)) E ∂ω := by
  exact Measure.bind_apply hE (measurable_iid_laws v K).aemeasurable

/-- The mixture of the packaged iid kernel [equals the mixture of the literal
finite-product laws](goal). -/
theorem bind_iidExperimentKernel (v : ℕ) (ω : Measure Z) (K : Kernel Z X)
    [IsMarkovKernel K] :
    ω.bind (iidExperimentKernel v K) =
      ω.bind (fun z => Measure.pi (fun _ : Fin v => K z)) := by
  congr 1
  funext z
  exact iidExperimentKernel_apply v K z


/-- Two [globally separated real families](hyp:hsep) on a nonempty index set have
[a fixed threshold at least half their separation from every target](goal).

Use `a = sSup (Set.range β) + s/2`. Nonemptiness supplies a point in each range,
and one fixed α value bounds the whole β range above. No measurable target is used. -/
theorem exists_separating_threshold [Nonempty Z] (α β : Z → ℝ) {s : ℝ}
    (hsep : ∀ z z', s ≤ α z - β z') :
    ∃ a : ℝ, (∀ z, a + s / 2 ≤ α z) ∧ (∀ z, β z ≤ a - s / 2) := by
  classical
  obtain ⟨z₀⟩ := ‹Nonempty Z›
  have hb : BddAbove (Set.range β) := by
    refine ⟨α z₀ - s, ?_⟩
    rintro b ⟨z, rfl⟩
    have := hsep z₀ z
    linarith
  refine ⟨sSup (Set.range β) + s / 2, ?_, ?_⟩
  · intro z
    have hu : sSup (Set.range β) ≤ α z - s := by
      apply csSup_le (Set.range_nonempty β)
      rintro b ⟨z', rfl⟩
      have := hsep z z'
      linarith
    linarith
  · intro z
    have := le_csSup hb (Set.mem_range_self z)
    linarith

/-- A [measurable estimator](hyp:ht) has a [measurable strict threshold test](goal). -/
theorem measurableSet_threshold {t : X → ℝ} (ht : Measurable t) (a : ℝ) :
    MeasurableSet {x | t x < a} := by
  exact measurableSet_lt ht measurable_const

/-- A [target at least δ above a threshold](hyp:hθ)
has [absolute risk at least δ times the below-threshold error probability](goal)
for a [measurable estimator](hyp:ht).

Bound the integrand below by the constant `ofReal δ` on the measurable event,
then integrate its indicator. No integrability or finite-risk premise is needed. -/
theorem threshold_error_mul_le_absolute_risk_above (P : Measure X)
    {t : X → ℝ} (ht : Measurable t) {a θ δ : ℝ}
    (hθ : a + δ ≤ θ) :
    ENNReal.ofReal δ * P {x | t x < a} ≤
      ∫⁻ x, ENNReal.ofReal |t x - θ| ∂P := by
  classical
  rw [← lintegral_indicator_const (measurableSet_threshold ht a)]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ {x | t x < a}
  · rw [Set.indicator_of_mem hx]
    apply ENNReal.ofReal_le_ofReal
    have hxa : t x < a := hx
    have habs := neg_le_abs (t x - θ)
    linarith
  · rw [Set.indicator_of_notMem hx]
    exact bot_le

/-- A [target at least δ below a threshold](hyp:hθ)
has [absolute risk at least δ times the complementary error probability](goal)
for a [measurable estimator](hyp:ht). -/
theorem threshold_error_mul_le_absolute_risk_below (P : Measure X)
    {t : X → ℝ} (ht : Measurable t) {a θ δ : ℝ}
    (hθ : θ ≤ a - δ) :
    ENNReal.ofReal δ * P {x | t x < a}ᶜ ≤
      ∫⁻ x, ENNReal.ofReal |t x - θ| ∂P := by
  classical
  rw [← lintegral_indicator_const (measurableSet_threshold ht a).compl]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ {x | t x < a}ᶜ
  · rw [Set.indicator_of_mem hx]
    apply ENNReal.ofReal_le_ofReal
    have hax : a ≤ t x := le_of_not_gt hx
    have habs := le_abs_self (t x - θ)
    linarith
  · rw [Set.indicator_of_notMem hx]
    exact bot_le

/-- For a probability prior and Markov experiment, [targets above a fixed threshold](hyp:hθ)
and [a uniform component risk bound](hyp:hR) imply [the same bound on the scaled
mixture error probability](goal) for a [measurable estimator](hyp:ht), without measurability of targets.

Rewrite the bind event by `Measure.bind_apply`. Move its constant multiplier
inside the prior lower integral and bound every integrand by R using the component
lemma. Integrate the constant against the probability prior. -/
theorem mixture_threshold_error_le_of_component_risk_above
    (ω : Measure Z) [IsProbabilityMeasure ω] (K : Kernel Z X) [IsMarkovKernel K]
    (θ : Z → ℝ) {t : X → ℝ} (ht : Measurable t) {a δ : ℝ} {R : ℝ≥0∞}
    (hθ : ∀ z, a + δ ≤ θ z)
    (hR : ∀ z, (∫⁻ x, ENNReal.ofReal |t x - θ z| ∂K z) ≤ R) :
    ENNReal.ofReal δ * (ω.bind K) {x | t x < a} ≤ R := by
  rw [Measure.bind_apply (measurableSet_threshold ht a) K.aemeasurable,
    ← lintegral_const_mul _ (K.measurable_coe (measurableSet_threshold ht a))]
  calc
    _ ≤ ∫⁻ _ : Z, R ∂ω := lintegral_mono fun z =>
      (threshold_error_mul_le_absolute_risk_above (K z) ht (hθ z)).trans (hR z)
    _ = R := by simp

/-- For a probability prior and Markov experiment, [targets below a fixed threshold](hyp:hθ)
and [a uniform component risk bound](hyp:hR) imply [the same bound on the scaled
complementary mixture error](goal) for a [measurable estimator](hyp:ht), without measurability of targets. -/
theorem mixture_threshold_error_le_of_component_risk_below
    (ω : Measure Z) [IsProbabilityMeasure ω] (K : Kernel Z X) [IsMarkovKernel K]
    (θ : Z → ℝ) {t : X → ℝ} (ht : Measurable t) {a δ : ℝ} {R : ℝ≥0∞}
    (hθ : ∀ z, θ z ≤ a - δ)
    (hR : ∀ z, (∫⁻ x, ENNReal.ofReal |t x - θ z| ∂K z) ≤ R) :
    ENNReal.ofReal δ * (ω.bind K) {x | t x < a}ᶜ ≤ R := by
  rw [Measure.bind_apply (measurableSet_threshold ht a).compl K.aemeasurable,
    ← lintegral_const_mul _ (K.measurable_coe (measurableSet_threshold ht a).compl)]
  calc
    _ ≤ ∫⁻ _ : Z, R ∂ω := lintegral_mono fun z =>
      (threshold_error_mul_le_absolute_risk_below (K z) ht (hθ z)).trans (hR z)
    _ = R := by simp

variable {Θ Z X Ω : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Ω]

/-- The [worst absolute risk](goal) for [a model](hyp:M), [observation laws](hyp:Q),
[a real target](hyp:Ψ) and [an estimator](hyp:t) is the extended-nonnegative supremum
of the lower integrals of absolute error over all model members. -/
noncomputable def worstAbsoluteRisk (M : Set Θ) (Q : Θ → Measure X)
    (Ψ : Θ → ℝ) (t : X → ℝ) : ℝ≥0∞ :=
  ⨆ θ : M, ∫⁻ x, ENNReal.ofReal |t x - Ψ θ.val| ∂Q θ.val

/-- The absolute risk of [a model member](hyp:hθ) is [bounded by the model supremum](goal). -/
theorem absolute_risk_le_model_sup (M : Set Θ) (Q : Θ → Measure X)
    (Ψ : Θ → ℝ) (t : X → ℝ) {θ : Θ} (hθ : θ ∈ M) :
    (∫⁻ x, ENNReal.ofReal |t x - Ψ θ| ∂Q θ) ≤ worstAbsoluteRisk M Q Ψ t := by
  exact le_iSup (fun θ : M => ∫⁻ x, ENNReal.ofReal |t x - Ψ θ.val| ∂Q θ.val) ⟨θ, hθ⟩

/-- [Model membership and matching experiment laws](hyp:hb,hc,hK,hL), together with
[a fixed half-separation threshold](hyp:ha,hbnd), bound [the scaled sum of mixture test
errors by twice the model supremum of absolute risk](goal) for a
[measurable estimator](hyp:ht) and [positive separation](hyp:hs).

Apply the two mixture-threshold lemmas with R = worstAbsoluteRisk and δ = s/2.
Each component risk is bounded by `absolute_risk_le_model_sup`. Add the inequalities;
distribute the constant. Targets themselves are never integrated over the prior. -/
theorem separated_mixture_errors_le_two_mul_sup
    (ω : Measure Z) [IsProbabilityMeasure ω]
    (K L : Kernel Z X) [IsMarkovKernel K] [IsMarkovKernel L]
    (M : Set Θ) (Q : Θ → Measure X) (Ψ : Θ → ℝ) (b c : Z → Θ)
    (hb : ∀ z, b z ∈ M) (hc : ∀ z, c z ∈ M)
    (hK : ∀ z, K z = Q (b z)) (hL : ∀ z, L z = Q (c z))
    {s a : ℝ} (hs : 0 < s)
    (ha : ∀ z, a + s / 2 ≤ Ψ (b z)) (hbnd : ∀ z, Ψ (c z) ≤ a - s / 2)
    {t : X → ℝ} (ht : Measurable t) :
    ENNReal.ofReal (s / 2) *
        ((ω.bind K) {x | t x < a} + (ω.bind L) {x | t x < a}ᶜ) ≤
      2 * worstAbsoluteRisk M Q Ψ t := by
  have hB := mixture_threshold_error_le_of_component_risk_above ω K
    (fun z => Ψ (b z)) ht ha (fun z => by
      rw [hK z]
      exact absolute_risk_le_model_sup M Q Ψ t (hb z))
  have hC := mixture_threshold_error_le_of_component_risk_below ω L
    (fun z => Ψ (c z)) ht hbnd (fun z => by
      rw [hL z]
      exact absolute_risk_le_model_sup M Q Ψ t (hc z))
  simpa only [mul_add, two_mul] using add_le_add hB hC

/-- [Two model families with matching Markov observation experiments](hyp:hb,hc,hK,hL)
and [globally separated targets](hyp:hsep,hs) force [every measurable estimator](hyp:ht)
to have [worst absolute risk at least the sharp separation/testing constant](goal), when
[the common-prior mixtures satisfy a Hellinger budget below two](hyp:hu0,hu2,hH).

Obtain Nonempty Z from the probability prior, then call `exists_separating_threshold`
on Ψ ∘ b and Ψ ∘ c. Use `isProbabilityMeasure_bind` for each mixture and the budget
binary-testing bound for the measurable threshold event. Combine with
`separated_mixture_errors_le_two_mul_sup` and cancel the finite positive factor two
in ENNReal. Handle an infinite model supremum directly; do not convert risks to real.
No measurable structure on Θ or measurability of Ψ, b or c is required. -/
theorem absolute_fuzzy_testing_lower_bound
    (ω : Measure Z) [IsProbabilityMeasure ω]
    (K L : Kernel Z X) [IsMarkovKernel K] [IsMarkovKernel L]
    (M : Set Θ) (Q : Θ → Measure X) (Ψ : Θ → ℝ) (b c : Z → Θ)
    (hb : ∀ z, b z ∈ M) (hc : ∀ z, c z ∈ M)
    (hK : ∀ z, K z = Q (b z)) (hL : ∀ z, L z = Q (c z))
    {s u : ℝ} (hs : 0 < s) (hu0 : 0 ≤ u) (hu2 : u < 2)
    (hsep : ∀ z z', s ≤ Ψ (b z) - Ψ (c z'))
    (hH : hellingerSqMeasure (ω.bind K) (ω.bind L) ≤ u)
    {t : X → ℝ} (ht : Measurable t) :
    ENNReal.ofReal ((s / 4) * (1 - Real.sqrt (u * (1 - u / 4)))) ≤
      worstAbsoluteRisk M Q Ψ t := by
  let : Nonempty Z := nonempty_of_isProbabilityMeasure ω
  let : IsProbabilityMeasure (ω.bind K) := isProbabilityMeasure_bind ω K
  let : IsProbabilityMeasure (ω.bind L) := isProbabilityMeasure_bind ω L
  obtain ⟨a, ha, hbnd⟩ := exists_separating_threshold
    (fun z => Ψ (b z)) (fun z => Ψ (c z)) hsep
  have htest := binary_test_error_ge_of_hellinger_budget
    (ω.bind K) (ω.bind L) hu0 hu2 hH (measurableSet_threshold ht a)
  have hrisk := (mul_le_mul_right htest (ENNReal.ofReal (s / 2))).trans
    (separated_mixture_errors_le_two_mul_sup ω K L M Q Ψ b c
      hb hc hK hL hs ha hbnd ht)
  have hconstant : ENNReal.ofReal (s / 2) *
      ENNReal.ofReal (1 - Real.sqrt (u * (1 - u / 4))) =
      2 * ENNReal.ofReal ((s / 4) * (1 - Real.sqrt (u * (1 - u / 4)))) := by
    rw [← ENNReal.ofReal_mul (show 0 ≤ s / 2 by positivity),
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    congr 1
    ring
  rw [hconstant] at hrisk
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hrisk

/-- Take a [sample size](hyp:v), a [probability prior on latent indices](hyp:ω), [two Markov
families of observation laws indexed by the latent index](hyp:B,C), a [model](hyp:M) [which
contains every law of both families](hyp:hB,hC),
and a [real functional](hyp:Ψ) [whose value at any law of the first family exceeds its value at
any law of the second family by at least a positive gap](hyp:hs,hsep). If [the squared Hellinger
distance between the two prior mixtures of the iid product laws is at most a budget that is
nonnegative and strictly below two](hyp:hu0,hu2,hH), then for [any measurable estimator based on
the iid sample](hyp:ht), [the supremum over the model of the expected absolute error under iid
sampling is at least one quarter of the gap times one minus the square root of the budget times
one minus a quarter of the budget](goal).

This includes every positive sample size required by the consumer (and the empty experiment).
The functional Ψ is arbitrary; neither measurability on laws nor on latent indices is assumed. -/
theorem absolute_fuzzy_testing_lower_bound_iid
    (v : ℕ) (ω : Measure Z) [IsProbabilityMeasure ω]
    (B C : Kernel Z Ω) [IsMarkovKernel B] [IsMarkovKernel C]
    (M : Set (Measure Ω)) (Ψ : Measure Ω → ℝ)
    (hB : ∀ z, B z ∈ M) (hC : ∀ z, C z ∈ M)
    {s u : ℝ} (hs : 0 < s) (hu0 : 0 ≤ u) (hu2 : u < 2)
    (hsep : ∀ z z', s ≤ Ψ (B z) - Ψ (C z'))
    (hH : hellingerSqMeasure
      (ω.bind (fun z => Measure.pi (fun _ : Fin v => B z)))
      (ω.bind (fun z => Measure.pi (fun _ : Fin v => C z))) ≤ u)
    {t : (Fin v → Ω) → ℝ} (ht : Measurable t) :
    ENNReal.ofReal ((s / 4) * (1 - Real.sqrt (u * (1 - u / 4)))) ≤
      ⨆ P : M, ∫⁻ sample, ENNReal.ofReal |t sample - Ψ P.val|
        ∂Measure.pi (fun _ : Fin v => P.val) := by
  have hbudget : hellingerSqMeasure (ω.bind (iidExperimentKernel v B))
      (ω.bind (iidExperimentKernel v C)) ≤ u := by
    simpa only [bind_iidExperimentKernel] using hH
  exact absolute_fuzzy_testing_lower_bound ω
    (iidExperimentKernel v B) (iidExperimentKernel v C) M
    (fun P => Measure.pi (fun _ : Fin v => P)) Ψ (fun z => B z) (fun z => C z)
    hB hC (iidExperimentKernel_apply v B) (iidExperimentKernel_apply v C)
    hs hu0 hu2 hsep hbudget ht


end Causalean.Stat.Minimax
