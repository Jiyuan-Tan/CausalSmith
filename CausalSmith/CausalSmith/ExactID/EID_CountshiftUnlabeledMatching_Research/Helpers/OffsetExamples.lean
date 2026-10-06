module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.PoissonMixtureMoments
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Canonical one-coordinate Gaussian--Poisson models used for offset examples. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Matrix

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

abbrev OffsetExampleFiber :=
  ((Fin 1 → ℝ) × (Fin 1 → ℝ)) × (Fin 1 → ℕ)

abbrev OffsetExampleSpace := Fin 2 → OffsetExampleFiber

-- @node: offsetExample_eta
@[no_expose]
private def offsetExampleEta (m : Fin 2) (_ : Fin 1) : ℝ := m.1

-- @node: poissonMeasure_parameter_measurable
private lemma poissonMeasure_parameter_measurable :
    Measurable (fun r : NNReal => poissonMeasure r) := by
  unfold poissonMeasure
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  simp_rw [Measure.sum_apply _ hs, Measure.smul_apply, Measure.dirac_apply' _ hs]
  exact Measurable.tsum fun _ => by fun_prop

-- @node: poissonCountLaw_fin_one_eq_map
private lemma poissonCountLaw_fin_one_eq_map (s z : Fin 1 → ℝ) :
    poissonCountLaw s z =
      (poissonMeasure (Real.toNNReal (s 0 * Real.exp (z 0)))).map
        (fun n _ => n) := by
  rw [poissonCountLaw]
  let q := poissonMeasure (Real.toNNReal (s 0 * Real.exp (z 0)))
  let e := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℕ)
  have h := MeasurePreserving.symm e
    (measurePreserving_piUnique (fun _ : Fin 1 => q))
  calc
    Measure.pi (fun j => poissonMeasure (Real.toNNReal (s j * Real.exp (z j)))) =
        Measure.pi (fun _ : Fin 1 => q) := by
      congr 1
      funext i
      rw [show i = 0 from Subsingleton.elim _ _]
    _ = q.map e.symm := h.map_eq.symm
    _ = q.map (fun n _ => n) := by
      congr 1

-- @node: poissonCountLaw_fin_one_isProbabilityMeasure
private lemma poissonCountLaw_fin_one_isProbabilityMeasure (s z : Fin 1 → ℝ) :
    IsProbabilityMeasure (poissonCountLaw s z) := by
  rw [poissonCountLaw_fin_one_eq_map]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

-- @node: poissonCountLaw_attach_measurable
private lemma poissonCountLaw_attach_measurable :
    Measurable (fun sz : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      (poissonCountLaw sz.1 sz.2).map (fun x => (sz, x))) := by
  refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
  have heval : (fun sz : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      ((poissonCountLaw sz.1 sz.2).map (fun x => (sz, x))) A) =
      fun sz => ∑' n : ℕ, ENNReal.ofReal
        (Real.exp (-(Real.toNNReal (sz.1 0 * Real.exp (sz.2 0)) : ℝ)) *
          (Real.toNNReal (sz.1 0 * Real.exp (sz.2 0)) : ℝ) ^ n /
            n.factorial) * A.indicator 1 (sz, fun _ => n) := by
    funext sz
    rw [poissonCountLaw_fin_one_eq_map,
      Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_apply (by fun_prop) hA, poissonMeasure,
      Measure.sum_apply _ (hA.preimage (by fun_prop))]
    have hm : Measurable ((fun x : Fin 1 → ℕ => (sz, x)) ∘
        (fun n : ℕ => fun _ : Fin 1 => n)) := by fun_prop
    simp_rw [Measure.smul_apply, Measure.dirac_apply' _ (hA.preimage hm)]
    rfl
  rw [heval]
  exact Measurable.tsum fun _ => by fun_prop

-- @node: offsetExample_base
@[no_expose]
private def offsetExampleBase (ρ : Measure ℝ) (m : Fin 2) :
    Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ)) :=
  (ρ.prod (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))).map
    (fun u => (fun _ => u.1,
      fun i => offsetExampleEta m i + (WithLp.ofLp u.2) i))

-- @node: offsetExample_kernel
@[no_expose]
private def offsetExampleKernel
    (sz : (Fin 1 → ℝ) × (Fin 1 → ℝ)) : Measure OffsetExampleFiber :=
  (poissonCountLaw sz.1 sz.2).map (fun x => (sz, x))

-- @node: offsetExample_envLaw
@[no_expose]
private def offsetExampleEnvLaw (ρ : Measure ℝ) (m : Fin 2) :
    Measure OffsetExampleFiber :=
  (offsetExampleBase ρ m).bind offsetExampleKernel

-- @node: offsetExample_law
@[no_expose]
def offsetExampleLaw (ρ : Measure ℝ) : Measure OffsetExampleSpace :=
  Measure.pi (fun m => offsetExampleEnvLaw ρ m)

-- @node: offsetExample_base_probability
private lemma offsetExample_base_probability (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (m : Fin 2) :
    IsProbabilityMeasure (offsetExampleBase ρ m) := by
  unfold offsetExampleBase
  exact Measure.isProbabilityMeasure_map (by fun_prop)

-- @node: offsetExample_kernel_probability
private lemma offsetExample_kernel_probability
    (sz : (Fin 1 → ℝ) × (Fin 1 → ℝ)) :
    IsProbabilityMeasure (offsetExampleKernel sz) := by
  unfold offsetExampleKernel
  let _ := poissonCountLaw_fin_one_isProbabilityMeasure sz.1 sz.2
  exact Measure.isProbabilityMeasure_map (by fun_prop)

-- @node: offsetExample_env_probability
private lemma offsetExample_env_probability (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (m : Fin 2) :
    IsProbabilityMeasure (offsetExampleEnvLaw ρ m) := by
  let _ := offsetExample_base_probability ρ m
  unfold offsetExampleEnvLaw
  exact MeasureTheory.isProbabilityMeasure_bind poissonCountLaw_attach_measurable.aemeasurable
    (ae_of_all _ offsetExample_kernel_probability)

-- @node: offsetExample_law_probability
lemma offsetExample_law_probability (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] : IsProbabilityMeasure (offsetExampleLaw ρ) := by
  let _ (m : Fin 2) := offsetExample_env_probability ρ m
  unfold offsetExampleLaw
  infer_instance

-- @node: offsetExample_map_eval
private lemma offsetExample_map_eval (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (m : Fin 2) :
    (offsetExampleLaw ρ).map (fun ω => ω m) = offsetExampleEnvLaw ρ m := by
  let _ (i : Fin 2) := offsetExample_env_probability ρ i
  rw [offsetExampleLaw, Measure.pi_map_eval]
  simp

-- @node: offsetExample_env_map_condition
private lemma offsetExample_env_map_condition (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (m : Fin 2) :
    (offsetExampleEnvLaw ρ m).map Prod.fst = offsetExampleBase ρ m := by
  let _ := offsetExample_base_probability ρ m
  have hk : Measurable offsetExampleKernel :=
    poissonCountLaw_attach_measurable
  ext A hA
  rw [Measure.map_apply measurable_fst hA, offsetExampleEnvLaw,
    Measure.bind_apply (hA.preimage measurable_fst)
      hk.aemeasurable]
  simp_rw [offsetExampleKernel, Measure.map_apply measurable_prodMk_left
    (hA.preimage measurable_fst)]
  simp only [Set.preimage, Set.mem_ofPred_eq]
  rw [show (fun sz : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      (poissonCountLaw sz.1 sz.2) {x | sz ∈ A}) = A.indicator 1 by
    funext sz
    by_cases hsz : sz ∈ A
    · simp [hsz, isProbabilityMeasure_iff.mp
        (poissonCountLaw_fin_one_isProbabilityMeasure sz.1 sz.2)]
    · simp [hsz]]
  rw [lintegral_indicator hA]
  exact setLIntegral_one A

-- @node: offsetExample_base_map_disturbance
private lemma offsetExample_base_map_disturbance (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (m : Fin 2) :
    (offsetExampleBase ρ m).map
        (fun sz => WithLp.toLp 2 (fun i => sz.2 i - offsetExampleEta m i)) =
      multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [offsetExampleBase, Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : (fun sz : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      WithLp.toLp 2 (fun i => sz.2 i - offsetExampleEta m i)) ∘
      (fun u : ℝ × EuclideanSpace ℝ (Fin 1) =>
        (fun _ => u.1, fun i => offsetExampleEta m i + (WithLp.ofLp u.2) i)) =
      Prod.snd := by
    funext u
    apply WithLp.ofLp_injective
    ext i
    simp
  rw [hcomp, Measure.map_snd_prod]
  simp

-- @node: offsetExample_env_map_disturbance
private lemma offsetExample_env_map_disturbance (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (m : Fin 2) :
    (offsetExampleEnvLaw ρ m).map
        (fun y => WithLp.toLp 2 (fun i => y.1.2 i - offsetExampleEta m i)) =
      multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [show (fun y : OffsetExampleFiber =>
      WithLp.toLp 2 (fun i => y.1.2 i - offsetExampleEta m i)) =
      (fun sz => WithLp.toLp 2 (fun i => sz.2 i - offsetExampleEta m i)) ∘
        Prod.fst from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    offsetExample_env_map_condition,
    offsetExample_base_map_disturbance]

-- @node: offsetExample_law_map_disturbance
private lemma offsetExample_law_map_disturbance (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (m : Fin 2) :
    (offsetExampleLaw ρ).map (fun ω =>
        WithLp.toLp 2 (fun i => (ω m).1.2 i - offsetExampleEta m i)) =
      multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [show (fun ω : OffsetExampleSpace =>
      WithLp.toLp 2 (fun i => (ω m).1.2 i - offsetExampleEta m i)) =
      (fun y => WithLp.toLp 2 (fun i => y.1.2 i - offsetExampleEta m i)) ∘
        (fun ω => ω m) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), offsetExample_map_eval,
    offsetExample_env_map_disturbance]

-- @node: offsetExample_law_map_condition
private lemma offsetExample_law_map_condition (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (m : Fin 2) :
    (offsetExampleLaw ρ).map (fun ω => (ω m).1) = offsetExampleBase ρ m := by
  rw [show (fun ω : OffsetExampleSpace => (ω m).1) =
      Prod.fst ∘ (fun ω => ω m) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), offsetExample_map_eval,
    offsetExample_env_map_condition]

-- @node: offsetExample_law_map_offset
private lemma offsetExample_law_map_offset (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (m : Fin 2) :
    (offsetExampleLaw ρ).map (fun ω => (ω m).1.1 0) = ρ := by
  rw [show (fun ω : OffsetExampleSpace => (ω m).1.1 0) =
      (fun sz => sz.1 0) ∘ (fun ω => (ω m).1) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    offsetExample_law_map_condition, offsetExampleBase,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : (fun sz : (Fin 1 → ℝ) × (Fin 1 → ℝ) => sz.1 0) ∘
      (fun u : ℝ × EuclideanSpace ℝ (Fin 1) =>
        (fun _ => u.1, fun i => offsetExampleEta m i + (WithLp.ofLp u.2) i)) =
      Prod.fst := by rfl
  rw [hcomp, Measure.map_fst_prod]
  simp

-- @node: offsetExample_positive
private lemma offsetExample_positive (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : ∀ᵐ s ∂ρ, 0 < s) (m : Fin 2) :
    ∀ᵐ ω ∂offsetExampleLaw ρ, ∀ i, 0 < (ω m).1.1 i := by
  have hm : MeasurableSet {s : ℝ | 0 < s} := measurableSet_Ioi
  have hs : ∀ᵐ ω ∂offsetExampleLaw ρ, 0 < (ω m).1.1 0 := by
    rw [← ae_map_iff
      ((by fun_prop : Measurable (fun ω : OffsetExampleSpace => (ω m).1.1 0))).aemeasurable
      hm, offsetExample_law_map_offset]
    exact hρ
  filter_upwards [hs] with ω hω i
  simpa only [show i = 0 from Subsingleton.elim _ _] using hω

-- @node: offsetExample_model
@[no_expose]
def offsetExampleModel (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : ∀ᵐ s ∂ρ, 0 < s) :
    AtomicCountModel 1 1 OffsetExampleSpace (offsetExampleLaw ρ) where
  p_pos := by norm_num
  M_pos := by norm_num
  A := 0
  η := offsetExampleEta
  Ωc := fun _ => 1
  α := fun _ => 1
  t := fun _ => 0
  ξ := fun m ω i => (ω m).1.2 i - offsetExampleEta m i
  S := fun m ω => (ω m).1.1
  X := fun m ω => (ω m).2
  acyclic := by
    constructor
    · simp
    · intro i h
      have hempty : ∀ {a b : Fin 1},
          Relation.TransGen (fun _ _ => False) a b → False := by
        intro a b hab
        induction hab with
        | single h => exact h
        | tail _ h _ => exact h
      apply hempty
      simpa using h
  atomic := by
    intro m
    funext i
    fin_cases m
    fin_cases i
    simp [offsetExampleEta]
  nonvanishing := by simp [NonvanishingStrength]
  gaussian := by
    intro m
    refine ⟨Matrix.PosDef.one, ?_⟩
    have hmap := offsetExample_law_map_disturbance ρ m
    refine ⟨AEMeasurable.of_map_ne_zero ?_, hmap⟩
    rw [hmap]
    exact IsProbabilityMeasure.ne_zero _
  poisson := by
    intro m _
    have hlatent (ω : OffsetExampleSpace) :
        latentState (0 : Matrix (Fin 1) (Fin 1) ℝ) offsetExampleEta
          (fun m ω i => (ω m).1.2 i - offsetExampleEta m i) m ω =
          (ω m).1.2 := by
      ext i
      simp [latentState, totalEffect]
    refine ⟨offsetExample_positive ρ hρ m, ?_, ?_, ?_⟩
    · simpa only [hlatent] using
        (show Measurable (fun ω : OffsetExampleSpace => (ω m).1) by fun_prop).aemeasurable
    · simpa only [hlatent] using
        (show Measurable (fun ω : OffsetExampleSpace => ω m) by fun_prop).aemeasurable
    · have hfull : (fun ω : OffsetExampleSpace =>
          (((ω m).1.1,
            latentState (0 : Matrix (Fin 1) (Fin 1) ℝ) offsetExampleEta
              (fun m ω i => (ω m).1.2 i - offsetExampleEta m i) m ω),
            (ω m).2)) = fun ω => ω m := by
          funext ω
          simp only [hlatent]
      rw [hfull, offsetExample_map_eval, offsetExampleEnvLaw,
        show (fun ω : OffsetExampleSpace =>
          ((ω m).1.1,
            latentState (0 : Matrix (Fin 1) (Fin 1) ℝ) offsetExampleEta
              (fun m ω i => (ω m).1.2 i - offsetExampleEta m i) m ω)) =
          fun ω => (ω m).1 by funext ω; simp only [hlatent],
        offsetExample_law_map_condition]
      rfl

-- @node: offsetExample_eval_measurePreserving
private lemma offsetExample_eval_measurePreserving (s z : Fin 1 → ℝ) :
    MeasurePreserving (fun x : Fin 1 → ℕ => x 0) (poissonCountLaw s z)
      (poissonMeasure (Real.toNNReal (s 0 * Real.exp (z 0)))) := by
  refine ⟨measurable_pi_apply 0, ?_⟩
  rw [poissonCountLaw, Measure.pi_map_eval]
  simp

-- @node: offsetExample_first_fiber_integrable
private lemma offsetExample_first_fiber_integrable (s z : Fin 1 → ℝ)
    (_hs : s 0 ≠ 0) :
    Integrable (fun x => firstFactorial x s 0) (poissonCountLaw s z) := by
  have hp := offsetExample_eval_measurePreserving s z
  have hi : Integrable (fun n : ℕ => (n : ℝ))
      (poissonMeasure (Real.toNNReal (s 0 * Real.exp (z 0)))) := by
    simpa using Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
      (Real.toNNReal (s 0 * Real.exp (z 0))) 1
  have hcomp := (hp.integrable_comp (by measurability)).2 hi
  convert hcomp.mul_const (s 0)⁻¹ using 1
  funext x
  simp only [firstFactorial, Function.comp_apply, div_eq_mul_inv]

-- @node: offsetExample_first_fiber_integral
private lemma offsetExample_first_fiber_integral (s z : Fin 1 → ℝ)
    (hs : 0 < s 0) :
    (∫ x, firstFactorial x s 0 ∂poissonCountLaw s z) = Real.exp (z 0) := by
  simp only [firstFactorial]
  rw [integral_div]
  have hp := offsetExample_eval_measurePreserving s z
  rw [show (∫ x : Fin 1 → ℕ, (x 0 : ℝ) ∂poissonCountLaw s z) =
      ∫ n : ℕ, (n : ℝ) ∂poissonMeasure
        (Real.toNNReal (s 0 * Real.exp (z 0))) by
        rw [← hp.map_eq, integral_map (measurable_pi_apply 0).aemeasurable
          (by measurability)]]
  rw [show (∫ n : ℕ, (n : ℝ) ∂poissonMeasure
      (Real.toNNReal (s 0 * Real.exp (z 0)))) =
      (Real.toNNReal (s 0 * Real.exp (z 0)) : ℝ) by
        simpa using Causalean.Stat.Concentration.Poisson.poisson_descFactorial_moment
          (Real.toNNReal (s 0 * Real.exp (z 0))) 1,
    Real.coe_toNNReal _ (mul_nonneg hs.le (Real.exp_pos _).le)]
  field_simp

-- @node: offsetExample_poisson_mixed_integrable
private lemma offsetExample_poisson_mixed_integrable (rate : NNReal) (h t : ℕ) :
    Integrable (fun n : ℕ => (n.descFactorial h : ℝ) * (n.descFactorial t : ℝ))
      (poissonMeasure rate) := by
  have hi := integrable_finsetSum (Finset.range (min h t + 1))
    (fun r _ =>
      (Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable rate
        (h + t - r)).const_mul
          ((h.choose r : ℝ) * (t.choose r : ℝ) * (Nat.factorial r : ℝ)))
  rw [show (fun n : ℕ => (n.descFactorial h : ℝ) * (n.descFactorial t : ℝ)) =
      (fun n : ℕ => ∑ r ∈ Finset.range (min h t + 1),
        (h.choose r : ℝ) * (t.choose r : ℝ) * (Nat.factorial r : ℝ) *
          (n.descFactorial (h + t - r) : ℝ)) by
    funext n
    exact Causalean.Stat.Concentration.Poisson.descFactorial_mul n h t]
  exact hi

-- @node: offsetExample_first_sq_fiber_integrable
private lemma offsetExample_first_sq_fiber_integrable (s z : Fin 1 → ℝ)
    (_hs : s 0 ≠ 0) :
    Integrable (fun x => (firstFactorial x s 0) ^ 2) (poissonCountLaw s z) := by
  have hp := offsetExample_eval_measurePreserving s z
  let rate := Real.toNNReal (s 0 * Real.exp (z 0))
  have hi := offsetExample_poisson_mixed_integrable rate 1 1
  have hcomp := (hp.integrable_comp (by fun_prop)).2 hi
  convert hcomp.mul_const ((s 0) ^ 2)⁻¹ using 1
  funext x
  simp only [firstFactorial, div_eq_mul_inv, Function.comp_apply]
  norm_num [Nat.descFactorial]
  ring

-- @node: offsetExample_first_sq_fiber_integral
private lemma offsetExample_first_sq_fiber_integral (s z : Fin 1 → ℝ)
    (hs : 0 < s 0) :
    (∫ x, (firstFactorial x s 0) ^ 2 ∂poissonCountLaw s z) =
      Real.exp (2 * z 0) + Real.exp (z 0) / s 0 := by
  let rate := Real.toNNReal (s 0 * Real.exp (z 0))
  have hp := offsetExample_eval_measurePreserving s z
  have hsq : (∫ x : Fin 1 → ℕ, (x 0 : ℝ) ^ 2 ∂poissonCountLaw s z) =
      (rate : ℝ) ^ 2 + rate := by
    rw [show (∫ x : Fin 1 → ℕ, (x 0 : ℝ) ^ 2 ∂poissonCountLaw s z) =
        ∫ n : ℕ, (n.descFactorial 1 : ℝ) * (n.descFactorial 1 : ℝ)
          ∂poissonMeasure rate by
          rw [← hp.map_eq, integral_map (measurable_pi_apply 0).aemeasurable
            (by measurability)]
          congr 1
          funext x
          norm_num [Nat.descFactorial]
          ring]
    rw [Causalean.Stat.Concentration.Poisson.poisson_descFactorial_mixed]
    simp [Finset.sum_range_succ]
  simp only [firstFactorial, div_pow]
  rw [integral_div, hsq]
  simp only [rate]
  rw [Real.coe_toNNReal _ (mul_nonneg hs.le (Real.exp_pos _).le)]
  have he : Real.exp (2 * z 0) = Real.exp (z 0) ^ 2 := by
    rw [show 2 * z 0 = z 0 + z 0 by ring, Real.exp_add, pow_two]
  rw [he]
  field_simp

-- @node: offsetExample_base_positive
private lemma offsetExample_base_positive (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : ∀ᵐ s ∂ρ, 0 < s) (m : Fin 2) :
    ∀ᵐ sz ∂offsetExampleBase ρ m, ∀ i, 0 < sz.1 i := by
  have hmap : (offsetExampleBase ρ m).map (fun sz => sz.1 0) = ρ := by
    rw [offsetExampleBase, Measure.map_map (by fun_prop) (by fun_prop)]
    change Measure.map Prod.fst
      (ρ.prod (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))) = ρ
    rw [Measure.map_fst_prod]
    simp
  have hs : ∀ᵐ sz ∂offsetExampleBase ρ m, 0 < sz.1 0 := by
    rw [← ae_map_iff
      ((by fun_prop : Measurable (fun sz : (Fin 1 → ℝ) × (Fin 1 → ℝ) => sz.1 0))).aemeasurable
      measurableSet_Ioi, hmap]
    exact hρ
  filter_upwards [hs] with sz hsz i
  simpa only [show i = 0 from Subsingleton.elim _ _] using hsz

-- @node: offsetExample_first_integrable
private lemma offsetExample_first_integrable (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : ∀ᵐ s ∂ρ, 0 < s) (m : Fin 2)
    (hbase : Integrable (fun sz => Real.exp (sz.2 0)) (offsetExampleBase ρ m)) :
    Integrable (fun y : OffsetExampleFiber => firstFactorial y.2 y.1.1 0)
      (offsetExampleEnvLaw ρ m) := by
  let κ : Kernel ((Fin 1 → ℝ) × (Fin 1 → ℝ)) OffsetExampleFiber :=
    ⟨offsetExampleKernel, poissonCountLaw_attach_measurable⟩
  have hfmeas : Measurable (fun y : OffsetExampleFiber =>
      firstFactorial y.2 y.1.1 0) := by
    simp only [firstFactorial]
    exact (measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp
      ((measurable_pi_apply 0).comp measurable_snd) |>.div
        ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_fst))
  change Integrable (fun y : OffsetExampleFiber => firstFactorial y.2 y.1.1 0)
    ((offsetExampleBase ρ m).bind κ)
  apply (Measure.integrable_comp_iff hfmeas.aestronglyMeasurable).2
  constructor
  · filter_upwards [offsetExample_base_positive ρ hρ m] with sz hs
    change Integrable (fun y : OffsetExampleFiber => firstFactorial y.2 y.1.1 0)
      (offsetExampleKernel sz)
    rw [offsetExampleKernel, integrable_map_measure hfmeas.aestronglyMeasurable
      (by fun_prop)]
    convert offsetExample_first_fiber_integrable sz.1 sz.2 (ne_of_gt (hs 0)) using 1
    rfl
  · apply hbase.congr
    filter_upwards [offsetExample_base_positive ρ hρ m] with sz hs
    symm
    change (∫ y : OffsetExampleFiber,
      ‖firstFactorial y.2 y.1.1 0‖ ∂offsetExampleKernel sz) = Real.exp (sz.2 0)
    rw [offsetExampleKernel,
      integral_map (by fun_prop) hfmeas.norm.aestronglyMeasurable]
    rw [show (fun x : Fin 1 → ℕ => ‖firstFactorial x sz.1 0‖) =
        fun x => firstFactorial x sz.1 0 by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact div_nonneg (Nat.cast_nonneg _) (hs 0).le]
    exact offsetExample_first_fiber_integral sz.1 sz.2 (hs 0)

-- @node: offsetExample_first_sq_integrable
private lemma offsetExample_first_sq_integrable (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : ∀ᵐ s ∂ρ, 0 < s) (m : Fin 2)
    (hbase : Integrable (fun sz => Real.exp (2 * sz.2 0) +
      Real.exp (sz.2 0) / sz.1 0) (offsetExampleBase ρ m)) :
    Integrable (fun y : OffsetExampleFiber => (firstFactorial y.2 y.1.1 0) ^ 2)
      (offsetExampleEnvLaw ρ m) := by
  let κ : Kernel ((Fin 1 → ℝ) × (Fin 1 → ℝ)) OffsetExampleFiber :=
    ⟨offsetExampleKernel, poissonCountLaw_attach_measurable⟩
  have hfmeas : Measurable (fun y : OffsetExampleFiber =>
      (firstFactorial y.2 y.1.1 0) ^ 2) := by
    simp only [firstFactorial]
    exact ((measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp
      ((measurable_pi_apply 0).comp measurable_snd) |>.div
        ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_fst))).pow_const 2
  change Integrable (fun y : OffsetExampleFiber => (firstFactorial y.2 y.1.1 0) ^ 2)
    ((offsetExampleBase ρ m).bind κ)
  apply (Measure.integrable_comp_iff hfmeas.aestronglyMeasurable).2
  constructor
  · filter_upwards [offsetExample_base_positive ρ hρ m] with sz hs
    change Integrable (fun y : OffsetExampleFiber => (firstFactorial y.2 y.1.1 0) ^ 2)
      (offsetExampleKernel sz)
    rw [offsetExampleKernel, integrable_map_measure hfmeas.aestronglyMeasurable
      (by fun_prop)]
    convert offsetExample_first_sq_fiber_integrable sz.1 sz.2 (ne_of_gt (hs 0)) using 1
    rfl
  · apply hbase.congr
    filter_upwards [offsetExample_base_positive ρ hρ m] with sz hs
    symm
    change (∫ y : OffsetExampleFiber,
      ‖(firstFactorial y.2 y.1.1 0) ^ 2‖ ∂offsetExampleKernel sz) =
        Real.exp (2 * sz.2 0) + Real.exp (sz.2 0) / sz.1 0
    rw [offsetExampleKernel,
      integral_map (by fun_prop) hfmeas.norm.aestronglyMeasurable]
    rw [show (fun x : Fin 1 → ℕ => ‖(firstFactorial x sz.1 0) ^ 2‖) =
        fun x => (firstFactorial x sz.1 0) ^ 2 by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]]
    exact offsetExample_first_sq_fiber_integral sz.1 sz.2 (hs 0)

-- @node: offsetExample_base_mul_exp_integrable
private lemma offsetExample_base_mul_exp_integrable (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (a : ℝ → ℝ) (hameas : Measurable a)
    (ha : Integrable a ρ) (t : ℝ) :
    Integrable (fun sz => a (sz.1 0) * Real.exp (t * sz.2 0))
      (offsetExampleBase ρ 0) := by
  have hp := measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin 1)))
    (S := (1 : Matrix (Fin 1) (Fin 1) ℝ)) Matrix.PosDef.one.posSemidef (i := 0)
  have hg : Integrable (fun v : EuclideanSpace ℝ (Fin 1) =>
      Real.exp (t * v 0)) (multivariateGaussian 0 1) :=
    (hp.integrable_comp (by fun_prop)).2 (integrable_exp_mul_gaussianReal t)
  let F : ℝ × EuclideanSpace ℝ (Fin 1) → (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
    fun u => (fun _ => u.1,
      fun i => offsetExampleEta 0 i + (WithLp.ofLp u.2) i)
  let G : ((Fin 1 → ℝ) × (Fin 1 → ℝ)) → ℝ :=
    fun sz => a (sz.1 0) * Real.exp (t * sz.2 0)
  have hF : Measurable F := by fun_prop
  have hG : Measurable G := by
    dsimp only [G]
    exact (hameas.comp ((measurable_pi_apply 0).comp measurable_fst)).mul
      (Real.measurable_exp.comp
        (measurable_const.mul ((measurable_pi_apply 0).comp measurable_snd)))
  apply (integrable_map_measure hG.aestronglyMeasurable hF.aemeasurable).2
  convert ha.mul_prod hg using 1
  funext u
  simp [F, G, offsetExampleEta]

-- @node: offsetExample_base_mul_exp_integral
private lemma offsetExample_base_mul_exp_integral (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (a : ℝ → ℝ) (hameas : Measurable a) (t : ℝ) :
    (∫ sz, a (sz.1 0) * Real.exp (t * sz.2 0) ∂offsetExampleBase ρ 0) =
      (∫ s, a s ∂ρ) *
        ∫ v : EuclideanSpace ℝ (Fin 1), Real.exp (t * v 0)
          ∂multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  let F : ℝ × EuclideanSpace ℝ (Fin 1) → (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
    fun u => (fun _ => u.1,
      fun i => offsetExampleEta 0 i + (WithLp.ofLp u.2) i)
  let G : ((Fin 1 → ℝ) × (Fin 1 → ℝ)) → ℝ :=
    fun sz => a (sz.1 0) * Real.exp (t * sz.2 0)
  have hF : Measurable F := by fun_prop
  have hG : Measurable G := by
    dsimp only [G]
    exact (hameas.comp ((measurable_pi_apply 0).comp measurable_fst)).mul
      (Real.measurable_exp.comp
        (measurable_const.mul ((measurable_pi_apply 0).comp measurable_snd)))
  rw [show offsetExampleBase ρ 0 =
      (ρ.prod (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))).map F from rfl,
    integral_map hF.aemeasurable hG.aestronglyMeasurable]
  simpa [F, G, offsetExampleEta] using integral_prod_mul a
    (fun v : EuclideanSpace ℝ (Fin 1) => Real.exp (t * v 0))

-- @node: offsetExample_condition_integral
private lemma offsetExample_condition_integral (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (H : ((Fin 1 → ℝ) × (Fin 1 → ℝ)) → ℝ)
    (hH : Measurable H) :
    (∫ ω, H ((ω 0).1) ∂offsetExampleLaw ρ) =
      ∫ sz, H sz ∂offsetExampleBase ρ 0 := by
  rw [← offsetExample_law_map_condition ρ 0,
    integral_map
      ((show Measurable (fun ω : OffsetExampleSpace => (ω 0).1) by fun_prop).aemeasurable)
      hH.aestronglyMeasurable]

-- @node: offsetExample_condition_integrable
private lemma offsetExample_condition_integrable (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (H : ((Fin 1 → ℝ) × (Fin 1 → ℝ)) → ℝ)
    (hH : Measurable H) (hi : Integrable H (offsetExampleBase ρ 0)) :
    Integrable (fun ω => H ((ω 0).1)) (offsetExampleLaw ρ) := by
  have hm : MeasurePreserving (fun ω : OffsetExampleSpace => (ω 0).1)
      (offsetExampleLaw ρ) (offsetExampleBase ρ 0) :=
    ⟨by fun_prop, offsetExample_law_map_condition ρ 0⟩
  exact (hm.integrable_comp hH.aestronglyMeasurable).2 hi

-- @node: offsetExample_first_integrable_law
private lemma offsetExample_first_integrable_law (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hρ : ∀ᵐ s ∂ρ, 0 < s)
    (hbase : Integrable (fun sz => Real.exp (sz.2 0)) (offsetExampleBase ρ 0)) :
    Integrable (fun ω : OffsetExampleSpace =>
      firstFactorial (ω 0).2 (ω 0).1.1 0) (offsetExampleLaw ρ) := by
  have hm : MeasurePreserving (fun ω : OffsetExampleSpace => ω 0)
      (offsetExampleLaw ρ) (offsetExampleEnvLaw ρ 0) :=
    ⟨by fun_prop, offsetExample_map_eval ρ 0⟩
  have hmeas : Measurable (fun y : OffsetExampleFiber =>
      firstFactorial y.2 y.1.1 0) := by
    simp only [firstFactorial]
    exact ((measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp
      ((measurable_pi_apply 0).comp measurable_snd)).div
        ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_fst))
  exact (hm.integrable_comp hmeas.aestronglyMeasurable).2
    (offsetExample_first_integrable ρ hρ 0 hbase)

-- @node: offsetExample_first_sq_integrable_law
private lemma offsetExample_first_sq_integrable_law (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hρ : ∀ᵐ s ∂ρ, 0 < s)
    (hbase : Integrable (fun sz => Real.exp (2 * sz.2 0) +
      Real.exp (sz.2 0) / sz.1 0) (offsetExampleBase ρ 0)) :
    Integrable (fun ω : OffsetExampleSpace =>
      (firstFactorial (ω 0).2 (ω 0).1.1 0) ^ 2) (offsetExampleLaw ρ) := by
  have hm : MeasurePreserving (fun ω : OffsetExampleSpace => ω 0)
      (offsetExampleLaw ρ) (offsetExampleEnvLaw ρ 0) :=
    ⟨by fun_prop, offsetExample_map_eval ρ 0⟩
  have hmeas : Measurable (fun y : OffsetExampleFiber =>
      (firstFactorial y.2 y.1.1 0) ^ 2) := by
    simp only [firstFactorial]
    exact (((measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp
      ((measurable_pi_apply 0).comp measurable_snd)).div
        ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_fst))).pow_const 2
  exact (hm.integrable_comp hmeas.aestronglyMeasurable).2
    (offsetExample_first_sq_integrable ρ hρ 0 hbase)

-- @node: offsetExample_moment_difference
lemma offsetExample_moment_difference (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hρ : ∀ᵐ s ∂ρ, 0 < s)
    (hinv : Integrable (fun s : ℝ => s⁻¹) ρ)
    (hinv2 : Integrable (fun s : ℝ => s⁻¹ ^ 2) ρ) :
    let μ := offsetExampleLaw ρ
    let 𝔐 := offsetExampleModel ρ hρ
    (∫ ω, firstFactorial (𝔐.X 0 ω) (𝔐.S 0 ω) 0 *
        (firstFactorial (𝔐.X 0 ω) (𝔐.S 0 ω) 0 - 1) ∂μ) -
      ∫ ω, secondFactorial (𝔐.X 0 ω) (𝔐.S 0 ω) 0 ∂μ =
      ((∫ s, s⁻¹ ∂ρ) - 1) *
        ∫ v : EuclideanSpace ℝ (Fin 1), Real.exp (v 0)
          ∂multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  dsimp only
  let μ := offsetExampleLaw ρ
  let 𝔐 := offsetExampleModel ρ hρ
  let G := multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) ρ := integrable_const 1
  have hb1 := offsetExample_base_mul_exp_integrable ρ (fun _ => 1)
    measurable_const hone 1
  have hb2 := offsetExample_base_mul_exp_integrable ρ (fun _ => 1)
    measurable_const hone 2
  have hb3 := offsetExample_base_mul_exp_integrable ρ (fun _ => 1)
    measurable_const hone 3
  have hb4 := offsetExample_base_mul_exp_integrable ρ (fun _ => 1)
    measurable_const hone 4
  have hbinv1 := offsetExample_base_mul_exp_integrable ρ (fun s => s⁻¹)
    (by fun_prop) hinv 1
  have hbinv2 := offsetExample_base_mul_exp_integrable ρ (fun s => s⁻¹)
    (by fun_prop) hinv 3
  have hbinvSq := offsetExample_base_mul_exp_integrable ρ (fun s => s⁻¹ ^ 2)
    (by fun_prop) hinv2 2
  have hbaseU2 : Integrable (fun sz => Real.exp (2 * sz.2 0) +
      Real.exp (sz.2 0) / sz.1 0) (offsetExampleBase ρ 0) := by
    exact (hb2.add hbinv1).congr (ae_of_all _ fun sz => by
      simp [div_eq_mul_inv, mul_comm])
  have hbaseW2 : Integrable (fun sz => Real.exp (4 * sz.2 0) +
      4 * Real.exp (3 * sz.2 0) / sz.1 0 +
      2 * Real.exp (2 * sz.2 0) / sz.1 0 ^ 2) (offsetExampleBase ρ 0) := by
    exact (hb4.add (hbinv2.const_mul 4) |>.add (hbinvSq.const_mul 2)).congr
      (ae_of_all _ fun sz => by
        simp [div_eq_mul_inv]
        ring)
  have h1 := offsetExample_condition_integrable ρ
    (fun sz => Real.exp (sz.2 0)) (by fun_prop) (by simpa using hb1)
  have h2 := offsetExample_condition_integrable ρ
    (fun sz => Real.exp (2 * sz.2 0)) (by fun_prop) (by simpa using hb2)
  have hU2 := offsetExample_condition_integrable ρ
    (fun sz => Real.exp (2 * sz.2 0) + Real.exp (sz.2 0) / sz.1 0)
    (by fun_prop) hbaseU2
  have hW2 := offsetExample_condition_integrable ρ
    (fun sz => Real.exp (4 * sz.2 0) + 4 * Real.exp (3 * sz.2 0) / sz.1 0 +
      2 * Real.exp (2 * sz.2 0) / sz.1 0 ^ 2) (by fun_prop) hbaseW2
  let _ : IsProbabilityMeasure μ := offsetExample_law_probability ρ
  have hp : PoissonMeasurement μ
      (fun _ : Unit => fun _ : Unit => fun ω => (ω 0).1.2)
      (fun _ _ => fun ω => (ω 0).1.1) (fun _ _ => fun ω => (ω 0).2) := by
    intro _ _
    refine ⟨offsetExample_positive ρ hρ 0, ?_, ?_, ?_⟩
    · exact (show Measurable (fun ω : OffsetExampleSpace => (ω 0).1) by
        fun_prop).aemeasurable
    · exact (show Measurable (fun ω : OffsetExampleSpace => ω 0) by
        fun_prop).aemeasurable
    · rw [offsetExample_map_eval, offsetExampleEnvLaw,
          offsetExample_law_map_condition]
      rfl
  have hraw := poisson_mixture_adjusted_factorial_raw_moments μ
    (fun ω => (ω 0).1.1) (fun ω => (ω 0).1.2) (fun ω => (ω 0).2)
    hp 0 h1 h2 hU2 hW2
  have hUi := offsetExample_first_integrable_law ρ hρ (by simpa using hb1)
  have hU2i := offsetExample_first_sq_integrable_law ρ hρ hbaseU2
  have hleft : (∫ ω, firstFactorial (ω 0).2 (ω 0).1.1 0 *
      (firstFactorial (ω 0).2 (ω 0).1.1 0 - 1) ∂μ) =
      (∫ ω, (firstFactorial (ω 0).2 (ω 0).1.1 0) ^ 2 ∂μ) -
        ∫ ω, firstFactorial (ω 0).2 (ω 0).1.1 0 ∂μ := by
    rw [← integral_sub hU2i hUi]
    congr 1
    funext ω
    ring
  have hexp : (∫ ω, Real.exp ((ω 0).1.2 0) ∂μ) =
      ∫ v : EuclideanSpace ℝ (Fin 1), Real.exp (v 0) ∂G := by
    rw [offsetExample_condition_integral ρ (fun sz => Real.exp (sz.2 0)) (by fun_prop)]
    have h := offsetExample_base_mul_exp_integral ρ (fun _ => 1) measurable_const 1
    simpa [G] using h
  have hinvexp : (∫ ω, Real.exp ((ω 0).1.2 0) / (ω 0).1.1 0 ∂μ) =
      (∫ s, s⁻¹ ∂ρ) * ∫ v : EuclideanSpace ℝ (Fin 1), Real.exp (v 0) ∂G := by
    rw [offsetExample_condition_integral ρ
      (fun sz => Real.exp (sz.2 0) / sz.1 0) (by fun_prop)]
    calc
      ∫ sz, Real.exp (sz.2 0) / sz.1 0 ∂offsetExampleBase ρ 0 =
          ∫ sz, (sz.1 0)⁻¹ * Real.exp (1 * sz.2 0) ∂offsetExampleBase ρ 0 := by
            congr 1
            funext sz
            simp [div_eq_mul_inv, mul_comm]
      _ = (∫ s, s⁻¹ ∂ρ) * ∫ v : EuclideanSpace ℝ (Fin 1),
          Real.exp (1 * v 0) ∂multivariateGaussian 0
            (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
        offsetExample_base_mul_exp_integral ρ (fun s => s⁻¹) (by fun_prop) 1
      _ = _ := by simp [G]
  have hquot : Integrable
      (fun ω : OffsetExampleSpace => Real.exp ((ω 0).1.2 0) / (ω 0).1.1 0) μ := by
    exact (hU2.sub h2).congr (ae_of_all _ fun ω => by simp)
  change (∫ ω, firstFactorial (ω 0).2 (ω 0).1.1 0 *
      (firstFactorial (ω 0).2 (ω 0).1.1 0 - 1) ∂μ) -
      ∫ ω, secondFactorial (ω 0).2 (ω 0).1.1 0 ∂μ =
      ((∫ s, s⁻¹ ∂ρ) - 1) * ∫ v : EuclideanSpace ℝ (Fin 1),
        Real.exp (v 0) ∂G
  rw [hleft, hraw.2.1, hraw.1, hraw.2.2.1]
  rw [integral_add h2 hquot]
  rw [hexp, hinvexp]
  ring

-- @node: offsetExample_nonunit
lemma offsetExample_nonunit (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hpos : ∀ᵐ s ∂ρ, 0 < s) (hρ : ∀ᵐ s ∂ρ, s ≠ 1) (m : Fin 2) :
    ∀ᵐ ω ∂offsetExampleLaw ρ, (offsetExampleModel ρ hpos).S m ω 0 ≠ 1 := by
  change ∀ᵐ ω ∂offsetExampleLaw ρ, (ω m).1.1 0 ≠ 1
  have hm : MeasurableSet {s : ℝ | s ≠ 1} := (measurableSet_singleton 1).compl
  rw [← ae_map_iff
    ((by fun_prop : Measurable (fun ω : OffsetExampleSpace => (ω m).1.1 0))).aemeasurable
    hm, offsetExample_law_map_offset]
  exact hρ

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
