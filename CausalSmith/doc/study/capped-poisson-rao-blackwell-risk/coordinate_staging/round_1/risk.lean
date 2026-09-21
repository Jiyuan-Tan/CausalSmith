/-! ## Capped-Poisson Rao--Blackwell risk transfer -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Causalean.Stat

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.GraphMapProd
open Causalean.Stat

variable {X : Type*} [MeasurableSpace X]

/-- Given [a statistic on finite samples](hyp:T), [an overflow value](hyp:zOver),
[a fixed array](hyp:x), and [an auxiliary count](hyp:m), the [randomized capped
statistic](goal) evaluates `T` on the requested prefix off overflow and equals
the specified value on overflow. -/
def cappedStatistic {n : ℕ} (T : FiniteSample X → ℝ) (zOver : ℝ)
    (x : Fin n → X) (m : ℕ) : ℝ :=
  if h : m ≤ n then T (prefixOfLE x m h) else zOver

/-- If [the finite-sample statistic is measurable](hyp:hT), then [the capped
statistic is jointly measurable in the fixed array and auxiliary count](goal). -/
@[fun_prop]
theorem measurable_cappedStatistic {n : ℕ} {T : FiniteSample X → ℝ}
    (hT : Measurable T) (zOver : ℝ) :
    Measurable (fun z : (Fin n → X) × ℕ ↦
      cappedStatistic T zOver z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro m
  unfold cappedStatistic
  change Measurable (fun x : Fin n → X ↦
    if h : m ≤ n then T (prefixOfLE x m h) else zOver)
  split
  · exact hT.comp (measurable_prefixOfLE (X := X) ‹m ≤ n›)
  · exact measurable_const

/-- Given [a Poisson mean](hyp:lambda), the [auxiliary-count Markov kernel](goal)
sends each fixed array to that same array paired with an independent Poisson
count. -/
noncomputable def auxPoissonCountKernel {n : ℕ} (lambda : ℝ≥0) :
    Kernel (Fin n → X) ((Fin n → X) × ℕ) :=
  mechanismKernel (poissonMeasure lambda)
    (fun z : (Fin n → X) × ℕ ↦ z)

/-- The [auxiliary-count kernel](hyp:lambda) is [a Markov kernel](goal). -/
instance auxPoissonCountKernel.isMarkovKernel {n : ℕ} (lambda : ℝ≥0) :
    IsMarkovKernel (auxPoissonCountKernel (X := X) (n := n) lambda) := by
  unfold auxPoissonCountKernel
  exact instIsMarkovKernelMechanismKernel _ measurable_id

/-- For [an observation probability law](hyp:P), [a Poisson mean](hyp:lambda),
and [a fixed sample size](hyp:n),
[mixing the auxiliary-count kernel over the fixed iid sample law gives exactly
the product of that iid law and the Poisson count law](goal). -/
theorem auxPoissonCountKernel_comp_pi
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) (n : ℕ) :
    auxPoissonCountKernel (X := X) (n := n) lambda ∘ₘ
        Measure.pi (fun _ : Fin n ↦ P) =
      (Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda) := by
  -- Use `map_graph_prod_eq_compProd` with the identity mechanism, then take
  -- the second marginal (`Measure.snd_compProd`).
  have hgraph :
      Measure.map
          (fun p : (Fin n → X) × ℕ => (p.1, p))
          ((Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda)) =
        (Measure.pi (fun _ : Fin n ↦ P)).compProd
          (auxPoissonCountKernel lambda) := by
    simpa [auxPoissonCountKernel] using
      (map_graph_prod_eq_compProd
        (Measure.pi (fun _ : Fin n ↦ P)) (poissonMeasure lambda)
          (show Measurable (fun z : (Fin n → X) × ℕ ↦ z) from measurable_id))
  have hsnd := congrArg (Measure.map Prod.snd) hgraph
  rw [Measure.map_map measurable_snd
      (show Measurable (fun p : (Fin n → X) × ℕ => (p.1, p)) from
        measurable_fst.prodMk measurable_id)] at hsnd
  change _ = ((Measure.pi (fun _ : Fin n ↦ P)) ⊗ₘ
    auxPoissonCountKernel lambda).snd at hsnd
  rw [Measure.snd_compProd] at hsnd
  simpa [Function.comp_def] using hsnd.symm

/-- Given [a Poisson mean](hyp:lambda), [a statistic](hyp:T), and
[an overflow value](hyp:zOver), the [fixed-sample Rao--Blackwell statistic](goal)
is the mean of the capped statistic under the auxiliary-count kernel. -/
noncomputable def raoBlackwellStatistic {n : ℕ} (lambda : ℝ≥0)
    (T : FiniteSample X → ℝ) (zOver : ℝ) :
    (Fin n → X) → ℝ :=
  kernelMean (auxPoissonCountKernel lambda)
    (fun z ↦ cappedStatistic T zOver z.1 z.2)

/-- If [the finite-sample statistic is measurable](hyp:hT), then for [a fixed
array](hyp:x), [the Rao--Blackwell statistic equals the Poisson integral of the
capped prefix statistic](goal). -/
theorem raoBlackwellStatistic_eq_integral {n : ℕ} (lambda : ℝ≥0)
    (T : FiniteSample X → ℝ) (hT : Measurable T) (zOver : ℝ)
    (x : Fin n → X) :
    raoBlackwellStatistic lambda T zOver x =
      ∫ m : ℕ, cappedStatistic T zOver x m ∂poissonMeasure lambda := by
  -- Unfold the kernel mean, rewrite with `mechanismKernel_apply`, and use
  -- `integral_map` with `measurable_cappedStatistic hT zOver`.
  unfold raoBlackwellStatistic kernelMean auxPoissonCountKernel
  rw [mechanismKernel_apply _
    (show Measurable (fun z : (Fin n → X) × ℕ ↦ z) from measurable_id) x]
  exact integral_map measurable_prodMk_left.aemeasurable
    (measurable_cappedStatistic hT zOver).aestronglyMeasurable

/-! ## Restricted-risk bridge lemmas

These three statements isolate the measure-theoretic pieces of the headline
transfer theorem: transport on the nonoverflow restriction, evaluation on the
overflow restriction, and monotonicity when the count restriction is removed.
-/

/-- For [an observation probability law](hyp:P), [a Poisson mean](hyp:lambda),
[a fixed sample size](hyp:n), [a measurable finite-sample statistic](hyp:hT),
[an overflow value](hyp:zOver), and [a target](hyp:theta), [the squared risk of
the capped statistic on the nonoverflow restriction equals the squared risk of
the original statistic under the correspondingly restricted finite-Poisson
law](goal). -/
theorem sqRisk_cappedStatistic_restrict_nonoverflow_eq
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) (n : ℕ)
    {T : FiniteSample X → ℝ} (hT : Measurable T) (zOver theta : ℝ) :
    sqRisk
        (((Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda)).restrict
          (Prod.snd ⁻¹' Set.Iic n))
        (fun z ↦ cappedStatistic T zOver z.1 z.2) theta =
      sqRisk
        ((finitePoissonSampleLaw P lambda).restrict
          (FiniteSample.count ⁻¹' Set.Iic n)) T theta := by
  -- On the restricted source, `cappedStatistic` is the squared loss pulled
  -- back along `totalizedPrefix`; use `integral_map` and
  -- `map_totalizedPrefix_restrict_nonoverflow`.
  let overflow : FiniteSample X := ⟨0, fun i => Fin.elim0 i⟩
  unfold sqRisk
  rw [← map_totalizedPrefix_restrict_nonoverflow P lambda n overflow]
  rw [integral_map
    (μ := ((Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda)).restrict
      (Prod.snd ⁻¹' Set.Iic n))
    (φ := fun z : (Fin n → X) × ℕ ↦ totalizedPrefix overflow z.1 z.2)
    (f := fun s : FiniteSample X ↦ (T s - theta) ^ 2)
    (measurable_totalizedPrefix overflow).aemeasurable
    ((hT.sub measurable_const).pow_const 2).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurable_snd measurableSet_Iic)] with z hz
  have hzn : z.2 ≤ n := hz
  simp [cappedStatistic, totalizedPrefix, cappedPrefix, hzn]

/-- For [an observation probability law](hyp:P), [a Poisson mean](hyp:lambda),
[a fixed sample size](hyp:n), [a statistic](hyp:T), [an overflow value](hyp:zOver),
and [a target](hyp:theta), [the squared risk of the capped statistic on the
overflow restriction is its constant overflow loss times the Poisson overflow
probability](goal). -/
theorem sqRisk_cappedStatistic_restrict_overflow_eq
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) (n : ℕ)
    (T : FiniteSample X → ℝ) (zOver theta : ℝ) :
    sqRisk
        (((Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda)).restrict
          (Prod.snd ⁻¹' Set.Ioi n))
        (fun z ↦ cappedStatistic T zOver z.1 z.2) theta =
      (zOver - theta) ^ 2 * (poissonMeasure lambda).real (Set.Ioi n) := by
  -- The capped statistic is constant on `m > n`; evaluate the restricted
  -- integral and the product-event mass using that the iid law has mass one.
  unfold sqRisk
  have hae : ∀ᵐ z ∂
      ((Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda)).restrict
        (Prod.snd ⁻¹' Set.Ioi n),
      (cappedStatistic T zOver z.1 z.2 - theta) ^ 2 =
        (zOver - theta) ^ 2 := by
    filter_upwards [ae_restrict_mem (measurable_snd measurableSet_Ioi)] with z hz
    change n < z.2 at hz
    simp [cappedStatistic, not_le_of_gt hz]
  have hset : (Prod.snd : ((Fin n → X) × ℕ) → ℕ) ⁻¹' Set.Ioi n =
      (Set.univ : Set (Fin n → X)) ×ˢ Set.Ioi n := by
    ext z
    simp
  rw [integral_congr_ae hae, integral_const]
  simp only [smul_eq_mul, measureReal_def]
  rw [Measure.restrict_apply_univ, hset,
    Measure.prod_apply (MeasurableSet.univ.prod measurableSet_Ioi)]
  simp [mul_comm]

/-- For [an observation probability law](hyp:P), [a Poisson mean](hyp:lambda),
[a fixed sample size](hyp:n), [a measurable uniformly bounded statistic](hyp:hT,hTb),
and [a target](hyp:theta), [restricting the finite-Poisson law to counts at most
the fixed sample size cannot increase squared risk](goal). -/
theorem sqRisk_finitePoisson_restrict_nonoverflow_le
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) (n : ℕ)
    {T : FiniteSample X → ℝ} (hT : Measurable T)
    (hTb : UniformlyBounded T) (theta : ℝ) :
    sqRisk
        ((finitePoissonSampleLaw P lambda).restrict
          (FiniteSample.count ⁻¹' Set.Iic n)) T theta ≤
      sqRisk (finitePoissonSampleLaw P lambda) T theta := by
  -- Split the full integral over the measurable count event and its
  -- complement, then discard the nonnegative complementary squared loss.
  obtain ⟨M, hM, hTb⟩ := hTb
  let μ : Measure (FiniteSample X) := finitePoissonSampleLaw P lambda
  let s : Set (FiniteSample X) := FiniteSample.count ⁻¹' Set.Iic n
  have hs : MeasurableSet s := by
    exact measurable_finiteSample_count measurableSet_Iic
  have hlossInt : Integrable (fun z => (T z - theta) ^ 2) μ := by
    refine (integrable_const ((M + |theta|) ^ 2)).mono'
      ((hT.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg hM (abs_nonneg theta))]
    exact (abs_sub _ _).trans (add_le_add (hTb z) le_rfl)
  have hsInt : Integrable (fun z => (T z - theta) ^ 2) (μ.restrict s) :=
    hlossInt.restrict
  have hscInt : Integrable (fun z => (T z - theta) ^ 2) (μ.restrict sᶜ) :=
    hlossInt.restrict
  unfold sqRisk
  change (∫ z, (T z - theta) ^ 2 ∂μ.restrict s) ≤
    ∫ z, (T z - theta) ^ 2 ∂μ
  conv_rhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hs,
    integral_add_measure hsInt hscInt]
  exact le_add_of_nonneg_right
    (integral_nonneg fun z => sq_nonneg (T z - theta))

/-- For [an observation probability law](hyp:P), [a Poisson mean](hyp:lambda),
and [a fixed sample size](hyp:n), if [the statistic is measurable](hyp:hT),
[the interval is ordered](hyp:hab),
[the statistic stays in the interval](hyp:hTmem), [the target is in the
interval](hyp:htheta), and [the overflow value is in the interval](hyp:hzOver),
then [the fixed-iid squared risk of the Rao--Blackwell statistic is at most the
uncapped finite-Poisson risk plus the squared interval diameter times the
Poisson overflow probability](goal). -/
theorem sqRisk_raoBlackwellStatistic_le
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) (n : ℕ)
    {T : FiniteSample X → ℝ} (hT : Measurable T)
    {a b theta zOver : ℝ} (hab : a ≤ b)
    (hTmem : ∀ s, T s ∈ Set.Icc a b) (htheta : theta ∈ Set.Icc a b)
    (hzOver : zOver ∈ Set.Icc a b) :
    sqRisk (Measure.pi (fun _ : Fin n ↦ P))
        (raoBlackwellStatistic lambda T zOver) theta ≤
      sqRisk (finitePoissonSampleLaw P lambda) T theta +
        (b - a) ^ 2 * (poissonMeasure lambda).real (Set.Ioi n) := by
  -- Apply `sqRisk_kernelMean_le_comp` to the bounded capped statistic, rewrite
  -- the composed law with `auxPoissonCountKernel_comp_pi`, and split its risk
  -- integral over `m ≤ n` and `m > n`.  Rewrite the first restriction with
  -- `map_totalizedPrefix_restrict_nonoverflow`; bound the overflow loss by
  -- the squared interval diameter before integrating its indicator.
  have hTb : UniformlyBounded T := by
    refine ⟨max |a| |b|, ?_, ?_⟩
    · exact (abs_nonneg a).trans (le_max_left _ _)
    · intro s
      exact abs_le_max_abs_abs (hTmem s).1 (hTmem s).2
  have hCappedBound : UniformlyBounded
      (fun z : (Fin n → X) × ℕ ↦ cappedStatistic T zOver z.1 z.2) := by
    refine ⟨max |a| |b|, ?_, ?_⟩
    · exact (abs_nonneg a).trans (le_max_left _ _)
    · intro z
      by_cases h : z.2 ≤ n
      · simp only [cappedStatistic, h, ↓reduceDIte]
        exact abs_le_max_abs_abs (hTmem _).1 (hTmem _).2
      · simp only [cappedStatistic, h, ↓reduceDIte]
        exact abs_le_max_abs_abs hzOver.1 hzOver.2
  let μ : Measure ((Fin n → X) × ℕ) :=
    (Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda)
  let s : Set ((Fin n → X) × ℕ) := Prod.snd ⁻¹' Set.Iic n
  have hs : MeasurableSet s := measurable_snd measurableSet_Iic
  obtain ⟨M, hM, hCappedBoundM⟩ := hCappedBound
  have hlossInt : Integrable
      (fun z : (Fin n → X) × ℕ =>
        (cappedStatistic T zOver z.1 z.2 - theta) ^ 2) μ := by
    refine (integrable_const ((M + |theta|) ^ 2)).mono'
      (((measurable_cappedStatistic hT zOver).sub measurable_const).pow_const 2
        ).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg hM (abs_nonneg theta))]
    exact (abs_sub _ _).trans (add_le_add (hCappedBoundM z) le_rfl)
  have hsplit :
      sqRisk μ (fun z : (Fin n → X) × ℕ ↦
          cappedStatistic T zOver z.1 z.2) theta =
        sqRisk (μ.restrict s) (fun z : (Fin n → X) × ℕ ↦
            cappedStatistic T zOver z.1 z.2) theta +
          sqRisk (μ.restrict sᶜ) (fun z : (Fin n → X) × ℕ ↦
            cappedStatistic T zOver z.1 z.2) theta := by
    unfold sqRisk
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hs,
      integral_add_measure hlossInt.restrict hlossInt.restrict]
  have hsc : sᶜ = Prod.snd ⁻¹' Set.Ioi n := by
    rw [← Set.preimage_compl, Set.compl_Iic]
  have hoverflowSq : (zOver - theta) ^ 2 ≤ (b - a) ^ 2 := by
    have hdist : |zOver - theta| ≤ b - a := by
      simpa [Real.dist_eq] using Real.dist_le_of_mem_Icc hzOver htheta
    rw [← sq_abs (zOver - theta)]
    exact (sq_le_sq₀ (abs_nonneg _) (sub_nonneg.mpr hab)).2 hdist
  have hoverflowProb : 0 ≤ (poissonMeasure lambda).real (Set.Ioi n) := by
    positivity
  calc
    sqRisk (Measure.pi (fun _ : Fin n ↦ P))
          (raoBlackwellStatistic lambda T zOver) theta ≤
        sqRisk (auxPoissonCountKernel lambda ∘ₘ
            Measure.pi (fun _ : Fin n ↦ P))
          (fun z : (Fin n → X) × ℕ ↦ cappedStatistic T zOver z.1 z.2) theta := by
      exact sqRisk_kernelMean_le_comp
        (Measure.pi (fun _ : Fin n ↦ P)) (auxPoissonCountKernel lambda)
          (measurable_cappedStatistic hT zOver)
          ⟨M, hM, hCappedBoundM⟩ theta
    _ = sqRisk μ (fun z : (Fin n → X) × ℕ ↦
          cappedStatistic T zOver z.1 z.2) theta := by
      rw [auxPoissonCountKernel_comp_pi]
    _ = sqRisk (μ.restrict s) (fun z : (Fin n → X) × ℕ ↦
            cappedStatistic T zOver z.1 z.2) theta +
          sqRisk (μ.restrict sᶜ) (fun z : (Fin n → X) × ℕ ↦
            cappedStatistic T zOver z.1 z.2) theta := hsplit
    _ = sqRisk
          ((finitePoissonSampleLaw P lambda).restrict
            (FiniteSample.count ⁻¹' Set.Iic n)) T theta +
        (zOver - theta) ^ 2 * (poissonMeasure lambda).real (Set.Ioi n) := by
      rw [show μ.restrict s =
          ((Measure.pi (fun _ : Fin n ↦ P)).prod
            (poissonMeasure lambda)).restrict (Prod.snd ⁻¹' Set.Iic n) from rfl,
        sqRisk_cappedStatistic_restrict_nonoverflow_eq P lambda n hT zOver theta,
        hsc]
      exact congrArg
        (fun r => sqRisk
          ((finitePoissonSampleLaw P lambda).restrict
            (FiniteSample.count ⁻¹' Set.Iic n)) T theta + r)
        (sqRisk_cappedStatistic_restrict_overflow_eq
          P lambda n T zOver theta)
    _ ≤ sqRisk (finitePoissonSampleLaw P lambda) T theta +
        (b - a) ^ 2 * (poissonMeasure lambda).real (Set.Ioi n) :=
      add_le_add
        (sqRisk_finitePoisson_restrict_nonoverflow_le
          P lambda n hT hTb theta)
        (mul_le_mul_of_nonneg_right hoverflowSq hoverflowProb)

/-- For [an observation probability law](hyp:P), [a Poisson mean](hyp:lambda),
and [a fixed sample size](hyp:n), under
[measurability of the statistic](hyp:hT),
[unit-interval bounds on the statistic](hyp:hTmem), [target](hyp:htheta),
and [overflow value](hyp:hzOver), [the fixed-iid Rao--Blackwell risk is at most
the uncapped finite-Poisson risk plus exactly the overflow probability](goal). -/
theorem sqRisk_raoBlackwellStatistic_unitInterval_le
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) (n : ℕ)
    {T : FiniteSample X → ℝ} (hT : Measurable T)
    {theta zOver : ℝ} (hTmem : ∀ s, T s ∈ Set.Icc (0 : ℝ) 1)
    (htheta : theta ∈ Set.Icc (0 : ℝ) 1)
    (hzOver : zOver ∈ Set.Icc (0 : ℝ) 1) :
    sqRisk (Measure.pi (fun _ : Fin n ↦ P))
        (raoBlackwellStatistic lambda T zOver) theta ≤
      sqRisk (finitePoissonSampleLaw P lambda) T theta +
        (poissonMeasure lambda).real (Set.Ioi n) := by
  -- Specialize the interval theorem to `[0,1]` and normalize `(1 - 0)^2`.
  simpa using
    (sqRisk_raoBlackwellStatistic_le P lambda n hT
      (a := (0 : ℝ)) (b := 1) (theta := theta) (zOver := zOver)
      (by norm_num) hTmem htheta hzOver)

end Causalean.Stat
