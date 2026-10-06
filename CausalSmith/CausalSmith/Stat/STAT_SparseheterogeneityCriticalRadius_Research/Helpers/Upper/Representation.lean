module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Estimator
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Causalean.Stat.Sample.PiTransport
public import Causalean.Stat.Minimax.MarkovKernelTransport

/-! Probability-law representation of the finite Poisson averaging step. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- The finite estimator's displayed coefficient is exactly the product of
the two independent Poisson singleton probabilities. -/
lemma poissonWeight_eq_product_singletons (n u v : ℕ) :
    poissonWeight n u v =
      (poissonMeasure (Real.toNNReal (blockMean n))).real {u} *
        (poissonMeasure (Real.toNNReal (blockMean n))).real {v} := by
  have hm0 : 0 ≤ blockMean n := by
    simp only [blockMean, postPilotSize, pilotSize]
    positivity
  rw [poissonWeight, poissonMeasure_real_singleton,
    poissonMeasure_real_singleton]
  rw [Real.coe_toNNReal _ hm0]
  rw [pow_add]
  rw [show Real.exp (-2 * blockMean n) =
      Real.exp (-blockMean n) * Real.exp (-blockMean n) by
    rw [← Real.exp_add]
    congr 1
    ring]
  ring

/-- Coordinate embedding of the post-pilot block into the full sample. -/
def postPilotIndex (n : ℕ) (i : Fin (postPilotSize n)) : Fin n :=
  ⟨pilotSize n + i, by
    have hi := i.isLt
    simp only [postPilotSize, pilotSize] at hi ⊢
    omega⟩

def postPilotSample (n : ℕ) (sample : Fin n → SampleObs n) :
    Fin (postPilotSize n) → SampleObs n :=
  fun i => sample (postPilotIndex n i)

-- keep: measurability certificate for the deterministic post-pilot projection
lemma measurable_postPilotSample (n : ℕ) : Measurable (postPilotSample n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply (postPilotIndex n i)

/-- The first part of a nonoverflowing triangular post-pilot split. -/
def classifierPrefix (n u v : ℕ) (h : u + v ≤ postPilotSize n)
    (sample : Fin n → SampleObs n) : Fin u → SampleObs n :=
  fun i => sample ⟨pilotSize n + i, by
    have hi := i.isLt
    simp only [postPilotSize, pilotSize] at h ⊢
    omega⟩

/-- The contiguous second part of a nonoverflowing triangular post-pilot split. -/
def estimationPrefix (n u v : ℕ) (h : u + v ≤ postPilotSize n)
    (sample : Fin n → SampleObs n) : Fin v → SampleObs n :=
  fun i => sample ⟨pilotSize n + u + i, by
    have hi := i.isLt
    simp only [postPilotSize, pilotSize] at h ⊢
    omega⟩

lemma measurable_classifierPrefix (n u v : ℕ) (h : u + v ≤ postPilotSize n) :
    Measurable (classifierPrefix n u v h) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

lemma measurable_estimationPrefix (n u v : ℕ) (h : u + v ≤ postPilotSize n) :
    Measurable (estimationPrefix n u v h) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

abbrev PostPilotCoord (n : ℕ) := {i : Fin n // pilotSize n ≤ i.val}

def restrictPostPilot (n : ℕ) (sample : Fin n → SampleObs n) :
    PostPilotCoord n → SampleObs n := fun i => sample i.1

/-- The retained post-pilot coordinates of the fixed i.i.d. experiment still
have their exact product law. -/
lemma map_restrictPostPilot_productLaw {n : ℕ} (P : Law n) :
    Measure.map (restrictPostPilot n)
        (DiscreteAteHeterogeneityFrontier.productLaw n P) =
      Measure.pi (fun _ : PostPilotCoord n => P.observedLaw) := by
  unfold DiscreteAteHeterogeneityFrontier.productLaw restrictPostPilot
  exact Causalean.Stat.map_pi_restrict P.observedLaw
    (fun i : Fin n => pilotSize n ≤ i.val)

abbrev SampleSliceCoord (n lo hi : ℕ) := {i : Fin n // lo ≤ i.val ∧ i.val < hi}

def restrictSampleSlice (n lo hi : ℕ) (sample : Fin n → SampleObs n) :
    SampleSliceCoord n lo hi → SampleObs n := fun i => sample i.1

/-- Any deterministic contiguous slice of the fixed i.i.d. sample has its
own exact product law.  The classifier and estimation prefixes are obtained
by taking `[pilotSize,pilotSize+u)` and `[pilotSize+u,pilotSize+u+v)`. -/
-- keep: general contiguous-slice product-law theorem for prefix representations
lemma map_restrictSampleSlice_productLaw {n lo hi : ℕ} (P : Law n) :
    Measure.map (restrictSampleSlice n lo hi)
        (DiscreteAteHeterogeneityFrontier.productLaw n P) =
      Measure.pi (fun _ : SampleSliceCoord n lo hi => P.observedLaw) := by
  unfold DiscreteAteHeterogeneityFrontier.productLaw restrictSampleSlice
  exact Causalean.Stat.map_pi_restrict P.observedLaw
    (fun i : Fin n => lo ≤ i.val ∧ i.val < hi)

/-- Coordinates used by a fixed nonoverflowing triangular split. -/
abbrev UsedPrefixCoord (n u v : ℕ) :=
  {i : Fin n // pilotSize n ≤ i.val ∧ i.val < pilotSize n + u + v}

def restrictUsedPrefix (n u v : ℕ) (sample : Fin n → SampleObs n) :
    UsedPrefixCoord n u v → SampleObs n := fun i => sample i.1

/-- Within the used post-pilot prefix, the classifier coordinates are exactly
the coordinates before the classifier/estimation cut. -/
def isClassifierCoord (n u : ℕ) (i : UsedPrefixCoord n u v) : Prop :=
  i.1.val < pilotSize n + u

noncomputable instance decidablePred_isClassifierCoord (n u v : ℕ) :
    DecidablePred (isClassifierCoord (v := v) n u) := Classical.decPred _

/-- The exact joint law of the two sides of a fixed triangular prefix split.
The second factor is the complement *inside the used prefix*, hence it consists
precisely of the contiguous estimation coordinates. -/
-- keep: exact joint law for the classifier and estimation prefix split
lemma map_splitUsedPrefix_productLaw {n u v : ℕ} (P : Law n) :
    Measure.map
        (fun sample =>
          MeasurableEquiv.piEquivPiSubtypeProd
            (fun _ : UsedPrefixCoord n u v => SampleObs n)
            (isClassifierCoord n u) (restrictUsedPrefix n u v sample))
        (DiscreteAteHeterogeneityFrontier.productLaw n P) =
      (Measure.pi fun _ : Subtype (isClassifierCoord n u) => P.observedLaw).prod
        (Measure.pi fun _ : Subtype (fun i => ¬ isClassifierCoord n u i) =>
          P.observedLaw) := by
  classical
  unfold DiscreteAteHeterogeneityFrontier.productLaw restrictUsedPrefix
  let hrestrict := Causalean.Stat.measurePreserving_pi_restrict P.observedLaw
    (fun i : Fin n => pilotSize n ≤ i.val ∧ i.val < pilotSize n + u + v)
  let hsplit := MeasureTheory.measurePreserving_piEquivPiSubtypeProd
    (μ := fun _ : UsedPrefixCoord n u v => P.observedLaw)
    (isClassifierCoord n u)
  exact (hsplit.comp hrestrict).map_eq

abbrev ClassifierCoord (n u v : ℕ) :=
  Subtype (isClassifierCoord (v := v) n u)

abbrev EstimationCoord (n u v : ℕ) :=
  Subtype (fun i : UsedPrefixCoord n u v => ¬ isClassifierCoord n u i)

/-- Reindex the classifier side of a nonoverflowing used-prefix split by
`Fin u`, matching `classifierPrefix`. -/
def classifierCoordEquivFin (n u v : ℕ) (h : u + v ≤ postPilotSize n) :
    ClassifierCoord n u v ≃ Fin u where
  toFun i := ⟨i.1.1.val - pilotSize n, by
    have hlo := i.1.2.1
    have hhi := i.2
    unfold isClassifierCoord at hhi
    omega⟩
  invFun j := ⟨⟨⟨pilotSize n + j.val, by
    have hj := j.isLt
    simp only [postPilotSize, pilotSize] at h ⊢
    omega⟩, by
      change pilotSize n ≤ pilotSize n + j.val ∧
        pilotSize n + j.val < pilotSize n + u + v
      constructor
      · omega
      · have hj := j.isLt
        omega⟩, by
        change pilotSize n + j.val < pilotSize n + u
        exact Nat.add_lt_add_left j.isLt _⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    simp only
    exact Nat.add_sub_of_le i.1.2.1
  right_inv j := by
    apply Fin.ext
    simp

/-- Reindex the estimation side of a nonoverflowing used-prefix split by
`Fin v`, matching `estimationPrefix`. -/
def estimationCoordEquivFin (n u v : ℕ) (h : u + v ≤ postPilotSize n) :
    EstimationCoord n u v ≃ Fin v where
  toFun i := ⟨i.1.1.val - (pilotSize n + u), by
    have hused := i.1.2
    have hcut := i.2
    unfold isClassifierCoord at hcut
    omega⟩
  invFun j := ⟨⟨⟨pilotSize n + u + j.val, by
    have hj := j.isLt
    simp only [postPilotSize, pilotSize] at h ⊢
    omega⟩, by
      change pilotSize n ≤ pilotSize n + u + j.val ∧
        pilotSize n + u + j.val < pilotSize n + u + v
      constructor
      · omega
      · have hj := j.isLt
        omega⟩, by
        change ¬pilotSize n + u + j.val < pilotSize n + u
        omega⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    simp only
    have hcut := i.2
    unfold isClassifierCoord at hcut
    omega
  right_inv j := by
    apply Fin.ext
    simp

/-- Under the fixed i.i.d. law, the actual classifier and estimation prefixes
of every nonoverflowing triangular split are jointly independent i.i.d.
samples of sizes `u` and `v`. -/
lemma map_classifierPrefix_estimationPrefix_productLaw {n u v : ℕ}
    (P : Law n) (h : u + v ≤ postPilotSize n) :
    Measure.map
        (fun sample =>
          (classifierPrefix n u v h sample,
            estimationPrefix n u v h sample))
        (DiscreteAteHeterogeneityFrontier.productLaw n P) =
      (Measure.pi fun _ : Fin u => P.observedLaw).prod
        (Measure.pi fun _ : Fin v => P.observedLaw) := by
  classical
  let ec := classifierCoordEquivFin n u v h
  let ee := estimationCoordEquivFin n u v h
  let hrestrict := Causalean.Stat.measurePreserving_pi_restrict P.observedLaw
    (fun i : Fin n => pilotSize n ≤ i.val ∧ i.val < pilotSize n + u + v)
  let hsplit := MeasureTheory.measurePreserving_piEquivPiSubtypeProd
    (μ := fun _ : UsedPrefixCoord n u v => P.observedLaw)
    (isClassifierCoord n u)
  let hc := MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : Fin u => P.observedLaw) ec
  let he := MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : Fin v => P.observedLaw) ee
  have hjoint := (hc.prod he).comp (hsplit.comp hrestrict)
  unfold DiscreteAteHeterogeneityFrontier.productLaw
  rw [← hjoint.map_eq]
  congr 1
  funext sample
  apply Prod.ext
  · funext j
    simp [Function.comp_apply, ec, classifierCoordEquivFin,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply,
      MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd]
    rfl
  · funext j
    simp [Function.comp_apply, ee, estimationCoordEquivFin,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply,
      MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd]
    rfl

noncomputable def fixedPrefixSamples (n u v : ℕ)
    (h : u + v ≤ postPilotSize n) (sample : Fin n → SampleObs n) :
    FiniteSample (SampleObs n) × FiniteSample (SampleObs n) :=
  (fixedSizeEmbed u (classifierPrefix n u v h sample),
    fixedSizeEmbed v (estimationPrefix n u v h sample))

lemma measurable_fixedPrefixSamples (n u v : ℕ)
    (h : u + v ≤ postPilotSize n) :
    Measurable (fixedPrefixSamples n u v h) := by
  exact (measurable_fixedSizeEmbed u).comp
    (measurable_classifierPrefix n u v h) |>.prodMk
      ((measurable_fixedSizeEmbed v).comp
        (measurable_estimationPrefix n u v h))

/-- Fixed nonoverflowing actual prefixes have the exact pair of fixed-count
i.i.d. fibre laws used in the finite-Poisson construction. -/
lemma map_fixedPrefixSamples_productLaw {n u v : ℕ} (P : Law n)
    (h : u + v ≤ postPilotSize n) :
    Measure.map (fixedPrefixSamples n u v h)
        (DiscreteAteHeterogeneityFrontier.productLaw n P) =
      (Measure.map (fixedSizeEmbed u)
        (Measure.pi fun _ : Fin u => P.observedLaw)).prod
      (Measure.map (fixedSizeEmbed v)
        (Measure.pi fun _ : Fin v => P.observedLaw)) := by
  let prefixes := fun sample : Fin n → SampleObs n =>
    (classifierPrefix n u v h sample, estimationPrefix n u v h sample)
  let embed : ((Fin u → SampleObs n) × (Fin v → SampleObs n)) →
      (FiniteSample (SampleObs n) × FiniteSample (SampleObs n)) :=
    Prod.map (fixedSizeEmbed u) (fixedSizeEmbed v)
  change Measure.map (embed ∘ prefixes)
      (DiscreteAteHeterogeneityFrontier.productLaw n P) = _
  rw [← Measure.map_map
    ((measurable_fixedSizeEmbed u).prodMap (measurable_fixedSizeEmbed v))
    ((measurable_classifierPrefix n u v h).prodMk
      (measurable_estimationPrefix n u v h))]
  rw [map_classifierPrefix_estimationPrefix_productLaw P h]
  rw [← Measure.map_prod_map _ _
    (measurable_fixedSizeEmbed u) (measurable_fixedSizeEmbed v)]

/-- Exact count-fibre form of the fixed-prefix representation: after weighting
by the two Poisson atoms, the actual prefix law is the corresponding pair of
finite-Poisson count fibres. -/
-- keep: count-fibre identity connecting fixed prefixes to Poisson sample laws
lemma smul_map_fixedPrefixSamples_eq_poisson_countFibres {n u v : ℕ}
    (P : Law n) (lam : ℝ≥0) (h : u + v ≤ postPilotSize n) :
    ((poissonMeasure lam {u}) * (poissonMeasure lam {v})) •
        Measure.map (fixedPrefixSamples n u v h)
          (DiscreteAteHeterogeneityFrontier.productLaw n P) =
      ((finitePoissonSampleLaw P.observedLaw lam).restrict
          (FiniteSample.count ⁻¹' ({u} : Set ℕ))).prod
        ((finitePoissonSampleLaw P.observedLaw lam).restrict
          (FiniteSample.count ⁻¹' ({v} : Set ℕ))) := by
  rw [finitePoissonSampleLaw_restrict_count_eq,
    finitePoissonSampleLaw_restrict_count_eq,
    map_fixedPrefixSamples_productLaw P h]
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

/-- The centered part of the triangular Poisson mixture is exactly its finite
double sum.  Centering by `c` makes the integrand finitely supported, so this
identity applies directly to the estimator's fallback value. -/
lemma triangularPoisson_correction_integral (n : ℕ) (F : ℕ × ℕ → ℝ) (c C : ℝ)
    (hF : ∀ z, |F z| ≤ C) :
    ∫ z : ℕ × ℕ,
        (if z.1 + z.2 ≤ postPilotSize n then F z - c else 0)
      ∂((poissonMeasure (Real.toNNReal (blockMean n))).prod
        (poissonMeasure (Real.toNNReal (blockMean n)))) =
      ∑ u ∈ Finset.range (postPilotSize n + 1),
        ∑ v ∈ Finset.range (postPilotSize n - u + 1),
          poissonWeight n u v * (F (u, v) - c) := by
  let lam := Real.toNNReal (blockMean n)
  let g : ℕ × ℕ → ℝ := fun z =>
    if z.1 + z.2 ≤ postPilotSize n then F z - c else 0
  have hgBound (z : ℕ × ℕ) : |g z| ≤ C + |c| := by
    dsimp [g]
    split_ifs
    · calc
        |F z - c| ≤ |F z| + |c| := abs_sub _ _
        _ ≤ C + |c| := by linarith [hF z]
    · simp
      have hC : 0 ≤ C := le_trans (abs_nonneg (F z)) (hF z)
      positivity
  have hgInt : Integrable g ((poissonMeasure lam).prod (poissonMeasure lam)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (C + |c|)
    filter_upwards [] with z
    simpa [Real.norm_eq_abs] using hgBound z
  change (∫ z, g z ∂((poissonMeasure lam).prod (poissonMeasure lam))) = _
  rw [integral_prod _ hgInt, integral_poissonMeasure]
  simp only [smul_eq_mul]
  rw [tsum_eq_sum (s := Finset.range (postPilotSize n + 1))]
  · apply Finset.sum_congr rfl
    intro u hu
    have hu' : u ≤ postPilotSize n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
    rw [integral_poissonMeasure]
    simp only [smul_eq_mul]
    rw [tsum_eq_sum (s := Finset.range (postPilotSize n - u + 1))]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      have hv' : v ≤ postPilotSize n - u :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hv)
      have huv : u + v ≤ postPilotSize n := by omega
      simp only [g, huv, ↓reduceIte]
      have hw := poissonWeight_eq_product_singletons n u v
      rw [poissonMeasure_real_singleton, poissonMeasure_real_singleton] at hw
      rw [hw]
      ring
    · intro v hv
      have hv' : postPilotSize n - u < v := by
        simpa using hv
      have huv : ¬u + v ≤ postPilotSize n := by omega
      simp [g, huv]
  · intro u hu
    have hu' : postPilotSize n < u := by simpa using hu
    have huv (v : ℕ) : ¬u + v ≤ postPilotSize n := by omega
    simp [g, huv]

/-- Exact finite-triangle Poisson averaging with fallback `c`. -/
lemma triangularPoisson_average_eq (n : ℕ) (F : ℕ × ℕ → ℝ) (c C : ℝ)
    (hF : ∀ z, |F z| ≤ C) :
    ∫ z : ℕ × ℕ,
        (if z.1 + z.2 ≤ postPilotSize n then F z else c)
      ∂((poissonMeasure (Real.toNNReal (blockMean n))).prod
        (poissonMeasure (Real.toNNReal (blockMean n)))) =
      (∑ u ∈ Finset.range (postPilotSize n + 1),
        ∑ v ∈ Finset.range (postPilotSize n - u + 1),
          poissonWeight n u v * F (u, v)) +
      (1 - ∑ u ∈ Finset.range (postPilotSize n + 1),
        ∑ v ∈ Finset.range (postPilotSize n - u + 1),
          poissonWeight n u v) * c := by
  let μ := (poissonMeasure (Real.toNNReal (blockMean n))).prod
    (poissonMeasure (Real.toNNReal (blockMean n)))
  let g : ℕ × ℕ → ℝ := fun z =>
    if z.1 + z.2 ≤ postPilotSize n then F z - c else 0
  have hgBound (z : ℕ × ℕ) : |g z| ≤ C + |c| := by
    dsimp [g]
    split_ifs
    · calc
        |F z - c| ≤ |F z| + |c| := abs_sub _ _
        _ ≤ C + |c| := by linarith [hF z]
    · simp
      have hC : 0 ≤ C := le_trans (abs_nonneg (F z)) (hF z)
      positivity
  have hgInt : Integrable g μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (C + |c|)
    filter_upwards [] with z
    simpa [Real.norm_eq_abs] using hgBound z
  have hpoint (z : ℕ × ℕ) :
      (if z.1 + z.2 ≤ postPilotSize n then F z else c) = c + g z := by
    dsimp [g]
    split_ifs <;> ring
  calc
    _ = ∫ z : ℕ × ℕ, (c + g z) ∂μ := integral_congr_ae <|
      Filter.Eventually.of_forall hpoint
    _ = c + ∫ z : ℕ × ℕ, g z ∂μ := by
      rw [integral_add (integrable_const c) hgInt, integral_const]
      simp
    _ = c + ∑ u ∈ Finset.range (postPilotSize n + 1),
        ∑ v ∈ Finset.range (postPilotSize n - u + 1),
          poissonWeight n u v * (F (u, v) - c) := by
      rw [triangularPoisson_correction_integral n F c C hF]
    _ = _ := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      have hc :
          (∑ u ∈ Finset.range (postPilotSize n + 1),
            ∑ v ∈ Finset.range (postPilotSize n - u + 1),
              poissonWeight n u v * c) =
            (∑ u ∈ Finset.range (postPilotSize n + 1),
              ∑ v ∈ Finset.range (postPilotSize n - u + 1),
                poissonWeight n u v) * c := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.sum_mul]
      rw [hc]
      ring

/-- The implemented finite estimator is exactly the expectation of its
triangularly capped randomized Poisson-count output. -/
lemma knownRadiusEstimator_eq_integral_poissonCounts (n : ℕ) (M rho : ℝ)
    (hM : 0 ≤ M) (sample : Fin n → SampleObs n) :
    knownRadiusEstimator n M rho sample =
      ∫ z : ℕ × ℕ,
        (if z.1 + z.2 ≤ postPilotSize n then
          conditionalEstimator n M rho sample z.1 z.2
        else pilotTau n M sample)
      ∂((poissonMeasure (Real.toNNReal (blockMean n))).prod
        (poissonMeasure (Real.toNNReal (blockMean n)))) := by
  have hbound (z : ℕ × ℕ) :
      |conditionalEstimator n M rho sample z.1 z.2| ≤ M := by
    exact abs_le.mpr (conditionalEstimator_range n M rho hM sample z.1 z.2)
  rw [triangularPoisson_average_eq n
    (fun z => conditionalEstimator n M rho sample z.1 z.2)
    (pilotTau n M sample) M hbound]
  rfl

noncomputable def poissonCountLaw (n : ℕ) : Measure (ℕ × ℕ) :=
  (poissonMeasure (Real.toNNReal (blockMean n))).prod
    (poissonMeasure (Real.toNNReal (blockMean n)))

noncomputable instance poissonCountLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (poissonCountLaw n) := by
  unfold poissonCountLaw
  infer_instance

/-- Randomization kernel retaining the fixed sample and adjoining two
independent Poisson block sizes. -/
noncomputable def poissonCountKernel (n : ℕ) :
    Kernel (Fin n → SampleObs n) ((Fin n → SampleObs n) × (ℕ × ℕ)) :=
  Kernel.id.prod (Kernel.const (Fin n → SampleObs n) (poissonCountLaw n))

noncomputable instance poissonCountKernel_isMarkovKernel (n : ℕ) :
    IsMarkovKernel (poissonCountKernel n) := by
  unfold poissonCountKernel
  infer_instance

noncomputable def randomizedPoissonOutput (n : ℕ) (M rho : ℝ) :
    ((Fin n → SampleObs n) × (ℕ × ℕ)) → ℝ := fun w =>
  if w.2.1 + w.2.2 ≤ postPilotSize n then
    conditionalEstimator n M rho w.1 w.2.1 w.2.2
  else pilotTau n M w.1

lemma randomizedPoissonOutput_measurable (n : ℕ) (M rho : ℝ) :
    Measurable (randomizedPoissonOutput n M rho) := by
  apply measurable_from_prod_countable_left
  intro z
  change Measurable (fun x : Fin n → SampleObs n =>
    if z.1 + z.2 ≤ postPilotSize n then
      conditionalEstimator n M rho x z.1 z.2 else pilotTau n M x)
  split_ifs
  · exact conditionalEstimator_measurable n M rho z.1 z.2
  · exact pilotTau_measurable n M

lemma randomizedPoissonOutput_abs_le (n : ℕ) (M rho : ℝ) (hM : 0 ≤ M)
    (w : (Fin n → SampleObs n) × (ℕ × ℕ)) :
    |randomizedPoissonOutput n M rho w| ≤ M := by
  unfold randomizedPoissonOutput
  split_ifs
  · exact abs_le.mpr (conditionalEstimator_range n M rho hM w.1 w.2.1 w.2.2)
  · exact abs_le.mpr (pilotTau_range n M hM w.1)

/-- Kernel-mean representation of the actual finite estimator. -/
lemma knownRadiusEstimator_eq_kernelMean (n : ℕ) (M rho : ℝ) (hM : 0 ≤ M) :
    knownRadiusEstimator n M rho =
      Causalean.Stat.kernelMean (poissonCountKernel n)
        (randomizedPoissonOutput n M rho) := by
  funext sample
  rw [knownRadiusEstimator_eq_integral_poissonCounts n M rho hM sample]
  unfold Causalean.Stat.kernelMean poissonCountKernel poissonCountLaw
  rw [Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]
  have hstrong : StronglyMeasurable (Function.uncurry fun
      (x : Fin n → SampleObs n) (z : ℕ × ℕ) =>
        randomizedPoissonOutput n M rho (x, z)) := by
    change StronglyMeasurable (randomizedPoissonOutput n M rho)
    exact (randomizedPoissonOutput_measurable n M rho).stronglyMeasurable
  have hint : Integrable (randomizedPoissonOutput n M rho)
      ((Measure.dirac sample).prod
        ((poissonMeasure (Real.toNNReal (blockMean n))).prod
          (poissonMeasure (Real.toNNReal (blockMean n))))) := by
    apply Integrable.of_bound
      (randomizedPoissonOutput_measurable n M rho).aestronglyMeasurable M
    filter_upwards [] with w
    simpa [Real.norm_eq_abs] using randomizedPoissonOutput_abs_le n M rho hM w
  rw [integral_prod _ hint]
  rw [integral_dirac' _ _ hstrong.integral_prod_right]
  rfl

/-- Pointwise Rao--Blackwell/Jensen bridge from the implemented estimator to
the randomized capped Poisson-count output. -/
-- keep: estimator-level Jensen bridge used to audit de-Poissonization
lemma knownRadiusEstimator_sqLoss_le (n : ℕ) (M rho tau : ℝ) (hM : 0 ≤ M)
    (sample : Fin n → SampleObs n) :
    (knownRadiusEstimator n M rho sample - tau) ^ 2 ≤
      ∫ w, (randomizedPoissonOutput n M rho w - tau) ^ 2
        ∂poissonCountKernel n sample := by
  rw [knownRadiusEstimator_eq_kernelMean n M rho hM]
  apply Causalean.Stat.sqLoss_kernelMean_le
  · exact randomizedPoissonOutput_measurable n M rho
  · exact ⟨M, hM, randomizedPoissonOutput_abs_le n M rho hM⟩

/-- Adjoining the independent count pair to any finite measure gives its
ordinary product with the two-Poisson count law. -/
lemma poissonCountKernel_comp_eq_prod {n : ℕ}
    (Q : Measure (Fin n → SampleObs n)) [SFinite Q] :
    poissonCountKernel n ∘ₘ Q = Q.prod (poissonCountLaw n) := by
  unfold poissonCountKernel
  rw [← Measure.compProd_eq_comp_prod]
  exact Measure.compProd_const

/-- Integrated squared-risk Jensen inequality for the implemented estimator. -/
lemma knownRadiusEstimator_sqRisk_le_randomized {n : ℕ} (P : Law n)
    (M rho tau : ℝ) (hM : 0 ≤ M) :
    Causalean.Stat.sqRisk
        (DiscreteAteHeterogeneityFrontier.productLaw n P)
        (knownRadiusEstimator n M rho) tau ≤
      Causalean.Stat.sqRisk
        ((DiscreteAteHeterogeneityFrontier.productLaw n P).prod
          (poissonCountLaw n))
        (randomizedPoissonOutput n M rho) tau := by
  rw [knownRadiusEstimator_eq_kernelMean n M rho hM]
  have hj := Causalean.Stat.sqRisk_kernelMean_le_comp
    (DiscreteAteHeterogeneityFrontier.productLaw n P)
    (poissonCountKernel n)
    (randomizedPoissonOutput_measurable n M rho)
    ⟨M, hM, randomizedPoissonOutput_abs_le n M rho hM⟩ tau
  rwa [poissonCountKernel_comp_eq_prod] at hj

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
