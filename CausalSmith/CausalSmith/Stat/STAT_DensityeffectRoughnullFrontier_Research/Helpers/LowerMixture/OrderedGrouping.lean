module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.ActualPoissonMoments
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Depoissonization

/-!
Forget auxiliary marks in the actual Poisson partition experiment. The resulting
measurable grouping map acts on the original ordered observations and has the
independent, shared-sign localized null laws used in the second-moment calculation.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- A Poisson sample law is the sum of its genuine count fibers. -/
-- @node: lower_finitePoissonSampleLaw_eq_sum
lemma lower_finitePoissonSampleLaw_eq_sum {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (lam : NNReal) :
    finitePoissonSampleLaw P lam = Measure.sum (fun m => poissonMeasure lam {m} •
      (Measure.pi (fun _ : Fin m => P)).map (fixedSizeEmbed m)) := by
  have hcover : (⋃ m : ℕ, (FiniteSample.count : FiniteSample E → ℕ) ⁻¹' {m}) =
      Set.univ := by ext s; simp
  have hdis : Pairwise (Function.onFun Disjoint
      (fun m : ℕ => (FiniteSample.count : FiniteSample E → ℕ) ⁻¹' {m})) := by
    intro m n hmn
    exact (Set.disjoint_singleton.mpr hmn).preimage _
  rw [← Measure.restrict_univ (μ := finitePoissonSampleLaw P lam), ← hcover,
    Measure.restrict_iUnion hdis
      (fun m => (measurableSet_singleton m).preimage measurable_finiteSample_count)]
  simp_rw [finitePoissonSampleLaw_restrict_count_eq]

/-- Mapping every observation commutes with drawing an independent Poisson count. -/
-- @node: lower_finitePoissonSampleLaw_map
lemma lower_finitePoissonSampleLaw_map {E F : Type*} [MeasurableSpace E]
    [MeasurableSpace F] (P : Measure E) [IsProbabilityMeasure P]
    (f : E → F) (hf : Measurable f) (lam : NNReal) :
    (finitePoissonSampleLaw P lam).map (finiteSampleMap f) =
      @finitePoissonSampleLaw F _ (P.map f)
        (Measure.isProbabilityMeasure_map hf.aemeasurable) lam := by
  have : IsProbabilityMeasure (P.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  rw [lower_finitePoissonSampleLaw_eq_sum, lower_finitePoissonSampleLaw_eq_sum,
    Measure.map_sum (measurable_finiteSampleMap f hf).aemeasurable]
  congr 1
  funext m
  rw [Measure.map_smul, Measure.map_map (measurable_finiteSampleMap f hf)
    (measurable_fixedSizeEmbed m)]
  have hcomp : finiteSampleMap f ∘ fixedSizeEmbed m =
      fixedSizeEmbed m ∘ (fun o : Fin m → E => fun i => f (o i)) := rfl
  rw [hcomp, ← Measure.map_map (measurable_fixedSizeEmbed m) (by fun_prop),
    Measure.pi_map_pi (fun _ => hf.aemeasurable)]

/-- Independent marks can be forgotten without changing the ordered observation law. -/
-- @node: lower_markedPoisson_forget
lemma lower_markedPoisson_forget (P : Measure Omega) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : NNReal) :
    (finiteMarkedPoissonSampleLaw P R lam).map (finiteSampleMap Prod.fst) =
      finitePoissonSampleLaw P lam := by
  unfold finiteMarkedPoissonSampleLaw
  rw [lower_finitePoissonSampleLaw_map _ _ measurable_fst]
  simp only [Measure.map_fst_prod, measure_univ, one_smul]

/-- Adding deterministic marks gives the marked partition theorem a genuine ordered
observation input, without changing any statistical information. -/
-- @node: lower_poisson_attach_zero
lemma lower_poisson_attach_zero (P : Measure Omega) [IsProbabilityMeasure P]
    (lam : NNReal) :
    (finitePoissonSampleLaw P lam).map (finiteSampleMap (fun o => (o, (0 : ℝ)))) =
      finiteMarkedPoissonSampleLaw P (Measure.dirac 0) lam := by
  rw [lower_finitePoissonSampleLaw_map _ _ (by fun_prop)]
  simp only [← Measure.prod_dirac]
  rfl

/-- Group an ordered observation sample by the covariate classifier and retain
within-cell order; deterministic marks are discarded immediately. -/
-- @node: lowerOrderedGrouping
def lowerOrderedGrouping (k : ℕ) (hk : 0 < k) (s : FiniteSample Omega) :
    Fin k → FiniteSample Omega :=
  fun r => finiteSampleMap Prod.fst ((lowerRecordPartition k hk).restrictCell r
    (finiteSampleMap (fun o => (o, (0 : ℝ))) s))

/-- Grouping the original ordered observations is measurable. -/
-- @node: measurable_lowerOrderedGrouping
@[fun_prop] lemma measurable_lowerOrderedGrouping (k : ℕ) (hk : 0 < k) :
    Measurable (lowerOrderedGrouping k hk) := by
  apply measurable_pi_lambda
  intro r
  exact (measurable_finiteSampleMap Prod.fst measurable_fst).comp
    (((lowerRecordPartition k hk).measurable_restrictCell r).comp
      (measurable_finiteSampleMap (fun o : Omega => (o, (0 : ℝ))) (by fun_prop)))

/-- At a fixed propensity sign, grouping the ordered Poisson observations gives
independent actual localized Poisson samples. -/
-- @node: lower_ordered_grouping_fixed_sign
lemma lower_ordered_grouping_fixed_sign (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) (lam : NNReal) :
    (finitePoissonSampleLaw (lowerNullLaw theta k j hp lambda omega).law lam).map
      (lowerOrderedGrouping k hk) =
    Measure.pi (fun r => finitePoissonSampleLaw
      (lowerLocalizedNullLaw theta k j hp r (lambda r) omega) (lam / k)) := by
  unfold lowerOrderedGrouping
  rw [show (fun s : FiniteSample Omega => fun r : Fin k =>
      finiteSampleMap Prod.fst ((lowerRecordPartition k hk).restrictCell r
        (finiteSampleMap (fun o => (o, (0 : ℝ))) s))) =
      (fun q : Fin k → FiniteSample (Omega × ℝ) => fun r => finiteSampleMap Prod.fst (q r)) ∘
        (lowerRecordPartition k hk).restrictPartition ∘
          finiteSampleMap (fun o : Omega => (o, (0 : ℝ))) by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (lowerRecordPartition k hk).measurable_restrictPartition
      (measurable_finiteSampleMap (fun o : Omega => (o, (0 : ℝ))) (by fun_prop)),
    lower_poisson_attach_zero,
    lower_null_poisson_partition_fixed_sign theta k j hp hk lambda omega (Measure.dirac 0) lam,
    Measure.pi_map_pi (fun _ => (measurable_finiteSampleMap Prod.fst measurable_fst).aemeasurable)]
  simp_rw [lower_markedPoisson_forget]

/-- Mixing the shared propensity signs after grouping yields exactly the product
null law used by the actual grouped likelihood second moment. -/
-- @node: lower_ordered_grouping_sign_mixture
lemma lower_ordered_grouping_sign_mixture (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (omega : Fin j → Bool) (lam : NNReal) :
    (lowerUniformPoissonMixture (fun lambda : Fin k → Bool =>
      lowerNullLaw theta k j hp lambda omega) lam).map (lowerOrderedGrouping k hk) =
    Measure.pi (fun r => lowerLocalizedPoissonNull theta k j hp r omega (lam / k)) := by
  unfold lowerUniformPoissonMixture Causalean.Stat.Minimax.Mixture.uniformMixture
    Causalean.Stat.mixture
  rw [Measure.map_finset_sum' (measurable_lowerOrderedGrouping k hk).aemeasurable]
  simp_rw [Measure.map_smul, lower_ordered_grouping_fixed_sign theta k j hp hk]
  exact lower_uniform_sign_product_measure k (fun r b =>
    finitePoissonSampleLaw (lowerLocalizedNullLaw theta k j hp r b omega) (lam / k))

/-- The histogram and likelihood classifiers assign every covariate to the same cell,
including endpoints and off-support values. -/
-- @node: lowerRecordCell_eq_lowerCellIndex
lemma lowerRecordCell_eq_lowerCellIndex (k : ℕ) (hk : 0 < k) (o : Omega) :
    lowerRecordCell k hk o = lowerCellIndex k hk (X o) := by
  apply Fin.ext
  simp only [lowerRecordCell, lowerCellIndex, cell]
  omega

/-- Cell likelihoods are invariant under enumerating the same records in another order. -/
-- @node: cellAlternativeRatio_reindex
lemma cellAlternativeRatio_reindex {m n : ℕ} (e : Fin m ≃ Fin n)
    (tau gamma : ℝ) (u : Fin n → ℝ) (a : Fin n → Bool) (v : Fin n → ℝ) :
    cellAlternativeRatio tau gamma (u ∘ e) (a ∘ e) (v ∘ e) =
      cellAlternativeRatio tau gamma u a v := by
  rw [cellAlternativeRatio_eq_weighted_product, cellAlternativeRatio_eq_weighted_product]
  simp only [cellSignLikelihood, Finset.prod_filter, Function.comp_apply]
  rw [e.prod_comp (fun i => 1 + tau * signValue true * u i * signValue (a i)),
    e.prod_comp (fun i => 1 + tau * signValue false * u i * signValue (a i)),
    e.prod_comp (fun i => if a i = true then
      1 + gamma * (u i / (1 + tau * u i)) * v i else 1),
    e.prod_comp (fun i => if a i = true then
      1 + gamma * (-u i / (1 - tau * u i)) * v i else 1)]

/-- Stable filtering and the likelihood's arbitrary fiber enumeration give the same
product of record functions. No distinctness of the observed records is required. -/
-- @node: lowerOrderedGrouping_prod
lemma lowerOrderedGrouping_prod (k n : ℕ) (hk : 0 < k) (o : Data n)
    (r : Fin k) (f : Omega → ℝ) :
    (∏ i, f ((lowerOrderedGrouping k hk (fixedSizeEmbed n o) r).points i)) =
      ∏ i : {i : Fin n // lowerCellIndex k hk (X (o i)) = r}, f (o i.val) := by
  classical
  let t : Finset (Fin n) := Finset.univ.filter
    (fun i => lowerCellIndex k hk (X (o i)) = r)
  let t0 : Finset (Fin n) := @Finset.filter _ (fun i => lowerRecordCell k hk (o i) = r)
    (fun _ => Classical.propDecidable _) Finset.univ
  dsimp +instances only [lowerOrderedGrouping, finiteSampleMap, fixedSizeEmbed,
    FiniteMeasurablePartition.restrictCell, FiniteMeasurablePartition.cellIndices,
    FiniteSample.points, FiniteSample.count, lowerRecordPartition]
  change (∏ i : Fin t0.card, f (o (t0.orderIsoOfFin rfl i).val)) = _
  have ht : t0 = t := by ext i; simp [t0, t, lowerRecordCell_eq_lowerCellIndex]
  rw [ht]
  change (∏ i : Fin t.card, f (o (t.orderIsoOfFin rfl i).val)) = _
  calc
    _ = ∏ i : t, f (o i.val) :=
      (t.orderIsoOfFin rfl).toEquiv.prod_comp (fun i : t => f (o i.val))
    _ = ∏ i ∈ t, f (o i) := Finset.prod_coe_sort t (fun i => f (o i))
    _ = _ := Finset.prod_subtype t (by simp [t]) (fun i => f (o i))

/-- The stable-filter cell likelihood equals the likelihood on the earlier allocated
fiber. This identifies the two enumerations before taking any moments. -/
-- @node: lower_ordered_grouping_cell_ratio
lemma lower_ordered_grouping_cell_ratio (theta : ℝ) (k j n : ℕ) (hk : 0 < k)
    (omega : Fin j → Bool) (o : Data n) (r : Fin k) :
    let q := lowerOrderedGrouping k hk (fixedSizeEmbed n o) r
    let allocation := fun i => lowerCellIndex k hk (X (o i))
    let records := lowerAllocatedSample allocation o r
    lowerActualCellRatio theta k j q.count r omega q.points =
      cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j)
        (fun i => lowerBump ((k : ℝ) * X (records i) - r.val)) (fun i => A (records i))
        (fun i => signedBumps j omega (Y (records i)) / baselineDensity (Y (records i))) := by
  dsimp only
  unfold lowerActualCellRatio
  rw [cellAlternativeRatio_eq_weighted_product, cellAlternativeRatio_eq_weighted_product]
  dsimp +instances only [lowerLocalizedCellData, lowerOutcomeScore]
  simp +instances only [cellSignLikelihood, Finset.prod_filter]
  have hprod (f : Omega → ℝ) :
      (∏ i, f ((lowerOrderedGrouping k hk (fixedSizeEmbed n o) r).points i)) =
      ∏ i, f (lowerAllocatedSample (fun i => lowerCellIndex k hk (X (o i))) o r i) := by
    rw [lowerOrderedGrouping_prod, lowerAllocatedSample_prod]
  rw [hprod (fun o => 1 + lowerTau theta k * signValue true *
      lowerBump ((k : ℝ) * X o - r.val) * signValue (A o)),
    hprod (fun o => 1 + lowerTau theta k * signValue false *
      lowerBump ((k : ℝ) * X o - r.val) * signValue (A o)),
    hprod (fun o => if A o = true then 1 + lowerGamma theta j *
      (lowerBump ((k : ℝ) * X o - r.val) /
        (1 + lowerTau theta k * lowerBump ((k : ℝ) * X o - r.val))) *
          (signedBumps j omega (Y o) / baselineDensity (Y o)) else 1),
    hprod (fun o => if A o = true then 1 + lowerGamma theta j *
      (-lowerBump ((k : ℝ) * X o - r.val) /
        (1 - lowerTau theta k * lowerBump ((k : ℝ) * X o - r.val))) *
          (signedBumps j omega (Y o) / baselineDensity (Y o)) else 1)]

/-- The product likelihood in the ordered sample is exactly the grouped likelihood,
pointwise, including boundary records and empty cells. -/
-- @node: lower_ordered_grouping_likelihood
lemma lower_ordered_grouping_likelihood (theta : ℝ) (k j : ℕ) (hk : 0 < k)
    (omega : Fin j → Bool) (s : FiniteSample Omega) :
    lowerSampleCellRatio theta k j s.count hk omega s.points =
      lowerActualPoissonCellProduct theta k j omega (lowerOrderedGrouping k hk s) := by
  cases s with
  | mk n o =>
    unfold lowerSampleCellRatio lowerActualPoissonCellProduct
    apply Finset.prod_congr rfl
    intro r _
    exact (lower_ordered_grouping_cell_ratio theta k j n hk omega o r).symm

/-- The common outcome-sign vector stays outside the cell product when the ordered
likelihood is written as a function of grouped observations. -/
-- @node: lower_ordered_grouping_outcome_average
lemma lower_ordered_grouping_outcome_average (theta : ℝ) (k j : ℕ) (hk : 0 < k)
    (s : FiniteSample Omega) :
    lowerOutcomeAveragedSampleRatio theta k j s.count hk s.points =
      lowerActualPoissonOutcomeAverage theta k j (lowerOrderedGrouping k hk s) := by
  unfold lowerOutcomeAveragedSampleRatio lowerActualPoissonOutcomeAverage
  simp_rw [lower_ordered_grouping_likelihood]

/-- An unused finite prior coordinate does not change a uniform mixture. -/
-- @node: lower_uniformMixture_unused_coordinate
lemma lower_uniformMixture_unused_coordinate {S T E : Type*}
    [Fintype S] [Nonempty S] [Fintype T] [Nonempty T] [MeasurableSpace E]
    (mu : S → Measure E) :
    Causalean.Stat.Minimax.Mixture.uniformMixture (fun s : S × T => mu s.1) =
      Causalean.Stat.Minimax.Mixture.uniformMixture mu := by
  classical
  unfold Causalean.Stat.Minimax.Mixture.uniformMixture Causalean.Stat.mixture
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← smul_smul]
  have ht : (Fintype.card T : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card T ≠ 0)
  apply Finset.sum_congr rfl
  intro x _
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (by simp) (by simp)]
  rw [mul_left_comm, ENNReal.mul_inv_cancel ht (by simp), mul_one]

/-- The redundant outcome prior can be removed from the actual null Poisson law. -/
-- @node: lower_full_poisson_null_unused_outcome
lemma lower_full_poisson_null_unused_outcome (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (base : Fin j → Bool) (lam : NNReal) :
    lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
      lowerNullLaw theta k j hp s.1 s.2) lam =
    lowerUniformPoissonMixture (fun lambda : Fin k → Bool =>
      lowerNullLaw theta k j hp lambda base) lam := by
  exact lower_uniformMixture_unused_coordinate (fun lambda =>
    finitePoissonSampleLaw (lowerNullLaw theta k j hp lambda base).law lam)

/-- The complete null prior on ordered observations maps to the actual independent
cell null laws, with no dependence on the unused outcome signs. -/
-- @node: lower_full_poisson_grouping
lemma lower_full_poisson_grouping (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (base : Fin j → Bool) (lam : NNReal) :
    (lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
      lowerNullLaw theta k j hp s.1 s.2) lam).map (lowerOrderedGrouping k hk) =
    Measure.pi (fun r => lowerLocalizedPoissonNull theta k j hp r base (lam / k)) := by
  rw [lower_full_poisson_null_unused_outcome theta k j hp base lam]
  exact lower_ordered_grouping_sign_mixture theta k j hp hk base lam

/-- The grouped outcome-sign likelihood is measurable on the independent cell space. -/
-- @node: measurable_lowerActualPoissonOutcomeAverage
@[fun_prop] lemma measurable_lowerActualPoissonOutcomeAverage (theta : ℝ) (k j : ℕ) :
    Measurable (lowerActualPoissonOutcomeAverage theta k j) := by
  have hm (r : Fin k) (omega : Fin j → Bool) :
      Measurable (fun s : FiniteSample Omega =>
        lowerActualCellRatio theta k j s.count r omega s.points) := by
    intro A hA
    rw [MeasurableSpace.measurableSet_iInf]
    intro m
    exact measurable_lowerActualCellRatio theta k j m r omega hA
  unfold lowerActualPoissonOutcomeAverage lowerActualPoissonCellProduct
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro omega _
  apply Finset.measurable_prod
  intro r _
  exact (hm r omega).comp (measurable_pi_apply r)

/-- Square integrability of the ordered likelihood follows by grouping from the
proved exponential cell envelopes. -/
-- @node: lower_full_poisson_likelihood_sq_integrable
lemma lower_full_poisson_likelihood_sq_integrable (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (lam : NNReal) :
    Integrable (fun s => (lowerOutcomeAveragedSampleRatio theta k j s.count hk s.points) ^ 2)
      (lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerNullLaw theta k j hp s.1 s.2) lam) := by
  simp_rw [lower_ordered_grouping_outcome_average]
  apply (integrable_map_measure
    ((measurable_lowerActualPoissonOutcomeAverage theta k j).pow_const 2).aestronglyMeasurable
    (measurable_lowerOrderedGrouping k hk).aemeasurable).mp
  rw [lower_full_poisson_grouping theta k j hp hk (fun _ => false) lam]
  exact lowerActualPoissonOutcomeAverage_sq_integrable theta k j hp (fun _ => false) (lam / k)

/-- Equation (40) for the original ordered Poisson observation mixtures. Stable
filtering preserves the likelihood pointwise, so restoring order needs no extra kernel. -/
-- @node: lower_full_poisson_likelihood_second_moment
lemma lower_full_poisson_likelihood_second_moment (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (lam : NNReal) :
    (∫ s, (lowerOutcomeAveragedSampleRatio theta k j s.count hk s.points) ^ 2
      ∂lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerNullLaw theta k j hp s.1 s.2) lam) =
    signPairExpectation j (fun omega op =>
      lowerPoissonOverlap (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) (lam / k)
        (lowerGamma theta j) (weightedSignOverlap j (lowerOutcomeWeight j) omega op) ^ k) := by
  simp_rw [lower_ordered_grouping_outcome_average]
  rw [← integral_map (measurable_lowerOrderedGrouping k hk).aemeasurable
    ((measurable_lowerActualPoissonOutcomeAverage theta k j).pow_const 2).aestronglyMeasurable,
    lower_full_poisson_grouping theta k j hp hk (fun _ => false) lam]
  exact lowerActualPoissonOutcomeAverage_second_moment theta k j hp hk (fun _ => false) (lam / k)

/-- The actual Poisson alternative is absolutely continuous with respect to its
actual null mixture, by the already identified likelihood density. -/
-- @node: lower_full_poisson_absolutelyContinuous
lemma lower_full_poisson_absolutelyContinuous (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (lam : NNReal) :
    lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
      lowerAlternativeLaw theta k j hp s.1 s.2) lam ≪
    lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
      lowerNullLaw theta k j hp s.1 s.2) lam := by
  rw [lower_full_poisson_withDensity_cell_average theta k j hp hk lam]
  exact withDensity_absolutelyContinuous _ _

/-- The squared Radon--Nikodym deviation is integrable, derived from the genuine
likelihood's first and second moments. -/
-- @node: lower_full_poisson_rnDeriv_deviation_integrable
lemma lower_full_poisson_rnDeriv_deviation_integrable (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (lam : NNReal) :
    Integrable (fun s =>
      (((lowerUniformPoissonMixture (fun t : (Fin k → Bool) × (Fin j → Bool) =>
        lowerAlternativeLaw theta k j hp t.1 t.2) lam).rnDeriv
        (lowerUniformPoissonMixture (fun t : (Fin k → Bool) × (Fin j → Bool) =>
          lowerNullLaw theta k j hp t.1 t.2) lam) s).toReal - 1) ^ 2)
      (lowerUniformPoissonMixture (fun t : (Fin k → Bool) × (Fin j → Bool) =>
        lowerNullLaw theta k j hp t.1 t.2) lam) := by
  have hi := ((lower_full_poisson_likelihood_sq_integrable theta k j hp hk lam).sub
    ((lower_full_poisson_likelihood_integrable theta k j hp hk lam).const_mul 2)).add
      (integrable_const 1)
  apply hi.congr
  filter_upwards [lower_full_poisson_rnDeriv_cell_average theta k j hp hk lam] with s hs
  rw [hs, ENNReal.toReal_ofReal (lowerOutcomeAveragedSampleRatio_nonneg theta k j _ hp hk _)]
  dsimp only [Pi.sub_apply, Pi.add_apply]
  ring

/-- The actual ordered Poisson chi-square divergence is the sign-pair average in
(40), minus one. This connects the rate budget to the original experiment. -/
-- @node: lower_full_poisson_chiSqDiv
lemma lower_full_poisson_chiSqDiv (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (lam : NNReal) :
    Causalean.Stat.chiSqDiv
      (lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerAlternativeLaw theta k j hp s.1 s.2) lam)
      (lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerNullLaw theta k j hp s.1 s.2) lam) =
    signPairExpectation j (fun omega op =>
      lowerPoissonOverlap (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) (lam / k)
        (lowerGamma theta j) (weightedSignOverlap j (lowerOutcomeWeight j) omega op) ^ k) - 1 := by
  rw [Causalean.Stat.chiSqDiv_eq
    (lower_full_poisson_absolutelyContinuous theta k j hp hk lam)
    (lower_full_poisson_rnDeriv_deviation_integrable theta k j hp hk lam)]
  rw [← lower_full_poisson_likelihood_second_moment theta k j hp hk lam]
  congr 1
  apply integral_congr_ae
  filter_upwards [lower_full_poisson_rnDeriv_cell_average theta k j hp hk lam] with s hs
  rw [hs, ENNReal.toReal_ofReal (lowerOutcomeAveragedSampleRatio_nonneg theta k j _ hp hk _)]

/-- Scheffé and Cauchy--Schwarz give (45) for the actual ordered mixtures. The
second-moment representation and its integrability are both proved above. -/
-- @node: lower_full_poisson_tv_le
lemma lower_full_poisson_tv_le (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (lam : NNReal) :
    Causalean.Stat.tvDist
      (lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerNullLaw theta k j hp s.1 s.2) lam)
      (lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerAlternativeLaw theta k j hp s.1 s.2) lam) ≤
    (1 / 2) * Real.sqrt (signPairExpectation j (fun omega op =>
      lowerPoissonOverlap (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) (lam / k)
        (lowerGamma theta j) (weightedSignOverlap j (lowerOutcomeWeight j) omega op) ^ k) - 1) := by
  rw [Causalean.Stat.tvDist_symm]
  have h := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv _ _
    (lower_full_poisson_absolutelyContinuous theta k j hp hk lam)
    (lower_full_poisson_rnDeriv_deviation_integrable theta k j hp hk lam)
  rwa [lower_full_poisson_chiSqDiv theta k j hp hk lam] at h

/-- Equation (43) now bounds the divergence of the actual ordered experiments,
using the derived moment identity and the proved singleton and outcome-weight bounds. -/
-- @node: lower_full_poisson_chiSqDiv_le
lemma lower_full_poisson_chiSqDiv_le (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (hj : 0 < j)
    (lam : NNReal) (hx : ((lam / k : NNReal) : ℝ) ≤ 1)
    (hr : ((lam / k : NNReal) : ℝ) * lowerGamma theta j ^ 2 ≤ 1)
    (hd : 2 * ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
      (16 * (k : ℝ) * ((lam / k : NNReal) : ℝ) ^ 2 * lowerGamma theta j ^ 4) ≤ 1 / 2)
    (ha : ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
      ((k : ℝ) * (Real.exp ((5 / 3 : ℝ) ^ 2 - 1) *
        ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4)) *
        ((lam / k : NNReal) : ℝ) ^ 2 * lowerTau theta k ^ 2 * lowerGamma theta j ^ 2) ^ 2 ≤ 1 / 2) :
    Causalean.Stat.chiSqDiv
      (lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerAlternativeLaw theta k j hp s.1 s.2) lam)
      (lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerNullLaw theta k j hp s.1 s.2) lam) ≤
      8 * (((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
        ((k : ℝ) * (Real.exp ((5 / 3 : ℝ) ^ 2 - 1) *
          ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4)) *
          ((lam / k : NNReal) : ℝ) ^ 2 * lowerTau theta k ^ 2 * lowerGamma theta j ^ 2) ^ 2 +
        ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
          (16 * (k : ℝ) * ((lam / k : NNReal) : ℝ) ^ 2 * lowerGamma theta j ^ 4)) := by
  rw [lower_full_poisson_chiSqDiv theta k j hp hk lam]
  exact lowerPoissonOverlap_actual_weights_excess_le (lowerTau theta k)
    (lowerTau_mem_Ioc theta k j hp hk) (lam / k) hx (lowerGamma theta j) k j hj hr hd ha

end CausalSmith.Stat.DensityEffectRoughNull
