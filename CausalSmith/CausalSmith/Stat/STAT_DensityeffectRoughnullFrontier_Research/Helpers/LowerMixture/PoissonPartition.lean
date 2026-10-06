module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.LocalizedDesign
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CorrectedMean
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Partition.CellLaws

/-!
The actual observed null law split into independent Poisson covariate cells.
The histogram classifier assigns boundaries to a unique cell; its restrictions
agree almost everywhere with the closed cells used for affine localization.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Zero-based measurable cell label for every record, including off-support records. -/
-- @node: lowerRecordCell
def lowerRecordCell (k : ℕ) (hk : 0 < k) (o : Omega) : Fin k :=
  ⟨cell k (X o) - 1, by have h := cell_index_mem k hk (X o); omega⟩

/-- The finite label is a measurable function of the observed covariate. -/
-- @node: measurable_lowerRecordCell
@[fun_prop] lemma measurable_lowerRecordCell (k : ℕ) (hk : 0 < k) :
    Measurable (lowerRecordCell k hk) := by
  apply measurable_to_countable'
  intro r
  have hm : Measurable (fun o : Omega => cell k (X o) - 1) := by
    unfold X
    fun_prop
  convert hm (measurableSet_singleton r.val) using 1
  ext o
  simp [lowerRecordCell, Fin.ext_iff]

/-- The unique-cell partition used in the ordered Poisson experiment. -/
-- @node: lowerRecordPartition
def lowerRecordPartition (k : ℕ) (hk : 0 < k) : FiniteMeasurablePartition Omega (Fin k) :=
  ⟨lowerRecordCell k hk, measurable_lowerRecordCell k hk⟩

/-- On the observation support, classifier fibers are exactly the histogram cells. -/
-- @node: lowerRecordPartition_cellSet_ae
lemma lowerRecordPartition_cellSet_ae (P : ObsLaw) (k : ℕ) (hk : 0 < k) (r : Fin k) :
    (lowerRecordPartition k hk).cellSet r =ᵐ[P.law]
      {o | X o ∈ histogramCell k (r.val + 1)} := by
  filter_upwards [P.support] with o ho
  have h := cell_index_mem k hk (X o)
  apply propext
  change lowerRecordCell k hk o = r ↔
    X o ∈ Set.Icc 0 1 ∧ cell k (X o) = r.val + 1
  rw [Fin.ext_iff]
  simp only [lowerRecordCell, ho.1, true_and]
  omega

/-- The actual classifier cell has mass 1/k under the known uniform design. -/
-- @node: lowerRecordPartition_mass
lemma lowerRecordPartition_mass (P : ObsLaw) (hP : UniformDesign P)
    (k : ℕ) (hk : 0 < k) (r : Fin k) :
    P.law ((lowerRecordPartition k hk).cellSet r) = (ENNReal.ofReal (k : ℝ))⁻¹ := by
  rw [measure_congr (lowerRecordPartition_cellSet_ae P k hk r)]
  have hmap : P.law {o | X o ∈ histogramCell k (r.val + 1)} =
      unitVolume (histogramCell k (r.val + 1)) := by
    rw [← hP]
    exact (Measure.map_apply (by unfold X; fun_prop)
      (measurableSet_histogramCell k (r.val + 1))).symm
  rw [hmap]
  have hm := histogramCell_mass_eq k hk r
  rw [measureReal_def] at hm
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), hm, one_div,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hk)]

/-- The unique histogram cell and the closed localization cell agree under each
actual null law; shared endpoints therefore do not change conditional laws. -/
-- @node: lower_null_partition_restrict_eq_closed
lemma lower_null_partition_restrict_eq_closed (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    (lowerNullLaw theta k j hp lambda omega).law.restrict
        ((lowerRecordPartition k hk).cellSet r) =
      (lowerNullLaw theta k j hp lambda omega).law.restrict
        {o | X o ∈ lowerClosedCell k r} := by
  let P := lowerNullLaw theta k j hp lambda omega
  have hP := (lower_null_model theta k j hp lambda omega).1.design
  rw [Measure.restrict_congr_set (lowerRecordPartition_cellSet_ae P k hk r)]
  apply Measure.restrict_congr_set
  apply ae_eq_of_subset_of_measure_ge
  · intro o ho
    exact histogramCell_subset_bin k hk r ho
  · have hmass := lowerRecordPartition_mass P hP k hk r
    rw [measure_congr (lowerRecordPartition_cellSet_ae P k hk r)] at hmass
    rw [hmass, lower_null_closed_cell_mass theta k j hp hk r lambda omega]
  · exact ((measurableSet_histogramCell k (r.val + 1)).preimage
      (by unfold X; fun_prop)).nullMeasurableSet
  · exact measure_ne_top _ _

/-- Nonnegative cell mass used by the reusable Poisson partition theorem. -/
-- @node: lower_null_partition_cellMass
lemma lower_null_partition_cellMass (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    (lowerRecordPartition k hk).cellMass
      (lowerNullLaw theta k j hp lambda omega).law r = (k : NNReal)⁻¹ := by
  unfold FiniteMeasurablePartition.cellMass
  rw [lowerRecordPartition_mass _ (lower_null_model theta k j hp lambda omega).1.design]
  simp

/-- The normalized classifier-cell observation law is the actual affine-localized
law at the cell's single latent sign. -/
-- @node: lower_null_partition_cellObservationLaw
lemma lower_null_partition_cellObservationLaw (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    (lowerRecordPartition k hk).cellObservationLaw
        (lowerNullLaw theta k j hp lambda omega).law r =
      lowerLocalizedNullLaw theta k j hp r (lambda r) omega := by
  have hmass := lowerRecordPartition_mass
    (lowerNullLaw theta k j hp lambda omega)
    (lower_null_model theta k j hp lambda omega).1.design k hk r
  rw [FiniteMeasurablePartition.cellObservationLaw, dif_neg (by
    rw [hmass]
    exact ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top), hmass, inv_inv,
    lower_null_partition_restrict_eq_closed theta k j hp hk r lambda omega,
    lower_null_law_restrict_depends_on_cell theta k j hp hk r lambda omega]
  rfl

/-- Conditional on the complete propensity sign vector, the actual ordered
Poisson sample splits into independent localized samples, all with mean lam/k.
The auxiliary real marks may be taken to be deterministic zero. -/
-- @node: lower_null_poisson_partition_fixed_sign
lemma lower_null_poisson_partition_fixed_sign (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k)
    (lambda : Fin k → Bool) (omega : Fin j → Bool)
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : NNReal) :
    (finiteMarkedPoissonSampleLaw (lowerNullLaw theta k j hp lambda omega).law R lam).map
        (lowerRecordPartition k hk).restrictPartition =
      Measure.pi (fun r : Fin k => finiteMarkedPoissonSampleLaw
        (lowerLocalizedNullLaw theta k j hp r (lambda r) omega) R (lam / k)) := by
  rw [FiniteMeasurablePartition.map_restrictPartition_finiteMarkedPoissonSampleLaw]
  simp_rw [lower_null_partition_cellObservationLaw theta k j hp hk,
    lower_null_partition_cellMass theta k j hp hk, ← div_eq_mul_inv]

/-- The vector of actual covariate-cell counts consists of independent Poisson
counts. This is the count/allocation identity preceding (29), as a measure equality. -/
-- @node: lower_null_poisson_partition_counts
lemma lower_null_poisson_partition_counts (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k)
    (lambda : Fin k → Bool) (omega : Fin j → Bool)
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : NNReal) :
    (finiteMarkedPoissonSampleLaw (lowerNullLaw theta k j hp lambda omega).law R lam).map
        (fun s => fun r : Fin k => ((lowerRecordPartition k hk).restrictCell r s).count) =
      Measure.pi (fun _ : Fin k => poissonMeasure (lam / k)) := by
  rw [show (fun s => fun r : Fin k =>
      ((lowerRecordPartition k hk).restrictCell r s).count) =
      (fun q : Fin k → FiniteSample (Omega × ℝ) => fun r => (q r).count) ∘
        (lowerRecordPartition k hk).restrictPartition by rfl,
    ← Measure.map_map (by fun_prop)
      (lowerRecordPartition k hk).measurable_restrictPartition,
    lower_null_poisson_partition_fixed_sign theta k j hp hk lambda omega R lam,
    Measure.pi_map_pi (fun _ => measurable_finiteSample_count.aemeasurable)]
  simp_rw [finiteMarkedPoissonSampleLaw_map_count]

/-- Independent fair cell signs commute with the finite product of their laws.
Each sign is mixed after constructing the entire within-cell sample law. -/
-- @node: lower_uniform_sign_product_measure
lemma lower_uniform_sign_product_measure {E : Type*} [MeasurableSpace E]
    (k : ℕ) (nu : Fin k → Bool → Measure E)
    [∀ r b, IsProbabilityMeasure (nu r b)] :
    Causalean.Stat.Minimax.Mixture.uniformMixture
        (fun lambda : Fin k → Bool => Measure.pi (fun r => nu r (lambda r))) =
      Measure.pi (fun r => Causalean.Stat.Minimax.Mixture.uniformMixture (nu r)) := by
  classical
  have (r : Fin k) : IsProbabilityMeasure
      (Causalean.Stat.Minimax.Mixture.uniformMixture (nu r)) :=
    Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability _
  symm
  apply Measure.pi_eq
  intro s hs
  simp only [Causalean.Stat.Minimax.Mixture.uniformMixture, Causalean.Stat.mixture,
    Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.pi_pi]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [show ((2 : ℝ≥0∞) ^ k)⁻¹ = ∏ _ : Fin k, (2 : ℝ≥0∞)⁻¹ by simp [ENNReal.inv_pow]]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun r b => (2 : ℝ≥0∞)⁻¹ * nu r b (s r))).symm

/-- Under the actual null sign prior, the cell restrictions are independent
Poisson samples with one fair latent sign shared by all records in each cell. -/
-- @node: lower_null_poisson_partition_sign_mixture
lemma lower_null_poisson_partition_sign_mixture (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (omega : Fin j → Bool)
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : NNReal) :
    (Causalean.Stat.Minimax.Mixture.uniformMixture (fun lambda : Fin k → Bool =>
      finiteMarkedPoissonSampleLaw (lowerNullLaw theta k j hp lambda omega).law R lam)).map
        (lowerRecordPartition k hk).restrictPartition =
      Measure.pi (fun r : Fin k => Causalean.Stat.Minimax.Mixture.uniformMixture
        (fun b : Bool => finiteMarkedPoissonSampleLaw
          (lowerLocalizedNullLaw theta k j hp r b omega) R (lam / k))) := by
  unfold Causalean.Stat.Minimax.Mixture.uniformMixture Causalean.Stat.mixture
  rw [Measure.map_finset_sum' (lowerRecordPartition k hk).measurable_restrictPartition.aemeasurable]
  simp_rw [Measure.map_smul,
    lower_null_poisson_partition_fixed_sign theta k j hp hk _ omega R lam]
  exact lower_uniform_sign_product_measure k
    (fun r b => finiteMarkedPoissonSampleLaw
      (lowerLocalizedNullLaw theta k j hp r b omega) R (lam / k))

/-- Report the count, localized bump scores and treatment flags of a cell sample. -/
-- @node: lowerPoissonCellReport
def lowerPoissonCellReport (k : ℕ) (r : Fin k)
    (s : FiniteSample (Omega × ℝ)) :
    Σ m : ℕ, Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m :=
  ⟨s.count, lowerLocalizedCellData k s.count r (fun i => (s.points i).1)⟩

/-- Reporting the variable-count cell design is measurable on each count fiber. -/
-- @node: measurable_lowerPoissonCellReport
@[fun_prop] lemma measurable_lowerPoissonCellReport (k : ℕ) (r : Fin k) :
    Measurable (lowerPoissonCellReport k r) := by
  intro B hB
  rw [MeasurableSpace.measurableSet_iInf] at hB ⊢
  intro m
  have hBm := hB m
  change MeasurableSet ((Sigma.mk m) ⁻¹' B) at hBm
  change MeasurableSet ((fun o : Fin m → Omega × ℝ =>
    lowerLocalizedCellData k m r (fun i => (o i).1)) ⁻¹' ((Sigma.mk m) ⁻¹' B))
  exact hBm.preimage ((measurable_lowerLocalizedCellData k m r).comp
    (show Measurable (fun o : Fin m → Omega × ℝ => fun i => (o i).1) by fun_prop))

/-- After forgetting auxiliary marks, the fixed-count actual cell law reports
exactly its localized design. -/
-- @node: lower_localized_marked_fixed_count_design
lemma lower_localized_marked_fixed_count_design (theta : ℝ) (k j m : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (b : Bool) (omega : Fin j → Bool) (R : Measure ℝ) [IsProbabilityMeasure R] :
    (Measure.pi (fun _ : Fin m => (lowerLocalizedNullLaw theta k j hp r b omega).prod R)).map
        (fun o => lowerLocalizedCellData k m r (fun i => (o i).1)) =
      (dataLaw (lowerUnitNullFamily (lowerTau theta k)
        (lowerTau_mem_Ioc theta k j hp hk) b) m).map (lowerUnitCellData m) := by
  rw [show (fun o => lowerLocalizedCellData k m r (fun i => (o i).1)) =
      lowerLocalizedCellData k m r ∘ (fun o : Fin m → Omega × ℝ => fun i => (o i).1) by rfl,
    ← Measure.map_map (measurable_lowerLocalizedCellData k m r) (by fun_prop),
    Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
  simp only [Measure.map_fst_prod, measure_univ, one_smul]
  exact lower_localized_null_design_fixed_sign theta k j m hp hk r b omega

/-- Exact unnormalized count-fiber law of the reported actual cell design.
The single propensity sign remains shared throughout the fixed-size sample. -/
-- @node: lower_localized_poisson_report_fixed_sign_fiber
lemma lower_localized_poisson_report_fixed_sign_fiber (theta : ℝ) (k j m : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (b : Bool) (omega : Fin j → Bool) (R : Measure ℝ) [IsProbabilityMeasure R]
    (xi : NNReal) :
    ((finiteMarkedPoissonSampleLaw (lowerLocalizedNullLaw theta k j hp r b omega) R xi).restrict
      (FiniteSample.count ⁻¹' {m})).map (lowerPoissonCellReport k r) =
      poissonMeasure xi {m} •
        ((dataLaw (lowerUnitNullFamily (lowerTau theta k)
          (lowerTau_mem_Ioc theta k j hp hk) b) m).map (lowerUnitCellData m)).map
          (Sigma.mk m) := by
  have hmk : Measurable (Sigma.mk m :
      Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m →
        Σ n : ℕ, Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell n) := by
    apply Measurable.of_le_map
    exact iInf_le _ m
  rw [finiteMarkedPoissonSampleLaw_restrict_count_eq, Measure.map_smul,
    Measure.map_map (measurable_lowerPoissonCellReport k r) (measurable_fixedSizeEmbed m)]
  change poissonMeasure xi {m} •
      (Measure.pi (fun _ : Fin m => (lowerLocalizedNullLaw theta k j hp r b omega).prod R)).map
        ((Sigma.mk m) ∘ (fun o => lowerLocalizedCellData k m r (fun i => (o i).1))) = _
  rw [← Measure.map_map hmk (by fun_prop),
    lower_localized_marked_fixed_count_design theta k j m hp hk r b omega R]

/-- Averaging the one shared cell sign gives the canonical unit-cell design on
every count fiber, with precisely the Poisson count mass as its coefficient. -/
-- @node: lower_localized_poisson_report_sign_mixture_fiber
lemma lower_localized_poisson_report_sign_mixture_fiber (theta : ℝ) (k j m : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (omega : Fin j → Bool) (R : Measure ℝ) [IsProbabilityMeasure R] (xi : NNReal) :
    ((Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
      finiteMarkedPoissonSampleLaw (lowerLocalizedNullLaw theta k j hp r b omega) R xi)).restrict
        (FiniteSample.count ⁻¹' {m})).map (lowerPoissonCellReport k r) =
      poissonMeasure xi {m} •
        (lowerUnitCellDesign (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) m).map
          (Sigma.mk m) := by
  have hmk : Measurable (Sigma.mk m :
      Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m →
        Σ n : ℕ, Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell n) := by
    apply Measurable.of_le_map
    exact iInf_le _ m
  unfold Causalean.Stat.Minimax.Mixture.uniformMixture Causalean.Stat.mixture
  rw [Fintype.sum_bool, Measure.restrict_add]
  simp only [Measure.restrict_smul]
  rw [Measure.map_add _ _ (measurable_lowerPoissonCellReport k r)]
  simp only [Measure.map_smul,
    lower_localized_poisson_report_fixed_sign_fiber theta k j m hp hk r _ omega R xi]
  unfold lowerUnitCellDesign uniformSampleMixture
    Causalean.Stat.Minimax.Mixture.uniformMixture Causalean.Stat.mixture
  rw [Fintype.sum_bool, Measure.map_add _ _ (measurable_lowerUnitCellData m)]
  simp only [Measure.map_smul]
  rw [Measure.map_add _ _ hmk]
  simp only [Measure.map_smul, smul_add]
  congr 1 <;> rw [smul_comm]

/-- The complete actual localized Poisson design is the count mixture of the
canonical shared-sign designs. This includes the empty-cell law. -/
-- @node: lower_localized_poisson_report_sign_mixture
lemma lower_localized_poisson_report_sign_mixture (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (omega : Fin j → Bool) (R : Measure ℝ) [IsProbabilityMeasure R] (xi : NNReal) :
    (Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
      finiteMarkedPoissonSampleLaw (lowerLocalizedNullLaw theta k j hp r b omega) R xi)).map
        (lowerPoissonCellReport k r) =
      Measure.sum (fun m : ℕ => poissonMeasure xi {m} •
        (lowerUnitCellDesign (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) m).map
          (Sigma.mk m)) := by
  let mu := Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
    finiteMarkedPoissonSampleLaw (lowerLocalizedNullLaw theta k j hp r b omega) R xi)
  have hcover : (⋃ m : ℕ,
      (FiniteSample.count : FiniteSample (Omega × ℝ) → ℕ) ⁻¹' {m}) = Set.univ := by
    ext s
    simp
  have hdis : Pairwise (Function.onFun Disjoint
      (fun m : ℕ => (FiniteSample.count : FiniteSample (Omega × ℝ) → ℕ) ⁻¹' {m})) := by
    intro m n hmn
    exact (Set.disjoint_singleton.mpr hmn).preimage _
  have hsum : mu = Measure.sum (fun m : ℕ => mu.restrict
      (FiniteSample.count ⁻¹' {m})) := by
    rw [← Measure.restrict_iUnion hdis
      (fun m => (measurableSet_singleton m).preimage measurable_finiteSample_count),
      hcover, Measure.restrict_univ]
  change mu.map _ = _
  rw [hsum, Measure.map_sum (measurable_lowerPoissonCellReport k r).aemeasurable]
  congr 1
  funext m
  exact lower_localized_poisson_report_sign_mixture_fiber theta k j m hp hk r omega R xi

/-- Reported designs in all actual null cells are independent and each has the
canonical Poisson-count mixture. This supplies the null design averaging in (40). -/
-- @node: lower_null_poisson_partition_reported_design
lemma lower_null_poisson_partition_reported_design (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (omega : Fin j → Bool)
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : NNReal) :
    (Causalean.Stat.Minimax.Mixture.uniformMixture (fun lambda : Fin k → Bool =>
      finiteMarkedPoissonSampleLaw (lowerNullLaw theta k j hp lambda omega).law R lam)).map
        (fun s => fun r : Fin k => lowerPoissonCellReport k r
          ((lowerRecordPartition k hk).restrictCell r s)) =
      Measure.pi (fun _ : Fin k => Measure.sum (fun m : ℕ =>
        poissonMeasure (lam / k) {m} •
          (lowerUnitCellDesign (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) m).map
            (Sigma.mk m))) := by
  have (r : Fin k) : IsProbabilityMeasure
      (Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
        finiteMarkedPoissonSampleLaw (lowerLocalizedNullLaw theta k j hp r b omega) R
          (lam / k))) := Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability _
  rw [show (fun s => fun r : Fin k => lowerPoissonCellReport k r
      ((lowerRecordPartition k hk).restrictCell r s)) =
      (fun q : Fin k → FiniteSample (Omega × ℝ) => fun r => lowerPoissonCellReport k r (q r)) ∘
        (lowerRecordPartition k hk).restrictPartition by rfl,
    ← Measure.map_map (by fun_prop)
      (lowerRecordPartition k hk).measurable_restrictPartition,
    lower_null_poisson_partition_sign_mixture theta k j hp hk omega R lam,
    Measure.pi_map_pi (fun r => (measurable_lowerPoissonCellReport k r).aemeasurable)]
  simp_rw [lower_localized_poisson_report_sign_mixture theta k j hp hk _ omega R (lam / k)]

end CausalSmith.Stat.DensityEffectRoughNull
