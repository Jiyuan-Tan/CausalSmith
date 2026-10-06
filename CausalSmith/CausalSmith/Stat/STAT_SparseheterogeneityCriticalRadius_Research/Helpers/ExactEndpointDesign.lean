module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Estimator

/-! # Finite-design statistics for the exact-homogeneity endpoint

This module defines the cell and treatment counts and the within-cell regression
denominator used by the exact-homogeneity estimator.  It also supplies their
elementary measurability facts independently of the endpoint theorem.
-/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- The exact-homogeneity subclass consists of critical-class laws whose occupied-cell effects
all equal their average treatment effect. -/
-- @node: ExactClass
def ExactClass (n : ℕ) (M : ℝ) :=
  {P : CriticalClass n M // ∀ k, 0 < P.law.cellMass k →
    DiscreteAteHeterogeneityFrontier.cellEffect P.law k =
      DiscreteAteHeterogeneityFrontier.rawAteFormula P.law}

/-- The number of sample observations in a specified covariate cell. -/
-- @node: exactCellCount
def exactCellCount (n : ℕ) (sample : Fin n → SampleObs n) (k : Fin n) : ℕ :=
  ∑ i : Fin n, if (sample i).x = k then 1 else 0

/-- The number of treated sample observations in a specified covariate cell. -/
-- @node: exactTreatedCount
def exactTreatedCount (n : ℕ) (sample : Fin n → SampleObs n) (k : Fin n) : ℕ :=
  ∑ i : Fin n, if (sample i).x = k ∧ (sample i).a = true then 1 else 0

/-- The number of repeated covariate observations beyond the first observation in each occupied
cell. -/
-- @node: exactCollisionCount
def exactCollisionCount (n : ℕ) (sample : Fin n → SampleObs n) : ℕ :=
  ∑ k : Fin n, (exactCellCount n sample k - 1)

/-- The guarded empirical treatment fraction in a specified covariate cell. -/
-- @node: exactTreatmentMean
noncomputable def exactTreatmentMean (n : ℕ)
    (sample : Fin n → SampleObs n) (k : Fin n) : ℝ :=
  if exactCellCount n sample k = 0 then 0
  else exactTreatedCount n sample k / exactCellCount n sample k

/-- The within-cell treatment regression denominator, totalized at empty cells. -/
-- @node: exactRegressionD
noncomputable def exactRegressionD (n : ℕ)
    (sample : Fin n → SampleObs n) : ℝ :=
  ∑ k : Fin n, if exactCellCount n sample k = 0 then 0 else
    exactTreatedCount n sample k *
      (exactCellCount n sample k - exactTreatedCount n sample k : ℕ) /
      exactCellCount n sample k

/-- The covariate coordinate of one observed record is measurable. -/
-- @node: sampleObsX_measurable
lemma sampleObsX_measurable (n : ℕ) :
    Measurable (fun o : SampleObs n => o.x) := by
  have htuple : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  exact measurable_fst.comp htuple

/-- The treatment coordinate of one observed record is measurable. -/
-- @node: sampleObsA_measurable
lemma sampleObsA_measurable (n : ℕ) :
    Measurable (fun o : SampleObs n => o.a) := by
  have htuple : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  exact measurable_fst.comp (measurable_snd.comp htuple)

/-- The outcome coordinate of one observed record is measurable. -/
-- @node: sampleObsY_measurable
lemma sampleObsY_measurable (n : ℕ) :
    Measurable (fun o : SampleObs n => o.y) := by
  have htuple : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  exact measurable_snd.comp (measurable_snd.comp htuple)

/-- A fixed cell count is measurable as a function of the sample. -/
-- @node: exactCellCount_measurable
lemma exactCellCount_measurable (n : ℕ) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n => exactCellCount n sample k) := by
  unfold exactCellCount
  classical
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.ite
  · exact (measurableSet_singleton k).preimage
      ((sampleObsX_measurable n).comp (measurable_pi_apply i))
  · exact measurable_const
  · exact measurable_const

/-- A fixed treated-cell count is measurable as a function of the sample. -/
-- @node: exactTreatedCount_measurable
lemma exactTreatedCount_measurable (n : ℕ) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n => exactTreatedCount n sample k) := by
  unfold exactTreatedCount
  classical
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.ite
  · exact ((measurableSet_singleton k).preimage
        ((sampleObsX_measurable n).comp (measurable_pi_apply i))).inter
      ((measurableSet_singleton true).preimage
        ((sampleObsA_measurable n).comp (measurable_pi_apply i)))
  · exact measurable_const
  · exact measurable_const

/-- The cell counts sum to the sample size. -/
-- @node: sum_exactCellCount
lemma sum_exactCellCount (n : ℕ) (sample : Fin n → SampleObs n) :
    ∑ k : Fin n, exactCellCount n sample k = n := by
  classical
  unfold exactCellCount
  rw [Finset.sum_comm]
  simp

/-- The repeated-observation collision count is measurable as a function of the sample. -/
-- @node: exactCollisionCount_measurable
lemma exactCollisionCount_measurable (n : ℕ) :
    Measurable (exactCollisionCount n) := by
  unfold exactCollisionCount
  apply Finset.measurable_sum
  intro k hk
  exact (exactCellCount_measurable n k).sub measurable_const

/-- A measurable natural-valued statistic remains measurable after coercion to the reals. -/
-- @node: measurable_nat_to_real
lemma measurable_nat_to_real {α : Type*} [MeasurableSpace α] (f : α → ℕ)
    (hf : Measurable f) : Measurable (fun x => (f x : ℝ)) :=
  (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp hf

/-- A fixed cell's guarded empirical treatment fraction is measurable. -/
-- @node: exactTreatmentMean_measurable
lemma exactTreatmentMean_measurable (n : ℕ) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n => exactTreatmentMean n sample k) := by
  unfold exactTreatmentMean
  apply Measurable.ite
  · exact (measurableSet_singleton 0).preimage (exactCellCount_measurable n k)
  · exact measurable_const
  · exact (measurable_nat_to_real _ (exactTreatedCount_measurable n k)).div
      (measurable_nat_to_real _ (exactCellCount_measurable n k))

/-- Looking up one member of a finite measurable family at a measurable finite index is
measurable. -/
-- @node: measurable_finite_lookup
lemma measurable_finite_lookup (n : ℕ) {α : Type*} [MeasurableSpace α]
    (f : Fin n → α → ℝ) (g : α → Fin n)
    (hf : ∀ k, Measurable (f k)) (hg : Measurable g) :
    Measurable (fun s => f (g s) s) := by
  classical
  have h : (fun s => f (g s) s) =
      (fun s => ∑ k : Fin n, if g s = k then f k s else 0) := by
    funext s
    simp
  rw [h]
  apply Finset.measurable_sum
  intro k hk
  apply Measurable.ite
  · exact (measurableSet_singleton k).preimage hg
  · exact hf k
  · exact measurable_const

/-- The within-cell treatment regression denominator is measurable. -/
-- @node: exactRegressionD_measurable
lemma exactRegressionD_measurable (n : ℕ) :
    Measurable (exactRegressionD n) := by
  unfold exactRegressionD
  apply Finset.measurable_sum
  intro k hk
  apply Measurable.ite
  · exact (measurableSet_singleton 0).preimage (exactCellCount_measurable n k)
  · exact measurable_const
  · exact ((measurable_nat_to_real _ (exactTreatedCount_measurable n k)).mul
      (measurable_nat_to_real _ ((exactCellCount_measurable n k).sub
        (exactTreatedCount_measurable n k)))).div
        (measurable_nat_to_real _ (exactCellCount_measurable n k))

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
