module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.AtomLaw
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.HistogramCoordinates

/-!
Singleton factorization and structural zero support for the original raw atom
histograms, connecting the embedded count experiment to independent atom counts.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- Independent atom counts in both original raw channels. -/
-- @node: affineRawHistogramLaw
noncomputable def affineRawHistogramLaw (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    Measure ((Obs d → Nat) × (AuxObs d → Nat)) :=
  (Measure.pi fun z : Obs d => poissonMeasure
    (Real.toNNReal ((affineTuning n m d eps).u * rawTable hyp n m d eps sigma lat z))).prod
  (Measure.pi fun z : AuxObs d => poissonMeasure
    (Real.toNNReal ((affineTuning n m d eps).w *
      ∑ y : Bool, rawTable hyp n m d eps sigma lat (z.1, z.2, y))))

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,j,n,m,d), Raw complete counts have no positive control outcomes.  This gives [the stated result](goal).-/
-- @node: affine_rawTable_control_zero
lemma affine_rawTable_control_zero (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (j : Fin d) : rawTable hyp n m d eps sigma lat (j, false, true) = 0 := by
  simp [rawTable, bernoulliMass]

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,j,hj,a,n,m,d), Outside the rare cells, all complete positive outcome atoms are structural zeros.  This gives [the stated result](goal).-/
-- @node: affine_rawTable_positive_outcome_zero
lemma affine_rawTable_positive_outcome_zero (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (j : Fin d) (hj : (affineTuning n m d eps).Kstar ≤ j.val) (a : Bool) :
    rawTable hyp n m d eps sigma lat (j, a, true) = 0 := by
  simp [rawTable, not_lt.mpr hj, bernoulliMass]

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,j,hj,n,m,d,a,y), Labels beyond the reservoir have zero complete and auxiliary raw mass.  This gives [the stated result](goal).-/
-- @node: affine_rawTable_null
lemma affine_rawTable_null (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (j : Fin d) (hj : (affineTuning n m d eps).Kstar < j.val) (a y : Bool) :
    rawTable hyp n m d eps sigma lat (j, a, y) = 0 := by
  simp [rawTable, not_lt.mpr hj.le, ne_of_gt hj]

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,h,n,m,d), Singleton probabilities of the full original histogram factor over all atoms.  This gives [the stated result](goal).-/
-- @node: affineRawHistogramLaw_singleton
lemma affineRawHistogramLaw_singleton (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (h : (Obs d → Nat) × (AuxObs d → Nat)) :
    affineRawHistogramLaw n m d eps sigma hyp lat {h} =
      (∏ z : Obs d, poissonMeasure
        (Real.toNNReal ((affineTuning n m d eps).u *
          rawTable hyp n m d eps sigma lat z)) {h.1 z}) *
      (∏ z : AuxObs d, poissonMeasure
        (Real.toNNReal ((affineTuning n m d eps).w *
          ∑ y : Bool, rawTable hyp n m d eps sigma lat (z.1, z.2, y))) {h.2 z}) := by
  unfold affineRawHistogramLaw
  rw [← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.pi_singleton, Measure.pi_singleton]

/-- [Under the stated inputs and conditions](hyp:r), A zero-intensity atom contributes one exactly at count zero.  This gives [the stated result](goal).-/
-- @node: affine_poisson_zero_singleton
lemma affine_poisson_zero_singleton (r : Nat) :
    poissonMeasure 0 {r} = if r = 0 then 1 else 0 := by
  by_cases hr : r = 0
  · subst r; simp [poissonMeasure_singleton]
  · simp [poissonMeasure_singleton, hr, zero_pow hr]

/-- The six atom factors at a single original covariate label. -/
-- @node: affineRawCellSingleton
noncomputable def affineRawCellSingleton (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (h : (Obs d → Nat) × (AuxObs d → Nat)) (j : Fin d) : ENNReal :=
  (∏ ay : Bool × Bool, poissonMeasure
    (Real.toNNReal ((affineTuning n m d eps).u *
      rawTable hyp n m d eps sigma lat (j, ay))) {h.1 (j, ay)}) *
  (∏ a : Bool, poissonMeasure
    (Real.toNNReal ((affineTuning n m d eps).w *
      ∑ y : Bool, rawTable hyp n m d eps sigma lat (j, a, y))) {h.2 (j, a)})

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,h,n,m,d), Grouping by label preserves every original complete and auxiliary atom.  This gives [the stated result](goal).-/
-- @node: affineRawHistogramLaw_singleton_by_label
lemma affineRawHistogramLaw_singleton_by_label (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (h : (Obs d → Nat) × (AuxObs d → Nat)) :
    affineRawHistogramLaw n m d eps sigma hyp lat {h} =
      ∏ j, affineRawCellSingleton n m d eps sigma hyp lat h j := by
  rw [affineRawHistogramLaw_singleton]
  simp only [Obs, AuxObs, Fintype.prod_prod_type]
  rw [← Finset.prod_mul_distrib]
  simp only [affineRawCellSingleton, Fintype.prod_prod_type]

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,h,hs,j,hj,n,m,d), Every unused label contributes only deterministic zero counts.  This gives [the stated result](goal).-/
-- @node: affineRawCellSingleton_null
lemma affineRawCellSingleton_null (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (h : (Obs d → Nat) × (AuxObs d → Nat))
    (hs : affineHistogramSupported d (affineTuning n m d eps).Kstar h)
    (j : Fin d) (hj : (affineTuning n m d eps).Kstar < j.val) :
    affineRawCellSingleton n m d eps sigma hyp lat h j = 1 := by
  simp [affineRawCellSingleton, affine_rawTable_null n m d eps sigma hyp lat j hj,
    (hs.2.2 j hj).1, (hs.2.2 j hj).2, affine_poisson_zero_singleton]

/-- [Under the stated inputs and conditions](hyp:M,hk,f,ht,d,k), A finite label product with unit tail consists of its rare prefix and reservoir.  This gives [the stated result](goal).-/
-- @node: affine_label_product_prefix
lemma affine_label_product_prefix {M : Type*} [CommMonoid M] (d k : Nat)
    (hk : k < d) (f : Fin d → M) (ht : ∀ j, k < j.val → f j = 1) :
    (∏ j, f j) = (∏ i : Fin k, f ⟨i.val, lt_trans i.isLt hk⟩) * f ⟨k, hk⟩ := by
  let e : Fin (k + 1) → Fin d := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  have he : Function.Injective e := fun i j hij => Fin.ext (congrArg (fun z : Fin d => z.val) hij)
  have htail : ∀ j ∉ Set.range e, f j = 1 := by
    intro j hj
    apply ht
    by_contra hle
    apply hj
    exact ⟨⟨j.val, by omega⟩, rfl⟩
  rw [← Fintype.prod_of_injective e he (fun i => f (e i)) f htail (fun _ => rfl),
    Fin.prod_univ_castSucc]
  rfl

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,hk,h,hs,i,n,m,d), At a rare label the original atom factors are exactly its five-coordinate law.  This gives [the stated result](goal).-/
-- @node: affineRawCellSingleton_rare
lemma affineRawCellSingleton_rare (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (hk : (affineTuning n m d eps).Kstar < d)
    (h : (Obs d → Nat) × (AuxObs d → Nat))
    (hs : affineHistogramSupported d (affineTuning n m d eps).Kstar h)
    (i : Fin (affineTuning n m d eps).Kstar) :
    affineRawCellSingleton n m d eps sigma hyp lat h ⟨i.val, lt_trans i.isLt hk⟩ =
      affineCellFullPoissonLaw sigma (affineTuning n m d eps).u
        (affineTuning n m d eps).w hyp (lat i)
        {(affineHistogramCoordinates d (affineTuning n m d eps).Kstar hk h).1 i} := by
  rw [affineCellFullPoissonLaw_raw_atoms n m d eps sigma hyp lat
    ⟨i.val, lt_trans i.isLt hk⟩ i.isLt]
  simp only [affineHistogramCoordinates, affineRawCellSingleton,
    Fintype.prod_prod_type, Fintype.prod_bool,
    ← Set.singleton_prod_singleton, Measure.prod_prod]
  simp only [affine_rawTable_control_zero, mul_zero, Real.toNNReal_zero,
    hs.1, affine_poisson_zero_singleton, if_pos rfl, one_mul]
  ac_rfl

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,hk,h,hs,n,m,d), At the reservoir label the original atom factors retain both channels and arms.  This gives [the stated result](goal).-/
-- @node: affineRawCellSingleton_reservoir
lemma affineRawCellSingleton_reservoir (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (hk : (affineTuning n m d eps).Kstar < d)
    (h : (Obs d → Nat) × (AuxObs d → Nat))
    (hs : affineHistogramSupported d (affineTuning n m d eps).Kstar h) :
    affineRawCellSingleton n m d eps sigma hyp lat h ⟨(affineTuning n m d eps).Kstar, hk⟩ =
      affineReservoirCountLaw n m d eps sigma
        {(affineHistogramCoordinates d (affineTuning n m d eps).Kstar hk h).2} := by
  rw [affineReservoirCountLaw_raw_atoms n m d eps sigma hyp lat
    ⟨(affineTuning n m d eps).Kstar, hk⟩ rfl]
  simp only [affineHistogramCoordinates, affineRawCellSingleton,
    Fintype.prod_prod_type, Fintype.prod_bool,
    ← Set.singleton_prod_singleton, Measure.prod_prod]
  simp only [affine_rawTable_positive_outcome_zero n m d eps sigma hyp lat
    ⟨(affineTuning n m d eps).Kstar, hk⟩ (le_refl _) , mul_zero,
    Real.toNNReal_zero, hs.1, hs.2.1 ⟨(affineTuning n m d eps).Kstar, hk⟩ (le_refl _),
    affine_poisson_zero_singleton, if_pos rfl, one_mul]
  ac_rfl

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,hk,h,hs,n,m,d), Supported histogram singleton probabilities agree in both count constructions.  This gives [the stated result](goal).-/
-- @node: affineHistogramKernel_raw_supported_singleton
lemma affineHistogramKernel_raw_supported_singleton (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (hk : (affineTuning n m d eps).Kstar < d)
    (h : (Obs d → Nat) × (AuxObs d → Nat))
    (hs : affineHistogramSupported d (affineTuning n m d eps).Kstar h) :
    affineHistogramKernel n m d eps sigma hyp lat {h} =
      affineRawHistogramLaw n m d eps sigma hyp lat {h} := by
  rw [affineHistogramKernel_supported_singleton n m d eps sigma hyp lat hk h hs,
    affineRawHistogramLaw_singleton_by_label,
    affine_label_product_prefix d _ hk _ (affineRawCellSingleton_null n m d eps sigma hyp lat h hs),
    affineRawCellSingleton_reservoir n m d eps sigma hyp lat hk h hs]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact (affineRawCellSingleton_rare n m d eps sigma hyp lat hk h hs i).symm

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,h,z,hz,hc,n,m,d), A nonzero count at a zero complete intensity makes the whole atom mass zero.  This gives [the stated result](goal).-/
-- @node: affineRawHistogramLaw_complete_zero
lemma affineRawHistogramLaw_complete_zero (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (h : (Obs d → Nat) × (AuxObs d → Nat)) (z : Obs d)
    (hz : rawTable hyp n m d eps sigma lat z = 0) (hc : h.1 z ≠ 0) :
    affineRawHistogramLaw n m d eps sigma hyp lat {h} = 0 := by
  rw [affineRawHistogramLaw_singleton]
  have hp : (∏ z : Obs d, poissonMeasure
      (Real.toNNReal ((affineTuning n m d eps).u *
        rawTable hyp n m d eps sigma lat z)) {h.1 z}) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ z)
    simp [hz, affine_poisson_zero_singleton, hc]
  rw [hp, zero_mul]

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,h,z,hz,hc,n,m,d), A nonzero count at a zero auxiliary intensity makes the whole atom mass zero.  This gives [the stated result](goal).-/
-- @node: affineRawHistogramLaw_auxiliary_zero
lemma affineRawHistogramLaw_auxiliary_zero (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (h : (Obs d → Nat) × (AuxObs d → Nat)) (z : AuxObs d)
    (hz : ∀ y, rawTable hyp n m d eps sigma lat (z.1, z.2, y) = 0)
    (hc : h.2 z ≠ 0) :
    affineRawHistogramLaw n m d eps sigma hyp lat {h} = 0 := by
  rw [affineRawHistogramLaw_singleton]
  have hp : (∏ z : AuxObs d, poissonMeasure
      (Real.toNNReal ((affineTuning n m d eps).w *
        ∑ y : Bool, rawTable hyp n m d eps sigma lat (z.1, z.2, y))) {h.2 z}) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ z)
    simp [hz, affine_poisson_zero_singleton, hc]
  rw [hp, mul_zero]

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,h,hs,n,m,d), Unsupported histograms have probability zero also in the independent atom law.  This gives [the stated result](goal).-/
-- @node: affineRawHistogramLaw_unsupported_singleton
lemma affineRawHistogramLaw_unsupported_singleton (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (h : (Obs d → Nat) × (AuxObs d → Nat))
    (hs : ¬ affineHistogramSupported d (affineTuning n m d eps).Kstar h) :
    affineRawHistogramLaw n m d eps sigma hyp lat {h} = 0 := by
  by_contra hne
  apply hs
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_contra hc
    exact hne (affineRawHistogramLaw_complete_zero n m d eps sigma hyp lat h
      (j, false, true) (affine_rawTable_control_zero n m d eps sigma hyp lat j) hc)
  · intro j hj
    by_contra hc
    exact hne (affineRawHistogramLaw_complete_zero n m d eps sigma hyp lat h
      (j, true, true) (affine_rawTable_positive_outcome_zero n m d eps sigma hyp lat j hj true) hc)
  · intro j hj
    constructor
    · intro a y
      by_contra hc
      exact hne (affineRawHistogramLaw_complete_zero n m d eps sigma hyp lat h
        (j, a, y) (affine_rawTable_null n m d eps sigma hyp lat j hj a y) hc)
    · intro a
      by_contra hc
      exact hne (affineRawHistogramLaw_auxiliary_zero n m d eps sigma hyp lat h
        (j, a) (fun y => affine_rawTable_null n m d eps sigma hyp lat j hj a y) hc)

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,hk,n,m,d), The embedded conditional law equals the full independent raw atom histogram law.  This gives [the stated result](goal).-/
-- @node: affineHistogramKernel_eq_raw_atom_law
lemma affineHistogramKernel_eq_raw_atom_law (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (hk : (affineTuning n m d eps).Kstar < d) :
    affineHistogramKernel n m d eps sigma hyp lat =
      affineRawHistogramLaw n m d eps sigma hyp lat := by
  apply Measure.ext_of_singleton
  intro h
  by_cases hs : affineHistogramSupported d (affineTuning n m d eps).Kstar h
  · exact affineHistogramKernel_raw_supported_singleton n m d eps sigma hyp lat hk h hs
  · rw [affineHistogramKernel_singleton n m d eps sigma hyp lat hk h, if_neg hs,
      affineRawHistogramLaw_unsupported_singleton n m d eps sigma hyp lat h hs]

/-- [Under the stated inputs and conditions](hyp:eps,hd,n,m,d), The selected reservoir fits inside the original public alphabet.  This gives [the stated result](goal).-/
-- @node: affine_tuning_Kstar_lt_dimension
lemma affine_tuning_Kstar_lt_dimension (n m d : Nat) (eps : Real) (hd : 2 ≤ d) :
    (affineTuning n m d eps).Kstar < d := by
  have hk : (affineTuning n m d eps).Kstar ≤ d - 1 := Nat.min_le_left _ _
  omega

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,n,m,d), The conditional histogram is exactly the normalized random-scale atom count law.  This gives [the stated result](goal).-/
-- @node: affineHistogramKernel_eq_normalized_counts
lemma affineHistogramKernel_eq_normalized_counts (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    let t := affineTuning n m d eps
    let P := normalizedLaw hyp n m d eps hd sigma lat
    let Q := rawNormalizer n m d eps sigma lat
    affineHistogramKernel n m d eps sigma hyp lat =
      (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.independentPoissonCountLaw
        P.pmf.toMeasure (Real.toNNReal (t.u * Q))).prod
      (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.independentPoissonCountLaw
        (auxMarginal P).toMeasure (Real.toNNReal (t.w * Q))) := by
  dsimp only
  rw [affine_complete_countLaw_readback n m d eps hn hd heps heps' sigma hyp lat,
    affine_auxiliary_countLaw_readback n m d eps hn hd heps heps' sigma hyp lat]
  exact affineHistogramKernel_eq_raw_atom_law n m d eps sigma hyp lat
    (affine_tuning_Kstar_lt_dimension n m d eps hd)

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,n,m,d), Ordering the actual conditional histogram gives precisely the two independent
normalized iid channels at their shared random scale.  This gives [the stated result](goal).-/
-- @node: affineHistogramKernel_ordered_apply
lemma affineHistogramKernel_ordered_apply (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    let t := affineTuning n m d eps
    let P := normalizedLaw hyp n m d eps hd sigma lat
    let Q := rawNormalizer n m d eps sigma lat
    (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedHistogramReconstructionKernel
      (Obs d) (AuxObs d) ∘ₖ affineHistogramKernel n m d eps sigma hyp) lat =
      (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
        P.pmf.toMeasure (Real.toNNReal (t.u * Q))).prod
      (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
        (auxMarginal P).toMeasure (Real.toNNReal (t.w * Q))) := by
  dsimp only
  rw [Kernel.comp_apply, affineHistogramKernel_eq_raw_atom_law n m d eps sigma hyp lat
    (affine_tuning_Kstar_lt_dimension n m d eps hd)]
  exact affine_raw_atom_counts_reconstruction n m d eps hn hd heps heps' sigma hyp lat

end CausalSmith.Stat.AnnotationRarearmFrontier
