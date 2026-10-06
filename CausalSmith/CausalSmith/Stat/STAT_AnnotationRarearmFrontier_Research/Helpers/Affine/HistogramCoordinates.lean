module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Histogram

/-!
The full histogram embedding is injective and its image consists precisely of
histograms with zero counts at the structural zero atoms. Singleton probabilities
therefore reduce to the unique original rare-cell and reservoir count vector.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Read every rare-cell and reservoir coordinate from the original histograms. -/
-- @node: affineHistogramCoordinates
def affineHistogramCoordinates (d k : Nat) (hk : k < d)
    (h : (Obs d → Nat) × (AuxObs d → Nat)) :
    (Fin k → ((Nat × Nat) × (Nat × (Nat × Nat)))) ×
      ((Nat × Nat) × (Nat × Nat)) :=
  (fun i =>
    let j : Fin d := ⟨i.val, lt_trans i.isLt hk⟩
    ((h.1 (j, true, true), h.1 (j, true, false)),
      (h.2 (j, true), (h.1 (j, false, false), h.2 (j, false)))),
   ((h.1 (⟨k, hk⟩, true, false), h.1 (⟨k, hk⟩, false, false)),
    (h.2 (⟨k, hk⟩, true), h.2 (⟨k, hk⟩, false))))

/-- [Under the stated inputs and conditions](hyp:hk,d,k), The full embedding loses none of the nine types of stochastic coordinates.  This gives [the stated result](goal).-/
-- @node: affineHistogramCoordinates_leftInverse
lemma affineHistogramCoordinates_leftInverse (d k : Nat) (hk : k < d) :
    Function.LeftInverse (affineHistogramCoordinates d k hk)
      (affineFullCountHistograms d k) := by
  intro counts
  apply Prod.ext
  · funext i
    simp [affineHistogramCoordinates, affineFullCountHistograms]
  · simp [affineHistogramCoordinates, affineFullCountHistograms]

/-- [Under the stated inputs and conditions](hyp:hk,d,k), A full count vector is uniquely determined by its original atom histograms.  This gives [the stated result](goal).-/
-- @node: affineFullCountHistograms_injective
lemma affineFullCountHistograms_injective (d k : Nat) (hk : k < d) :
    Function.Injective (affineFullCountHistograms d k) :=
  (affineHistogramCoordinates_leftInverse d k hk).injective

/-- Structural zero coordinates of the two-channel raw affine experiment. -/
-- @node: affineHistogramSupported
def affineHistogramSupported (d k : Nat)
    (h : (Obs d → Nat) × (AuxObs d → Nat)) : Prop :=
  (∀ j : Fin d, h.1 (j, false, true) = 0) ∧
  (∀ j : Fin d, k ≤ j.val → h.1 (j, true, true) = 0) ∧
  (∀ j : Fin d, k < j.val →
    (∀ a y : Bool, h.1 (j, a, y) = 0) ∧ (∀ a : Bool, h.2 (j, a) = 0))

/-- [Under the stated inputs and conditions](hyp:counts,d,k), Every embedded count vector vanishes at exactly the structural zero coordinates.  This gives [the stated result](goal).-/
-- @node: affineFullCountHistograms_supported
lemma affineFullCountHistograms_supported (d k : Nat)
    (counts : (Fin k → ((Nat × Nat) × (Nat × (Nat × Nat)))) ×
      ((Nat × Nat) × (Nat × Nat))) :
    affineHistogramSupported d k (affineFullCountHistograms d k counts) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simp [affineFullCountHistograms]
  · intro j hj
    simp [affineFullCountHistograms, not_lt.mpr hj]
  · intro j hj
    exact ⟨fun a y => (affineFullCountHistograms_null d k counts j hj a y).1,
      fun a => (affineFullCountHistograms_null d k counts j hj a false).2⟩

/-- [Under the stated inputs and conditions](hyp:hk,h,hs,d,k), Reading and re-embedding any supported histogram returns that histogram.  This gives [the stated result](goal).-/
-- @node: affineHistogramCoordinates_rightInverse
lemma affineHistogramCoordinates_rightInverse (d k : Nat) (hk : k < d)
    (h : (Obs d → Nat) × (AuxObs d → Nat)) (hs : affineHistogramSupported d k h) :
    affineFullCountHistograms d k (affineHistogramCoordinates d k hk h) = h := by
  rcases hs with ⟨hcontrol, htreated, hnull⟩
  apply Prod.ext
  · funext z
    rcases z with ⟨j, a, y⟩
    by_cases hj : j.val < k
    · cases a <;> cases y <;>
        simp [affineFullCountHistograms, affineHistogramCoordinates, hj, hcontrol]
    · by_cases heq : j.val = k
      · have hjEq : j = ⟨k, hk⟩ := Fin.ext heq
        subst j
        cases a <;> cases y <;>
          simp [affineFullCountHistograms, affineHistogramCoordinates, hcontrol,
            htreated ⟨k, hk⟩ (le_refl k)]
      · have hgt : k < j.val := lt_of_le_of_ne (not_lt.mp hj) (Ne.symm heq)
        simp [affineFullCountHistograms, hj, heq, (hnull j hgt).1 a y]
  · funext z
    rcases z with ⟨j, a⟩
    by_cases hj : j.val < k
    · cases a <;> simp [affineFullCountHistograms, affineHistogramCoordinates, hj]
    · by_cases heq : j.val = k
      · have hjEq : j = ⟨k, hk⟩ := Fin.ext heq
        subst j
        cases a <;> simp [affineFullCountHistograms, affineHistogramCoordinates]
      · have hgt : k < j.val := lt_of_le_of_ne (not_lt.mp hj) (Ne.symm heq)
        simp [affineFullCountHistograms, hj, heq, (hnull j hgt).2 a]

/-- [Under the stated inputs and conditions](hyp:hk,h,d,k), The structural zero conditions exactly characterize the histogram image.  This gives [the stated result](goal).-/
-- @node: affineFullCountHistograms_range
lemma affineFullCountHistograms_range (d k : Nat) (hk : k < d)
    (h : (Obs d → Nat) × (AuxObs d → Nat)) :
    h ∈ Set.range (affineFullCountHistograms d k) ↔ affineHistogramSupported d k h := by
  constructor
  · rintro ⟨counts, rfl⟩
    exact affineFullCountHistograms_supported d k counts
  · intro hs
    exact ⟨affineHistogramCoordinates d k hk h,
      affineHistogramCoordinates_rightInverse d k hk h hs⟩

/-- [Under the stated inputs and conditions](hyp:hk,h,hs,d,k), A supported histogram has precisely one preimage, the explicit coordinate readback.  This gives [the stated result](goal).-/
-- @node: affineFullCountHistograms_preimage_singleton
lemma affineFullCountHistograms_preimage_singleton (d k : Nat) (hk : k < d)
    (h : (Obs d → Nat) × (AuxObs d → Nat)) (hs : affineHistogramSupported d k h) :
    affineFullCountHistograms d k ⁻¹' {h} = {affineHistogramCoordinates d k hk h} := by
  ext counts
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hc
    apply affineFullCountHistograms_injective d k hk
    exact hc.trans (affineHistogramCoordinates_rightInverse d k hk h hs).symm
  · rintro rfl
    exact affineHistogramCoordinates_rightInverse d k hk h hs

/-- [Under the stated inputs and conditions](hyp:h,hs,d,k), Unsupported histograms have no preimage under the full embedding.  This gives [the stated result](goal).-/
-- @node: affineFullCountHistograms_preimage_singleton_empty
lemma affineFullCountHistograms_preimage_singleton_empty (d k : Nat)
    (h : (Obs d → Nat) × (AuxObs d → Nat)) (hs : ¬ affineHistogramSupported d k h) :
    affineFullCountHistograms d k ⁻¹' {h} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro counts hc
  apply hs
  have heq : affineFullCountHistograms d k counts = h := hc
  rw [← heq]
  exact affineFullCountHistograms_supported d k counts

/-- [Under the stated inputs and conditions](hyp:hk,mu,h,d,k), Singleton masses after embedding are explicit coordinate masses on the image,
and zero off the image. This applies to conditional laws and to their mixtures.  This gives [the stated result](goal).-/
-- @node: affineFullCountHistograms_map_singleton
lemma affineFullCountHistograms_map_singleton (d k : Nat) (hk : k < d)
    (mu : Measure ((Fin k → ((Nat × Nat) × (Nat × (Nat × Nat)))) ×
      ((Nat × Nat) × (Nat × Nat))))
    (h : (Obs d → Nat) × (AuxObs d → Nat)) :
    mu.map (affineFullCountHistograms d k) {h} =
      if affineHistogramSupported d k h then mu {affineHistogramCoordinates d k hk h}
      else 0 := by
  classical
  rw [Measure.map_apply (affineFullCountHistograms_measurable d k)
    (measurableSet_singleton h)]
  split_ifs with hs
  · rw [affineFullCountHistograms_preimage_singleton d k hk h hs]
  · rw [affineFullCountHistograms_preimage_singleton_empty d k h hs, measure_empty]

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,n,m,d), The actual conditional histogram law is the pushforward of the full count law.  This gives [the stated result](goal).-/
-- @node: affineHistogramKernel_apply_eq_map
lemma affineHistogramKernel_apply_eq_map (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    affineHistogramKernel n m d eps sigma hyp lat =
      (affineFullCountKernel n m d eps sigma hyp lat).map
        (affineFullCountHistograms d (affineTuning n m d eps).Kstar) := by
  rw [affineHistogramKernel, Kernel.deterministic_comp_eq_map, Kernel.map_apply]
  exact affineFullCountHistograms_measurable d _

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,hk,h,n,m,d), The conditional histogram singleton mass is the unique original count mass;
no untracked coordinates or histogram multiplicities remain.  This gives [the stated result](goal).-/
-- @node: affineHistogramKernel_singleton
lemma affineHistogramKernel_singleton (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (hk : (affineTuning n m d eps).Kstar < d)
    (h : (Obs d → Nat) × (AuxObs d → Nat)) :
    affineHistogramKernel n m d eps sigma hyp lat {h} =
      if affineHistogramSupported d (affineTuning n m d eps).Kstar h then
        affineFullCountKernel n m d eps sigma hyp lat
          {affineHistogramCoordinates d (affineTuning n m d eps).Kstar hk h}
      else 0 := by
  rw [affineHistogramKernel_apply_eq_map]
  exact affineFullCountHistograms_map_singleton d _ hk _ h

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,counts,n,m,d), Conditional full count singleton probabilities factor over the independent rare
cells and the independent common reservoir.  This gives [the stated result](goal).-/
-- @node: affineFullCountKernel_singleton
lemma affineFullCountKernel_singleton (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (counts : (Fin (affineTuning n m d eps).Kstar →
      ((Nat × Nat) × (Nat × (Nat × Nat)))) × ((Nat × Nat) × (Nat × Nat))) :
    affineFullCountKernel n m d eps sigma hyp lat {counts} =
      (∏ i, affineCellFullPoissonLaw sigma (affineTuning n m d eps).u
        (affineTuning n m d eps).w hyp (lat i) {counts.1 i}) *
      affineReservoirCountLaw n m d eps sigma {counts.2} := by
  rw [affineFullCountKernel, Kernel.prod_apply, Kernel.const_apply]
  change ((Measure.pi fun i => affineCellFullPoissonLaw sigma
    (affineTuning n m d eps).u (affineTuning n m d eps).w hyp (lat i)).prod
      (affineReservoirCountLaw n m d eps sigma)) {(counts.1, counts.2)} = _
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, Measure.pi_singleton]

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,hk,h,hs,n,m,d), A supported original histogram has the product probability of its read-back
rare-cell counts and reservoir counts in the actual conditional experiment.  This gives [the stated result](goal).-/
-- @node: affineHistogramKernel_supported_singleton
lemma affineHistogramKernel_supported_singleton (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (hk : (affineTuning n m d eps).Kstar < d)
    (h : (Obs d → Nat) × (AuxObs d → Nat))
    (hs : affineHistogramSupported d (affineTuning n m d eps).Kstar h) :
    let counts := affineHistogramCoordinates d (affineTuning n m d eps).Kstar hk h
    affineHistogramKernel n m d eps sigma hyp lat {h} =
      (∏ i, affineCellFullPoissonLaw sigma (affineTuning n m d eps).u
        (affineTuning n m d eps).w hyp (lat i) {counts.1 i}) *
      affineReservoirCountLaw n m d eps sigma {counts.2} := by
  rw [affineHistogramKernel_singleton n m d eps sigma hyp lat hk h, if_pos hs]
  exact affineFullCountKernel_singleton n m d eps sigma hyp lat _

end CausalSmith.Stat.AnnotationRarearmFrontier
