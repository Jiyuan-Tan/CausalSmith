module
public import Causalean.Stat.OrderStatistic.Basic

/-!
# Dirichlet coordinate law for uniform spacings

The first `n` spacings, including the gap from zero to the first order
statistic, give ordinary coordinates for the `n+1`-component spacing simplex.
The last spacing is one minus their sum. Their density in these coordinates
is the constant `n!` on the standard simplex.
-/

@[expose] public section

namespace Causalean.Stat.OrderStatistic

open MeasureTheory

noncomputable section

/-- Given [a finite dimension](hyp:n), [an ordered real tuple](hyp:y), and [a coordinate index](hyp:i), the [ordered spacing](goal) is [the successive difference at that coordinate, beginning from zero](step:1). -/
def orderedSpacings (n : ℕ) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i.val = 0 then y i else y i - y ⟨i.val - 1, by omega⟩

/-- Given [a finite dimension](hyp:n), [a spacing vector](hyp:z), and [a coordinate index](hyp:i), the [prefix coordinate](goal) is [the sum of spacings through that coordinate](step:1). -/
def prefixCoordinates (n : ℕ) (z : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.Iic i, z j

/-- Given [a sample size](hyp:n), [a real sample](hyp:x), and [a coordinate index](hyp:i), the [first spacing vector](goal) is [the successive differences of the sorted sample, beginning from zero, so its first entry is the smallest observation itself](step:1). -/
def firstNSpacings (n : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i.val = 0 then sortedSample n x i
  else sortedSample n x i - sortedSample n x ⟨i.val - 1, by omega⟩

/-- Given [a finite dimension](hyp:n), the [spacing simplex](goal) is [the nonnegative coordinate simplex with total at most one](step:1). -/
def spacingSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {z | (∀ i, 0 ≤ z i) ∧ (∑ i, z i) ≤ 1}

/-- Given [a finite dimension](hyp:n) and [a spacing vector](hyp:z), [successive differences of its prefix coordinates recover that vector](goal). -/
theorem orderedSpacings_prefixCoordinates (n : ℕ) (z : Fin n → ℝ) :
    orderedSpacings n (prefixCoordinates n z) = z := by
  funext i
  by_cases hi : i.val = 0
  · have hset : Finset.Iic i = {i} := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_singleton]
      constructor
      · intro hj
        exact Fin.ext (by omega)
      · intro h
        subst j
        exact le_refl _
    simp [orderedSpacings, prefixCoordinates, hi, hset]
  · have hset : Finset.Iic (⟨i.val - 1, by omega⟩ : Fin n) = Finset.Iio i := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_Iio, Fin.le_def, Fin.lt_def]
      omega
    have hsum := Finset.sum_Iio_add_eq_sum_Iic (f := z) i
    rw [← hset] at hsum
    simp only [orderedSpacings, prefixCoordinates, hi, ↓reduceIte]
    linarith

/-- Given [a finite dimension](hyp:n) and [a real tuple](hyp:y), [prefix sums of its successive differences recover that tuple](goal). -/
theorem prefixCoordinates_orderedSpacings (n : ℕ) (y : Fin n → ℝ) :
    prefixCoordinates n (orderedSpacings n y) = y := by
  cases n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n =>
      funext i
      induction i using Fin.induction with
      | zero =>
          have hset : Finset.Iic (0 : Fin (n + 1)) = {0} := by
            ext j
            simp only [Finset.mem_Iic, Finset.mem_singleton]
            exact ⟨fun h => le_antisymm h (bot_le), fun h => h ▸ le_refl _⟩
          simp [prefixCoordinates, orderedSpacings, hset]
      | succ j ih =>
          have hset : Finset.Iio j.succ = Finset.Iic j.castSucc := by
            ext k
            simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def]
            simp only [Fin.val_succ, Fin.val_castSucc]
            omega
          have hpred : (⟨j.val, by omega⟩ : Fin (n + 1)) = j.castSucc := by
            ext
            rfl
          have hsum := Finset.sum_Iio_add_eq_sum_Iic
            (f := orderedSpacings (n + 1) y) j.succ
          rw [hset] at hsum
          change (∑ k ∈ Finset.Iic j.succ, orderedSpacings (n + 1) y k) = y j.succ
          rw [← hsum, ← prefixCoordinates, ih]
          simp [orderedSpacings, hpred]

/-- Given [a finite dimension](hyp:n), [the preimage of the spacing simplex under successive differences is exactly the ordered unit region](goal). -/
theorem orderedSpacings_preimage_simplex (n : ℕ) :
    (orderedSpacings n) ⁻¹' spacingSimplex n = orderedUnitRegion n := by
  ext y
  simp only [Set.mem_preimage, spacingSimplex, orderedUnitRegion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hpos, hsum⟩
    have hy : prefixCoordinates n (orderedSpacings n y) = y :=
      prefixCoordinates_orderedSpacings n y
    have hmono : Monotone (prefixCoordinates n (orderedSpacings n y)) := by
      intro i j hij
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Iic_subset_Iic.mpr hij) (by intros; exact hpos _)
    refine ⟨?_, hy ▸ hmono⟩
    intro i
    rw [← hy]
    constructor
    · exact Finset.sum_nonneg (fun j _ => hpos j)
    · exact le_trans (Finset.sum_le_univ_sum_of_nonneg hpos) hsum
  · rintro ⟨hunit, hmono⟩
    constructor
    · intro i
      by_cases hi : i.val = 0
      · simpa [orderedSpacings, hi] using (hunit i).1
      · have hp : (⟨i.val - 1, by omega⟩ : Fin n) ≤ i := by
          apply Fin.le_def.mpr
          change i.val - 1 ≤ i.val
          omega
        simpa [orderedSpacings, hi] using sub_nonneg.mpr (hmono hp)
    · cases n with
      | zero => simp
      | succ m =>
          have hlast : (Finset.Iic (Fin.last m)) = Finset.univ := by
            ext i
            simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
            exact Fin.le_last i
          have h := congrFun (prefixCoordinates_orderedSpacings (m + 1) y) (Fin.last m)
          simp only [prefixCoordinates, hlast] at h
          rw [h]
          exact (hunit (Fin.last m)).2

/-- Given [a finite dimension](hyp:n), the [linear spacing transformation](goal) is [the linear map of successive coordinate differences](step:1). -/
def orderedSpacingsLinear (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i : Fin n =>
    if h : i.val = 0 then (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    else (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) -
      LinearMap.proj (⟨i.val - 1, by omega⟩ : Fin n)

/-- Given [a finite dimension](hyp:n) and [a real tuple](hyp:y), [the linear spacing transformation agrees with the spacing definition](goal). -/
theorem orderedSpacingsLinear_apply (n : ℕ) (y : Fin n → ℝ) :
    orderedSpacingsLinear n y = orderedSpacings n y := by
  funext i
  by_cases hi : i.val = 0
  · simp [orderedSpacingsLinear, orderedSpacings, hi]
  · simp [orderedSpacingsLinear, orderedSpacings, hi]

/-- Given [a finite dimension](hyp:n), [the linear spacing transformation has determinant one](goal). -/
theorem orderedSpacingsLinear_det (n : ℕ) :
    LinearMap.det (orderedSpacingsLinear n) = 1 := by
  classical
  let M := LinearMap.toMatrix' (orderedSpacingsLinear n)
  have htri : M.IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    have hj0 : i.val ≠ 0 ∨ i.val = 0 := ne_or_eq _ _
    rcases hj0 with hi | hi
    · simp [M, LinearMap.toMatrix'_apply, orderedSpacingsLinear_apply,
        orderedSpacings, hi, ne_of_lt hij',
        show (⟨i.val - 1, by omega⟩ : Fin n) ≠ j from by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega]
    · simp [M, LinearMap.toMatrix'_apply, orderedSpacingsLinear_apply,
        orderedSpacings, hi, ne_of_lt hij']
  have hdiag (i : Fin n) : M i i = 1 := by
    by_cases hi : i.val = 0
    · simp [M, LinearMap.toMatrix'_apply, orderedSpacingsLinear_apply,
        orderedSpacings, hi]
    · have hp : (⟨i.val - 1, by omega⟩ : Fin n) ≠ i := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [M, LinearMap.toMatrix'_apply, orderedSpacingsLinear_apply,
        orderedSpacings, hi, hp]
  rw [← LinearMap.det_toMatrix']
  change M.det = 1
  rw [Matrix.det_of_isLowerTriangular M htri]
  simp [hdiag]

/-- Given [a finite dimension](hyp:n), [the linear spacing transformation preserves Lebesgue measure](goal). -/
theorem orderedSpacings_measurePreserving (n : ℕ) :
    MeasurePreserving (orderedSpacings n) volume volume := by
  have hfun : orderedSpacings n = orderedSpacingsLinear n := by
    funext y
    exact (orderedSpacingsLinear_apply n y).symm
  have hmeas : Measurable (orderedSpacings n) := by
    rw [hfun]
    exact (orderedSpacingsLinear n).continuous_of_finiteDimensional.measurable
  refine ⟨hmeas, ?_⟩
  rw [hfun]
  simpa [orderedSpacingsLinear_det n] using
    (Real.map_linearMap_volume_pi_eq_smul_volume_pi
      (f := orderedSpacingsLinear n) (by simp [orderedSpacingsLinear_det n]))

/-- Given [a finite dimension](hyp:n), [successive differences transport restricted Lebesgue measure from the ordered unit region to the spacing simplex](goal). -/
theorem orderedSpacings_restrict_law (n : ℕ) :
    (volume.restrict (orderedUnitRegion n)).map (orderedSpacings n) =
      volume.restrict (spacingSimplex n) := by
  have hsimplex : MeasurableSet (spacingSimplex n) := by
    have hclosed : IsClosed (spacingSimplex n) := by
      change IsClosed {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ (∑ i, z i) ≤ 1}
      apply IsClosed.inter
      · have hp : IsClosed (⋂ i : Fin n,
            (fun z : Fin n → ℝ => z i) ⁻¹' Set.Ici (0 : ℝ)) :=
          isClosed_iInter (fun i => isClosed_Ici.preimage (continuous_apply i))
        have heq : {z : Fin n → ℝ | ∀ i, 0 ≤ z i} =
            ⋂ i : Fin n, (fun z : Fin n → ℝ => z i) ⁻¹' Set.Ici (0 : ℝ) := by
          ext z
          simp
        change IsClosed (Set.ofPred (fun z : Fin n → ℝ => ∀ i, 0 ≤ z i))
        rw [heq]
        exact hp
      · exact isClosed_Iic.preimage
          (continuous_finsetSum _ (fun i _ =>
            (show Continuous (fun z : Fin n → ℝ => z i) from continuous_apply i)))
    exact hclosed.measurableSet
  have hmp := orderedSpacings_measurePreserving n
  rw [← orderedSpacings_preimage_simplex n,
    ← Measure.restrict_map hmp.measurable hsimplex, hmp.map_eq]

/-- Given [a finite sample size](hyp:n) and [a real sample](hyp:x), [the first spacing vector equals the successive differences of the sorted sample](goal). -/
theorem firstNSpacings_eq_orderedSpacings (n : ℕ) (x : Fin n → ℝ) :
    firstNSpacings n x = orderedSpacings n (sortedSample n x) := by
  rfl

/-- Given [a finite sample size](hyp:n), [the first spacing vector of an iid unit-uniform sample has factorial density on the spacing simplex](goal). -/
theorem uniform_firstN_spacings_law (n : ℕ) :
    (iidSample uniform01 n).map (firstNSpacings n) =
      (n.factorial : ENNReal) • (volume.restrict (spacingSimplex n)) := by
  have hsort : AEMeasurable (sortedSample n) (volume : Measure (Fin n → ℝ)) := by
    let s (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
      {x | Monotone (x ∘ σ)}
    have hs (σ : Equiv.Perm (Fin n)) : MeasurableSet (s σ) := by
      have hc : Continuous (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
      exact (isClosed_monotone.preimage hc).measurableSet
    have hcover : (⋃ σ, s σ) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨Tuple.sort x, Tuple.monotone_sort x⟩
    have hpiece (σ : Equiv.Perm (Fin n)) :
        AEMeasurable (sortedSample n) (volume.restrict (s σ)) := by
      have hp : Measurable (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
      apply hp.aemeasurable.congr
      exact ae_restrict_of_forall_mem (hs σ) (fun x hx =>
        (show (fun x => x ∘ σ) x = sortedSample n x from
          (Tuple.comp_sort_eq_comp_iff_monotone (f := x) (σ := σ)).2 hx))
    simpa only [hcover, Measure.restrict_univ] using (AEMeasurable.iUnion hpiece)
  have hsort' : AEMeasurable (sortedSample n) (iidSample uniform01 n) := by
    rw [iid_uniform_cube_law]
    exact hsort.restrict
  have hspacing : Measurable (orderedSpacings n) :=
    (orderedSpacings_measurePreserving n).measurable
  have hfun : firstNSpacings n = orderedSpacings n ∘ sortedSample n := by
    funext x
    exact firstNSpacings_eq_orderedSpacings n x
  rw [hfun]
  rw [← AEMeasurable.map_map_of_aemeasurable
    (hspacing.aemeasurable : AEMeasurable (orderedSpacings n)
      ((iidSample uniform01 n).map (sortedSample n))) hsort']
  rw [sorted_uniform_law n, Measure.map_smul, orderedSpacings_restrict_law]

end
end Causalean.Stat.OrderStatistic
