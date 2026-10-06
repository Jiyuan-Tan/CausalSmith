module
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.OrderStatisticMoments

/-!
# First two moments of a uniform order statistic

The sorted-coordinate identities follow from the first-`n` spacing law and
the simplex coordinate and cross moments in `OrderStatisticMoments`.
The zero-based sorted index `j` corresponds to beta parameters `j+1` and
`n-j`, as in the standard uniform order-statistic density.
-/

public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open Causalean.Stat.OrderStatistic

noncomputable section

private theorem firstNSpacings_aemeasurable_local (n : ℕ) :
    AEMeasurable (firstNSpacings n) (iidSample uniform01 n) := by
  classical
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
  convert hspacing.comp_aemeasurable hsort' using 1
  funext x
  exact firstNSpacings_eq_orderedSpacings n x

private theorem simplex_measurable_local (n : ℕ) :
    MeasurableSet (spacingSimplex n) := by
    change MeasurableSet {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ (∑ i, z i) ≤ 1}
    apply MeasurableSet.inter
    · have heq : {z : Fin n → ℝ | ∀ i, 0 ≤ z i} =
            ⋂ i : Fin n, (fun z : Fin n → ℝ => z i) ⁻¹' Set.Ici 0 := by
        ext z
        simp
      change MeasurableSet ({z : Fin n → ℝ | ∀ i, 0 ≤ z i})
      rw [heq]
      exact MeasurableSet.iInter (fun i =>
        measurableSet_Ici.preimage (measurable_pi_apply i))
    · exact measurableSet_Iic.preimage
        (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))

private theorem simplex_coordinate_bound_local (n : ℕ) (i : Fin n) :
    ∀ᵐ z ∂volume.restrict (spacingSimplex n), ‖z i‖ ≤ (1 : ℝ) := by
  apply ae_restrict_of_forall_mem (simplex_measurable_local n)
  intro z hz
  have h0 : 0 ≤ z i := hz.1 i
  have hle : z i ≤ 1 := by
    calc
      z i ≤ ∑ k, z k := Finset.single_le_sum (fun k _ => hz.1 k) (Finset.mem_univ i)
      _ ≤ 1 := hz.2
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact hle

private theorem simplex_coordinate_integrable_local (n : ℕ) (i : Fin n) :
    Integrable (fun z : Fin n → ℝ => z i) (volume.restrict (spacingSimplex n)) := by
  have hfinite : volume (spacingSimplex n) ≠ ⊤ := by
    change volume (scaledSpacingSimplex n 1) ≠ ⊤
    rw [scaledSpacingSimplex_volume n 1 (by norm_num)]
    simp
  exact Measure.integrableOn_of_bounded hfinite
    ((measurable_pi_apply i).aestronglyMeasurable) (simplex_coordinate_bound_local n i)

private theorem simplex_coordinate_product_integrable_local (n : ℕ) (i k : Fin n) :
    Integrable (fun z : Fin n → ℝ => z i * z k)
      (volume.restrict (spacingSimplex n)) := by
  exact Integrable.bdd_mul (simplex_coordinate_integrable_local n k)
    ((measurable_pi_apply i).aestronglyMeasurable)
    (simplex_coordinate_bound_local n i)

/-- For a [positive sample size](hyp:hn) and [zero-based sorted index](hyp:j),
 [the corresponding uniform order statistic has mean `(j+1)/(n+1)`](goal). -/
theorem uniform_order_mean {n : ℕ} (hn : 0 < n) (j : Fin n) :
    (∫ x, sortedSample n x j ∂iidSample uniform01 n) =
      ((j : ℕ) + 1 : ℝ) / (n + 1) := by
  have _ := hn
  classical
  let s := Finset.Iic j
  have hsorted (x : Fin n → ℝ) :
      sortedSample n x j = ∑ i ∈ s, firstNSpacings n x i := by
    simpa [s, prefixCoordinates, firstNSpacings_eq_orderedSpacings] using
      (congrFun (prefixCoordinates_orderedSpacings n (sortedSample n x)) j).symm
  have hsmeas : Measurable (fun z : Fin n → ℝ => ∑ i ∈ s, z i) := by
    fun_prop
  calc
    (∫ x, sortedSample n x j ∂iidSample uniform01 n) =
        ∫ z, (∑ i ∈ s, z i) ∂(iidSample uniform01 n).map (firstNSpacings n) := by
          rw [integral_map (firstNSpacings_aemeasurable_local n)
            hsmeas.aestronglyMeasurable]
          simp only [← hsorted]
    _ = (n.factorial : ℝ) *
        (∫ z, (∑ i ∈ s, z i) ∂volume.restrict (spacingSimplex n)) := by
          rw [uniform_firstN_spacings_law, integral_smul_measure]
          simp
    _ = ∑ i ∈ s, (1 : ℝ) / (n + 1) := by
          rw [integral_finsetSum _ (fun i _ => simplex_coordinate_integrable_local n i),
            Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => simplex_coordinate_first_moment n i)
    _ = ((j : ℕ) + 1 : ℝ) / (n + 1) := by
          simp [s, Fin.card_Iic, div_eq_mul_inv]

/-- For a [positive sample size](hyp:hn) and [zero-based sorted index](hyp:j),
 [the corresponding uniform order statistic has second moment `(j+1)(j+2)/((n+1)(n+2))`](goal). -/
theorem uniform_order_second_moment {n : ℕ} (hn : 0 < n) (j : Fin n) :
    (∫ x, (sortedSample n x j) ^ 2 ∂iidSample uniform01 n) =
      (((j : ℕ) + 1 : ℝ) * ((j : ℕ) + 2)) / ((n + 1) * (n + 2)) := by
  have _ := hn
  classical
  let s := Finset.Iic j
  let D : ℝ := (n + 1) * (n + 2)
  have hsorted (x : Fin n → ℝ) :
      sortedSample n x j = ∑ i ∈ s, firstNSpacings n x i := by
    simpa [s, prefixCoordinates, firstNSpacings_eq_orderedSpacings] using
      (congrFun (prefixCoordinates_orderedSpacings n (sortedSample n x)) j).symm
  have hsquare (z : Fin n → ℝ) :
      (∑ i ∈ s, z i) ^ 2 = ∑ i ∈ s, ∑ k ∈ s, z i * z k := by
    rw [pow_two, Finset.sum_mul_sum]
  have hmeas : Measurable (fun z : Fin n → ℝ =>
      ∑ i ∈ s, ∑ k ∈ s, z i * z k) := by fun_prop
  have hpair (i k : Fin n) :
      (n.factorial : ℝ) *
        (∫ z in spacingSimplex n, z i * z k ∂volume) =
          (if i = k then (2 : ℝ) else 1) / D := by
    by_cases hik : i = k
    · subst k
      simpa [D, pow_two] using simplex_coordinate_second_moment n i
    · simpa [hik, D] using simplex_coordinate_cross_moment n i k hik
  have hinter (i : Fin n) : Integrable
      (fun z : Fin n → ℝ => ∑ k ∈ s, z i * z k)
      (volume.restrict (spacingSimplex n)) := by
    exact integrable_finsetSum s (fun k _ => simplex_coordinate_product_integrable_local n i k)
  have hcount (i : Fin n) (hi : i ∈ s) :
      (∑ k ∈ s, (if i = k then (2 : ℝ) else 1) / D) =
        ((s.card : ℝ) + 1) / D := by
    have hnum : (∑ k ∈ s, if i = k then (2 : ℝ) else 1) =
        (s.card : ℝ) + 1 := by
      calc
        _ = ∑ k ∈ s, ((1 : ℝ) + if i = k then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro k hk
          split_ifs <;> norm_num
        _ = _ := by simp [Finset.sum_add_distrib, hi]
    rw [← Finset.sum_div]
    exact congrArg (· / D) hnum
  calc
    (∫ x, (sortedSample n x j) ^ 2 ∂iidSample uniform01 n) =
        ∫ z, (∑ i ∈ s, ∑ k ∈ s, z i * z k)
          ∂(iidSample uniform01 n).map (firstNSpacings n) := by
            rw [integral_map (firstNSpacings_aemeasurable_local n)
              hmeas.aestronglyMeasurable]
            simp only [← hsquare, ← hsorted]
    _ = (n.factorial : ℝ) *
        (∫ z, (∑ i ∈ s, ∑ k ∈ s, z i * z k)
          ∂volume.restrict (spacingSimplex n)) := by
            rw [uniform_firstN_spacings_law, integral_smul_measure]
            simp
    _ = ∑ i ∈ s, ∑ k ∈ s, (if i = k then (2 : ℝ) else 1) / D := by
          rw [integral_finsetSum _ (fun i _ => hinter i), Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_finsetSum _
            (fun k _ => simplex_coordinate_product_integrable_local n i k), Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => hpair i k)
    _ = ((s.card : ℝ) * ((s.card : ℝ) + 1)) / D := by
          rw [Finset.sum_congr rfl (fun i hi => hcount i hi)]
          simp [div_eq_mul_inv]
          ring
    _ = (((j : ℕ) + 1 : ℝ) * ((j : ℕ) + 2)) / ((n + 1) * (n + 2)) := by
          simp [s, D, Fin.card_Iic]
          ring

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant
