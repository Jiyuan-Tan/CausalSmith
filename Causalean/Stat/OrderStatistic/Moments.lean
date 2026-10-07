module
public import Causalean.Stat.OrderStatistic.SimplexIntegrals

/-!
# Exact moments of uniform order-statistic spacings

The adjacent interior gaps of an iid unit-uniform sample have a common exact
second moment. Summing every other gap gives the finite even-sample identity.
-/

public section

namespace Causalean.Stat.OrderStatistic

open MeasureTheory

noncomputable section

/-- Given [a finite dimension](hyp:n) and [a coordinate index](hyp:i), [the factorial-scaled second moment of that simplex coordinate has the stated exact value](goal). -/
theorem simplex_coordinate_second_moment (n : ℕ) (i : Fin n) :
    (n.factorial : ℝ) * (∫ z in spacingSimplex n, (z i) ^ 2 ∂volume) =
      (2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ)) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
      rw [simplex_coordinate_square_eq_first]
      change (m + 1).factorial *
        (∫ z in spacingSimplex (m + 1), (z (0 : Fin (m + 1))) ^ 2 ∂volume) = _
      rw [simplex_first_coordinate_square_slice]
      have hfactorial : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
      simp_rw [← mul_div_assoc]
      rw [intervalIntegral.integral_div]
      rw [unit_beta_square_integral]
      norm_num [hfactorial, Nat.factorial_succ]
      have hm : (m.factorial : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- The finite spacing map is almost everywhere measurable under the iid uniform law. -/
private theorem firstNSpacings_aemeasurable (n : ℕ) :
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
  convert hspacing.aemeasurable.comp_aemeasurable hsort' using 1
  funext x
  exact firstNSpacings_eq_orderedSpacings n x

/-- Given [a finite sample size](hyp:n), [an adjacent-gap index](hyp:k), and [proof that the gap is interior](hyp:hk), [the squared sorted unit-uniform gap has the stated exact second moment](goal). -/
theorem uniform_gap_second_moment (n k : ℕ) (hk : k + 1 < n) :
    ∫ x, (sortedGap n k x) ^ 2 ∂iidSample uniform01 n =
      (2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ)) := by
  have hfirst := firstNSpacings_aemeasurable n
  let i : Fin n := ⟨k + 1, hk⟩
  have hgap (x : Fin n → ℝ) : sortedGap n k x = firstNSpacings n x i := by
    simp [sortedGap, firstNSpacings, i, hk]
  calc
    (∫ x, (sortedGap n k x) ^ 2 ∂iidSample uniform01 n) =
        ∫ z, (z i) ^ 2 ∂(iidSample uniform01 n).map (firstNSpacings n) := by
          rw [integral_map hfirst ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable]
          simp only [hgap]
    _ = (n.factorial : ℝ) *
        (∫ z in spacingSimplex n, (z i) ^ 2 ∂volume) := by
          rw [uniform_firstN_spacings_law, integral_smul_measure]
          simp
    _ = _ := simplex_coordinate_second_moment n i

/-- Given [a finite sample size](hyp:n), [an adjacent-gap index](hyp:k), and [proof that the gap is interior](hyp:hk), [the squared sorted unit-uniform gap is integrable](goal). -/
theorem uniform_gap_square_integrable (n k : ℕ) (hk : k + 1 < n) :
    Integrable (fun x => (sortedGap n k x) ^ 2) (iidSample uniform01 n) := by
  let i : Fin n := ⟨k + 1, hk⟩
  have hgap (x : Fin n → ℝ) : sortedGap n k x = firstNSpacings n x i := by
    simp [sortedGap, firstNSpacings, i, hk]
  have hmeas : AEStronglyMeasurable
      (fun x => (sortedGap n k x) ^ 2) (iidSample uniform01 n) := by
    have h := ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable.comp_aemeasurable
      (firstNSpacings_aemeasurable n)
    convert h using 1
    funext x
    simp [hgap]
  have hfinite : (iidSample uniform01 n) Set.univ ≠ ⊤ := by
    have : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
    simp [iidSample]
  have hcube : MeasurableSet (unitCube n) := by
    change MeasurableSet {x : Fin n → ℝ | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}
    have heq : {x : Fin n → ℝ | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1} =
        ⋂ i : Fin n, (fun x : Fin n → ℝ => x i) ⁻¹' Set.Icc 0 1 := by
      ext x
      simp
    rw [heq]
    exact MeasurableSet.iInter (fun i => measurableSet_Icc.preimage (measurable_pi_apply i))
  have hbound : ∀ᵐ x ∂iidSample uniform01 n,
      ‖(sortedGap n k x) ^ 2‖ ≤ (1 : ℝ) := by
    rw [iid_uniform_cube_law]
    apply ae_restrict_of_forall_mem hcube
    intro x hx
    have hmono : Monotone (sortedSample n x) := Tuple.monotone_sort x
    have h0 : 0 ≤ sortedSample n x ⟨k, by omega⟩ :=
      (hx (Tuple.sort x ⟨k, by omega⟩)).1
    have h1 : sortedSample n x i ≤ 1 := (hx (Tuple.sort x i)).2
    have hle : sortedSample n x ⟨k, by omega⟩ ≤ sortedSample n x i :=
      hmono (by simp [i, Fin.le_def])
    have hgap' : sortedGap n k x =
        sortedSample n x i - sortedSample n x ⟨k, by omega⟩ := by
      simp [sortedGap, hk, i]
    have hb : 0 ≤ sortedGap n k x ∧ sortedGap n k x ≤ 1 := by
      rw [hgap']
      constructor <;> linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  exact integrableOn_univ.mp
    (Measure.integrableOn_of_bounded hfinite hmeas
      (by simpa only [Measure.restrict_univ] using hbound) :
      IntegrableOn (fun x => (sortedGap n k x) ^ 2) Set.univ (iidSample uniform01 n))

/-- Given [a finite sample size](hyp:n) and [proof that it is even](hyp:hn), [the expected sum of squares of every other sorted gap of an iid unit-uniform sample (the gaps between the order statistics of ranks `2j+1` and `2j+2`, over all `n/2` such pairs) equals `n/((n+1)(n+2))`](goal). -/
theorem uniform_alternating_gap_second_moment (n : ℕ) (hn : Even n) :
    ∫ x, (∑ j ∈ Finset.range (n / 2), (sortedGap n (2 * j) x) ^ 2)
        ∂iidSample uniform01 n =
      (n : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ)) := by
  have heven : 2 * (n / 2) = n := by
    rcases hn with ⟨m, hm⟩
    omega
  have hindex (j : ℕ) (hj : j ∈ Finset.range (n / 2)) : 2 * j + 1 < n := by
    simp only [Finset.mem_range] at hj
    omega
  rw [integral_finsetSum (Finset.range (n / 2)) (fun j hj =>
    uniform_gap_square_integrable n (2 * j) (hindex j hj))]
  have hsum :
      (∑ j ∈ Finset.range (n / 2),
        ∫ x, (sortedGap n (2 * j) x) ^ 2 ∂iidSample uniform01 n) =
      ∑ _j ∈ Finset.range (n / 2),
        (2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact uniform_gap_second_moment n (2 * j) (hindex j hj)
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hreal : (2 : ℝ) * (n / 2 : ℕ) = n := by exact_mod_cast heven
  have hden : ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

end
end Causalean.Stat.OrderStatistic
