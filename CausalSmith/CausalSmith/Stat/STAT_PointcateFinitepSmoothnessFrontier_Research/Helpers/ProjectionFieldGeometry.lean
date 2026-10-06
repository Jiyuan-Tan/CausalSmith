module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.Kernels

/-! Orthogonal energy assembly for the multiscale projection field. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- The square integral of a finite orthogonal family is the sum of its energies. -/
-- @node: integral_sq_orthogonal_sum
lemma integral_sq_orthogonal_sum {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (∫ x, f i x * f j x ∂μ) = 0) :
    (∫ x, (∑ i ∈ s, f i x)^2 ∂μ) = ∑ i ∈ s, ∫ x, (f i x)^2 ∂μ := by
  classical
  have hi (i) (h : i ∈ s) := (hf i h).integrable_sq
  have hij (i) (h : i ∈ s) (j) (h' : j ∈ s) :
      Integrable (fun x => f i x * f j x) μ := (hf i h).integrable_mul (hf j h')
  calc
    _ = ∫ x, ∑ i ∈ s, ∑ j ∈ s, f i x * f j x ∂μ := by
      congr 1
      funext x
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ x, f i x * f j x ∂μ := by
      rw [integral_finset_sum s (fun i h =>
        integrable_finset_sum s (fun j h' => hij i h j h'))]
      apply Finset.sum_congr rfl
      intro i h
      exact integral_finset_sum s (fun j h' => hij i h j h')
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i h
      rw [Finset.sum_eq_single i]
      · simp only [pow_two]
      · intro j h' hji
        exact ho i h j h' hji.symm
      · exact fun hn => (hn h).elim

/-- Arbitrary square-integrable inputs at different levels still have orthogonal projected bands. -/
-- @node: projectionField_energy
lemma projectionField_energy (law : ObservedLaw) (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (J : ℕ) (T : Fin (J+1) → ℝ)
    (hf : ∀ j, MemLp (truncatedMean law (T j)) 2 (design.restrict (window h))) :
    (∫ x in window h, (projectionField law h J T x)^2 ∂design) =
      (∫ x in window h, (projOp h 0 (truncatedMean law (T 0)) x)^2 ∂design) +
      ∑ j : Fin J, ∫ x in window h, (bandOp h (j.val+1) (truncatedMean law (T j.succ)) x)^2 ∂design := by
  classical
  let f : Fin (J+1) → unitInterval → ℝ := fun j =>
    if j.val = 0 then projOp h 0 (truncatedMean law (T j))
    else bandOp h j.val (truncatedMean law (T j))
  have hmem (j) : MemLp (f j) 2 (design.restrict (window h)) := by
    dsimp [f]; split_ifs
    · exact projOp_memLp h 0 _
    · exact bandOp_memLp h _ _ (hf j)
  have ho (i j : Fin (J+1)) (hne : i ≠ j) :
      (∫ x in window h, f i x * f j x ∂design) = 0 := by
    have hv : i.val ≠ j.val := fun he => hne (Fin.ext he)
    by_cases hi : i.val = 0
    · have hj : j.val ≠ 0 := by omega
      simp only [f, if_pos hi, if_neg hj]
      exact projOp_zero_bandOp_orthogonal h hh _ _ _ (hf j)
    · by_cases hj : j.val = 0
      · simp only [f, if_neg hi, if_pos hj]
        simp_rw [mul_comm (bandOp h i.val _ _)]
        exact projOp_zero_bandOp_orthogonal h hh _ _ _ (hf i)
      · simp only [f, if_neg hi, if_neg hj]
        exact bandOp_distinct_orthogonal h hh _ _ (by omega) (by omega) hv _ _ (hf i) (hf j)
  have he := integral_sq_orthogonal_sum (design.restrict (window h)) Finset.univ f
    (fun j _ => hmem j) (fun i _ j _ hn => ho i j hn)
  have hs (x) : (∑ j, f j x) = projectionField law h J T x := by
    rw [Fin.sum_univ_succ]
    simp [f, projectionField]
  simp_rw [hs] at he
  rw [he, Fin.sum_univ_succ]
  simp [f]

/-- A single positive-level band contracts squared energy. -/
-- @node: bandOp_energy_contraction
lemma bandOp_energy_contraction (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h))) :
    (∫ x in window h, (bandOp h (j+1) f x)^2 ∂design) ≤
      ∫ x in window h, (f x)^2 ∂design := by
  rw [bandOp_energy_increment h hh j f hf]
  exact (sub_le_self _ (integral_nonneg fun x => sq_nonneg _)).trans
    (projOp_energy_contraction h hh (j+1) f hf)

/-- Splitting a band into its common mean and its truncation error costs at most a factor two. -/
-- @node: bandOp_energy_split
lemma bandOp_energy_split (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f g : unitInterval → ℝ)
    (hf : MemLp f 2 (design.restrict (window h)))
    (hg : MemLp g 2 (design.restrict (window h))) :
    (∫ x in window h, (bandOp h (j+1) f x)^2 ∂design) ≤
      2 * (∫ x in window h, (bandOp h (j+1) g x)^2 ∂design) +
      2 * (∫ x in window h, (f x-g x)^2 ∂design) := by
  have he (x) : bandOp h (j+1) (f-g) x =
      bandOp h (j+1) f x - bandOp h (j+1) g x := by
    rw [bandOp_eq_sub h _ _ (hf.sub hg)]
    change projOp h (j+1) (fun z => f z-g z) x - projOp h (j+1-1) (fun z => f z-g z) x = _
    rw [projOp_sub h _ _ _ hf hg, projOp_sub h _ _ _ hf hg,
      bandOp_eq_sub h _ _ hf, bandOp_eq_sub h _ _ hg]
    ring
  have hb := bandOp_memLp h (j+1) f hf
  have hc := bandOp_memLp h (j+1) g hg
  have hd := bandOp_memLp h (j+1) _ (hf.sub hg)
  have hi : Integrable (fun x => (bandOp h (j+1) g x)^2) (design.restrict (window h)) := hc.integrable_sq
  have hi' : Integrable (fun x => (bandOp h (j+1) (f-g) x)^2) (design.restrict (window h)) := hd.integrable_sq
  calc
    _ ≤ ∫ x in window h, 2*(bandOp h (j+1) g x)^2 +
        2*(bandOp h (j+1) (f-g) x)^2 ∂design := by
      apply integral_mono hb.integrable_sq
        ((hc.integrable_sq.const_mul 2).add (hd.integrable_sq.const_mul 2))
      intro x
      dsimp only [Pi.add_apply]
      rw [he]
      nlinarith [sq_nonneg (bandOp h (j+1) f x - 2*bandOp h (j+1) g x)]
    _ = 2*(∫ x in window h, (bandOp h (j+1) g x)^2 ∂design) +
        2*(∫ x in window h, (bandOp h (j+1) (f-g) x)^2 ∂design) := by
      integral_linearity
    _ ≤ _ := by
      simpa only [Pi.sub_apply] using add_le_add (le_refl (2 * (∫ x in window h, (bandOp h (j+1) g x)^2 ∂design)))
        (mul_le_mul_of_nonneg_left (bandOp_energy_contraction h hh j (f-g) (hf.sub hg)) (by norm_num : (0 : ℝ) ≤ 2))

/-- A common-threshold prefix telescopes exactly at the energy level. -/
-- @node: projection_energy_prefix
lemma projection_energy_prefix (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (F : ℕ → unitInterval → ℝ) (hf : ∀ j, MemLp (F j) 2 (design.restrict (window h)))
    (j0 J : ℕ) (hj0 : j0 ≤ J) (hcap : ∀ j, j ≤ j0 → F j = F 0) :
    (∫ x in window h, (projOp h 0 (F 0) x)^2 ∂design) +
      (∑ j ∈ Finset.range J, ∫ x in window h, (bandOp h (j+1) (F (j+1)) x)^2 ∂design) =
    (∫ x in window h, (projOp h j0 (F 0) x)^2 ∂design) +
      ∑ j ∈ Finset.range J, if j0 < j+1 then
        (∫ x in window h, (bandOp h (j+1) (F (j+1)) x)^2 ∂design) else 0 := by
  have hbase :
      (∫ x in window h, (projOp h 0 (F 0) x)^2 ∂design) +
        (∑ j ∈ Finset.range j0, ∫ x in window h, (bandOp h (j+1) (F (j+1)) x)^2 ∂design) =
      ∫ x in window h, (projOp h j0 (F 0) x)^2 ∂design := by
    have he : (∑ j ∈ Finset.range j0, ∫ x in window h, (bandOp h (j+1) (F (j+1)) x)^2 ∂design) =
        ∑ j ∈ Finset.range j0, ∫ x in window h, (bandOp h (j+1) (F 0) x)^2 ∂design := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcap (j+1) (by have := Finset.mem_range.mp hj; omega)]
    rw [he, bandOp_energy_telescope h j0 hh (F 0) (hf 0)]
    ring
  induction J, hj0 using Nat.le_induction with
  | base =>
    rw [hbase]
    have hz : (∑ j ∈ Finset.range j0, if j0 < j+1 then
        (∫ x in window h, (bandOp h (j+1) (F (j+1)) x)^2 ∂design) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg (by have := Finset.mem_range.mp hj; omega)]
    rw [hz, add_zero]
  | succ J hJ ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, if_pos (by omega)]
    linarith

/-- Orthogonality, prefix telescoping, and contraction bound the field by the original mean
and the individual errors after the common-threshold prefix. -/
-- @node: projection_energy_error_bound
lemma projection_energy_error_bound (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (F : ℕ → unitInterval → ℝ) (hf : ∀ j, MemLp (F j) 2 (design.restrict (window h)))
    (g : unitInterval → ℝ) (hg : MemLp g 2 (design.restrict (window h)))
    (j0 J : ℕ) (hj0 : j0 ≤ J) (hcap : ∀ j, j ≤ j0 → F j = F 0) :
    (∫ x in window h, (projOp h 0 (F 0) x)^2 ∂design) +
      (∑ j ∈ Finset.range J, ∫ x in window h, (bandOp h (j+1) (F (j+1)) x)^2 ∂design) ≤
    (∫ x in window h, (F 0 x)^2 ∂design) + 2*(∫ x in window h, (g x)^2 ∂design) +
      2*∑ j ∈ Finset.range J, if j0 < j+1 then (∫ x in window h, (F (j+1) x-g x)^2 ∂design) else 0 := by
  rw [projection_energy_prefix h hh F hf j0 J hj0 hcap]
  have hs : (∑ j ∈ Finset.range J, if j0 < j+1 then
      (∫ x in window h, (bandOp h (j+1) (F (j+1)) x)^2 ∂design) else 0) ≤
      ∑ j ∈ Finset.range J, (2*(∫ x in window h, (bandOp h (j+1) g x)^2 ∂design) +
        2*(if j0 < j+1 then (∫ x in window h, (F (j+1) x-g x)^2 ∂design) else 0)) := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact bandOp_energy_split h hh j _ g (hf _) hg
    · have hn : 0 ≤ ∫ x in window h, (bandOp h (j+1) g x)^2 ∂design := integral_nonneg fun x => sq_nonneg _
      linarith
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hp := projOp_energy_contraction h hh j0 (F 0) (hf 0)
  have hb := bandOp_energy_sum_le h J hh g hg
  linarith

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
