module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.MomentDependence.WalshExpansion

/-!
# Helpers/MomentDependence/Covariance

Finite original-record private value frontiers: Helpers/MomentDependence/Covariance.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n m d : ℕ}
/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the stated hjj condition](hyp:hjj). [Affine statistics of distinct coordinates attain the one-row correlation bound exactly](goal). -/
-- @node: blockCov_affine_scaled_abs
lemma blockCov_affine_scaled_abs (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (i : Fin m) (j j' : Fin d) (hjj : j ≠ j') (a c a' c' : ℝ) :
    |blockCov P eps (fun z => a + c * scaledMessages eps z i j)
      (fun z => a' + c' * scaledMessages eps z i j')| =
      |contrast P j * contrast P j'| /
        Real.sqrt (((noiseScale d eps)^2 - (contrast P j)^2) *
          ((noiseScale d eps)^2 - (contrast P j')^2)) *
        Real.sqrt (blockVar P eps (fun z => a + c * scaledMessages eps z i j) *
          blockVar P eps (fun z => a' + c' * scaledMessages eps z i j')) := by
  rw [blockCov_affine_scaled P hP eps heps hd i j j' hjj,
    blockVar_affine_scaled P hP eps heps hd,
    blockVar_affine_scaled P hP eps heps hd]
  let v := (noiseScale d eps)^2 - (contrast P j)^2
  let v' := (noiseScale d eps)^2 - (contrast P j')^2
  have hv : 0 < v := column_scale_variance_pos P hP eps heps hd j
  have hv' : 0 < v' := column_scale_variance_pos P hP eps heps hd j'
  have hroot : Real.sqrt (v*v') ≠ 0 := (Real.sqrt_pos.2 (mul_pos hv hv')).ne'
  change |-(c*c'*contrast P j*contrast P j')| =
    |contrast P j * contrast P j'| / Real.sqrt (v*v') * Real.sqrt ((c^2*v)*(c'^2*v'))
  have hprod : (c^2*v)*(c'^2*v') = (c*c')^2*(v*v') := by ring
  rw [hprod, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rw [abs_neg]
  have habs : |c*c'*contrast P j*contrast P j'| =
      |c*c'| * |contrast P j*contrast P j'| := by simp only [abs_mul, mul_assoc]
  rw [habs]
  field_simp

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the stated hjj condition](hyp:hjj). [The full arbitrary-column covariance inequality for a block containing one participant](goal). -/
-- @node: column_covariance_bound_one
lemma column_covariance_bound_one (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (g : Fin d → (Fin 1 → ℝ) → ℝ) (j j' : Fin d) (hjj : j ≠ j') :
    |blockCov P eps (columnStatistic eps g j) (columnStatistic eps g j')| ≤
      |contrast P j * contrast P j'| /
        Real.sqrt (((noiseScale d eps)^2 - (contrast P j)^2) *
          ((noiseScale d eps)^2 - (contrast P j')^2)) *
        Real.sqrt (blockVar P eps (columnStatistic eps g j) *
          blockVar P eps (columnStatistic eps g j')) := by
  have hb : noiseScale d eps ≠ 0 := by
    have hb := noiseScale_gt_dimension (d := d) eps heps (by omega)
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨a,c,h⟩ := columnStatistic_one_affine eps hb g j
  obtain ⟨a',c',h'⟩ := columnStatistic_one_affine eps hb g j'
  rw [h,h']
  exact (blockCov_affine_scaled_abs P hP eps heps hd 0 j j' hjj a c a' c').le

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [A dimension bound on the exact cross-column correlation coefficient](goal). -/
-- @node: column_correlation_le_inv_dimension
lemma column_correlation_le_inv_dimension (P : Measure (FullRecord d))
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (j j' : Fin d) :
    |contrast P j * contrast P j'| /
      Real.sqrt (((noiseScale d eps)^2 - (contrast P j)^2) *
        ((noiseScale d eps)^2 - (contrast P j')^2)) ≤ (d : ℝ)⁻¹ := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb := noiseScale_gt_dimension (d := d) eps heps (by omega)
  have ht (l : Fin d) : |contrast P l| ≤ (1/2 : ℝ) :=
    abs_le.mpr (contrast_mem_parameterCube P hP l)
  have hs (l : Fin d) : (contrast P l)^2 ≤ (1/4 : ℝ) := by
    have := ht l
    have := sq_abs (contrast P l)
    nlinarith [mul_nonneg (abs_nonneg (contrast P l)) (by linarith : 0 ≤ 1/2 - |contrast P l|)]
  have hden (l : Fin d) : (d : ℝ) ≤ (noiseScale d eps)^2 - (contrast P l)^2 := by
    have := hs l
    nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hprod : (d : ℝ)^2 ≤
      ((noiseScale d eps)^2 - (contrast P j)^2) *
        ((noiseScale d eps)^2 - (contrast P j')^2) := by
    simpa [pow_two] using mul_le_mul (hden j) (hden j') (by linarith) (by linarith [hden j])
  have hroot : (d : ℝ) ≤ Real.sqrt
      (((noiseScale d eps)^2 - (contrast P j)^2) *
        ((noiseScale d eps)^2 - (contrast P j')^2)) := by
    have := Real.sqrt_le_sqrt hprod
    simpa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ d)] using this
  have hnum : |contrast P j * contrast P j'| ≤ (1 : ℝ) := by
    rw [abs_mul]
    have := mul_le_mul (ht j) (ht j') (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/2)
    norm_num at this
    linarith
  calc
    _ ≤ 1 / (d : ℝ) := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1) hnum (by linarith) hroot
    _ = _ := one_div _

/-- Assume [positive dimension](hyp:hd) and [the function hcov](hyp:hcov). [Summing diagonal variances and bounded cross-column covariances gives the paper's factor-two bound for the average. This step does not assume independent columns](goal). -/
-- @node: blockVar_average_le_of_covariance
lemma blockVar_average_le_of_covariance (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (eps : ℝ) (hd : 0 < d)
    (f : Fin d → (Fin m → Fin d → Bool) → ℝ)
    (hcov : ∀ j j', j ≠ j' → |blockCov P eps (f j) (f j')| ≤
      (d : ℝ)⁻¹ * Real.sqrt (blockVar P eps (f j) * blockVar P eps (f j'))) :
    blockVar P eps (fun z => (d : ℝ)⁻¹ * ∑ j, f j z) ≤
      (2/(d : ℝ)) * sSup (Set.range (fun j => blockVar P eps (f j))) := by
  classical
  let v := sSup (Set.range (fun j => blockVar P eps (f j)))
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hvar (j : Fin d) : 0 ≤ blockVar P eps (f j) := by
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hvj (j : Fin d) : blockVar P eps (f j) ≤ v :=
    le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self j)
  have hv : 0 ≤ v := (hvar ⟨0,hd⟩).trans (hvj ⟨0,hd⟩)
  have hsqrt (j j' : Fin d) :
      Real.sqrt (blockVar P eps (f j) * blockVar P eps (f j')) ≤ v := by
    have h := Real.sqrt_le_sqrt (mul_le_mul (hvj j) (hvj j') (hvar j') hv)
    simpa [← pow_two, Real.sqrt_sq hv] using h
  have hrow (j : Fin d) : ∑ j', blockCov P eps (f j) (f j') ≤ 2*v := by
    calc
      _ ≤ ∑ j' : Fin d, ((if j' = j then v else 0) + (d : ℝ)⁻¹*v) := by
        apply Finset.sum_le_sum
        intro j' _
        by_cases heq : j' = j
        · subst j'
          rw [blockCov_self]
          simp only [if_true]
          nlinarith [hvj j, mul_nonneg (inv_nonneg.mpr hdR.le) hv]
        · simp only [heq, if_false, zero_add]
          exact (le_abs_self _).trans ((hcov j j' (Ne.symm heq)).trans
            (mul_le_mul_of_nonneg_left (hsqrt j j') (inv_nonneg.mpr hdR.le)))
      _ = 2*v := by
        rw [Finset.sum_add_distrib]
        simp [hdR.ne', ← mul_assoc]
        ring
  rw [blockVar_average_eq_covariance_sum]
  calc
    _ ≤ ((d : ℝ)⁻¹)^2 * ∑ j : Fin d, 2*v :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hrow j)) (sq_nonneg _)
    _ = (2/(d : ℝ))*v := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a privacy budget in the interval from zero to one](hyp:heps), [dimension at least two](hyp:hd), and [measurability of g](hyp:hg). [The remaining finite Walsh-basis calculation controls arbitrary column statistics. This is the dependence step in the paper's private-moment proof roadmap](goal). -/
-- @node: column_covariance_bound
lemma column_covariance_bound (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : eps ∈ Set.Ioc 0 1)
    (hd : 2 ≤ d) (g : Fin d → (Fin m → ℝ) → ℝ) (hg : ∀ j, Measurable (g j)) :
    ∀ j j' : Fin d, j ≠ j' →
      |blockCov (m := m) P eps (columnStatistic eps g j) (columnStatistic eps g j')| ≤
        |contrast P j * contrast P j'| /
          Real.sqrt (((noiseScale d eps)^2 - (contrast P j)^2) *
            ((noiseScale d eps)^2 - (contrast P j')^2)) *
          Real.sqrt (blockVar (m := m) P eps (columnStatistic eps g j) *
            blockVar (m := m) P eps (columnStatistic eps g j')) := by
  classical
  intro j j' hjj
  obtain ⟨c, hc0, hc⟩ := columnStatistic_centered_walsh_expansion P hP eps heps.1 hd g j
  obtain ⟨c', hc0', hc'⟩ := columnStatistic_centered_walsh_expansion P hP eps heps.1 hd g j'
  let r := -(contrast P j * contrast P j') /
    Real.sqrt (((noiseScale d eps)^2 - (contrast P j)^2) *
      ((noiseScale d eps)^2 - (contrast P j')^2))
  have hrabs : |r| = |contrast P j * contrast P j'| /
      Real.sqrt (((noiseScale d eps)^2 - (contrast P j)^2) *
        ((noiseScale d eps)^2 - (contrast P j')^2)) := by
    simp only [r, abs_div, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hr : |r| ≤ 1 := by
    rw [hrabs]
    have hdim := column_correlation_le_inv_dimension P hP eps heps.1 hd j j'
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hinv : (d : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by linarith : (0 : ℝ) < d)]
      linarith
    exact hdim.trans hinv
  rw [blockCov_walsh_expansion P hP eps heps.1 hd j j' hjj _ _ c c' hc hc',
    blockVar_walsh_expansion P hP eps heps.1 hd j _ c hc,
    blockVar_walsh_expansion P hP eps heps.1 hd j' _ c' hc']
  exact (walsh_diagonal_sum_abs_le c c' hc0 r hr).trans_eq (by rw [hrabs])

-- @node: lem:private-moment-and-dependence
/-- For [iid sampling](hyp:hIID), a [causal population law](hyp:hP), [privacy in the calibrated
range](hyp:heps), [at least two cells](hyp:hd), and a [positive block size bounded by the sample
size](hyp:hm,hmn), the vector channel satisfies [privacy, its moment identities, and both
column-dependence bounds](goal). -/
lemma private_moment_and_dependence (S : SamplingScheme n d) (hIID : IidPeople S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : eps ∈ Set.Ioc 0 1) (hd : 2 ≤ d) (hm : 0 < m) (hmn : m ≤ n) :
    NoninteractiveClass (vectorProtocol n d eps) eps ∧
    (∀ (i : Fin m) (j : Fin d),
      blockMean (m := m) P eps (fun z => scaledMessages eps z i j) = contrast P j ∧
      blockMean (m := m) P eps (fun z => (scaledMessages eps z i j)^2) = (noiseScale d eps)^2) ∧
    (∀ (i : Fin m) (j j' : Fin d), j ≠ j' →
      blockMean (m := m) P eps (fun z => scaledMessages eps z i j * scaledMessages eps z i j')
        = 0) ∧
    (∀ k : ℕ, k ≤ m → ∀ j : Fin d,
      blockMean (m := m) P eps (fun z => privateMoment (scaledMessages eps z) k j) = (contrast
        P j)^k) ∧
    (∀ k : ℕ, 2*k ≤ m → ∀ j : Fin d,
      blockMean (m := m) P eps (fun z => (privateMoment (scaledMessages eps z) k j)^2) ≤
        ((contrast P j)^2 + 2*k*(noiseScale d eps)^2/m)^k) ∧
    (∀ g : Fin d → (Fin m → ℝ) → ℝ, (∀ j, Measurable (g j)) →
      (∀ j j' : Fin d, j ≠ j' → -- @realizes j'(second cell index)
        |blockCov (m := m) P eps (columnStatistic eps g j) (columnStatistic eps g j')| ≤
          |contrast P j * contrast P j'| /
            Real.sqrt (((noiseScale d eps)^2 - (contrast P j)^2) *
              ((noiseScale d eps)^2 - (contrast P j')^2)) *
            Real.sqrt (blockVar (m := m) P eps (columnStatistic eps g j) *
              blockVar (m := m) P eps (columnStatistic eps g j'))) ∧
      blockVar (m := m) P eps (fun z => (d : ℝ)⁻¹ * ∑ j, columnStatistic eps g j z) ≤
        (2/(d : ℝ)) * sSup (Set.range (fun j => blockVar (m := m) P eps (columnStatistic eps g
          j)))) := by
  obtain ⟨hNI, hfirst, hcross, hpower, hsecond⟩ :=
    vector_private_moments S hIID P hP eps heps hd hm hmn
  refine ⟨hNI, hfirst, hcross, hpower, hsecond, ?_⟩
  intro g hg
  have hpair := column_covariance_bound (m := m) P hP eps heps hd g hg
  refine ⟨hpair, ?_⟩
  apply blockVar_average_le_of_covariance P eps (by omega) (columnStatistic eps g)
  intro j j' hjj
  exact (hpair j j' hjj).trans (mul_le_mul_of_nonneg_right
    (column_correlation_le_inv_dimension P hP eps heps.1 hd j j')
    (Real.sqrt_nonneg _))


end CausalSmith.Stat.LdpOptvalueUniformFrontier
