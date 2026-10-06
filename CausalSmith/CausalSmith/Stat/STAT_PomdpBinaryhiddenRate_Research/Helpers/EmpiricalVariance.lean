module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.EmpiricalMoments

/-!
# Finite lag summation for the seven empirical moments

Short lags cost at most six score second moments per epoch; separated lags
are summed through the geometric mixing tail. This proves equations (8) and (9).
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- For a finite collection of nonnegative powers whose distinct exponents all lie below a horizon, the selected power sum is at most the complete geometric sum up to that horizon. [Under the listed formal conditions](hyp:hr,hf,hinj), [the stated conclusion holds](goal).
-/
-- @node: binary_sum_pow_image_le_range
lemma binary_sum_pow_image_le_range {ι : Type*}
    (s : Finset ι) (f : ι → Nat) (n : Nat) (r : ℝ)
    (hr : 0 ≤ r) (hf : ∀ i ∈ s, f i < n) (hinj : Set.InjOn f ↑s) :
    ∑ i ∈ s, r ^ f i ≤ ∑ j ∈ Finset.range n, r ^ j := by
  classical
  rw [← Finset.sum_image hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hf i hi)
  · intro j _ _
    positivity

/-- A finite geometric sum with a nonnegative ratio strictly below one is bounded by the reciprocal of one minus that ratio. [Under the listed formal conditions](hyp:ha0,ha1), [the stated conclusion holds](goal).
-/
-- @node: binary_geom_partial_le_inv
lemma binary_geom_partial_le_inv {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (n : Nat) :
    ∑ j ∈ Finset.range n, a ^ j ≤ 1 / (1 - a) := by
  calc
    ∑ j ∈ Finset.range n, a ^ j ≤ ∑' j : Nat, a ^ j := by
      apply Summable.sum_le_tsum
      · intro j _
        positivity
      · exact summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs, abs_of_nonneg ha0])
    _ = 1 / (1 - a) := by rw [tsum_geometric_of_lt_one ha0 ha1]; ring

/-- For a symmetric pairwise quantity on a finite ordered sample, the sum of its absolute values equals the diagonal contribution plus twice the strictly upper-triangular contribution. [Under the listed formal conditions](hyp:hsymm), [the stated conclusion holds](goal).
-/
-- @node: binary_sum_abs_symmetric_eq_diag_add_two_upper
lemma binary_sum_abs_symmetric_eq_diag_add_two_upper
    {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (f : ι → ι → ℝ) (hsymm : ∀ i j, |f i j| = |f j i|) :
    ∑ i ∈ s, ∑ j ∈ s, |f i j| =
      ∑ i ∈ s, |f i i| + 2 * ∑ i ∈ s, ∑ j ∈ s.filter (i < ·), |f i j| := by
  classical
  have hsplit (i : ι) (hi : i ∈ s) :
      ∑ j ∈ s, |f i j| = |f i i| +
        ∑ j ∈ s.filter (fun j ↦ j < i), |f i j| +
          ∑ j ∈ s.filter (fun j ↦ i < j), |f i j| := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun j ↦ j < i)]
    simp only [not_lt]
    rw [← Finset.sum_filter_add_sum_filter_not (s.filter fun j ↦ i ≤ j) (fun j ↦ i = j)]
    simp only [Finset.filter_filter]
    have heq : s.filter (fun j ↦ i ≤ j ∧ i = j) = {i} := by
      ext j
      constructor
      · intro hj
        obtain ⟨_, _, hji⟩ := Finset.mem_filter.mp hj
        simpa using hji.symm
      · intro hj
        have hji : j = i := by simpa using hj
        subst j
        exact Finset.mem_filter.mpr ⟨hi, le_rfl, rfl⟩
    have hgt : s.filter (fun j ↦ i ≤ j ∧ ¬i = j) = s.filter (fun j ↦ i < j) := by
      ext j
      simp [lt_iff_le_and_ne]
    rw [heq, hgt]
    simp
    ring
  rw [Finset.sum_congr rfl (fun i hi ↦ hsplit i hi), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hpast :
      ∑ i ∈ s, ∑ j ∈ s.filter (fun j ↦ j < i), |f i j| =
        ∑ i ∈ s, ∑ j ∈ s.filter (fun j ↦ i < j), |f i j| := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : i < j
    · simp [h, hsymm]
    · simp [h]
  rw [hpast]
  ring

/-- The sum over future retained scores has at most k short lags and a
geometrically summable separated tail. [Under the listed formal conditions](hyp:hM,htk), [the stated conclusion holds](goal).-/
-- @node: binary_sum_abs_covariance_future_le
lemma binary_sum_abs_covariance_future_le {T : Nat} {t0 zeta : ℝ}
    (M : RawPomdpExperiment T 2 2) (hM : BinaryPomdpClass t0 zeta M)
    (k : Fin 7) (t : Fin T) (htk : k.val ≤ t.val) :
    ∑ u ∈ (Finset.univ.filter (fun u : Fin T => 6 ≤ u.val)).filter (fun u => t < u),
      |covariance (fun w => score k.val M.b M.e w t)
        (fun w => score k.val M.b M.e w u) (obsLaw M)| ≤
      k.val * policyFactor zeta ^ (k.val + 1) + 1 / (1 - mixingAlpha t0) := by
  classical
  let I := Finset.univ.filter (fun u : Fin T => 6 ≤ u.val)
  let U := I.filter (fun u => t < u)
  let A := U.filter (fun u => u.val - t.val ≤ k.val)
  let D := U.filter (fun u => k.val + 1 ≤ u.val - t.val)
  have hpart : U = A ∪ D := by
    ext u
    simp only [U, A, D, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      by_cases hlag : u.val - t.val ≤ k.val
      · exact Or.inl ⟨hu, hlag⟩
      · exact Or.inr ⟨hu, by omega⟩
    · rintro (hu | hu) <;> exact hu.1
  have hdisj : Disjoint A D := by
    rw [Finset.disjoint_left]
    intro u huA huD
    simp only [A, D, Finset.mem_filter] at huA huD
    omega
  change (∑ u ∈ U, _) ≤ _
  rw [hpart, Finset.sum_union hdisj]
  have hAcard : (A.card : ℝ) ≤ k.val := by
    have hb := binary_sum_pow_image_le_range A (fun u => u.val - t.val - 1)
      k.val 1 zero_le_one
      (by
        intro u hu
        obtain ⟨huU, hlag⟩ := Finset.mem_filter.mp hu
        have htu := (Finset.mem_filter.mp huU).2
        omega)
      (by
        intro u hu v hv huv
        apply Fin.ext
        have htu := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
        have htv := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
        simp only at huv
        omega)
    simpa using hb
  have hA :
      (∑ u ∈ A, |covariance (fun w => score k.val M.b M.e w t)
        (fun w => score k.val M.b M.e w u) (obsLaw M)|) ≤
      k.val * policyFactor zeta ^ (k.val + 1) := by
    calc
      _ ≤ ∑ _u ∈ A, policyFactor zeta ^ (k.val + 1) := by
        apply Finset.sum_le_sum
        intro u hu
        have htu := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
        exact observable_score_covariance_le M hM k t u htk (by omega)
      _ = A.card * policyFactor zeta ^ (k.val + 1) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hAcard (by unfold policyFactor; positivity)
  have ha0 : 0 ≤ mixingAlpha t0 := by unfold mixingAlpha; positivity
  have ha1 : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr hM.t0_pos)
  have hD :
      (∑ u ∈ D, |covariance (fun w => score k.val M.b M.e w t)
        (fun w => score k.val M.b M.e w u) (obsLaw M)|) ≤
      1 / (1 - mixingAlpha t0) := by
    calc
      _ ≤ ∑ u ∈ D, mixingAlpha t0 ^ (u.val - t.val - k.val - 1) := by
        apply Finset.sum_le_sum
        intro u hu
        exact observable_score_covariance_le_separated M hM k t u htk
          (Finset.mem_filter.mp hu).2
      _ ≤ ∑ j ∈ Finset.range T, mixingAlpha t0 ^ j := by
        apply binary_sum_pow_image_le_range D
          (fun u => u.val - t.val - k.val - 1) T (mixingAlpha t0) ha0
        · intro u hu
          omega
        · intro u hu v hv huv
          apply Fin.ext
          have hlu := (Finset.mem_filter.mp hu).2
          have hlv := (Finset.mem_filter.mp hv).2
          simp only at huv
          omega
      _ ≤ _ := binary_geom_partial_le_inv ha0 ha1 T
  exact add_le_add hA hD

/-- Equation (8): each unbiased empirical moment has mean-squared error at
most V divided by the number of retained epochs. [Under the listed formal conditions](hyp:hT,hM), [the stated conclusion holds](goal).-/
-- @node: empiricalMoment_mse_le_varianceFactor
lemma empiricalMoment_mse_le_varianceFactor {T : Nat} {t0 zeta : ℝ}
    (hT : 12 ≤ T) (M : RawPomdpExperiment T 2 2)
    (hM : BinaryPomdpClass t0 zeta M) (k : Fin 7) :
    (∫ w, (empiricalMoment k.val M.b M.e w -
      matrixMoment (stationaryLaw (policyKernel M M.b))
        (Matrix.of (policyKernel M M.e)) (rewardRegression M) k.val) ^ 2 ∂obsLaw M) ≤
      varianceFactor (mixingAlpha t0) (policyFactor zeta) / (T - 6 : Nat) := by
  classical
  let := binary_obsLaw_isProbability M
  let I := Finset.univ.filter (fun t : Fin T => 6 ≤ t.val)
  let L := policyFactor zeta
  let a := mixingAlpha t0
  have hI : I = Finset.Ici (⟨6, by omega⟩ : Fin T) := by
    ext t
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    rfl
  have hcard : I.card = T - 6 := by rw [hI, Fin.card_Ici]
  have hL : 1 ≤ L := by
    simpa only [L, policyFactor, Real.exp_zero] using Real.exp_le_exp.mpr hM.zeta_nonneg
  have hp : L ^ (k.val + 1) ≤ L ^ 7 := by
    exact pow_le_pow_right₀ hL (by omega)
  have hsum :
      (∑ t ∈ I, ∑ u ∈ I, covariance (fun w => score k.val M.b M.e w t)
        (fun w => score k.val M.b M.e w u) (obsLaw M)) ≤
      (T - 6 : Nat) * varianceFactor a L := by
    calc
      _ ≤ ∑ t ∈ I, ∑ u ∈ I, |covariance (fun w => score k.val M.b M.e w t)
        (fun w => score k.val M.b M.e w u) (obsLaw M)| := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro u hu
        exact le_abs_self _
      _ = (∑ t ∈ I, |covariance (fun w => score k.val M.b M.e w t)
          (fun w => score k.val M.b M.e w t) (obsLaw M)|) +
        2 * ∑ t ∈ I, ∑ u ∈ I.filter (fun u => t < u),
          |covariance (fun w => score k.val M.b M.e w t)
            (fun w => score k.val M.b M.e w u) (obsLaw M)| := by
        apply binary_sum_abs_symmetric_eq_diag_add_two_upper
        intro t u
        rw [covariance_comm]
      _ ≤ I.card * L ^ (k.val + 1) +
        2 * (I.card * (k.val * L ^ (k.val + 1) + 1 / (1 - a))) := by
        gcongr
        · calc
            _ ≤ ∑ _t ∈ I, L ^ (k.val + 1) := by
              apply Finset.sum_le_sum
              intro t ht
              have ht6 := (Finset.mem_filter.mp ht).2
              rw [covariance_self (score_measurable k.val M.b M.e t).aemeasurable,
                abs_of_nonneg (variance_nonneg _ _)]
              exact observable_score_variance_le M hM k t (by omega)
            _ = _ := by simp
        · calc
            _ ≤ ∑ _t ∈ I, (k.val * L ^ (k.val + 1) + 1 / (1 - a)) := by
              apply Finset.sum_le_sum
              intro t ht
              have ht6 := (Finset.mem_filter.mp ht).2
              exact binary_sum_abs_covariance_future_le M hM k t (by omega)
            _ = _ := by simp; ring
      _ = I.card * ((1 + 2 * k.val) * L ^ (k.val + 1) + 2 / (1 - a)) := by ring
      _ ≤ I.card * (13 * L ^ 7 + 2 / (1 - a)) := by
        gcongr
        · have hk : (k.val : ℝ) ≤ 6 := by exact_mod_cast (show k.val ≤ 6 by omega)
          linarith
      _ = _ := by rw [hcard]; rfl
  rw [empiricalMoment_mse_eq_covariance_sum hT M hM k]
  change ((T - 6 : Nat) : ℝ)⁻¹ ^ 2 * (∑ t ∈ I, ∑ u ∈ I, _) ≤ _
  calc
    _ ≤ ((T - 6 : Nat) : ℝ)⁻¹ ^ 2 *
        ((T - 6 : Nat) * varianceFactor a L) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by
      have hn : ((T - 6 : Nat) : ℝ) ≠ 0 := by exact_mod_cast (show T - 6 ≠ 0 by omega)
      dsimp [a, L]
      field_simp

/-- Equation (9): taking the maximum of seven errors costs only a factor seven. [Under the listed formal conditions](hyp:hT,hM), [the stated conclusion holds](goal).-/
-- @node: empiricalMoment_max_mse_le_varianceFactor
lemma empiricalMoment_max_mse_le_varianceFactor {T : Nat} {t0 zeta : ℝ}
    (hT : 12 ≤ T) (M : RawPomdpExperiment T 2 2)
    (hM : BinaryPomdpClass t0 zeta M) :
    (∫ w, (⨆ k : Fin 7, |empiricalMoment k.val M.b M.e w -
      matrixMoment (stationaryLaw (policyKernel M M.b))
        (Matrix.of (policyKernel M M.e)) (rewardRegression M) k.val|) ^ 2 ∂obsLaw M) ≤
      7 * varianceFactor (mixingAlpha t0) (policyFactor zeta) / (T - 6 : Nat) := by
  calc
    _ ≤ ∑ k : Fin 7, ∫ w, (empiricalMoment k.val M.b M.e w -
        matrixMoment (stationaryLaw (policyKernel M M.b))
          (Matrix.of (policyKernel M M.e)) (rewardRegression M) k.val) ^ 2 ∂obsLaw M :=
      empiricalMoment_max_mse_le_sum M hM _
    _ ≤ ∑ _k : Fin 7, varianceFactor (mixingAlpha t0) (policyFactor zeta) /
        (T - 6 : Nat) := Finset.sum_le_sum (fun k _ =>
      empiricalMoment_mse_le_varianceFactor hT M hM k)
    _ = _ := by simp; ring

end CausalSmith.Stat.PomdpBinaryhiddenRate
