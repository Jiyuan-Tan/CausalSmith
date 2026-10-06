module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.Estimators
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SurvivalBounds
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.SurvivalTaylor
public import Causalean.Stat.Nonparametric.LocalPoly.GramCoercivity
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Continuation bias

Moment matching of the continuation polynomial removes the first `ell + 1`
terms of the endpoint Taylor expansion.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

open scoped BigOperators

-- @node: continuationPolynomial
noncomputable def continuationPolynomial (ell : ℕ)
    (v : Fin (ell + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ m, v m * x ^ m.val

-- @node: continuationPolynomial_continuous
lemma continuationPolynomial_continuous (ell : ℕ)
    (v : Fin (ell + 1) → ℝ) :
    Continuous (continuationPolynomial ell v) := by
  unfold continuationPolynomial
  fun_prop

-- @node: continuationGram_eq_integral
lemma continuationGram_eq_integral (ell : ℕ)
    (j m : Fin (ell + 1)) :
    continuationGram ell j m = ∫ x in (1 : ℝ)..2, x ^ j.val * x ^ m.val := by
  rw [show (fun x : ℝ ↦ x ^ j.val * x ^ m.val) =
      fun x : ℝ ↦ x ^ (m.val + j.val) by
    funext x
    rw [pow_add, mul_comm]]
  rw [integral_pow]
  · unfold continuationGram
    push_cast
    ring

-- @node: continuationGram_quadForm
lemma continuationGram_quadForm (ell : ℕ)
    (v : Fin (ell + 1) → ℝ) :
    dotProduct v ((continuationGram ell).mulVec v) =
      ∫ x in (1 : ℝ)..2, (continuationPolynomial ell v x) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, continuationPolynomial, Finset.mul_sum]
  simp_rw [continuationGram_eq_integral]
  calc
    ∑ j : Fin (ell + 1), ∑ m : Fin (ell + 1),
        v j * ((∫ x in (1 : ℝ)..2, x ^ j.val * x ^ m.val) * v m) =
        ∑ j : Fin (ell + 1), ∑ m : Fin (ell + 1),
          ∫ x in (1 : ℝ)..2, (v j * x ^ j.val) * (v m * x ^ m.val) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro m _
      rw [show (fun x : ℝ ↦ (v j * x ^ j.val) * (v m * x ^ m.val)) =
          fun x : ℝ ↦ (v j * v m) * (x ^ j.val * x ^ m.val) by
        funext x
        ring]
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = ∫ x in (1 : ℝ)..2,
        ∑ j : Fin (ell + 1), ∑ m : Fin (ell + 1),
          (v j * x ^ j.val) * (v m * x ^ m.val) := by
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [intervalIntegral.integral_finset_sum]
        intro m _
        exact (((continuous_const.mul (continuous_pow _)).mul
          (continuous_const.mul (continuous_pow _))).intervalIntegrable _ _)
      · intro j _
        exact (continuous_finset_sum _ fun m _ => by fun_prop).intervalIntegrable _ _
    _ = ∫ x in (1 : ℝ)..2, (∑ j, v j * x ^ j.val) ^ 2 := by
      congr 1
      funext x
      rw [pow_two, Finset.sum_mul_sum]

-- @node: continuationPolynomial_ne_zero
lemma continuationPolynomial_ne_zero (ell : ℕ)
    {v : Fin (ell + 1) → ℝ} (hv : v ≠ 0) :
    continuationPolynomial ell v ≠ 0 := by
  intro hzero
  have hpoly :
      Causalean.Stat.Nonparametric.LocalPolynomial.localPolynomial ell v = 0 := by
    apply Polynomial.funext
    intro x
    rw [Causalean.Stat.Nonparametric.LocalPolynomial.localPolynomial_eval]
    simpa [continuationPolynomial] using congrFun hzero x
  exact hv ((Causalean.Stat.Nonparametric.LocalPolynomial.localPolynomial_eq_zero_iff ell v).mp
    hpoly)

-- @node: continuationGram_posDef
lemma continuationGram_posDef (ell : ℕ) :
    (continuationGram ell).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro j m
    simp only [star_id_of_comm]
    simp [continuationGram, add_comm]
  · intro v hv
    have hstar : star v = v := funext (fun i => star_trivial _)
    rw [hstar, continuationGram_quadForm]
    let f : ℝ → ℝ := continuationPolynomial ell v
    have hfcont : Continuous f := continuationPolynomial_continuous ell v
    have hfint : IntervalIntegrable (fun x => (f x) ^ 2) volume 1 2 :=
      (hfcont.pow 2).intervalIntegrable 1 2
    have hpoly :
        Causalean.Stat.Nonparametric.LocalPolynomial.localPolynomial ell v ≠ 0 := by
      simpa [Causalean.Stat.Nonparametric.LocalPolynomial.localPolynomial_eq_zero_iff] using hv
    have hroots : Set.Finite
        {x : ℝ | Polynomial.IsRoot
          (Causalean.Stat.Nonparametric.LocalPolynomial.localPolynomial ell v) x} :=
      (Polynomial.roots
          (Causalean.Stat.Nonparametric.LocalPolynomial.localPolynomial ell v)).toFinset
        |>.finite_toSet.subset (by
            intro x hx
            simpa [Polynomial.mem_roots hpoly] using hx)
    have hinter : Set.Infinite (Set.Ioo (1 : ℝ) 2) := Set.Ioo_infinite (by norm_num)
    obtain ⟨x, hxI, hxroot⟩ := (hinter.sdiff hroots).nonempty
    have hfx : f x ≠ 0 := by
      rw [show f x =
          (Causalean.Stat.Nonparametric.LocalPolynomial.localPolynomial ell v).eval x by
        simp [f, continuationPolynomial,
          Causalean.Stat.Nonparametric.LocalPolynomial.localPolynomial_eval]]
      intro he
      exact hxroot (by simpa [Polynomial.IsRoot] using he)
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
      (by
        filter_upwards [ae_restrict_mem
          (measurableSet_uIoc : MeasurableSet (Set.uIoc (1 : ℝ) 2))] with y hy
        exact sq_nonneg (f y)) hfint]
    refine ⟨by norm_num, ?_⟩
    let U := Function.support (fun y => (f y) ^ 2) ∩ Set.Ioo (1 : ℝ) 2
    have hUopen : IsOpen U := (hfcont.pow 2).isOpen_support.inter isOpen_Ioo
    have hUne : U.Nonempty := ⟨x, pow_ne_zero 2 hfx, hxI⟩
    exact lt_of_lt_of_le (hUopen.measure_pos volume hUne) (measure_mono (by
      intro y hy
      exact ⟨hy.1, hy.2.1, hy.2.2.le⟩))

-- @node: continuationPoly_eq_polynomial
lemma continuationPoly_eq_polynomial (ell : ℕ) (x : ℝ) :
    continuationPoly ell x =
      continuationPolynomial ell ((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) x := by
  simp [continuationPoly, continuationPolynomial, Matrix.mulVec, dotProduct]

-- @node: continuationPoly_moment
lemma continuationPoly_moment (ell : ℕ) (j : Fin (ell + 1)) :
    ∫ x in (1 : ℝ)..2, continuationPoly ell x * x ^ j.val =
      continuationRhs ell j := by
  rw [show (fun x : ℝ => continuationPoly ell x * x ^ j.val) =
      fun x : ℝ => ∑ m : Fin (ell + 1),
        ((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m *
          (x ^ m.val * x ^ j.val) by
    funext x
    rw [continuationPoly_eq_polynomial]
    simp only [continuationPolynomial, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    ring]
  rw [intervalIntegral.integral_finset_sum]
  · simp_rw [intervalIntegral.integral_const_mul]
    have hentry (m : Fin (ell + 1)) :
        (∫ x in (1 : ℝ)..2, x ^ m.val * x ^ j.val) = continuationGram ell j m := by
      rw [← continuationGram_eq_integral ell m j]
      simp [continuationGram, add_comm]
    simp_rw [hentry]
    rw [show (∑ m : Fin (ell + 1),
        ((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m *
          continuationGram ell j m) =
        ((continuationGram ell).mulVec
          ((continuationGram ell)⁻¹.mulVec (continuationRhs ell))) j by
      simp [Matrix.mulVec, dotProduct, mul_comm]]
    rw [Matrix.mulVec_mulVec]
    have hunit : IsUnit (continuationGram ell).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (continuationGram_posDef ell).isUnit
    rw [Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  · intro m _
    exact ((continuous_const.mul ((continuous_pow _).mul (continuous_pow _))).intervalIntegrable
      _ _)

-- @node: continuationPolynomial_abs_le_coeffSum
lemma continuationPolynomial_abs_le_coeffSum (ell : ℕ)
    (v : Fin (ell + 1) → ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    |continuationPolynomial ell v x| ≤
      ∑ m : Fin (ell + 1), |v m| * (2 : ℝ) ^ m.val := by
  unfold continuationPolynomial
  calc
    |∑ m : Fin (ell + 1), v m * x ^ m.val| ≤
        ∑ m : Fin (ell + 1), |v m * x ^ m.val| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m : Fin (ell + 1), |v m| * x ^ m.val := by
      apply Finset.sum_congr rfl
      intro m _
      rw [abs_mul, abs_pow, abs_of_nonneg hx0]
    _ ≤ ∑ m : Fin (ell + 1), |v m| * (2 : ℝ) ^ m.val := by
      apply Finset.sum_le_sum
      intro m _
      gcongr

-- @node: continuationPoly_abs_le_coeffSum
lemma continuationPoly_abs_le_coeffSum (ell : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    |continuationPoly ell x| ≤
      ∑ m : Fin (ell + 1),
        |((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m| *
          (2 : ℝ) ^ m.val := by
  rw [continuationPoly_eq_polynomial]
  exact continuationPolynomial_abs_le_coeffSum ell _ hx0 hx2

-- @node: continuationWeight_abs_le_coeffSum
lemma continuationWeight_abs_le_coeffSum (ell : ℕ) {h t : ℝ}
    (hh : 0 < h) :
    |continuationWeight ell h t| ≤
      1 + ∑ m : Fin (ell + 1),
        |((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m| *
          (2 : ℝ) ^ m.val := by
  let K : ℝ := ∑ m : Fin (ell + 1),
    |((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m| *
      (2 : ℝ) ^ m.val
  have hK : 0 ≤ K := Finset.sum_nonneg (by
    intro m _
    positivity)
  by_cases hband : 1 - 2 * h ≤ t ∧ t ≤ 1 - h
  · have hx0 : 0 ≤ (1 - t) / h := div_nonneg (by linarith [hband.2]) hh.le
    have hx2 : (1 - t) / h ≤ 2 := (div_le_iff₀ hh).2 (by linarith [hband.1])
    have hpoly := continuationPoly_abs_le_coeffSum ell hx0 hx2
    change |continuationPoly ell ((1 - t) / h)| ≤ K at hpoly
    by_cases hleft : t ≤ 1 - h
    · simp only [continuationWeight, ne_of_gt hh, ↓reduceIte, hleft, hband]
      exact (abs_add_le 1 (continuationPoly ell ((1 - t) / h))).trans (by
        simp only [abs_one]
        linarith)
    · exact (hleft hband.2).elim
  · by_cases hleft : t ≤ 1 - h
    · simp only [continuationWeight, if_neg (ne_of_gt hh), if_pos hleft,
        if_neg hband, add_zero, abs_one]
      linarith
    · simp only [continuationWeight, if_neg (ne_of_gt hh), if_neg hleft,
        if_neg hband, zero_add, abs_zero]
      linarith

-- @node: continuationPoly_scaled_moment
lemma continuationPoly_scaled_moment (ell : ℕ) (j : Fin (ell + 1))
    {h : ℝ} (hh : 0 < h) :
    ∫ t in (1 - 2 * h)..(1 - h),
        continuationPoly ell ((1 - t) / h) * (1 - t) ^ j.val =
      h ^ (j.val + 1) * continuationRhs ell j := by
  have hne : h ≠ 0 := ne_of_gt hh
  let f : ℝ → ℝ := fun t =>
    continuationPoly ell ((1 - t) / h) * (1 - t) ^ j.val
  have hsub := intervalIntegral.integral_comp_sub_mul (f := f)
    (a := (1 : ℝ)) (b := 2) hne (1 : ℝ)
  simp only [f] at hsub
  have hscaled :
      (∫ t in (1 - 2 * h)..(1 - h),
        continuationPoly ell ((1 - t) / h) * (1 - t) ^ j.val) =
      h * (∫ x in (1 : ℝ)..2,
        continuationPoly ell ((1 - (1 - h * x)) / h) *
          (1 - (1 - h * x)) ^ j.val) := by
    have heq := congrArg (fun z : ℝ => h * z) hsub
    simpa [smul_eq_mul, hne, mul_comm, mul_left_comm, mul_assoc] using heq.symm
  rw [hscaled]
  have hintegral :
      (∫ x in (1 : ℝ)..2,
        continuationPoly ell ((1 - (1 - h * x)) / h) *
          (1 - (1 - h * x)) ^ j.val) =
      h ^ j.val * continuationRhs ell j := by
    rw [show (fun x : ℝ =>
        continuationPoly ell ((1 - (1 - h * x)) / h) *
          (1 - (1 - h * x)) ^ j.val) =
        (fun x : ℝ => h ^ j.val * (continuationPoly ell x * x ^ j.val)) by
      funext x
      have hx : (1 - (1 - h * x)) / h = x := by field_simp; ring
      rw [hx, show 1 - (1 - h * x) = h * x by ring, mul_pow]
      ring]
    rw [intervalIntegral.integral_const_mul, continuationPoly_moment]
  rw [hintegral, pow_succ]
  ring

-- @node: continuationPoly_band_moment
lemma continuationPoly_band_moment (ell : ℕ) (j : Fin (ell + 1))
    {h : ℝ} (hh : 0 < h) :
    (∫ t in (1 - 2 * h)..(1 - h),
      continuationPoly ell ((1 - t) / h) * (1 - t) ^ j.val) =
    ∫ t in (1 - h)..1, (1 - t) ^ j.val := by
  rw [continuationPoly_scaled_moment ell j hh]
  have hsub := intervalIntegral.integral_comp_sub_left
    (f := fun x : ℝ => x ^ j.val) (a := 1 - h) (b := 1) (1 : ℝ)
  rw [hsub]
  rw [integral_pow]
  simp [continuationRhs, div_eq_mul_inv]

-- @node: continuationPoly_continuous
lemma continuationPoly_continuous (ell : ℕ) : Continuous (continuationPoly ell) := by
  rw [show continuationPoly ell =
      continuationPolynomial ell ((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) by
    funext x
    exact continuationPoly_eq_polynomial ell x]
  exact continuationPolynomial_continuous ell _

-- @node: continuationPoly_reproduces
lemma continuationPoly_reproduces (ell : ℕ)
    (v : Fin (ell + 1) → ℝ) {h : ℝ} (hh : 0 < h) :
    (∫ t in (1 - 2 * h)..(1 - h),
      continuationPoly ell ((1 - t) / h) *
        (∑ j : Fin (ell + 1), v j * (1 - t) ^ j.val)) =
    ∫ t in (1 - h)..1, ∑ j : Fin (ell + 1), v j * (1 - t) ^ j.val := by
  have hpoly : Continuous (fun t : ℝ => continuationPoly ell ((1 - t) / h)) := by
    exact (continuationPoly_continuous ell).comp (by fun_prop)
  rw [show (fun t : ℝ => continuationPoly ell ((1 - t) / h) *
        (∑ j : Fin (ell + 1), v j * (1 - t) ^ j.val)) =
      (fun t : ℝ => ∑ j : Fin (ell + 1),
        v j * (continuationPoly ell ((1 - t) / h) * (1 - t) ^ j.val)) by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring]
  rw [intervalIntegral.integral_finsetSum, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      continuationPoly_band_moment ell j hh]
  · intro j _
    exact (by fun_prop : Continuous (fun t : ℝ => v j * (1 - t) ^ j.val))
      |>.intervalIntegrable _ _
  · intro j _
    exact (by fun_prop : Continuous (fun t : ℝ =>
      v j * (continuationPoly ell ((1 - t) / h) * (1 - t) ^ j.val)))
      |>.intervalIntegrable _ _

-- @node: continuationWeight_polynomial_reproduces
lemma continuationWeight_polynomial_reproduces (ell : ℕ)
    (v : Fin (ell + 1) → ℝ) {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2) :
    (∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t *
      (∑ j : Fin (ell + 1), v j * (1 - t) ^ j.val)) =
    ∫ t in (0 : ℝ)..1, ∑ j : Fin (ell + 1), v j * (1 - t) ^ j.val := by
  let p : ℝ → ℝ := fun t => ∑ j : Fin (ell + 1), v j * (1 - t) ^ j.val
  let k : ℝ → ℝ := fun t => continuationPoly ell ((1 - t) / h)
  have hp : Continuous p := by
    dsimp [p]
    fun_prop
  have hk : Continuous k := (continuationPoly_continuous ell).comp (by fun_prop)
  have h01 : (0 : ℝ) ≤ 1 - 2 * h := by linarith
  have h12 : 1 - 2 * h ≤ 1 - h := by linarith
  have hbase : ∀ t ∈ Set.Ioo (0 : ℝ) (1 - 2 * h),
      continuationWeight ell h t * p t = p t := by
    intro t ht
    have hleft : t ≤ 1 - h := by linarith [ht.2]
    have hnot : ¬ (1 ≤ t + 2 * h) := by linarith [ht.2]
    simp [continuationWeight, hh.ne', hleft, hnot]
  have hband : ∀ t ∈ Set.Ioo (1 - 2 * h) (1 - h),
      continuationWeight ell h t * p t = p t + k t * p t := by
    intro t ht
    have hleft : t ≤ 1 - h := ht.2.le
    have hinside : 1 - 2 * h ≤ t ∧ t ≤ 1 - h := ⟨ht.1.le, ht.2.le⟩
    simp [continuationWeight, hh.ne', hleft, hinside, k]
    ring
  have hpoly : (∫ t in (1 - 2 * h)..(1 - h), k t * p t) =
      ∫ t in (1 - h)..1, p t := by
    exact continuationPoly_reproduces ell v hh
  have hsplit1 : (∫ t in (0 : ℝ)..(1 - 2 * h), p t) +
      (∫ t in (1 - 2 * h)..(1 - h), p t) =
      ∫ t in (0 : ℝ)..(1 - h), p t := intervalIntegral.integral_add_adjacent_intervals
    (hp.intervalIntegrable 0 (1 - 2 * h))
    (hp.intervalIntegrable (1 - 2 * h) (1 - h))
  have hsplit2 : (∫ t in (0 : ℝ)..(1 - h), p t) +
      (∫ t in (1 - h)..1, p t) =
      ∫ t in (0 : ℝ)..1, p t := intervalIntegral.integral_add_adjacent_intervals
    (hp.intervalIntegrable 0 (1 - h))
    (hp.intervalIntegrable (1 - h) 1)
  have hweightBase : IntervalIntegrable (fun t => continuationWeight ell h t * p t)
      volume 0 (1 - 2 * h) :=
    (hp.intervalIntegrable _ _).congr_uIoo (by
      rw [Set.uIoo_of_le h01]
      intro t ht
      exact (hbase t ht).symm)
  have hweightBand : IntervalIntegrable (fun t => continuationWeight ell h t * p t)
      volume (1 - 2 * h) (1 - h) := by
    have hc : Continuous (fun t => p t + k t * p t) := hp.add (hk.mul hp)
    exact (hc.intervalIntegrable _ _).congr_uIoo (by
      rw [Set.uIoo_of_le h12]
      intro t ht
      exact (hband t ht).symm)
  have hsplitWeighted :
      (∫ t in (0 : ℝ)..(1 - 2 * h), continuationWeight ell h t * p t) +
      (∫ t in (1 - 2 * h)..(1 - h), continuationWeight ell h t * p t) =
      ∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * p t :=
    intervalIntegral.integral_add_adjacent_intervals
    hweightBase hweightBand
  change (∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * p t) =
    ∫ t in (0 : ℝ)..1, p t
  have heqBase :
      (∫ t in (0 : ℝ)..(1 - 2 * h), continuationWeight ell h t * p t) =
      ∫ t in (0 : ℝ)..(1 - 2 * h), p t :=
    intervalIntegral.integral_congr_uIoo (by
      rw [Set.uIoo_of_le h01]
      intro t ht
      exact hbase t ht)
  have heqBand :
      (∫ t in (1 - 2 * h)..(1 - h), continuationWeight ell h t * p t) =
      ∫ t in (1 - 2 * h)..(1 - h), p t + k t * p t :=
    intervalIntegral.integral_congr_uIoo (by
      rw [Set.uIoo_of_le h12]
      intro t ht
      exact hband t ht)
  calc
    _ = (∫ t in (0 : ℝ)..(1 - 2 * h), continuationWeight ell h t * p t) +
        ∫ t in (1 - 2 * h)..(1 - h), continuationWeight ell h t * p t :=
      hsplitWeighted.symm
    _ = (∫ t in (0 : ℝ)..(1 - 2 * h), p t) +
        ∫ t in (1 - 2 * h)..(1 - h), p t + k t * p t := by
      rw [heqBase, heqBand]
    _ = (∫ t in (0 : ℝ)..(1 - 2 * h), p t) +
        (∫ t in (1 - 2 * h)..(1 - h), p t) +
        (∫ t in (1 - 2 * h)..(1 - h), k t * p t) := by
      have hadd : (∫ t in (1 - 2 * h)..(1 - h), p t + k t * p t) =
          (∫ t in (1 - 2 * h)..(1 - h), p t) +
          (∫ t in (1 - 2 * h)..(1 - h), k t * p t) := by
        exact intervalIntegral.integral_add
          (hp.intervalIntegrable _ _) ((hk.mul hp).intervalIntegrable _ _)
      rw [hadd]
      ring
    _ = _ := by rw [hsplit1, hpoly, hsplit2]

-- @node: continuationWeight_remainder_identity
lemma continuationWeight_remainder_identity (ell : ℕ)
    (v : Fin (ell + 1) → ℝ) {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 1)
    (hwf : IntervalIntegrable (fun t => continuationWeight ell h t * f t)
      volume 0 (1 - h)) :
    (∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * f t) -
        ∫ t in (0 : ℝ)..1, f t =
      (∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t *
        (f t - ∑ j : Fin (ell + 1), v j * (1 - t) ^ j.val)) -
      ∫ t in (0 : ℝ)..1,
        (f t - ∑ j : Fin (ell + 1), v j * (1 - t) ^ j.val) := by
  let p : ℝ → ℝ := fun t => ∑ j : Fin (ell + 1), v j * (1 - t) ^ j.val
  have hp : Continuous p := by
    dsimp [p]
    fun_prop
  have hwp : IntervalIntegrable (fun t => continuationWeight ell h t * p t)
      volume 0 (1 - h) := by
    have h01 : (0 : ℝ) ≤ 1 - 2 * h := by linarith
    have h12 : 1 - 2 * h ≤ 1 - h := by linarith
    apply IntervalIntegrable.trans (b := 1 - 2 * h)
    · apply (hp.intervalIntegrable _ _).congr_uIoo
      rw [Set.uIoo_of_le h01]
      intro t ht
      have hleft : t ≤ 1 - h := by linarith [ht.2]
      have hnot : ¬ (1 ≤ t + 2 * h) := by linarith [ht.2]
      simp [continuationWeight, hh.ne', hleft, hnot]
    · have hc : Continuous (fun t : ℝ =>
          p t + continuationPoly ell ((1 - t) / h) * p t) :=
        hp.add (((continuationPoly_continuous ell).comp (by fun_prop)).mul hp)
      apply (hc.intervalIntegrable _ _).congr_uIoo
      rw [Set.uIoo_of_le h12]
      intro t ht
      have hleft : t ≤ 1 - h := ht.2.le
      have hinside : 1 - 2 * h ≤ t ∧ t ≤ 1 - h := ⟨ht.1.le, ht.2.le⟩
      simp [continuationWeight, hh.ne', hleft, hinside]
      ring
  have hfp := continuationWeight_polynomial_reproduces ell v hh hhalf
  change (∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * f t) -
      ∫ t in (0 : ℝ)..1, f t =
    (∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * (f t - p t)) -
      ∫ t in (0 : ℝ)..1, (f t - p t)
  rw [show (fun t => continuationWeight ell h t * (f t - p t)) =
      (fun t => continuationWeight ell h t * f t - continuationWeight ell h t * p t)
      by funext t; ring]
  rw [intervalIntegral.integral_sub hwf hwp,
    intervalIntegral.integral_sub hf (hp.intervalIntegrable _ _)]
  change (∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * f t) -
      ∫ t in (0 : ℝ)..1, f t =
    ((∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * f t) -
      ∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * p t) -
      ((∫ t in (0 : ℝ)..1, f t) - ∫ t in (0 : ℝ)..1, p t)
  rw [hfp]
  ring

-- @node: continuationWeight_remainder_band_terminal
lemma continuationWeight_remainder_band_terminal (ell : ℕ)
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    (r : ℝ → ℝ) (hr : ContinuousOn r (Set.Icc (0 : ℝ) 1)) :
    (∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * r t) -
      ∫ t in (0 : ℝ)..1, r t =
    (∫ t in (1 - 2 * h)..(1 - h),
      continuationPoly ell ((1 - t) / h) * r t) -
      ∫ t in (1 - h)..1, r t := by
  let k : ℝ → ℝ := fun t => continuationPoly ell ((1 - t) / h)
  have hk : Continuous k := (continuationPoly_continuous ell).comp (by fun_prop)
  have h01 : (0 : ℝ) ≤ 1 - 2 * h := by linarith
  have h12 : 1 - 2 * h ≤ 1 - h := by linarith
  have h1h : 1 - h ≤ 1 := by linarith
  have hrint {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u ≤ v) :
      IntervalIntegrable r volume u v := by
    have hrsub : ContinuousOn r (Set.Icc u v) := hr.mono (by
      intro t ht
      exact ⟨hu.trans ht.1, ht.2.trans hv⟩)
    exact hrsub.intervalIntegrable_of_Icc huv
  have hbase : ∀ t ∈ Set.Ioo (0 : ℝ) (1 - 2 * h),
      continuationWeight ell h t * r t = r t := by
    intro t ht
    have hleft : t ≤ 1 - h := by linarith [ht.2]
    have hnot : ¬ (1 ≤ t + 2 * h) := by linarith [ht.2]
    simp [continuationWeight, hh.ne', hleft, hnot]
  have hband : ∀ t ∈ Set.Ioo (1 - 2 * h) (1 - h),
      continuationWeight ell h t * r t = r t + k t * r t := by
    intro t ht
    have hleft : t ≤ 1 - h := ht.2.le
    have hinside : 1 - 2 * h ≤ t ∧ t ≤ 1 - h := ⟨ht.1.le, ht.2.le⟩
    simp [continuationWeight, hh.ne', hleft, hinside, k]
    ring
  have hrband : ContinuousOn r (Set.Icc (1 - 2 * h) (1 - h)) := hr.mono (by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2.trans h1h⟩)
  have hweightBase : IntervalIntegrable
      (fun t => continuationWeight ell h t * r t) volume 0 (1 - 2 * h) :=
    (hrint (le_refl 0) (by linarith) h01).congr_uIoo (by
      rw [Set.uIoo_of_le h01]
      intro t ht
      exact (hbase t ht).symm)
  have hweightBand : IntervalIntegrable
      (fun t => continuationWeight ell h t * r t)
      volume (1 - 2 * h) (1 - h) := by
    refine ((hrband.add (hk.continuousOn.mul hrband)).intervalIntegrable_of_Icc h12)
      |>.congr_uIoo ?_
    rw [Set.uIoo_of_le h12]
    intro t ht
    exact (hband t ht).symm
  have hsplitWeighted :
      (∫ t in (0 : ℝ)..(1 - 2 * h), continuationWeight ell h t * r t) +
      (∫ t in (1 - 2 * h)..(1 - h), continuationWeight ell h t * r t) =
      ∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * r t :=
    intervalIntegral.integral_add_adjacent_intervals
    hweightBase hweightBand
  have hsplitBase :
      (∫ t in (0 : ℝ)..(1 - 2 * h), r t) +
      (∫ t in (1 - 2 * h)..(1 - h), r t) =
      ∫ t in (0 : ℝ)..(1 - h), r t :=
    intervalIntegral.integral_add_adjacent_intervals
    (hrint (le_refl 0) (by linarith) h01)
    (hrint h01 (by linarith) h12)
  have hsplitTerminal :
      (∫ t in (0 : ℝ)..(1 - h), r t) +
      (∫ t in (1 - h)..1, r t) =
      ∫ t in (0 : ℝ)..1, r t :=
    intervalIntegral.integral_add_adjacent_intervals
    (hrint (le_refl 0) h1h (by linarith))
    (hrint (by linarith) (le_refl 1) h1h)
  have heqBase :
      (∫ t in (0 : ℝ)..(1 - 2 * h), continuationWeight ell h t * r t) =
      ∫ t in (0 : ℝ)..(1 - 2 * h), r t :=
    intervalIntegral.integral_congr_uIoo (by
      rw [Set.uIoo_of_le h01]
      intro t ht
      exact hbase t ht)
  have heqBand :
      (∫ t in (1 - 2 * h)..(1 - h), continuationWeight ell h t * r t) =
      ∫ t in (1 - 2 * h)..(1 - h), r t + k t * r t :=
    intervalIntegral.integral_congr_uIoo (by
      rw [Set.uIoo_of_le h12]
      intro t ht
      exact hband t ht)
  have hadd :
      (∫ t in (1 - 2 * h)..(1 - h), r t + k t * r t) =
      (∫ t in (1 - 2 * h)..(1 - h), r t) +
      (∫ t in (1 - 2 * h)..(1 - h), k t * r t) :=
    intervalIntegral.integral_add
    (hrint h01 (by linarith) h12)
    ((hk.continuousOn.mul hrband).intervalIntegrable_of_Icc h12)
  rw [← hsplitWeighted, heqBase, heqBand, hadd]
  dsimp only [k]
  linear_combination hsplitBase + hsplitTerminal

-- @node: endpointRpow_terminal_integral
lemma endpointRpow_terminal_integral {β h : ℝ} (hβ : 0 < β) :
    (∫ t in (1 - h)..1, (1 - t) ^ β) = h ^ (β + 1) / (β + 1) := by
  rw [intervalIntegral.integral_comp_sub_left
    (f := fun x : ℝ => x ^ β) (d := (1 : ℝ))]
  have hp : -1 < β := by linarith
  rw [integral_rpow (Or.inl hp)]
  simp [Real.zero_rpow (by linarith : β + 1 ≠ 0)]

-- @node: endpointRpow_band_integral
lemma endpointRpow_band_integral {β h : ℝ} (hβ : 0 < β) :
    (∫ t in (1 - 2 * h)..(1 - h), (1 - t) ^ β) =
      ((2 * h) ^ (β + 1) - h ^ (β + 1)) / (β + 1) := by
  rw [intervalIntegral.integral_comp_sub_left
    (f := fun x : ℝ => x ^ β) (d := (1 : ℝ))]
  have hp : -1 < β := by linarith
  convert integral_rpow (a := h) (b := 2 * h) (r := β) (Or.inl hp) using 1 <;>
    ring

-- @node: continuationPoly_band_remainder_bound
lemma continuationPoly_band_remainder_bound (ell : ℕ) {h β C : ℝ}
    (hh : 0 < h) (hβ : 0 ≤ β) (hC : 0 ≤ C) (r : ℝ → ℝ)
    (hr : ∀ t ∈ Set.Icc (1 - 2 * h) (1 - h),
      |r t| ≤ C * (1 - t) ^ β) :
    |∫ t in (1 - 2 * h)..(1 - h),
      continuationPoly ell ((1 - t) / h) * r t| ≤
      (∑ m : Fin (ell + 1),
        |((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m| *
          (2 : ℝ) ^ m.val) * C * (2 * h) ^ β * h := by
  let K : ℝ := ∑ m : Fin (ell + 1),
    |((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m| *
      (2 : ℝ) ^ m.val
  have hK : 0 ≤ K := Finset.sum_nonneg (by
    intro m _
    positivity)
  have hbound : ∀ t ∈ Set.uIoc (1 - 2 * h) (1 - h),
      ‖continuationPoly ell ((1 - t) / h) * r t‖ ≤
        K * C * (2 * h) ^ β := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith : 1 - 2 * h ≤ 1 - h)] at ht
    have ht' : t ∈ Set.Icc (1 - 2 * h) (1 - h) := ⟨ht.1.le, ht.2⟩
    have hx0 : 0 ≤ (1 - t) / h := div_nonneg (by linarith [ht.2]) hh.le
    have hx2 : (1 - t) / h ≤ 2 := (div_le_iff₀ hh).2 (by linarith [ht.1])
    have hk := continuationPoly_abs_le_coeffSum ell hx0 hx2
    change |continuationPoly ell ((1 - t) / h)| ≤ K at hk
    have hp : (1 - t) ^ β ≤ (2 * h) ^ β :=
      Real.rpow_le_rpow (by linarith [ht.2]) (by linarith [ht.1]) hβ
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |continuationPoly ell ((1 - t) / h)| * |r t|
          ≤ K * (C * (1 - t) ^ β) := mul_le_mul hk (hr t ht')
            (abs_nonneg _) hK
      _ ≤ K * (C * (2 * h) ^ β) := by gcongr
      _ = K * C * (2 * h) ^ β := by ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa only [Real.norm_eq_abs, show (1 - h) - (1 - 2 * h) = h by ring,
    abs_of_pos hh, mul_assoc] using hnorm

-- @node: continuationTerminal_remainder_bound
lemma continuationTerminal_remainder_bound {h β C : ℝ}
    (hh : 0 < h) (hβ : 0 ≤ β) (hC : 0 ≤ C) (r : ℝ → ℝ)
    (hr : ∀ t ∈ Set.Icc (1 - h) 1,
      |r t| ≤ C * (1 - t) ^ β) :
    |∫ t in (1 - h)..1, r t| ≤ C * h ^ β * h := by
  have hbound : ∀ t ∈ Set.uIoc (1 - h) 1, ‖r t‖ ≤ C * h ^ β := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith : 1 - h ≤ 1)] at ht
    have ht' : t ∈ Set.Icc (1 - h) 1 := ⟨ht.1.le, ht.2⟩
    have hp : (1 - t) ^ β ≤ h ^ β :=
      Real.rpow_le_rpow (by linarith [ht.2]) (by linarith [ht.1]) hβ
    rw [Real.norm_eq_abs]
    calc
      |r t| ≤ C * (1 - t) ^ β := hr t ht'
      _ ≤ C * h ^ β := by gcongr
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa only [Real.norm_eq_abs, show (1 : ℝ) - (1 - h) = h by ring,
    abs_of_pos hh] using hnorm

-- @node: continuationWeight_remainder_bound
lemma continuationWeight_remainder_bound (ell : ℕ) {h β C : ℝ}
    (hh : 0 < h) (hhalf : h ≤ 1 / 2) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (r : ℝ → ℝ) (hrcont : ContinuousOn r (Set.Icc (0 : ℝ) 1))
    (hr : ∀ t ∈ Set.Icc (1 - 2 * h) 1,
      |r t| ≤ C * (1 - t) ^ β) :
    |(∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * r t) -
      ∫ t in (0 : ℝ)..1, r t| ≤
      (∑ m : Fin (ell + 1),
        |((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m| *
          (2 : ℝ) ^ m.val) * C * (2 * h) ^ β * h +
      C * h ^ β * h := by
  rw [continuationWeight_remainder_band_terminal ell hh hhalf r hrcont]
  have hband := continuationPoly_band_remainder_bound ell hh hβ hC r
    (fun t ht => hr t ⟨ht.1, ht.2.trans (by linarith : 1 - h ≤ 1)⟩)
  have hterminal := continuationTerminal_remainder_bound hh hβ hC r
    (fun t ht => hr t ⟨by linarith [ht.1], ht.2⟩)
  exact (abs_sub _ _).trans (add_le_add hband hterminal)

-- @node: holderOrder_remainder_exponent
lemma holderOrder_remainder_exponent (c : ClassConstants) :
    0 < c.beta - (holderOrder c : ℝ) ∧
      c.beta - (holderOrder c : ℝ) ≤ 1 := by
  have hceil : 0 < Nat.ceil c.beta := Nat.ceil_pos.mpr c.beta_pos
  have hsucc : holderOrder c + 1 = Nat.ceil c.beta := by
    simp [holderOrder, Nat.sub_add_cancel hceil]
  have hlt : ((holderOrder c : ℕ) : ℝ) < c.beta := by
    apply (Nat.lt_ceil).mp
    omega
  have hle : c.beta ≤ (holderOrder c : ℝ) + 1 := by
    have h := Nat.le_ceil c.beta
    rw [← hsucc] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  constructor <;> linarith

-- @node: modelClass_survival_continuousOn
lemma modelClass_survival_continuousOn (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    ContinuousOn (survival P a) (Set.Icc (0 : ℝ) 1) := by
  have hd : ContinuousOn (P.hazard a) (Set.Icc (0 : ℝ) 1) :=
    (hP.deathHolder a).1.continuousOn
  have hi : IntervalIntegrable (P.hazard a) volume 0 1 :=
    hd.intervalIntegrable_of_Icc (by norm_num)
  have hprim : ContinuousOn
      (fun t : ℝ => ∫ u in (0 : ℝ)..t, P.hazard a u)
      (Set.Icc (0 : ℝ) 1) := by
    simpa using intervalIntegral.continuousOn_primitive_interval'
      (a := (0 : ℝ)) hi (by norm_num : (0 : ℝ) ∈ Set.uIcc 0 1)
  change ContinuousOn
    (fun t : ℝ => Real.exp (-(∫ u in (0 : ℝ)..t, P.hazard a u)))
    (Set.Icc (0 : ℝ) 1)
  exact Real.continuous_exp.comp_continuousOn hprim.neg

-- @node: modelClass_target_intervalIntegrable
lemma modelClass_target_intervalIntegrable (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    IntervalIntegrable (fun t => survival P a t * P.lam a t) volume 0 1 := by
  have hs := modelClass_survival_continuousOn c P hP a
  have hl : ContinuousOn (P.lam a) (Set.Icc (0 : ℝ) 1) :=
    (hP.recurrenceHolder a).1.continuousOn
  exact (hs.mul hl).intervalIntegrable_of_Icc (by norm_num)

-- @node: modelClass_weightedTarget_intervalIntegrable
lemma modelClass_weightedTarget_intervalIntegrable (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {h : ℝ}
    (hh : 0 < h) (hhalf : h ≤ 1 / 2) :
    IntervalIntegrable (fun t => continuationWeight (holderOrder c) h t *
      survival P a t * P.lam a t) volume 0 (1 - h) := by
  let f : ℝ → ℝ := fun t => survival P a t * P.lam a t
  have hf : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    (modelClass_survival_continuousOn c P hP a).mul
      (hP.recurrenceHolder a).1.continuousOn
  have hbase : (0 : ℝ) ≤ 1 - 2 * h := by linarith
  have hband : 1 - 2 * h ≤ 1 - h := by linarith
  have hfbase : IntervalIntegrable f volume 0 (1 - 2 * h) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hbase
    exact hf.mono (by intro t ht; exact ⟨ht.1, by linarith [ht.2]⟩)
  have hfb : ContinuousOn f (Set.Icc (1 - 2 * h) (1 - h)) :=
    hf.mono (by intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hpoly : Continuous (fun t : ℝ =>
      continuationPoly (holderOrder c) ((1 - t) / h)) :=
    (continuationPoly_continuous _).comp (by fun_prop)
  have hwbase : IntervalIntegrable
      (fun t => continuationWeight (holderOrder c) h t * f t)
      volume 0 (1 - 2 * h) := by
    apply hfbase.congr_uIoo
    rw [Set.uIoo_of_le hbase]
    intro t ht
    have hleft : t ≤ 1 - h := by linarith [ht.2]
    have hout : ¬ (1 ≤ t + 2 * h) := by linarith [ht.2]
    simp [continuationWeight, hh.ne', hleft, hout]
  have hwband : IntervalIntegrable
      (fun t => continuationWeight (holderOrder c) h t * f t)
      volume (1 - 2 * h) (1 - h) := by
    have hc : ContinuousOn (fun t =>
        (1 + continuationPoly (holderOrder c) ((1 - t) / h)) * f t)
        (Set.Icc (1 - 2 * h) (1 - h)) :=
      (continuousOn_const.add hpoly.continuousOn).mul hfb
    apply (hc.intervalIntegrable_of_Icc hband).congr_uIoo
    rw [Set.uIoo_of_le hband]
    intro t ht
    have hleft : t ≤ 1 - h := ht.2.le
    have hinside : 1 - 2 * h ≤ t ∧ t ≤ 1 - h := ⟨ht.1.le, ht.2.le⟩
    simp [continuationWeight, hh.ne', hleft, hinside]
  simpa only [f, mul_assoc] using
    (IntervalIntegrable.trans (b := 1 - 2 * h) hwbase hwband)

-- @node: continuationBias_of_uniformTaylorRemainderOn
lemma continuationBias_of_uniformTaylorRemainderOn (ell : ℕ) {β C h : ℝ}
    (hh : 0 < h) (hhalf : h ≤ 1 / 2) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (v : Fin (ell + 1) → ℝ)
    (hrem : ∀ t ∈ Set.Icc (1 - 2 * h) 1,
      |f t - ∑ j : Fin (ell + 1), v j * (1 - t) ^ j.val| ≤
        C * (1 - t) ^ β) :
    |(∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * f t) -
        ∫ t in (0 : ℝ)..1, f t| ≤
      ((∑ m : Fin (ell + 1),
        |((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m| *
          (2 : ℝ) ^ m.val) * (2 : ℝ) ^ β + 1) * C * h ^ (β + 1) := by
  let p : ℝ → ℝ := fun t =>
    ∑ j : Fin (ell + 1), v j * (1 - t) ^ j.val
  let r : ℝ → ℝ := fun t => f t - p t
  have hp : Continuous p := by
    dsimp [p]
    fun_prop
  have hr : ContinuousOn r (Set.Icc (0 : ℝ) 1) := hf.sub hp.continuousOn
  have hfint : IntervalIntegrable f volume (0 : ℝ) 1 :=
    hf.intervalIntegrable_of_Icc (by norm_num)
  have hweight : IntervalIntegrable
      (fun t => continuationWeight ell h t * f t) volume 0 (1 - h) := by
    have hbase : (0 : ℝ) ≤ 1 - 2 * h := by linarith
    have hband : 1 - 2 * h ≤ 1 - h := by linarith
    apply IntervalIntegrable.trans (b := 1 - 2 * h)
    · have hfbase : ContinuousOn f (Set.Icc (0 : ℝ) (1 - 2 * h)) := hf.mono (by
        intro t ht
        exact ⟨ht.1, by linarith [ht.2]⟩)
      apply (hfbase.intervalIntegrable_of_Icc hbase).congr_uIoo
      rw [Set.uIoo_of_le hbase]
      intro t ht
      have hleft : t ≤ 1 - h := by linarith [ht.2]
      have hout : ¬ (1 ≤ t + 2 * h) := by linarith [ht.2]
      simp [continuationWeight, hh.ne', hleft, hout]
    · have hc : ContinuousOn (fun t : ℝ =>
          (1 + continuationPoly ell ((1 - t) / h)) * f t)
          (Set.Icc (1 - 2 * h) (1 - h)) :=
        (continuousOn_const.add (((continuationPoly_continuous ell).comp
          (by fun_prop)).continuousOn)).mul
          (hf.mono (by intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩))
      apply (hc.intervalIntegrable_of_Icc hband).congr_uIoo
      rw [Set.uIoo_of_le hband]
      intro t ht
      have hleft : t ≤ 1 - h := ht.2.le
      have hinside : 1 - 2 * h ≤ t ∧ t ≤ 1 - h := ⟨ht.1.le, ht.2.le⟩
      simp [continuationWeight, hh.ne', hleft, hinside]
  rw [continuationWeight_remainder_identity ell v hh hhalf f
    hfint hweight]
  have hbound := continuationWeight_remainder_bound ell hh hhalf hβ hC r hr
    (by simpa only [r, p] using hrem)
  have hmul : (2 * h) ^ β = (2 : ℝ) ^ β * h ^ β :=
    Real.mul_rpow (by norm_num) hh.le
  rw [hmul] at hbound
  have hpow : h ^ β * h = h ^ (β + 1) := by
    rw [Real.rpow_add hh]
    simp
  calc
    _ ≤ (∑ m : Fin (ell + 1),
          |((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m| *
            (2 : ℝ) ^ m.val) * C * ((2 : ℝ) ^ β * h ^ β) * h +
          C * h ^ β * h := hbound
    _ = ((∑ m : Fin (ell + 1),
          |((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m| *
            (2 : ℝ) ^ m.val) * (2 : ℝ) ^ β + 1) * C * h ^ (β + 1) := by
      rw [← hpow]
      ring

-- @node: continuationBias_of_uniformTaylorRemainder
lemma continuationBias_of_uniformTaylorRemainder (ell : ℕ) {β C h : ℝ}
    (hh : 0 < h) (hhalf : h ≤ 1 / 2) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (f : ℝ → ℝ) (hf : Continuous f) (v : Fin (ell + 1) → ℝ)
    (hrem : ∀ t ∈ Set.Icc (1 - 2 * h) 1,
      |f t - ∑ j : Fin (ell + 1), v j * (1 - t) ^ j.val| ≤
        C * (1 - t) ^ β) :
    |(∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * f t) -
        ∫ t in (0 : ℝ)..1, f t| ≤
      ((∑ m : Fin (ell + 1),
        |((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m| *
          (2 : ℝ) ^ m.val) * (2 : ℝ) ^ β + 1) * C * h ^ (β + 1) :=
  continuationBias_of_uniformTaylorRemainderOn ell hh hhalf hβ hC f
    hf.continuousOn v hrem

-- @node: lem:continuation-bias
lemma continuation_bias (c : ClassConstants) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ P : SubjectLaw,
      ModelClass c P →
      ∀ a : Arm, ∀ h : ℝ, 0 < h → h ≤ c.x0 / 2 →
        |truncatedMean c P a h - armMean P a| ≤ B * h ^ (c.beta + 1) := by
  obtain ⟨hα, hα1⟩ := holderOrder_remainder_exponent c
  obtain ⟨C, hC, hTaylor⟩ :=
    Causalean.Mathlib.Analysis.Calculus.HolderTaylor.survival_product_endpoint_taylor_Icc
      (holderOrder c) (c.beta - holderOrder c) 0 1
      c.dMax c.Ld c.lambdaMax c.Llambda hα hα1 (by norm_num)
      (le_trans c.dMin_pos.le c.dMin_lt.le) c.Ld_pos.le
      (le_trans c.lambdaMin_pos.le c.lambdaMin_lt.le) c.Llambda_pos.le
  let K : ℝ := ∑ m : Fin (holderOrder c + 1),
    |((continuationGram (holderOrder c))⁻¹.mulVec
      (continuationRhs (holderOrder c))) m| * (2 : ℝ) ^ m.val
  have hK : 0 ≤ K := Finset.sum_nonneg (by
    intro m _
    positivity)
  refine ⟨(K * (2 : ℝ) ^ c.beta + 1) * C,
    mul_nonneg (add_nonneg (mul_nonneg hK (Real.rpow_nonneg (by norm_num) _))
      (by norm_num)) hC, ?_⟩
  intro P hP a h hh hcap
  have hHazardAbs : ∀ t ∈ Set.Icc (0 : ℝ) 1, |P.hazard a t| ≤ c.dMax := by
    intro t ht
    obtain ⟨hlower, hupper⟩ := hP.deathBounds a t ht
    rw [abs_of_nonneg (c.dMin_pos.le.trans hlower)]
    exact hupper
  have hLambdaAbs : ∀ t ∈ Set.Icc (0 : ℝ) 1, |P.lam a t| ≤ c.lambdaMax := by
    intro t ht
    obtain ⟨hlower, hupper⟩ := hP.recurrenceBounds a t ht
    rw [abs_of_nonneg (c.lambdaMin_pos.le.trans hlower)]
    exact hupper
  obtain ⟨v, hv⟩ := hTaylor (P.hazard a) (P.lam a)
    (hP.deathHolder a).1 (hP.recurrenceHolder a).1
    hHazardAbs hLambdaAbs (hP.deathHolder a).2 (hP.recurrenceHolder a).2
  have hhalf : h ≤ 1 / 2 := by linarith [c.x0_le]
  have h2h : 2 * h ≤ c.x0 := by linarith [hcap]
  have hf : ContinuousOn (fun t => survival P a t * P.lam a t)
      (Set.Icc (0 : ℝ) 1) :=
    (modelClass_survival_continuousOn c P hP a).mul
      (hP.recurrenceHolder a).1.continuousOn
  have hrem : ∀ t ∈ Set.Icc (1 - 2 * h) 1,
      |survival P a t * P.lam a t -
        ∑ j : Fin (holderOrder c + 1), v j * (1 - t) ^ j.val| ≤
          C * (1 - t) ^ c.beta := by
    intro t ht
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith [ht.1, h2h, c.x0_le]
      · exact ht.2
    have htaylor := hv t ht01
    have hexponent : (holderOrder c : ℝ) +
        (c.beta - holderOrder c) = c.beta := by ring
    rw [hexponent] at htaylor
    simpa only [survival] using htaylor
  have hbias := continuationBias_of_uniformTaylorRemainderOn
    (holderOrder c) hh hhalf c.beta_pos.le hC
    (fun t => survival P a t * P.lam a t) hf v hrem
  simpa only [truncatedMean, armMean, K, mul_assoc] using hbias

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
