module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CitedGates
public import Causalean.Tactic.IntegralLinearity

/-! # Deterministic diagonal separation for isotropic row signing

Signed squared norms split into a sign-independent diagonal and an off-diagonal
quadratic form. Random partitioning recovers one quarter of each form, and optimizing
after averaging is bounded by averaging the cross-group maxima. Finite extrema and
selector averages are measurable and integrable under coordinate second moments.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The off-diagonal quadratic form for a fixed signing of deterministic rows. -/
-- @node: signingOffDiagonal
def signingOffDiagonal {n r : ℕ} (vs : Fin n → EuclideanSpace ℝ (Fin r))
    (z : Signs n) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else sgn (z i) * sgn (z j) * inner ℝ (vs i) (vs j)

/-- The maximum absolute off-diagonal quadratic form over the finite sign space. -/
-- @node: signingOffDiagonalMax
def signingOffDiagonalMax {n r : ℕ} (vs : Fin n → EuclideanSpace ℝ (Fin r)) : ℝ :=
  ⨆ z : Signs n, |signingOffDiagonal vs z|

/-- Every signed squared norm has the same diagonal part.](goal) This uses [the stated conclusion](goal). -/
-- @node: signing_norm_sq_eq_diagonal_add
lemma signing_norm_sq_eq_diagonal_add {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) (z : Signs n) :
    ‖∑ i, sgn (z i) • vs i‖ ^ 2 =
      (∑ i, ‖vs i‖ ^ 2) + signingOffDiagonal vs z := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  unfold signingOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hdiag : ‖vs i‖ ^ 2 = ∑ j : Fin n, if i = j then ‖vs i‖ ^ 2 else 0 := by simp
  rw [hdiag, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    cases z i <;> simp [sgn]
  · simp [hij, mul_assoc]

/-- [ The finite minimum is bounded below by diagonal energy minus maximum fluctuation.](goal) -/
-- @node: signing_min_ge_diagonal_sub_max
lemma signing_min_ge_diagonal_sub_max {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) :
    (∑ i, ‖vs i‖ ^ 2) - signingOffDiagonalMax vs ≤
      ⨅ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ^ 2 := by
  apply le_ciInf
  intro z
  have hmax : |signingOffDiagonal vs z| ≤ signingOffDiagonalMax vs :=
    le_ciSup (Finite.bddAbove_range (fun z : Signs n => |signingOffDiagonal vs z|)) z
  rw [signing_norm_sq_eq_diagonal_add]
  linarith [neg_abs_le (signingOffDiagonal vs z)]

/-- Coordinate second moments integrate the squared norm of every fixed signing. Under [the stated conditions](hyp:hmom), [the asserted mathematical result follows](goal). -/
-- @node: signing_norm_sq_integrable
lemma signing_norm_sq_integrable (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) (z : Signs n) :
    Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) =>
      ‖∑ i, sgn (z i) • vs i‖ ^ 2) (Measure.pi (fun _ : Fin n => P)) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  apply integrable_finsetSum
  intro a _
  have hcoord (i : Fin n) : MemLp
      (fun vs : Fin n → EuclideanSpace ℝ (Fin r) => sgn (z i) * vs i a)
      2 (Measure.pi (fun _ : Fin n => P)) :=
    ((hmom a).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => P) i)).const_mul _
  simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    (memLp_finsetSum Finset.univ (fun i _ => hcoord i)).integrable_sq

/-- [ The genuine finite signing minimum is Borel. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: signing_min_measurable
lemma signing_min_measurable (n r : ℕ) :
    Measurable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) =>
      ⨅ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ^ 2) := by
  apply Measurable.iInf
  intro z
  fun_prop

/-- The finite minimum is integrable, since it lies between zero and one fixed signing.](goal) Under [the stated conditions](hyp:hmom). This uses [the stated conclusion](goal). -/
-- @node: signing_min_integrable
lemma signing_min_integrable (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) :
    Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) =>
      ⨅ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ^ 2) (Measure.pi (fun _ : Fin n => P)) := by
  apply (signing_norm_sq_integrable n r P hmom (fun _ => true)).mono'
    (signing_min_measurable n r).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro vs
  have hnonneg : 0 ≤ ⨅ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ^ 2 :=
    le_ciInf (fun _ => sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact ciInf_le (Finite.bddBelow_range _) (fun _ => true)

/-- [ The maximum off-diagonal fluctuation is Borel. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: signingOffDiagonalMax_measurable
lemma signingOffDiagonalMax_measurable (n r : ℕ) :
    Measurable (signingOffDiagonalMax (n := n) (r := r)) := by
  unfold signingOffDiagonalMax signingOffDiagonal
  apply Measurable.iSup
  intro z
  apply Measurable.abs
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  split_ifs <;> fun_prop

/-- Each off-diagonal form is integrable, as the difference of two quadratic energies.](goal) Under [the stated conditions](hyp:hmom). This uses [the stated conclusion](goal). -/
-- @node: signingOffDiagonal_integrable
lemma signingOffDiagonal_integrable (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) (z : Signs n) :
    Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) => signingOffDiagonal vs z)
      (Measure.pi (fun _ : Fin n => P)) := by
  have hdiag : Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) =>
      ∑ i, ‖vs i‖ ^ 2) (Measure.pi (fun _ : Fin n => P)) := by
    apply integrable_finsetSum
    intro i _
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    apply integrable_finsetSum
    intro a _
    exact ((hmom a).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => P) i)).integrable_sq
  have h := (signing_norm_sq_integrable n r P hmom z).sub hdiag
  change Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) =>
    ‖∑ i, sgn (z i) • vs i‖ ^ 2 - ∑ i, ‖vs i‖ ^ 2) _ at h
  simpa only [signing_norm_sq_eq_diagonal_add, add_sub_cancel_left] using h

/-- [ The maximum absolute fluctuation is integrable, bounded by the finite sum of fluctuations.](goal) Under [the stated conditions](hyp:hmom). -/
-- @node: signingOffDiagonalMax_integrable
lemma signingOffDiagonalMax_integrable (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) :
    Integrable (signingOffDiagonalMax (n := n) (r := r))
      (Measure.pi (fun _ : Fin n => P)) := by
  classical
  have hsum : Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) =>
      ∑ z : Signs n, |signingOffDiagonal vs z|) (Measure.pi (fun _ : Fin n => P)) :=
    integrable_finsetSum _ (fun z _ => (signingOffDiagonal_integrable n r P hmom z).abs)
  apply hsum.mono' (signingOffDiagonalMax_measurable n r).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro vs
  have hnonneg : 0 ≤ signingOffDiagonalMax vs :=
    (abs_nonneg _).trans (le_ciSup
      (Finite.bddAbove_range (fun z : Signs n => |signingOffDiagonal vs z|)) (fun _ => true))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  apply ciSup_le
  intro z
  exact Finset.single_le_sum (f := fun z : Signs n => |signingOffDiagonal vs z|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ z)

/-- [ Distinct coordinates of a uniformly sampled sign vector have zero product mean.](goal) Under [the stated conditions](hyp:hij). -/
-- @node: fairSigns_distinct_product_mean_zero
lemma fairSigns_distinct_product_mean_zero (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (∫ z, sgn (z i) * sgn (z j) ∂fairSigns n) = 0 := by
  classical
  let := fairSigns_probability n
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Measure.real, fairSigns, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, smul_eq_mul]
  let e : Signs n ≃ Signs n :=
    { toFun := fun z => Function.update z i (!(z i))
      invFun := fun z => Function.update z i (!(z i))
      left_inv := by intro z; funext k; by_cases hk : k = i <;> simp [hk]
      right_inv := by intro z; funext k; by_cases hk : k = i <;> simp [hk] }
  have hsum := e.sum_comp (fun z =>
    ((Fintype.card (Signs n) : ℝ≥0∞)⁻¹).toReal * (sgn (z i) * sgn (z j)))
  have hneg (z : Signs n) : sgn (e z i) * sgn (e z j) = -(sgn (z i) * sgn (z j)) := by
    change sgn (Function.update z i (!(z i)) i) *
      sgn (Function.update z i (!(z i)) j) = _
    simp only [Function.update_self, Function.update_of_ne hij.symm]
    cases z i <;> cases z j <;> norm_num [sgn]
  simp only [hneg, mul_neg, Finset.sum_neg_distrib] at hsum
  linarith

/-- [ An ordered pair of distinct rows belongs to the selected and complementary groups
with probability exactly one quarter.](goal) Under [the stated conditions](hyp:hij). -/
-- @node: fairSigns_partition_pair_mean
lemma fairSigns_partition_pair_mean (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (∫ η : Signs n, if η i = true ∧ η j = false then (1 : ℝ) else 0 ∂fairSigns n) = 1 / 4 := by
  let := fairSigns_probability n
  have hp (η : Signs n) :
      (if η i = true ∧ η j = false then (1 : ℝ) else 0) =
        (1 + sgn (η i) - sgn (η j) - sgn (η i) * sgn (η j)) / 4 := by
    cases η i <;> cases η j <;> norm_num [sgn]
  simp_rw [hp]
  integral_linearity
  rw [integral_sub (Integrable.of_finite) (Integrable.of_finite),
    integral_sub (Integrable.of_finite) (Integrable.of_finite),
    integral_add (Integrable.of_finite) (Integrable.of_finite)]
  rw [fairSigns_mean_zero, fairSigns_mean_zero, fairSigns_distinct_product_mean_zero n i j hij]
  simp

/-- The cross-group signed quadratic form for a selected set and its complement. -/
-- @node: signingPartitionCross
def signingPartitionCross {n r : ℕ} (vs : Fin n → EuclideanSpace ℝ (Fin r))
    (z η : Signs n) : ℝ :=
  ∑ i, ∑ j, if η i = true ∧ η j = false then
    sgn (z i) * sgn (z j) * inner ℝ (vs i) (vs j) else 0

/-- Random partitioning recovers exactly one quarter of every fixed off-diagonal form. [The asserted mathematical result follows](goal). -/
-- @node: signingOffDiagonal_eq_partition_average
lemma signingOffDiagonal_eq_partition_average {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) (z : Signs n) :
    signingOffDiagonal vs z = 4 * ∫ η, signingPartitionCross vs z η ∂fairSigns n := by
  classical
  let := fairSigns_probability n
  unfold signingPartitionCross
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  rw [Finset.mul_sum]
  unfold signingOffDiagonal
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp
  · rw [if_neg hij]
    have hc : (∫ η : Signs n, if η i = true ∧ η j = false then
        sgn (z i) * sgn (z j) * inner ℝ (vs i) (vs j) else 0 ∂fairSigns n) =
        (sgn (z i) * sgn (z j) * inner ℝ (vs i) (vs j)) * (1 / 4) := by
      have he (η : Signs n) :
          (if η i = true ∧ η j = false then
            sgn (z i) * sgn (z j) * inner ℝ (vs i) (vs j) else 0) =
          (sgn (z i) * sgn (z j) * inner ℝ (vs i) (vs j)) *
            (if η i = true ∧ η j = false then (1 : ℝ) else 0) := by
        split_ifs <;> simp
      simp_rw [he]
      rw [integral_const_mul, fairSigns_partition_pair_mean n i j hij]
    rw [hc]
    ring

/-- [ The cross-group form is the actual inner product of the two disjoint signed sums.](goal) -/
-- @node: signingPartitionCross_eq_inner
lemma signingPartitionCross_eq_inner {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) (z η : Signs n) :
    signingPartitionCross vs z η =
      inner ℝ (∑ i, if η i = true then sgn (z i) • vs i else 0)
        (∑ j, if η j = false then sgn (z j) • vs j else 0) := by
  classical
  unfold signingPartitionCross
  simp_rw [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : η i = true <;> by_cases hj : η j = false <;>
    simp [hi, hj, real_inner_smul_left, real_inner_smul_right, mul_assoc, mul_left_comm]

/-- [ Maximum absolute signed cross-group fluctuation for a realized partition. -/
-- @node: signingPartitionCrossMax
def signingPartitionCrossMax {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) (η : Signs n) : ℝ :=
  ⨆ z : Signs n, |signingPartitionCross vs z η|

/-- Optimizing after averaging can only decrease the absolute supremum. This is the
load-bearing direction of the random-partition inequality in the roadmap.](goal) This uses [the stated conclusion](goal). -/
-- @node: signingOffDiagonalMax_le_partition_average
lemma signingOffDiagonalMax_le_partition_average {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) :
    signingOffDiagonalMax vs ≤ 4 * ∫ η, signingPartitionCrossMax vs η ∂fairSigns n := by
  classical
  let := fairSigns_probability n
  unfold signingOffDiagonalMax
  apply ciSup_le
  intro z
  rw [signingOffDiagonal_eq_partition_average, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    |∫ η, signingPartitionCross vs z η ∂fairSigns n| ≤
        ∫ η, |signingPartitionCross vs z η| ∂fairSigns n := abs_integral_le_integral_abs
    _ ≤ ∫ η, signingPartitionCrossMax vs η ∂fairSigns n := by
      apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
      intro η
      exact le_ciSup (Finite.bddAbove_range (fun z : Signs n => |signingPartitionCross vs z η|)) z

/-- Coordinate second moments integrate inner products of any two rows, even when equal. Under [the stated conditions](hyp:hmom), [the asserted mathematical result follows](goal). -/
-- @node: signing_row_inner_integrable
lemma signing_row_inner_integrable (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) (i j : Fin n) :
    Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) => inner ℝ (vs i) (vs j))
      (Measure.pi (fun _ : Fin n => P)) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply integrable_finsetSum
  intro a _
  exact ((hmom a).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin n => P) j)).integrable_mul
      ((hmom a).comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => P) i))

/-- [ Each signed cross-group quadratic form is integrable under coordinate second moments.](goal) Under [the stated conditions](hyp:hmom). -/
-- @node: signingPartitionCross_integrable
lemma signingPartitionCross_integrable (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) (z η : Signs n) :
    Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) => signingPartitionCross vs z η)
      (Measure.pi (fun _ : Fin n => P)) := by
  unfold signingPartitionCross
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  split_ifs
  · exact (signing_row_inner_integrable n r P hmom i j).const_mul _
  · exact integrable_zero _ _ _

/-- [ The finite cross-group maximum is Borel for every realized selector. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: signingPartitionCrossMax_measurable
lemma signingPartitionCrossMax_measurable (n r : ℕ) (η : Signs n) :
    Measurable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) => signingPartitionCrossMax vs η) := by
  unfold signingPartitionCrossMax signingPartitionCross
  apply Measurable.iSup
  intro z
  apply Measurable.abs
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  split_ifs <;> fun_prop

/-- The finite cross-group maximum is integrable under coordinate second moments.](goal) Under [the stated conditions](hyp:hmom). This uses [the stated conclusion](goal). -/
-- @node: signingPartitionCrossMax_integrable
lemma signingPartitionCrossMax_integrable (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) (η : Signs n) :
    Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) => signingPartitionCrossMax vs η)
      (Measure.pi (fun _ : Fin n => P)) := by
  classical
  have hsum : Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) =>
      ∑ z : Signs n, |signingPartitionCross vs z η|) (Measure.pi (fun _ : Fin n => P)) :=
    integrable_finsetSum _ (fun z _ => (signingPartitionCross_integrable n r P hmom z η).abs)
  apply hsum.mono' (signingPartitionCrossMax_measurable n r η).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro vs
  have hnonneg : 0 ≤ signingPartitionCrossMax vs η :=
    (abs_nonneg _).trans (le_ciSup
      (Finite.bddAbove_range (fun z : Signs n => |signingPartitionCross vs z η|)) (fun _ => true))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  apply ciSup_le
  intro z
  exact Finset.single_le_sum (f := fun z : Signs n => |signingPartitionCross vs z η|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ z)

/-- [ Averaging a finite cross-group maximum over selectors preserves integrability.](goal) Under [the stated conditions](hyp:hmom). -/
-- @node: signingPartitionCross_average_integrable
lemma signingPartitionCross_average_integrable (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) :
    Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) =>
      ∫ η, signingPartitionCrossMax vs η ∂fairSigns n) (Measure.pi (fun _ : Fin n => P)) := by
  let := fairSigns_probability n
  simp_rw [integral_fintype (Integrable.of_finite), smul_eq_mul]
  exact integrable_finsetSum _ (fun η _ =>
    (signingPartitionCrossMax_integrable n r P hmom η).const_mul _)

/-- [ The expected absolute off-diagonal maximum is at most four times the expected
cross-group maximum. The finite selector average is inside the row expectation.](goal) Under [the stated conditions](hyp:hmom). -/
-- @node: signingOffDiagonal_integral_le_partition_average
lemma signingOffDiagonal_integral_le_partition_average (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) :
    (∫ vs : Fin n → EuclideanSpace ℝ (Fin r), signingOffDiagonalMax vs
      ∂Measure.pi (fun _ : Fin n => P)) ≤
      4 * ∫ vs : Fin n → EuclideanSpace ℝ (Fin r),
        ∫ η, signingPartitionCrossMax vs η ∂fairSigns n ∂Measure.pi (fun _ : Fin n => P) := by
  have h := integral_mono (signingOffDiagonalMax_integrable n r P hmom)
    ((signingPartitionCross_average_integrable n r P hmom).const_mul 4)
    signingOffDiagonalMax_le_partition_average
  rwa [integral_const_mul] at h

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
