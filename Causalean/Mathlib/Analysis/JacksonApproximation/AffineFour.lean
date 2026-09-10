import Causalean.Mathlib.Analysis.JacksonApproximation.CoefficientEnvelopeFour

/-!
# Affine Jackson approximation on four-dimensional rectangles

This module transports tensor Jackson approximation between the normalized cube and a
nondegenerate rectangle, preserving evaluation, degree, approximation, and coefficient bounds.
-/

namespace Causalean.Mathlib.Analysis.JacksonApproximation

open scoped BigOperators

/-- [A finite dimension](hyp:d), [a rectangle center](hyp:c), [coordinate radii](hyp:r), and
[normalized coordinates](hyp:z) determine [the corresponding point under the
center-plus-radius affine map](goal).
-/
def affinePoint {d : ℕ} (c r z : Fin d → ℝ) : Fin d → ℝ :=
  fun i => c i + r i * z i

/-- [A finite dimension](hyp:d), [a rectangle center](hyp:c), [coordinate radii](hyp:r), and [a
point in the rectangle's ambient space](hyp:y) determine [its normalized coordinates](goal) by
subtracting the center and dividing coordinatewise by the radii.
-/
noncomputable def normalizedPoint {d : ℕ} (c r y : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (y i - c i) / r i

/-- [A finite dimension](hyp:d), [a center](hyp:c), and [coordinate radii](hyp:r) determine [the
closed centered rectangle](goal) consisting of points whose coordinatewise distance from the
center does not exceed the corresponding radius.
-/
def centeredRectangle {d : ℕ} (c r : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {y | ∀ i, |y i - c i| ≤ r i}

/-- For [a finite dimension](hyp:d), [a center](hyp:c), [coordinate radii](hyp:r), and [normalized
coordinates](hyp:z), if [every radius is positive](hyp:hr), then [normalizing the affine image
recovers the original normalized coordinates](goal).
-/
theorem normalizedPoint_affinePoint {d : ℕ} (c r z : Fin d → ℝ)
    (hr : ∀ i, 0 < r i) : normalizedPoint c r (affinePoint c r z) = z := by
  funext i
  simp only [normalizedPoint, affinePoint]
  field_simp [ne_of_gt (hr i)]
  ring

/-- For [a finite dimension](hyp:d), [a center](hyp:c), [coordinate radii](hyp:r), and [a
point](hyp:y), if [every radius is positive](hyp:hr), then [applying the affine map to the
normalized point recovers the original point](goal).
-/
theorem affinePoint_normalizedPoint {d : ℕ} (c r y : Fin d → ℝ)
    (hr : ∀ i, 0 < r i) : affinePoint c r (normalizedPoint c r y) = y := by
  funext i
  simp only [affinePoint, normalizedPoint]
  field_simp [ne_of_gt (hr i)]
  ring

/-- For [a finite dimension](hyp:d), [a center](hyp:c), [coordinate radii](hyp:r), and [normalized
coordinates](hyp:z), if [every radius is nonnegative](hyp:hr) and [the normalized point lies
in the normalized cube](hyp:hz), then [its affine image lies in the centered rectangle](goal).
-/
theorem affinePoint_mem_centeredRectangle {d : ℕ} (c r z : Fin d → ℝ)
    (hr : ∀ i, 0 < r i) (hz : z ∈ normalizedCube d) :
    affinePoint c r z ∈ centeredRectangle c r := by
  intro i
  simp only [affinePoint]
  rw [add_sub_cancel_left, abs_mul, abs_of_pos (hr i)]
  exact mul_le_of_le_one_right (le_of_lt (hr i)) (abs_le.mpr (hz i))

/-- For [a finite dimension](hyp:d), [a center](hyp:c), [coordinate radii](hyp:r), and [a
point](hyp:y), if [every radius is positive](hyp:hr) and [the point lies in the centered
rectangle](hyp:hy), then [its normalized coordinates lie in the normalized cube](goal).
-/
theorem normalizedPoint_mem_normalizedCube {d : ℕ} (c r y : Fin d → ℝ)
    (hr : ∀ i, 0 < r i) (hy : y ∈ centeredRectangle c r) :
    normalizedPoint c r y ∈ normalizedCube d := by
  intro i
  rw [show normalizedPoint c r y i = (y i - c i) / r i by rfl,
    Set.mem_Icc]
  apply abs_le.mp
  rw [abs_div, abs_of_pos (hr i), div_le_one (hr i)]
  exact hy i

private lemma mvCoeffL1_eq_sum_superset {d : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (s : Finset (Fin d →₀ ℕ)) (hs : p.support ⊆ s) :
    mvCoeffL1 p = ∑ m ∈ s, |p.coeff m| := by
  unfold mvCoeffL1
  apply Finset.sum_subset hs
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff.mp hm, abs_zero]

private lemma mvCoeffL1_add_le {d : ℕ} (p q : MvPolynomial (Fin d) ℝ) :
    mvCoeffL1 (p + q) ≤ mvCoeffL1 p + mvCoeffL1 q := by
  classical
  rw [mvCoeffL1_eq_sum_superset (p + q) (p.support ∪ q.support)
    (MvPolynomial.support_add.trans Finset.Subset.rfl)]
  simp_rw [MvPolynomial.coeff_add]
  calc
    (∑ m ∈ p.support ∪ q.support, |p.coeff m + q.coeff m|) ≤
        ∑ m ∈ p.support ∪ q.support, (|p.coeff m| + |q.coeff m|) := by
      gcongr with m hm
      exact abs_add_le _ _
    _ = (∑ m ∈ p.support ∪ q.support, |p.coeff m|) +
        ∑ m ∈ p.support ∪ q.support, |q.coeff m| := by
      simp only [Finset.sum_add_distrib]
    _ = mvCoeffL1 p + mvCoeffL1 q := by
      rw [← mvCoeffL1_eq_sum_superset p _ Finset.subset_union_left,
        ← mvCoeffL1_eq_sum_superset q _ Finset.subset_union_right]

private lemma mvCoeffL1_monomial {d : ℕ} (m : Fin d →₀ ℕ) (a : ℝ) :
    mvCoeffL1 (MvPolynomial.monomial m a) = |a| := by
  classical
  by_cases ha : a = 0
  · simp [ha, mvCoeffL1]
  · simp [mvCoeffL1, MvPolynomial.support_monomial, ha]

private lemma mvCoeffL1_C {d : ℕ} (a : ℝ) :
    mvCoeffL1 (MvPolynomial.C a : MvPolynomial (Fin d) ℝ) = |a| := by
  rw [← MvPolynomial.monomial_zero']
  exact mvCoeffL1_monomial 0 a

private lemma mvCoeffL1_X {d : ℕ} (i : Fin d) :
    mvCoeffL1 (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) = 1 := by
  rw [← pow_one (MvPolynomial.X i : MvPolynomial (Fin d) ℝ),
    MvPolynomial.X_pow_eq_monomial, mvCoeffL1_monomial]
  simp

private lemma mvCoeffL1_neg {d : ℕ} (p : MvPolynomial (Fin d) ℝ) :
    mvCoeffL1 (-p) = mvCoeffL1 p := by
  classical
  simp [mvCoeffL1, MvPolynomial.coeff_neg]

private lemma mvCoeffL1_monomial_mul {d : ℕ} (m : Fin d →₀ ℕ) (a : ℝ)
    (p : MvPolynomial (Fin d) ℝ) :
    mvCoeffL1 (MvPolynomial.monomial m a * p) = |a| * mvCoeffL1 p := by
  classical
  by_cases ha : a = 0
  · simp [ha, mvCoeffL1]
  · unfold mvCoeffL1
    rw [show (MvPolynomial.monomial m a * p).support =
        p.support.map (addLeftEmbedding m) by
      exact AddMonoidAlgebra.support_coeff_single_mul p a
        (fun y => mul_eq_zero.trans (or_iff_right ha)) m]
    rw [Finset.sum_map]
    change (∑ x ∈ p.support,
      |(MvPolynomial.monomial m a * p).coeff (m + x)|) =
        |a| * ∑ x ∈ p.support, |p.coeff x|
    simp_rw [MvPolynomial.coeff_monomial_mul, abs_mul]
    rw [Finset.mul_sum]

private lemma mvCoeffL1_finsetSum_le {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin d) ℝ) :
    mvCoeffL1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, mvCoeffL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvCoeffL1]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (mvCoeffL1_add_le _ _).trans (add_le_add le_rfl ih)

private lemma mvCoeffL1_mul_le {d : ℕ} (p q : MvPolynomial (Fin d) ℝ) :
    mvCoeffL1 (p * q) ≤ mvCoeffL1 p * mvCoeffL1 q := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [Finset.sum_mul]
  calc
    mvCoeffL1 (∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m) * q) ≤
        ∑ m ∈ p.support,
          mvCoeffL1 (MvPolynomial.monomial m (p.coeff m) * q) :=
      mvCoeffL1_finsetSum_le _ _
    _ = ∑ m ∈ p.support, |p.coeff m| * mvCoeffL1 q := by
      apply Finset.sum_congr rfl
      intro m hm
      exact mvCoeffL1_monomial_mul m (p.coeff m) q
    _ = mvCoeffL1 p * mvCoeffL1 q := by
      rw [← Finset.sum_mul]
      rfl

private lemma mvCoeffL1_pow_le {d : ℕ} (p : MvPolynomial (Fin d) ℝ) (k : ℕ) :
    mvCoeffL1 (p ^ k) ≤ mvCoeffL1 p ^ k := by
  induction k with
  | zero => simp [mvCoeffL1, MvPolynomial.support_one]
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (mvCoeffL1_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right ih (by unfold mvCoeffL1; positivity))

private lemma mvCoeffL1_finsetProd_le {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin d) ℝ) :
    mvCoeffL1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, mvCoeffL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvCoeffL1, MvPolynomial.support_one]
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (mvCoeffL1_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left ih (by unfold mvCoeffL1; positivity))

private lemma affineVariable_degreeOf_le (c r : Fin 4 → ℝ) (i j : Fin 4) :
    (((MvPolynomial.X j - MvPolynomial.C (c j)) *
      MvPolynomial.C (r j)⁻¹ : MvPolynomial (Fin 4) ℝ).degreeOf i) ≤
        if i = j then 1 else 0 := by
  calc
    ((MvPolynomial.X j - MvPolynomial.C (c j)) *
        MvPolynomial.C (r j)⁻¹ : MvPolynomial (Fin 4) ℝ).degreeOf i ≤
      (MvPolynomial.X j - MvPolynomial.C (c j) :
        MvPolynomial (Fin 4) ℝ).degreeOf i +
          (MvPolynomial.C (r j)⁻¹ : MvPolynomial (Fin 4) ℝ).degreeOf i :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ max ((MvPolynomial.X j : MvPolynomial (Fin 4) ℝ).degreeOf i)
        ((-MvPolynomial.C (c j) : MvPolynomial (Fin 4) ℝ).degreeOf i) + 0 := by
      gcongr
      · simpa [sub_eq_add_neg] using MvPolynomial.degreeOf_add_le i
          (MvPolynomial.X j : MvPolynomial (Fin 4) ℝ) (-MvPolynomial.C (c j))
      · simp
    _ = if i = j then 1 else 0 := by
      simp [MvPolynomial.degreeOf_X]

private lemma affineVariable_totalDegree_le (c r : Fin 4 → ℝ) (j : Fin 4) :
    ((MvPolynomial.X j - MvPolynomial.C (c j)) *
      MvPolynomial.C (r j)⁻¹ : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 := by
  calc
    ((MvPolynomial.X j - MvPolynomial.C (c j)) *
        MvPolynomial.C (r j)⁻¹ : MvPolynomial (Fin 4) ℝ).totalDegree ≤
      (MvPolynomial.X j - MvPolynomial.C (c j) :
        MvPolynomial (Fin 4) ℝ).totalDegree +
          (MvPolynomial.C (r j)⁻¹ : MvPolynomial (Fin 4) ℝ).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ max (MvPolynomial.X j : MvPolynomial (Fin 4) ℝ).totalDegree
        (-MvPolynomial.C (c j) : MvPolynomial (Fin 4) ℝ).totalDegree + 0 := by
      gcongr
      · simpa [sub_eq_add_neg] using MvPolynomial.totalDegree_add
          (MvPolynomial.X j : MvPolynomial (Fin 4) ℝ) (-MvPolynomial.C (c j))
      · simp
    _ = 1 := by simp

/-- Given [a four-variable polynomial](hyp:q), [a center](hyp:c), [coordinate radii](hyp:r) that
[are strictly positive](hyp:hr), [a coordinate-degree limit](hyp:n), and [the corresponding
support bound](hyp:hqcoord), [affine substitution produces a four-variable polynomial with the
stated evaluation, support, total-degree, and coefficient one-norm bounds](goal).
-/
theorem mvPolynomial_affine_substitution_four
    (q : MvPolynomial (Fin 4) ℝ) (c r : Fin 4 → ℝ) (n : ℕ)
    (hr : ∀ i, 0 < r i)
    (hqcoord : ∀ m ∈ q.support, ∀ i, m i ≤ n) :
    ∃ p : MvPolynomial (Fin 4) ℝ,
      (∀ y, MvPolynomial.eval y p = MvPolynomial.eval (normalizedPoint c r y) q) ∧
      (∀ m ∈ p.support, ∀ i, m i ≤ n) ∧
      p.totalDegree ≤ q.totalDegree ∧
      mvCoeffL1 p ≤ mvCoeffL1 q *
        ∏ i : Fin 4, (max 1 ((1 + |c i|) / r i)) ^ n := by
  classical
  let g : Fin 4 → MvPolynomial (Fin 4) ℝ := fun i =>
    (MvPolynomial.X i - MvPolynomial.C (c i)) * MvPolynomial.C (r i)⁻¹
  let p := MvPolynomial.bind₁ g q
  have hp_sum : p = ∑ m ∈ q.support,
      MvPolynomial.bind₁ g (MvPolynomial.monomial m (q.coeff m)) := by
    dsimp [p]
    conv_lhs => rw [q.as_sum]
    simp only [map_sum]
  have hcoord_term (m : Fin 4 →₀ ℕ) (a : ℝ) (i : Fin 4) :
      (MvPolynomial.bind₁ g (MvPolynomial.monomial m a)).degreeOf i ≤ m i := by
    rw [MvPolynomial.bind₁_monomial]
    calc
      (MvPolynomial.C a * ∏ j ∈ m.support, g j ^ m j :
          MvPolynomial (Fin 4) ℝ).degreeOf i ≤
        (MvPolynomial.C a : MvPolynomial (Fin 4) ℝ).degreeOf i +
          (∏ j ∈ m.support, g j ^ m j :
            MvPolynomial (Fin 4) ℝ).degreeOf i :=
        MvPolynomial.degreeOf_mul_le _ _ _
      _ ≤ 0 + ∑ j ∈ m.support, (g j ^ m j :
          MvPolynomial (Fin 4) ℝ).degreeOf i := by
        gcongr
        · simp
        · exact MvPolynomial.degreeOf_prod_le _ _ _
      _ ≤ ∑ j ∈ m.support, m j * (if i = j then 1 else 0) := by
        simp only [zero_add]
        gcongr with j hj
        exact (MvPolynomial.degreeOf_pow_le _ _ _).trans
          (Nat.mul_le_mul_left _ (by
            dsimp [g]
            exact affineVariable_degreeOf_le c r i j))
      _ = m i := by
        by_cases hi : i ∈ m.support
        · rw [Finset.sum_eq_single i]
          · simp
          · intro j hj hji
            simp [Ne.symm hji]
          · exact fun h => (h hi).elim
        · have hmi : m i = 0 := Finsupp.notMem_support_iff.mp hi
          rw [hmi]
          apply Finset.sum_eq_zero
          intro j hj
          have hji : i ≠ j := by
            intro hij
            subst j
            exact hi hj
          simp [hji]
  have htotal_term (m : Fin 4 →₀ ℕ) (a : ℝ) :
      (MvPolynomial.bind₁ g (MvPolynomial.monomial m a)).totalDegree ≤
        m.sum fun _ e => e := by
    rw [MvPolynomial.bind₁_monomial]
    calc
      (MvPolynomial.C a * ∏ j ∈ m.support, g j ^ m j :
          MvPolynomial (Fin 4) ℝ).totalDegree ≤
        (MvPolynomial.C a : MvPolynomial (Fin 4) ℝ).totalDegree +
          (∏ j ∈ m.support, g j ^ m j :
            MvPolynomial (Fin 4) ℝ).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + ∑ j ∈ m.support,
          (g j ^ m j : MvPolynomial (Fin 4) ℝ).totalDegree := by
        gcongr
        · simp
        · exact MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ j ∈ m.support, m j := by
        simp only [zero_add]
        gcongr with j hj
        exact (MvPolynomial.totalDegree_pow _ _).trans
          (by simpa [g] using
            Nat.mul_le_mul_left (m j) (affineVariable_totalDegree_le c r j))
      _ = m.sum fun _ e => e := by rfl
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · intro y
    dsimp [p]
    rw [← MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_bind₁,
      MvPolynomial.aeval_eq_eval]
    apply congrArg (fun z => MvPolynomial.eval z q)
    funext i
    simp [g, normalizedPoint, div_eq_mul_inv]
  · intro m hm i
    apply (MvPolynomial.monomial_le_degreeOf i hm).trans
    rw [hp_sum]
    refine (MvPolynomial.degreeOf_sum_le i q.support
      (fun m => MvPolynomial.bind₁ g (MvPolynomial.monomial m (q.coeff m)))).trans ?_
    exact Finset.sup_le fun m hm => (hcoord_term m (q.coeff m) i).trans (hqcoord m hm i)
  · rw [hp_sum]
    refine (MvPolynomial.totalDegree_finsetSum q.support
      (fun m => MvPolynomial.bind₁ g (MvPolynomial.monomial m (q.coeff m)))).trans ?_
    exact Finset.sup_le fun m hm => (htotal_term m (q.coeff m)).trans
      (MvPolynomial.le_totalDegree hm)
  · let A : Fin 4 → ℝ := fun i => (1 + |c i|) / r i
    let M : Fin 4 → ℝ := fun i => max 1 (A i)
    have hA (i : Fin 4) : 0 ≤ A i := by
      dsimp [A]
      exact div_nonneg (by positivity) (le_of_lt (hr i))
    have hAM (i : Fin 4) : A i ≤ M i := by
      exact le_max_right _ _
    have hM (i : Fin 4) : 1 ≤ M i := by
      exact le_max_left _ _
    have hg_l1 (i : Fin 4) : mvCoeffL1 (g i) ≤ A i := by
      dsimp [g, A]
      calc
        mvCoeffL1 ((MvPolynomial.X i - MvPolynomial.C (c i)) *
            MvPolynomial.C (r i)⁻¹ : MvPolynomial (Fin 4) ℝ) ≤
          mvCoeffL1 (MvPolynomial.X i - MvPolynomial.C (c i) :
            MvPolynomial (Fin 4) ℝ) *
            mvCoeffL1 (MvPolynomial.C (r i)⁻¹ : MvPolynomial (Fin 4) ℝ) :=
          mvCoeffL1_mul_le _ _
        _ ≤ (mvCoeffL1 (MvPolynomial.X i : MvPolynomial (Fin 4) ℝ) +
              mvCoeffL1 (-MvPolynomial.C (c i) : MvPolynomial (Fin 4) ℝ)) *
            mvCoeffL1 (MvPolynomial.C (r i)⁻¹ : MvPolynomial (Fin 4) ℝ) := by
          apply mul_le_mul_of_nonneg_right
          · simpa [sub_eq_add_neg] using mvCoeffL1_add_le
              (MvPolynomial.X i : MvPolynomial (Fin 4) ℝ) (-MvPolynomial.C (c i))
          · unfold mvCoeffL1
            positivity
        _ = (1 + |c i|) / r i := by
          rw [mvCoeffL1_X, mvCoeffL1_neg, mvCoeffL1_C, mvCoeffL1_C,
            abs_inv, abs_of_pos (hr i)]
          simp [div_eq_mul_inv]
    have hterm_l1 (m : Fin 4 →₀ ℕ) (a : ℝ) :
        mvCoeffL1 (MvPolynomial.bind₁ g (MvPolynomial.monomial m a)) ≤
          |a| * ∏ i ∈ m.support, A i ^ m i := by
      rw [MvPolynomial.bind₁_monomial]
      calc
        mvCoeffL1 (MvPolynomial.C a * ∏ i ∈ m.support, g i ^ m i) ≤
          mvCoeffL1 (MvPolynomial.C a : MvPolynomial (Fin 4) ℝ) *
            mvCoeffL1 (∏ i ∈ m.support, g i ^ m i) := mvCoeffL1_mul_le _ _
        _ ≤ |a| * ∏ i ∈ m.support, mvCoeffL1 (g i ^ m i) := by
          rw [mvCoeffL1_C]
          exact mul_le_mul_of_nonneg_left (mvCoeffL1_finsetProd_le _ _)
            (abs_nonneg a)
        _ ≤ |a| * ∏ i ∈ m.support, mvCoeffL1 (g i) ^ m i := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
          apply Finset.prod_le_prod
          · intro i hi
            unfold mvCoeffL1
            positivity
          · intro i hi
            exact mvCoeffL1_pow_le _ _
        _ ≤ |a| * ∏ i ∈ m.support, A i ^ m i := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
          apply Finset.prod_le_prod
          · intro i hi
            exact pow_nonneg (by unfold mvCoeffL1; positivity) _
          · intro i hi
            exact pow_le_pow_left₀ (by unfold mvCoeffL1; positivity) (hg_l1 i) _
    have hfactor (m : Fin 4 →₀ ℕ) (hm : m ∈ q.support) :
        (∏ i ∈ m.support, A i ^ m i) ≤ ∏ i : Fin 4, M i ^ n := by
      calc
        (∏ i ∈ m.support, A i ^ m i) ≤
            ∏ i ∈ m.support, M i ^ n := by
          apply Finset.prod_le_prod
          · intro i hi
            exact pow_nonneg (hA i) _
          · intro i hi
            exact (pow_le_pow_left₀ (hA i) (hAM i) _).trans
              (pow_le_pow_right₀ (hM i) (hqcoord m hm i))
        _ ≤ ∏ i : Fin 4, M i ^ n := by
          apply Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
          · intro i hi
            positivity
          · intro i hi hnot
            exact one_le_pow₀ (hM i)
    rw [hp_sum]
    calc
      mvCoeffL1 (∑ m ∈ q.support,
          MvPolynomial.bind₁ g (MvPolynomial.monomial m (q.coeff m))) ≤
        ∑ m ∈ q.support,
          mvCoeffL1 (MvPolynomial.bind₁ g
            (MvPolynomial.monomial m (q.coeff m))) := mvCoeffL1_finsetSum_le _ _
      _ ≤ ∑ m ∈ q.support, |q.coeff m| * ∏ i : Fin 4, M i ^ n := by
        gcongr with m hm
        exact (hterm_l1 m (q.coeff m)).trans
          (mul_le_mul_of_nonneg_left (hfactor m hm) (abs_nonneg _))
      _ = mvCoeffL1 q * ∏ i : Fin 4, M i ^ n := by
        rw [← Finset.sum_mul]
        rfl
      _ = mvCoeffL1 q *
          ∏ i : Fin 4, (max 1 ((1 + |c i|) / r i)) ^ n := by rfl

/-- For [integer order K](hyp:K) that is [strictly positive](hyp:hK), [a rectangle center](hyp:c),
[positive coordinate radii](hyp:r,hr), and [a function](hyp:f) that [is continuous on the
centered rectangle](hyp:hf), [the affine Jackson construction has a four-variable polynomial
representation with the stated evaluation, support, and degree bounds](goal).
-/
theorem affineJackson_exists_mvPolynomial_four {K : ℕ} (hK : 0 < K)
    (c r : Fin 4 → ℝ) (hr : ∀ i, 0 < r i)
    (f : (Fin 4 → ℝ) → ℝ) (hf : ContinuousOn f (centeredRectangle c r)) :
    ∃ p q : MvPolynomial (Fin 4) ℝ,
      (∀ y, MvPolynomial.eval y p = MvPolynomial.eval (normalizedPoint c r y) q) ∧
      (∀ x, MvPolynomial.eval (cosPoint x) q =
        tensorConvolution K (fun z => f (affinePoint c r z)) x) ∧
      (∀ m ∈ p.support, ∀ i, m i ≤ 2 * (K - 1)) ∧
      p.totalDegree ≤ 8 * (K - 1) := by
  /-
  Pull `f` back along `affinePoint`, proving continuity on `normalizedCube 4`
  with `ContinuousOn.comp` and `affinePoint_mem_centeredRectangle`.  Apply
  `tensorConvolution_exists_mvPolynomial`, then apply
  `mvPolynomial_affine_substitution_four` to its output with
  `n = 2 * (K - 1)`.  The substitution evaluation identity is exactly the
  first conjunct; its support and total-degree conclusions, together with
  `4 * (2 * (K - 1)) = 8 * (K - 1)`, discharge the remaining conjuncts.
  -/
  have haff : Continuous (affinePoint c r) := by
    apply continuous_pi
    intro i
    exact continuous_const.add (continuous_const.mul (continuous_apply i))
  have hpull : ContinuousOn (fun z => f (affinePoint c r z)) (normalizedCube 4) :=
    hf.comp haff.continuousOn
      (fun z hz => affinePoint_mem_centeredRectangle c r z hr hz)
  obtain ⟨q, hqeval, hqcoord, hqtotal⟩ :=
    tensorConvolution_exists_mvPolynomial hK
      (fun z => f (affinePoint c r z)) hpull
  obtain ⟨p, hpeval, hpcoord, hptotal, _⟩ :=
    mvPolynomial_affine_substitution_four q c r (2 * (K - 1)) hr hqcoord
  refine ⟨p, q, hpeval, hqeval, hpcoord, ?_⟩
  omega

/-- For [integer order K](hyp:K) that is [strictly positive](hyp:hK), [a rectangle center](hyp:c),
[positive coordinate radii](hyp:r,hr), [a function](hyp:f), [a nonnegative Lipschitz
constant](hyp:L,hL), [continuity on the centered rectangle](hyp:hf), and [the stated Lipschitz
bound in normalized coordinates](hyp:hlip), [there is a degree-controlled polynomial that
approximates the function throughout the rectangle within one hundred twenty-eight times the
Lipschitz constant divided by K](goal).
-/
theorem affineJackson_approx_four {K : ℕ} (hK : 0 < K)
    (c r : Fin 4 → ℝ) (hr : ∀ i, 0 < r i)
    (f : (Fin 4 → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ContinuousOn f (centeredRectangle c r))
    (hlip : ∀ y ∈ centeredRectangle c r, ∀ z ∈ centeredRectangle c r,
      |f y - f z| ≤ L * ∑ i, |(y i - z i) / r i|) :
    ∃ p : MvPolynomial (Fin 4) ℝ,
      (∀ m ∈ p.support, ∀ i, m i ≤ 2 * (K - 1)) ∧
      p.totalDegree ≤ 8 * (K - 1) ∧
      ∀ y ∈ centeredRectangle c r,
        |MvPolynomial.eval y p - f y| ≤ 128 * L / (K : ℝ) := by
  /-
  Use the same pulled-back function and polynomial extraction/substitution as
  above.  Its cube Lipschitz hypothesis follows from `hlip`: affine coordinate
  differences divided by a positive radius simplify to `x i - z i`.  Apply
  `tensorConvolution_approx_lipschitz` in dimension four.  For a rectangle
  point `y`, set the phase coordinate to
  `Real.arccos (normalizedPoint c r y i)`; membership in the normalized cube
  and `Real.cos_arccos` identify its cosine point with the normalized point.
  Finally use `affinePoint_normalizedPoint` and normalize the constant
  `32 * (4 : ℝ) * L / K` to `128 * L / K`.
  -/
  have haff : Continuous (affinePoint c r) := by
    apply continuous_pi
    intro i
    exact continuous_const.add (continuous_const.mul (continuous_apply i))
  have hpull : ContinuousOn (fun z => f (affinePoint c r z)) (normalizedCube 4) :=
    hf.comp haff.continuousOn
      (fun z hz => affinePoint_mem_centeredRectangle c r z hr hz)
  have hlip_pull : ∀ x ∈ normalizedCube 4, ∀ z ∈ normalizedCube 4,
      |f (affinePoint c r x) - f (affinePoint c r z)| ≤
        L * ∑ i, |x i - z i| := by
    intro x hx z hz
    have h := hlip (affinePoint c r x)
      (affinePoint_mem_centeredRectangle c r x hr hx) (affinePoint c r z)
      (affinePoint_mem_centeredRectangle c r z hr hz)
    have hcoord (i : Fin 4) :
        (affinePoint c r x i - affinePoint c r z i) / r i = x i - z i := by
      simp only [affinePoint]
      field_simp [ne_of_gt (hr i)]
      ring
    simpa only [hcoord] using h
  obtain ⟨p, q, hpeval, hqeval, hpcoord, hptotal⟩ :=
    affineJackson_exists_mvPolynomial_four hK c r hr f hf
  refine ⟨p, hpcoord, hptotal, ?_⟩
  intro y hy
  let x : Fin 4 → ℝ := fun i => Real.arccos (normalizedPoint c r y i)
  have hn := normalizedPoint_mem_normalizedCube c r y hr hy
  have hcos : cosPoint x = normalizedPoint c r y := by
    funext i
    exact Real.cos_arccos (hn i).1 (hn i).2
  have happ := tensorConvolution_approx_lipschitz hK
    (fun z => f (affinePoint c r z)) L hL hpull hlip_pull x
  calc
    |MvPolynomial.eval y p - f y| =
        |tensorConvolution K (fun z => f (affinePoint c r z)) x -
          f (affinePoint c r (cosPoint x))| := by
            rw [hpeval y, ← hcos, hqeval x, hcos,
              affinePoint_normalizedPoint c r y hr]
    _ ≤ 32 * (4 : ℝ) * L / (K : ℝ) := happ
    _ = 128 * L / (K : ℝ) := by ring

/-- For [integer order K](hyp:K) that is [strictly positive](hyp:hK), [a rectangle center](hyp:c),
[positive coordinate radii](hyp:r,hr), [a function](hyp:f), [a nonnegative uniform
bound](hyp:B,hB), [continuity on the centered rectangle](hyp:hf), and [the corresponding
uniform bound throughout the rectangle](hyp:hbound), [the affine Jackson construction has a
four-variable polynomial representation with the stated evaluation, support, degree, and
exponential coefficient one-norm bounds](goal).
-/
theorem affineJackson_coeffBound_four {K : ℕ} (hK : 0 < K)
    (c r : Fin 4 → ℝ) (hr : ∀ i, 0 < r i)
    (f : (Fin 4 → ℝ) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ContinuousOn f (centeredRectangle c r))
    (hbound : ∀ y ∈ centeredRectangle c r, |f y| ≤ B) :
    ∃ p q : MvPolynomial (Fin 4) ℝ,
      (∀ y, MvPolynomial.eval y p = MvPolynomial.eval (normalizedPoint c r y) q) ∧
      (∀ x, MvPolynomial.eval (cosPoint x) q =
        tensorConvolution K (fun z => f (affinePoint c r z)) x) ∧
      (∀ m ∈ p.support, ∀ i, m i ≤ 2 * (K - 1)) ∧
      p.totalDegree ≤ 8 * (K - 1) ∧
      mvCoeffL1 p ≤ (2 : ℝ) ^ (40 * K + 20) * B *
        ∏ i : Fin 4, (max 1 ((1 + |c i|) / r i)) ^ (2 * (K - 1)) := by
  /-
  Pull `f` back along `affinePoint`; rectangle boundedness restricts to cube
  boundedness by `affinePoint_mem_centeredRectangle`.  Obtain `q` from
  `tensorConvolution_exists_mvPolynomial_four_coeffBound`, then substitute it
  using `mvPolynomial_affine_substitution_four` at degree `2 * (K - 1)`.
  Combine the two coefficient inequalities by multiplication with the
  nonnegative finite product.  Reuse the substitution support/total-degree
  conclusions and the tensor evaluation identity without reconstructing a
  different representative.
  -/
  have haff : Continuous (affinePoint c r) := by
    apply continuous_pi
    intro i
    exact continuous_const.add (continuous_const.mul (continuous_apply i))
  have hpull : ContinuousOn (fun z => f (affinePoint c r z)) (normalizedCube 4) :=
    hf.comp haff.continuousOn
      (fun z hz => affinePoint_mem_centeredRectangle c r z hr hz)
  have hbound_pull : ∀ z ∈ normalizedCube 4, |f (affinePoint c r z)| ≤ B := by
    intro z hz
    exact hbound (affinePoint c r z)
      (affinePoint_mem_centeredRectangle c r z hr hz)
  obtain ⟨q, hqeval, hqcoord, hqtotal, hqcoeff⟩ :=
    tensorConvolution_exists_mvPolynomial_four_coeffBound hK
      (fun z => f (affinePoint c r z)) B hB hpull hbound_pull
  obtain ⟨p, hpeval, hpcoord, hptotal, hpcoeff⟩ :=
    mvPolynomial_affine_substitution_four q c r (2 * (K - 1)) hr hqcoord
  refine ⟨p, q, hpeval, hqeval, hpcoord, ?_, ?_⟩
  · omega
  · have hfactor : 0 ≤
        ∏ i : Fin 4, (max 1 ((1 + |c i|) / r i)) ^ (2 * (K - 1)) := by
      positivity
    exact hpcoeff.trans (mul_le_mul_of_nonneg_right hqcoeff hfactor)

end Causalean.Mathlib.Analysis.JacksonApproximation
