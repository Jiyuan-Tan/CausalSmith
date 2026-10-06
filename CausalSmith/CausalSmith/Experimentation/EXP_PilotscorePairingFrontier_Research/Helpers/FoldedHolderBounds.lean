module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedKLAssembly

/-! # Difference bounds for folded hypercube bumps -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

lemma foldedFirstBump_diff_le (s t : ℝ) :
    |foldedFirstBump s - foldedFirstBump t| ≤ 32 * |s - t| := by
  unfold foldedFirstBump
  calc
    |max 0 (min 1 (min (32 * (s - 13 / 32)) (32 * (19 / 32 - s)))) -
        max 0 (min 1 (min (32 * (t - 13 / 32)) (32 * (19 / 32 - t))))| ≤
        max |(0 : ℝ) - 0|
          |min 1 (min (32 * (s - 13 / 32)) (32 * (19 / 32 - s))) -
            min 1 (min (32 * (t - 13 / 32)) (32 * (19 / 32 - t)))| :=
      abs_max_sub_max_le_max _ _ _ _
    _ ≤ max |(0 : ℝ) - 0| (max |(1 : ℝ) - 1|
        |min (32 * (s - 13 / 32)) (32 * (19 / 32 - s)) -
          min (32 * (t - 13 / 32)) (32 * (19 / 32 - t))|) := by
      gcongr
      exact abs_min_sub_min_le_max _ _ _ _
    _ ≤ max |(0 : ℝ) - 0| (max |(1 : ℝ) - 1|
        (max |32 * (s - 13 / 32) - 32 * (t - 13 / 32)|
          |32 * (19 / 32 - s) - 32 * (19 / 32 - t)|)) := by
      gcongr
      exact abs_min_sub_min_le_max _ _ _ _
    _ = 32 * |s - t| := by
      rw [show 32 * (s - 13 / 32) - 32 * (t - 13 / 32) =
          32 * (s - t) by ring,
        show 32 * (19 / 32 - s) - 32 * (19 / 32 - t) =
          -(32 * (s - t)) by ring]
      simp [abs_mul]

lemma foldedTransverseBump_diff_le (s t : ℝ) :
    |foldedTransverseBump s - foldedTransverseBump t| ≤ 16 * |s - t| := by
  unfold foldedTransverseBump
  calc
    |max 0 (min 1 (min (16 * (s - 3 / 16)) (16 * (13 / 16 - s)))) -
        max 0 (min 1 (min (16 * (t - 3 / 16)) (16 * (13 / 16 - t))))| ≤
        max |(0 : ℝ) - 0|
          |min 1 (min (16 * (s - 3 / 16)) (16 * (13 / 16 - s))) -
            min 1 (min (16 * (t - 3 / 16)) (16 * (13 / 16 - t)))| :=
      abs_max_sub_max_le_max _ _ _ _
    _ ≤ max |(0 : ℝ) - 0| (max |(1 : ℝ) - 1|
        |min (16 * (s - 3 / 16)) (16 * (13 / 16 - s)) -
          min (16 * (t - 3 / 16)) (16 * (13 / 16 - t))|) := by
      gcongr
      exact abs_min_sub_min_le_max _ _ _ _
    _ ≤ max |(0 : ℝ) - 0| (max |(1 : ℝ) - 1|
        (max |16 * (s - 3 / 16) - 16 * (t - 3 / 16)|
          |16 * (13 / 16 - s) - 16 * (13 / 16 - t)|)) := by
      gcongr
      exact abs_min_sub_min_le_max _ _ _ _
    _ = 16 * |s - t| := by
      rw [show 16 * (s - 3 / 16) - 16 * (t - 3 / 16) =
          16 * (s - t) by ring,
        show 16 * (13 / 16 - s) - 16 * (13 / 16 - t) =
          -(16 * (s - t)) by ring]
      simp [abs_mul]

lemma abs_prod_sub_prod_le_sum_abs_sub {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι -> ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1)
    (hg : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.sum_insert ha]
      have hfs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hgs : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1 :=
        fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hpf0 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi => (hfs i hi).1
      have hpg0 : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg fun i hi => (hgs i hi).1
      have hpf1 : ∏ i ∈ s, f i ≤ 1 := Finset.prod_le_one
        (fun i hi => (hfs i hi).1) (fun i hi => (hfs i hi).2)
      have hpg1 : ∏ i ∈ s, g i ≤ 1 := Finset.prod_le_one
        (fun i hi => (hgs i hi).1) (fun i hi => (hgs i hi).2)
      calc
        |f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i| =
            |f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) +
              (f a - g a) * ∏ i ∈ s, g i| := by congr 1; ring
        _ ≤ |f a| * |∏ i ∈ s, f i - ∏ i ∈ s, g i| +
            |f a - g a| * |∏ i ∈ s, g i| := by
              simpa [abs_mul] using abs_add_le
                (f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i))
                ((f a - g a) * ∏ i ∈ s, g i)
        _ ≤ |∏ i ∈ s, f i - ∏ i ∈ s, g i| + |f a - g a| := by
          rw [abs_of_nonneg (hf a (Finset.mem_insert_self a s)).1,
            abs_of_nonneg hpg0]
          apply add_le_add
          · exact mul_le_of_le_one_left (abs_nonneg _)
              (hf a (Finset.mem_insert_self a s)).2
          · exact mul_le_of_le_one_right (abs_nonneg _) hpg1
        _ ≤ ∑ i ∈ s, |f i - g i| + |f a - g a| := by
          simpa [add_comm] using add_le_add_right (ih hfs hgs) |f a - g a|
        _ = |f a - g a| + ∑ i ∈ s, |f i - g i| := by ring

lemma coordinate_abs_sub_le_euclideanDistance (x y : XSpace d) (i : Fin d) :
    |x i - y i| ≤ euclideanDistance x y := by
  unfold euclideanDistance
  apply (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).2
  rw [sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j - y j)) (Finset.mem_univ i)

/-- A single product bump has an explicit dimension-dependent Euclidean
modulus. The factor `48*d` records one slope-32 first-coordinate factor and
at most `d` slope-16 transverse factors. -/
lemma meshBump_diff_le (hd : 0 < d) {h : ℝ} (hh : 0 < h)
    (k : Fin d -> ℕ) (x y : XSpace d) :
    |meshBump hd h k x - meshBump hd h k y| ≤
      (48 * (d : ℝ) / h) * euclideanDistance x y := by
  let z : Fin d := ⟨0, hd⟩
  let F : XSpace d -> Fin d -> ℝ := fun w i =>
    if i.val = 0 then 1 else foldedTransverseBump (w i / h - k i)
  have hF (w : XSpace d) (i : Fin d) : 0 ≤ F w i ∧ F w i ≤ 1 := by
    dsimp [F]
    split
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨foldedTransverseBump_nonneg _, foldedTransverseBump_le_one _⟩
  have hP := abs_prod_sub_prod_le_sum_abs_sub (Finset.univ : Finset (Fin d))
    (F x) (F y) (fun i _ => hF x i) (fun i _ => hF y i)
  have hcoord (i : Fin d) : |F x i - F y i| ≤
      (16 / h) * euclideanDistance x y := by
    dsimp [F]
    split
    · simp
      exact mul_nonneg (div_nonneg (by norm_num) hh.le)
        (by unfold euclideanDistance; positivity)
    · calc
        |foldedTransverseBump (x i / h - k i) -
            foldedTransverseBump (y i / h - k i)| ≤
            16 * |(x i / h - k i) - (y i / h - k i)| :=
          foldedTransverseBump_diff_le _ _
        _ = (16 / h) * |x i - y i| := by
          rw [show (x i / h - k i) - (y i / h - k i) = (x i - y i) / h by ring,
            abs_div, abs_of_pos hh]
          ring
        _ ≤ (16 / h) * euclideanDistance x y := by
          gcongr
          exact coordinate_abs_sub_le_euclideanDistance x y i
  have hP' : |∏ i : Fin d, F x i - ∏ i : Fin d, F y i| ≤
      (d : ℝ) * ((16 / h) * euclideanDistance x y) := by
    refine hP.trans ?_
    calc
      ∑ i : Fin d, |F x i - F y i| ≤
          ∑ _i : Fin d, (16 / h) * euclideanDistance x y :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * ((16 / h) * euclideanDistance x y) := by simp
  let f : XSpace d -> ℝ := fun w => foldedFirstBump (w z / h - k z)
  have hf (w : XSpace d) : 0 ≤ f w ∧ f w ≤ 1 := by
    exact ⟨foldedFirstBump_nonneg _, foldedFirstBump_le_one _⟩
  have hfdiff : |f x - f y| ≤ (32 / h) * euclideanDistance x y := by
    calc
      |f x - f y| ≤ 32 * |(x z / h - k z) - (y z / h - k z)| :=
        foldedFirstBump_diff_le _ _
      _ = (32 / h) * |x z - y z| := by
        rw [show (x z / h - k z) - (y z / h - k z) = (x z - y z) / h by ring,
          abs_div, abs_of_pos hh]
        ring
      _ ≤ (32 / h) * euclideanDistance x y := by
        gcongr
        exact coordinate_abs_sub_le_euclideanDistance x y z
  change |f x * ∏ i : Fin d, F x i - f y * ∏ i : Fin d, F y i| ≤ _
  calc
    |f x * ∏ i : Fin d, F x i - f y * ∏ i : Fin d, F y i| ≤
        |f x - f y| + |∏ i : Fin d, F x i - ∏ i : Fin d, F y i| := by
      calc
        _ = |(f x - f y) * (∏ i : Fin d, F x i) +
            f y * ((∏ i : Fin d, F x i) - ∏ i : Fin d, F y i)| := by
              congr 1
              ring
        _ ≤ |f x - f y| * |∏ i : Fin d, F x i| +
            |f y| * |(∏ i : Fin d, F x i) - ∏ i : Fin d, F y i| := by
              simpa [abs_mul] using abs_add_le
                ((f x - f y) * ∏ i : Fin d, F x i)
                (f y * ((∏ i : Fin d, F x i) - ∏ i : Fin d, F y i))
        _ ≤ _ := by
          have hprod0 : 0 ≤ ∏ i : Fin d, F x i :=
            Finset.prod_nonneg fun i _ => (hF x i).1
          have hprod1 : ∏ i : Fin d, F x i ≤ 1 := Finset.prod_le_one
            (fun i _ => (hF x i).1) (fun i _ => (hF x i).2)
          rw [abs_of_nonneg hprod0, abs_of_nonneg (hf y).1]
          exact add_le_add
            (mul_le_of_le_one_right (abs_nonneg _) hprod1)
            (mul_le_of_le_one_left (abs_nonneg _) (hf y).2)
    _ ≤ (32 / h) * euclideanDistance x y +
        (d : ℝ) * ((16 / h) * euclideanDistance x y) := add_le_add hfdiff hP'
    _ ≤ (48 * (d : ℝ) / h) * euclideanDistance x y := by
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hdist : 0 ≤ euclideanDistance x y := by unfold euclideanDistance; positivity
      field_simp
      nlinarith

/-- Disjoint support prevents the signed bump sum from accumulating the number
of cells: between two points, at most two cell bumps contribute. -/
lemma signed_bump_sum_diff_le_two {K : ℕ}
    {Q : Fin K -> Set (XSpace d)} {psi : Fin K -> XSpace d -> ℝ}
    (hdisj : ∀ i j, i ≠ j -> Disjoint (Q i) (Q j))
    (hoff : ∀ i x, x ∉ Q i -> psi i x = 0)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hdiff : ∀ i x y, |psi i x - psi i y| ≤ C * euclideanDistance x y)
    (theta : Fin K -> Bool) (x y : XSpace d) :
    |(∑ i : Fin K, localSign (theta i) * psi i x) -
      ∑ i : Fin K, localSign (theta i) * psi i y| ≤
      2 * C * euclideanDistance x y := by
  classical
  have hmem {i : Fin K} {w : XSpace d} (hi : psi i w ≠ 0) : w ∈ Q i := by
    by_contra hw
    exact hi (hoff i w hw)
  have hsum_eq {w : XSpace d} {i : Fin K} (hi : psi i w ≠ 0) :
      (∑ k : Fin K, localSign (theta k) * psi k w) =
        localSign (theta i) * psi i w := by
    rw [Finset.sum_eq_single i]
    · intro k hk hki
      have hwk : w ∉ Q k := by
        intro hw
        exact Set.disjoint_left.mp (hdisj k i hki) hw (hmem hi)
      simp [hoff k w hwk]
    · simp
  by_cases hx : ∃ i, psi i x ≠ 0
  · obtain ⟨i, hi⟩ := hx
    rw [hsum_eq hi]
    by_cases hy : ∃ j, psi j y ≠ 0
    · obtain ⟨j, hj⟩ := hy
      rw [hsum_eq hj]
      by_cases hij : i = j
      · subst j
        rw [← mul_sub, abs_mul, abs_localSign, one_mul]
        have hd0 : 0 ≤ euclideanDistance x y := by
          unfold euclideanDistance
          positivity
        exact (hdiff i x y).trans (by nlinarith [mul_nonneg hC0 hd0])
      · have hiy : psi i y = 0 := by
          apply hoff i y
          intro hyi
          exact Set.disjoint_left.mp (hdisj i j hij) hyi (hmem hj)
        have hjx : psi j x = 0 := by
          apply hoff j x
          intro hxj
          exact Set.disjoint_left.mp (hdisj j i (Ne.symm hij)) hxj (hmem hi)
        calc
          |localSign (theta i) * psi i x - localSign (theta j) * psi j y| ≤
              |psi i x| + |psi j y| := by
                calc
                  _ ≤ |localSign (theta i) * psi i x| +
                      |localSign (theta j) * psi j y| := abs_sub _ _
                  _ = _ := by
                    rw [abs_mul, abs_mul, abs_localSign, abs_localSign,
                      one_mul, one_mul]
          _ = |psi i x - psi i y| + |psi j x - psi j y| := by
            rw [hiy, hjx, sub_zero, zero_sub, abs_neg]
          _ ≤ C * euclideanDistance x y + C * euclideanDistance x y :=
            add_le_add (hdiff i x y) (hdiff j x y)
          _ = 2 * C * euclideanDistance x y := by ring
    · have hzero : ∀ j, psi j y = 0 := by push_neg at hy; exact hy
      simp_rw [hzero, mul_zero, Finset.sum_const_zero, sub_zero]
      rw [abs_mul, abs_localSign, one_mul, ← sub_zero (psi i x),
        ← hzero i]
      exact (hdiff i x y).trans (by
        have hd0 : 0 ≤ euclideanDistance x y := by unfold euclideanDistance; positivity
        nlinarith)
  · have hzero : ∀ i, psi i x = 0 := by push_neg at hx; exact hx
    simp_rw [hzero, mul_zero, Finset.sum_const_zero, zero_sub, abs_neg]
    by_cases hy : ∃ j, psi j y ≠ 0
    · obtain ⟨j, hj⟩ := hy
      rw [hsum_eq hj, abs_mul, abs_localSign, one_mul, ← sub_zero (psi j y),
        ← hzero j, abs_sub_comm]
      exact (hdiff j x y).trans (by
        have hd0 : 0 ≤ euclideanDistance x y := by unfold euclideanDistance; positivity
        nlinarith)
    · have hzero' : ∀ j, psi j y = 0 := by push_neg at hy; exact hy
      simp [hzero']
      have hd0 : 0 ≤ euclideanDistance x y := by unfold euclideanDistance; positivity
      positivity

lemma FoldedGeometry.signed_bump_sum_diff_le
    {hd : 0 < d} {q K : ℕ} {Q : Fin K -> Set (XSpace d)}
    {psi : Fin K -> XSpace d -> ℝ} {B : Fin K -> Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B)
    (theta : Fin K -> Bool) (x y : XSpace d) :
    |(∑ i : Fin K, localSign (theta i) * psi i x) -
      ∑ i : Fin K, localSign (theta i) * psi i y| ≤
      (96 * (d : ℝ) / (q : ℝ)⁻¹) * euclideanDistance x y := by
  have hh : 0 < (q : ℝ)⁻¹ := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hgeo.1
    positivity
  have hs := signed_bump_sum_diff_le_two
    (fun i j hij => hgeo.pairwise_disjoint hij)
    (fun i x hx => hgeo.bump_eq_zero_off_cell i hx)
    (C := 48 * (d : ℝ) / (q : ℝ)⁻¹)
    (by positivity)
    (by
      intro i x y
      rcases hgeo with ⟨hq, idx, hinj, hcomplete, hdefs⟩
      rw [(hdefs i).2.1]
      exact meshBump_diff_le hd hh (idx i) x y)
    theta x y
  convert hs using 1 <;> ring

end CausalSmith.Experimentation.PilotscorePairingFrontier
