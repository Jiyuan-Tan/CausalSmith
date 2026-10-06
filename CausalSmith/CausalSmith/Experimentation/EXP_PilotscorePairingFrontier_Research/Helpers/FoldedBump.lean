module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Basic

/-! # Elementary bounds for the folded mesh bumps -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

lemma foldedFirstBump_nonneg (t : ℝ) : 0 ≤ foldedFirstBump t := by
  simp [foldedFirstBump]

lemma foldedFirstBump_le_one (t : ℝ) : foldedFirstBump t ≤ 1 := by
  simp only [foldedFirstBump]
  exact max_le (by norm_num) (min_le_left _ _)

lemma foldedFirstBump_eq_zero_of_le {t : ℝ} (ht : t ≤ 13 / 32) :
    foldedFirstBump t = 0 := by
  simp only [foldedFirstBump]
  have : 32 * (t - 13 / 32) ≤ 0 := by linarith
  have hmin : min 1 (min (32 * (t - 13 / 32)) (32 * (19 / 32 - t))) ≤ 0 :=
    le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) this
  exact max_eq_left hmin

lemma foldedFirstBump_eq_zero_of_ge {t : ℝ} (ht : 19 / 32 ≤ t) :
    foldedFirstBump t = 0 := by
  simp only [foldedFirstBump]
  have : 32 * (19 / 32 - t) ≤ 0 := by linarith
  have hmin : min 1 (min (32 * (t - 13 / 32)) (32 * (19 / 32 - t))) ≤ 0 :=
    le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) this
  exact max_eq_left hmin

lemma foldedFirstBump_eq_one {t : ℝ} (hlo : 7 / 16 ≤ t) (hhi : t ≤ 9 / 16) :
    foldedFirstBump t = 1 := by
  simp only [foldedFirstBump]
  have hl : 1 ≤ 32 * (t - 13 / 32) := by linarith
  have hr : 1 ≤ 32 * (19 / 32 - t) := by linarith
  rw [min_eq_left (le_min hl hr), max_eq_right zero_le_one]

lemma foldedFirstBump_eq_ramp_up {t : ℝ}
    (hlo : 13 / 32 ≤ t) (hhi : t ≤ 7 / 16) :
    foldedFirstBump t = 32 * (t - 13 / 32) := by
  unfold foldedFirstBump
  have h0 : 0 ≤ 32 * (t - 13 / 32) := by linarith
  have h1 : 32 * (t - 13 / 32) ≤ 1 := by linarith
  have hcross : 32 * (t - 13 / 32) ≤ 32 * (19 / 32 - t) := by linarith
  rw [min_eq_left hcross, min_eq_right h1, max_eq_right h0]

lemma foldedFirstBump_eq_ramp_down {t : ℝ}
    (hlo : 9 / 16 ≤ t) (hhi : t ≤ 19 / 32) :
    foldedFirstBump t = 32 * (19 / 32 - t) := by
  unfold foldedFirstBump
  have h0 : 0 ≤ 32 * (19 / 32 - t) := by linarith
  have h1 : 32 * (19 / 32 - t) ≤ 1 := by linarith
  have hcross : 32 * (19 / 32 - t) ≤ 32 * (t - 13 / 32) := by linarith
  rw [min_eq_right hcross, min_eq_right h1, max_eq_right h0]

lemma foldedFirstBump_support {t : ℝ} (ht : foldedFirstBump t ≠ 0) :
    13 / 32 < t ∧ t < 19 / 32 := by
  constructor
  · by_contra h
    exact ht (foldedFirstBump_eq_zero_of_le (le_of_not_gt h))
  · by_contra h
    exact ht (foldedFirstBump_eq_zero_of_ge (le_of_not_gt h))

lemma foldedTransverseBump_nonneg (t : ℝ) : 0 ≤ foldedTransverseBump t := by
  simp [foldedTransverseBump]

lemma foldedTransverseBump_le_one (t : ℝ) : foldedTransverseBump t ≤ 1 := by
  simp only [foldedTransverseBump]
  exact max_le (by norm_num) (min_le_left _ _)

lemma foldedTransverseBump_eq_zero_of_le {t : ℝ} (ht : t ≤ 3 / 16) :
    foldedTransverseBump t = 0 := by
  simp only [foldedTransverseBump]
  have : 16 * (t - 3 / 16) ≤ 0 := by linarith
  have hmin : min 1 (min (16 * (t - 3 / 16)) (16 * (13 / 16 - t))) ≤ 0 :=
    le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) this
  exact max_eq_left hmin

lemma foldedTransverseBump_eq_zero_of_ge {t : ℝ} (ht : 13 / 16 ≤ t) :
    foldedTransverseBump t = 0 := by
  simp only [foldedTransverseBump]
  have : 16 * (13 / 16 - t) ≤ 0 := by linarith
  have hmin : min 1 (min (16 * (t - 3 / 16)) (16 * (13 / 16 - t))) ≤ 0 :=
    le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) this
  exact max_eq_left hmin

lemma foldedTransverseBump_eq_one {t : ℝ} (hlo : 1 / 4 ≤ t) (hhi : t ≤ 3 / 4) :
    foldedTransverseBump t = 1 := by
  simp only [foldedTransverseBump]
  have hl : 1 ≤ 16 * (t - 3 / 16) := by linarith
  have hr : 1 ≤ 16 * (13 / 16 - t) := by linarith
  rw [min_eq_left (le_min hl hr), max_eq_right zero_le_one]

lemma foldedTransverseBump_support {t : ℝ} (ht : foldedTransverseBump t ≠ 0) :
    3 / 16 < t ∧ t < 13 / 16 := by
  constructor
  · by_contra h
    exact ht (foldedTransverseBump_eq_zero_of_le (le_of_not_gt h))
  · by_contra h
    exact ht (foldedTransverseBump_eq_zero_of_ge (le_of_not_gt h))

lemma meshBump_nonneg (hd : 0 < d) (h : ℝ) (k : Fin d → ℕ) (x : XSpace d) :
    0 ≤ meshBump hd h k x := by
  unfold meshBump
  apply mul_nonneg (foldedFirstBump_nonneg _)
  exact Finset.prod_nonneg fun i _ => by
    split
    · norm_num
    · exact foldedTransverseBump_nonneg _

lemma meshBump_le_one (hd : 0 < d) (h : ℝ) (k : Fin d → ℕ) (x : XSpace d) :
    meshBump hd h k x ≤ 1 := by
  unfold meshBump
  have hp0 : 0 ≤ ∏ i : Fin d, if i.val = 0 then (1 : ℝ)
      else foldedTransverseBump (x i / h - k i) :=
    Finset.prod_nonneg fun i _ => by
      split
      · norm_num
      · exact foldedTransverseBump_nonneg _
  have hp1 : (∏ i : Fin d, if i.val = 0 then (1 : ℝ)
      else foldedTransverseBump (x i / h - k i)) ≤ 1 := by
    apply Finset.prod_le_one
    · exact fun i _ => by
        split
        · norm_num
        · exact foldedTransverseBump_nonneg _
    · exact fun i _ => by
        split
        · norm_num
        · exact foldedTransverseBump_le_one _
  nlinarith [foldedFirstBump_nonneg (x ⟨0, hd⟩ / h - k ⟨0, hd⟩),
    foldedFirstBump_le_one (x ⟨0, hd⟩ / h - k ⟨0, hd⟩)]

lemma meshBump_eq_one_on_core (hd : 0 < d) {h : ℝ} (hh : 0 < h)
    (k : Fin d → ℕ) {x : XSpace d} (hx : x ∈ meshCore hd h k) :
    meshBump hd h k x = 1 := by
  have hfirstlo : (7 / 16 : ℝ) ≤ x ⟨0, hd⟩ / h - k ⟨0, hd⟩ := by
    apply (le_sub_iff_add_le).2
    apply (le_div_iff₀ hh).2
    simpa [add_mul, add_comm] using hx.2.1
  have hfirsthi : x ⟨0, hd⟩ / h - k ⟨0, hd⟩ ≤ (9 / 16 : ℝ) := by
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ hh).2
    simpa [add_mul, add_comm] using hx.2.2.1
  have htrans (i : Fin d) (hi : i.val ≠ 0) :
      foldedTransverseBump (x i / h - k i) = 1 := by
    have hlo : (1 / 4 : ℝ) ≤ x i / h - k i := by
      apply (le_sub_iff_add_le).2
      apply (le_div_iff₀ hh).2
      simpa [add_mul, add_comm] using (hx.2.2.2 i hi).1
    have hhi : x i / h - k i ≤ (3 / 4 : ℝ) := by
      apply (sub_le_iff_le_add).2
      apply (div_le_iff₀ hh).2
      simpa [add_mul, add_comm] using (hx.2.2.2 i hi).2
    exact foldedTransverseBump_eq_one hlo hhi
  unfold meshBump
  rw [foldedFirstBump_eq_one hfirstlo hfirsthi, one_mul]
  apply Finset.prod_eq_one
  intro i hi
  split
  · rfl
  · exact htrans i ‹i.val ≠ 0›

lemma meshBump_eq_zero_off_cube (hd : 0 < d) (q : ℕ) (hq : 0 < q)
    (k : Fin d → ℕ) (hk : ∀ i, k i < q) {x : XSpace d}
    (hx : x ∉ meshCube ((q : ℝ)⁻¹) k) :
    meshBump hd ((q : ℝ)⁻¹) k x = 0 := by
  classical
  by_contra hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : (0 : ℝ) < (q : ℝ)⁻¹ := inv_pos.mpr hqR
  have hmul := (mul_ne_zero_iff.mp hb)
  have hfirst := foldedFirstBump_support hmul.1
  have hprod : ∀ i : Fin d,
      (if i.val = 0 then (1 : ℝ)
       else foldedTransverseBump (x i / (q : ℝ)⁻¹ - k i)) ≠ 0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp hmul.2) i (Finset.mem_univ i)
  have hcoord (i : Fin d) :
      (k i : ℝ) * (q : ℝ)⁻¹ ≤ x i ∧
        x i < ((k i : ℝ) + 1) * (q : ℝ)⁻¹ := by
    by_cases hi : i.val = 0
    · have hieq : i = ⟨0, hd⟩ := Fin.ext hi
      subst i
      constructor
      · have h := (lt_sub_iff_add_lt.mp hfirst.1)
        have h' := (lt_div_iff₀ hh).mp h
        nlinarith
      · have h := (sub_lt_iff_lt_add.mp hfirst.2)
        have h' := (div_lt_iff₀ hh).mp h
        nlinarith
    · have htne : foldedTransverseBump
          (x i / (q : ℝ)⁻¹ - k i) ≠ 0 := by
        simpa [hi] using hprod i
      have ht := foldedTransverseBump_support htne
      constructor
      · have h := (lt_sub_iff_add_lt.mp ht.1)
        have h' := (lt_div_iff₀ hh).mp h
        nlinarith
      · have h := (sub_lt_iff_lt_add.mp ht.2)
        have h' := (div_lt_iff₀ hh).mp h
        nlinarith
  apply hx
  constructor
  · intro i
    constructor
    · exact le_trans (by positivity : 0 ≤ (k i : ℝ) * (q : ℝ)⁻¹) (hcoord i).1
    · have hki : (k i : ℝ) + 1 ≤ q := by
        exact_mod_cast Nat.succ_le_of_lt (hk i)
      have hone : ((k i : ℝ) + 1) * (q : ℝ)⁻¹ ≤ 1 := by
        calc
          ((k i : ℝ) + 1) * (q : ℝ)⁻¹ ≤ (q : ℝ) * (q : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right hki hh.le
          _ = 1 := mul_inv_cancel₀ hqR.ne'
      exact (hcoord i).2.le.trans hone
  · intro i
    exact ⟨(hcoord i).1, Or.inl (hcoord i).2⟩

end CausalSmith.Experimentation.PilotscorePairingFrontier
