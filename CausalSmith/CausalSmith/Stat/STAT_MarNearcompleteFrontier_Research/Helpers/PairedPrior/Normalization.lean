module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.PairedPrior.Atoms

/-! # Exact normalization and positivity of constructed full laws -/

@[expose] public section
namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators ENNReal NNReal

-- @node: ell_pos_for_normalization
/-- Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma ell_pos_for_normalization (n : ℕ) : 0 < ell n := by
  unfold ell
  have h : (1 : ℝ) < Real.exp 1 + n := by
    have he : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  exact Real.log_pos h

-- @node: priorK_lower_for_normalization
/-- Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma priorK_lower_for_normalization (n : ℕ) :
    8 * ell n ≤ (priorK n : ℝ) := by
  unfold priorK
  exact Nat.le_ceil _

-- @node: priorH_le_one_for_normalization
/-- Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma priorH_le_one_for_normalization (n : ℕ) : priorH n ≤ 1 := by
  have h : (1 : ℝ) ≤ priorK n := by
    have he := ell_pos_for_normalization n
    have hk := priorK_lower_for_normalization n
    have hkpos : (0 : ℝ) < priorK n := by linarith
    have hkposNat : 0 < priorK n := by exact_mod_cast hkpos
    exact_mod_cast (show 1 ≤ priorK n by omega)
  unfold priorH
  have hk : (1 : ℝ) ≤ priorK n := by exact_mod_cast h
  have hi : (priorK n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hk
  have hnonneg : (0 : ℝ) ≤ (priorK n : ℝ)⁻¹ := by positivity
  nlinarith

-- @node: interpolationNode_nonneg_for_normalization
/-- Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `i`](hyp:i). -/
lemma interpolationNode_nonneg_for_normalization (n : ℕ) (i : Fin (priorK n)) :
    0 ≤ interpolationNode n i := by
  have hh : 0 ≤ priorH n := by unfold priorH; positivity
  have hh1 := priorH_le_one_for_normalization n
  have hc := Real.neg_one_le_cos ((i : ℝ) * Real.pi / ((priorK n - 1 : ℕ) : ℝ))
  unfold interpolationNode
  nlinarith

/-- For [positive sample size](hyp:hn), [positive covariate dimension](hyp:hd), and [an arrival floor in the admissible range](hyp:hq), [the normalization constant is strictly positive](goal). -/
lemma normalizationJ_pos (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (θ : Theta n d) :
    0 < normalizationJ n d θ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hL := ell_pos_for_normalization n
  have hK := priorK_lower_for_normalization n
  have hKpos : (0 : ℝ) < priorK n := by linarith
  have hM : (pairCount n d : ℝ) ≤ (n : ℝ) * ell n := by
    have hm : pairCount n d ≤ Nat.floor ((n : ℝ) * ell n) := by
      unfold pairCount
      exact min_le_right _ _
    have hf : ((Nat.floor ((n : ℝ) * ell n) : ℕ) : ℝ) ≤ (n : ℝ) * ell n :=
      Nat.floor_le (le_of_lt (mul_pos hnpos hL))
    exact (Nat.cast_le.mpr hm).trans hf
  have hMnonneg : (0 : ℝ) ≤ pairCount n d := Nat.cast_nonneg _
  have hbound : 8 * (pairCount n d : ℝ) ≤ (n : ℝ) * priorK n := by
    nlinarith [mul_nonneg (le_of_lt hnpos) (sub_nonneg.mpr hK)]
  have hsmall : (pairCount n d : ℝ) / (512 * n * priorK n) < 1 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hrewrite :
      2 * (pairCount n d : ℝ) * priorH n * priorB n =
        (pairCount n d : ℝ) / (512 * n * priorK n) := by
    unfold priorH priorB
    field_simp
    <;> ring
  have hfiller : 0 < fillerMass n d := by
    unfold fillerMass
    rw [hrewrite]
    linarith
  have hsum : 0 ≤ ∑ j : Fin (pairCount n d), latentP n (θ.1 j) := by
    apply Finset.sum_nonneg
    intro j hj
    unfold latentP
    split
    · exact mul_nonneg (by unfold priorB; positivity)
        (interpolationNode_nonneg_for_normalization n _)
    · positivity
  unfold normalizationJ
  nlinarith

/-- For [an arrival floor in the admissible range](hyp:hq), [the associated baseline mean lies between zero and one](goal). -/
lemma baseMean_mem_unit (q : ℝ) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    baseMean q ∈ Set.Icc 0 1 := by
  rcases hq with ⟨hq0, hq1⟩
  have hqpos : 0 < q := by linarith
  unfold baseMean delta
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < 2 * q)).mpr
    nlinarith [sq_nonneg (q - 1)]

-- @node: fillerAtomWeight_nonneg
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `w`](hyp:w), [the stated mathematical conclusion holds](goal). Given [the specified input `θ`](hyp:θ). Given [the specified input `hq`](hyp:hq). -/
lemma fillerAtomWeight_nonneg (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (θ : Theta n d) (w : FullAtom d) :
    0 ≤ fillerAtomWeight n d q hd θ w := by
  have hJ := normalizationJ_pos n d q hn hd hq θ
  have hf : 0 ≤ fillerMass n d := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hL := ell_pos_for_normalization n
    have hK := priorK_lower_for_normalization n
    have hKpos : (0 : ℝ) < priorK n := by linarith
    have hM : (pairCount n d : ℝ) ≤ (n : ℝ) * ell n := by
      have hm : pairCount n d ≤ Nat.floor ((n : ℝ) * ell n) := by
        unfold pairCount
        exact min_le_right _ _
      have hf : ((Nat.floor ((n : ℝ) * ell n) : ℕ) : ℝ) ≤
          (n : ℝ) * ell n := Nat.floor_le (le_of_lt (mul_pos hnpos hL))
      exact (Nat.cast_le.mpr hm).trans hf
    have hbound : 8 * (pairCount n d : ℝ) ≤ (n : ℝ) * priorK n := by
      nlinarith [mul_nonneg (le_of_lt hnpos) (sub_nonneg.mpr hK)]
    have hrewrite :
        2 * (pairCount n d : ℝ) * priorH n * priorB n =
          (pairCount n d : ℝ) / (512 * n * priorK n) := by
      unfold priorH priorB
      field_simp
      <;> ring
    unfold fillerMass
    rw [hrewrite]
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  by_cases h : w.X = fillerLabel d hd ∧ w.S0 = false ∧ w.S1 = false ∧
      w.S = false ∧ w.Y0 = false ∧ w.Y = (if w.A then w.Y1 else w.Y0) ∧
      w.R = true
  · simp only [fillerAtomWeight, if_pos h]
    exact mul_nonneg
      (div_nonneg (div_nonneg hf (le_of_lt hJ)) (by norm_num))
      (bernoulliFactor_nonneg _ (baseMean_mem_unit q hq) _)
  · simp only [fillerAtomWeight, if_neg h]
    norm_num

-- @node: pairedAtomWeight_nonneg
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `w`](hyp:w), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `hq`](hyp:hq), [the specified input `hσ`](hyp:hσ). -/
lemma pairedAtomWeight_nonneg (n d : ℕ) (q σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ ∈ Set.Icc (-1) 1) (θ : Theta n d) (w : FullAtom d) :
    0 ≤ pairedAtomWeight n d q σ hd θ w := by
  unfold pairedAtomWeight
  apply add_nonneg (fillerAtomWeight_nonneg n d q hn hd hq θ w)
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro side _
  exact pairAtomWeight_nonneg n d q σ hd hq hσ θ
    (normalizationJ_pos n d q hn hd hq θ) j side w


-- @node: fullAtomTuple
/-- Given [the specified input `d`](hyp:d), [the stated mathematical conclusion holds](goal). -/
abbrev fullAtomTuple (d : ℕ) :=
  Fin d × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool

-- @node: fullAtomTupleEquiv
/-- Given [the specified input `d`](hyp:d), [the stated mathematical conclusion holds](goal). -/
def fullAtomTupleEquiv (d : ℕ) : FullAtom d ≃ fullAtomTuple d where
  toFun w := (w.X, w.S0, w.S1, w.Y0, w.Y1, w.A, w.S, w.Y, w.R)
  invFun t := ⟨⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1⟩,
    t.2.2.2.2.2.1, t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.1,
    t.2.2.2.2.2.2.2.2⟩
  left_inv := by intro w; rcases w with ⟨⟨x,s0,s1,y0,y1⟩,a,s,y,r⟩; rfl
  right_inv := by
    intro t
    rcases t with ⟨x,s0,s1,y0,y1,a,s,y,r⟩
    rfl

-- @node: sum_fillerAtomWeight
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `θ`](hyp:θ). -/
lemma sum_fillerAtomWeight (n d : ℕ) (q : ℝ) (hd : 1 ≤ d) (θ : Theta n d) :
    (∑ w : FullAtom d, fillerAtomWeight n d q hd θ w) =
      fillerMass n d / normalizationJ n d θ := by
  rw [Fintype.sum_equiv (fullAtomTupleEquiv d)
    (fillerAtomWeight n d q hd θ)
    (fun t => fillerAtomWeight n d q hd θ ((fullAtomTupleEquiv d).symm t))
    (by intro w; simp)]
  simp only [Fintype.sum_prod_type]
  simp [fullAtomTupleEquiv, fillerAtomWeight, bernoulliFactor, fillerLabel,
    FullAtom.X]
  calc
    _ = ∑ x : Fin d, if x = ⟨0, hd⟩ then
          fillerMass n d * (normalizationJ n d θ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = ⟨0, hd⟩ <;> simp [hx] <;> ring
    _ = _ := by simp [div_eq_mul_inv]

-- @node: sum_pairAtomWeight
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `side`](hyp:side), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `j`](hyp:j). -/
lemma sum_pairAtomWeight (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d) (θ : Theta n d)
    (j : Fin (pairCount n d)) (side : Bool) :
    (∑ w : FullAtom d, pairAtomWeight n d q σ hd θ j side w) =
      latentP n (θ.1 j) / normalizationJ n d θ := by
  rw [Fintype.sum_equiv (fullAtomTupleEquiv d)
    (pairAtomWeight n d q σ hd θ j side)
    (fun t => pairAtomWeight n d q σ hd θ j side ((fullAtomTupleEquiv d).symm t))
    (by intro w; simp)]
  simp only [Fintype.sum_prod_type]
  simp [fullAtomTupleEquiv, pairAtomWeight, bernoulliFactor, FullAtom.X,
    FullAtom.S0, FullAtom.S1, FullAtom.Y0, FullAtom.Y1]
  calc
    _ = ∑ x : Fin d, if x = pairLabel n d hd j side then
          latentP n (θ.1 j) / normalizationJ n d θ else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = pairLabel n d hd j side <;> simp [hx] <;> ring
    _ = _ := by simp

-- @node: sum_fillerAtomWeight_arm
/-- Each treatment arm receives half the normalized filler mass. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `a`](hyp:a), [the stated mathematical conclusion holds](goal). Given [the specified input `θ`](hyp:θ). -/
lemma sum_fillerAtomWeight_arm (n d : ℕ) (q : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) (a : Bool) :
    (∑ w : FullAtom d, if w.A = a then fillerAtomWeight n d q hd θ w else 0) =
      fillerMass n d / normalizationJ n d θ / 2 := by
  rw [Fintype.sum_equiv (fullAtomTupleEquiv d)
    (fun w => if w.A = a then fillerAtomWeight n d q hd θ w else 0)
    (fun t => if ((fullAtomTupleEquiv d).symm t).A = a then
      fillerAtomWeight n d q hd θ ((fullAtomTupleEquiv d).symm t) else 0)
    (by intro w; simp)]
  simp only [Fintype.sum_prod_type]
  simp [fullAtomTupleEquiv, fillerAtomWeight, bernoulliFactor, fillerLabel,
    FullAtom.X]
  cases a <;> simp [Finset.sum_add_distrib] <;> ring

-- @node: sum_pairAtomWeight_arm
/-- Each treatment arm receives half the normalized mass of an oriented pair label. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `side`](hyp:side), [the specified input `a`](hyp:a), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `j`](hyp:j). -/
lemma sum_pairAtomWeight_arm (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) (j : Fin (pairCount n d)) (side a : Bool) :
    (∑ w : FullAtom d, if w.A = a then
      pairAtomWeight n d q σ hd θ j side w else 0) =
      latentP n (θ.1 j) / normalizationJ n d θ / 2 := by
  rw [Fintype.sum_equiv (fullAtomTupleEquiv d)
    (fun w => if w.A = a then pairAtomWeight n d q σ hd θ j side w else 0)
    (fun t => if ((fullAtomTupleEquiv d).symm t).A = a then
      pairAtomWeight n d q σ hd θ j side ((fullAtomTupleEquiv d).symm t) else 0)
    (by intro w; simp)]
  simp only [Fintype.sum_prod_type]
  simp [fullAtomTupleEquiv, pairAtomWeight, bernoulliFactor, FullAtom.X,
    FullAtom.S0, FullAtom.S1, FullAtom.Y0, FullAtom.Y1]
  cases a <;> simp [Finset.sum_add_distrib] <;> ring

-- @node: sum_pairedAtomWeight_real
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `hq`](hyp:hq). -/
lemma sum_pairedAtomWeight_real (n d : ℕ) (q σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (θ : Theta n d) :
    (∑ w : FullAtom d, pairedAtomWeight n d q σ hd θ w) = 1 := by
  have hJ : normalizationJ n d θ ≠ 0 :=
    ne_of_gt (normalizationJ_pos n d q hn hd hq θ)
  calc
    _ = (∑ w : FullAtom d, fillerAtomWeight n d q hd θ w) +
        ∑ j : Fin (pairCount n d), ∑ side : Bool,
          ∑ w : FullAtom d, pairAtomWeight n d q σ hd θ j side w := by
            simp only [pairedAtomWeight, Finset.sum_add_distrib]
            rw [Finset.sum_comm]
            apply congrArg₂ (· + ·) rfl
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_comm]
    _ = fillerMass n d / normalizationJ n d θ +
        ∑ j : Fin (pairCount n d), ∑ side : Bool,
          latentP n (θ.1 j) / normalizationJ n d θ := by
            rw [sum_fillerAtomWeight]
            simp_rw [sum_pairAtomWeight]
    _ = 1 := by
      simp_rw [Fintype.sum_bool]
      simp_rw [← add_div]
      rw [← Finset.sum_div, ← add_div]
      have hsum : (∑ j : Fin (pairCount n d),
          (latentP n (θ.1 j) + latentP n (θ.1 j))) =
          2 * ∑ j : Fin (pairCount n d), latentP n (θ.1 j) := by
        rw [Finset.sum_add_distrib]
        ring
      rw [hsum]
      change normalizationJ n d θ / normalizationJ n d θ = 1
      exact div_self hJ

-- @node: pairedAtomWeight_sum
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `hq`](hyp:hq), [the specified input `hσ`](hyp:hσ). -/
lemma pairedAtomWeight_sum (n d : ℕ) (q σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ ∈ Set.Icc (-1) 1) (θ : Theta n d) :
    (∑ w : FullAtom d, ENNReal.ofReal (pairedAtomWeight n d q σ hd θ w)) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ =>
    pairedAtomWeight_nonneg n d q σ hn hd hq hσ θ w)]
  rw [sum_pairedAtomWeight_real n d q σ hn hd hq θ]
  norm_num


end CausalSmith.Stat.MarNearcompleteFrontier
