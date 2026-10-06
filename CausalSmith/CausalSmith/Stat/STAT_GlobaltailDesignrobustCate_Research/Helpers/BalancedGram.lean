module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Estimators

/-! # Deterministic lower bound for the balanced Gram matrix -/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open scoped BigOperators Matrix

-- @node: outerQuadraticForm
lemma outerQuadraticForm {ι : Type} [Fintype ι]
    (v a : ι → ℝ) :
    quadraticForm (fun i j => v i * v j : Matrix ι ι ℝ) a =
      (∑ i, a i * v i) ^ 2 := by
  calc
    _ = ∑ i, (a i * v i) * (∑ j, v j * a j) := by
      simp [quadraticForm, Finset.mul_sum, mul_assoc]
    _ = (∑ i, a i * v i) ^ 2 := by
      rw [← Finset.sum_mul, sq]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

-- @node: quadraticFormSub
lemma quadraticFormSub {ι : Type} [Fintype ι]
    (G H : ι → ι → ℝ) (a : ι → ℝ) :
    quadraticForm (G - H) a = quadraticForm G a - quadraticForm H a := by
  simp [quadraticForm, Pi.sub_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib]

-- @node: referenceGramQuadraticForm
lemma referenceGramQuadraticForm (d m : ℕ)
    (a : MultiIndex d m → ℝ) :
    quadraticForm (referenceGram d m) a =
      (Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
        ∑ ℓ : MultiIndex d m,
          quadraticForm
            (fun i j => monomial d m (normingNode d m ℓ) i *
              monomial d m (normingNode d m ℓ) j :
              Matrix (MultiIndex d m) (MultiIndex d m) ℝ) a := by
  simp only [quadraticForm, referenceGram, Finset.mul_sum,
    Finset.sum_mul]
  let f : MultiIndex d m → MultiIndex d m → MultiIndex d m → ℝ :=
    fun i j ℓ => a i * ((Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
      (monomial d m (normingNode d m ℓ) i *
      monomial d m (normingNode d m ℓ) j)) * a j
  change (∑ i, ∑ j, ∑ ℓ, f i j ℓ) = _
  have hrotate : (∑ i, ∑ j, ∑ ℓ, f i j ℓ) =
      ∑ ℓ, ∑ i, ∑ j, f i j ℓ := by
    calc
      _ = ∑ i, ∑ ℓ, ∑ j, f i j ℓ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  rw [hrotate]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [f]
  ring

-- @node: rotateFourFiniteSums
lemma rotateFourFiniteSums {A B C D : Type} [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] (f : A → B → C → D → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := by rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_comm]

-- @node: balancedGramQuadraticForm
lemma balancedGramQuadraticForm {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ)
    (Q : Fin d → Fin (2 ^ j)) (a : MultiIndex d m → ℝ) :
    quadraticForm (balancedGram sample arm j m ε Q) a = (by
      classical
      exact
      (Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
        ∑ ℓ : MultiIndex d m,
          (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹ *
            ∑ i : Fin n,
              if (sample i).2.1 = arm ∧
                (sample i).1 ∈ scaledSubcell d j m ε Q ℓ then
                quadraticForm
                  (fun r s =>
                    monomial d m (fun k => ((sample i).1 k - cellOrigin d j Q k) /
                      dyadicWidth j) r *
                    monomial d m (fun k => ((sample i).1 k - cellOrigin d j Q k) /
                      dyadicWidth j) s : Matrix (MultiIndex d m) (MultiIndex d m) ℝ) a
              else 0) := by
  classical
  simp only [quadraticForm, balancedGram, Finset.mul_sum,
    Finset.sum_mul]
  let f : MultiIndex d m → MultiIndex d m → MultiIndex d m → Fin n → ℝ :=
    fun r s ℓ i => a r *
      ((Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
        ((subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹ *
          if (sample i).2.1 = arm ∧ (sample i).1 ∈ scaledSubcell d j m ε Q ℓ then
            monomial d m (fun k => ((sample i).1 k - cellOrigin d j Q k) /
              dyadicWidth j) r *
            monomial d m (fun k => ((sample i).1 k - cellOrigin d j Q k) /
              dyadicWidth j) s
          else 0)) * a s
  change (∑ r, ∑ s, ∑ ℓ, ∑ i, f r s ℓ i) = _
  rw [rotateFourFiniteSums f]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : (sample i).2.1 = arm ∧
      (sample i).1 ∈ scaledSubcell d j m ε Q ℓ
  · simp only [if_pos h]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    dsimp [f]
    rw [if_pos h]
    ring
  · simp [f, h]

-- @node: referenceLowerEigenvalueBound
lemma referenceLowerEigenvalueBound (d m : ℕ)
    (a : MultiIndex d m → ℝ) :
    referenceLowerEigenvalue d m * (∑ i, (a i) ^ 2) ≤
      quadraticForm (referenceGram d m) a := by
  have hnonneg (b : MultiIndex d m → ℝ) :
      0 ≤ quadraticForm (referenceGram d m) b := by
    rw [referenceGramQuadraticForm]
    simp_rw [outerQuadraticForm]
    positivity
  let S : Set ℝ := {c | ∀ b : MultiIndex d m → ℝ,
    c * (∑ i, (b i) ^ 2) ≤ quadraticForm (referenceGram d m) b}
  have hS : S.Nonempty := ⟨0, by
    intro b
    simpa using hnonneg b⟩
  change sSup S * (∑ i, (a i) ^ 2) ≤ _
  by_cases hz : (∑ i, (a i) ^ 2) = 0
  · simpa [hz] using hnonneg a
  have hs : 0 < (∑ i, (a i) ^ 2) :=
    lt_of_le_of_ne (by positivity) (Ne.symm hz)
  have hupper : ∀ c ∈ S,
      c ≤ quadraticForm (referenceGram d m) a / (∑ i, (a i) ^ 2) := by
    intro c hc
    exact (le_div_iff₀ hs).2 (hc a)
  exact (le_div_iff₀ hs).1 (csSup_le hS hupper)

-- @node: normalizedSelectedSumLower
lemma normalizedSelectedSumLower {n : ℕ} (p : Fin n → Prop)
    [DecidablePred p] (N : ℕ) (hN : 0 < N)
    (hcount : N = ∑ i : Fin n, if p i then 1 else 0)
    (f : Fin n → ℝ) (c : ℝ) (hf : ∀ i, p i → c ≤ f i) :
    c ≤ (N : ℝ)⁻¹ * ∑ i : Fin n, if p i then f i else 0 := by
  have hsum : (N : ℝ) * c ≤ ∑ i : Fin n, if p i then f i else 0 := by
    calc
      _ = ∑ i : Fin n, if p i then c else 0 := by
        rw [hcount]
        push_cast
        simp [Finset.sum_ite]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs with hp
        · exact hf i hp
        · exact le_refl _
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmul := mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hNreal))
  calc
    c = (N : ℝ)⁻¹ * ((N : ℝ) * c) := by field_simp
    _ ≤ _ := hmul

-- @node: armBalanced_gram
/-- Every occupied cell has a uniformly coercive balanced empirical Gram
matrix, regardless of the within-subcell design distribution. -/
lemma armBalanced_gram {d n : ℕ} (sample : Fin n → Obs d) (arm : Bool) (j : ℕ) (β : ℝ)
    (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q) :
    ∀ a : MultiIndex d (polynomialOrder β) → ℝ,
      referenceLowerEigenvalue d (polynomialOrder β) / 2 *
        (∑ i, (a i) ^ 2) ≤
      quadraticForm (balancedGram sample arm j (polynomialOrder β)
        (normingSubcells d β).radius Q) a := by
  classical
  intro a
  let m := polynomialOrder β
  let ε := (normingSubcells d β).radius
  let lam := referenceLowerEigenvalue d m
  let A := ∑ i, (a i) ^ 2
  have hsub (ℓ : MultiIndex d m) :
      0 < subcellCount sample arm j m ε Q ℓ := by
    have hle : minimumCellCount sample arm j m ε Q ≤
        subcellCount sample arm j m ε Q ℓ := by
      exact Finset.inf'_le (fun t => subcellCount sample arm j m ε Q t)
        (by simp : ℓ ∈ (Finset.univ : Finset (MultiIndex d m)))
    exact lt_of_lt_of_le hcount hle
  let b : ℝ := lam / 2 * A
  let nodeQ (ℓ : MultiIndex d m) : ℝ :=
    quadraticForm
      (fun r s => monomial d m (normingNode d m ℓ) r *
        monomial d m (normingNode d m ℓ) s : Matrix (MultiIndex d m) (MultiIndex d m) ℝ) a
  let sampleQ (i : Fin n) : ℝ :=
    quadraticForm
      (fun r s => monomial d m
        (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j) r *
        monomial d m
        (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j) s :
        Matrix (MultiIndex d m) (MultiIndex d m) ℝ) a
  have hpoint (ℓ : MultiIndex d m) (i : Fin n)
      (hi : (sample i).2.1 = arm ∧
        (sample i).1 ∈ scaledSubcell d j m ε Q ℓ) :
      nodeQ ℓ - b ≤ sampleQ i := by
    have hosc := (normingSubcells d β).oscillation ℓ
      (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j)
      hi.2.2 a
    change |quadraticForm
      ((fun r s => monomial d m
        (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j) r *
        monomial d m
        (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j) s :
        Matrix (MultiIndex d m) (MultiIndex d m) ℝ) -
       (fun r s => monomial d m (normingNode d m ℓ) r *
         monomial d m (normingNode d m ℓ) s :
         Matrix (MultiIndex d m) (MultiIndex d m) ℝ)) a| ≤ b at hosc
    rw [quadraticFormSub] at hosc
    have hlow := (abs_le.mp hosc).1
    change -b ≤ sampleQ i - nodeQ ℓ at hlow
    linarith
  have havg (ℓ : MultiIndex d m) :
      nodeQ ℓ - b ≤
        (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹ *
          ∑ i : Fin n,
            if (sample i).2.1 = arm ∧
              (sample i).1 ∈ scaledSubcell d j m ε Q ℓ then
              sampleQ i else 0 := by
    classical
    apply normalizedSelectedSumLower
      (fun i => (sample i).2.1 = arm ∧
        (sample i).1 ∈ scaledSubcell d j m ε Q ℓ)
      (subcellCount sample arm j m ε Q ℓ) (hsub ℓ)
    · rfl
    · intro i hi
      exact hpoint ℓ i hi
  have hrank : (0 : ℝ) < Fintype.card (MultiIndex d m) := by
    exact_mod_cast Fintype.card_pos
  have hsum :
      (Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
        (∑ ℓ : MultiIndex d m, (nodeQ ℓ - b)) ≤
      quadraticForm (balancedGram sample arm j m ε Q) a := by
    rw [balancedGramQuadraticForm]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hrank))
    change (∑ ℓ : MultiIndex d m, (nodeQ ℓ - b)) ≤
      ∑ ℓ : MultiIndex d m,
        (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹ *
          ∑ i : Fin n,
            if (sample i).2.1 = arm ∧
              (sample i).1 ∈ scaledSubcell d j m ε Q ℓ then sampleQ i else 0
    exact Finset.sum_le_sum (s := Finset.univ) (fun ℓ _ => havg ℓ)
  have href : lam * A ≤ quadraticForm (referenceGram d m) a :=
    referenceLowerEigenvalueBound d m a
  have hrewrite :
      (Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
        (∑ ℓ : MultiIndex d m, (nodeQ ℓ - b)) =
      quadraticForm (referenceGram d m) a - b := by
    calc
      _ = (Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
          (∑ ℓ : MultiIndex d m, nodeQ ℓ) - b := by
        simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        simp only [Finset.card_univ]
        field_simp
      _ = _ := by
        rw [referenceGramQuadraticForm]
  change lam / 2 * A ≤ quadraticForm (balancedGram sample arm j m ε Q) a
  rw [hrewrite] at hsum
  have hhalf : lam / 2 * A ≤ quadraticForm (referenceGram d m) a - b := by
    dsimp [b]
    nlinarith [href]
  exact hhalf.trans hsum

-- @node: lem:balanced-gram
/-- Every occupied cell has a uniformly coercive balanced empirical Gram
matrix, regardless of the within-subcell design distribution. -/
lemma balanced_gram {d n : ℕ} (sample : Fin n → Obs d) (j : ℕ) (β : ℝ)
    (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample true j (polynomialOrder β)
      (normingSubcells d β).radius Q) :
    ∀ a : MultiIndex d (polynomialOrder β) → ℝ,
      referenceLowerEigenvalue d (polynomialOrder β) / 2 *
        (∑ i, (a i) ^ 2) ≤
      quadraticForm (balancedGram sample true j (polynomialOrder β)
        (normingSubcells d β).radius Q) a := by
  exact armBalanced_gram sample true j β Q hcount

-- @node: armBalancedGram_posDef
/-- Occupancy makes the balanced Gram matrix positive definite for either arm.
The norming lower eigenvalue is strictly positive, so the fit uses a genuine
matrix inverse on every occupied cell, including control cells in (C6). -/
lemma armBalancedGram_posDef {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j : ℕ) (β : ℝ) (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q) :
    (balancedGram sample arm j (polynomialOrder β) (normingSubcells d β).radius Q).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext a b
    simp [Matrix.conjTranspose, balancedGram, mul_comm]
  · intro a ha
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 :=
      not_forall.mp (fun h => ha (funext h))
    have hnorm : 0 < ∑ i, (a i) ^ 2 :=
      (sq_pos_of_ne_zero hi).trans_le
        (Finset.single_le_sum (fun k _ => sq_nonneg (a k)) (Finset.mem_univ i))
    have hcoercive := armBalanced_gram sample arm j β Q hcount a
    have hpos := mul_pos
      (half_pos (referenceLowerEigenvalue_pos d (polynomialOrder β))) hnorm
    have hq : quadraticForm
        (balancedGram sample arm j (polynomialOrder β) (normingSubcells d β).radius Q) a =
        star a ⬝ᵥ ((balancedGram sample arm j (polynomialOrder β)
          (normingSubcells d β).radius Q) *ᵥ a) := by
      simp [quadraticForm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [← hq]
    exact hpos.trans_le hcoercive

-- @node: armBalancedGram_normalEquation
/-- On an occupied cell the coefficient vector solves the balanced normal
equation exactly. This supplies the algebraic starting point of (8), (10),
and (C11), without any assumption of invertibility. -/
lemma armBalancedGram_normalEquation {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j : ℕ) (β : ℝ) (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q)
    (b : MultiIndex d (polynomialOrder β) → ℝ) :
    let G := balancedGram sample arm j (polynomialOrder β) (normingSubcells d β).radius Q
    G *ᵥ (G⁻¹ *ᵥ b) = b := by
  classical
  dsimp only
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (armBalancedGram_posDef sample arm j β Q hcount).isUnit), Matrix.one_mulVec]

end CausalSmith.Stat.GlobalTailDesignRobustCate
