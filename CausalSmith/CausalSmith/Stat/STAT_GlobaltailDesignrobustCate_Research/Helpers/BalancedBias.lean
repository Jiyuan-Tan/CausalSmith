module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedGram
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedWeights
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.MassBudget
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.TaylorBias

/-! # Deterministic balanced score and Taylor residual

The balanced normal equations reproduce tensor polynomials exactly. Subtracting
such a polynomial leaves a balanced residual score whose coordinates are bounded
by the cell approximation error. These identities apply to either arm.
-/
@[expose] public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open scoped BigOperators Matrix

/-- Balanced empirical score with an arbitrary scalar response at each observation. -/
-- @node: balancedScore
noncomputable def balancedScore {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (y : Fin n → ℝ) : MultiIndex d m → ℝ := by
  classical
  exact fun a => (Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
    ∑ ℓ : MultiIndex d m, (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹ *
      ∑ i : Fin n,
        if (sample i).2.1 = arm ∧ (sample i).1 ∈ scaledSubcell d j m ε Q ℓ then
          monomial d m (fun k => ((sample i).1 k - cellOrigin d j Q k) /
            dyadicWidth j) a * y i else 0

/-- The estimator's observed outcome moment is its balanced score. -/
-- @node: balancedMoment_eq_score
lemma balancedMoment_eq_score {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j)) :
    balancedMoment sample arm j m ε Q =
      balancedScore sample arm j m ε Q (fun i => (sample i).2.2) := rfl

/-- Subtracting scalar responses subtracts their balanced scores. -/
-- @node: balancedScore_sub
lemma balancedScore_sub {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (y z : Fin n → ℝ) :
    balancedScore sample arm j m ε Q (fun i => y i - z i) =
      balancedScore sample arm j m ε Q y - balancedScore sample arm j m ε Q z := by
  classical
  funext a
  have hsplit (p : Prop) [Decidable p] (a b : ℝ) :
      (if p then a - b else 0) = (if p then a else 0) - (if p then b else 0) := by
    split_ifs <;> ring
  simp only [balancedScore, Pi.sub_apply, mul_sub, hsplit, Finset.sum_sub_distrib]

/-- A polynomial response has balanced score equal to the Gram matrix times
its coefficients, even before imposing occupancy. -/
-- @node: balancedScore_polynomial
lemma balancedScore_polynomial {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (θ : MultiIndex d m → ℝ) :
    balancedScore sample arm j m ε Q
      (fun i => ∑ b, monomial d m
        (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j) b * θ b) =
      balancedGram sample arm j m ε Q *ᵥ θ := by
  classical
  funext a
  simp only [balancedScore, balancedGram, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext ℓ
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (sample i).2.1 = arm ∧ (sample i).1 ∈ scaledSubcell d j m ε Q ℓ
  · simp only [if_pos hi]
    apply Finset.sum_congr rfl
    intro b _
    ring
  · simp [hi]

/-- Tensor monomials have absolute value at most one on the unit cube. -/
-- @node: monomial_abs_le_one
lemma monomial_abs_le_one {d m : ℕ} (u : Fin d → ℝ)
    (hu : u ∈ cube d) (a : MultiIndex d m) : |monomial d m u a| ≤ 1 := by
  unfold monomial
  rw [Finset.abs_prod]
  apply Finset.prod_le_one
  · intro i _
    positivity
  · intro i _
    rw [abs_pow]
    apply pow_le_one₀ (abs_nonneg _) _
    have hi := hu i (by simp)
    rw [abs_of_nonneg hi.1]
    exact hi.2

/-- Selected norming-subcell observations have unit-cube normalized coordinates. -/
-- @node: scaledSubcell_normalized_mem_cube
lemma scaledSubcell_normalized_mem_cube {d : ℕ} (j : ℕ) (β : ℝ)
    (Q : Fin d → Fin (2 ^ j)) (ℓ : MultiIndex d (polynomialOrder β))
    (x : Fin d → ℝ)
    (hx : x ∈ scaledSubcell d j (polynomialOrder β) (normingSubcells d β).radius Q ℓ) :
    (fun k => (x k - cellOrigin d j Q k) / dyadicWidth j) ∈ cube d := by
  have hu := (normingSubcells d β).interior ℓ hx.2
  intro i _
  exact ⟨(hu i (by simp)).1.le, (hu i (by simp)).2.le⟩

/-- A bounded selected summand has a bounded normalized average. -/
-- @node: normalizedSelectedSum_abs_le
lemma normalizedSelectedSum_abs_le {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (f : Fin n → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ i, p i → |f i| ≤ E) :
    |((∑ i : Fin n, if p i then 1 else 0 : ℕ) : ℝ)⁻¹ *
      ∑ i : Fin n, if p i then f i else 0| ≤ E := by
  let N : ℕ := ∑ i : Fin n, if p i then 1 else 0
  by_cases hN : N = 0
  · change |(N : ℝ)⁻¹ * _| ≤ E
    simp [hN, hE]
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hsum : |∑ i : Fin n, if p i then f i else 0| ≤ (N : ℝ) * E := by
    calc
      _ ≤ ∑ i : Fin n, |if p i then f i else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, if p i then E else 0 := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi
        · exact hf i hi
        · simp
      _ = _ := selectedConstantSum p E
  change |(N : ℝ)⁻¹ * _| ≤ E
  rw [abs_mul, abs_of_pos (inv_pos.mpr hNr)]
  calc
    _ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * E) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = E := by field_simp

/-- The residual score has coordinate bound equal to the approximation error.
The result also holds at zero counts because the corresponding score is zero. -/
-- @node: balancedScore_abs_le
lemma balancedScore_abs_le {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j : ℕ) (β : ℝ) (Q : Fin d → Fin (2 ^ j))
    (r : Fin n → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hr : ∀ ℓ i, (sample i).2.1 = arm →
      (sample i).1 ∈ scaledSubcell d j (polynomialOrder β)
        (normingSubcells d β).radius Q ℓ → |r i| ≤ E)
    (a : MultiIndex d (polynomialOrder β)) :
    |balancedScore sample arm j (polynomialOrder β) (normingSubcells d β).radius Q r a| ≤ E := by
  classical
  have hterm (ℓ : MultiIndex d (polynomialOrder β)) :
      |(subcellCount sample arm j (polynomialOrder β) (normingSubcells d β).radius Q ℓ : ℝ)⁻¹ *
        ∑ i : Fin n, if (sample i).2.1 = arm ∧
          (sample i).1 ∈ scaledSubcell d j (polynomialOrder β) (normingSubcells d β).radius Q ℓ then
          monomial d (polynomialOrder β)
            (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j) a * r i else 0| ≤ E := by
    apply normalizedSelectedSum_abs_le _ _ E hE
    intro i hi
    rw [abs_mul]
    calc
      _ ≤ 1 * E := mul_le_mul
        (monomial_abs_le_one _ (scaledSubcell_normalized_mem_cube j β Q ℓ _ hi.2) a)
        (hr ℓ i hi.1 hi.2) (abs_nonneg _) (by norm_num)
      _ = E := one_mul E
  unfold balancedScore
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ)⁻¹ * ∑ _ℓ : MultiIndex d (polynomialOrder β), E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ℓ _ => hterm ℓ)) (by positivity)
    _ = E := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

/-- Coercivity and Cauchy–Schwarz propagate a coordinatewise score bound to
any prediction vector with coordinates bounded by one. -/
-- @node: coercive_prediction_abs_le
lemma coercive_prediction_abs_le {ι : Type} [Fintype ι]
    (G : Matrix ι ι ℝ) (a b v : ι → ℝ) (c E : ℝ)
    (hc : 0 < c) (hE : 0 ≤ E)
    (hcoercive : c * (∑ i, (a i) ^ 2) ≤ quadraticForm G a)
    (heq : G *ᵥ a = b) (hb : ∀ i, |b i| ≤ E) (hv : ∀ i, |v i| ≤ 1) :
    |∑ i, v i * a i| ≤ (Fintype.card ι : ℝ) * E / c := by
  classical
  let A : ℝ := ∑ i, (a i) ^ 2
  let R : ℝ := Fintype.card ι
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hq : quadraticForm G a = ∑ i, a i * b i := by
    rw [← heq]
    simp only [quadraticForm, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hq] at hcoercive
  change c * A ≤ ∑ i, a i * b i at hcoercive
  have hB : (∑ i, (b i) ^ 2) ≤ R * E ^ 2 := by
    calc
      _ ≤ ∑ _i : ι, E ^ 2 := Finset.sum_le_sum (fun i _ => by
        have hi := hb i
        nlinarith [sq_abs (b i), abs_nonneg (b i)])
      _ = _ := by simp [R]
  have hV : (∑ i, (v i) ^ 2) ≤ R := by
    calc
      _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
        have hi := hv i
        nlinarith [sq_abs (v i), abs_nonneg (v i)])
      _ = _ := by simp [R]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hqnonneg : 0 ≤ ∑ i, a i * b i :=
    (mul_nonneg hc.le hA).trans hcoercive
  have henergy : c ^ 2 * A ≤ R * E ^ 2 := by
    by_cases hz : A = 0
    · rw [hz, mul_zero]
      positivity
    have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
    have hbound : (c * A) ^ 2 ≤ A * (R * E ^ 2) := by
      calc
        _ ≤ (∑ i, a i * b i) ^ 2 := by
          simpa only [pow_two] using mul_self_le_mul_self (mul_nonneg hc.le hA) hcoercive
        _ ≤ A * (∑ i, (b i) ^ 2) := hcs
        _ ≤ _ := mul_le_mul_of_nonneg_left hB hA
    apply (mul_le_mul_iff_right₀ hApos).mp
    nlinarith only [hbound]
  have hpred := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v a
  have hpred' : (∑ i, v i * a i) ^ 2 ≤ R * A :=
    hpred.trans (mul_le_mul_of_nonneg_right hV hA)
  have hscaled : (c * |∑ i, v i * a i|) ^ 2 ≤ (R * E) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hpred' (sq_nonneg c)
    have h2 := mul_le_mul_of_nonneg_left henergy hR
    nlinarith only [h1, h2, sq_abs (∑ i, v i * a i)]
  apply (le_div_iff₀ hc).mpr
  have hnonneg : 0 ≤ R * E := mul_nonneg hR hE
  nlinarith [mul_nonneg hc.le (abs_nonneg (∑ i, v i * a i))]

/-- The occupied fit reproduces any tensor polynomial; its coefficient error
is the inverse Gram applied to the polynomial residual score (roadmap (8)). -/
-- @node: balancedScore_coefficient_residual
lemma balancedScore_coefficient_residual {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j : ℕ) (β : ℝ) (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q)
    (y : Fin n → ℝ) (θ : MultiIndex d (polynomialOrder β) → ℝ) :
    let m := polynomialOrder β
    let ε := (normingSubcells d β).radius
    let G := balancedGram sample arm j m ε Q
    G⁻¹ *ᵥ balancedScore sample arm j m ε Q y - θ =
      G⁻¹ *ᵥ balancedScore sample arm j m ε Q
        (fun i => y i - ∑ b, monomial d m
          (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j) b * θ b) := by
  classical
  dsimp only
  rw [balancedScore_sub, balancedScore_polynomial, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp
        (armBalancedGram_posDef sample arm j β Q hcount).isUnit), Matrix.one_mulVec]

/-- An occupied-cell residual fit has uniform prediction bound
`2 R E / λ₀`, implementing roadmap (9) with no design distribution assumption. -/
-- @node: balancedScore_prediction_abs_le
lemma balancedScore_prediction_abs_le {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j : ℕ) (β : ℝ) (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q)
    (r : Fin n → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hr : ∀ ℓ i, (sample i).2.1 = arm →
      (sample i).1 ∈ scaledSubcell d j (polynomialOrder β)
        (normingSubcells d β).radius Q ℓ → |r i| ≤ E)
    (u : Fin d → ℝ) (hu : u ∈ cube d) :
    let m := polynomialOrder β
    let ε := (normingSubcells d β).radius
    let G := balancedGram sample arm j m ε Q
    |∑ a, monomial d m u a *
      (G⁻¹ *ᵥ balancedScore sample arm j m ε Q r) a| ≤
        (Fintype.card (MultiIndex d m) : ℝ) * E /
          (referenceLowerEigenvalue d m / 2) := by
  dsimp only
  apply coercive_prediction_abs_le
  · exact half_pos (referenceLowerEigenvalue_pos d (polynomialOrder β))
  · exact hE
  · exact armBalanced_gram sample arm j β Q hcount _
  · exact armBalancedGram_normalEquation sample arm j β Q hcount _
  · exact balancedScore_abs_le sample arm j β Q r E hE hr
  · exact monomial_abs_le_one u hu

/-- The fit to regression values has uniform error bounded by the Taylor
error times `1 + 2R/λ₀`. This is the deterministic part of roadmap (8)--(9). -/
-- @node: balancedScore_fit_bias_le
lemma balancedScore_fit_bias_le {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j : ℕ) (β : ℝ) (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q)
    (f : (Fin d → ℝ) → ℝ) (θ : MultiIndex d (polynomialOrder β) → ℝ)
    (E : ℝ) (hE : 0 ≤ E)
    (happrox : ∀ x ∈ cube d, x ∈ dyadicCell d j Q →
      |f x - ∑ a, monomial d (polynomialOrder β)
        (fun k => (x k - cellOrigin d j Q k) / dyadicWidth j) a * θ a| ≤ E)
    (x : Fin d → ℝ) (hx : x ∈ cube d) (hQ : x ∈ dyadicCell d j Q) :
    let m := polynomialOrder β
    let ε := (normingSubcells d β).radius
    let G := balancedGram sample arm j m ε Q
    |(∑ a, monomial d m (fun k => (x k - cellOrigin d j Q k) / dyadicWidth j) a *
      (G⁻¹ *ᵥ balancedScore sample arm j m ε Q (fun i => f (sample i).1)) a) - f x| ≤
        (1 + (Fintype.card (MultiIndex d m) : ℝ) /
          (referenceLowerEigenvalue d m / 2)) * E := by
  classical
  let m := polynomialOrder β
  let ε := (normingSubcells d β).radius
  let G := balancedGram sample arm j m ε Q
  let y : Fin n → ℝ := fun i => f (sample i).1
  let r : Fin n → ℝ := fun i => y i - ∑ b, monomial d m
    (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j) b * θ b
  let v := monomial d m (fun k => (x k - cellOrigin d j Q k) / dyadicWidth j)
  have hr : ∀ ℓ i, (sample i).2.1 = arm →
      (sample i).1 ∈ scaledSubcell d j m ε Q ℓ → |r i| ≤ E := by
    intro ℓ i _ hi
    exact happrox (sample i).1 (scaledSubcell_subset_cube d j m (normingSubcells d β) Q ℓ hi) hi.1
  have hpred := balancedScore_prediction_abs_le sample arm j β Q hcount r E hE hr
    _ (normalizedDyadicPoint_mem_cube d j Q x hx hQ)
  have hcoef : G⁻¹ *ᵥ balancedScore sample arm j m ε Q y - θ =
      G⁻¹ *ᵥ balancedScore sample arm j m ε Q r :=
    balancedScore_coefficient_residual sample arm j β Q hcount y θ
  have hsplit : (∑ a, v a * (G⁻¹ *ᵥ balancedScore sample arm j m ε Q y) a) - f x =
      (∑ a, v a * (G⁻¹ *ᵥ balancedScore sample arm j m ε Q r) a) +
        ((∑ a, v a * θ a) - f x) := by
    rw [← hcoef]
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  change |(∑ a, v a * (G⁻¹ *ᵥ balancedScore sample arm j m ε Q y) a) - f x| ≤ _
  rw [hsplit]
  calc
    _ ≤ |∑ a, v a * (G⁻¹ *ᵥ balancedScore sample arm j m ε Q r) a| +
        |(∑ a, v a * θ a) - f x| := abs_add_le _ _
    _ ≤ (Fintype.card (MultiIndex d m) : ℝ) * E /
        (referenceLowerEigenvalue d m / 2) + E := by
      apply add_le_add hpred
      rw [abs_sub_comm]
      exact happrox x hx hQ
    _ = _ := by ring

/-- One positive constant controls the occupied-cell deterministic treated
bias uniformly over laws, samples, bandwidths, and cells. -/
-- @node: treated_balancedScore_bias
lemma treated_balancedScore_bias (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B : ℝ, 0 < B ∧ ∀ P : Law d, LawClass d β γ C L M P →
      ∀ (n j : ℕ) (sample : Fin n → Obs d) (Q : Fin d → Fin (2 ^ j)),
        0 < minimumCellCount sample true j (polynomialOrder β) (normingSubcells d β).radius Q →
        ∀ x ∈ cube d, x ∈ dyadicCell d j Q →
          let m := polynomialOrder β
          let ε := (normingSubcells d β).radius
          let G := balancedGram sample true j m ε Q
          |(∑ a, monomial d m (fun k => (x k - cellOrigin d j Q k) / dyadicWidth j) a *
            (G⁻¹ *ᵥ balancedScore sample true j m ε Q (fun i => P.mu1 (sample i).1)) a) -
              P.mu1 x| ≤ B * L * (dyadicWidth j) ^ β := by
  obtain ⟨BT, hBT, hTaylor⟩ := treated_dyadic_tensor_approx d β γ C L M hparam
  let A : ℝ := 1 + (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) /
    (referenceLowerEigenvalue d (polynomialOrder β) / 2)
  have hA : 0 < A := by
    have hlam := referenceLowerEigenvalue_pos d (polynomialOrder β)
    dsimp [A]
    positivity
  refine ⟨A * BT, mul_pos hA hBT, ?_⟩
  intro P hP n j sample Q hcount x hx hQ
  obtain ⟨θ, hθ⟩ := hTaylor P hP j Q
  have hE : 0 ≤ BT * L * (dyadicWidth j) ^ β := by
    have hL := hparam.2.2.2.2.1
    have hh := (dyadicWidth_mem_Ioc j).1
    positivity
  have h := balancedScore_fit_bias_le sample true j β Q hcount P.mu1 θ
    (BT * L * (dyadicWidth j) ^ β) hE (by
      intro z hz hzQ
      simpa only [mul_comm] using hθ z hz hzQ) x hx hQ
  convert h using 1
  dsimp [A]
  ring

/-- Projection onto the outcome interval contracts distance to any target
inside that interval. -/
-- @node: clipping_abs_sub_le
lemma clipping_abs_sub_le (M z t : ℝ) (ht : t ∈ Set.Icc (-M) M) :
    |max (-M) (min M z) - t| ≤ |z - t| := by
  have hdist := abs_le.mp (le_refl |z - t|)
  have hnonneg := abs_nonneg (z - t)
  apply abs_le.mpr
  constructor
  · have hlo : t - |z - t| ≤ min M z := le_min (by linarith [ht.2]) (by linarith [hdist.1])
    have h := hlo.trans (le_max_right (-M) (min M z))
    linarith
  · have hhi : max (-M) (min M z) ≤ t + |z - t| := by
      apply max_le
      · linarith [ht.1]
      · exact (min_le_right M z).trans (by linarith [hdist.2])
    linarith

/-- The actual clipped treated estimator has deterministic bias plus the
inverse-Gram residual prediction on every occupied cell (roadmap (10)--(14)).
Only the probability bound for the second term remains stochastic. -/
-- @node: treated_balancedEstimator_bias_noise
lemma treated_balancedEstimator_bias_noise (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B : ℝ, 0 < B ∧ ∀ P : Law d, LawClass d β γ C L M P →
      ∀ (n j : ℕ) (sample : Fin n → Obs d) (x : Fin d → ℝ), x ∈ cube d →
        let m := polynomialOrder β
        let ε := (normingSubcells d β).radius
        let Q := cellIndex d j x
        let G := balancedGram sample true j m ε Q
        0 < minimumCellCount sample true j m ε Q →
        |balancedEstimator sample j β M x - P.mu1 x| ≤
          B * L * (dyadicWidth j) ^ β +
            |∑ a, monomial d m (fun k => (x k - cellOrigin d j Q k) / dyadicWidth j) a *
              (G⁻¹ *ᵥ balancedScore sample true j m ε Q
                (fun i => (sample i).2.2 - P.mu1 (sample i).1)) a| := by
  classical
  obtain ⟨B, hB, hbias⟩ := treated_balancedScore_bias d β γ C L M hparam
  refine ⟨B, hB, ?_⟩
  intro P hP n j sample x hx
  dsimp only
  intro hcount
  let m := polynomialOrder β
  let ε := (normingSubcells d β).radius
  let Q := cellIndex d j x
  let G := balancedGram sample true j m ε Q
  let v := monomial d m (fun k => (x k - cellOrigin d j Q k) / dyadicWidth j)
  let mean : MultiIndex d m → ℝ := G⁻¹ *ᵥ
    balancedScore sample true j m ε Q (fun i => P.mu1 (sample i).1)
  let fit : MultiIndex d m → ℝ := G⁻¹ *ᵥ balancedMoment sample true j m ε Q
  let noise : MultiIndex d m → ℝ := G⁻¹ *ᵥ
    balancedScore sample true j m ε Q (fun i => (sample i).2.2 - P.mu1 (sample i).1)
  have hcoef : noise = fit - mean := by
    dsimp [noise, fit, mean]
    rw [balancedScore_sub, Matrix.mulVec_sub, balancedMoment_eq_score]
  have hsplit : (∑ a, v a * fit a) - P.mu1 x =
      ((∑ a, v a * mean a) - P.mu1 x) + (∑ a, v a * noise a) := by
    rw [hcoef]
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hfit : |(∑ a, v a * fit a) - P.mu1 x| ≤
      B * L * (dyadicWidth j) ^ β + |∑ a, v a * noise a| := by
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add
      (hbias P hP n j sample Q hcount x hx rfl) (le_refl _))
  have hnonzero : minimumCellCount sample true j m ε Q ≠ 0 := Nat.ne_of_gt hcount
  change |balancedEstimator sample j β M x - P.mu1 x| ≤ _
  unfold balancedEstimator armBalancedEstimator
  dsimp only
  rw [if_neg hnonzero]
  exact (clipping_abs_sub_le M _ _ (hP.semantics.2.2.2.2.1 x hx)).trans hfit

end CausalSmith.Stat.GlobalTailDesignRobustCate
