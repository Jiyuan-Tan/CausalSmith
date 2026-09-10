import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.Software

/-!
# `clubSandwich` CR2 consumer identity

The deterministic equal-group identity is conditional on the two versioned
software contracts and on the explicit intercept-plus-binary-treatment fit data.
-/

open scoped BigOperators Matrix

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

/-- The algebraic data fixed by an unweighted equal-group intercept-plus-binary-
treatment OLS fit. -/
def EqualGroupBinaryFitSpec {n M G G1 : ℕ} (Y : PotentialOutcome n M)
    (w : PartitionTuple n M G × TreatmentSpace G G1)
    (rowUnit : ∀ g, Fin M ≃ {i : Fin n // i ∈ (w.1.1 g).1})
    (X : Fin G → Matrix (Fin M) (Fin 2) ℝ)
    (Xstack : Matrix (Fin (G * M)) (Fin 2) ℝ)
    (y : Fin G → Fin M → ℝ)
    (e : Fin G → Fin M → ℝ)
    (H A : Fin G → Matrix (Fin M) (Fin M) ℝ)
    (bread breadTilde : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀ g i j, X g i j = if j = 0 then 1 else if g ∈ w.2.1 then 1 else 0) ∧
  (∀ g i, y g i = Y (w.1.1 g) (rowUnit g i) (g ∈ w.2.1)) ∧
  (∀ g, (∑ i, y g i) / (M : ℝ) = obsGroupMean Y w g) ∧
  UnweightedFullRankLmFit (fun _ => M) X y e ∧
  (∀ g, (∑ i, e g i) / (M : ℝ) =
    obsGroupMean Y w g - armObsMean Y w (g ∈ w.2.1)) ∧
  Xstackᵀ * Xstack = ∑ g, (X g)ᵀ * X g ∧
  (∀ g, H g = X g * ((Xstackᵀ * Xstack)⁻¹) * (X g)ᵀ) ∧
  (∀ g, Matrix.PosDef (1 - H g)) ∧
  (∀ g, Matrix.PosDef (A g) ∧ A g = (A g)ᵀ ∧
    A g * A g * (1 - H g) = 1) ∧
  breadTilde = ((G * M : ℕ) : ℝ)⁻¹ • bread

-- @node: matrix_sandwich_rank_one
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:a,b,B,X,A,e,hB), [the matrix sandwich rank one result holds](goal). -/
lemma matrix_sandwich_rank_one {a b : Type} [Fintype a] [Fintype b]
    (B : Matrix b b ℝ) (X : Matrix a b ℝ) (A : Matrix a a ℝ) (e : a → ℝ)
    (hB : B = Bᵀ) :
    B * Xᵀ * A * Matrix.vecMulVec e e * Aᵀ * X * B =
      Matrix.vecMulVec (B *ᵥ (Xᵀ *ᵥ (A *ᵥ e)))
        (B *ᵥ (Xᵀ *ᵥ (A *ᵥ e))) := by
  let P := B * Xᵀ * A
  have hfactor : B * Xᵀ * A * Matrix.vecMulVec e e * Aᵀ * X * B =
      P * Matrix.vecMulVec e e * Pᵀ := by
    dsimp [P]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [← hB]
    simp [Matrix.mul_assoc]
  rw [hfactor, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMul_transpose]
  simp [P, Matrix.mulVec_mulVec, Matrix.mul_assoc]

-- @node: posDef_rankOne_inverse_sqrt
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,q,hM,hq,H,A,hH,hA,hAsymm,hA2), [the pos def rank one inverse sqrt result holds](goal). -/
lemma posDef_rankOne_inverse_sqrt {M q : ℕ} (hM : 0 < M) (hq : 2 ≤ q)
    (H A : Matrix (Fin M) (Fin M) ℝ)
    (hH : ∀ i j, H i j = 1 / ((M : ℝ) * (q : ℝ)))
    (hA : A.PosDef) (hAsymm : A = Aᵀ)
    (hA2 : A * A * (1 - H) = 1) :
    ∀ i j, A i j = (if i = j then 1 else 0) +
      (Real.sqrt ((q : ℝ) / ((q - 1 : ℕ) : ℝ)) - 1) / (M : ℝ) := by
  classical
  let u : Fin M → ℝ := fun _ => 1
  let v : Fin M → Fin M → ℝ := fun j k =>
    (if k = j then 1 else 0) - 1 / (M : ℝ)
  let a : ℝ := Real.sqrt ((q : ℝ) / ((q - 1 : ℕ) : ℝ))
  let Q : Matrix (Fin M) (Fin M) ℝ := 1 - H
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hqr : (q : ℝ) ≠ 0 := by positivity
  have hq1r : ((q - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : q - 1 ≠ 0)
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hEqVec (x : Fin M → ℝ) :
      A *ᵥ (A *ᵥ (Q *ᵥ x)) = x := by
    simpa only [Q, Matrix.mulVec_mulVec, Matrix.one_mulVec, Matrix.mul_assoc] using
      congrArg (fun K => K *ᵥ x) hA2
  have hQv (j : Fin M) : Q *ᵥ v j = v j := by
    ext i
    simp [Q, Matrix.mulVec, dotProduct, Matrix.one_apply, hH, v, hMr,
      sub_mul, mul_sub]
    field_simp
    ring
  have hA2v (j : Fin M) : A *ᵥ (A *ᵥ v j) = v j := by
    simpa [hQv] using hEqVec (v j)
  have hplusPos : (A + 1).PosDef := hA.add .one
  have hplusInj : Function.Injective (A + 1).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hplusPos.isUnit
  have hAv (j : Fin M) : A *ᵥ v j = v j := by
    apply hplusInj
    simp only [Matrix.add_mulVec, Matrix.one_mulVec]
    rw [hA2v]
    abel
  have hQu : Q *ᵥ u = (((q - 1 : ℕ) : ℝ) / (q : ℝ)) • u := by
    ext i
    simp [Q, Matrix.mulVec, dotProduct, Matrix.one_apply, hH, u, hMr,
      Nat.cast_sub (by omega : 1 ≤ q)]
    field_simp
  have hA2u : A *ᵥ (A *ᵥ u) = a ^ 2 • u := by
    have he := hEqVec u
    rw [hQu] at he
    simp only [Matrix.mulVec_smul] at he
    ext i
    have hei := congrFun he i
    simp only [Pi.smul_apply, u, smul_eq_mul] at hei ⊢
    rw [Real.sq_sqrt (by positivity : 0 ≤ (q : ℝ) / ((q - 1 : ℕ) : ℝ))]
    field_simp at hei ⊢
    linarith
  have hasmulPos : (a • (1 : Matrix (Fin M) (Fin M) ℝ)).PosDef :=
    Matrix.PosDef.smul .one ha_pos
  have haplusPos : (A + a • 1).PosDef := hA.add hasmulPos
  have haplusInj : Function.Injective (A + a • 1).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr haplusPos.isUnit
  have hAu : A *ᵥ u = a • u := by
    apply haplusInj
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hA2u, Matrix.mulVec_smul]
    module
  intro i j
  have hv := congrFun (hAv j) i
  have hu := congrFun hAu i
  simp only [Matrix.mulVec, dotProduct, v] at hv
  simp only [Matrix.mulVec, dotProduct, u, Pi.smul_apply] at hu
  simp_rw [mul_sub] at hv
  rw [Finset.sum_sub_distrib] at hv
  simp at hu
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hv
  rw [← Finset.sum_mul] at hv
  rw [hu] at hv
  dsimp [a] at hv hu ⊢
  field_simp at hv ⊢
  linarith

-- @node: prop:clubsandwich-consumer
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hM,hG1,hG0,Y,w,rowUnit,X,Xstack,y,e,H,A,bread,breadTilde,Sigma,hFit,hClubSandwichCR2Contract_of_gate,hSandwichLmBreadContract_of_gate), [the stated equality holds](goal). -/
theorem clubsandwich_cr2_consumer_identity {n M G G1 : ℕ}
    (hM : 2 ≤ M) (hG1 : 2 ≤ G1) (hG0 : 2 ≤ G - G1)
    (Y : PotentialOutcome n M)
    (w : PartitionTuple n M G × TreatmentSpace G G1)
    (rowUnit : ∀ g, Fin M ≃ {i : Fin n // i ∈ (w.1.1 g).1})
    (X : Fin G → Matrix (Fin M) (Fin 2) ℝ)
    (Xstack : Matrix (Fin (G * M)) (Fin 2) ℝ)
    (y : Fin G → Fin M → ℝ)
    (e : Fin G → Fin M → ℝ)
    (H A : Fin G → Matrix (Fin M) (Fin M) ℝ)
    (bread breadTilde Sigma : Matrix (Fin 2) (Fin 2) ℝ)
    (hFit : EqualGroupBinaryFitSpec Y w rowUnit X Xstack y e H A bread breadTilde)
    (hClubSandwichCR2Contract_of_gate :
      ClubSandwichCR2Contract (fun _ => M) (G * M)
        (pinnedClubSandwichCall Sigma) X y e H A bread breadTilde)
    (hSandwichLmBreadContract_of_gate :
      SandwichLmBreadContract (fun _ => M) (G * M)
        (pinnedSandwichBreadCall (G * M) bread) Xstack X y e) :
    Sigma 1 1 = cr2Var Y hG1 hG0 w := by
  classical
  rcases hFit with
    ⟨hX, hy, hGroupMean, hLm, hResidualMean, hStack, hH, hHpos, hA,
      hBreadScale⟩
  rcases hClubSandwichCR2Contract_of_gate with
    ⟨_, _, _, _, _, _, _, _, hClub⟩
  rcases hSandwichLmBreadContract_of_gate with
    ⟨_, _, _, _, hSandwich⟩
  have hG1le : G1 ≤ G := by omega
  have hGpos : 0 < G := by omega
  have hMpos : 0 < M := by omega
  have hG0pos : 0 < G - G1 := by omega
  have hG1r : (G1 : ℝ) ≠ 0 := by positivity
  have hG0r : (G : ℝ) - (G1 : ℝ) ≠ 0 := by
    rw [← Nat.cast_sub hG1le]
    positivity
  have hGram : ∀ i j, (Xstackᵀ * Xstack) i j =
      if i = 0 then
        if j = 0 then (M : ℝ) * G else (M : ℝ) * G1
      else if j = 0 then (M : ℝ) * G1 else (M : ℝ) * G1 := by
    intro i j
    rw [hStack, Matrix.sum_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    fin_cases i <;> fin_cases j
    · simp [hX]; ring
    · simp [hX, Finset.sum_ite_irrel, w.2.2]; ring
    · simp [hX, Finset.sum_ite_irrel, w.2.2]; ring
    · simp [hX, Finset.sum_ite_irrel, w.2.2]; ring
  have hBread : bread = ((G * M : ℕ) : ℝ) • (Xstackᵀ * Xstack)⁻¹ := by
    simpa [pinnedSandwichBreadCall] using hSandwich hLm hStack
  have hBreadTilde : breadTilde = (Xstackᵀ * Xstack)⁻¹ := by
    rw [hBreadScale, hBread]
    ext i j
    simp [Nat.cast_mul]
    field_simp
  have hBreadRow : ∀ i, breadTilde 1 i =
      if i = 0 then -1 / ((M : ℝ) * (G - G1 : ℝ))
      else 1 / ((M : ℝ) * (G - G1 : ℝ)) + 1 / ((M : ℝ) * (G1 : ℝ)) := by
    intro i
    rw [hBreadTilde, Matrix.inv_def]
    fin_cases i <;>
      simp [Matrix.smul_apply, Matrix.det_fin_two, Matrix.adjugate_fin_two, hGram,
        Nat.cast_sub hG1le] <;>
      field_simp [hMpos.ne', hG1r, hG0r]; ring
  have hBreadCol : ∀ i, breadTilde i 1 =
      if i = 0 then -1 / ((M : ℝ) * (G - G1 : ℝ))
      else 1 / ((M : ℝ) * (G - G1 : ℝ)) + 1 / ((M : ℝ) * (G1 : ℝ)) := by
    intro i
    rw [hBreadTilde, Matrix.inv_def]
    fin_cases i <;>
      simp [Matrix.smul_apply, Matrix.det_fin_two, Matrix.adjugate_fin_two, hGram,
        Nat.cast_sub hG1le] <;>
      field_simp [hMpos.ne', hG1r, hG0r]; ring
  have hBread00 : breadTilde 0 0 = 1 / ((M : ℝ) * (G - G1 : ℝ)) := by
    rw [hBreadTilde, Matrix.inv_def]
    simp [Matrix.smul_apply, Matrix.det_fin_two, Matrix.adjugate_fin_two, hGram]
    field_simp [hMpos.ne', hG1r, hG0r]
  have hHEntry : ∀ g i j, H g i j =
      1 / ((M : ℝ) * (armCount G G1 (g ∈ w.2.1) : ℝ)) := by
    intro g i j
    rw [hH g, ← hBreadTilde]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    by_cases hg : g ∈ w.2.1
    · simp [hX, hBreadRow, hBreadCol, hBread00, hg, armCount]
      field_simp [hMpos.ne', hG1r]
      ring
    · simp [hX, hBreadRow, hBreadCol, hBread00, hg, armCount, Nat.cast_sub hG1le]
  have hAEntry : ∀ g i j, A g i j =
      (if i = j then 1 else 0) +
        (Real.sqrt ((armCount G G1 (g ∈ w.2.1) : ℝ) /
          ((armCount G G1 (g ∈ w.2.1) - 1 : ℕ) : ℝ)) - 1) / (M : ℝ) := by
    intro g
    have hq : 2 ≤ armCount G G1 (g ∈ w.2.1) := by
      by_cases hg : g ∈ w.2.1 <;> simp [armCount, hg, hG1, hG0]
    exact posDef_rankOne_inverse_sqrt hMpos hq (H g) (A g) (hHEntry g)
      (hA g).1 (hA g).2.1 (hA g).2.2
  have hSigma : Sigma = breadTilde * cr2Meat (fun _ => M) X e A * breadTilde := by
    simpa [pinnedClubSandwichCall] using
      hClub hLm (by simpa [hStack] using hH) hHpos hA hBreadScale
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hAColSum (g : Fin G) (j : Fin M) :
      (∑ i, A g i j) =
        Real.sqrt ((armCount G G1 (g ∈ w.2.1) : ℝ) /
          ((armCount G G1 (g ∈ w.2.1) - 1 : ℕ) : ℝ)) := by
    simp_rw [hAEntry]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hASumE (g : Fin G) :
      (∑ i, (A g *ᵥ e g) i) =
        Real.sqrt ((armCount G G1 (g ∈ w.2.1) : ℝ) /
          ((armCount G G1 (g ∈ w.2.1) - 1 : ℕ) : ℝ)) * ∑ j, e g j := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hAColSum]
    rw [Finset.mul_sum]
  have hBreadSymm : breadTilde = breadTildeᵀ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.transpose_apply, hBreadRow, hBreadCol]
  let score : Fin G → Fin 2 → ℝ := fun g =>
    breadTilde *ᵥ ((X g)ᵀ *ᵥ (A g *ᵥ e g))
  have hScore (g : Fin G) : score g 1 =
      if hg : g ∈ w.2.1 then
        Real.sqrt ((G1 : ℝ) / ((G1 - 1 : ℕ) : ℝ)) *
          (obsGroupMean Y w g - armObsMean Y w true) / (G1 : ℝ)
      else
        -(Real.sqrt (((G - G1 : ℕ) : ℝ) / ((G - G1 - 1 : ℕ) : ℝ)) *
          (obsGroupMean Y w g - armObsMean Y w false) / ((G - G1 : ℕ) : ℝ)) := by
    unfold score
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two]
    by_cases hg : g ∈ w.2.1
    · simp [hg, hX, hBreadRow]
      rw [show (∑ i, ∑ j, A g i j * e g j) =
          Real.sqrt ((G1 : ℝ) / ((G1 - 1 : ℕ) : ℝ)) * ∑ j, e g j by
        simpa [Matrix.mulVec, dotProduct, hg, armCount] using hASumE g]
      have hr := hResidualMean g
      simp [hg] at hr
      have hrsum : (∑ j, e g j) = (M : ℝ) *
          (obsGroupMean Y w g - armObsMean Y w true) := by
        calc
          (∑ j, e g j) =
              (obsGroupMean Y w g - armObsMean Y w true) * (M : ℝ) :=
            (div_eq_iff hMne).mp hr
          _ = _ := by ring
      rw [hrsum]
      field_simp
      rw [Real.sqrt_div (by positivity)]
      ring
    · simp [hg, hX, hBreadRow]
      rw [show (∑ i, ∑ j, A g i j * e g j) =
          Real.sqrt (((G - G1 : ℕ) : ℝ) / ((G - G1 - 1 : ℕ) : ℝ)) * ∑ j, e g j by
        simpa [Matrix.mulVec, dotProduct, hg, armCount] using hASumE g]
      have hr := hResidualMean g
      simp [hg] at hr
      have hrsum : (∑ j, e g j) = (M : ℝ) *
          (obsGroupMean Y w g - armObsMean Y w false) := by
        calc
          (∑ j, e g j) =
              (obsGroupMean Y w g - armObsMean Y w false) * (M : ℝ) :=
            (div_eq_iff hMne).mp hr
          _ = _ := by ring
      rw [hrsum]
      rw [Nat.cast_sub (by omega : G1 ≤ G)]
      have hcast : (G1 : ℝ) < (G : ℝ) := by
        exact_mod_cast (by omega : G1 < G)
      have hG0pos : 0 < (G : ℝ) - (G1 : ℝ) := by
        linarith
      have hG0r : (G : ℝ) - (G1 : ℝ) ≠ 0 := ne_of_gt hG0pos
      have hsqrt0 : Real.sqrt ((G - G1 - 1 : ℕ) : ℝ) ≠ 0 := by
        exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < G - G1 - 1)))
      field_simp
      rw [Real.sqrt_div hG0pos.le]
      field_simp [hsqrt0]
  have hSandwich : breadTilde * cr2Meat (fun _ => M) X e A * breadTilde =
      ∑ g, Matrix.vecMulVec (score g) (score g) := by
    unfold cr2Meat
    rw [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro g _
    simpa [score, Matrix.mul_assoc] using
      matrix_sandwich_rank_one breadTilde (X g) (A g) (e g) hBreadSymm
  rw [hSigma, hSandwich]
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
  simp_rw [hScore]
  have hG1nz : (G1 : ℝ) ≠ 0 := by positivity
  have hG1mnz : ((G1 - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : G1 - 1 ≠ 0)
  have hG0nz : ((G - G1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hG0mnz : ((G - G1 - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : G - G1 - 1 ≠ 0)
  have htreated (d : ℝ) :
      (Real.sqrt ((G1 : ℝ) / ((G1 - 1 : ℕ) : ℝ)) * d / (G1 : ℝ)) ^ 2 =
        d ^ 2 / ((G1 - 1 : ℕ) : ℝ) / (G1 : ℝ) := by
    rw [show (Real.sqrt ((G1 : ℝ) / ((G1 - 1 : ℕ) : ℝ)) * d /
          (G1 : ℝ)) ^ 2 =
        Real.sqrt ((G1 : ℝ) / ((G1 - 1 : ℕ) : ℝ)) ^ 2 * d ^ 2 /
          (G1 : ℝ) ^ 2 by ring]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hcontrol (d : ℝ) :
      (Real.sqrt (((G - G1 : ℕ) : ℝ) / ((G - G1 - 1 : ℕ) : ℝ)) * d /
          ((G - G1 : ℕ) : ℝ)) ^ 2 =
        d ^ 2 / ((G - G1 - 1 : ℕ) : ℝ) / ((G - G1 : ℕ) : ℝ) := by
    rw [show (Real.sqrt (((G - G1 : ℕ) : ℝ) /
          ((G - G1 - 1 : ℕ) : ℝ)) * d / ((G - G1 : ℕ) : ℝ)) ^ 2 =
        Real.sqrt (((G - G1 : ℕ) : ℝ) /
          ((G - G1 - 1 : ℕ) : ℝ)) ^ 2 * d ^ 2 /
          ((G - G1 : ℕ) : ℝ) ^ 2 by ring]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  simp only [← pow_two]
  rw [show (∑ g,
        (if hg : g ∈ w.2.1 then
          Real.sqrt ((G1 : ℝ) / ((G1 - 1 : ℕ) : ℝ)) *
            (obsGroupMean Y w g - armObsMean Y w true) / (G1 : ℝ)
        else
          -(Real.sqrt (((G - G1 : ℕ) : ℝ) / ((G - G1 - 1 : ℕ) : ℝ)) *
            (obsGroupMean Y w g - armObsMean Y w false) /
              ((G - G1 : ℕ) : ℝ))) ^ 2) =
      ∑ g, if g ∈ w.2.1 then
        (obsGroupMean Y w g - armObsMean Y w true) ^ 2 /
          ((G1 - 1 : ℕ) : ℝ) / (G1 : ℝ)
      else
        (obsGroupMean Y w g - armObsMean Y w false) ^ 2 /
          ((G - G1 - 1 : ℕ) : ℝ) / ((G - G1 : ℕ) : ℝ) by
    apply Finset.sum_congr rfl
    intro g _
    by_cases hg : g ∈ w.2.1
    · rw [dif_pos hg, if_pos hg]
      exact htreated _
    · rw [dif_neg hg, if_neg hg, neg_sq]
      exact hcontrol _]
  rw [Finset.sum_ite]
  simp only [cr2Var, armSampleVar, realizedArmSet, armCount,
    Bool.false_eq_true, ↓reduceIte]
  have hfilterPos : Finset.univ.filter (fun g : Fin G => g ∈ w.2.1) = w.2.1 := by
    ext g
    simp
  have hfilterNeg : Finset.univ.filter (fun g : Fin G => g ∉ w.2.1) =
      Finset.univ \ w.2.1 := by
    ext g
    simp
  rw [hfilterPos, hfilterNeg]
  simp only [Finset.sum_div]

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
