import Causalean.Mathlib.Analysis.SymmetricTensorPencil.Projectors

/-!
# Recovery and normalization of directions

This module turns matched spectral projectors into quantitative direction information.  It
includes both direct recovery of a rank-one lifted line from a nearby projector and the
trace-coordinate construction that removes the degree-lift ambiguity by using coordinate probes.
-/

namespace Causalean.Mathlib.Analysis.SymmetricTensorPencil

/-- The standard coordinate vector in a finite real coordinate space. With [its explicit inputs](hyp:p,i), [the defined object](goal) is [given by the displayed formula](step:1). -/
def standardBasis (p : ℕ) (i : Fin p) : Vec p :=
  fun k => if k = i then 1 else 0

/-- Normalize a finite real array by its Euclidean norm, with the conventional zero value when
the input is zero. With [its explicit inputs](hyp:z), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def normalizeFinite {ι : Type*} [Fintype ι] (z : ι → ℝ) : ι → ℝ :=
  (finiteFrobeniusNorm z)⁻¹ • z

/-- Normalize a finite coordinate vector by its Euclidean norm. With [its explicit inputs](hyp:z), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def normalizeVec {p : ℕ} (z : Vec p) : Vec p :=
  normalizeFinite z

private theorem finiteFrobeniusNorm_eq_euclideanNorm {ι : Type*} [Fintype ι]
    (x : ι → ℝ) :
    finiteFrobeniusNorm x = ‖WithLp.toLp 2 x‖ := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Real.sq_sqrt]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem finiteFrobeniusNorm_add_le {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    finiteFrobeniusNorm (x + y) ≤
      finiteFrobeniusNorm x + finiteFrobeniusNorm y := by
  rw [finiteFrobeniusNorm_eq_euclideanNorm,
    finiteFrobeniusNorm_eq_euclideanNorm,
    finiteFrobeniusNorm_eq_euclideanNorm]
  simpa using norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

private theorem finiteFrobeniusNorm_smul (a : ℝ) {ι : Type*} [Fintype ι]
    (x : ι → ℝ) :
    finiteFrobeniusNorm (a • x) = |a| * finiteFrobeniusNorm x := by
  rw [finiteFrobeniusNorm_eq_euclideanNorm,
    finiteFrobeniusNorm_eq_euclideanNorm]
  simpa [Real.norm_eq_abs] using norm_smul a (WithLp.toLp 2 x)

private theorem abs_finiteFrobeniusNorm_sub_le {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    |finiteFrobeniusNorm x - finiteFrobeniusNorm y| ≤
      finiteFrobeniusNorm (x - y) := by
  rw [finiteFrobeniusNorm_eq_euclideanNorm,
    finiteFrobeniusNorm_eq_euclideanNorm,
    finiteFrobeniusNorm_eq_euclideanNorm]
  simpa using abs_norm_sub_norm_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

private theorem finiteFrobeniusNorm_mulVec_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    finiteFrobeniusNorm (A.mulVec x) ≤
      squareOperatorNorm A * finiteFrobeniusNorm x := by
  rw [finiteFrobeniusNorm_eq_euclideanNorm,
    finiteFrobeniusNorm_eq_euclideanNorm, squareOperatorNorm,
    Matrix.l2_opNorm_toEuclideanCLM]
  simpa using Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)

private theorem squareOperatorNorm_add_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A B : Matrix ι ι ℝ) :
    squareOperatorNorm (A + B) ≤ squareOperatorNorm A + squareOperatorNorm B := by
  simp only [squareOperatorNorm, map_add]
  exact norm_add_le _ _

private theorem squareOperatorNorm_mul_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A B : Matrix ι ι ℝ) :
    squareOperatorNorm (A * B) ≤ squareOperatorNorm A * squareOperatorNorm B := by
  simp only [squareOperatorNorm, Matrix.l2_opNorm_toEuclideanCLM]
  exact Matrix.l2_opNorm_mul A B

/-- Normalization on an arbitrary finite real array is Lipschitz away from zero, with constant
twice the reciprocal of the smaller input norm. -/
-- Proof route: add and subtract `‖x‖⁻¹ • y`, use the reverse triangle inequality to control
-- `|‖x‖⁻¹ - ‖y‖⁻¹|`, and clear the positive minimum of the two norms.
private theorem normalizeFinite_sub_normalizeFinite_le {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (hx : 0 < finiteFrobeniusNorm x) (hy : 0 < finiteFrobeniusNorm y) :
    finiteFrobeniusNorm (normalizeFinite x - normalizeFinite y) ≤
      2 * finiteFrobeniusNorm (x - y) /
        min (finiteFrobeniusNorm x) (finiteFrobeniusNorm y) := by
  let X := finiteFrobeniusNorm x
  let Y := finiteFrobeniusNorm y
  let D := finiteFrobeniusNorm (x - y)
  let m := min X Y
  have hX : 0 < X := hx
  have hY : 0 < Y := hy
  have hm : 0 < m := lt_min hX hY
  have hmX : m ≤ X := min_le_left _ _
  have hrev : |X - Y| ≤ D := abs_finiteFrobeniusNorm_sub_le x y
  have hdecomp :
      normalizeFinite x - normalizeFinite y =
        X⁻¹ • (x - y) + (X⁻¹ - Y⁻¹) • y := by
    ext i
    simp only [normalizeFinite, Pi.sub_apply, Pi.add_apply]
    change X⁻¹ * x i - Y⁻¹ * y i =
      X⁻¹ * (x i - y i) + (X⁻¹ - Y⁻¹) * y i
    ring
  have hinvX : |X⁻¹| = X⁻¹ := abs_of_pos (inv_pos.mpr hX)
  have hinvdiff : |X⁻¹ - Y⁻¹| * Y = |X - Y| / X := by
    rw [inv_sub_inv hX.ne' hY.ne', abs_div, abs_mul, abs_of_pos hX,
      abs_of_pos hY, abs_sub_comm]
    field_simp
  rw [hdecomp]
  calc
    finiteFrobeniusNorm
        (X⁻¹ • (x - y) + (X⁻¹ - Y⁻¹) • y) ≤
        finiteFrobeniusNorm (X⁻¹ • (x - y)) +
          finiteFrobeniusNorm ((X⁻¹ - Y⁻¹) • y) :=
      finiteFrobeniusNorm_add_le _ _
    _ = X⁻¹ * D + |X⁻¹ - Y⁻¹| * Y := by
      rw [finiteFrobeniusNorm_smul, finiteFrobeniusNorm_smul, hinvX]
    _ = D / X + |X - Y| / X := by rw [hinvdiff]; simp [div_eq_mul_inv, mul_comm]
    _ ≤ D / m + D / m := by
      apply add_le_add
      · exact (div_le_div_iff₀ hX hm).2
          (mul_le_mul_of_nonneg_left hmX (show 0 ≤ D from Real.sqrt_nonneg _))
      · exact (div_le_div_iff₀ hX hm).2
          (mul_le_mul hrev hmX hm.le (show 0 ≤ D from Real.sqrt_nonneg _))
    _ = 2 * D / m := by ring

/-- Apply a candidate projector to a degree-`d` rank-one lift and normalize the resulting lifted
direction. With [its explicit inputs](hyp:P,c), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def recoverRankOneLift {p d : ℕ}
    (P : Matrix (LiftIndex p d) (LiftIndex p d) ℝ) (c : Vec p) : LiftIndex p d → ℝ :=
  normalizeFinite (P.mulVec (fun I => ∏ k, c (I k)))

/-- A matched nearby projector recovers the normalized rank-one lifted direction with error at
most `2 * delta / (1 - delta)`. Under [the listed assumptions](hyp:hd,hunit,hfixed,hdelta,hsmall,hclose), [the stated conclusion follows](goal). -/
-- Proof route: apply the operator bound to the unit true lift, deduce that its projected image
-- has norm at least `1-delta`, and use `normalizeFinite_sub_normalizeFinite_le`.
theorem recoverRankOneLift_error_le {p d : ℕ} (hd : 0 < d)
    (P P' : Matrix (LiftIndex p d) (LiftIndex p d) ℝ) (c : Vec p) {delta : ℝ}
    (hunit : finiteFrobeniusNorm c = 1)
    (hfixed : P.mulVec (fun I => ∏ k, c (I k)) = fun I => ∏ k, c (I k))
    (hdelta : 0 ≤ delta) (hsmall : delta < 1)
    (hclose : squareOperatorNorm (P' - P) ≤ delta) :
    finiteFrobeniusNorm
      (recoverRankOneLift P' c - fun I => ∏ k, c (I k)) ≤
        2 * delta / (1 - delta) := by
  classical
  let v : LiftIndex p d → ℝ := fun I => ∏ k, c (I k)
  let C₁ : FactorMatrix p 1 := fun i _ => c i
  have hC₁ : ∀ j, finiteFrobeniusNorm (C₁.col j) = 1 := by
    intro j
    change finiteFrobeniusNorm (fun i => c i) = 1
    exact hunit
  have hv : finiteFrobeniusNorm v = 1 := by
    have h := finiteFrobeniusNorm_liftedColumn_eq_one hd C₁ hC₁ (0 : Fin 1)
    change finiteFrobeniusNorm
      (fun I : LiftIndex p d => ∏ k, c (I k)) = 1 at h
    exact h
  have herrEq : P'.mulVec v - v = (P' - P).mulVec v := by
    rw [Matrix.sub_mulVec, hfixed]
  have herr : finiteFrobeniusNorm (P'.mulVec v - v) ≤ delta := by
    rw [herrEq]
    calc
      finiteFrobeniusNorm ((P' - P).mulVec v) ≤
          squareOperatorNorm (P' - P) * finiteFrobeniusNorm v :=
        finiteFrobeniusNorm_mulVec_le _ _
      _ ≤ delta * 1 := mul_le_mul hclose hv.le (Real.sqrt_nonneg _) hdelta
      _ = delta := mul_one _
  have hlower : 1 - delta ≤ finiteFrobeniusNorm (P'.mulVec v) := by
    have hrev := abs_finiteFrobeniusNorm_sub_le (P'.mulVec v) v
    rw [hv] at hrev
    have hsigned : 1 - finiteFrobeniusNorm (P'.mulVec v) ≤
        |finiteFrobeniusNorm (P'.mulVec v) - 1| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    linarith
  have hpos : 0 < finiteFrobeniusNorm (P'.mulVec v) :=
    (sub_pos.mpr hsmall).trans_le hlower
  have hnormv : normalizeFinite v = v := by
    simp [normalizeFinite, hv]
  have hgeneric := normalizeFinite_sub_normalizeFinite_le
    (P'.mulVec v) v hpos (by rw [hv]; norm_num)
  rw [hnormv] at hgeneric
  change finiteFrobeniusNorm (recoverRankOneLift P' c - v) ≤ _
  rw [recoverRankOneLift]
  change finiteFrobeniusNorm (normalizeFinite (P'.mulVec v) - v) ≤ _
  calc
    finiteFrobeniusNorm (normalizeFinite (P'.mulVec v) - v) ≤
        2 * finiteFrobeniusNorm (P'.mulVec v - v) /
          min (finiteFrobeniusNorm (P'.mulVec v)) (finiteFrobeniusNorm v) := hgeneric
    _ ≤ 2 * delta / (1 - delta) := by
      have hden : 1 - delta ≤
          min (finiteFrobeniusNorm (P'.mulVec v)) (finiteFrobeniusNorm v) := by
        rw [hv]
        exact le_min hlower (by linarith)
      have hdenpos : 0 <
          min (finiteFrobeniusNorm (P'.mulVec v)) (finiteFrobeniusNorm v) :=
        (sub_pos.mpr hsmall).trans_le hden
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left herr (by norm_num))
        (sub_pos.mpr hsmall) hden

/-- Trace coordinates evaluate each coordinate pencil on a selected rank-one spectral
projector. With [its explicit inputs](hyp:G,P,j), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def traceCoordinates {p n : ℕ}
    (G : Vec p → Matrix (Fin n) (Fin n) ℝ)
    (P : Fin n → Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : Vec p :=
  fun i => Matrix.trace (G (standardBasis p i) * P j)

private theorem trace_diagonalizableMatrix_mul_coordinateProjector {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : IsUnit S.det)
    (a : Fin n → ℝ) (j : Fin n) :
    Matrix.trace (diagonalizableMatrix S a * coordinateProjector S j) = a j := by
  classical
  unfold diagonalizableMatrix coordinateProjector
  let D := Matrix.diagonal a
  let E := Matrix.diagonal (fun k : Fin n => if k = j then (1 : ℝ) else 0)
  change Matrix.trace ((S * D * S⁻¹) * (S * E * S⁻¹)) = a j
  calc
    Matrix.trace ((S * D * S⁻¹) * (S * E * S⁻¹)) =
        Matrix.trace (S * (D * E) * S⁻¹) := by
      congr 1
      rw [Matrix.mul_assoc (S * D), ← Matrix.mul_assoc S⁻¹ (S * E),
        ← Matrix.mul_assoc S⁻¹ S, Matrix.nonsing_inv_mul S hS,
        Matrix.one_mul]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((D * E) * S⁻¹ * S) := by
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm S ((D * E) * S⁻¹)
    _ = Matrix.trace (D * E) := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul S hS, Matrix.mul_one]
    _ = a j := by
      simp [D, E, Matrix.trace]

/-- For an exact simultaneous diagonalization, trace coordinates recover a factor column divided
by its positive denominator-probe loading. Under [the listed assumptions](hyp:hS,hprobe), [the stated conclusion follows](goal). -/
theorem traceCoordinates_diagonalization {p n : ℕ}
    (C : FactorMatrix p n) (u : Vec p) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsUnit S.det) (hprobe : ∀ j, dot u (C.col j) ≠ 0) :
    traceCoordinates
      (fun w => diagonalizableMatrix S (fun j => dot w (C.col j) / dot u (C.col j)))
      (coordinateProjector S) =
        fun j => (dot u (C.col j))⁻¹ • C.col j := by
  classical
  funext j i
  rw [traceCoordinates,
    trace_diagonalizableMatrix_mul_coordinateProjector S hS]
  have hcoord : dot (standardBasis p i) (C.col j) = C i j := by
    simp [dot, standardBasis]
  rw [hcoord]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
  field_simp [hprobe j]

/-- Given reference and perturbed coordinate pencils, reference and perturbed
projectors, coordinate-pencil error bounds, projector error bounds,
perturbed-projector norm bounds, and reference-pencil norm bounds,
every trace coordinate obeys the explicit product error bound. Under [the listed assumptions](hyp:hpencil,hprojector,hprojectorNorm,hpencilNorm), [the stated conclusion follows](goal). -/
-- Proof route: write `G'P'-GP = (G'-G)P' + G(P'-P)`, use submultiplicativity, and finish with
-- `abs_trace_le_card_mul_operatorNorm`.
theorem traceCoordinates_perturbation_bound {p n : ℕ}
    (G G' : Vec p → Matrix (Fin n) (Fin n) ℝ)
    (P P' : Fin n → Matrix (Fin n) (Fin n) ℝ)
    {pencilError projectorError projectorNorm pencilNorm : ℝ}
    (hpencil : ∀ i, squareOperatorNorm
      (G' (standardBasis p i) - G (standardBasis p i)) ≤ pencilError)
    (hprojector : ∀ j, squareOperatorNorm (P' j - P j) ≤ projectorError)
    (hprojectorNorm : ∀ j, squareOperatorNorm (P' j) ≤ projectorNorm)
    (hpencilNorm : ∀ i, squareOperatorNorm (G (standardBasis p i)) ≤ pencilNorm) :
    ∀ i j, |traceCoordinates G' P' j i - traceCoordinates G P j i| ≤
      n * (pencilError * projectorNorm + pencilNorm * projectorError) := by
  classical
  intro i j
  let e := standardBasis p i
  have hpencilError : 0 ≤ pencilError :=
    (show 0 ≤ squareOperatorNorm (G' e - G e) by
      exact norm_nonneg _).trans (hpencil i)
  have hprojectorError : 0 ≤ projectorError :=
    (show 0 ≤ squareOperatorNorm (P' j - P j) by
      exact norm_nonneg _).trans (hprojector j)
  have hprojectorNorm₀ : 0 ≤ projectorNorm :=
    (show 0 ≤ squareOperatorNorm (P' j) by
      exact norm_nonneg _).trans (hprojectorNorm j)
  have hpencilNorm₀ : 0 ≤ pencilNorm :=
    (show 0 ≤ squareOperatorNorm (G e) by
      exact norm_nonneg _).trans (hpencilNorm i)
  have hdecomp :
      G' e * P' j - G e * P j =
        (G' e - G e) * P' j + G e * (P' j - P j) := by
    noncomm_ring
  have hop : squareOperatorNorm (G' e * P' j - G e * P j) ≤
      pencilError * projectorNorm + pencilNorm * projectorError := by
    rw [hdecomp]
    calc
      squareOperatorNorm ((G' e - G e) * P' j + G e * (P' j - P j)) ≤
          squareOperatorNorm ((G' e - G e) * P' j) +
            squareOperatorNorm (G e * (P' j - P j)) :=
        squareOperatorNorm_add_le _ _
      _ ≤ squareOperatorNorm (G' e - G e) * squareOperatorNorm (P' j) +
            squareOperatorNorm (G e) * squareOperatorNorm (P' j - P j) :=
        add_le_add (squareOperatorNorm_mul_le _ _) (squareOperatorNorm_mul_le _ _)
      _ ≤ pencilError * projectorNorm + pencilNorm * projectorError := by
        apply add_le_add
        · exact mul_le_mul (hpencil i) (hprojectorNorm j)
            (show 0 ≤ squareOperatorNorm (P' j) by exact norm_nonneg _) hpencilError
        · exact mul_le_mul (hpencilNorm i) (hprojector j)
            (show 0 ≤ squareOperatorNorm (P' j - P j) by exact norm_nonneg _)
            hpencilNorm₀
  change |Matrix.trace (G' e * P' j) - Matrix.trace (G e * P j)| ≤ _
  rw [← Matrix.trace_sub]
  exact (abs_trace_le_card_mul_operatorNorm (G' e * P' j - G e * P j)).trans
    (mul_le_mul_of_nonneg_left hop (Nat.cast_nonneg n))

/-- A uniform coordinatewise error bound gives a Euclidean error bound larger by at most the
square root of the number of coordinates. Under [the listed assumptions](hyp:hb,hcoord), [the stated conclusion follows](goal). -/
theorem finiteFrobeniusNorm_sub_le_sqrt_mul {p : ℕ} (x y : Vec p) {b : ℝ}
    (hb : 0 ≤ b) (hcoord : ∀ i, |x i - y i| ≤ b) :
    finiteFrobeniusNorm (x - y) ≤ Real.sqrt p * b := by
  have hsum : ∑ i, (x i - y i) ^ 2 ≤ p * b ^ 2 := by
    calc
      ∑ i, (x i - y i) ^ 2 ≤ ∑ _i : Fin p, b ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) hb).2 (hcoord i)
      _ = p * b ^ 2 := by simp
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hb)).mp
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    mul_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
  simpa only [Pi.sub_apply] using hsum

/-- Normalization is quantitatively stable away from zero: the distance between normalized
vectors is at most twice their original distance divided by the smaller input norm. Under [the listed assumptions](hyp:hx,hy), [the stated conclusion follows](goal). -/
theorem normalizeVec_sub_normalizeVec_le {p : ℕ} (x y : Vec p)
    (hx : 0 < finiteFrobeniusNorm x) (hy : 0 < finiteFrobeniusNorm y) :
    finiteFrobeniusNorm (normalizeVec x - normalizeVec y) ≤
      2 * finiteFrobeniusNorm (x - y) /
        min (finiteFrobeniusNorm x) (finiteFrobeniusNorm y) := by
  simpa only [normalizeVec] using
    normalizeFinite_sub_normalizeFinite_le x y hx hy

/-- Positively rescaling a unit vector and then normalizing returns the original vector. Under [the listed assumptions](hyp:hc,ha), [the stated conclusion follows](goal). -/
-- Proof route: compute the squared Frobenius norm of `a⁻¹ • c`, use positivity of `a` to
-- simplify `|a⁻¹|`, then unfold normalization and cancel the nonzero scale.
theorem normalizeVec_inv_smul_eq {p : ℕ} (c : Vec p) (a : ℝ)
    (hc : finiteFrobeniusNorm c = 1) (ha : 0 < a) :
    normalizeVec (a⁻¹ • c) = c := by
  have hscale : finiteFrobeniusNorm (a⁻¹ • c) = a⁻¹ := by
    rw [finiteFrobeniusNorm_smul, hc, mul_one,
      abs_of_pos (inv_pos.mpr ha)]
  ext i
  simp [normalizeVec, normalizeFinite, hscale, ha.ne']

/-- If corresponding columns have Euclidean error at most `b`, their matrix Frobenius error is at
most `sqrt n * b`. Under [the listed assumptions](hyp:hb,hcol), [the stated conclusion follows](goal). -/
-- Proof route: unfold the matrix norm, regroup the entry sum by columns, square every column
-- bound, sum, and use `Real.sqrt_le_sqrt` together with `Real.sq_sqrt`.
theorem matrixFrobeniusNorm_le_sqrt_mul_of_columns {p n : ℕ}
    (A B : FactorMatrix p n) {b : ℝ} (hb : 0 ≤ b)
    (hcol : ∀ j, finiteFrobeniusNorm (A.col j - B.col j) ≤ b) :
    matrixFrobeniusNorm (A - B) ≤ Real.sqrt n * b := by
  have hcolSq (j : Fin n) :
      ∑ i, (A i j - B i j) ^ 2 ≤ b ^ 2 := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg _) hb).2 (hcol j)
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
    simpa only [Matrix.col_apply, Pi.sub_apply] using h
  have hsum : ∑ x : Fin p × Fin n, ((A - B) x.1 x.2) ^ 2 ≤ n * b ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc
      ∑ j : Fin n, ∑ i : Fin p, ((A - B) i j) ^ 2 ≤
          ∑ _j : Fin n, b ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [Matrix.sub_apply] using hcolSq j
      _ = n * b ^ 2 := by simp
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hb)).mp
  change (Real.sqrt (∑ x : Fin p × Fin n, ((A - B) x.1 x.2) ^ 2)) ^ 2 ≤
    (Real.sqrt n * b) ^ 2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  exact hsum

/-- Permute the columns of a finite factor matrix. With [its explicit inputs](hyp:C,pi), [the defined object](goal) is [given by the displayed formula](step:1). -/
def permuteColumns {p n : ℕ} (C : FactorMatrix p n) (pi : Equiv.Perm (Fin n)) :
    FactorMatrix p n :=
  fun i j => C i (pi j)

end Causalean.Mathlib.Analysis.SymmetricTensorPencil
