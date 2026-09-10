import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.ConeExtension
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.GlobalLipschitz
import Causalean.Mathlib.Analysis.JacksonApproximation.AffineFour
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.MvPolynomial.Degrees

/-! The order-four Jackson kernel and its tensor-convolution representation. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory
open scoped BigOperators Interval

/-- A pilot rectangle represented by lower and upper endpoints. -/
abbrev Rectangle := (Cell → ℝ) × (Cell → ℝ)
  -- @realizes \(Q_x\)(four-dimensional endpoint rectangle)

/-- The endpoint condition required of a genuine rectangle. -/
def Rectangle.Valid (Q : Rectangle) : Prop := ∀ j, Q.1 j ≤ Q.2 j

/-- For [the specified rectangle or law, cell index](hyp:Q,j), the [rectangle center is the midpoint of the lower and upper endpoint in the selected cell](goal). -/
noncomputable def rectangleCenter (Q : Rectangle) (j : Cell) : ℝ := (Q.1 j + Q.2 j) / 2
/-- For [the specified rectangle or law, cell index](hyp:Q,j), the [rectangle radius is half the difference between the upper and lower endpoint in the selected cell](goal). -/
noncomputable def rectangleRadius (Q : Rectangle) (j : Cell) : ℝ := (Q.2 j - Q.1 j) / 2

-- @node: cellFinFourEquiv
/-- The canonical enumeration of the four treatment--outcome coordinates. -/
def cellFinFourEquiv : Cell ≃ Fin 4 := finProdFinEquiv

-- @node: jacksonAffineFunction
/-- The cell functional, reindexed on the four-coordinate type used by the Jackson substrate. -/
noncomputable def jacksonAffineFunction (epsilon : ℝ) : (Fin 4 → ℝ) → ℝ :=
  fun y => globalCellValue epsilon (fun j => y (cellFinFourEquiv j))

-- @node: jacksonSubstrateConvolution
/-- The affine tensor Jackson convolution after enumerating the four cell coordinates. -/
noncomputable def jacksonSubstrateConvolution (epsilon : ℝ) (K : ℕ)
    (Q : Rectangle) (theta : Cell → ℝ) : ℝ :=
  Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K
    (fun z => jacksonAffineFunction epsilon
      (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
        (fun i => rectangleCenter Q (cellFinFourEquiv.symm i))
        (fun i => rectangleRadius Q (cellFinFourEquiv.symm i)) z))
    (fun i => theta (cellFinFourEquiv.symm i))

-- @node: JacksonTensorPolynomialData
/-- One polynomial together with the normalized-coordinate representative used for its
coefficient envelope. -/
structure JacksonTensorPolynomialData (epsilon : ℝ) (K : ℕ) (Q : Rectangle) where
  p : MvPolynomial Cell ℝ
  q : MvPolynomial (Fin 4) ℝ
  coordinateDegree : ∀ j, p.degreeOf j ≤ 2 * (K - 1)
  normalizedCoordinateDegree : ∀ m ∈ q.support, ∀ i, m i ≤ 2 * (K - 1)
  physicalEval : ∀ y : Cell → ℝ,
    MvPolynomial.eval y p - globalCellValue epsilon (rectangleCenter Q) =
      MvPolynomial.eval
        (fun i => (y (cellFinFourEquiv.symm i) -
          rectangleCenter Q (cellFinFourEquiv.symm i)) /
            rectangleRadius Q (cellFinFourEquiv.symm i)) q
  convolutionEval : ∀ theta : Cell → ℝ,
    MvPolynomial.eval (fun j => rectangleCenter Q j +
      rectangleRadius Q j * Real.cos (theta j)) p =
      jacksonSubstrateConvolution epsilon K Q theta
  coefficientBound :
    Causalean.Mathlib.Analysis.JacksonApproximation.mvCoeffL1 q ≤
      (2 : ℝ) ^ (40 * K + 20) * (1 + epsilon⁻¹) *
        ∑ j : Cell, rectangleRadius Q j

-- @node: jacksonTensorPolynomialData_exists
/-- If [the approximation degree satisfies its stated restriction](hyp:hK), and [the stated q0 condition holds](hyp:hQ0), and [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the stated qr condition holds](hyp:hQr), then [the stated jackson tensor polynomial data exists relation holds](goal). -/
lemma jacksonTensorPolynomialData_exists (epsilon : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (Q : Rectangle) (hQ0 : ∀ j, 0 ≤ Q.1 j)
    (hepsilon : 0 < epsilon) (hQr : ∀ j, 0 < rectangleRadius Q j) :
    Nonempty (JacksonTensorPolynomialData epsilon K Q) := by
  classical
  let e := cellFinFourEquiv
  let c : Fin 4 → ℝ := fun i => rectangleCenter Q (e.symm i)
  let r : Fin 4 → ℝ := fun i => rectangleRadius Q (e.symm i)
  let f : (Fin 4 → ℝ) → ℝ := jacksonAffineFunction epsilon
  let f0 : (Fin 4 → ℝ) → ℝ := fun y => f y - f c
  let B : ℝ := (1 + epsilon⁻¹) * ∑ j : Cell, rectangleRadius Q j
  have hr : ∀ i, 0 < r i := fun i => hQr (e.symm i)
  have hnonneg : ∀ y ∈
      Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r,
      ∀ j, 0 ≤ y (e j) := by
    intro y hy j
    have hj := hy (e j)
    dsimp [c, r] at hj
    simp only [Equiv.symm_apply_apply] at hj
    rw [abs_le] at hj
    have hc : rectangleCenter Q j - rectangleRadius Q j = Q.1 j := by
      simp only [rectangleCenter, rectangleRadius]
      ring
    nlinarith [hQ0 j]
  have hc_mem : c ∈
      Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r := by
    intro i
    simp [le_of_lt (hr i)]
  have hf : ContinuousOn f
      (Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r) := by
    apply LipschitzOnWith.continuousOn
    apply LipschitzOnWith.of_dist_le' (K := 4 * (1 + epsilon⁻¹))
    intro y hy z hz
    rw [Real.dist_eq]
    have hbase := globalCellValue_lipschitz hepsilon
      (fun j => y (e j)) (fun j => z (e j)) (hnonneg y hy) (hnonneg z hz)
    have hsum : l1CellDistance (fun j => y (e j)) (fun j => z (e j)) ≤
        4 * dist y z := by
      unfold l1CellDistance
      calc
        (∑ j : Cell, |y (e j) - z (e j)|) ≤ ∑ _j : Cell, dist y z := by
          gcongr with j
          have hcoord : dist (y (e j)) (z (e j)) ≤ dist y z := by
            exact_mod_cast nndist_le_pi_nndist y z (e j)
          simpa [Real.dist_eq] using hcoord
        _ = 4 * dist y z := by simp [Fintype.card_congr e]
    calc
      _ ≤ (1 + epsilon⁻¹) * (4 * dist y z) :=
        hbase.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
      _ = 4 * (1 + epsilon⁻¹) * dist y z := by ring
  have hf0 : ContinuousOn f0
      (Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r) :=
    hf.sub continuousOn_const
  have haff : Continuous
      (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r) := by
    apply continuous_pi
    intro i
    exact continuous_const.add (continuous_const.mul (continuous_apply i))
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => le_of_lt (hQr j))
  have hbound : ∀ y ∈
      Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r,
      |f0 y| ≤ B := by
    intro y hy
    have hbase := globalCellValue_lipschitz hepsilon
      (fun j => y (e j)) (fun j => c (e j)) (hnonneg y hy) (hnonneg c hc_mem)
    refine hbase.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    unfold l1CellDistance
    apply Finset.sum_le_sum
    intro j _
    simpa [c, r, e] using hy (e j)
  have hpull : ContinuousOn
      (fun z => f0 (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4) := by
    apply hf0.comp
    · exact haff.continuousOn
    · exact fun z hz =>
        Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint_mem_centeredRectangle
          c r z hr hz
  have hbound_pull : ∀ z ∈
      Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4,
      |f0 (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z)| ≤ B :=
    fun z hz => hbound _
      (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint_mem_centeredRectangle
        c r z hr hz)
  obtain ⟨q, hqeval, hqcoord, _hqtotal, hqcoeff⟩ :=
    Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution_exists_mvPolynomial_four_coeffBound
      (lt_of_lt_of_le (by omega) hK) _ B hB hpull hbound_pull
  obtain ⟨p4, hp4eval, hp4coord, _hp4total, _⟩ :=
    Causalean.Mathlib.Analysis.JacksonApproximation.mvPolynomial_affine_substitution_four
      q c r (2 * (K - 1)) hr hqcoord
  let p : MvPolynomial Cell ℝ :=
    MvPolynomial.rename e.symm p4 + MvPolynomial.C (globalCellValue epsilon (rectangleCenter Q))
  have hpdeg : ∀ j, p.degreeOf j ≤ 2 * (K - 1) := by
    intro j
    apply (MvPolynomial.degreeOf_add_le _ _ _).trans
    simp only [p, sup_le_iff]
    constructor
    · rw [show j = e.symm (e j) by simp,
        MvPolynomial.degreeOf_rename_of_injective e.symm.injective]
      exact MvPolynomial.degreeOf_le_iff.mpr (fun m hm => hp4coord m hm (e j))
    · simp
  refine ⟨⟨p, q, hpdeg, hqcoord, ?_, ?_, ?_⟩⟩
  · intro y
    simp only [p, MvPolynomial.eval_add, MvPolynomial.eval_rename, MvPolynomial.eval_C,
      add_sub_cancel_right]
    rw [hp4eval]
    rfl
  · intro theta
    simp only [p, MvPolynomial.eval_add, MvPolynomial.eval_rename, MvPolynomial.eval_C]
    rw [hp4eval]
    have hnorm := Causalean.Mathlib.Analysis.JacksonApproximation.normalizedPoint_affinePoint
      c r (fun i => Real.cos (theta (e.symm i))) hr
    rw [show ((fun j => rectangleCenter Q j + rectangleRadius Q j * Real.cos (theta j)) ∘
        e.symm) = Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
          (fun i => Real.cos (theta (e.symm i))) by rfl, hnorm]
    change MvPolynomial.eval
        (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint
          (fun i => theta (e.symm i))) q + _ = _
    rw [hqeval]
    change Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K
        (fun z => f0 (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z)) _ +
          globalCellValue epsilon (rectangleCenter Q) = _
    unfold Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution
    rw [show (fun u => f0 (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
          (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint
            ((fun i => theta (e.symm i)) - u))) *
          Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K 4 u) =
        fun u => f (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
          (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint
            ((fun i => theta (e.symm i)) - u))) *
            Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K 4 u -
          f c * Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K 4 u by
            funext u; dsimp [f0]; ring]
    rw [MeasureTheory.integral_sub]
    · rw [MeasureTheory.integral_const_mul,
        Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson_integral_eq_one
          (lt_of_lt_of_le (by omega) hK)]
      have hfc : f c = globalCellValue epsilon (rectangleCenter Q) := by
        simp [f, c, e, jacksonAffineFunction]
      rw [hfc]
      rw [mul_one, sub_add_cancel]
      unfold jacksonSubstrateConvolution
      simp only [Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution]
      rfl
    · have hcompact : IsCompact
          (Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4) := by
        rw [show Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4 =
          {u | ∀ i, u i ∈ Set.Icc (-Real.pi) Real.pi} by rfl]
        exact isCompact_pi_infinite fun _ => isCompact_Icc
      have hcosaff : Continuous (fun u : Fin 4 → ℝ =>
          Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
            (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint
              ((fun i => theta (e.symm i)) - u))) := by
        exact haff.comp (by unfold Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint; fun_prop)
      have hkernel : Continuous
          (Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K 4) := by
        unfold Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson
        fun_prop
      exact ((hf.comp_continuous hcosaff (fun _ =>
          Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint_mem_centeredRectangle
            c r _ hr (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint_mem_normalizedCube _))).mul
          hkernel).continuousOn.integrableOn_compact hcompact
    · have hcompact : IsCompact
          (Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4) := by
        rw [show Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4 =
          {u | ∀ i, u i ∈ Set.Icc (-Real.pi) Real.pi} by rfl]
        exact isCompact_pi_infinite fun _ => isCompact_Icc
      have hkernel : Continuous
          (Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K 4) := by
        unfold Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson
        fun_prop
      exact (continuous_const.mul hkernel).continuousOn.integrableOn_compact hcompact
  · dsimp [B] at hqcoeff
    nlinarith

/-- On a rectangle with at least one zero-radius coordinate, the tensor convolution still has a
physical-coordinate polynomial representative.  Zero-radius coordinates are frozen at their
singleton endpoint rather than causing the whole polynomial to vanish. This uses [the approximation degree satisfies its stated restriction](hyp:hK), and [the potential-outcome law satisfies the stated causal restrictions](hyp:hQ), and [the stated q0 condition holds](hyp:hQ0), and [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the stated deg condition holds](hyp:_hdeg). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma jacksonTensorPolynomial_degenerate_exists (epsilon : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (Q : Rectangle) (hQ : Q.Valid) (hQ0 : ∀ j, 0 ≤ Q.1 j)
    (hepsilon : 0 < epsilon) (_hdeg : ¬ ∀ j, 0 < rectangleRadius Q j) :
    ∃ p : MvPolynomial Cell ℝ,
      (∀ j, p.degreeOf j ≤ 2 * (K - 1)) ∧
      ∀ theta : Cell → ℝ,
        MvPolynomial.eval (fun j => rectangleCenter Q j +
          rectangleRadius Q j * Real.cos (theta j)) p =
          jacksonSubstrateConvolution epsilon K Q theta := by
  classical
  let e := cellFinFourEquiv
  let c : Fin 4 → ℝ := fun i => rectangleCenter Q (e.symm i)
  let r : Fin 4 → ℝ := fun i => rectangleRadius Q (e.symm i)
  let f : (Fin 4 → ℝ) → ℝ := jacksonAffineFunction epsilon
  have hr0 : ∀ i, 0 ≤ r i := by
    intro i
    have hi := hQ (e.symm i)
    dsimp [r, rectangleRadius]
    linarith
  have hnonneg : ∀ z ∈
      Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4,
      ∀ j, 0 ≤
        Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z (e j) := by
    intro z hz j
    have hzlo : -1 ≤ z (e j) := (hz (e j)).1
    have hmul : -r (e j) ≤ r (e j) * z (e j) := by
      nlinarith [mul_le_mul_of_nonneg_left hzlo (hr0 (e j))]
    have hc : c (e j) - r (e j) = Q.1 j := by
      simp [c, r, e, rectangleCenter, rectangleRadius]
      ring
    change 0 ≤ c (e j) + r (e j) * z (e j)
    linarith [hQ0 j]
  have hpull : ContinuousOn
      (fun z => f (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4) := by
    apply LipschitzOnWith.continuousOn
    apply LipschitzOnWith.of_dist_le'
      (K := (1 + epsilon⁻¹) * ∑ j : Cell, |r (e j)|)
    intro y hy z hz
    rw [Real.dist_eq]
    have hbase := globalCellValue_lipschitz hepsilon
      (fun j =>
        Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r y (e j))
      (fun j =>
        Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z (e j))
      (hnonneg y hy) (hnonneg z hz)
    have hsum : l1CellDistance
        (fun j => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r y (e j))
        (fun j => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z (e j)) ≤
        (∑ j : Cell, |r (e j)|) * dist y z := by
      unfold l1CellDistance
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      have hcoord : |y (e j) - z (e j)| ≤ dist y z := by
        have h := nndist_le_pi_nndist y z (e j)
        exact_mod_cast h
      simp only [Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint]
      rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left hcoord (abs_nonneg _)
    change |globalCellValue epsilon _ - globalCellValue epsilon _| ≤ _
    calc
      _ ≤ (1 + epsilon⁻¹) * l1CellDistance _ _ := hbase
      _ ≤ (1 + epsilon⁻¹) *
          ((∑ j : Cell, |r (e j)|) * dist y z) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ((1 + epsilon⁻¹) * ∑ j : Cell, |r (e j)|) * dist y z := by ring
  obtain ⟨q, hqeval, hqcoord, _hqtotal⟩ :=
    Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution_exists_mvPolynomial
      (lt_of_lt_of_le (by omega) hK)
      (fun z => f (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z)) hpull
  let r' : Fin 4 → ℝ := fun i => if r i = 0 then 1 else r i
  have hr' : ∀ i, 0 < r' i := by
    intro i
    dsimp [r']
    split_ifs with hi
    · norm_num
    · exact lt_of_le_of_ne (hr0 i) (Ne.symm hi)
  obtain ⟨p4, hp4eval, hp4coord, _hp4total, _hp4coeff⟩ :=
    Causalean.Mathlib.Analysis.JacksonApproximation.mvPolynomial_affine_substitution_four
      q c r' (2 * (K - 1)) hr' hqcoord
  let p : MvPolynomial Cell ℝ := MvPolynomial.rename e.symm p4
  refine ⟨p, ?_, ?_⟩
  · intro j
    rw [show j = e.symm (e j) by simp,
      MvPolynomial.degreeOf_rename_of_injective e.symm.injective]
    exact MvPolynomial.degreeOf_le_iff.mpr (fun m hm => hp4coord m hm (e j))
  · intro theta
    let theta' : Fin 4 → ℝ := fun i => if r i = 0 then Real.pi / 2 else theta (e.symm i)
    have hnorm :
        Causalean.Mathlib.Analysis.JacksonApproximation.normalizedPoint c r'
          ((fun j => rectangleCenter Q j + rectangleRadius Q j * Real.cos (theta j)) ∘
            e.symm) =
          Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint theta' := by
      funext i
      simp only [Causalean.Mathlib.Analysis.JacksonApproximation.normalizedPoint,
        Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint]
      by_cases hi : r i = 0
      · simp [theta', r', hi, c, r, e]
      · simp [theta', r', hi, c, r, e]
    have haffine (u : Fin 4 → ℝ) :
        Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
            (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (theta' - u)) =
          Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
            (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint
              ((fun i => theta (e.symm i)) - u)) := by
      funext i
      by_cases hi : r i = 0
      · simp [Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint, hi]
      · change c i + r i * Real.cos (theta' i - u i) =
          c i + r i * Real.cos (theta (e.symm i) - u i)
        have ht : theta' i = theta (e.symm i) := by simp [theta', hi]
        rw [ht]
    have hconv :
        Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K
            (fun z => f
              (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z)) theta' =
          Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K
            (fun z => f
              (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z))
              (fun i => theta (e.symm i)) := by
      unfold Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution
      congr 1 with u
      change f (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
          (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (theta' - u))) * _ =
        f (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
          (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint
            ((fun i => theta (e.symm i)) - u))) * _
      rw [haffine u]
    simp only [p, MvPolynomial.eval_rename]
    rw [hp4eval, hnorm, hqeval, hconv]
    rfl

-- @node: def:jackson-kernel
/-- The physical-coordinate polynomial induced by the four-dimensional Jackson convolution. -/
noncomputable def jacksonTensorPolynomial (epsilon : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (Q : Rectangle) (hQ : Q.Valid) (hQ0 : ∀ j, 0 ≤ Q.1 j) : MvPolynomial Cell ℝ :=
  if hepsilon : 0 < epsilon then
    if hQr : ∀ j, 0 < rectangleRadius Q j then
      (Classical.choice (jacksonTensorPolynomialData_exists epsilon K hK Q hQ0 hepsilon hQr)).p
    else
      Classical.choose
        (jacksonTensorPolynomial_degenerate_exists epsilon K hK Q hQ hQ0 hepsilon hQr)
  else 0
  -- @realizes \(P_{x,K_d}\)(physical-coordinate polynomial induced by the restricted convolution)

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
