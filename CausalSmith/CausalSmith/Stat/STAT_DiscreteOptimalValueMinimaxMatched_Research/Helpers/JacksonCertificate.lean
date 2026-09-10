import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.JacksonKernel
import Mathlib.Data.Fintype.Order

/-! Simultaneous pointwise and coefficient control for the tensor Jackson approximant. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory
open scoped BigOperators

/-- For [the specified rectangle or law, second cell vector](hyp:Q,v), the [rectangle-membership condition requires every cell coordinate to lie between its lower and upper endpoints](goal). In each cell, [the coordinate is at least the lower endpoint](step:1) and [at most the upper endpoint](step:2). -/
def inRectangle (Q : Rectangle) (v : Cell → ℝ) : Prop :=
  ∀ j, Q.1 j ≤ v j ∧ v j ≤ Q.2 j

/-- For [the specified rectangle or law, degree, second cell vector](hyp:Q,K,v), the [Jackson pointwise scale sums the local square-root boundary widths and second-order rectangle radii across the four cells](goal). -/
noncomputable def jacksonPointwiseScale (Q : Rectangle) (K : ℕ) (v : Cell → ℝ) : ℝ :=
  ∑ j : Cell, (Real.sqrt ((v j - Q.1 j) * (Q.2 j - v j)) / K +
    rectangleRadius Q j / K ^ 2)

-- @node: tensorConvolution_approx_weighted
/-- A tensor Jackson convolution inherits a coordinatewise first/second-order modulus. This uses [the approximation degree satisfies its stated restriction](hyp:hK), and [the Lipschitz scale is positive](hyp:hL), and [the target function is continuous](hyp:hf), and [the linear weights are nonnegative](hyp:ha), and [the quadratic weights are nonnegative](hyp:hb), and [the target function obeys the stated weighted increment bound](hyp:hdiff). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma tensorConvolution_approx_weighted {d K : ℕ} (hK : 0 < K)
    (f : (Fin d → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ContinuousOn f
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube d))
    (a b : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (x : Fin d → ℝ)
    (hdiff : ∀ u,
      |f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u)) -
          f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x)| ≤
        L * ∑ i, (a i * |u i| + b i * (u i) ^ 2)) :
    |Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K f x -
        f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x)| ≤
      L * ∑ i, (32 * a i / (K : ℝ) + 64 * b i / (K : ℝ) ^ 2) := by
  classical
  let box := Causalean.Mathlib.Analysis.JacksonApproximation.periodBox d
  let ker := Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K d
  have hcompact : IsCompact box := by
    rw [show box = {u | ∀ i, u i ∈ Set.Icc (-Real.pi) Real.pi} by rfl]
    exact isCompact_pi_infinite fun _ => isCompact_Icc
  have hfcos : Continuous (fun u : Fin d → ℝ =>
      f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u))) := by
    apply hf.comp_continuous
    · unfold Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint
      fun_prop
    · exact fun u =>
        Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint_mem_normalizedCube (x - u)
  have hker : Continuous ker := by
    dsimp [ker]
    unfold Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson
    fun_prop
  have hintDiff : IntegrableOn (fun u : Fin d → ℝ =>
      (f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u)) -
        f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x)) * ker u) box :=
    ((hfcos.sub continuous_const).mul hker).continuousOn.integrableOn_compact hcompact
  have hintBound : IntegrableOn (fun u : Fin d → ℝ =>
      L * (∑ i, (a i * |u i| + b i * (u i) ^ 2)) * ker u) box := by
    have hc : Continuous (fun u : Fin d → ℝ =>
        L * (∑ i, (a i * |u i| + b i * (u i) ^ 2)) * ker u) := by
      fun_prop
    exact hc.continuousOn.integrableOn_compact hcompact
  have hconvDiff :
      Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K f x -
          f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x) =
        ∫ u in box,
          (f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u)) -
            f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x)) * ker u := by
    unfold Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution
    dsimp [box, ker]
    calc
      (∫ u in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox d,
          f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u)) *
            Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K d u) -
          f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x) =
          (∫ u in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox d,
            f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u)) *
              Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K d u) -
          f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x) *
            (∫ u in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox d,
              Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K d u) := by
            rw [Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson_integral_eq_one hK,
              mul_one]
      _ = (∫ u in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox d,
            f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u)) *
              Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K d u) -
          ∫ u in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox d,
            f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x) *
              Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K d u := by
            rw [MeasureTheory.integral_const_mul]
      _ = _ := by
        rw [← MeasureTheory.integral_sub]
        · apply MeasureTheory.integral_congr_ae
          filter_upwards
          intro u
          ring
        · exact (hfcos.mul hker).continuousOn.integrableOn_compact hcompact
        · exact (continuous_const.mul hker).continuousOn.integrableOn_compact hcompact
  rw [hconvDiff]
  calc
    |∫ u in box, (f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u)) -
        f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x)) * ker u| ≤
        ∫ u in box, |(f
          (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u)) -
          f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x)) * ker u| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ u in box, L * (∑ i, (a i * |u i| + b i * (u i) ^ 2)) * ker u := by
      apply setIntegral_mono hintDiff.abs hintBound
      intro u
      change |(f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u)) -
          f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x)) * ker u| ≤ _
      rw [abs_mul, abs_of_nonneg
        (Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson_nonneg hK u)]
      exact mul_le_mul_of_nonneg_right (hdiff u)
        (Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson_nonneg hK u)
    _ = L * ∑ i, (a i * (∫ u in box, |u i| * ker u) +
          b i * (∫ u in box, (u i) ^ 2 * ker u)) := by
      rw [show (fun u => L * (∑ i, (a i * |u i| + b i * (u i) ^ 2)) * ker u) =
        fun u => L * ((∑ i, (a i * |u i| + b i * (u i) ^ 2)) * ker u) by
          funext u; ring, MeasureTheory.integral_const_mul]
      rw [show (fun u => (∑ i, (a i * |u i| + b i * (u i) ^ 2)) * ker u) =
        fun u => ∑ i, (a i * |u i| + b i * (u i) ^ 2) * ker u by
          funext u; rw [Finset.sum_mul]]
      rw [MeasureTheory.integral_finsetSum]
      · apply congrArg
        apply Finset.sum_congr rfl
        intro i _
        have hfirst : IntegrableOn (fun u : Fin d → ℝ =>
            a i * (|u i| * ker u)) box := by
          exact (show Continuous (fun u : Fin d → ℝ =>
            a i * (|u i| * ker u)) by fun_prop).continuousOn.integrableOn_compact hcompact
        have hsecond : IntegrableOn (fun u : Fin d → ℝ =>
            b i * ((u i) ^ 2 * ker u)) box := by
          exact (show Continuous (fun u : Fin d → ℝ =>
            b i * ((u i) ^ 2 * ker u)) by fun_prop).continuousOn.integrableOn_compact hcompact
        rw [show (fun u => (a i * |u i| + b i * (u i) ^ 2) * ker u) =
          fun u => a i * (|u i| * ker u) + b i * ((u i) ^ 2 * ker u) by
            funext u; ring]
        rw [MeasureTheory.integral_add hfirst hsecond, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
      · intro i _
        exact (show Continuous (fun u : Fin d → ℝ =>
          (a i * |u i| + b i * (u i) ^ 2) * ker u) by
            fun_prop).continuousOn.integrableOn_compact hcompact
    _ ≤ L * ∑ i, (a i * (32 / (K : ℝ)) + b i * (64 / (K : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hL
      apply Finset.sum_le_sum
      intro i _
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (ha i)
        dsimp [box, ker]
        rw [Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson_first_moment_eq hK i]
        exact Causalean.Mathlib.Analysis.JacksonApproximation.jackson_first_moment K hK
      · apply mul_le_mul_of_nonneg_left _ (hb i)
        dsimp [box, ker]
        rw [Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson_second_moment_eq hK i]
        exact Causalean.Mathlib.Analysis.JacksonApproximation.jackson_second_moment K hK
    _ = L * ∑ i, (32 * a i / (K : ℝ) + 64 * b i / (K : ℝ) ^ 2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

-- @node: abs_cos_sub_shift_le
/-- A cosine shift has the first/second-order bound used at rectangle faces. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma abs_cos_sub_shift_le (x u : ℝ) :
    |Real.cos (x - u) - Real.cos x| ≤ |Real.sin x| * |u| + u ^ 2 / 2 := by
  calc
    |Real.cos (x - u) - Real.cos x| =
        |Real.cos x * (Real.cos u - 1) + Real.sin x * Real.sin u| := by
          rw [Real.cos_sub]
          congr 1
          ring
    _ ≤ |Real.cos x * (Real.cos u - 1)| + |Real.sin x * Real.sin u| :=
      abs_add_le _ _
    _ = |Real.cos x| * (1 - Real.cos u) + |Real.sin x| * |Real.sin u| := by
      rw [abs_mul, abs_mul, abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one u))]
      ring
    _ ≤ 1 * (u ^ 2 / 2) + |Real.sin x| * |u| := by
      apply add_le_add
      · apply mul_le_mul (Real.abs_cos_le_one x)
          (by linarith [Real.one_sub_sq_div_two_le_cos (x := u)])
          (sub_nonneg.mpr (Real.cos_le_one u)) (by positivity)
      · exact mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (abs_nonneg _)
    _ = |Real.sin x| * |u| + u ^ 2 / 2 := by ring

/-- A finite centered, radius-scaled monomial expansion of a physical polynomial. -/
def CenteredCoefficientExpansion (epsilon : ℝ) (Q : Rectangle)
    (p : MvPolynomial Cell ℝ) (S : Finset (Cell →₀ ℕ))
    (coeff : (Cell →₀ ℕ) → ℝ) : Prop :=
  ∀ v : Cell → ℝ,
    MvPolynomial.eval v p - globalCellValue epsilon (rectangleCenter Q) =
      ∑ alpha ∈ S, coeff alpha *
        ∏ j : Cell, ((v j - rectangleCenter Q j) / rectangleRadius Q j) ^ alpha j

-- @node: lem:simultaneous-jackson-certificate
/-- [one universal exponential coefficient constant yields, for every overlap level, simultaneous degree, approximation, and centered-coefficient bounds for the Jackson polynomial](goal). -/
lemma simultaneous_jackson_certificate :
    ∃ A : ℝ, 0 < A ∧ ∀ epsilon : ℝ,
      0 < epsilon → epsilon < 1 / 2 →
      ∃ Cepsilon : ℝ, 0 < Cepsilon ∧ ∀ (K : ℕ) (Q : Rectangle),
        ∀ (hK : 2 ≤ K), ∀ (hQ : Q.Valid),
        ∀ (hQ0 : ∀ j, 0 ≤ Q.1 j), (∀ j, 0 < rectangleRadius Q j) →
        let p := jacksonTensorPolynomial epsilon K hK Q hQ hQ0
        (∀ j, p.degreeOf j ≤ 2 * (K - 1)) ∧
        (∀ v, inRectangle Q v →
          |MvPolynomial.eval v p - globalCellValue epsilon v| ≤
            Cepsilon * jacksonPointwiseScale Q K v) ∧
        ∃ S : Finset (Cell →₀ ℕ), ∃ coeff : (Cell →₀ ℕ) → ℝ,
          CenteredCoefficientExpansion epsilon Q p S coeff ∧
          (∀ alpha ∈ S, ∀ j, alpha j ≤ 2 * (K - 1)) ∧
          (∑ alpha ∈ S, |coeff alpha|) ≤
            A ^ K * (1 + epsilon⁻¹) * ∑ j : Cell, rectangleRadius Q j := by
  classical
  refine ⟨(2 : ℝ) ^ 60, by positivity, ?_⟩
  intro epsilon hepsilon _hepsilon_half
  refine ⟨32 * (1 + epsilon⁻¹), by positivity, ?_⟩
  intro K Q hK _hQ hQ0 hQr
  let data := Classical.choice
    (jacksonTensorPolynomialData_exists epsilon K hK Q hQ0 hepsilon hQr)
  have hp : jacksonTensorPolynomial epsilon K hK Q _hQ hQ0 = data.p := by
    simp only [jacksonTensorPolynomial, dif_pos hepsilon, dif_pos hQr, data]
  dsimp only
  constructor
  · rw [hp]
    exact data.coordinateDegree
  constructor
  · intro v hv
    let e := cellFinFourEquiv
    let c : Fin 4 → ℝ := fun i => rectangleCenter Q (e.symm i)
    let r : Fin 4 → ℝ := fun i => rectangleRadius Q (e.symm i)
    let y : Fin 4 → ℝ := fun i => v (e.symm i)
    let z := Causalean.Mathlib.Analysis.JacksonApproximation.normalizedPoint c r y
    let x : Fin 4 → ℝ := fun i => Real.arccos (z i)
    let F : (Fin 4 → ℝ) → ℝ := fun w => jacksonAffineFunction epsilon
      (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r w)
    have hr : ∀ i, 0 < r i := fun i => hQr (e.symm i)
    have hy : y ∈ Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r := by
      intro i
      dsimp [y, c, r]
      rw [abs_le]
      have hi := hv (e.symm i)
      constructor <;> simp only [rectangleCenter, rectangleRadius] <;> nlinarith
    have hz := Causalean.Mathlib.Analysis.JacksonApproximation.normalizedPoint_mem_normalizedCube
      c r y hr hy
    have hcos : Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x = z := by
      funext i
      exact Real.cos_arccos (hz i).1 (hz i).2
    have hnonneg (w : Fin 4 → ℝ)
        (hw : w ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4) :
        ∀ j, 0 ≤ Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r w (e j) := by
      intro j
      have hwj := (hw (e j)).1
      have hlower : c (e j) - r (e j) = Q.1 j := by
        simp only [c, r, Equiv.symm_apply_apply, rectangleCenter, rectangleRadius]
        ring
      dsimp [Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint]
      have hrj := hr (e j)
      rw [show c (e j) = Q.1 j + r (e j) by linarith] 
      nlinarith [hQ0 j]
    have hF : ContinuousOn F
        (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4) := by
      apply LipschitzOnWith.continuousOn
      apply LipschitzOnWith.of_dist_le' (K := (1 + epsilon⁻¹) *
        (∑ i : Fin 4, r i))
      intro w hw w' hw'
      rw [Real.dist_eq]
      have hbase := globalCellValue_lipschitz hepsilon
        (fun j => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r w (e j))
        (fun j => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r w' (e j))
        (hnonneg w hw) (hnonneg w' hw')
      dsimp [F, jacksonAffineFunction]
      refine hbase.trans ?_
      unfold l1CellDistance
      have hcoord (i : Fin 4) :
          |Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r w i -
              Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r w' i| ≤
            r i * dist w w' := by
        have hi : |w i - w' i| ≤ dist w w' := by
          simpa [Real.dist_eq] using dist_le_pi_dist w w' i
        simp only [Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint]
        rw [show c i + r i * w i - (c i + r i * w' i) = r i * (w i - w' i) by ring,
          abs_mul, abs_of_pos (hr i)]
        exact mul_le_mul_of_nonneg_left hi (le_of_lt (hr i))
      calc
        (1 + epsilon⁻¹) *
            (∑ j : Cell,
              |Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r w (e j) -
                Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r w' (e j)|) ≤
            (1 + epsilon⁻¹) * ∑ i : Fin 4, r i * dist w w' := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              calc
                (∑ j : Cell,
                  |Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r w (e j) -
                    Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r w' (e j)|) =
                    ∑ i : Fin 4,
                      |Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r w i -
                        Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r w' i| :=
                  Fintype.sum_equiv e _ _ (fun j => by simp)
                _ ≤ ∑ i : Fin 4, r i * dist w w' :=
                  Finset.sum_le_sum fun i _ => hcoord i
        _ = (1 + epsilon⁻¹) * (∑ i : Fin 4, r i) * dist w w' := by
          rw [show (∑ i : Fin 4, r i * dist w w') =
            (∑ i : Fin 4, r i) * dist w w' by rw [Finset.sum_mul]]
          ring
    have hdiff (u : Fin 4 → ℝ) :
        |F (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u)) -
            F (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x)| ≤
          (1 + epsilon⁻¹) * ∑ i,
            (r i * |Real.sin (x i)| * |u i| + (r i / 2) * (u i) ^ 2) := by
      have hbase := globalCellValue_lipschitz hepsilon
        (fun j => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
          (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u)) (e j))
        (fun j => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
          (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x) (e j))
        (hnonneg _ (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint_mem_normalizedCube _))
        (hnonneg _ (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint_mem_normalizedCube _))
      dsimp [F, jacksonAffineFunction]
      refine hbase.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      unfold l1CellDistance
      calc
        (∑ j : Cell, |(fun j =>
            Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
              (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u)) (e j)) j -
            (fun j => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
              (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x) (e j)) j|) =
            ∑ i : Fin 4,
              |Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
                (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (x - u)) i -
               Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
                (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x) i| :=
          Fintype.sum_equiv e _ _ (fun j => by simp)
        _ ≤ ∑ i : Fin 4,
            (r i * |Real.sin (x i)| * |u i| + (r i / 2) * (u i) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          simp only [Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint,
            Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint, Pi.sub_apply]
          rw [show c i + r i * Real.cos (x i - u i) - (c i + r i * Real.cos (x i)) =
            r i * (Real.cos (x i - u i) - Real.cos (x i)) by ring,
            abs_mul, abs_of_pos (hr i)]
          nlinarith [mul_le_mul_of_nonneg_left (abs_cos_sub_shift_le (x i) (u i))
            (le_of_lt (hr i))]
    have happ := tensorConvolution_approx_weighted (lt_of_lt_of_le (by omega) hK)
      F (1 + epsilon⁻¹) (by positivity) hF
      (fun i => r i * |Real.sin (x i)|) (fun i => r i / 2)
      (fun i => mul_nonneg (le_of_lt (hr i)) (abs_nonneg _))
      (fun i => div_nonneg (le_of_lt (hr i)) (by norm_num)) x hdiff
    rw [hp]
    have heval := data.convolutionEval (fun j => x (e j))
    have hphysical : (fun j => rectangleCenter Q j + rectangleRadius Q j *
        Real.cos (x (e j))) = v := by
      funext j
      have haff := Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint_normalizedPoint
        c r y hr
      have hj := congrFun haff (e j)
      calc
        rectangleCenter Q j + rectangleRadius Q j * Real.cos (x (e j)) =
            Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
              (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x) (e j) := by
                simp [c, r, e,
                  Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint,
                  Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint]
        _ = Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z (e j) := by
          rw [hcos]
        _ = Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r
              (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedPoint c r y) (e j) := rfl
        _ = y (e j) := hj
        _ = v j := by simp [y, e]
    rw [hphysical] at heval
    rw [heval]
    have hconv : jacksonSubstrateConvolution epsilon K Q (fun j => x (e j)) =
        Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K F x := by
      rfl
    rw [hconv]
    have hFv : F (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x) =
        globalCellValue epsilon v := by
      dsimp [F, jacksonAffineFunction]
      change globalCellValue epsilon
        (fun j => rectangleCenter Q j + rectangleRadius Q j * Real.cos (x (e j))) = _
      rw [hphysical]
    rw [hFv] at happ
    refine happ.trans_eq ?_
    have hsin (j : Cell) :
        r (e j) * |Real.sin (x (e j))| =
          Real.sqrt ((v j - Q.1 j) * (Q.2 j - v j)) := by
      rw [show x (e j) = Real.arccos (z (e j)) by rfl,
        Real.sin_arccos, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hzj : z (e j) = (v j - rectangleCenter Q j) / rectangleRadius Q j := by
        simp [z, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedPoint,
          y, c, r, e]
      rw [hzj]
      have halg : (v j - Q.1 j) * (Q.2 j - v j) =
          (rectangleRadius Q j) ^ 2 *
            (1 - ((v j - rectangleCenter Q j) / rectangleRadius Q j) ^ 2) := by
        field_simp [ne_of_gt (hQr j)]
        simp only [rectangleCenter, rectangleRadius]
        ring
      rw [halg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_pos (hQr j)]
      simp [r, e]
    have hscale : (∑ i : Fin 4,
        (32 * (r i * |Real.sin (x i)|) / (K : ℝ) +
          64 * (r i / 2) / (K : ℝ) ^ 2)) =
        32 * jacksonPointwiseScale Q K v := by
      unfold jacksonPointwiseScale
      calc
        (∑ i : Fin 4, (32 * (r i * |Real.sin (x i)|) / (K : ℝ) +
            64 * (r i / 2) / (K : ℝ) ^ 2)) =
            ∑ j : Cell, (32 * (r (e j) * |Real.sin (x (e j))|) / (K : ℝ) +
              64 * (r (e j) / 2) / (K : ℝ) ^ 2) :=
          Fintype.sum_equiv e.symm _ _ (fun i => by simp)
        _ = 32 * ∑ j : Cell,
            (Real.sqrt ((v j - Q.1 j) * (Q.2 j - v j)) / (K : ℝ) +
              rectangleRadius Q j / (K : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [hsin j]
          simp only [r, Equiv.symm_apply_apply]
          ring
    rw [hscale]
    ring_nf
  · let qCell : MvPolynomial Cell ℝ := MvPolynomial.rename cellFinFourEquiv.symm data.q
    let g : (Fin 4 →₀ ℕ) → (Cell →₀ ℕ) := Finsupp.mapDomain cellFinFourEquiv.symm
    refine ⟨data.q.support.image g, qCell.coeff, ?_, ?_, ?_⟩
    · intro v
      rw [hp, data.physicalEval]
      change MvPolynomial.eval
        ((fun j => (v j - rectangleCenter Q j) / rectangleRadius Q j) ∘
          cellFinFourEquiv.symm) data.q = _
      rw [← MvPolynomial.eval_rename]
      change MvPolynomial.eval _ qCell = _
      rw [MvPolynomial.eval_eq']
      rw [show qCell.support = data.q.support.image g by
        exact MvPolynomial.support_rename_of_injective cellFinFourEquiv.symm.injective]
    · intro alpha halpha j
      rw [Finset.mem_image] at halpha
      obtain ⟨beta, hbeta, rfl⟩ := halpha
      have hmap : g beta j = beta (cellFinFourEquiv j) := by
        exact Finsupp.mapDomain_equiv_apply beta j
      rw [hmap]
      exact data.normalizedCoordinateDegree beta hbeta (cellFinFourEquiv j)
    · change (∑ alpha ∈ data.q.support.image g, |qCell.coeff alpha|) ≤ _
      rw [Finset.sum_image (Finsupp.mapDomain_injective
        cellFinFourEquiv.symm.injective).injOn]
      simp only [qCell, MvPolynomial.coeff_rename_mapDomain,
        cellFinFourEquiv.symm.injective]
      change Causalean.Mathlib.Analysis.JacksonApproximation.mvCoeffL1 data.q ≤ _
      refine data.coefficientBound.trans ?_
      have hpow : (2 : ℝ) ^ (40 * K + 20) ≤ ((2 : ℝ) ^ 60) ^ K := by
        rw [← pow_mul]
        exact_mod_cast Nat.pow_le_pow_right (n := 2) (by omega)
          (by omega : 40 * K + 20 ≤ 60 * K)
      gcongr
      exact Finset.sum_nonneg fun j _ => le_of_lt (hQr j)

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
