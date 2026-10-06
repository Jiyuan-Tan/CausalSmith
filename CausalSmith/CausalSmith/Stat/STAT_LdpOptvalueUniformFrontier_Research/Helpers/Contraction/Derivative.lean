module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.CanonicalDensity
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.StageIdentification
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Helpers/Contraction/Derivative

Finite original-record private value frontiers: Helpers/Contraction/Derivative.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n d : ℕ}
/-- Fix [the function xi](hyp:xi). [Higher-order elementary-symmetric score recursion](goal). -/
-- @node: scoreElementary
def scoreElementary (xi : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | v+1, k+1 => scoreElementary xi v (k + 1) + xi v * scoreElementary xi v k

/-- [The zeroth elementary score is one at every sample size](goal). -/
-- @node: scoreElementary_zero
lemma scoreElementary_zero (xi : ℕ → ℝ) (v : ℕ) : scoreElementary xi v 0 = 1 := by
  cases v <;> rfl

/-- Assume [the stated h condition](hyp:h). [No subset of a prefix has cardinality greater than that prefix](goal). -/
-- @node: scoreElementary_above
lemma scoreElementary_above (xi : ℕ → ℝ) (v k : ℕ) (h : v < k) :
    scoreElementary xi v k = 0 := by
  induction v generalizing k with
  | zero => cases k <;> simp_all [scoreElementary]
  | succ v ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [scoreElementary, ih (k + 1) (by omega), ih k (by omega)]
      ring

/-- Assume [the stated hb condition](hyp:hb) and [the stated hxi condition](hyp:hxi). [The bounded-score subset expansion has its deterministic binomial bound](goal). -/
-- @node: scoreElementary_abs_le
lemma scoreElementary_abs_le (xi : ℕ → ℝ) (beta : ℝ) (hb : 0 ≤ beta)
    (hxi : ∀ i, |xi i| ≤ beta) (v k : ℕ) :
    |scoreElementary xi v k| ≤ (Nat.choose v k : ℝ) * beta^k := by
  induction v generalizing k with
  | zero => cases k <;> simp [scoreElementary]
  | succ v ih =>
    cases k with
    | zero => simp [scoreElementary_zero]
    | succ k =>
      calc
        |scoreElementary xi (v + 1) (k + 1)| ≤
            |scoreElementary xi v (k + 1)| + |xi v| * |scoreElementary xi v k| := by
          simpa only [scoreElementary, abs_mul] using
            abs_add_le (scoreElementary xi v (k + 1)) (xi v * scoreElementary xi v k)
        _ ≤ (Nat.choose v (k + 1) : ℝ) * beta^(k + 1) +
            beta * ((Nat.choose v k : ℝ) * beta^k) :=
          add_le_add (ih (k + 1)) (mul_le_mul (hxi v) (ih k) (abs_nonneg _) hb)
        _ = (Nat.choose (v + 1) (k + 1) : ℝ) * beta^(k + 1) := by
          rw [Nat.choose_succ_succ]
          push_cast
          ring

/-- [The recursion is the exact coefficient expansion of a finite product of affine factors](goal). -/
-- @node: scoreElementary_affineProduct
lemma scoreElementary_affineProduct (xi : ℕ → ℝ) (v : ℕ) (t : ℝ) :
    (∏ i ∈ Finset.range v, (1 + t*xi i)) =
      ∑ k ∈ Finset.range (v + 1), scoreElementary xi v k * t^k := by
  induction v with
  | zero => simp [scoreElementary]
  | succ v ih =>
    let S := ∑ k ∈ Finset.range (v + 1), scoreElementary xi v k * t^k
    have hshift : (∑ k ∈ Finset.range (v + 1), scoreElementary xi v (k + 1) * t^(k + 1)) + 1 = S := by
      rw [Finset.sum_range_succ]
      rw [scoreElementary_above xi v (v + 1) (by omega)]
      simp only [zero_mul, add_zero]
      dsimp [S]
      rw [Finset.sum_range_succ']
      simp [scoreElementary_zero]
    have hscale : (∑ k ∈ Finset.range (v + 1), xi v * scoreElementary xi v k * t^(k + 1)) =
        xi v * t * S := by
      dsimp [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ]
      ring
    rw [Finset.prod_range_succ, ih]
    change S * (1 + t*xi v) = _
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [scoreElementary, add_mul, Finset.sum_add_distrib, pow_zero, mul_one]
    rw [hscale]
    have hshift' : (∑ k ∈ Finset.range (v + 1), scoreElementary xi v (k + 1) * t^(k + 1)) = S - 1 := by
      linarith
    rw [hshift']
    ring

/-- Assume [the stated hpos condition](hyp:hpos). [A coordinate shift factors each positive affine stage density into its base density times one plus the shift times its conditional score. [](](goal). -/
-- @node: stageMixtureDensity_shift_factor
lemma stageMixtureDensity_shift_factor (theta : Fin d → ℝ) (f : PairedSymbol d → ℝ)
    (j : Fin d) (t : ℝ) (hpos : 0 < stageMixtureDensity theta f) :
    stageMixtureDensity (Function.update theta j (theta j + t)) f =
      stageMixtureDensity theta f *
        (1 + t * (stageCoordinateSlope f j / stageMixtureDensity theta f)) := by
  rw [stageMixtureDensity_update]
  field_simp [ne_of_gt hpos]
  <;> ring

/-- Assume [the stated hpos condition](hyp:hpos). [The explicit stage-density product has the elementary-score coefficient expansion at every parameter with positive stage densities](goal). -/
-- @node: stageProduct_score_expansion
lemma stageProduct_score_expansion (theta : Fin d → ℝ)
    (f : ℕ → PairedSymbol d → ℝ) (j : Fin d) (v : ℕ) (t : ℝ)
    (hpos : ∀ i < v, 0 < stageMixtureDensity theta (f i)) :
    (∏ i ∈ Finset.range v,
      stageMixtureDensity (Function.update theta j (theta j + t)) (f i)) =
      (∏ i ∈ Finset.range v, stageMixtureDensity theta (f i)) *
        ∑ k ∈ Finset.range (v + 1),
          scoreElementary (fun i => stageCoordinateSlope (f i) j /
            stageMixtureDensity theta (f i)) v k * t^k := by
  calc
    _ = ∏ i ∈ Finset.range v, stageMixtureDensity theta (f i) *
        (1 + t * (stageCoordinateSlope (f i) j / stageMixtureDensity theta (f i))) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact stageMixtureDensity_shift_factor theta (f i) j t (hpos i (Finset.mem_range.mp hi))
    _ = _ := by rw [Finset.prod_mul_distrib, scoreElementary_affineProduct]

/-- [Differentiation at zero extracts a finite polynomial coefficient with the factorial required by the density derivative bound](goal). -/
-- @node: iteratedDeriv_score_polynomial_zero
lemma iteratedDeriv_score_polynomial_zero (xi : ℕ → ℝ) (v k : ℕ) :
    iteratedDeriv k (fun t : ℝ =>
      ∑ q ∈ Finset.range (v + 1), scoreElementary xi v q * t^q) 0 =
      (k.factorial : ℝ) * scoreElementary xi v k := by
  rw [iteratedDeriv_fun_sum]
  · simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
    by_cases hk : k < v + 1
    · simp [hk, mul_comm]
    · have hzero := scoreElementary_above xi v k (by omega)
      simp [hk, hzero]
  · intro q _
    fun_prop

/-- Assume [the stated hpos condition](hyp:hpos). [Repeated coordinate differentiation of the explicit affine product is exactly factorial times the base product times the elementary conditional score](goal). -/
-- @node: stageProduct_iteratedDeriv_score
lemma stageProduct_iteratedDeriv_score (theta : Fin d → ℝ)
    (f : ℕ → PairedSymbol d → ℝ) (j : Fin d) (v k : ℕ)
    (hpos : ∀ i < v, 0 < stageMixtureDensity theta (f i)) :
    iteratedDeriv k (fun t : ℝ => ∏ i ∈ Finset.range v,
      stageMixtureDensity (Function.update theta j (theta j + t)) (f i)) 0 =
      (k.factorial : ℝ) * (∏ i ∈ Finset.range v, stageMixtureDensity theta (f i)) *
        scoreElementary (fun i => stageCoordinateSlope (f i) j /
          stageMixtureDensity theta (f i)) v k := by
  have hfun := funext (fun t => stageProduct_score_expansion theta f j v t hpos)
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_score_polynomial_zero]
  ring

/-- Assume [the stated hpos condition](hyp:hpos). [The product-score identity in the original coordinate, including boundary parameters where the polynomial defines the derivative](goal). -/
-- @node: stageProduct_coordinateDerivative_score
lemma stageProduct_coordinateDerivative_score (theta : Fin d → ℝ)
    (f : ℕ → PairedSymbol d → ℝ) (j : Fin d) (v k : ℕ)
    (hpos : ∀ i < v, 0 < stageMixtureDensity theta (f i)) :
    iteratedDeriv k (fun x : ℝ => ∏ i ∈ Finset.range v,
      stageMixtureDensity (Function.update theta j x) (f i)) (theta j) =
      (k.factorial : ℝ) * (∏ i ∈ Finset.range v, stageMixtureDensity theta (f i)) *
        scoreElementary (fun i => stageCoordinateSlope (f i) j /
          stageMixtureDensity theta (f i)) v k := by
  have h := stageProduct_iteratedDeriv_score theta f j v k hpos
  have hcomm : (fun t : ℝ => ∏ i ∈ Finset.range v,
      stageMixtureDensity (Function.update theta j (theta j + t)) (f i)) =
      (fun t : ℝ => ∏ i ∈ Finset.range v,
        stageMixtureDensity (Function.update theta j (t + theta j)) (f i)) := by
    funext t
    rw [add_comm (theta j)]
  rw [hcomm] at h
  rw [iteratedDeriv_comp_add_const (f := fun x : ℝ => ∏ i ∈ Finset.range v,
    stageMixtureDensity (Function.update theta j x) (f i))] at h
  simpa only [zero_add] using h

/-- [Elementary scores depend measurably only on the preceding increments](goal) when [all increments before the cutoff are measurable](hyp:hxi). -/
-- @node: measurable_scoreElementary
@[fun_prop] lemma measurable_scoreElementary {Ω : Type*} [MeasurableSpace Ω]
    (xi : ℕ → Ω → ℝ) (v k : ℕ) (hxi : ∀ i < v, Measurable (xi i)) :
    Measurable (fun w => scoreElementary (fun i => xi i w) v k) := by
  induction v generalizing k with
  | zero => cases k <;> exact measurable_const
  | succ v ih =>
    cases k with
    | zero => exact measurable_const
    | succ k =>
      change Measurable (fun w => scoreElementary (fun i => xi i w) v (k + 1) +
        xi v w * scoreElementary (fun i => xi i w) v k)
      first
      | fun_prop
      | exact (ih (k + 1) (fun i hi => hxi i (by omega))).add
          ((hxi v (by omega)).mul (ih k (fun i hi => hxi i (by omega))))

/-- Assume [measurability of xi](hyp:hxi), [the stated hb condition](hyp:hb), and [the stated hbound condition](hyp:hbound). [Bounded score products have finite moments of every natural order](goal). -/
-- @node: integrable_scoreElementary_pow
lemma integrable_scoreElementary_pow {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsFiniteMeasure mu] (xi : ℕ → Ω → ℝ)
    (hxi : ∀ i, Measurable (xi i)) (beta : ℝ) (hb : 0 ≤ beta)
    (hbound : ∀ i w, |xi i w| ≤ beta) (v k q : ℕ) :
    Integrable (fun w => (scoreElementary (fun i => xi i w) v k)^q) mu := by
  apply Integrable.of_bound
    ((measurable_scoreElementary xi v k (fun i _ => hxi i)).pow_const q).aestronglyMeasurable
    (((Nat.choose v k : ℝ) * beta^k)^q)
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (scoreElementary_abs_le _ beta hb
    (fun i => hbound i w) v k) q

/-- Assume [the stated hm condition](hyp:hm), [measurability of f](hyp:hf), [the stated hg condition](hyp:hg), [the stated hfg condition](hyp:hfg), and [the stated hmean condition](hyp:hmean). [Conditional mean zero kills a bounded, past-measurable cross term](goal). -/
-- @node: score_cross_integral_zero
lemma score_cross_integral_zero {Ω : Type*} {m0 : MeasurableSpace Ω}
    (mu : Measure Ω) [IsProbabilityMeasure mu] (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (f g : Ω → ℝ) (hf : Measurable[m] f) (hg : Integrable g mu)
    (hfg : Integrable (f * g) mu) (hmean : mu[g | m] =ᵐ[mu] 0) :
    (∫ w, f w * g w ∂mu) = 0 := by
  rw [← integral_condExp hm]
  have hpull := condExp_mul_of_stronglyMeasurable_left hf.stronglyMeasurable hfg hg
  have hzero : mu[f * g | m] =ᵐ[mu] 0 := by
    filter_upwards [hpull, hmean] with w hw hw0
    simp only [Pi.mul_apply, Pi.zero_apply] at hw hw0 ⊢
    rw [hw, hw0, mul_zero]
  exact (integral_congr_ae hzero).trans (by simp)

/-- Assume [measurability of xi](hyp:hxi), [the stated hb condition](hyp:hb), [the stated hbound condition](hyp:hbound), and [the stated hcross condition](hyp:hcross). [Cross-term cancellation and bounded increments give the score second-moment recursion](goal). -/
-- @node: scoreElementary_secondMoment_step
lemma scoreElementary_secondMoment_step {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (xi : ℕ → Ω → ℝ)
    (hxi : ∀ i, Measurable (xi i)) (beta : ℝ) (hb : 0 ≤ beta)
    (hbound : ∀ i w, |xi i w| ≤ beta) (v k : ℕ)
    (hcross : (∫ w, scoreElementary (fun i => xi i w) v (k + 1) *
      (xi v w * scoreElementary (fun i => xi i w) v k) ∂mu) = 0) :
    (∫ w, (scoreElementary (fun i => xi i w) (v + 1) (k + 1))^2 ∂mu) ≤
      (∫ w, (scoreElementary (fun i => xi i w) v (k + 1))^2 ∂mu) +
      beta^2 * (∫ w, (scoreElementary (fun i => xi i w) v k)^2 ∂mu) := by
  let A := fun w => scoreElementary (fun i => xi i w) v (k + 1)
  let B := fun w => xi v w * scoreElementary (fun i => xi i w) v k
  have hA : Measurable A := measurable_scoreElementary xi _ _ (fun i _ => hxi i)
  have hB : Measurable B := (hxi v).mul
    (measurable_scoreElementary xi _ _ (fun i _ => hxi i))
  have hAb : ∀ w, |A w| ≤ (Nat.choose v (k + 1) : ℝ) * beta^(k + 1) :=
    fun w => scoreElementary_abs_le _ beta hb (fun i => hbound i w) _ _
  have hBb : ∀ w, |B w| ≤ beta * ((Nat.choose v k : ℝ) * beta^k) := by
    intro w
    rw [abs_mul]
    exact mul_le_mul (hbound v w)
      (scoreElementary_abs_le _ beta hb (fun i => hbound i w) _ _) (abs_nonneg _) hb
  have hB2 : Integrable (fun w => B w^2) mu := by
    apply Integrable.of_bound (hB.pow_const 2).aestronglyMeasurable
      ((beta * ((Nat.choose v k : ℝ) * beta^k))^2)
    filter_upwards [] with w
    simpa only [Real.norm_eq_abs, abs_pow] using
      pow_le_pow_left₀ (abs_nonneg (B w)) (hBb w) 2
  have hAB : Integrable (fun w => A w * B w) mu := by
    apply Integrable.of_bound (hA.mul hB).aestronglyMeasurable
      (((Nat.choose v (k + 1) : ℝ) * beta^(k + 1)) *
        (beta * ((Nat.choose v k : ℝ) * beta^k)))
    filter_upwards [] with w
    simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    exact mul_le_mul (hAb w) (hBb w) (abs_nonneg _) (by positivity)
  have hA2 : Integrable (fun w => A w^2) mu :=
    integrable_scoreElementary_pow mu xi hxi beta hb hbound v (k + 1) 2
  have hE2 := integrable_scoreElementary_pow mu xi hxi beta hb hbound v k 2
  have hexp : (fun w => (scoreElementary (fun i => xi i w) (v + 1) (k + 1))^2) =
      (fun w => A w^2 + 2 * (A w * B w) + B w^2) := by
    funext w
    dsimp [A, B]
    rw [scoreElementary]
    ring
  rw [hexp]
  integral_linearity
  change _ + 2 * (∫ w, A w * B w ∂mu) + _ ≤ _
  have hcross' : (∫ w, A w * B w ∂mu) = 0 := hcross
  rw [hcross']
  simp only [mul_zero, add_zero]
  apply add_le_add le_rfl
  rw [← integral_const_mul]
  apply integral_mono hB2 (hE2.const_mul (beta^2))
  intro w
  dsimp [B]
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hh := pow_le_pow_left₀ (abs_nonneg (xi v w)) (hbound v w) 2
  simpa only [sq_abs] using hh

/-- Assume [measurability of xi](hyp:hxi), [the stated hb condition](hyp:hb), [the stated hbound condition](hyp:hbound), and [the stated hcross condition](hyp:hcross). [The martingale score recursion yields the binomial second-moment bound](goal). -/
-- @node: scoreElementary_secondMoment_le
lemma scoreElementary_secondMoment_le {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (xi : ℕ → Ω → ℝ)
    (hxi : ∀ i, Measurable (xi i)) (beta : ℝ) (hb : 0 ≤ beta)
    (hbound : ∀ i w, |xi i w| ≤ beta)
    (hcross : ∀ v k, (∫ w, scoreElementary (fun i => xi i w) v (k + 1) *
      (xi v w * scoreElementary (fun i => xi i w) v k) ∂mu) = 0)
    (v k : ℕ) :
    (∫ w, (scoreElementary (fun i => xi i w) v k)^2 ∂mu) ≤
      (Nat.choose v k : ℝ) * beta^(2*k) := by
  induction v generalizing k with
  | zero => cases k <;> simp [scoreElementary]
  | succ v ih =>
    cases k with
    | zero => simp [scoreElementary_zero]
    | succ k =>
      calc
        _ ≤ (∫ w, (scoreElementary (fun i => xi i w) v (k + 1))^2 ∂mu) +
            beta^2 * (∫ w, (scoreElementary (fun i => xi i w) v k)^2 ∂mu) :=
          scoreElementary_secondMoment_step mu xi hxi beta hb hbound v k (hcross v k)
        _ ≤ (Nat.choose v (k + 1) : ℝ) * beta^(2*(k + 1)) +
            beta^2 * ((Nat.choose v k : ℝ) * beta^(2*k)) :=
          add_le_add (ih (k + 1)) (mul_le_mul_of_nonneg_left (ih k) (sq_nonneg beta))
        _ = (Nat.choose (v + 1) (k + 1) : ℝ) * beta^(2*(k + 1)) := by
          rw [Nat.choose_succ_succ]
          push_cast
          rw [show 2*(k + 1) = 2*k+2 by omega, pow_add]
          ring


/-- [An adapted score prefix is measurable with respect to its own past](goal) when [the filtration is monotone](hyp:hF) and [each increment is adapted](hyp:hadapt). -/
-- @node: measurable_scoreElementary_past
@[fun_prop] lemma measurable_scoreElementary_past {Ω : Type*}
    (F : ℕ → MeasurableSpace Ω) (hF : Monotone F) (xi : ℕ → Ω → ℝ)
    (hadapt : ∀ i, Measurable[F (i + 1)] (xi i)) (v k : ℕ) :
    Measurable[F v] (fun w => scoreElementary (fun i => xi i w) v k) := by
  let : MeasurableSpace Ω := F v
  apply measurable_scoreElementary xi v k
  intro i hi
  exact (hadapt i).mono (hF (by omega)) le_rfl

/-- Assume [the stated f condition](hyp:hF), [the stated hle condition](hyp:hle), [measurability of adapt](hyp:hadapt), [the stated hb condition](hyp:hb), [the stated hbound condition](hyp:hbound), and [the stated hmean condition](hyp:hmean). [Bounded adapted martingale increments cancel every elementary-score cross term](goal). -/
-- @node: scoreElementary_martingale_cross
lemma scoreElementary_martingale_cross {Ω : Type*} [m0 : MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (F : ℕ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ v, F v ≤ m0)
    (xi : ℕ → Ω → ℝ) (hadapt : ∀ i, Measurable[F (i + 1)] (xi i))
    (beta : ℝ) (hb : 0 ≤ beta) (hbound : ∀ i w, |xi i w| ≤ beta)
    (hmean : ∀ v, mu[xi v | F v] =ᵐ[mu] 0) (v k : ℕ) :
    (∫ w, scoreElementary (fun i => xi i w) v (k + 1) *
      (xi v w * scoreElementary (fun i => xi i w) v k) ∂mu) = 0 := by
  have hxi : ∀ i, Measurable (xi i) := fun i => (hadapt i).mono (hle _) le_rfl
  let f := fun w => scoreElementary (fun i => xi i w) v (k + 1) *
    scoreElementary (fun i => xi i w) v k
  have hf : Measurable[F v] f := by fun_prop
  have hg : Integrable (xi v) mu := by
    apply Integrable.of_bound (hxi v).aestronglyMeasurable beta
    filter_upwards [] with w
    exact (Real.norm_eq_abs _).symm ▸ hbound v w
  have hfg : Integrable (f * xi v) mu := by
    apply Integrable.of_bound (((hf.mono (hle v) le_rfl).mul (hxi v)).aestronglyMeasurable)
      (((Nat.choose v (k + 1) : ℝ) * beta^(k + 1)) *
        ((Nat.choose v k : ℝ) * beta^k) * beta)
    filter_upwards [] with w
    simp only [Pi.mul_apply, Real.norm_eq_abs, f, abs_mul]
    exact mul_le_mul
      (mul_le_mul (scoreElementary_abs_le _ beta hb (fun i => hbound i w) v (k + 1))
        (scoreElementary_abs_le _ beta hb (fun i => hbound i w) v k)
        (abs_nonneg _) (by positivity))
      (hbound v w) (abs_nonneg _) (by positivity)
  have hz := score_cross_integral_zero mu (F v) (hle v) f (xi v) hf hg hfg (hmean v)
  convert hz using 1
  congr 1
  funext w
  dsimp [f]
  ring

/-- Assume [the stated f condition](hyp:hF), [the stated hle condition](hyp:hle), [measurability of adapt](hyp:hadapt), [the stated hb condition](hyp:hb), [the stated hbound condition](hyp:hbound), and [the stated hmean condition](hyp:hmean). [The binomial bound holds for adaptive martingale scores, without independence](goal). -/
-- @node: scoreElementary_martingale_secondMoment
lemma scoreElementary_martingale_secondMoment {Ω : Type*} [m0 : MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (F : ℕ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ v, F v ≤ m0)
    (xi : ℕ → Ω → ℝ) (hadapt : ∀ i, Measurable[F (i + 1)] (xi i))
    (beta : ℝ) (hb : 0 ≤ beta) (hbound : ∀ i w, |xi i w| ≤ beta)
    (hmean : ∀ v, mu[xi v | F v] =ᵐ[mu] 0) (v k : ℕ) :
    (∫ w, (scoreElementary (fun i => xi i w) v k)^2 ∂mu) ≤
      (Nat.choose v k : ℝ) * beta^(2*k) := by
  apply scoreElementary_secondMoment_le mu xi
    (fun i => (hadapt i).mono (hle _) le_rfl) beta hb hbound
  exact scoreElementary_martingale_cross mu F hF hle xi hadapt beta hb hbound hmean

/-- Assume [the stated f condition](hyp:hF), [the stated hle condition](hyp:hle), [measurability of adapt](hyp:hadapt), [the stated hb condition](hyp:hb), [the stated hbound condition](hyp:hbound), and [the stated hmean condition](hyp:hmean). [Cauchy–Schwarz converts the adaptive binomial second moment into the needed L1 bound](goal). -/
-- @node: scoreElementary_martingale_firstMoment
lemma scoreElementary_martingale_firstMoment {Ω : Type*} [m0 : MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (F : ℕ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ v, F v ≤ m0)
    (xi : ℕ → Ω → ℝ) (hadapt : ∀ i, Measurable[F (i + 1)] (xi i))
    (beta : ℝ) (hb : 0 ≤ beta) (hbound : ∀ i w, |xi i w| ≤ beta)
    (hmean : ∀ v, mu[xi v | F v] =ᵐ[mu] 0) (v k : ℕ) :
    (∫ w, |scoreElementary (fun i => xi i w) v k| ∂mu) ≤
      Real.sqrt (Nat.choose v k) * beta^k := by
  let E := fun w => scoreElementary (fun i => xi i w) v k
  let c := ∫ w, |E w| ∂mu
  have hxi : ∀ i, Measurable (xi i) := fun i => (hadapt i).mono (hle _) le_rfl
  have hi : Integrable E mu := by
    simpa only [pow_one] using integrable_scoreElementary_pow mu xi hxi beta hb hbound v k 1
  have hi2 : Integrable (fun w => |E w|^2) mu := by
    simpa only [sq_abs] using integrable_scoreElementary_pow mu xi hxi beta hb hbound v k 2
  have hnonneg : 0 ≤ ∫ w, (|E w| - c)^2 ∂mu :=
    integral_nonneg (fun w => sq_nonneg _)
  have hexp : (fun w => (|E w| - c)^2) =
      (fun w => |E w|^2 - 2*c*|E w| + c^2) := by funext w; ring
  rw [hexp] at hnonneg
  have hiabs := hi.abs
  have hilinear : Integrable (fun w => 2*c*|E w|) mu := hiabs.const_mul (2*c)
  have hlin : (∫ w, |E w|^2 - 2*c*|E w| + c^2 ∂mu) =
      (∫ w, |E w|^2 ∂mu) - 2*c*(∫ w, |E w| ∂mu) + (∫ _ : Ω, c^2 ∂mu) := by
    integral_linearity
  rw [hlin] at hnonneg
  simp only [integral_const, probReal_univ, one_smul] at hnonneg
  have hsq : c^2 ≤ ∫ w, (E w)^2 ∂mu := by
    simp only [sq_abs] at hnonneg
    change 0 ≤ (∫ w, E w^2 ∂mu) - 2*c*c + c^2 at hnonneg
    nlinarith
  have hsecond := scoreElementary_martingale_secondMoment mu F hF hle xi hadapt
    beta hb hbound hmean v k
  have hcs := Real.le_sqrt_of_sq_le (hsq.trans hsecond)
  have hpower : beta^(2*k) = (beta^k)^2 := by rw [← pow_mul]; congr 1; omega
  rw [hpower, Real.sqrt_mul (by positivity), Real.sqrt_sq (pow_nonneg hb k)] at hcs
  exact hcs

/-- Assume [measurability of p](hyp:hp), [the stated hp0 condition](hyp:hp0), [the stated hc condition](hyp:hc), and [the stated d condition](hyp:hD). [The density-times-score identity changes the derivative L1 integral into a factorial times the score first moment under the parameter-specific law](goal). -/
-- @node: integral_abs_density_score
lemma integral_abs_density_score {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (p E D : Ω → ℝ) (hp : Measurable p)
    (hp0 : ∀ w, 0 ≤ p w) (c : ℝ) (hc : 0 ≤ c)
    (hD : ∀ w, D w = c * p w * E w) :
    (∫ w, |D w| ∂mu) =
      c * (∫ w, |E w| ∂mu.withDensity (fun w => ENNReal.ofReal (p w))) := by
  rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (Filter.Eventually.of_forall (fun w => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hp0 _), smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  rw [hD w, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg (hp0 w)]
  ring

/-- Assume [the stated hpos condition](hyp:hpos), [measurability of p](hyp:hp), [the stated probability-measure property](hyp:hprob), [the stated f condition](hyp:hF), [the stated hle condition](hyp:hle), [measurability of adapt](hyp:hadapt), [the stated hb condition](hyp:hb), [the stated hbound condition](hyp:hbound), and [the stated hmean condition](hyp:hmean). [The explicit affine stage product satisfies the sharp derivative L1 bound whenever its conditional scores are bounded martingale increments under its own density-weighted transcript law. This is the change-of-measure assembly used after identifying the stage product with the protocol density](goal). -/
-- @node: stageProduct_coordinateDerivative_l1
lemma stageProduct_coordinateDerivative_l1 {Ω : Type*} [m0 : MeasurableSpace Ω]
    (mu : Measure Ω) (theta : Fin d → ℝ)
    (f : ℕ → Ω → PairedSymbol d → ℝ) (j : Fin d) (v k : ℕ)
    (hpos : ∀ i < v, ∀ w, 0 < stageMixtureDensity theta (f i w))
    (hp : Measurable (fun w => ∏ i ∈ Finset.range v,
      stageMixtureDensity theta (f i w)))
    (hprob : IsProbabilityMeasure (mu.withDensity (fun w => ENNReal.ofReal
      (∏ i ∈ Finset.range v, stageMixtureDensity theta (f i w)))))
    (F : ℕ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ i, F i ≤ m0)
    (hadapt : ∀ i, Measurable[F (i + 1)] (fun w =>
      stageCoordinateSlope (f i w) j / stageMixtureDensity theta (f i w)))
    (beta : ℝ) (hb : 0 ≤ beta)
    (hbound : ∀ i w, |stageCoordinateSlope (f i w) j /
      stageMixtureDensity theta (f i w)| ≤ beta)
    (hmean : ∀ i, condExp (F i) (mu.withDensity (fun w => ENNReal.ofReal
      (∏ q ∈ Finset.range v, stageMixtureDensity theta (f q w))))
      (fun w => stageCoordinateSlope (f i w) j /
          stageMixtureDensity theta (f i w)) =ᵐ[mu.withDensity (fun w => ENNReal.ofReal
          (∏ q ∈ Finset.range v, stageMixtureDensity theta (f q w)))] 0) :
    (∫ w, |iteratedDeriv k (fun x : ℝ => ∏ i ∈ Finset.range v,
      stageMixtureDensity (Function.update theta j x) (f i w)) (theta j)| ∂mu) ≤
      (k.factorial : ℝ) * Real.sqrt (Nat.choose v k) * beta^k := by
  let p := fun w => ∏ i ∈ Finset.range v, stageMixtureDensity theta (f i w)
  let xi := fun i w => stageCoordinateSlope (f i w) j / stageMixtureDensity theta (f i w)
  let nu := mu.withDensity (fun w => ENNReal.ofReal (p w))
  let : IsProbabilityMeasure nu := hprob
  have hp0 : ∀ w, 0 ≤ p w := by
    intro w
    exact Finset.prod_nonneg fun i hi => le_of_lt (hpos i (Finset.mem_range.mp hi) w)
  rw [integral_abs_density_score mu p
    (fun w => scoreElementary (fun i => xi i w) v k) _ hp hp0
    (k.factorial : ℝ) (by positivity)
    (fun w => stageProduct_coordinateDerivative_score theta (fun i => f i w) j v k
      (fun i hi => hpos i hi w))]
  have hfirst := scoreElementary_martingale_firstMoment nu F hF hle xi hadapt
    beta hb hbound hmean v k
  calc
    _ ≤ (k.factorial : ℝ) * (Real.sqrt (Nat.choose v k) * beta^k) :=
      mul_le_mul_of_nonneg_left hfirst (by positivity)
    _ = _ := by ring

/-- Assume [the stated hk condition](hyp:hk). [Every derivative above the degree bound of a finite coefficient polynomial vanishes](goal). -/
-- @node: iteratedDeriv_fin_polynomial_eq_zero
lemma iteratedDeriv_fin_polynomial_eq_zero {n k : ℕ} (coeff : Fin (n + 1) → ℝ)
    (hk : n < k) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ => ∑ q, coeff q * y ^ q.val) x = 0 := by
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_eq_zero
    intro q hq
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
    have hqk : q.val < k := lt_of_le_of_lt (Nat.le_of_lt_succ q.isLt) hk
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hqk]
    simp
  · intro q hq
    fun_prop

/-- Assume [the function hpoly](hyp:hpoly) and [the stated hk condition](hyp:hk). [Coordinate polynomiality forces transcript-density derivatives above the sample size to vanish](goal). -/
-- @node: densityDerivative_eq_zero_of_coordinate_polynomial
lemma densityDerivative_eq_zero_of_coordinate_polynomial
    {Q : LocalProtocol n (ObsRecord d)}
    (p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ)
    (hpoly : ∀ theta r z j, ∃ coeff : Fin (n + 1) → ℝ,
      ∀ x : ℝ, p (Function.update theta j x, r, z) = ∑ q, coeff q * x ^ q.val)
    (theta : Fin d → ℝ) (r : Q.Seed) (z : ProtocolTranscript Q)
    (j : Fin d) (k : ℕ) (hk : n < k) :
    densityDerivative p theta r z j k = 0 := by
  obtain ⟨coeff, hcoeff⟩ := hpoly theta r z j
  unfold densityDerivative
  have hfun : (fun x => p (Function.update theta j x, r, z)) =
      (fun x : ℝ => ∑ q, coeff q * x ^ q.val) := funext hcoeff
  rw [hfun]
  exact iteratedDeriv_fin_polynomial_eq_zero coeff hk (theta j)

end CausalSmith.Stat.LdpOptvalueUniformFrontier
