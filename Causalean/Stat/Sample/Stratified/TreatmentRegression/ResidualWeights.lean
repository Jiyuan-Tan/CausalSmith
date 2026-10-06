module
public import Causalean.Stat.Sample.OccupancyWeightedMean.MomentBounds
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Basic

/-! # Arbitrary finite-design residual coefficients

This module isolates the square-integrability and variance calculation for a
sum of arm-cell residuals with arbitrary coefficients depending on the entire
observed categorical design. It imposes no bounded-outcome condition. The
regression application takes each coefficient to be the residualized treatment
weight times the guarded inverse Gram. No categorical conditioning or Gram
tail theorem is needed in this lower dependency layer.
-/

@[expose] public section

noncomputable section

namespace Causalean.Stat.Sample.Stratified.TreatmentRegression

open MeasureTheory Set Causalean.Stat
open scoped BigOperators

variable {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- [The design-weighted residual sum](goal) of [a sample z of n observations](hyp:n,z) with
[cell label X](hyp:X), [treatment A](hyp:A) and [outcome Y](hyp:Y) adds, over observations, the
residual of the outcome from [its arm-and-cell centre](hyp:center) times
[a coefficient that may depend on the whole observed design](hyp:b). -/
def designWeightedResidual {n : ℕ} (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (b : (Fin n → κ × Bool) → Fin n → ℝ)
    (z : Fin n → Ω) : ℝ :=
  ∑ i, b (sampleDesign X A z) i * (Y (z i) - center (A (z i)) (X (z i)))

/-- At [every observation ω](hyp:ω), [the residual of the outcome Y from the centre of its own arm
and cell equals the sum over all arm-cell pairs of the residuals supported on those arm-cell
events](goal), for any [cell label X](hyp:X), [treatment A](hyp:A), [outcome Y](hyp:Y) and
[centres](hyp:center). -/
private lemma residual_eq_sum_supported
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ) (center : Bool → κ → ℝ)
    (ω : Ω) :
    Y ω - center (A ω) (X ω) =
      ∑ c : Bool × κ, supportedArmGroupResidual X A Y center c.1 c.2 ω := by
  classical
  cases ha : A ω <;>
    simp [Fintype.sum_prod_type, supportedArmGroupResidual, armGroupEvent,
      armGroupResidual, Set.indicator_apply, ha]

/-- If [the cell label X](hyp:X,hX) and [the treatment A](hyp:A,hA) are measurable and
[a function f of the sample lies in Lp under the n-fold product of μ](hyp:n,p,μ,f,hf), then for
[any real function v of the observed design](hyp:v), [v at the observed design times f is again
in Lp under the same law](goal). -/
private lemma memLp_mul_design {n : ℕ} {p : ENNReal} (μ : Measure Ω)
    (X : Ω → κ) (A : Ω → Bool) (hX : Measurable X) (hA : Measurable A)
    (f : (Fin n → Ω) → ℝ) (hf : MemLp f p (Measure.pi (fun _ : Fin n => μ)))
    (v : (Fin n → κ × Bool) → ℝ) :
    MemLp (fun z => v (sampleDesign X A z) * f z) p
      (Measure.pi (fun _ : Fin n => μ)) := by
  classical
  let C : ℝ := ∑ d : Fin n → κ × Bool, |v d|
  have hv (d : Fin n → κ × Bool) : |v d| ≤ C :=
    Finset.single_le_sum (fun d' _ => abs_nonneg (v d')) (Finset.mem_univ d)
  apply hf.of_le_mul (c := C)
  · exact (((Measurable.of_discrete : Measurable v).comp
      (measurable_sampleDesign X A hX hA)).aestronglyMeasurable.mul
        hf.aestronglyMeasurable)
  · filter_upwards [] with z
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hv _) (abs_nonneg _)

/-- Under [a probability law μ of one observation](hyp:μ), if [the cell label X](hyp:X,hX),
[the treatment A](hyp:A,hA) and [the outcome Y](hyp:Y,hY) are measurable and
[each arm-cell-supported residual from the centres is square integrable](hyp:center,hmem), then
for [every sample size n](hyp:n) and [every design-dependent coefficient](hyp:b)
[the design-weighted residual sum is square integrable under the iid product law](goal).

Expand the coordinate residual into its finite sum of supported arm-cell
residuals. Each supported residual pulls back along measurePreserving_eval;
the coefficients are bounded by the finite sum of their absolute values over
designs. Use MemLp.of_le_mul and memLp_finsetSum.
-/
lemma designWeightedResidual_memLp (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ) (center : Bool → κ → ℝ)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y)
    (hmem : ∀ a k, MemLp (supportedArmGroupResidual X A Y center a k) 2 μ)
    (b : (Fin n → κ × Bool) → Fin n → ℝ) :
    MemLp (designWeightedResidual X A Y center b) 2
      (Measure.pi (fun _ : Fin n => μ)) := by
  classical
  have hr : MemLp (fun ω => Y ω - center (A ω) (X ω)) 2 μ := by
    have hs := memLp_finsetSum Finset.univ
      (fun (c : Bool × κ) _ => hmem c.1 c.2)
    simpa only [← residual_eq_sum_supported X A Y center] using hs
  unfold designWeightedResidual
  exact memLp_finsetSum Finset.univ fun i _ =>
    memLp_mul_design μ X A hX hA _
      (hr.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i))
      (fun d => b d i)

/-- Under [a probability law μ of one observation](hyp:μ), suppose [the cell label X](hyp:X,hX),
[the treatment A](hyp:A,hA) and [the outcome Y](hyp:Y,hY) are measurable, and on each arm-cell
event the residual from [its centre](hyp:center) [is square integrable](hyp:hmem),
[integrates to zero](hyp:hcenter), and [has integral of its square at most the event's mass times
M²](hyp:M,hsq). Then for [any design-dependent coefficients b](hyp:b) and [any nonnegative weight
W on designs of n cell-treatment pairs](hyp:n,W,hW), [the expectation under the iid product law of
W at the observed design times the squared design-weighted residual sum is at most M² times the
expectation of W times the sum of the squared coefficients](goal).

Centered arm-cell residuals with conditional second moments at most M²
give a weighted second-moment bound by M² times the sum of squared design
coefficients, for every nonnegative finite-design weight.

Expand into coordinates and supported arm-cell residuals. Invoke
integral_designWeight_residual_cross_coordinates_eq_zero with the weight
W d * b d i * b d j off the coordinate diagonal. Different arm-cell
supports at the same coordinate have zero product pointwise. Apply
integral_designWeight_residual_sq_le_indicator with weight W d * (b d i)^2
to the surviving terms; sum the cell indicators to one. The preceding L2
lemma, also with coordinate-isolating coefficients, supplies integrability
for the finite integral expansions. No homogeneity or overlap is used here.
-/
theorem integral_designWeightedResidual_sq_le (n : ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (M : ℝ)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y)
    (hmem : ∀ a k, MemLp (supportedArmGroupResidual X A Y center a k) 2 μ)
    (hcenter : ∀ a k,
      ∫ ω in armGroupEvent X A a k, armGroupResidual Y center a k ω ∂μ = 0)
    (hsq : ∀ a k,
      ∫ ω in armGroupEvent X A a k, (armGroupResidual Y center a k ω) ^ 2 ∂μ ≤
        (μ (armGroupEvent X A a k)).toReal * M ^ 2)
    (b : (Fin n → κ × Bool) → Fin n → ℝ)
    (W : (Fin n → κ × Bool) → ℝ) (hW : ∀ d, 0 ≤ W d) :
    (∫ z : Fin n → Ω, W (sampleDesign X A z) *
      designWeightedResidual X A Y center b z ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) ≤
      M ^ 2 * ∫ z : Fin n → Ω, W (sampleDesign X A z) *
        (∑ i, b (sampleDesign X A z) i ^ 2)
        ∂Measure.pi (fun _ : Fin n => μ) := by
  classical
  let ν := Measure.pi (fun _ : Fin n => μ)
  let T := Fin n × (Bool × κ)
  let r : T → (Fin n → Ω) → ℝ := fun t z =>
    supportedArmGroupResidual X A Y center t.2.1 t.2.2 (z t.1)
  let F : T → T → (Fin n → Ω) → ℝ := fun t u z =>
    W (sampleDesign X A z) * b (sampleDesign X A z) t.1 *
      b (sampleDesign X A z) u.1 * r t z * r u z
  let G : T → (Fin n → Ω) → ℝ := fun t z =>
    W (sampleDesign X A z) * b (sampleDesign X A z) t.1 ^ 2 *
      (armGroupEvent X A t.2.1 t.2.2).indicator (fun _ => (1 : ℝ)) (z t.1)
  have hr (t : T) : MemLp (r t) 2 ν :=
    (hmem t.2.1 t.2.2).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => μ) t.1)
  have hF (t u : T) : Integrable (F t u) ν := by
    exact (memLp_mul_design μ X A hX hA (r t) (hr t)
      (fun d => W d * b d t.1 * b d u.1)).integrable_mul (hr u)
  have hG (t : T) : Integrable (G t) ν := by
    have hc : MemLp ((armGroupEvent X A t.2.1 t.2.2).indicator
        (fun _ : Ω => (1 : ℝ))) 2 μ :=
      (memLp_const (1 : ℝ)).indicator
        (measurableSet_armGroupEvent X A hX hA t.2.1 t.2.2)
    have hi := hc.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => μ) t.1)
    exact (memLp_mul_design μ X A hX hA _ hi
      (fun d => W d * b d t.1 ^ 2)).integrable (by norm_num)
  have hexpand (z : Fin n → Ω) :
      W (sampleDesign X A z) * designWeightedResidual X A Y center b z ^ 2 =
        ∑ t : T, ∑ u : T, F t u z := by
    have he : designWeightedResidual X A Y center b z =
        ∑ t : T, b (sampleDesign X A z) t.1 * r t z := by
      simp only [designWeightedResidual, T, Fintype.sum_prod_type, r,
        ← Finset.mul_sum, ← residual_eq_sum_supported X A Y center]
    rw [he, pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    dsimp [F]
    ring
  have hoff (t u : T) (htu : t ≠ u) : ∫ z, F t u z ∂ν = 0 := by
    by_cases hi : t.1 = u.1
    · have hc : t.2 ≠ u.2 := fun hc => htu (Prod.ext hi hc)
      have hz (z : Fin n → Ω) : F t u z = 0 := by
        have hh := supportedArmGroupResidual_mul_eq_zero_of_ne
          X A Y center t.2.1 u.2.1 t.2.2 u.2.2 hc (z t.1)
        dsimp [F, r]
        rw [← hi, mul_assoc, hh, mul_zero]
      simp only [hz, integral_zero]
    · exact integral_designWeight_residual_cross_coordinates_eq_zero μ X A Y center
        hX hA hY hmem hcenter (fun d => W d * b d t.1 * b d u.1)
        t.1 u.1 hi t.2.1 u.2.1 t.2.2 u.2.2
  have hdiag (t : T) : (∫ z, F t t z ∂ν) ≤ M ^ 2 * ∫ z, G t z ∂ν := by
    have hh := integral_designWeight_residual_sq_le_indicator μ X A Y center M
      hX hA hY hmem hsq (fun d => W d * b d t.1 ^ 2)
      (fun d => mul_nonneg (hW d) (sq_nonneg _)) t.1 t.2.1 t.2.2
    convert hh using 1
    congr 1
    funext z
    dsimp [F, r]
    ring
  have hsumG (z : Fin n → Ω) :
      (∑ t : T, G t z) =
        W (sampleDesign X A z) * ∑ i, b (sampleDesign X A z) i ^ 2 := by
    simp only [T, Fintype.sum_prod_type, G]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [← Finset.mul_sum]
    have hind : (∑ a : Bool, ∑ k : κ,
        (armGroupEvent X A a k).indicator (fun _ => (1 : ℝ)) (z i)) = 1 := by
      cases ha : A (z i) <;>
        simp [-Finset.sum_boole, armGroupEvent,
          Set.indicator_apply, ha]
    rw [hind, mul_one]
  calc
    (∫ z, W (sampleDesign X A z) * designWeightedResidual X A Y center b z ^ 2 ∂ν) =
        ∑ t : T, ∑ u : T, ∫ z, F t u z ∂ν := by
      simp only [hexpand]
      rw [integral_finsetSum _ (fun t _ =>
        integrable_finsetSum _ (fun u _ => hF t u))]
      apply Finset.sum_congr rfl
      intro t _
      exact integral_finsetSum _ (fun u _ => hF t u)
    _ = ∑ t : T, ∫ z, F t t z ∂ν := by
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.sum_eq_single t (fun u _ hut => hoff t u (Ne.symm hut))
        (fun ht => (ht (Finset.mem_univ t)).elim)
    _ ≤ ∑ t : T, M ^ 2 * ∫ z, G t z ∂ν :=
      Finset.sum_le_sum (fun t _ => hdiag t)
    _ = M ^ 2 * ∫ z, W (sampleDesign X A z) *
        (∑ i, b (sampleDesign X A z) i ^ 2) ∂ν := by
      rw [← Finset.mul_sum, ← integral_finsetSum _ (fun t _ => hG t)]
      simp only [hsumG]

/-- For [a sample z of n observations](hyp:n,z) with any [cell label X](hyp:X),
[treatment A](hyp:A), [outcome Y](hyp:Y) and [arm-and-cell centres](hyp:center), [the guarded
residual regression coefficient equals the design-weighted residual sum whose coefficients are the
guarded inverse Gram times the residualized treatment weights](goal), also at a zero Gram. -/
lemma residualRegression_eq_designWeightedResidual {n : ℕ}
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ) (center : Bool → κ → ℝ)
    (z : Fin n → Ω) :
    residualRegression X A Y center z =
      designWeightedResidual X A Y center
        (fun d i => inverseGram d * residualWeight d i) z := by
  classical
  unfold residualRegression regression designWeightedResidual numerator inverseGram
  by_cases hp : 0 < gram (sampleDesign X A z)
  · simp only [hp, if_pos, Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp [hp]

end Causalean.Stat.Sample.Stratified.TreatmentRegression
