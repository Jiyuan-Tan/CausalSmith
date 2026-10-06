module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CosineDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Integration by parts for the cosine-prior cutoff

The piecewise affine cutoff has an integrable derivative. Splitting at its
joining points proves integration by parts for a cutoff times a smooth formula:
the shared boundary terms cancel and the exterior boundary terms vanish.
This supplies the one-dimensional face-cancellation step of the weak-derivative
roadmap, without imposing a periodic boundary condition.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The cutoff derivative is integrable on every finite interval.](goal) -/
-- @node: cosineCutoff_deriv_intervalIntegrable
lemma cosineCutoff_deriv_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (deriv cosineCutoff) volume a b := by
  -- `fun_prop` does not cover this bounded derivative's integrability.
  rw [intervalIntegrable_iff]
  apply (intervalIntegrable_iff.mp (intervalIntegrable_const (a := a) (b := b)
    (c := (1 : ℝ)))).mono'
  · exact (measurable_deriv cosineCutoff).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using cosineCutoff_deriv_bound x)

/-- [ The cutoff vanishes at the two exterior faces of its support interval.](goal) -/
-- @node: cosineCutoff_exterior_endpoints
lemma cosineCutoff_exterior_endpoints : cosineCutoff (-1) = 0 ∧ cosineCutoff 2 = 0 := by
  norm_num [cosineCutoff]

/-- On a single smooth piece, the derivative of the cutoff product has the usual product rule. Under [the stated conditions](hyp:hq,hf), [the asserted mathematical result follows](goal). -/
-- @node: cosineCutoff_mul_hasDerivAt
lemma cosineCutoff_mul_hasDerivAt {f f' : ℝ → ℝ} {x : ℝ}
    (hq : DifferentiableAt ℝ cosineCutoff x) (hf : HasDerivAt f (f' x) x) :
    HasDerivAt (fun u => cosineCutoff u * f u)
      (deriv cosineCutoff x * f x + cosineCutoff x * f' x) x := by
  exact hq.hasDerivAt.mul hf

/-- [ The cutoff product rule holds almost everywhere, including across its joins.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: cosineCutoff_mul_ae_hasDerivAt
lemma cosineCutoff_mul_ae_hasDerivAt {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) :
    ∀ᵐ x : ℝ ∂volume, HasDerivAt (fun u => cosineCutoff u * f u)
      (deriv cosineCutoff x * f x + cosineCutoff x * f' x) x := by
  filter_upwards [cosineCutoff_ae_differentiableAt] with x hx
  exact cosineCutoff_mul_hasDerivAt hx (hf x)

/-- [ The candidate product derivative is integrable on any finite interval when the formula
has a continuous derivative.](goal) Under [the stated conditions](hyp:hf,hf'). -/
-- @node: cosineCutoff_mul_deriv_intervalIntegrable
lemma cosineCutoff_mul_deriv_intervalIntegrable {f f' : ℝ → ℝ}
    (hf : Continuous f) (hf' : Continuous f') (a b : ℝ) :
    IntervalIntegrable (fun x => deriv cosineCutoff x * f x + cosineCutoff x * f' x)
      volume a b := by
  exact ((cosineCutoff_deriv_intervalIntegrable a b).mul_continuousOn hf.continuousOn).add
    ((hf'.intervalIntegrable a b).continuousOn_mul cosineCutoff_continuous.continuousOn)

/-- [ Integration by parts for a cutoff product on a piece where the cutoff is differentiable.](goal) Under [the stated conditions](hyp:hf,hf',hv,hv',hq). -/
-- @node: cosineCutoff_mul_integration_by_parts_piece
lemma cosineCutoff_mul_integration_by_parts_piece {f f' v v' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : Continuous v') (a b : ℝ)
    (hq : ∀ x ∈ Ioo (min a b) (max a b), DifferentiableAt ℝ cosineCutoff x) :
    (∫ x in a..b, (cosineCutoff x * f x) * v' x) =
      (cosineCutoff b * f b) * v b - (cosineCutoff a * f a) * v a -
        ∫ x in a..b, (deriv cosineCutoff x * f x + cosineCutoff x * f' x) * v x := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hvc : Continuous v := continuous_iff_continuousAt.mpr (fun x => (hv x).continuousAt)
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (cosineCutoff_continuous.mul hfc).continuousOn hvc.continuousOn
    (fun x hx => cosineCutoff_mul_hasDerivAt (hq x hx) (hf x))
    (fun x _ => hv x) (cosineCutoff_mul_deriv_intervalIntegrable hfc hf' a b)
    (hv'.intervalIntegrable a b)

/-- [ Integration by parts across all three pieces cancels the interior faces; the exterior
faces contribute zero. This is the weak product rule tested on a smooth function.](goal) Under [the stated conditions](hyp:hf,hf',hv,hv'). -/
-- @node: cosineCutoff_mul_integration_by_parts
lemma cosineCutoff_mul_integration_by_parts {f f' v v' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : Continuous v') :
    (∫ x in (-1 : ℝ)..2, (cosineCutoff x * f x) * v' x) =
      -(∫ x in (-1 : ℝ)..2,
        (deriv cosineCutoff x * f x + cosineCutoff x * f' x) * v x) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hvc : Continuous v := continuous_iff_continuousAt.mpr (fun x => (hv x).continuousAt)
  have hleft := cosineCutoff_mul_integration_by_parts_piece hf hf' hv hv' (-1) 0
    (fun x hx => (cosineCutoff_hasDerivAt_left (by simpa using hx)).differentiableAt)
  have hmid := cosineCutoff_mul_integration_by_parts_piece hf hf' hv hv' 0 1
    (fun x hx => (cosineCutoff_hasDerivAt_plateau (by simpa using hx)).differentiableAt)
  have hright := cosineCutoff_mul_integration_by_parts_piece hf hf' hv hv' 1 2
    (fun x hx => (cosineCutoff_hasDerivAt_right (by simpa using hx)).differentiableAt)
  have hi (a b : ℝ) : IntervalIntegrable
      (fun x => (cosineCutoff x * f x) * v' x) volume a b :=
    ((cosineCutoff_continuous.mul hfc).mul hv').intervalIntegrable a b
  have hj (a b : ℝ) : IntervalIntegrable
      (fun x => (deriv cosineCutoff x * f x + cosineCutoff x * f' x) * v x)
      volume a b :=
    (cosineCutoff_mul_deriv_intervalIntegrable hfc hf' a b).mul_continuousOn hvc.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-1) 1) (hi 1 2),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-1) 0) (hi 0 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hj (-1) 1) (hj 1 2),
    ← intervalIntegral.integral_add_adjacent_intervals (hj (-1) 0) (hj 0 1),
    hleft, hmid, hright, cosineCutoff_exterior_endpoints.1,
    cosineCutoff_exterior_endpoints.2]
  ring

/-- [ The derivative vanishes outside the cutoff's support interval.](goal) Under [the stated conditions](hyp:hx). -/
-- @node: cosineCutoff_deriv_eq_zero_exterior
lemma cosineCutoff_deriv_eq_zero_exterior {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 2) :
    deriv cosineCutoff x = 0 := by
  exact (cosineCutoff_hasDerivAt_exterior hx).deriv

/-- [ On the whole real line the cutoff product satisfies integration by parts, with no
boundary restriction on either smooth factor.](goal) Under [the stated conditions](hyp:hf,hf',hv,hv'). -/
-- @node: cosineCutoff_mul_weak_derivative
lemma cosineCutoff_mul_weak_derivative {f f' v v' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : Continuous v') :
    (∫ x : ℝ, (cosineCutoff x * f x) * v' x) =
      -(∫ x : ℝ, (deriv cosineCutoff x * f x + cosineCutoff x * f' x) * v x) := by
  have hi : (∫ x in (-1 : ℝ)..2, (cosineCutoff x * f x) * v' x) =
      ∫ x : ℝ, (cosineCutoff x * f x) * v' x := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 2),
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [cosineCutoff_eq_zero hx]
  have hj : (∫ x in (-1 : ℝ)..2,
      (deriv cosineCutoff x * f x + cosineCutoff x * f' x) * v x) =
      ∫ x : ℝ, (deriv cosineCutoff x * f x + cosineCutoff x * f' x) * v x := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 2),
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [cosineCutoff_eq_zero hx, cosineCutoff_deriv_eq_zero_exterior hx]
  rw [← hi, ← hj]
  exact cosineCutoff_mul_integration_by_parts hf hf' hv hv'

/-- [ The finite cosine polynomial is continuous on the whole coordinate plane. This uses [the stated conclusion](goal). -/
-- @node: pairCosinePolynomial_continuous
@[fun_prop] lemma pairCosinePolynomial_continuous {L : ℕ} (h : Fin L × Fin L → ℝ) :
    Continuous (pairCosinePolynomial h) := by
  unfold pairCosinePolynomial
  fun_prop

/-- Each explicit partial polynomial is continuous on the whole coordinate plane. This uses [the stated conclusion](goal). -/
-- @node: pairCosinePartial_continuous
@[fun_prop] lemma pairCosinePartial_continuous {L : ℕ} (h : Fin L × Fin L → ℝ)
    (r : Fin 2) : Continuous (pairCosinePartial h r) := by
  unfold pairCosinePartial pairDerivativeMode
  split_ifs <;> fun_prop

/-- The cutoff's coordinate partial, using the almost-everywhere scalar derivative. -/
-- @node: pairCutoffPartial
def pairCutoffPartial (r : Fin 2) (x : Cube 2) : ℝ :=
  if r = 0 then deriv cosineCutoff (x 0) * cosineCutoff (x 1)
  else cosineCutoff (x 0) * deriv cosineCutoff (x 1)

/-- The roadmap's explicit weak partial derivative of the cutoff cosine polynomial. -/
-- @node: pairCosineExtensionPartial
def pairCosineExtensionPartial {L : ℕ} (h : Fin L × Fin L → ℝ)
    (r : Fin 2) (x : Cube 2) : ℝ :=
  pairCutoffPartial r x * pairCosinePolynomial h x +
    (cosineCutoff (x 0) * cosineCutoff (x 1)) * pairCosinePartial h r x

/-- On every coordinate slice the explicit pair partial is a weak derivative of the
cutoff extension. The smooth test function need not vanish at the cutoff's joins.](goal) Under [the stated conditions](hyp:hv,hv'). This uses [the stated conclusion](goal). -/
-- @node: pairCosineExtensionPartial_weak_slice
lemma pairCosineExtensionPartial_weak_slice {L : ℕ} (h : Fin L × Fin L → ℝ)
    (r : Fin 2) (x : Cube 2) {v v' : ℝ → ℝ}
    (hv : ∀ t, HasDerivAt v (v' t) t) (hv' : Continuous v') :
    (∫ t : ℝ, (cosineCutoff (Function.update x r t 0) *
      cosineCutoff (Function.update x r t 1) *
      pairCosinePolynomial h (Function.update x r t)) * v' t) =
      -(∫ t : ℝ, pairCosineExtensionPartial h r (Function.update x r t) * v t) := by
  classical
  have hd (t : ℝ) : HasDerivAt (fun u => pairCosinePolynomial h (Function.update x r u))
      (pairCosinePartial h r (Function.update x r t)) t := by
    simpa using
      pairCosinePolynomial_hasDerivAt h r (Function.update x r t)
  fin_cases r
  · have hf (t : ℝ) := (hd t).const_mul (cosineCutoff (x 1))
    have hf' : Continuous (fun t => cosineCutoff (x 1) *
        pairCosinePartial h 0 (Function.update x 0 t)) := by fun_prop
    convert cosineCutoff_mul_weak_derivative hf hf' hv hv' using 1 <;>
      congr 2 <;> funext t <;>
      dsimp [pairCosineExtensionPartial, pairCutoffPartial, Function.update] <;> ring
  · have hf (t : ℝ) := (hd t).const_mul (cosineCutoff (x 0))
    have hf' : Continuous (fun t => cosineCutoff (x 0) *
        pairCosinePartial h 1 (Function.update x 1 t)) := by fun_prop
    convert cosineCutoff_mul_weak_derivative hf hf' hv hv' using 1 <;>
      congr 2 <;> funext t <;>
      dsimp [pairCosineExtensionPartial, pairCutoffPartial, Function.update] <;> ring

/-- Each cutoff partial has absolute value at most one. [The asserted mathematical result follows](goal). -/
-- @node: pairCutoffPartial_abs_le
lemma pairCutoffPartial_abs_le (r : Fin 2) (x : Cube 2) :
    |pairCutoffPartial r x| ≤ 1 := by
  have hq (j : Fin 2) : |cosineCutoff (x j)| ≤ 1 := by
    rw [abs_of_nonneg (cosineCutoff_bounds _).1]
    exact (cosineCutoff_bounds _).2
  fin_cases r <;> simp only [pairCutoffPartial, Fin.zero_eta, ↓reduceIte, abs_mul]
  · simpa using mul_le_mul (cosineCutoff_deriv_bound _) (hq 1) (abs_nonneg _) (by norm_num)
  · simpa using mul_le_mul (hq 0) (cosineCutoff_deriv_bound _) (abs_nonneg _) (by norm_num)

/-- [ The explicit extension partial is dominated by continuous polynomial magnitudes.](goal) -/
-- @node: pairCosineExtensionPartial_abs_le
lemma pairCosineExtensionPartial_abs_le {L : ℕ} (h : Fin L × Fin L → ℝ)
    (r : Fin 2) (x : Cube 2) :
    |pairCosineExtensionPartial h r x| ≤
      |pairCosinePolynomial h x| + |pairCosinePartial h r x| := by
  have hq : |cosineCutoff (x 0) * cosineCutoff (x 1)| ≤ 1 := by
    have hb := cosinePairCutoff_bounds (WithLp.toLp 2 x)
    change 0 ≤ cosineCutoff (x 0) * cosineCutoff (x 1) ∧
      cosineCutoff (x 0) * cosineCutoff (x 1) ≤ 1 at hb
    rw [abs_of_nonneg hb.1]
    exact hb.2
  calc
    |pairCosineExtensionPartial h r x| ≤
        |pairCutoffPartial r x * pairCosinePolynomial h x| +
          |(cosineCutoff (x 0) * cosineCutoff (x 1)) * pairCosinePartial h r x| :=
      abs_add_le _ _
    _ ≤ |pairCosinePolynomial h x| + |pairCosinePartial h r x| := by
      simp only [abs_mul]
      exact add_le_add
        (by simpa using mul_le_mul_of_nonneg_right (pairCutoffPartial_abs_le r x) (abs_nonneg _))
        (by simpa using mul_le_mul_of_nonneg_right hq (abs_nonneg _))

/-- The extension partial vanishes when either coordinate is outside the support square. Under [the stated conditions](hyp:hx), [the asserted mathematical result follows](goal). -/
-- @node: pairCosineExtensionPartial_eq_zero_exterior
lemma pairCosineExtensionPartial_eq_zero_exterior {L : ℕ} (h : Fin L × Fin L → ℝ)
    (r : Fin 2) (x : Cube 2)
    (hx : x 0 ∉ Icc (-1 : ℝ) 2 ∨ x 1 ∉ Icc (-1 : ℝ) 2) :
    pairCosineExtensionPartial h r x = 0 := by
  rcases hx with hx | hx <;> fin_cases r <;>
    simp [pairCosineExtensionPartial, pairCutoffPartial,
      cosineCutoff_eq_zero hx, cosineCutoff_deriv_eq_zero_exterior hx]

/-- The candidate partial has compact support in the Euclidean plane. [The asserted mathematical result follows](goal). -/
-- @node: pairCosineExtensionPartial_hasCompactSupport
lemma pairCosineExtensionPartial_hasCompactSupport {L : ℕ} (h : Fin L × Fin L → ℝ)
    (r : Fin 2) :
    HasCompactSupport (fun u : EuclideanSpace ℝ (Fin 2) =>
      pairCosineExtensionPartial h r (fun j => u j)) := by
  have hsub : Function.support (fun u : EuclideanSpace ℝ (Fin 2) =>
      pairCosineExtensionPartial h r (fun j => u j)) ⊆ Metric.closedBall 0 4 := by
    intro u hu
    have h0 : u 0 ∈ Icc (-1 : ℝ) 2 := by
      by_contra hx
      exact hu (pairCosineExtensionPartial_eq_zero_exterior h r _ (Or.inl hx))
    have h1 : u 1 ∈ Icc (-1 : ℝ) 2 := by
      by_contra hx
      exact hu (pairCosineExtensionPartial_eq_zero_exterior h r _ (Or.inr hx))
    have hsq : ‖u‖ ^ 2 ≤ 8 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      nlinarith [h0.1, h0.2, h1.1, h1.2, sq_nonneg (u 0 + 1), sq_nonneg (u 1 + 1)]
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg u]
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 4).of_isClosed_subset
    (isClosed_tsupport _) (closure_minimal hsub Metric.isClosed_closedBall)

/-- The explicit weak partial is in every Lp space, in particular L1 and L2: it is measurable,
compactly supported, and bounded by a continuous envelope on that support. Under [the stated conditions](hyp:p), [the asserted mathematical result follows](goal). -/
-- @node: pairCosineExtensionPartial_memLp
lemma pairCosineExtensionPartial_memLp {L : ℕ} (h : Fin L × Fin L → ℝ)
    (r : Fin 2) (p : ℝ≥0∞) :
    MemLp (fun u : EuclideanSpace ℝ (Fin 2) =>
      pairCosineExtensionPartial h r (fun j => u j)) p volume := by
  let F := fun u : EuclideanSpace ℝ (Fin 2) => pairCosineExtensionPartial h r (fun j => u j)
  have hs : HasCompactSupport F := pairCosineExtensionPartial_hasCompactSupport h r
  have he : Continuous (fun u : EuclideanSpace ℝ (Fin 2) =>
      |pairCosinePolynomial h (fun j => u j)| + |pairCosinePartial h r (fun j => u j)|) := by
    fun_prop
  obtain ⟨C, hC⟩ := hs.bddAbove_image he.continuousOn
  apply hs.memLp_of_bound (C := max C 0)
  · apply Measurable.aestronglyMeasurable
    dsimp [F]
    unfold pairCosineExtensionPartial pairCutoffPartial
    split_ifs <;> fun_prop
  · apply Filter.Eventually.of_forall
    intro u
    by_cases hz : F u = 0
    · simp [hz]
    · rw [Real.norm_eq_abs]
      exact (pairCosineExtensionPartial_abs_le h r _).trans
        ((hC ⟨u, subset_closure hz, rfl⟩).trans (le_max_left _ _))

/-- Both analytic integrability obligations for the weak partial follow from its Lp regularity. [The asserted mathematical result follows](goal). -/
-- @node: pairCosineExtensionPartial_integrable_and_memLp
lemma pairCosineExtensionPartial_integrable_and_memLp {L : ℕ}
    (h : Fin L × Fin L → ℝ) (r : Fin 2) :
    Integrable (fun u : EuclideanSpace ℝ (Fin 2) =>
      pairCosineExtensionPartial h r (fun j => u j)) volume ∧
    MemLp (fun u : EuclideanSpace ℝ (Fin 2) =>
      pairCosineExtensionPartial h r (fun j => u j)) 2 volume := by
  exact ⟨memLp_one_iff_integrable.mp (pairCosineExtensionPartial_memLp h r 1),
    pairCosineExtensionPartial_memLp h r 2⟩

/-- [ The two explicit cutoff partials have total squared length at most two.](goal) -/
-- @node: pairCutoffPartial_gradient_sq_le
lemma pairCutoffPartial_gradient_sq_le (x : Cube 2) :
    pairCutoffPartial 0 x ^ 2 + pairCutoffPartial 1 x ^ 2 ≤ 2 := by
  simpa [pairCutoffPartial] using cosinePairCutoff_gradient_sq_bound (x 0) (x 1)

/-- [ The product rule and the squared triangle inequality give the roadmap's pointwise
gradient estimate before integration.](goal) -/
-- @node: pairCosineExtensionPartial_gradient_sq_le
lemma pairCosineExtensionPartial_gradient_sq_le {L : ℕ} (h : Fin L × Fin L → ℝ)
    (x : Cube 2) :
    (pairCosineExtensionPartial h 0 x ^ 2 + pairCosineExtensionPartial h 1 x ^ 2) / 2 ≤
      (cosineCutoff (x 0) * cosineCutoff (x 1)) ^ 2 *
        (pairCosinePartial h 0 x ^ 2 + pairCosinePartial h 1 x ^ 2) +
      2 * pairCosinePolynomial h x ^ 2 := by
  have hsum (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  have h0 := hsum (pairCutoffPartial 0 x * pairCosinePolynomial h x)
    ((cosineCutoff (x 0) * cosineCutoff (x 1)) * pairCosinePartial h 0 x)
  have h1 := hsum (pairCutoffPartial 1 x * pairCosinePolynomial h x)
    ((cosineCutoff (x 0) * cosineCutoff (x 1)) * pairCosinePartial h 1 x)
  have hq := mul_le_mul_of_nonneg_right (pairCutoffPartial_gradient_sq_le x)
    (sq_nonneg (pairCosinePolynomial h x))
  change (pairCosineExtensionPartial h 0 x) ^ 2 ≤ _ at h0
  change (pairCosineExtensionPartial h 1 x) ^ 2 ≤ _ at h1
  simp only [mul_pow] at h0 h1
  nlinarith

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
