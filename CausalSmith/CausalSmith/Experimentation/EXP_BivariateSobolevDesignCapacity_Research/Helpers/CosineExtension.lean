module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CosinePrior
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Explicit whole-space extensions of the cosine prior

The roadmap's piecewise affine cutoff is one on the cube and zero outside
[-1,2]. Its product gives continuous compactly supported extensions of the
canonical pair polynomials, admissible in the restriction-norm infimum.
The weak-derivative and weighted Fourier-energy bounds remain separate obligations.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The piecewise affine cutoff with plateau [0,1] and support [-1,2]. -/
-- @node: cosineCutoff
def cosineCutoff (u : ℝ) : ℝ := max 0 (min 1 (min (u + 1) (2 - u)))

/-- The cutoff is continuous, including at every joining point. This uses [the stated conclusion](goal). -/
-- @node: cosineCutoff_continuous
@[fun_prop] lemma cosineCutoff_continuous : Continuous cosineCutoff := by
  unfold cosineCutoff
  fun_prop

/-- The cutoff takes values between zero and one everywhere.](goal) This uses [the stated conclusion](goal). -/
-- @node: cosineCutoff_bounds
lemma cosineCutoff_bounds (u : ℝ) : 0 ≤ cosineCutoff u ∧ cosineCutoff u ≤ 1 := by
  unfold cosineCutoff
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The plateau agrees exactly with one on the closed unit interval. Under [the stated conditions](hyp:hu), [the asserted mathematical result follows](goal). -/
-- @node: cosineCutoff_eq_one
lemma cosineCutoff_eq_one {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    cosineCutoff u = 1 := by
  unfold cosineCutoff
  rw [min_eq_left (le_min (by linarith [hu.1]) (by linarith [hu.2]))]
  norm_num

/-- [ On the left ramp the cutoff has slope one.](goal) Under [the stated conditions](hyp:hu). -/
-- @node: cosineCutoff_eq_add_one
lemma cosineCutoff_eq_add_one {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 0) :
    cosineCutoff u = u + 1 := by
  unfold cosineCutoff
  rw [min_eq_left (show u + 1 ≤ 2 - u by linarith [hu.2]),
    min_eq_right (show u + 1 ≤ 1 by linarith [hu.2]),
    max_eq_right (by linarith [hu.1])]

/-- [ On the right ramp the cutoff has slope minus one.](goal) Under [the stated conditions](hyp:hu). -/
-- @node: cosineCutoff_eq_two_sub
lemma cosineCutoff_eq_two_sub {u : ℝ} (hu : u ∈ Icc (1 : ℝ) 2) :
    cosineCutoff u = 2 - u := by
  unfold cosineCutoff
  rw [min_eq_right (show 2 - u ≤ u + 1 by linarith [hu.1]),
    min_eq_right (show 2 - u ≤ 1 by linarith [hu.1]),
    max_eq_right (by linarith [hu.2])]

/-- [ Outside the larger closed interval the cutoff vanishes.](goal) Under [the stated conditions](hyp:hu). -/
-- @node: cosineCutoff_eq_zero
lemma cosineCutoff_eq_zero {u : ℝ} (hu : u ∉ Icc (-1 : ℝ) 2) :
    cosineCutoff u = 0 := by
  apply max_eq_left
  simp only [mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (by linarith))
  · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (by linarith))

/-- The cutoff is a contraction on the whole real line. [The asserted mathematical result follows](goal). -/
-- @node: cosineCutoff_lipschitz
lemma cosineCutoff_lipschitz : LipschitzWith 1 cosineCutoff := by
  have hl : LipschitzWith 1 (fun u : ℝ => u + 1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq]
  have hr : LipschitzWith 1 (fun u : ℝ => 2 - u) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    have he : (2 - x) - (2 - y) = -(x - y) := by ring
    rw [he, abs_neg]
  unfold cosineCutoff
  convert ((hl.min hr).const_min 1).const_max 0 using 1
  simp

/-- On the open left ramp the cutoff has derivative one. Under [the stated conditions](hyp:hu), [the asserted mathematical result follows](goal). -/
-- @node: cosineCutoff_hasDerivAt_left
lemma cosineCutoff_hasDerivAt_left {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 0) :
    HasDerivAt cosineCutoff 1 u := by
  apply ((hasDerivAt_id u).add_const 1).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact cosineCutoff_eq_add_one ⟨hv.1.le, hv.2.le⟩

/-- [ On the open plateau the cutoff has derivative zero.](goal) Under [the stated conditions](hyp:hu). -/
-- @node: cosineCutoff_hasDerivAt_plateau
lemma cosineCutoff_hasDerivAt_plateau {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt cosineCutoff 0 u := by
  apply (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact cosineCutoff_eq_one ⟨hv.1.le, hv.2.le⟩

/-- [ On the open right ramp the cutoff has derivative minus one.](goal) Under [the stated conditions](hyp:hu). -/
-- @node: cosineCutoff_hasDerivAt_right
lemma cosineCutoff_hasDerivAt_right {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt cosineCutoff (-1) u := by
  have h : HasDerivAt (fun v : ℝ => 2 - v) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub 2
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact cosineCutoff_eq_two_sub ⟨hv.1.le, hv.2.le⟩

/-- [ Outside the support interval the cutoff has derivative zero.](goal) Under [the stated conditions](hyp:hu). -/
-- @node: cosineCutoff_hasDerivAt_exterior
lemma cosineCutoff_hasDerivAt_exterior {u : ℝ} (hu : u ∉ Icc (-1 : ℝ) 2) :
    HasDerivAt cosineCutoff 0 u := by
  apply (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hu] with v hv
  exact cosineCutoff_eq_zero hv

/-- [ The cutoff is differentiable away from its four joining points.](goal) Under [the stated conditions](hyp:hm,h0,h1,h2). -/
-- @node: cosineCutoff_differentiableAt
lemma cosineCutoff_differentiableAt {u : ℝ}
    (hm : u ≠ -1) (h0 : u ≠ 0) (h1 : u ≠ 1) (h2 : u ≠ 2) :
    DifferentiableAt ℝ cosineCutoff u := by
  by_cases he : u ∉ Icc (-1 : ℝ) 2
  · exact (cosineCutoff_hasDerivAt_exterior he).differentiableAt
  have hi : u ∈ Icc (-1 : ℝ) 2 := by simpa using he
  by_cases hz : u < 0
  · exact (cosineCutoff_hasDerivAt_left ⟨lt_of_le_of_ne hi.1 hm.symm, hz⟩).differentiableAt
  by_cases ho : u < 1
  · exact (cosineCutoff_hasDerivAt_plateau ⟨lt_of_le_of_ne (le_of_not_gt hz) h0.symm,
      ho⟩).differentiableAt
  exact (cosineCutoff_hasDerivAt_right ⟨lt_of_le_of_ne (le_of_not_gt ho) h1.symm,
    lt_of_le_of_ne hi.2 h2⟩).differentiableAt

/-- The four joining points form a null set, so the cutoff is differentiable almost everywhere. [The asserted mathematical result follows](goal). -/
-- @node: cosineCutoff_ae_differentiableAt
lemma cosineCutoff_ae_differentiableAt :
    ∀ᵐ u : ℝ ∂volume, DifferentiableAt ℝ cosineCutoff u := by
  filter_upwards [Measure.ae_ne volume (-1 : ℝ), Measure.ae_ne volume (0 : ℝ),
    Measure.ae_ne volume (1 : ℝ), Measure.ae_ne volume (2 : ℝ)] with u hm h0 h1 h2
  exact cosineCutoff_differentiableAt hm h0 h1 h2

/-- [ The derivative is bounded by one, including Lean's zero value at nondifferentiable points.](goal) -/
-- @node: cosineCutoff_deriv_bound
lemma cosineCutoff_deriv_bound (u : ℝ) : |deriv cosineCutoff u| ≤ 1 := by
  simpa only [Real.norm_eq_abs, NNReal.coe_one] using
    (norm_deriv_le_of_lipschitz (x₀ := u) cosineCutoff_lipschitz)

/-- [ The product cutoff in the two component coordinates. -/
-- @node: cosinePairCutoff
def cosinePairCutoff (u : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  cosineCutoff (u 0) * cosineCutoff (u 1)

/-- The product cutoff is continuous. This uses [the stated conclusion](goal). -/
-- @node: cosinePairCutoff_continuous
@[fun_prop] lemma cosinePairCutoff_continuous : Continuous cosinePairCutoff := by
  unfold cosinePairCutoff
  fun_prop

/-- The product cutoff is between zero and one.](goal) This uses [the stated conclusion](goal). -/
-- @node: cosinePairCutoff_bounds
lemma cosinePairCutoff_bounds (u : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ cosinePairCutoff u ∧ cosinePairCutoff u ≤ 1 := by
  obtain ⟨h0, h0'⟩ := cosineCutoff_bounds (u 0)
  obtain ⟨h1, h1'⟩ := cosineCutoff_bounds (u 1)
  exact ⟨mul_nonneg h0 h1, by unfold cosinePairCutoff; nlinarith⟩

/-- Differentiating the first coordinate slice gives the first product-rule term. Under [the stated conditions](hyp:hu), [the asserted mathematical result follows](goal). -/
-- @node: cosinePairCutoff_hasDerivAt_first
lemma cosinePairCutoff_hasDerivAt_first {u v : ℝ}
    (hu : DifferentiableAt ℝ cosineCutoff u) :
    HasDerivAt (fun x => cosineCutoff x * cosineCutoff v)
      (deriv cosineCutoff u * cosineCutoff v) u := by
  exact hu.hasDerivAt.mul_const _

/-- [ Differentiating the second coordinate slice gives the second product-rule term.](goal) Under [the stated conditions](hyp:hv). -/
-- @node: cosinePairCutoff_hasDerivAt_second
lemma cosinePairCutoff_hasDerivAt_second {u v : ℝ}
    (hv : DifferentiableAt ℝ cosineCutoff v) :
    HasDerivAt (fun x => cosineCutoff u * cosineCutoff x)
      (cosineCutoff u * deriv cosineCutoff v) v := by
  exact hv.hasDerivAt.const_mul _

/-- The squared Euclidean length of the two cutoff partial derivatives is at most two. [The asserted mathematical result follows](goal). -/
-- @node: cosinePairCutoff_gradient_sq_bound
lemma cosinePairCutoff_gradient_sq_bound (u v : ℝ) :
    (deriv cosineCutoff u * cosineCutoff v) ^ 2 +
      (cosineCutoff u * deriv cosineCutoff v) ^ 2 ≤ 2 := by
  have hu := cosineCutoff_bounds u
  have hv := cosineCutoff_bounds v
  have hdu := (abs_le.mp (cosineCutoff_deriv_bound u))
  have hdv := (abs_le.mp (cosineCutoff_deriv_bound v))
  have hdu2 : (deriv cosineCutoff u) ^ 2 ≤ 1 := by nlinarith
  have hdv2 : (deriv cosineCutoff v) ^ 2 ≤ 1 := by nlinarith
  have hu2 : cosineCutoff u ^ 2 ≤ 1 := by nlinarith
  have hv2 : cosineCutoff v ^ 2 ≤ 1 := by nlinarith
  rw [mul_pow, mul_pow]
  have hfirst := mul_le_mul hdu2 hv2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hsecond := mul_le_mul hu2 hdv2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith

/-- The product cutoff equals one on the closed Euclidean unit cube. Under [the stated conditions](hyp:hu), [the asserted mathematical result follows](goal). -/
-- @node: cosinePairCutoff_eq_one
lemma cosinePairCutoff_eq_one {u : EuclideanSpace ℝ (Fin 2)}
    (hu : u ∈ euclideanCube 2) : cosinePairCutoff u = 1 := by
  rw [cosinePairCutoff, cosineCutoff_eq_one (hu 0), cosineCutoff_eq_one (hu 1), mul_one]

/-- [ A nonzero product cutoff forces both coordinates into [-1,2].](goal) Under [the stated conditions](hyp:hu). -/
-- @node: cosinePairCutoff_support_coordinates
lemma cosinePairCutoff_support_coordinates {u : EuclideanSpace ℝ (Fin 2)}
    (hu : cosinePairCutoff u ≠ 0) : u 0 ∈ Icc (-1 : ℝ) 2 ∧ u 1 ∈ Icc (-1 : ℝ) 2 := by
  constructor
  · by_contra h
    exact hu (by simp [cosinePairCutoff, cosineCutoff_eq_zero h])
  · by_contra h
    exact hu (by simp [cosinePairCutoff, cosineCutoff_eq_zero h])

/-- The product cutoff has compact support in the whole Euclidean plane. [The asserted mathematical result follows](goal). -/
-- @node: cosinePairCutoff_hasCompactSupport
lemma cosinePairCutoff_hasCompactSupport : HasCompactSupport cosinePairCutoff := by
  have hsub : Function.support cosinePairCutoff ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 4 := by
    intro u hu
    obtain ⟨h0, h1⟩ := cosinePairCutoff_support_coordinates hu
    have hsq : ‖u‖ ^ 2 ≤ 8 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      nlinarith [h0.1, h0.2, h1.1, h1.2,
        sq_nonneg (u 0 + 1), sq_nonneg (u 1 + 1)]
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg u]
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 4).of_isClosed_subset
    (isClosed_tsupport _) (closure_minimal hsub Metric.isClosed_closedBall)

/-- [ Multiply a cube formula by the roadmap's product cutoff to extend it globally. -/
-- @node: cosinePairExtension
def cosinePairExtension (g : Cube 2 → ℝ) (u : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (cosinePairCutoff u * g (fun h => u h) : ℝ)

/-- Continuous component formulas give continuous cutoff extensions. This uses [the hg hypothesis](hyp:hg), [the stated conclusion](goal). -/
-- @node: cosinePairExtension_continuous
@[fun_prop] lemma cosinePairExtension_continuous {g : Cube 2 → ℝ} (hg : Continuous g) :
    Continuous (cosinePairExtension g) := by
  unfold cosinePairExtension
  fun_prop

/-- The extension vanishes outside the support of the fixed product cutoff.](goal) This uses [the stated conclusion](goal). -/
-- @node: cosinePairExtension_hasCompactSupport
lemma cosinePairExtension_hasCompactSupport (g : Cube 2 → ℝ) :
    HasCompactSupport (cosinePairExtension g) := by
  have hsub : Function.support (cosinePairExtension g) ⊆ Function.support cosinePairCutoff := by
    intro u hu
    change cosinePairCutoff u ≠ 0
    intro hz
    exact hu (by simp [cosinePairExtension, hz])
  exact cosinePairCutoff_hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
    (closure_mono hsub)

/-- On the closed cube the extension is the original formula, including its boundary. Under [the stated conditions](hyp:hu), [the asserted mathematical result follows](goal). -/
-- @node: cosinePairExtension_eq_on_cube
lemma cosinePairExtension_eq_on_cube (g : Cube 2 → ℝ)
    {u : EuclideanSpace ℝ (Fin 2)} (hu : u ∈ euclideanCube 2) :
    cosinePairExtension g u = (g (fun h => u h) : ℂ) := by
  simp [cosinePairExtension, cosinePairCutoff_eq_one hu]

/-- [ A continuous pair formula has a valid integrable, square-integrable extension
in the defining infimum of the restriction norm.](goal) Under [the stated conditions](hyp:hg). -/
-- @node: cosinePairExtension_admissible
lemma cosinePairExtension_admissible {g : Cube 2 → ℝ} (hg : Continuous g) :
    Integrable (cosinePairExtension g) volume ∧
      MemLp (cosinePairExtension g) 2 volume ∧
      cosinePairExtension g =ᵐ[volume.restrict (euclideanCube 2)]
        fun u => (g (fun h => u h) : ℂ) := by
  have hc := cosinePairExtension_continuous hg
  have hs := cosinePairExtension_hasCompactSupport g
  refine ⟨hc.integrable_of_hasCompactSupport hs, hc.memLp_of_hasCompactSupport hs, ?_⟩
  apply (ae_restrict_iff' ?_).2
  · exact Filter.Eventually.of_forall (fun u hu => cosinePairExtension_eq_on_cube g hu)
  · have heq : euclideanCube 2 = ⋂ h : Fin 2,
        (fun u : EuclideanSpace ℝ (Fin 2) => u h) ⁻¹' Icc (0 : ℝ) 1 := by
      ext u
      simp [euclideanCube]
    rw [heq]
    exact MeasurableSet.iInter (fun h => measurableSet_Icc.preimage (by fun_prop))

/-- [ The canonical pair effects of every cosine-prior realization are continuous formulas. This uses [the hjl hypothesis](hyp:hjl), [the stated conclusion](goal). -/
-- @node: mXi_g2_continuous
@[fun_prop] lemma mXi_g2_continuous {d L : ℕ} (s : ℝ) (ξ : PairIdx d L → Bool)
    (j l : Fin d) (hjl : j < l) :
    Continuous (fun u : Cube 2 => g2 (mXi s L ξ) j l (u 0) (u 1)) := by
  simp_rw [mXi_g2 s ξ j l hjl]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro α _
  by_cases h : α.val.1.1 = j ∧ α.val.1.2 = l
  · simp only [if_pos h]
    fun_prop
  · simp only [if_neg h]
    fun_prop

/-- Every canonical pair polynomial has an explicit admissible whole-space extension.](goal) Under [the stated conditions](hyp:hjl). This uses [the stated conclusion](goal). -/
-- @node: mXi_g2_extension_admissible
lemma mXi_g2_extension_admissible {d L : ℕ} (s : ℝ) (ξ : PairIdx d L → Bool)
    (j l : Fin d) (hjl : j < l) :
    let g : Cube 2 → ℝ := fun u => g2 (mXi s L ξ) j l (u 0) (u 1)
    Integrable (cosinePairExtension g) volume ∧ MemLp (cosinePairExtension g) 2 volume ∧
      cosinePairExtension g =ᵐ[volume.restrict (euclideanCube 2)]
        fun u => (g (fun h => u h) : ℂ) := by
  exact cosinePairExtension_admissible (mXi_g2_continuous s ξ j l hjl)

/-- [ Any admissible whole-space extension bounds the restriction-norm infimum
by its own weighted Fourier energy.](goal) Under [the stated conditions](hyp:hG). -/
-- @node: sobolevNormSq_le_extension_energy
lemma sobolevNormSq_le_extension_energy {p : ℕ} (s : ℝ) (g : Cube p → ℝ)
    (G : EuclideanSpace ℝ (Fin p) → ℂ)
    (hG : Integrable G volume ∧ MemLp G 2 volume ∧
      G =ᵐ[volume.restrict (euclideanCube p)] fun u => (g (fun h => u h) : ℂ)) :
    sobolevNormSq p s g ≤
      ∫⁻ ω, ENNReal.ofReal (‖Fourier G ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s) := by
  exact iInf_le_of_le G (iInf_le_of_le hG le_rfl)

/-- [ The explicit cutoff extension can be used directly to bound every
canonical pair restriction norm of the prior.](goal) Under [the stated conditions](hyp:hjl). -/
-- @node: mXi_g2_norm_le_extension_energy
lemma mXi_g2_norm_le_extension_energy {d L : ℕ} (s : ℝ) (ξ : PairIdx d L → Bool)
    (j l : Fin d) (hjl : j < l) :
    let g : Cube 2 → ℝ := fun u => g2 (mXi s L ξ) j l (u 0) (u 1)
    sobolevNormSq 2 s g ≤
      ∫⁻ ω, ENNReal.ofReal (‖Fourier (cosinePairExtension g) ω‖ ^ 2 *
        (1 + ‖ω‖ ^ 2 / (2 : ℝ)) ^ s) := by
  exact sobolevNormSq_le_extension_energy s _ _ (mXi_g2_extension_admissible s ξ j l hjl)

/-- The zero formula has zero restriction energy, using the zero extension. [The asserted mathematical result follows](goal). -/
-- @node: sobolevNormSq_zero
lemma sobolevNormSq_zero (p : ℕ) (s : ℝ) :
    sobolevNormSq p s (fun _ => 0) = 0 := by
  apply le_antisymm _ (zero_le)
  have hG : Integrable (fun _ : EuclideanSpace ℝ (Fin p) => (0 : ℂ)) volume ∧
      MemLp (fun _ : EuclideanSpace ℝ (Fin p) => (0 : ℂ)) 2 volume ∧
      (fun _ : EuclideanSpace ℝ (Fin p) => (0 : ℂ)) =ᵐ[volume.restrict (euclideanCube p)]
        fun _ => ((0 : ℝ) : ℂ) := ⟨integrable_zero _ _ _, MemLp.zero, Filter.Eventually.of_forall
          (fun _ => rfl)⟩
  simpa [Fourier] using sobolevNormSq_le_extension_energy s (fun _ => 0) (fun _ => 0) hG

/-- [ The main effects contribute no restriction energy to any cosine-prior realization.](goal) -/
-- @node: mXi_main_budget_zero
lemma mXi_main_budget_zero {d L : ℕ} (s : ℝ) (ξ : PairIdx d L → Bool) :
    (∑ j, sobolevNormSq 1 s (fun u => g1 (mXi s L ξ) j (u 0))) = 0 := by
  simp only [mXi_g1_zero, sobolevNormSq_zero, Finset.sum_const_zero]

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
