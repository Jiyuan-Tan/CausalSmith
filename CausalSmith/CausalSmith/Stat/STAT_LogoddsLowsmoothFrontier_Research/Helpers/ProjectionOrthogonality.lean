module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.ProjectionApproximation
public import Causalean.Stat.UStatistic.LocalizedVariance.Mean
public import Causalean.Tactic.IntegralLinearity

/-! # Projection orthogonality

Conditional mark means retain the unit-interval range. Finite cosine
orthogonality proves the residual bias and projected energy identities.
Symmetrization preserves the ordered statistic and its squared envelope. -/
@[expose] public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The conditional mean of a unit-interval mark is nonnegative.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: conditionalMarkMean_nonneg
lemma conditionalMarkMean_nonneg (P : ObservedLaw) (W : BoundedMark) (x : Covariate) :
    0 ≤ conditionalMarkMean P W x := by
  unfold conditionalMarkMean
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro y hy
  exact mul_nonneg (P.interior_cells a y x).1.le (W.range_value (x, a, y)).1

/-- [Normalization of the conditional cells keeps the conditional mark mean below one.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: conditionalMarkMean_le_one
lemma conditionalMarkMean_le_one (P : ObservedLaw) (W : BoundedMark) (x : Covariate) :
    conditionalMarkMean P W x ≤ 1 := by
  rw [← P.normalized_cells x]
  unfold conditionalMarkMean
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro y hy
  exact mul_le_of_le_one_right (P.interior_cells a y x).1.le
    (W.range_value (x, a, y)).2

/-- [A Borel mark and continuous conditional cells give a Borel conditional mean. [the documented result](goal) -/
-- @node: conditionalMarkMean_measurable
@[fun_prop]
lemma conditionalMarkMean_measurable (P : ObservedLaw) (W : BoundedMark) :
    Measurable (conditionalMarkMean P W) := by
  unfold conditionalMarkMean
  have hcells (a y : Bool) : Measurable (P.cells a y) :=
    (P.continuous_cells a y).measurable
  have hmark : Measurable W.value := W.measurable_value
  fun_prop

/-- The squared conditional mean has the unit envelope used in the first-order variance bound. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: conditionalMarkMean_sq_le_one
lemma conditionalMarkMean_sq_le_one (P : ObservedLaw) (W : BoundedMark) (x : Covariate) :
    (conditionalMarkMean P W x)^2 ≤ 1 := by
  have hlo := conditionalMarkMean_nonneg P W x
  have hhi := conditionalMarkMean_le_one P W x
  nlinarith

/-- [The subtype cosine modes inherit the exact orthonormality of the public library. [the stated conclusion](goal) holds. -/
-- @node: cosineBasis_uniformInner
lemma cosineBasis_uniformInner (i j : ℕ) :
    uniformInner (cosineBasis i) (cosineBasis j) = if i = j then 1 else 0 := by
  unfold uniformInner uniformLaw
  have h :=
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.cosineBasis_orthonormal i j
  unfold Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.uniformMeasure at h
  rw [← integral_subtype_comap measurableSet_Icc] at h
  exact h

/-- Products of finitely many cosine modes are integrable under the public design. [the stated conclusion](goal) holds. -/
-- @node: cosineBasis_mul_integrable
lemma cosineBasis_mul_integrable (i j : ℕ) :
    Integrable (fun x => cosineBasis i x * cosineBasis j x) uniformLaw := by
  have h :=
    ((Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.continuous_cosineBasis i).mul
      (Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.continuous_cosineBasis j)).integrableOn_Icc
      (μ := volume) (a := (0 : ℝ)) (b := 1)
  exact (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp h

/-- The inner product of the two literal finite projections is the coefficient product sum. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: cosineProjection_uniformInner
lemma cosineProjection_uniformInner (k : ℕ) (f g : Covariate → ℝ) :
    uniformInner (cosineProjection k f) (cosineProjection k g) =
      ∑ j ∈ Finset.range k, uniformInner f (cosineBasis j) * uniformInner g (cosineBasis j) := by
  have hpoint (x : Covariate) : cosineProjection k f x * cosineProjection k g x =
      ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
        (uniformInner f (cosineBasis i) * uniformInner g (cosineBasis j)) *
          (cosineBasis i x * cosineBasis j x) := by
    unfold cosineProjection
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  unfold uniformInner at ⊢
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun i hi =>
    integrable_finsetSum _ (fun j hj => (cosineBasis_mul_integrable i j).const_mul _))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j hj => (cosineBasis_mul_integrable i j).const_mul _)]
  simp_rw [integral_const_mul]
  change (∑ j ∈ Finset.range k,
    (uniformInner f (cosineBasis i) * uniformInner g (cosineBasis j)) *
      uniformInner (cosineBasis i) (cosineBasis j)) = _
  simp_rw [cosineBasis_uniformInner]
  simp [hi, uniformInner]

/-- [Each cosine mode is integrable under the public design. [the stated conclusion](goal) holds. -/
-- @node: cosineBasis_integrable
lemma cosineBasis_integrable (j : ℕ) : Integrable (cosineBasis j) uniformLaw := by
  have h0 : cosineBasis 0 = fun _ => 1 := by funext x; simp [cosineBasis]
  simpa only [h0, mul_one] using cosineBasis_mul_integrable j 0

/-- A bounded conditional mark mean can multiply any integrable design function. Under the stated assumptions. [The stated hypotheses](hyp:hg) hold, and [the stated conclusion follows](goal). -/
-- @node: conditionalMarkMean_mul_integrable
lemma conditionalMarkMean_mul_integrable (P : ObservedLaw) (W : BoundedMark)
    {g : Covariate → ℝ} (hg : Integrable g uniformLaw) :
    Integrable (fun x => conditionalMarkMean P W x * g x) uniformLaw := by
  apply hg.bdd_mul (c := 1) (conditionalMarkMean_measurable P W).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (conditionalMarkMean_nonneg P W x)]
  exact conditionalMarkMean_le_one P W x

/-- [Finite projection against a target is the sum of their coefficient products.](goal) Under [the stated assumptions](hyp:f,g). Under [the stated assumptions](hyp:hf). -/
-- @node: uniformInner_cosineProjection
lemma uniformInner_cosineProjection (k : ℕ) (f g : Covariate → ℝ)
    (hf : ∀ j, Integrable (fun x => f x * cosineBasis j x) uniformLaw) :
    uniformInner f (cosineProjection k g) =
      ∑ j ∈ Finset.range k, uniformInner f (cosineBasis j) * uniformInner g (cosineBasis j) := by
  unfold uniformInner cosineProjection
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun j hj => (hf j).mul_const _ |>.congr
    (Filter.Eventually.of_forall (fun x => by ring)))]
  apply Finset.sum_congr rfl
  intro j hj
  unfold uniformInner
  rw [show (fun x => f x * ((∫ z, g z * cosineBasis j z ∂uniformLaw) * cosineBasis j x)) =
    (fun x => (f x * cosineBasis j x) * (∫ z, g z * cosineBasis j z ∂uniformLaw)) by
      funext x; ring, integral_mul_const]

/-- [The public inner product is symmetric.](goal) Under [the stated assumptions](hyp:f,g). -/
-- @node: uniformInner_comm
lemma uniformInner_comm (f g : Covariate → ℝ) : uniformInner f g = uniformInner g f := by
  unfold uniformInner
  congr 1
  funext x
  exact mul_comm _ _

/-- [A target times a finite projection is integrable whenever its mode products are.](goal) Under [the stated assumptions](hyp:f,g). Under [the stated assumptions](hyp:hf). -/
-- @node: mul_cosineProjection_integrable
lemma mul_cosineProjection_integrable (k : ℕ) (f g : Covariate → ℝ)
    (hf : ∀ j, Integrable (fun x => f x * cosineBasis j x) uniformLaw) :
    Integrable (fun x => f x * cosineProjection k g x) uniformLaw := by
  simp only [cosineProjection, Finset.mul_sum]
  apply integrable_finsetSum
  intro j hj
  exact ((hf j).mul_const _).congr (Filter.Eventually.of_forall (fun x => by ring))

/-- [Orthogonality of the finite cosine modes gives the exact residual-product bias identity.](goal) Under [the stated assumptions](hyp:f,g). Under [the stated assumptions](hyp:hfg,hf,hg). -/
-- @node: cosineProjection_residual_inner
lemma cosineProjection_residual_inner (k : ℕ) (f g : Covariate → ℝ)
    (hfg : Integrable (fun x => f x * g x) uniformLaw)
    (hf : ∀ j, Integrable (fun x => f x * cosineBasis j x) uniformLaw)
    (hg : ∀ j, Integrable (fun x => g x * cosineBasis j x) uniformLaw) :
    uniformInner f g - uniformInner (cosineProjection k f) (cosineProjection k g) =
      uniformInner (fun x => f x - cosineProjection k f x)
        (fun x => g x - cosineProjection k g x) := by
  have hfp := mul_cosineProjection_integrable k f g hf
  have hgp := mul_cosineProjection_integrable k g f hg
  have hpp : Integrable (fun x => cosineProjection k f x * cosineProjection k g x) uniformLaw := by
    apply mul_cosineProjection_integrable
    intro j
    simp_rw [mul_comm _ (cosineBasis j _)]
    apply mul_cosineProjection_integrable
    exact fun i => cosineBasis_mul_integrable j i
  have hpoint (x : Covariate) :
      (f x - cosineProjection k f x) * (g x - cosineProjection k g x) =
        (f x * g x - f x * cosineProjection k g x) -
          g x * cosineProjection k f x + cosineProjection k f x * cosineProjection k g x := by
    ring
  unfold uniformInner
  rw [show (fun x => (f x - cosineProjection k f x) *
      (g x - cosineProjection k g x)) = _ from funext hpoint]
  integral_linearity
  change uniformInner f g - uniformInner (cosineProjection k f) (cosineProjection k g) =
    uniformInner f g - uniformInner f (cosineProjection k g) -
    uniformInner g (cosineProjection k f) + uniformInner (cosineProjection k f) (cosineProjection k g)
  rw [uniformInner_cosineProjection k f g hf, uniformInner_cosineProjection k g f hg,
    cosineProjection_uniformInner]
  have hs : (∑ j ∈ Finset.range k, uniformInner g (cosineBasis j) * uniformInner f (cosineBasis j)) =
      ∑ j ∈ Finset.range k, uniformInner f (cosineBasis j) * uniformInner g (cosineBasis j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  rw [hs]
  ring

/-- [Conditional mark means are integrable without continuity of the mark. [the stated conclusion](goal) holds. -/
-- @node: conditionalMarkMean_integrable
lemma conditionalMarkMean_integrable (P : ObservedLaw) (W : BoundedMark) :
    Integrable (conditionalMarkMean P W) uniformLaw := by
  have h0 : cosineBasis 0 = fun _ => 1 := by funext x; simp [cosineBasis]
  simpa only [h0, mul_one] using
    conditionalMarkMean_mul_integrable P W (cosineBasis_integrable 0)

/-- The conditional means of Borel bounded marks satisfy the residual-bias identity. [the stated conclusion](goal) holds. -/
-- @node: conditionalMarkMean_residual_inner
lemma conditionalMarkMean_residual_inner (P : ObservedLaw) (W V : BoundedMark) (k : ℕ) :
    uniformInner (conditionalMarkMean P W) (conditionalMarkMean P V) -
      uniformInner (cosineProjection k (conditionalMarkMean P W))
        (cosineProjection k (conditionalMarkMean P V)) =
    uniformInner (fun x => conditionalMarkMean P W x - cosineProjection k (conditionalMarkMean P W) x)
      (fun x => conditionalMarkMean P V x - cosineProjection k (conditionalMarkMean P V) x) := by
  exact cosineProjection_residual_inner k _ _
    (conditionalMarkMean_mul_integrable P W (conditionalMarkMean_integrable P V))
    (fun j => conditionalMarkMean_mul_integrable P W (cosineBasis_integrable j))
    (fun j => conditionalMarkMean_mul_integrable P V (cosineBasis_integrable j))

/-- A finite cosine projection cannot increase the squared energy of a conditional mark mean. [the stated conclusion](goal) holds. -/
-- @node: conditionalMarkMean_projection_energy_le
lemma conditionalMarkMean_projection_energy_le (P : ObservedLaw) (W : BoundedMark) (k : ℕ) :
    uniformInner (cosineProjection k (conditionalMarkMean P W))
      (cosineProjection k (conditionalMarkMean P W)) ≤
    uniformInner (conditionalMarkMean P W) (conditionalMarkMean P W) := by
  have h := conditionalMarkMean_residual_inner P W W k
  have hn : 0 ≤ uniformInner
      (fun x => conditionalMarkMean P W x - cosineProjection k (conditionalMarkMean P W) x)
      (fun x => conditionalMarkMean P W x - cosineProjection k (conditionalMarkMean P W) x) := by
    apply integral_nonneg
    intro x
    exact mul_self_nonneg _
  linarith

/-- Under uniform design each projected conditional mark mean has squared energy at most one. Under the stated assumptions. [The stated hypotheses](hyp:hDesign) hold, and [the stated conclusion follows](goal). -/
-- @node: conditionalMarkMean_projection_energy_le_one
lemma conditionalMarkMean_projection_energy_le_one (P : ObservedLaw) (hDesign : UniformDesign P)
    (W : BoundedMark) (k : ℕ) :
    uniformInner (cosineProjection k (conditionalMarkMean P W))
      (cosineProjection k (conditionalMarkMean P W)) ≤ 1 := by
  let : IsProbabilityMeasure uniformLaw := hDesign ▸
    Measure.isProbabilityMeasure_map (by unfold covariate; fun_prop : Measurable covariate).aemeasurable
  apply (conditionalMarkMean_projection_energy_le P W k).trans
  have hi := conditionalMarkMean_mul_integrable P W (conditionalMarkMean_integrable P W)
  have hbound (x : Covariate) : conditionalMarkMean P W x * conditionalMarkMean P W x ≤ 1 := by
    simpa only [pow_two] using conditionalMarkMean_sq_le_one P W x
  simpa [uniformInner] using integral_mono hi (integrable_const (1 : ℝ)) hbound

/-- [The finite cosine kernel is symmetric in its covariate arguments.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: projectionKernel_symm
lemma projectionKernel_symm (k : ℕ) (x z : Covariate) :
    projectionKernel k x z = projectionKernel k z x := by
  unfold projectionKernel
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- [Integrating one squared kernel slice gives the diagonal sum of squared cosine modes.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: projectionKernel_sq_integral_right
lemma projectionKernel_sq_integral_right (k : ℕ) (x : Covariate) :
    (∫ z, (projectionKernel k x z)^2 ∂uniformLaw) =
      ∑ j ∈ Finset.range k, (cosineBasis j x)^2 := by
  have hpoint (z : Covariate) : (projectionKernel k x z)^2 =
      ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
        (cosineBasis i x * cosineBasis j x) * (cosineBasis i z * cosineBasis j z) := by
    unfold projectionKernel
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun i hi =>
    integrable_finsetSum _ (fun j hj => (cosineBasis_mul_integrable i j).const_mul _))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j hj => (cosineBasis_mul_integrable i j).const_mul _)]
  simp_rw [integral_const_mul]
  change (∑ j ∈ Finset.range k,
    (cosineBasis i x * cosineBasis j x) * uniformInner (cosineBasis i) (cosineBasis j)) = _
  simp_rw [cosineBasis_uniformInner]
  simp [hi, pow_two]

/-- [The squared cosine kernel has exactly rank-k energy under two uniform covariates. [the stated conclusion](goal) holds. -/
-- @node: projectionKernel_sq_integral
lemma projectionKernel_sq_integral (k : ℕ) :
    (∫ x, ∫ z, (projectionKernel k x z)^2 ∂uniformLaw ∂uniformLaw) = (k : ℝ) := by
  simp_rw [projectionKernel_sq_integral_right]
  have hi (j : ℕ) : Integrable (fun x => (cosineBasis j x)^2) uniformLaw := by
    simpa only [pow_two] using cosineBasis_mul_integrable j j
  rw [integral_finsetSum _ (fun j hj => hi j)]
  have he (j : ℕ) : (∫ x, (cosineBasis j x)^2 ∂uniformLaw) = 1 := by
    simpa only [uniformInner, pow_two, ↓reduceIte] using cosineBasis_uniformInner j j
  simp_rw [he]
  simp

/-- The symmetric two-record kernel of the ordered marked statistic. -/
-- @node: symmetricProjectionKernel
def symmetricProjectionKernel (k : ℕ) (W V : Record → ℝ) (o p : Record) : ℝ :=
  projectionKernel k (covariate o) (covariate p) *
    (W o * V p + V o * W p) / 2

/-- Symmetrizing the marks gives an exactly symmetric record kernel. [the stated conclusion](goal) holds. -/
-- @node: symmetricProjectionKernel_symm
lemma symmetricProjectionKernel_symm (k : ℕ) (W V : Record → ℝ) (o p : Record) :
    symmetricProjectionKernel k W V o p = symmetricProjectionKernel k W V p o := by
  unfold symmetricProjectionKernel
  rw [projectionKernel_symm k (covariate p) (covariate o)]
  ring

/-- Swapping the two distinct indices preserves the complete ordered-pair sum. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: orderedPair_sum_swap
lemma orderedPair_sum_swap (n : ℕ) (F : Fin n → Fin n → ℝ) :
    (∑ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2),
      F ij.1 ij.2) =
    ∑ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2),
      F ij.2 ij.1 := by
  apply Finset.sum_bij (fun ij _ => (ij.2, ij.1))
  · intro ij hij
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] using
      Ne.symm (Finset.mem_filter.mp hij).2
  · intro ij hij pq hpq heq
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  · intro ij hij
    refine ⟨(ij.2, ij.1), ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] using
        Ne.symm (Finset.mem_filter.mp hij).2
    · exact Prod.ext rfl rfl
  · intro ij hij
    rfl

/-- Averaging an ordered kernel with its transpose leaves the statistic unchanged. [the stated conclusion](goal) holds. -/
-- @node: projectionStatistic_eq_symmetric
lemma projectionStatistic_eq_symmetric (n k : ℕ) (W V : Record → ℝ)
    (o : Fin n → Record) :
    projectionStatistic n k W V o =
      ((n : ℝ) * ((n : ℝ) - 1))⁻¹ *
        ∑ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2),
          symmetricProjectionKernel k W V (o ij.1) (o ij.2) := by
  have hswap := orderedPair_sum_swap n
    (fun i j => projectionKernel k (covariate (o i)) (covariate (o j)) * W (o i) * V (o j))
  have hpoint (ij : Fin n × Fin n) :
      symmetricProjectionKernel k W V (o ij.1) (o ij.2) =
      (projectionKernel k (covariate (o ij.1)) (covariate (o ij.2)) * W (o ij.1) * V (o ij.2) +
        projectionKernel k (covariate (o ij.2)) (covariate (o ij.1)) * W (o ij.2) * V (o ij.1)) / 2 := by
    unfold symmetricProjectionKernel
    rw [projectionKernel_symm k (covariate (o ij.2)) (covariate (o ij.1))]
    ring
  unfold projectionStatistic
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← hswap]
  congr 1
  ring

/-- The symmetrized unit-interval marks never enlarge the squared cosine kernel. [the stated conclusion](goal) holds. -/
-- @node: symmetricProjectionKernel_sq_le
lemma symmetricProjectionKernel_sq_le (k : ℕ) (W V : BoundedMark) (o p : Record) :
    (symmetricProjectionKernel k W.value V.value o p)^2 ≤
      (projectionKernel k (covariate o) (covariate p))^2 := by
  have h₁ : 0 ≤ W.value o * V.value p :=
    mul_nonneg (W.range_value o).1 (V.range_value p).1
  have h₂ : 0 ≤ V.value o * W.value p :=
    mul_nonneg (V.range_value o).1 (W.range_value p).1
  have h₃ : W.value o * V.value p ≤ 1 :=
    (mul_le_of_le_one_right (W.range_value o).1 (V.range_value p).2).trans
      (W.range_value o).2
  have h₄ : V.value o * W.value p ≤ 1 :=
    (mul_le_of_le_one_right (V.range_value o).1 (W.range_value p).2).trans
      (V.range_value o).2
  have hsq : ((W.value o * V.value p + V.value o * W.value p) / 2)^2 ≤ 1 := by
    nlinarith
  unfold symmetricProjectionKernel
  rw [mul_div_assoc, mul_pow]
  exact (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)).trans_eq (mul_one _)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
