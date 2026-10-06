module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.Variance

/-! Finite-moment point-CATE frontier: Helpers/Centering. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- Product-law centering of an asymmetric bilinear kernel. -/
def centeredKernel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Ω → Ω → ℝ) (o z : Ω) : ℝ :=
  B o z - (∫ v, B v z ∂P) - (∫ v, B o v ∂P) + ∫ v, ∫ w, B v w ∂P ∂P


/-- Integrating one coordinate of a square-integrable kernel preserves square integrability,
by the nonnegativity of each section's variance. -/
-- @node: centeredKernel_row_mean_memLp
lemma centeredKernel_row_mean_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : Ω → Ω → ℝ)
    (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
    MemLp (fun x => ∫ y, B x y ∂P) 2 P := by
  have hm := hB.aestronglyMeasurable.integral_prod_right'
  apply (memLp_two_iff_integrable_sq hm).2
  refine hB.integrable_sq.integral_prod_left.mono_nonneg (hm.pow 2)
    (Filter.Eventually.of_forall fun x => sq_nonneg _) ?_
  filter_upwards [hB.aestronglyMeasurable.prodMk_left,
    hB.integrable_sq.prod_right_ae] with x hx hs
  have hsection := (memLp_two_iff_integrable_sq hx).2 hs
  have hv := variance_nonneg (X := fun y => B x y) (μ := P)
  rw [variance_eq_sub hsection] at hv
  exact sub_nonneg.mp hv

/-- Product-law centering has zero conditional mean in each coordinate. -/
-- @node: centeredKernel_conditional_means
lemma centeredKernel_conditional_means {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : Ω → Ω → ℝ)
    (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
    (∀ᵐ x ∂P, (∫ y, centeredKernel P B x y ∂P) = 0) ∧
      (∀ᵐ y ∂P, (∫ x, centeredKernel P B x y ∂P) = 0) := by
  have hi := hB.integrable (by norm_num)
  constructor
  · filter_upwards [hi.prod_right_ae] with x hx
    simp only [centeredKernel]
    have hc : Integrable (fun _ : Ω => ∫ v, B x v ∂P) P := integrable_const _
    have hb : Integrable (fun _ : Ω => ∫ v, ∫ w, B v w ∂P ∂P) P := integrable_const _
    have h1 : Integrable (fun y => B x y - ∫ v, B v y ∂P) P := hx.sub hi.integral_prod_right
    have h2 : Integrable (fun y => B x y - (∫ v, B v y ∂P) - ∫ v, B x v ∂P) P := h1.sub hc
    rw [integral_add h2 hb, integral_sub h1 hc,
      integral_sub hx hi.integral_prod_right, ← integral_integral_swap hi]
    simp
  · filter_upwards [hi.prod_left_ae] with y hy
    simp only [centeredKernel]
    have hc : Integrable (fun _ : Ω => ∫ v, B v y ∂P) P := integrable_const _
    have hb : Integrable (fun _ : Ω => ∫ v, ∫ w, B v w ∂P ∂P) P := integrable_const _
    have h1 : Integrable (fun x => B x y - ∫ v, B v y ∂P) P := hy.sub hc
    have h2 : Integrable (fun x => B x y - (∫ v, B v y ∂P) - ∫ v, B x v ∂P) P := h1.sub hi.integral_prod_left
    rw [integral_add h2 hb, integral_sub h1 hi.integral_prod_left, integral_sub hy hc]
    simp

/-- Removing the row mean is an orthogonal projection onto row-centered kernels,
and hence cannot increase product-law squared energy. -/
-- @node: centeredKernel_row_contraction
lemma centeredKernel_row_contraction {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : Ω → Ω → ℝ)
    (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
    MemLp (fun z : Ω × Ω => B z.1 z.2 - ∫ y, B z.1 y ∂P) 2 (P.prod P) ∧
    (∫ x, ∫ y, (B x y - ∫ z, B x z ∂P)^2 ∂P ∂P) ≤
      ∫ x, ∫ y, (B x y)^2 ∂P ∂P := by
  have hc := hB.sub ((centeredKernel_row_mean_memLp P B hB).comp_fst P)
  refine ⟨hc, integral_mono_ae hc.integrable_sq.integral_prod_left
    hB.integrable_sq.integral_prod_left ?_⟩
  filter_upwards [hB.aestronglyMeasurable.prodMk_left,
    hB.integrable_sq.prod_right_ae] with x hx hs
  have hsection := (memLp_two_iff_integrable_sq hx).2 hs
  rw [← variance_eq_integral hsection.aemeasurable, variance_eq_sub hsection]
  exact sub_le_self _ (sq_nonneg _)

/-- Successive row and column centering gives the doubly degenerate kernel;
each orthogonal centering contracts its squared energy. -/
-- @node: centeredKernel_energy_contraction
lemma centeredKernel_energy_contraction {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : Ω → Ω → ℝ)
    (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
    (∫ x, ∫ y, (centeredKernel P B x y)^2 ∂P ∂P) ≤
      ∫ x, ∫ y, (B x y)^2 ∂P ∂P := by
  let C : Ω → Ω → ℝ := fun x y => B x y - ∫ z, B x z ∂P
  have hr := centeredKernel_row_contraction P B hB
  have hC : MemLp (fun z : Ω × Ω => C z.1 z.2) 2 (P.prod P) := hr.1
  have hswap : MemLp (fun z : Ω × Ω => C z.2 z.1) 2 (P.prod P) :=
    (memLp_two_iff_integrable_sq hC.aestronglyMeasurable.prod_swap).2 hC.integrable_sq.swap
  have hc := centeredKernel_row_contraction P (fun x y => C y x) hswap
  have hCi := hC.integrable (by norm_num)
  have he : ∀ᵐ y ∂P, ∀ x, C x y - (∫ z, C z y ∂P) = centeredKernel P B x y := by
    filter_upwards [(hB.integrable (by norm_num)).prod_left_ae] with y hy
    intro x
    dsimp [C, centeredKernel]
    rw [integral_sub hy (hB.integrable (by norm_num)).integral_prod_left]
    ring
  have hsq : Integrable (fun z : Ω × Ω =>
      (C z.1 z.2 - ∫ v, C v z.2 ∂P)^2) (P.prod P) := hc.1.integrable_sq.swap
  have hrewrite : (∫ x, ∫ y, (centeredKernel P B x y)^2 ∂P ∂P) =
      ∫ y, ∫ x, (C x y - ∫ z, C z y ∂P)^2 ∂P ∂P := by
    calc
      _ = ∫ x, ∫ y, (C x y - ∫ z, C z y ∂P)^2 ∂P ∂P := by
        apply integral_congr_ae
        filter_upwards [] with x
        apply integral_congr_ae
        filter_upwards [he] with y hy
        rw [hy x]
      _ = _ := integral_integral_swap hsq
  rw [hrewrite]
  calc
    _ ≤ ∫ y, ∫ x, (C x y)^2 ∂P ∂P := hc.2
    _ = ∫ x, ∫ y, (C x y)^2 ∂P ∂P := integral_integral_swap hC.integrable_sq.swap
    _ ≤ _ := hr.2

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
