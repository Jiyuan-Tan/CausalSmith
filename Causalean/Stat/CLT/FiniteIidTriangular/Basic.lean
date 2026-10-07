module
public import Causalean.Stat.CLT.Lindeberg
public import Causalean.Stat.FiniteDesign.ProductMeasure

/-!
Finite iid triangular rows with bounded, centered, row-dependent scores. The module provides their literal product law, finite expectations, coordinate independence identities, and the row statistics used by the limit results.
-/

@[expose] public section

namespace Causalean.Stat.CLT.FiniteIidTriangular

open Filter MeasureTheory ProbabilityTheory Topology

/-- A bounded finite iid triangular experiment consists of row lengths tending to infinity,
row-dependent probability masses and exactly centered scores, a common absolute score bound,
and one-coordinate second moments tending to a positive variance. -/
structure RowModel (Y : Type*) [Fintype Y] where
  N : ℕ → ℕ
  w : ℕ → Y → ℝ
  f : ℕ → Y → ℝ
  B : ℝ
  v₀ : NNReal
  length_tendsto : Tendsto N atTop atTop
  mass_nonneg : ∀ n y, 0 ≤ w n y
  mass_one : ∀ n, ∑ y, w n y = 1
  centered : ∀ n, ∑ y, w n y * f n y = 0
  bound : ∀ n y, |f n y| ≤ B
  variance_tendsto : Tendsto (fun n => ∑ y, w n y * (f n y) ^ 2)
    atTop (𝓝 (v₀ : ℝ))
  variance_pos : 0 < v₀

namespace RowModel

variable {Y : Type*} [Fintype Y] (M : RowModel Y)

/-- A row and an outcome vector determine their finite iid product mass. -/
def mass (n : ℕ) (ys : Fin (M.N n) → Y) : ℝ :=
  ∏ i, M.w n (ys i)

/-- The finite-product expectation of a real statistic is its mass-weighted sum over all
outcome vectors in the row. -/
def expect (n : ℕ) (F : (Fin (M.N n) → Y) → ℝ) : ℝ :=
  ∑ ys, M.mass n ys * F ys

/-- The one-coordinate mean score in a row is the mass-weighted sum of the scores. The
centering condition of the row model makes it zero. -/
def oneMean (n : ℕ) : ℝ := ∑ y, M.w n y * M.f n y

/-- The one-coordinate second raw moment in a row is the mass-weighted sum of the squared
scores. Because the scores are centered, it is the one-coordinate variance. -/
def oneSecond (n : ℕ) : ℝ := ∑ y, M.w n y * (M.f n y) ^ 2

/-- The one-coordinate fourth raw moment in a row is the mass-weighted fourth score power. -/
def oneFourth (n : ℕ) : ℝ := ∑ y, M.w n y * (M.f n y) ^ 4

/-- The unscaled score sum is the sum of all coordinate scores in a row. -/
def scoreSum (n : ℕ) (ys : Fin (M.N n) → Y) : ℝ :=
  ∑ i, M.f n (ys i)

/-- The normalized score sum divides the score sum by the square root of the row length. -/
noncomputable def normalizedSum (n : ℕ) (ys : Fin (M.N n) → Y) : ℝ :=
  (Real.sqrt (M.N n : ℝ))⁻¹ * M.scoreSum n ys

/-- The empirical score mean divides the score sum by the row length, with zero at length zero. -/
noncomputable def empiricalMean (n : ℕ) (ys : Fin (M.N n) → Y) : ℝ :=
  (M.N n : ℝ)⁻¹ * M.scoreSum n ys

/-- The empirical second moment is the average of the squared coordinate scores. -/
noncomputable def empiricalSecond (n : ℕ) (ys : Fin (M.N n) → Y) : ℝ :=
  (M.N n : ℝ)⁻¹ * ∑ i, (M.f n (ys i)) ^ 2

/-- The centered empirical variance is the empirical second moment minus the squared
empirical score mean. -/
noncomputable def empiricalVariance (n : ℕ) (ys : Fin (M.N n) → Y) : ℝ :=
  M.empiricalSecond n ys - (M.empiricalMean n ys) ^ 2

/-- The product mass is nonnegative at every outcome vector. -/
theorem mass_nonnegative (n : ℕ) (ys : Fin (M.N n) → Y) : 0 ≤ M.mass n ys := by
  unfold mass
  exact Finset.prod_nonneg (by intro i hi; exact M.mass_nonneg n (ys i))

/-- [At each row index](hyp:n), [the total finite-product mass equals one](goal). -/
theorem mass_normalized (n : ℕ) : ∑ ys : Fin (M.N n) → Y, M.mass n ys = 1 := by
  classical
  calc
    ∑ ys : Fin (M.N n) → Y, M.mass n ys =
        ∏ _i : Fin (M.N n), ∑ y, M.w n y := by
          simpa [mass] using
            (Fintype.prod_sum (fun _i : Fin (M.N n) => M.w n)).symm
    _ = 1 := by simp [M.mass_one]

/-- The finite-product expectation of one coordinate statistic is its one-coordinate
mass-weighted expectation. -/
theorem expect_coordinate (n : ℕ) (i : Fin (M.N n)) (g : Y → ℝ) :
    M.expect n (fun ys => g (ys i)) = ∑ y, M.w n y * g y := by
  classical
  let q : Fin (M.N n) → Y → ℝ := fun k y => M.w n y * (if k = i then g y else 1)
  have hfactor (ys : Fin (M.N n) → Y) :
      (∏ k, q k (ys k)) = M.mass n ys * g (ys i) := by
    change (∏ k, M.w n (ys k) * (if k = i then g (ys k) else 1)) = _
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    rfl
  have hsum (k : Fin (M.N n)) :
      (∑ y, q k y) = if k = i then ∑ y, M.w n y * g y else 1 := by
    by_cases hk : k = i <;> simp [q, hk, M.mass_one]
  calc
    M.expect n (fun ys => g (ys i)) = ∑ ys : Fin (M.N n) → Y, ∏ k, q k (ys k) := by
      unfold expect
      apply Finset.sum_congr rfl
      intro ys _
      exact (hfactor ys).symm
    _ = ∏ k, ∑ y, q k y := (Fintype.prod_sum q).symm
    _ = ∑ y, M.w n y * g y := by
      simp_rw [hsum]
      simp

/-- Under the finite product law, two distinct coordinate statistics have expectation equal
to the product of their one-coordinate expectations. -/
theorem expect_coordinate_mul (n : ℕ) (i j : Fin (M.N n)) (hij : i ≠ j)
    (g h : Y → ℝ) :
    M.expect n (fun ys => g (ys i) * h (ys j)) =
      (∑ y, M.w n y * g y) * (∑ y, M.w n y * h y) := by
  classical
  let q : Fin (M.N n) → Y → ℝ := fun k y =>
    M.w n y * (if k = i then g y else 1) * (if k = j then h y else 1)
  have hfactor (ys : Fin (M.N n) → Y) :
      (∏ k, q k (ys k)) = M.mass n ys * (g (ys i) * h (ys j)) := by
    change (∏ k, (M.w n (ys k) * (if k = i then g (ys k) else 1)) *
      (if k = j then h (ys k) else 1)) = _
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    rw [Fintype.prod_ite_eq', Fintype.prod_ite_eq']
    simp only [mass]
    ring
  have hsum (k : Fin (M.N n)) :
      (∑ y, q k y) =
        (if k = i then ∑ y, M.w n y * g y else 1) *
        (if k = j then ∑ y, M.w n y * h y else 1) := by
    by_cases hik : k = i
    · by_cases hjk : k = j
      · exact (hij (hik.symm.trans hjk)).elim
      · have : i ≠ j := hij
        subst k
        simp [q, this]
    · by_cases hjk : k = j
      · have : j ≠ i := Ne.symm hij
        subst k
        simp [q, this]
      · simp [q, hik, hjk, M.mass_one]
  calc
    M.expect n (fun ys => g (ys i) * h (ys j)) =
        ∑ ys : Fin (M.N n) → Y, ∏ k, q k (ys k) := by
      unfold expect
      apply Finset.sum_congr rfl
      intro ys _
      exact (hfactor ys).symm
    _ = ∏ k, ∑ y, q k y := (Fintype.prod_sum q).symm
    _ = (∑ y, M.w n y * g y) * (∑ y, M.w n y * h y) := by
      simp_rw [hsum]
      rw [Finset.prod_mul_distrib]
      simp

end RowModel

open MeasureTheory ProbabilityTheory Causalean.Experimentation.DesignBased

namespace RowModel

variable {Y : Type*} [Fintype Y] (M : RowModel Y)

/-- The single-coordinate design of a row has the row's probability mass function. -/
def coordinateDesign (n : ℕ) : FiniteDesign Y where
  p := M.w n
  p_nonneg := M.mass_nonneg n
  p_sum := M.mass_one n

/-- The product design of a row assigns each outcome vector its literal product mass. -/
def productDesign (n : ℕ) : FiniteDesign (Fin (M.N n) → Y) :=
  prodDesign (fun _ : Fin (M.N n) => M.coordinateDesign n)

/-- Expectation under the product design is the literal finite-product expectation. -/
theorem productDesign_expect (n : ℕ) (F : (Fin (M.N n) → Y) → ℝ) :
    (M.productDesign n).E F = M.expect n F := by
  rfl

/-- A product of coordinate statistics has expectation equal to the product of their
one-coordinate expectations, even when the coordinate statistics differ. -/
theorem expect_prod_coordinate (n : ℕ) (g : Fin (M.N n) → Y → ℝ) :
    M.expect n (fun ys => ∏ i, g i (ys i)) =
      ∏ i, ∑ y, M.w n y * g i y := by
  simpa only [← M.productDesign_expect n, productDesign, coordinateDesign,
    FiniteDesign.E] using
    (FiniteDesign.E_prod_prod (fun _ : Fin (M.N n) => M.coordinateDesign n) g)

variable [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- The probability measure of a row is the finite product-design measure. -/
noncomputable def rowMeasure (n : ℕ) : Measure (Fin (M.N n) → Y) :=
  (M.productDesign n).toMeasure

/-- Integration against the row measure is the literal finite-product expectation. -/
theorem integral_rowMeasure_eq_expect (n : ℕ) (F : (Fin (M.N n) → Y) → ℝ) :
    ∫ ys, F ys ∂M.rowMeasure n = M.expect n F := by
  exact (FiniteDesign.integral_toMeasure (M.productDesign n) F).trans
    (M.productDesign_expect n F)

/-- All coordinate projections in a row are independent under its product measure. -/
theorem rowMeasure_independent (n : ℕ) :
    iIndepFun (fun (i : Fin (M.N n)) (ys : Fin (M.N n) → Y) => ys i)
      (M.rowMeasure n) := by
  exact iIndepFun_prodDesign_eval
    (fun _ : Fin (M.N n) => M.coordinateDesign n)

end RowModel
end Causalean.Stat.CLT.FiniteIidTriangular
