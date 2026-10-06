module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.TemplateGeometry

/-!
# Count-adaptive equal-cell estimator

This file defines the empirical equal-cell Gram matrix and estimator, then
derives deterministic conditioning from the tensor-template geometry.
-/
@[expose] public section
set_option linter.style.haveILetI false
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory
open scoped ENNReal BigOperators Matrix.Norms.L2Operator

-- @env: S3
variable (n : ℕ) (β : ℝ)

/-- Largest dyadic index permitted by the sample size. For [the stated inputs and conditions](hyp:d,n,β), [the `maxMeshIndex` object being defined](goal). -/
noncomputable def maxMeshIndex (d n : ℕ) (β : ℝ) : ℕ :=
  Nat.floor (Real.log n / Real.log 2 / (2 * β + d))

/-- Finite set of candidate dyadic mesh indices. For [the stated inputs and conditions](hyp:d,n,β), [the `meshIndices` object being defined](goal). -/
noncomputable def meshIndices (d n : ℕ) (β : ℝ) : Finset ℕ :=
  Finset.range (maxMeshIndex d n β + 1) -- @realizes Hn(dyadic candidate mesh set)

/-- Width at dyadic index `j`. For [the stated inputs and conditions](hyp:j), [the `meshWidth` object being defined](goal). -/
noncomputable def meshWidth (j : ℕ) : ℝ := (2 : ℝ) ^ (-(j : ℝ))

/-- Dyadic cube index of a point, capped at the last cube. For [the stated inputs and conditions](hyp:d,j,x), [the `cubeIndex` object being defined](goal). -/
noncomputable def cubeIndex (d j : ℕ) (x : Fin d → ℝ) : Fin d → Fin (2 ^ j) :=
  fun i => Fin.ofNat (2 ^ j) (min (Nat.floor ((2 ^ j : ℕ) * x i)) (2 ^ j - 1))

/-- Lower-left corner of a dyadic cube. For [the stated inputs and conditions](hyp:d,j,k), [the `cubeCorner` object being defined](goal). -/
noncomputable def cubeCorner (d j : ℕ) (k : Fin d → Fin (2 ^ j)) : Fin d → ℝ :=
  fun i => (k i).val * meshWidth j -- @realizes aQ(lower-left corner)

/-- Half-open dyadic cube with the global right boundary included. For [the stated inputs and conditions](hyp:d,j,k), [the `dyadicCube` object being defined](goal). -/
noncomputable def dyadicCube (d j : ℕ) (k : Fin d → Fin (2 ^ j)) : Set (Fin d → ℝ) :=
  {x | x ∈ cube d ∧ ∀ i, cubeCorner d j k i ≤ x i ∧
    (x i < cubeCorner d j k i + meshWidth j ∨
      ((k i).val = 2 ^ j - 1 ∧ x i = 1))} -- @realizes Qh(half-open dyadic partition)

/-- Scaled microcell in a macro-cube. For [the stated inputs and conditions](hyp:d,m,j,k,ℓ), [the `scaledMicroCell` object being defined](goal). -/
noncomputable def scaledMicroCell (d m j : ℕ) (k : Fin d → Fin (2 ^ j))
    (ℓ : Fin d → Fin (m + 1)) : Set (Fin d → ℝ) :=
  {x | (fun i => (x i - cubeCorner d j k i) / meshWidth j) ∈ microCube d m ℓ}
  -- @realizes EQell(scaled reference microcell)

/-- Treated observations in one microcell. For [the stated inputs and conditions](hyp:m,j,ω,k,ℓ), [the `treatedCount` object being defined](goal). -/
noncomputable def treatedCount {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (ℓ : Fin d → Fin (m + 1)) : ℕ := by
  classical
  exact
  (Finset.univ.filter (fun i : Fin n => (ω i).2.1 = true ∧
    (ω i).1 ∈ scaledMicroCell d m j k ℓ)).card -- @realizes NQell(treated count)

/-- Total inverse-count weight assigned to one template cell. For [the stated inputs and conditions](hyp:m,j,ω,k,ℓ), [the `treatedCellWeightSum` object being defined](goal). -/
noncomputable def treatedCellWeightSum {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (ℓ : Fin d → Fin (m + 1)) : ℝ := by
  classical
  exact (treatedCount m j ω k ℓ : ℝ)⁻¹ *
    ∑ i : Fin n,
      if (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ
        then (1 : ℝ) else 0

/-- When a template cell is occupied, its inverse-count observation weights sum to one. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,ℓ,hcount), [the asserted conclusion holds](goal). -/
lemma treatedCount_inv_weight_sum {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (ℓ : Fin d → Fin (m + 1))
    (hcount : 0 < treatedCount m j ω k ℓ) :
    treatedCellWeightSum m j ω k ℓ = 1 := by
  classical
  unfold treatedCellWeightSum
  have hsum :
      (∑ i : Fin n,
        if (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ
          then (1 : ℝ) else 0) = treatedCount m j ω k ℓ := by
    simp [treatedCount]
  rw [hsum]
  exact inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hcount))

/-- Mesh passes every cell-count threshold. For [the stated inputs and conditions](hyp:m,β,ω,j), [the `meshFeasible` object being defined](goal). -/
noncomputable def meshFeasible {d n : ℕ} (m : ℕ) (β : ℝ)
    (ω : Fin n → Obs d) (j : ℕ) : Prop :=
  j ∈ meshIndices d n β ∧
  ∀ (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)),
    meshWidth j ^ (-2 * β) ≤ treatedCount m j ω k ℓ

/-- Feasible dyadic indices. For [the stated inputs and conditions](hyp:m,β,ω), [the `feasibleIndices` object being defined](goal). -/
noncomputable def feasibleIndices {d n : ℕ} (m : ℕ) (β : ℝ)
    (ω : Fin n → Obs d) : Finset ℕ := by
  classical
  exact
  (meshIndices d n β).filter (fun j => meshFeasible m β ω j)
  -- @realizes Fh(feasible mesh set)

-- @node: def:mesh-selector
/-- Numerically smallest feasible width, or zero when no mesh is feasible. For [the stated inputs and conditions](hyp:m,β,ω), [the `countSelectedMesh` object being defined](goal). -/
noncomputable def countSelectedMesh {d n : ℕ} (m : ℕ) (β : ℝ)
    (ω : Fin n → Obs d) : ℝ :=
  if (feasibleIndices m β ω).Nonempty then
    meshWidth ((feasibleIndices m β ω).sup id) else 0
  -- @realizes hhat(selected mesh width)

/-- Equal-cell empirical Gram matrix. For [the stated inputs and conditions](hyp:m,j,ω,k), [the `gramHat` object being defined](goal). -/
noncomputable def gramHat {d n : ℕ} (m j : ℕ) (ω : Fin n → Obs d)
    (k : Fin d → Fin (2 ^ j)) : Matrix (MonoIndex d m) (MonoIndex d m) ℝ := by
  classical
  exact
  fun α β => (tensorCount d m : ℝ)⁻¹ *
    ∑ ℓ : Fin d → Fin (m + 1), (treatedCount m j ω k ℓ : ℝ)⁻¹ *
      ∑ i : Fin n, if (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ then
        monoVec d m (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α *
        monoVec d m (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) β
      else 0 -- @realizes GhatQ(equal-cell empirical Gram)

/-- Equal-cell weighting preserves symmetry of the empirical Gram matrix. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k), [the asserted conclusion holds](goal). -/
lemma gramHat_symmetric {d n : ℕ} (m j : ℕ) (ω : Fin n → Obs d)
    (k : Fin d → Fin (2 ^ j)) :
    (gramHat m j ω k).IsHermitian := by
  classical
  rw [Matrix.IsHermitian]
  ext α β
  simp only [Matrix.conjTranspose_apply, star_trivial]
  simp only [gramHat]
  congr 1
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

/-- Equal-cell average of squared polynomial evaluations. For [the stated inputs and conditions](hyp:m,j,ω,k,b), [the `gramHatSquareAvg` object being defined](goal). -/
noncomputable def gramHatSquareAvg {d n : ℕ} (m j : ℕ) (ω : Fin n → Obs d)
    (k : Fin d → Fin (2 ^ j)) (b : MonoIndex d m → ℝ) : ℝ := by
  classical
  exact (tensorCount d m : ℝ)⁻¹ *
    ∑ ℓ : Fin d → Fin (m + 1), (treatedCount m j ω k ℓ : ℝ)⁻¹ *
      ∑ i : Fin n, if (ω i).2.1 = true ∧
          (ω i).1 ∈ scaledMicroCell d m j k ℓ then
          (∑ α, b α * monoVec d m
            (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α) ^ 2
        else 0

/-- The empirical equal-cell Gram quadratic form is an average of squares. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,b), [the asserted conclusion holds](goal). -/
lemma gramHat_quadratic_sum_sq {d n : ℕ} (m j : ℕ) (ω : Fin n → Obs d)
    (k : Fin d → Fin (2 ^ j)) (b : MonoIndex d m → ℝ) :
    (∑ α, ∑ β, b α * gramHat m j ω k α β * b β) =
      gramHatSquareAvg m j ω k b := by
  classical
  simp only [gramHat, gramHatSquareAvg, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext α; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ _
  conv_lhs => arg 2; ext α; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · simp only [sq, Finset.sum_mul, Finset.mul_sum]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  · simp

/-- Every equal-cell empirical Gram matrix has a nonnegative quadratic form. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,b), [the asserted conclusion holds](goal). -/
lemma gramHat_quadratic_nonneg {d n : ℕ} (m j : ℕ) (ω : Fin n → Obs d)
    (k : Fin d → Fin (2 ^ j)) (b : MonoIndex d m → ℝ) :
    0 ≤ ∑ α, ∑ β, b α * gramHat m j ω k α β * b β := by
  rw [gramHat_quadratic_sum_sq]
  unfold gramHatSquareAvg
  classical
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro ℓ _
    apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro i _
      split_ifs <;> positivity

/-- Equal-cell weighting preserves any lower bound that holds at every treated
observation in each occupied template cell. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,b,r,hcount,hbound), [the asserted conclusion holds](goal). -/
lemma gramHatSquareAvg_ge_cell_bounds {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (b : MonoIndex d m → ℝ) (r : (Fin d → Fin (m + 1)) → ℝ)
    (hcount : ∀ ℓ, 0 < treatedCount m j ω k ℓ)
    (hbound : ∀ ℓ i, (ω i).2.1 = true ∧
        (ω i).1 ∈ scaledMicroCell d m j k ℓ →
      r ℓ ≤ (∑ α, b α * monoVec d m
        (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α) ^ 2) :
    (tensorCount d m : ℝ)⁻¹ * ∑ ℓ, r ℓ ≤
      gramHatSquareAvg m j ω k b := by
  classical
  unfold gramHatSquareAvg
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro ℓ _
  have hcountReal : (treatedCount m j ω k ℓ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hcount ℓ))
  have hsum :
      (∑ i : Fin n,
        if (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ
          then r ℓ else 0) = (treatedCount m j ω k ℓ : ℝ) * r ℓ := by
    simp [treatedCount, Finset.sum_ite, mul_comm]
  calc
    r ℓ = (treatedCount m j ω k ℓ : ℝ)⁻¹ *
        ∑ i : Fin n,
          if (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ
            then r ℓ else 0 := by rw [hsum]; field_simp
    _ ≤ (treatedCount m j ω k ℓ : ℝ)⁻¹ *
        ∑ i : Fin n,
          if (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ
            then (∑ α, b α * monoVec d m
              (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α) ^ 2
          else 0 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · exact hbound ℓ i hi
      · exact le_refl _

/-- A uniform pointwise squared-evaluation error transfers through equal-cell
weighting to a Gram quadratic-form error. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,b,ε,hcount,hpoint), [the asserted conclusion holds](goal). -/
lemma templateGram_quadratic_sub_error_le_gramHat {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (b : MonoIndex d m → ℝ) (ε : ℝ)
    (hcount : ∀ ℓ, 0 < treatedCount m j ω k ℓ)
    (hpoint : ∀ ℓ i, (ω i).2.1 = true ∧
        (ω i).1 ∈ scaledMicroCell d m j k ℓ →
      (∑ α, b α * monoVec d m (tensorNode d m ℓ) α) ^ 2 - ε ≤
        (∑ α, b α * monoVec d m
          (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α) ^ 2) :
    (∑ α, ∑ β, b α * templateGram d m α β * b β) - ε ≤
      ∑ α, ∑ β, b α * gramHat m j ω k α β * b β := by
  classical
  have hJ : (tensorCount d m : ℝ) ≠ 0 := by
    unfold tensorCount
    positivity
  have hraw := gramHatSquareAvg_ge_cell_bounds m j ω k b
    (fun ℓ => (∑ α, b α * monoVec d m (tensorNode d m ℓ) α) ^ 2 - ε)
    hcount hpoint
  rw [← gramHat_quadratic_sum_sq] at hraw
  rw [templateGram_quadratic_sum_sq]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, mul_sub] at hraw
  have hcard : (((m + 1) ^ d : ℕ) : ℝ) = (tensorCount d m : ℝ) := rfl
  rw [hcard, ← mul_assoc, inv_mul_cancel₀ hJ, one_mul] at hraw
  exact hraw

/-- Within a template microcube, the squared polynomial evaluation differs
from its node value by at most the template Lipschitz radius times the squared
coefficient norm. [For the stated inputs and conditions](hyp:d,m,b,ℓ,z,hz), [the asserted conclusion holds](goal). -/
lemma templatePointwise_square_perturbation (d m : ℕ)
    (b : MonoIndex d m → ℝ) (ℓ : Fin d → Fin (m + 1)) (z : Fin d → ℝ)
    (hz : z ∈ microCube d m ℓ) :
    (∑ α, b α * monoVec d m (tensorNode d m ℓ) α) ^ 2 -
        templateLip d m * (templateEta d m / 2) * finiteL2Norm b ^ 2 ≤
      (∑ α, b α * monoVec d m z α) ^ 2 := by
  classical
  let z₀ := tensorNode d m ℓ
  let M : Matrix (MonoIndex d m) (MonoIndex d m) ℝ :=
    (fun α β => monoVec d m z₀ α * monoVec d m z₀ β) -
      (fun α β => monoVec d m z α * monoVec d m z β)
  by_cases hzz : z₀ = z
  · subst z
    have hnonneg : 0 ≤ templateLip d m * (templateEta d m / 2) * finiteL2Norm b ^ 2 := by
      exact mul_nonneg
        (mul_nonneg (templateLip_nonneg d m)
          (div_nonneg (le_of_lt (templateEta_pos d m)) (by norm_num)))
        (sq_nonneg _)
    dsimp [z₀]
    linarith
  have hz₀cube : z₀ ∈ cube d := tensorNode_mem_cube d m ℓ
  have hzcube : z ∈ cube d := microCube_subset_cube d m ℓ hz
  have hquot := templateLip_bounds_quotient d m z₀ z hz₀cube hzcube hzz
  have hdist : 0 < ‖z₀ - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
  have hop : finiteL2OpNorm M ≤ templateLip d m * ‖z₀ - z‖ := by
    apply (div_le_iff₀ hdist).mp
    simpa [M] using hquot
  have hnorm : ‖z₀ - z‖ ≤ templateEta d m / 2 := by
    rw [norm_sub_rev]
    exact microCube_norm_sub_tensorNode_le d m ℓ z hz
  have hLip : 0 ≤ templateLip d m := templateLip_nonneg d m
  have hop' : finiteL2OpNorm M ≤ templateLip d m * (templateEta d m / 2) :=
    hop.trans (mul_le_mul_of_nonneg_left hnorm hLip)
  let i₀ : MonoIndex d m := ⟨fun _ => 0, by simp [monoIdx]⟩
  letI : Nonempty (MonoIndex d m) := ⟨i₀⟩
  have hquadM := quadraticForm_le_finiteL2OpNorm M b
  have hscaled : finiteL2OpNorm M * finiteL2Norm b ^ 2 ≤
      templateLip d m * (templateEta d m / 2) * finiteL2Norm b ^ 2 := by
    exact mul_le_mul_of_nonneg_right hop' (sq_nonneg _)
  have hid : (∑ α, ∑ β, b α * M α β * b β) =
      (∑ α, b α * monoVec d m z₀ α) ^ 2 -
        (∑ α, b α * monoVec d m z α) ^ 2 := by
    have hout (w : Fin d → ℝ) :
        (∑ α, ∑ β, b α *
          (monoVec d m w α * monoVec d m w β) * b β) =
          (∑ α, b α * monoVec d m w α) ^ 2 := by
      simp only [sq, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro α hα
      apply Finset.sum_congr rfl
      intro β hβ
      ring
    dsimp [M]
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    exact congrArg₂ (· - ·) (hout z₀) (hout z)
  rw [hid] at hquadM
  dsimp [z₀] at hquadM
  have htotal := hquadM.trans hscaled
  change (∑ α ∈ (monoIdx d m).attach,
      b α * monoVec d m (tensorNode d m ℓ) α) ^ 2 -
        templateLip d m * (templateEta d m / 2) * finiteL2Norm b ^ 2 ≤
      (∑ α ∈ (monoIdx d m).attach, b α * monoVec d m z α) ^ 2
  apply sub_le_iff_le_add.mpr
  simpa only [add_comm] using sub_le_iff_le_add.mp htotal


/-- Equal-cell empirical response moment. For [the stated inputs and conditions](hyp:m,j,ω,k), [the `responseMoment` object being defined](goal). -/
noncomputable def responseMoment {d n : ℕ} (m j : ℕ) (ω : Fin n → Obs d)
    (k : Fin d → Fin (2 ^ j)) : MonoIndex d m → ℝ := by
  classical
  exact
  fun α => (tensorCount d m : ℝ)⁻¹ *
    ∑ ℓ : Fin d → Fin (m + 1), (treatedCount m j ω k ℓ : ℝ)⁻¹ *
      ∑ i : Fin n, if (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ then
        monoVec d m (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α *
          (ω i).2.2 else 0

/-- Local polynomial coefficient vector. For [the stated inputs and conditions](hyp:m,j,ω,k), [the `coefHat` object being defined](goal). -/
noncomputable def coefHat {d n : ℕ} (m j : ℕ) (ω : Fin n → Obs d)
    (k : Fin d → Fin (2 ^ j)) : MonoIndex d m → ℝ :=
  Matrix.mulVec (gramHat m j ω k)⁻¹ (responseMoment m j ω k)
  -- @realizes chatQ(inverse Gram times moment)

-- @node: def:estimator
/-- Count-adaptive, clipped equal-cell local polynomial estimator. For [the stated inputs and conditions](hyp:β,B,ω,x), [the `equalCellEstimator` object being defined](goal). -/
noncomputable def equalCellEstimator {d n : ℕ} (β B : ℝ) (ω : Fin n → Obs d)
    (x : Fin d → ℝ) : ℝ :=
  let m := polynomialDegree β
  let h := countSelectedMesh m β ω
  if h = 0 then 0 else
    let j := (feasibleIndices m β ω).sup id
    let k := cubeIndex d j x
    max (-B) (min B (∑ α : MonoIndex d m,
      monoVec d m (fun a => (x a - cubeCorner d j k a) / h) α *
        coefHat m j ω k α)) -- @realizes muhat(piecewise clipped local polynomial)

/-- Population treated microcell mass. For [the stated inputs and conditions](hyp:P,m,j,k,ℓ), [the `microcellMass` object being defined](goal). -/
noncomputable def microcellMass {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j : ℕ) -- @realizes qQell(P is a probability law)
    (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)) : ℝ :=
  P.real {z | z.2.1 = true ∧ z.1 ∈ scaledMicroCell d m j k ℓ}
  -- @realizes qQell(population treated mass)

/-- Minimum microcell mass in a macro-cube. For [the stated inputs and conditions](hyp:P,m,j,k), [the `cubeMass` object being defined](goal). -/
noncomputable def cubeMass {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j : ℕ) -- @realizes qQ(P is a probability law)
    (k : Fin d → Fin (2 ^ j)) : ℝ :=
  sInf (Set.range (fun ℓ : Fin d → Fin (m + 1) => microcellMass P m j k ℓ))
  -- @realizes qQ(minimum microcell mass)

/-- Sorted weakest-cell masses. For [the stated inputs and conditions](hyp:P,m,j), [the `orderedCubeMass` object being defined](goal). -/
noncomputable def orderedCubeMass {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j : ℕ) : -- @realizes qorder(P is a probability law)
    List ℝ :=
  ((Finset.univ : Finset (Fin d → Fin (2 ^ j))).toList.map (cubeMass P m j)).mergeSort (· ≤ ·)
  -- @realizes qorder(ascending macro-cube masses)

/-- Expected pointwise loss for a measurable estimator and one model law. For [the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,x₀,T,P), [the `pointwiseLossRisk` object being defined](goal). -/
noncomputable def pointwiseLossRisk (d n : ℕ) (β B L C c_f γ : ℝ)
    (x₀ : Fin d → ℝ)
    (T : {T : (Fin n → Obs d) → ℝ // Measurable T})
    (P : {P : Measure (Obs d) // P ∈ ModelClass d β B L C c_f γ}) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal |T.1 ω - responseOf P.1 P.2 x₀|
    ∂Measure.pi (fun _ : Fin n => P.1)

/-- Pointwise minimax risk with extended nonnegative loss. For [the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,x₀), [the `pointwiseRisk` object being defined](goal). -/
noncomputable def pointwiseRisk (d n : ℕ) (β B L C c_f γ : ℝ)
    (x₀ : Fin d → ℝ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal (pointwiseLossRisk d n β B L C c_f γ x₀)
  -- @realizes Rpt(pointwise minimax risk)

/-- Expected spatial-supremum loss for one model law. For [the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,T,P), [the `supLossRisk` object being defined](goal). -/
noncomputable def supLossRisk (d n : ℕ) (β B L C c_f γ : ℝ)
    (T : {T : (Fin n → Obs d) → (Fin d → ℝ) → ℝ // Measurable T})
    (P : {P : Measure (Obs d) // P ∈ ModelClass d β B L C c_f γ}) : ℝ≥0∞ :=
  ∫⁻ ω, ⨆ x ∈ cube d, ENNReal.ofReal |T.1 ω x - responseOf P.1 P.2 x|
    ∂Measure.pi (fun _ : Fin n => P.1)

/-- Expected supremum minimax risk with extended nonnegative loss. For [the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ), [the `supremumRisk` object being defined](goal). -/
noncomputable def supremumRisk (d n : ℕ) (β B L C c_f γ : ℝ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal (supLossRisk d n β B L C c_f γ)
  -- @realizes Rsup(expected supremum minimax risk)

/-- A strictly positive quadratic lower bound makes a finite Gram matrix invertible. [For the stated inputs and conditions](hyp:ι,M,lam,hlam,hbound), [the asserted conclusion holds](goal). -/
lemma det_ne_zero_of_quadratic_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hbound : ∀ b : ι → ℝ,
      lam * finiteL2Norm b ^ 2 ≤ ∑ i, ∑ j, b i * M i j * b j) :
    M.det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨b, hb, hzero⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  have hnorm : 0 < finiteL2Norm b := (finiteL2Norm_pos_iff b).2 hb
  have hqzero : (∑ i, ∑ j, b i * M i j * b j) = 0 := by
    calc
      (∑ i, ∑ j, b i * M i j * b j) = ∑ i, b i * (M.mulVec b) i := by
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      _ = 0 := by simp [hzero]
  have hle := hbound b
  rw [hqzero] at hle
  nlinarith [sq_pos_of_pos hnorm]

/-- A positive quadratic lower bound controls the Euclidean norm of the inverse. [For the stated inputs and conditions](hyp:ι,M,lam,hlam,hbound), [the asserted conclusion holds](goal). -/
lemma finiteL2OpNorm_inv_le_of_quadratic_lower {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] (M : Matrix ι ι ℝ) (lam : ℝ)
    (hlam : 0 < lam)
    (hbound : ∀ b : ι → ℝ,
      lam * finiteL2Norm b ^ 2 ≤ ∑ i, ∑ j, b i * M i j * b j) :
    finiteL2OpNorm M⁻¹ ≤ lam⁻¹ := by
  classical
  have hdet := det_ne_zero_of_quadratic_lower M lam hlam hbound
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hvec : ∀ v : ι → ℝ,
      finiteL2Norm (M⁻¹.mulVec v) ≤ lam⁻¹ * finiteL2Norm v := by
    intro v
    let b := M⁻¹.mulVec v
    have hMb : M.mulVec b = v := by
      dsimp [b]
      rw [Matrix.mulVec_mulVec, M.mul_nonsing_inv hunit, Matrix.one_mulVec]
    have hdot : (∑ i, ∑ j, b i * M i j * b j) = ∑ i, b i * v i := by
      calc
        _ = ∑ i, b i * (M.mulVec b) i := by
          simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
        _ = ∑ i, b i * v i := by rw [hMb]
    have hcs : (∑ i, b i * v i) ≤ finiteL2Norm b * finiteL2Norm v := by
      simpa [finiteL2Norm] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ b v
    have hq := hbound b
    rw [hdot] at hq
    have hbnonneg : 0 ≤ finiteL2Norm b := Real.sqrt_nonneg _
    have hvnonneg : 0 ≤ finiteL2Norm v := Real.sqrt_nonneg _
    by_cases hb : finiteL2Norm b = 0
    · rw [show finiteL2Norm (M⁻¹.mulVec v) = 0 from hb]
      exact mul_nonneg (inv_nonneg.mpr hlam.le) hvnonneg
    · have hbpos : 0 < finiteL2Norm b := lt_of_le_of_ne hbnonneg (Ne.symm hb)
      have hlin : lam * finiteL2Norm b ≤ finiteL2Norm v := by
        nlinarith [sq_pos_of_pos hbpos]
      exact (le_inv_mul_iff₀ hlam).2 hlin
  unfold finiteL2OpNorm
  apply csSup_le
  · let i : ι := Classical.choice inferInstance
    refine ⟨finiteL2Norm (M⁻¹.mulVec (Pi.single i 1)), ?_⟩
    refine ⟨Pi.single i 1, ?_, rfl⟩
    simp [finiteL2Norm, Pi.single_apply]
  · rintro r ⟨v, hv, rfl⟩
    simpa [hv] using hvec v

/-- Unisolvence and distribution-free equal-cell Gram conditioning. [For the stated inputs and conditions](hyp:d,m,n,ω,j,k,hcount), [the asserted conclusion holds](goal). -/
lemma gramHat_minEig_ge_of_pos (d m n : ℕ) (ω : Fin n → Obs d) (j : ℕ)
    (k : Fin d → Fin (2 ^ j))
    (hcount : ∀ ℓ : Fin d → Fin (m + 1), 0 < treatedCount m j ω k ℓ) :
    0 < templateLambda d m ∧
    (∀ b : MonoIndex d m → ℝ,
      templateLambda d m / 2 * finiteL2Norm b ^ 2 ≤
        ∑ α, ∑ β, b α * gramHat m j ω k α β * b β) ∧
    (gramHat m j ω k).det ≠ 0 ∧
    finiteL2OpNorm ((gramHat m j ω k)⁻¹) ≤ 2 / templateLambda d m := by
  classical
  have hlam : 0 < templateLambda d m := templateLambda_pos d m
  have hquad : ∀ b : MonoIndex d m → ℝ,
      templateLambda d m / 2 * finiteL2Norm b ^ 2 ≤
        ∑ α, ∑ β, b α * gramHat m j ω k α β * b β := by
    intro b
    let ε := templateLip d m * (templateEta d m / 2) * finiteL2Norm b ^ 2
    have hpoint : ∀ ℓ i, (ω i).2.1 = true ∧
        (ω i).1 ∈ scaledMicroCell d m j k ℓ →
      (∑ α, b α * monoVec d m (tensorNode d m ℓ) α) ^ 2 - ε ≤
        (∑ α, b α * monoVec d m
          (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α) ^ 2 := by
      intro ℓ i hi
      apply templatePointwise_square_perturbation d m
      exact hi.2
    have htransfer := templateGram_quadratic_sub_error_le_gramHat
      m j ω k b ε hcount hpoint
    have hbase := templateLambda_le_quadratic d m b
    have heta := templateLip_eta_le_half_lambda d m
    have herr : ε ≤ templateLambda d m / 2 * finiteL2Norm b ^ 2 := by
      dsimp [ε]
      have heta' : templateLip d m * (templateEta d m / 2) ≤
          templateLambda d m / 2 := by
        convert heta using 1
        ring
      exact mul_le_mul_of_nonneg_right heta' (sq_nonneg _)
    nlinarith
  have hhalf : 0 < templateLambda d m / 2 := by positivity
  have hdet := det_ne_zero_of_quadratic_lower
    (gramHat m j ω k) (templateLambda d m / 2) hhalf hquad
  have : Nonempty (MonoIndex d m) :=
    ⟨⟨fun _ => 0, by simp [monoIdx]⟩⟩
  have hinv := finiteL2OpNorm_inv_le_of_quadratic_lower
    (gramHat m j ω k) (templateLambda d m / 2) hhalf hquad
  refine ⟨hlam, hquad, hdet, ?_⟩
  convert hinv using 1; field_simp

-- @node: lem:template-conditioning
/-- A feasible candidate mesh has the uniform equal-cell Gram conditioning
asserted in the paper. [For the stated inputs and conditions](hyp:d,m,n,β,ω,j,k,hfeasible), [the asserted conclusion holds](goal). -/
lemma gramHat_minEig_ge (d m n : ℕ) (β : ℝ) (ω : Fin n → Obs d) (j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (hfeasible : meshFeasible m β ω j) :
    0 < templateLambda d m ∧
    (∀ b : MonoIndex d m → ℝ,
      templateLambda d m / 2 * finiteL2Norm b ^ 2 ≤
        ∑ α, ∑ β, b α * gramHat m j ω k α β * b β) ∧
    (gramHat m j ω k).det ≠ 0 ∧
    finiteL2OpNorm ((gramHat m j ω k)⁻¹) ≤ 2 / templateLambda d m := by
  apply gramHat_minEig_ge_of_pos d m n ω j k
  intro ℓ
  have hlower := hfeasible.2 k ℓ
  have hwidth : 0 < meshWidth j := by unfold meshWidth; positivity
  have hthreshold : 0 < meshWidth j ^ (-2 * β) :=
    Real.rpow_pos_of_pos hwidth _
  exact_mod_cast hthreshold.trans_le hlower
end CausalSmith.Stat.WeakOverlap
