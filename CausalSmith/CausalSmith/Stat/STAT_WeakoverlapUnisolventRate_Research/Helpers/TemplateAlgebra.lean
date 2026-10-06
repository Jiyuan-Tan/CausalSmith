module
public import Causalean.Stat.Minimax.MinimaxValue
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Model
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Tensor-template algebra and finite Euclidean norms

`Causalean.Stat.Nonparametric.designMatrix` is univariate and
`designMatrix_inv_concentration` concerns random Gram concentration. This file
constructs the explicit multivariate tensor template, proves unisolvence, and
develops the finite Euclidean norm bounds used for Gram perturbations.
-/
@[expose] public section
set_option linter.unusedDecidableInType false
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory
open scoped ENNReal BigOperators Matrix.Norms.L2Operator

-- @env: S4
variable (d m : ℕ)

/-- Total-degree multiindices. For [the stated inputs and conditions](hyp:d,m), [the `monoIdx` object being defined](goal). -/
def monoIdx (d m : ℕ) : Finset (Fin d → Fin (m + 1)) :=
  Finset.univ.filter (fun α => (∑ i, (α i).val) ≤ m) -- @realizes Im(total-degree index set)

/-- For [the dimension and degree bound](hyp:d,m), [the monomial-index type](goal)
collects precisely the multiindices whose total degree does not exceed that bound. -/
abbrev MonoIndex (d m : ℕ) := {α : Fin d → Fin (m + 1) // α ∈ monoIdx d m}

/-- Vector of all total-degree monomials. For [the stated inputs and conditions](hyp:d,m,z), [the `monoVec` object being defined](goal). -/
def monoVec (d m : ℕ) (z : Fin d → ℝ) : MonoIndex d m → ℝ :=
  fun α => ∏ i, z i ^ (α.1 i).val -- @realizes U(monomial vector)

/-- Number of tensor nodes. For [the stated inputs and conditions](hyp:d,m), [the `tensorCount` object being defined](goal). -/
def tensorCount (d m : ℕ) : ℕ := (m + 1) ^ d -- @realizes J((m+1)^d)

/-- Tensor interpolation node. For [the stated inputs and conditions](hyp:d,m,ℓ), [the `tensorNode` object being defined](goal). -/
noncomputable def tensorNode (d m : ℕ) (ℓ : Fin d → Fin (m + 1)) : Fin d → ℝ :=
  fun i => ((ℓ i).val + 1 : ℝ) / (m + 2 : ℝ) -- @realizes v_ell(tensor node coordinates)

/-- A polynomial of coordinatewise degree at most `m` that vanishes on every
template node is zero. [For the stated inputs and conditions](hyp:d,m,p,hdeg,hzero), [the asserted conclusion holds](goal). -/
lemma tensorNode_polynomial_eq_zero (d m : ℕ) (p : MvPolynomial (Fin d) ℝ)
    (hdeg : ∀ i, p.degreeOf i ≤ m)
    (hzero : ∀ ℓ : Fin d → Fin (m + 1), MvPolynomial.eval (tensorNode d m ℓ) p = 0) :
    p = 0 := by
  classical
  let S : Fin d → Finset ℝ := fun _ =>
    Finset.univ.image (fun j : Fin (m + 1) => ((j.val + 1 : ℝ) / (m + 2 : ℝ)))
  have hcard (i : Fin d) : (S i).card = m + 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      apply Fin.ext
      have hden : (m + 2 : ℝ) ≠ 0 := by positivity
      have heq : (a.val + 1 : ℝ) = (b.val + 1 : ℝ) :=
        (div_left_inj' hden).mp hab
      exact_mod_cast (add_right_cancel heq : (a.val : ℝ) = b.val)
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset p S
    (by intro i; rw [hcard i]; exact Nat.lt_succ_of_le (hdeg i))
  intro x hx
  have hchoice : ∀ i : Fin d, ∃ a : Fin (m + 1),
      ((a.val + 1 : ℝ) / (m + 2 : ℝ)) = x i := by
    intro i
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (hx i)
    exact ⟨a, ha⟩
  choose ℓ hℓ using hchoice
  have heq : tensorNode d m ℓ = x := funext hℓ
  simpa only [heq] using hzero ℓ

/-- Equal-weight monomial Gram matrix. For [the stated inputs and conditions](hyp:d,m), [the `templateGram` object being defined](goal). -/
noncomputable def templateGram (d m : ℕ) : Matrix (MonoIndex d m) (MonoIndex d m) ℝ :=
  fun α β => (tensorCount d m : ℝ)⁻¹ *
    ∑ ℓ : Fin d → Fin (m + 1), monoVec d m (tensorNode d m ℓ) α *
      monoVec d m (tensorNode d m ℓ) β -- @realizes G0(equal-weight template Gram)

/-- The deterministic tensor template Gram matrix is symmetric. [For the stated inputs and conditions](hyp:d,m), [the asserted conclusion holds](goal). -/
lemma templateGram_symmetric (d m : ℕ) : (templateGram d m).IsHermitian := by
  classical
  rw [Matrix.IsHermitian]
  ext α β
  simp only [Matrix.conjTranspose_apply, star_trivial, templateGram]
  congr 1
  apply Finset.sum_congr rfl
  intro ℓ _
  ring

/-- The tensor Gram quadratic form is the mean of squared polynomial evaluations. [For the stated inputs and conditions](hyp:d,m,b), [the asserted conclusion holds](goal). -/
lemma templateGram_quadratic_sum_sq (d m : ℕ) (b : MonoIndex d m → ℝ) :
    (∑ α, ∑ β, b α * templateGram d m α β * b β) =
      (tensorCount d m : ℝ)⁻¹ *
        ∑ ℓ : Fin d → Fin (m + 1),
          (∑ α, b α * monoVec d m (tensorNode d m ℓ) α) ^ 2 := by
  classical
  simp only [templateGram, sq, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext α
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ _
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  ring

/-- The tensor Gram matrix is positive semidefinite. [For the stated inputs and conditions](hyp:d,m,b), [the asserted conclusion holds](goal). -/
lemma templateGram_quadratic_nonneg (d m : ℕ) (b : MonoIndex d m → ℝ) :
    0 ≤ ∑ α, ∑ β, b α * templateGram d m α β * b β := by
  rw [templateGram_quadratic_sum_sq]
  positivity

/-- One nonzero tensor-node evaluation makes the Gram quadratic form positive. [For the stated inputs and conditions](hyp:d,m,b,h), [the asserted conclusion holds](goal). -/
lemma templateGram_quadratic_pos_of_eval (d m : ℕ) (b : MonoIndex d m → ℝ)
    (h : ∃ ℓ : Fin d → Fin (m + 1),
      ∑ α, b α * monoVec d m (tensorNode d m ℓ) α ≠ 0) :
    0 < ∑ α, ∑ β, b α * templateGram d m α β * b β := by
  rw [templateGram_quadratic_sum_sq]
  apply mul_pos
  · have hJ : 0 < tensorCount d m := by
      unfold tensorCount
      exact pow_pos (Nat.succ_pos m) d
    exact inv_pos.mpr (by exact_mod_cast hJ)
  · obtain ⟨ℓ, hℓ⟩ := h
    apply Finset.sum_pos'
    · intro i hi
      positivity
    · exact ⟨ℓ, Finset.mem_univ _, sq_pos_of_ne_zero hℓ⟩

/-- Euclidean norm of a finite real vector. For [the stated inputs and conditions](hyp:b), [the `finiteL2Norm` object being defined](goal). -/
noncomputable def finiteL2Norm {ι : Type*} [Fintype ι] (b : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, b i ^ 2)

/-- The square of the finite Euclidean norm is the sum of coordinate squares. [For the stated inputs and conditions](hyp:ι,b), [the asserted conclusion holds](goal). -/
lemma finiteL2Norm_sq {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    finiteL2Norm b ^ 2 = ∑ i, b i ^ 2 := by
  unfold finiteL2Norm
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (b i)))

/-- A finite vector has positive Euclidean norm exactly when it is nonzero. [For the stated inputs and conditions](hyp:ι,b), [the asserted conclusion holds](goal). -/
lemma finiteL2Norm_pos_iff {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    0 < finiteL2Norm b ↔ b ≠ 0 := by
  rw [finiteL2Norm, Real.sqrt_pos.iff]
  constructor
  · intro h
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hi)
      (Finset.single_le_sum (fun j _ => sq_nonneg (b j)) (Finset.mem_univ i))
  · intro h hb
    subst b
    simp at h

/-- A unit finite vector has a nonzero coordinate. [For the stated inputs and conditions](hyp:ι,b,hb), [the asserted conclusion holds](goal). -/
lemma finiteL2Norm_one_exists_ne {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (hb : finiteL2Norm b = 1) : ∃ i, b i ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hz : b = 0 := funext fun i => h i
  subst b
  simp [finiteL2Norm] at hb

/-- Tensor-grid unisolvence makes the Gram quadratic form positive on unit vectors. [For the stated inputs and conditions](hyp:d,m,b,hb), [the asserted conclusion holds](goal). -/
lemma templateGram_unit_pos (d m : ℕ) (b : MonoIndex d m → ℝ)
    (hb : finiteL2Norm b = 1) :
    0 < ∑ α, ∑ β, b α * templateGram d m α β * b β := by
  classical
  let e : MonoIndex d m → Fin d →₀ ℕ :=
    fun α => Finsupp.equivFunOnFinite.symm (fun i => (α.1 i).val)
  let p : MvPolynomial (Fin d) ℝ := ∑ α, MvPolynomial.monomial (e α) (b α)
  have he : Function.Injective e := by
    intro α β h
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hi := congrFun (congrArg Finsupp.equivFunOnFinite h) i
    exact hi
  have hdeg : ∀ i, p.degreeOf i ≤ m := by
    intro i
    dsimp [p]
    refine (MvPolynomial.degreeOf_sum_le i Finset.univ _).trans ?_
    apply Finset.sup_le
    intro α _
    by_cases hba : b α = 0
    · simp [hba]
    · rw [MvPolynomial.degreeOf_monomial_eq (e α) i hba]
      have hmem := (Finset.mem_filter.mp α.property).2
      change (α.1 i).val ≤ m
      exact (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans hmem
  have hcoeff (α : MonoIndex d m) : p.coeff (e α) = b α := by
    simp [p, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, he.eq_iff]
  have hne := finiteL2Norm_one_exists_ne b hb
  apply templateGram_quadratic_pos_of_eval
  by_contra hnone
  push Not at hnone
  have hzero : ∀ ℓ : Fin d → Fin (m + 1), MvPolynomial.eval (tensorNode d m ℓ) p = 0 := by
    intro ℓ
    have hz := hnone ℓ
    simpa [p, e, MvPolynomial.eval_sum, MvPolynomial.eval_monomial,
      Finsupp.prod_fintype, monoVec] using hz
  have hp := tensorNode_polynomial_eq_zero d m p hdeg hzero
  obtain ⟨α, hα⟩ := hne
  exact hα (by rw [← hcoeff α, hp]; simp)

/-- Euclidean operator norm of a finite real matrix. For [the stated inputs and conditions](hyp:M), [the `finiteL2OpNorm` object being defined](goal). -/
noncomputable def finiteL2OpNorm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) : ℝ :=
  sSup {r : ℝ | ∃ b : κ → ℝ, finiteL2Norm b = 1 ∧
    r = finiteL2Norm (Matrix.mulVec M b)}

/-- The finite Euclidean operator norm is nonnegative. [For the stated inputs and conditions](hyp:ι,κ,M), [the asserted conclusion holds](goal). -/
lemma finiteL2OpNorm_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) : 0 ≤ finiteL2OpNorm M := by
  apply Real.sSup_nonneg
  rintro r ⟨b, -, rfl⟩
  exact Real.sqrt_nonneg _

/-- The custom finite Euclidean operator norm is bounded by Mathlib's matrix
`ℓ²` operator norm. [For the stated inputs and conditions](hyp:ι,κ,M), [the asserted conclusion holds](goal). -/
lemma finiteL2OpNorm_le_matrixL2 {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (M : Matrix ι κ ℝ) :
    finiteL2OpNorm M ≤ ‖M‖ := by
  unfold finiteL2OpNorm
  apply csSup_le
  · let i : κ := Classical.choice inferInstance
    refine ⟨finiteL2Norm (M.mulVec (Pi.single i 1)), ?_⟩
    refine ⟨Pi.single i 1, ?_, rfl⟩
    simp [finiteL2Norm, Pi.single_apply]
  · rintro r ⟨b, hb, rfl⟩
    have h := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 b)
    rw [show ‖WithLp.toLp 2 b‖ = finiteL2Norm b by
      simp [finiteL2Norm, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs], hb, mul_one] at h
    simpa [finiteL2Norm, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using h

/-- The custom finite operator norm bounds its action on every vector. [For the stated inputs and conditions](hyp:ι,κ,M,b), [the asserted conclusion holds](goal). -/
lemma finiteL2Norm_mulVec_le_opNorm {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (M : Matrix ι κ ℝ) (b : κ → ℝ) :
    finiteL2Norm (M.mulVec b) ≤ finiteL2OpNorm M * finiteL2Norm b := by
  classical
  by_cases hb : b = 0
  · subst b
    simp [finiteL2Norm]
  let r := finiteL2Norm b
  have hr : 0 < r := (finiteL2Norm_pos_iff b).2 hb
  let u : κ → ℝ := fun i => b i / r
  have hu : finiteL2Norm u = 1 := by
    have hsq : finiteL2Norm u ^ 2 = 1 := by
      rw [finiteL2Norm_sq]
      simp only [u, div_pow]
      rw [← Finset.sum_div, ← finiteL2Norm_sq]
      change r ^ 2 / r ^ 2 = 1
      exact div_self (pow_ne_zero 2 (ne_of_gt hr))
    nlinarith [show 0 ≤ finiteL2Norm u from Real.sqrt_nonneg _]
  have hbdd : BddAbove {x : ℝ | ∃ v : κ → ℝ, finiteL2Norm v = 1 ∧
      x = finiteL2Norm (M.mulVec v)} := by
    refine ⟨‖M‖, ?_⟩
    rintro x ⟨v, hv, rfl⟩
    have h := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 v)
    rw [show ‖WithLp.toLp 2 v‖ = finiteL2Norm v by
      simp [finiteL2Norm, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs], hv, mul_one] at h
    simpa [finiteL2Norm, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using h
  have hu_le : finiteL2Norm (M.mulVec u) ≤ finiteL2OpNorm M := by
    apply le_csSup hbdd
    exact ⟨u, hu, rfl⟩
  have hscale : finiteL2Norm (M.mulVec b) = finiteL2Norm (M.mulVec u) * r := by
    have hbu : b = r • u := by
      funext i
      dsimp [u]
      field_simp
    have hsquare : finiteL2Norm (M.mulVec b) ^ 2 =
        (finiteL2Norm (M.mulVec u) * r) ^ 2 := by
      rw [hbu, Matrix.mulVec_smul, finiteL2Norm_sq]
      calc
        ∑ i, (r • M.mulVec u) i ^ 2 = r ^ 2 * ∑ i, (M.mulVec u i) ^ 2 := by
          simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
        _ = r ^ 2 * finiteL2Norm (M.mulVec u) ^ 2 := by
          congr 1
          exact (finiteL2Norm_sq (M.mulVec u)).symm
        _ = (finiteL2Norm (M.mulVec u) * r) ^ 2 := by ring
    nlinarith [show 0 ≤ finiteL2Norm (M.mulVec b) from Real.sqrt_nonneg _,
      show 0 ≤ finiteL2Norm (M.mulVec u) from Real.sqrt_nonneg _,
      mul_nonneg (show 0 ≤ finiteL2Norm (M.mulVec u) from Real.sqrt_nonneg _) hr.le]
  rw [hscale]
  exact mul_le_mul_of_nonneg_right hu_le hr.le

/-- A real square-matrix quadratic form is bounded above by its finite Euclidean
operator norm times the squared coefficient norm. [For the stated inputs and conditions](hyp:ι,M,b), [the asserted conclusion holds](goal). -/
lemma quadraticForm_le_finiteL2OpNorm {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (M : Matrix ι ι ℝ) (b : ι → ℝ) :
    (∑ i, ∑ j, b i * M i j * b j) ≤ finiteL2OpNorm M * finiteL2Norm b ^ 2 := by
  have hdot : (∑ i, ∑ j, b i * M i j * b j) = ∑ i, b i * (M.mulVec b) i := by
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hcs : (∑ i, b i * (M.mulVec b) i) ≤
      finiteL2Norm b * finiteL2Norm (M.mulVec b) := by
    simpa [finiteL2Norm] using
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ b (M.mulVec b)
  rw [hdot]
  calc
    _ ≤ finiteL2Norm b * finiteL2Norm (M.mulVec b) := hcs
    _ ≤ finiteL2Norm b * (finiteL2OpNorm M * finiteL2Norm b) := by
      exact mul_le_mul_of_nonneg_left (finiteL2Norm_mulVec_le_opNorm M b)
        (Real.sqrt_nonneg _)
    _ = finiteL2OpNorm M * finiteL2Norm b ^ 2 := by ring

end CausalSmith.Stat.WeakOverlap
