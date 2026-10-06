module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Basic
public import Causalean.Stat.Concentration.Matrix.LocalizedGramBasic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Balanced polynomial estimators

All fits are total. A cell with an empty norming subcell receives the zero fit.
The scale index `j` denotes the dyadic width `2⁻ʲ`.
-/
@[expose] public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped BigOperators ENNReal Matrix

-- @env: S3
variable (d n : ℕ) (β M : ℝ)
  -- @realizes d(covariate dimension) @realizes n(sample size)
  -- @realizes beta(polynomial order) @realizes M(clipping bound)

/-- Polynomial order `ceil β - 1`. -/
noncomputable def polynomialOrder (β : ℝ) : ℕ :=
  ⌈β⌉₊ - 1 -- @realizes m(ceil beta minus one)

/-- Tensor multi-index. Its cardinality is `R`. -/
abbrev MultiIndex (d m : ℕ) := Fin d → Fin (m + 1)

/-- Tensor monomial basis. -/
noncomputable def monomial (d m : ℕ) (u : Fin d → ℝ)
    (a : MultiIndex d m) : ℝ :=
  ∏ i : Fin d, (u i) ^ (a i).val -- @realizes v(tensor monomial coordinates)

/-- Interior tensor norming nodes. -/
noncomputable def normingNode (d m : ℕ) (a : MultiIndex d m) : Fin d → ℝ :=
  fun i => ((a i).val + 1 : ℕ) / ((m + 2 : ℕ) : ℝ)
  -- @realizes z(j/(m+2), j=1,...,m+1)

/-- Radius-`ε` norming cube at a tensor node. -/
def normingCube (d m : ℕ) (ε : ℝ) (a : MultiIndex d m) : Set (Fin d → ℝ) :=
  {u | ∀ i : Fin d, |u i - normingNode d m a i| ≤ ε}
  -- @realizes S(centered norming subcell)

/-- Reference Gram matrix. -/
noncomputable def referenceGram (d m : ℕ) :
    Matrix (MultiIndex d m) (MultiIndex d m) ℝ :=
  fun a b => (Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
    ∑ ℓ : MultiIndex d m,
      monomial d m (normingNode d m ℓ) a * monomial d m (normingNode d m ℓ) b
  -- @realizes G0(average outer product at norming nodes)

/-- Quadratic form of a real square matrix. -/
noncomputable def quadraticForm {ι : Type} [Fintype ι]
    (G : Matrix ι ι ℝ) (a : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * G i j * a j

/-- Least Rayleigh lower bound of the reference Gram matrix. -/
noncomputable def referenceLowerEigenvalue (d m : ℕ) : ℝ :=
  sSup {c : ℝ | ∀ a : MultiIndex d m → ℝ,
    c * (∑ i, (a i) ^ 2) ≤ quadraticForm (referenceGram d m) a}
  -- @realizes lambda0(minimal eigenvalue via quadratic form)

/-- Norming radius certificate, with disjoint interior cubes and the exact
operator-norm perturbation needed for the balanced Gram bound. -/
structure NormingSubcells (d m : ℕ) where
  radius : ℝ
  radius_pos : 0 < radius
  interior : ∀ a : MultiIndex d m, normingCube d m radius a ⊆
    Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) 1)
  disjoint : ∀ a b : MultiIndex d m, a ≠ b →
    Disjoint (normingCube d m radius a) (normingCube d m radius b)
  oscillation : ∀ ℓ : MultiIndex d m, ∀ u ∈ normingCube d m radius ℓ,
    ∀ a : MultiIndex d m → ℝ,
      |quadraticForm
        ((fun i j => monomial d m u i * monomial d m u j :
          Matrix (MultiIndex d m) (MultiIndex d m) ℝ) -
         (fun i j => monomial d m (normingNode d m ℓ) i *
           monomial d m (normingNode d m ℓ) j :
           Matrix (MultiIndex d m) (MultiIndex d m) ℝ)) a| ≤
        referenceLowerEigenvalue d m / 2 * (∑ i, (a i) ^ 2)
  -- @realizes S(disjoint interior norming cubes and Gram oscillation)

/-- A radius below one quarter of the tensor-node spacing keeps every
norming cube in the open unit cube. -/
-- @node: normingCube_interior
lemma normingCube_interior (d m : ℕ) {ε : ℝ}
    (hε : ε ≤ 1 / (4 * ((m : ℝ) + 2))) (a : MultiIndex d m) :
    normingCube d m ε a ⊆ Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) 1) := by
  intro u hu i _
  have habs := abs_le.mp (hu i)
  have hden : 0 < (m : ℝ) + 2 := by positivity
  have hlo : 1 / ((m : ℝ) + 2) ≤ normingNode d m a i := by
    unfold normingNode
    push_cast
    apply div_le_div_of_nonneg_right _ hden.le
    linarith [(Nat.cast_nonneg (a i).val : (0 : ℝ) ≤ (a i).val)]
  have hhi : normingNode d m a i ≤ ((m : ℝ) + 1) / ((m : ℝ) + 2) := by
    unfold normingNode
    push_cast
    apply div_le_div_of_nonneg_right _ hden.le
    have := (a i).isLt
    exact_mod_cast (by omega : (a i).val + 1 ≤ m + 1)
  have hquarter : 1 / (4 * ((m : ℝ) + 2)) = (1 / ((m : ℝ) + 2)) / 4 := by
    rw [div_div]; congr 1; ring
  have hsum : ((m : ℝ) + 1) / ((m : ℝ) + 2) + 1 / ((m : ℝ) + 2) = 1 := by
    field_simp
    ring
  have hpos : 0 < 1 / ((m : ℝ) + 2) := by positivity
  rw [hquarter] at hε
  constructor <;> linarith

/-- Distinct tensor nodes differ by at least one grid spacing in some
coordinate, so cubes of quarter-spacing radius are disjoint. -/
-- @node: normingCube_disjoint
lemma normingCube_disjoint (d m : ℕ) {ε : ℝ}
    (hε : ε ≤ 1 / (4 * ((m : ℝ) + 2))) (a b : MultiIndex d m) (hab : a ≠ b) :
    Disjoint (normingCube d m ε a) (normingCube d m ε b) := by
  classical
  apply Set.disjoint_left.mpr
  intro u hua hub
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
    by_contra h
    exact hab (funext (by simpa using h))
  have hden : 0 < (m : ℝ) + 2 := by positivity
  have ha := abs_le.mp (hua i)
  have hb := abs_le.mp (hub i)
  have hclose : |normingNode d m a i - normingNode d m b i| ≤ 2 * ε := by
    rw [abs_le]
    constructor <;> linarith
  have hsep : 1 / ((m : ℝ) + 2) ≤
      |normingNode d m a i - normingNode d m b i| := by
    simp only [normingNode, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    change 1 / ((m : ℝ) + 2) ≤
      |(((a i).val : ℝ) + 1) / ((m : ℝ) + 2) -
        (((b i).val : ℝ) + 1) / ((m : ℝ) + 2)|
    rw [← sub_div, abs_div, abs_of_pos hden]
    apply div_le_div_of_nonneg_right _ hden.le
    have hv : (a i).val ≠ (b i).val := fun h => hi (Fin.ext h)
    rcases lt_or_gt_of_ne hv with h | h
    · rw [abs_of_nonpos (by
        have hc : (a i).val + (1 : ℝ) ≤ (b i).val := by exact_mod_cast h
        linarith)]
      have hc : (a i).val + 1 ≤ (b i).val := by omega
      have hc' : (a i).val + (1 : ℝ) ≤ (b i).val := by exact_mod_cast hc
      linarith
    · rw [abs_of_nonneg (by
        have hc : (b i).val + (1 : ℝ) ≤ (a i).val := by exact_mod_cast h
        linarith)]
      have hc : (b i).val + 1 ≤ (a i).val := by omega
      have hc' : (b i).val + (1 : ℝ) ≤ (a i).val := by exact_mod_cast hc
      linarith
  have hquarter : 1 / (4 * ((m : ℝ) + 2)) = (1 / ((m : ℝ) + 2)) / 4 := by
    rw [div_div]; congr 1; ring
  have hpos : 0 < 1 / ((m : ℝ) + 2) := by positivity
  rw [hquarter] at hε
  linarith

/-- Continuity of the finite monomial outer product gives a uniform small
radius for the quadratic perturbation at every tensor node. -/
-- @node: normingCube_oscillation_radius
lemma normingCube_oscillation_radius (d m : ℕ) {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ℓ : MultiIndex d m,
      ∀ u ∈ normingCube d m ε ℓ, ∀ a : MultiIndex d m → ℝ,
        |quadraticForm
          ((fun i j => monomial d m u i * monomial d m u j :
            Matrix (MultiIndex d m) (MultiIndex d m) ℝ) -
           (fun i j => monomial d m (normingNode d m ℓ) i *
             monomial d m (normingNode d m ℓ) j)) a| ≤
          lambda / 2 * (∑ i, (a i) ^ 2) := by
  classical
  let F : (Fin d → ℝ) → MultiIndex d m → MultiIndex d m → ℝ :=
    fun u i j => monomial d m u i * monomial d m u j
  have hF : Continuous F := by
    dsimp [F, monomial]
    fun_prop
  have hcard : (0 : ℝ) < Fintype.card (MultiIndex d m) := by
    exact_mod_cast Fintype.card_pos
  let η : ℝ := lambda / (2 * Fintype.card (MultiIndex d m))
  have hη : 0 < η := by dsimp [η]; positivity
  have hex : ∀ ℓ : MultiIndex d m, ∃ δ : ℝ, 0 < δ ∧
      ∀ u : Fin d → ℝ, dist u (normingNode d m ℓ) < δ →
        dist (F u) (F (normingNode d m ℓ)) < η := by
    intro ℓ
    exact Metric.continuousAt_iff.mp hF.continuousAt η hη
  choose δ hδ hclose using hex
  let r : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
  have hr : 0 < r := by
    dsimp [r]
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (by intro ℓ _; exact hδ ℓ)
  refine ⟨r / 2, by positivity, ?_⟩
  intro ℓ u hu a
  have hrδ : r ≤ δ ℓ := Finset.inf'_le _ (Finset.mem_univ ℓ)
  have hudist : dist u (normingNode d m ℓ) ≤ r / 2 := by
    apply (dist_pi_le_iff (by positivity : 0 ≤ r / 2)).mpr
    intro i
    simpa only [Real.dist_eq] using hu i
  have hmat := hclose ℓ u (by linarith)
  have hentry : ∀ i j, |F u i j - F (normingNode d m ℓ) i j| ≤ η := by
    intro i j
    have hi := (dist_pi_lt_iff hη).mp hmat i
    have hj := (dist_pi_lt_iff hη).mp hi j
    exact le_of_lt (show |F u i j - F (normingNode d m ℓ) i j| < η from by
      simpa only [Real.dist_eq] using hj)
  have hquad := Causalean.Stat.Concentration.entrywise_to_quadratic
    (fun i j => F u i j - F (normingNode d m ℓ) i j) a hη.le hentry
  have heq : (Fintype.card (MultiIndex d m) : ℝ) * η = lambda / 2 := by
    dsimp [η]
    field_simp
  rw [heq] at hquad
  convert hquad using 1
  unfold quadraticForm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [F]
  ring

/-- Once the reference Gram has positive least eigenvalue, shrink the
continuity radius below the tensor spacing to obtain all norming certificates. -/
-- @node: exists_normingSubcells_of_pos
lemma exists_normingSubcells_of_pos (d m : ℕ)
    (hlambda : 0 < referenceLowerEigenvalue d m) : Nonempty (NormingSubcells d m) := by
  obtain ⟨r, hr, hosc⟩ := normingCube_oscillation_radius d m hlambda
  let ε : ℝ := min r (1 / (4 * ((m : ℝ) + 2)))
  have hε : 0 < ε := lt_min hr (by positivity)
  refine ⟨{
    radius := ε
    radius_pos := hε
    interior := normingCube_interior d m (min_le_right _ _)
    disjoint := normingCube_disjoint d m (min_le_right _ _)
    oscillation := ?_ }⟩
  intro ℓ u hu a
  apply hosc ℓ u _ a
  intro i
  exact (hu i).trans (min_le_left _ _)

/-- A left inverse in one coordinate tensorizes to a left inverse on the full finite grid. -/
-- @node: tensorMatrix_leftInverse
lemma tensorMatrix_leftInverse {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A B : Matrix κ κ ℝ) (hBA : B * A = 1) :
    (Matrix.of fun a b : ι → κ => ∏ i, B (a i) (b i)) *
      (Matrix.of fun a b : ι → κ => ∏ i, A (a i) (b i)) = 1 := by
  classical
  ext a b
  change (∑ c : ι → κ, (∏ i, B (a i) (c i)) * (∏ i, A (c i) (b i))) = _
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i j => B (a i) j * A j (b i))]
  have hentry (i : ι) : (∑ j, B (a i) j * A j (b i)) = if a i = b i then 1 else 0 := by
    exact congrFun (congrFun hBA (a i)) (b i)
  simp_rw [hentry]
  by_cases hab : a = b
  · subst b
    simp
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra h
      exact hab (funext (by simpa using h))
    rw [Matrix.one_apply, if_neg hab]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The distinct interior grid nodes give an invertible one-dimensional Vandermonde matrix;
tensorizing its inverse recovers every monomial coefficient. -/
-- @node: normingEvaluation_leftInverse
lemma normingEvaluation_leftInverse (d m : ℕ) :
    ∃ B : Matrix (MultiIndex d m) (MultiIndex d m) ℝ,
      B * (Matrix.of fun ℓ a => monomial d m (normingNode d m ℓ) a) = 1 := by
  classical
  let z : Fin (m + 1) → ℝ := fun k => ((k.val + 1 : ℕ) : ℝ) / (m + 2 : ℕ)
  let V := Matrix.vandermonde z
  have hz : Function.Injective z := by
    intro a b hab
    have hden : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have hv : ((a.val + 1 : ℕ) : ℝ) = ((b.val + 1 : ℕ) : ℝ) :=
      (div_left_inj' hden).mp hab
    apply Fin.ext
    have hv' : a.val + 1 = b.val + 1 := by exact_mod_cast hv
    omega
  have hdet : IsUnit V.det := isUnit_iff_ne_zero.mpr
    (Matrix.det_vandermonde_ne_zero_iff.mpr hz)
  refine ⟨Matrix.of (fun a b => ∏ i : Fin d, V⁻¹ (a i) (b i)), ?_⟩
  simpa only [monomial, normingNode, V, Matrix.vandermonde_apply, z] using
    (tensorMatrix_leftInverse (ι := Fin d) V V⁻¹ (Matrix.nonsing_inv_mul V hdet))

/-- Cauchy–Schwarz bounds coefficient energy by evaluation energy times the squared entries of
a left inverse. -/
-- @node: matrix_leftInverse_sum_sq_le
lemma matrix_leftInverse_sum_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hBA : B * A = 1) (a : ι → ℝ) :
    (∑ i, (a i) ^ 2) ≤ (∑ i, ∑ j, (B i j) ^ 2) * ∑ j, (A *ᵥ a) j ^ 2 := by
  have ha : B *ᵥ (A *ᵥ a) = a := by
    rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  calc
    _ = ∑ i, (∑ j, B i j * (A *ᵥ a) j) ^ 2 := by
      conv_lhs => rw [← ha]
      rfl
    _ ≤ ∑ i, (∑ j, (B i j) ^ 2) * ∑ j, (A *ᵥ a) j ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The reference Gram quadratic form is the average squared polynomial evaluation on the
tensor grid. -/
-- @node: referenceGram_quadraticForm
lemma referenceGram_quadraticForm (d m : ℕ) (a : MultiIndex d m → ℝ) :
    quadraticForm (referenceGram d m) a =
      (Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
        ∑ ℓ : MultiIndex d m, (∑ i, monomial d m (normingNode d m ℓ) i * a i) ^ 2 := by
  classical
  unfold quadraticForm referenceGram
  simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ ℓ, ∑ j, a i *
        ((Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
          (monomial d m (normingNode d m ℓ) i * monomial d m (normingNode d m ℓ) j)) * a j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ ℓ, ∑ i, ∑ j, a i *
        ((Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
          (monomial d m (normingNode d m ℓ) i * monomial d m (normingNode d m ℓ) j)) * a j := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ℓ _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Tensor-grid unisolvence and Cauchy–Schwarz supply a strictly positive uniform Rayleigh
lower bound. -/
-- @node: referenceGram_coercive
lemma referenceGram_coercive (d m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : MultiIndex d m → ℝ,
      c * (∑ i, (a i) ^ 2) ≤ quadraticForm (referenceGram d m) a := by
  classical
  obtain ⟨B, hB⟩ := normingEvaluation_leftInverse d m
  let T : ℝ := (∑ i, ∑ j, (B i j) ^ 2) + 1
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hcard : (0 : ℝ) < Fintype.card (MultiIndex d m) := by
    exact_mod_cast Fintype.card_pos
  refine ⟨(Fintype.card (MultiIndex d m) : ℝ)⁻¹ / T, by positivity, ?_⟩
  intro a
  let A : Matrix (MultiIndex d m) (MultiIndex d m) ℝ :=
    Matrix.of fun ℓ i => monomial d m (normingNode d m ℓ) i
  have hnorm := matrix_leftInverse_sum_sq_le A B hB a
  have hsum : 0 ≤ ∑ j, (A *ᵥ a) j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hnorm' : (∑ i, (a i) ^ 2) ≤ T * ∑ j, (A *ᵥ a) j ^ 2 := by
    dsimp [T]
    nlinarith
  have hdiv : (∑ i, (a i) ^ 2) / T ≤ ∑ j, (A *ᵥ a) j ^ 2 :=
    (div_le_iff₀ hT).mpr (by simpa only [mul_comm] using hnorm')
  rw [referenceGram_quadraticForm]
  have h := mul_le_mul_of_nonneg_left hdiv (inv_nonneg.mpr hcard.le)
  simpa only [div_mul_eq_mul_div, mul_div_assoc, Matrix.mulVec, dotProduct, A,
    Matrix.of_apply] using h

/-- The Rayleigh lower bounds form a bounded-above set containing a positive coercivity
constant, so their supremum is positive. -/
-- @node: referenceLowerEigenvalue_pos
lemma referenceLowerEigenvalue_pos (d m : ℕ) : 0 < referenceLowerEigenvalue d m := by
  classical
  obtain ⟨c, hc, hcoercive⟩ := referenceGram_coercive d m
  have hbdd : BddAbove {r : ℝ | ∀ a : MultiIndex d m → ℝ,
      r * (∑ i, (a i) ^ 2) ≤ quadraticForm (referenceGram d m) a} := by
    let i₀ : MultiIndex d m := fun _ => 0
    refine ⟨referenceGram d m i₀ i₀, ?_⟩
    intro r hr
    have h := hr (Pi.single i₀ 1)
    simpa [quadraticForm, Pi.single_apply, mul_ite, ite_mul] using h
  exact hc.trans_le (le_csSup hbdd hcoercive)

/-- Existence of a small enough norming radius follows from tensor-grid
unisolvence and continuity of the monomial outer product. -/
-- @node: exists_normingSubcells
lemma exists_normingSubcells (d m : ℕ) : Nonempty (NormingSubcells d m) := by
  apply exists_normingSubcells_of_pos d m
  exact referenceLowerEigenvalue_pos d m

-- @node: def:norming-subcells
/-- The radius supplier is `exists_normingSubcells`. Its classical witness is
chosen once for each `(d, β)` and shared by all cells, scales, and estimators. -/
noncomputable def normingSubcells (d : ℕ) (β : ℝ) :
    NormingSubcells d (polynomialOrder β) :=
  Classical.choice (exists_normingSubcells d (polynomialOrder β))

/-- Dyadic width and deterministic half-open cell ownership. -/
noncomputable def dyadicWidth (j : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ j) -- @realizes h(dyadic width)

noncomputable def cellIndex (d j : ℕ) (x : Fin d → ℝ) : Fin d → Fin (2 ^ j) :=
  fun i => ⟨min (Nat.floor (((2 : ℝ) ^ j) * x i)) (2 ^ j - 1), by
    have hp : 0 < 2 ^ j := by positivity
    omega⟩

/-- Cell origin and its scaled norming subcell. -/
noncomputable def cellOrigin (d j : ℕ) (Q : Fin d → Fin (2 ^ j)) : Fin d → ℝ :=
  fun i => (Q i : ℕ) * dyadicWidth j

def dyadicCell (d j : ℕ) (Q : Fin d → Fin (2 ^ j)) : Set (Fin d → ℝ) :=
  {x | cellIndex d j x = Q} -- @realizes Q(half-open dyadic cell ownership)

noncomputable def scaledSubcell (d j m : ℕ) (ε : ℝ)
    (Q : Fin d → Fin (2 ^ j)) (ℓ : MultiIndex d m) : Set (Fin d → ℝ) :=
  {x | x ∈ dyadicCell d j Q ∧
    (fun i => (x i - cellOrigin d j Q i) / dyadicWidth j) ∈
      normingCube d m ε ℓ}
  -- @realizes Qell(origin plus width times norming subcell)

/-- Number of sampled units of a selected arm in a norming subcell. -/
noncomputable def subcellCount {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ)
    (Q : Fin d → Fin (2 ^ j)) (ℓ : MultiIndex d m) : ℕ :=
  by
    classical
    exact ∑ i : Fin n,
      if (sample i).2.1 = arm ∧
        (sample i).1 ∈ scaledSubcell d j m ε Q ℓ then 1 else 0
  -- @realizes NQell(arm-specific count in scaled norming subcell)

/-- Minimum of all norming subcell counts. -/
noncomputable def minimumCellCount {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j)) : ℕ :=
  Finset.univ.inf' (by simp : (Finset.univ : Finset (MultiIndex d m)).Nonempty)
    (fun ℓ => subcellCount sample arm j m ε Q ℓ)
  -- @realizes NQ(minimum norming-subcell count)

/-- Arm-specific balanced empirical Gram matrix. -/
noncomputable def balancedGram {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ)
    (Q : Fin d → Fin (2 ^ j)) : Matrix (MultiIndex d m) (MultiIndex d m) ℝ :=
  by
    classical
    exact fun a b => (Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
      ∑ ℓ : MultiIndex d m,
        (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹ *
        ∑ i : Fin n,
          if (sample i).2.1 = arm ∧
              (sample i).1 ∈ scaledSubcell d j m ε Q ℓ then
            monomial d m (fun k => ((sample i).1 k - cellOrigin d j Q k) /
              dyadicWidth j) a *
            monomial d m (fun k => ((sample i).1 k - cellOrigin d j Q k) /
              dyadicWidth j) b
          else 0
  -- @realizes GQ(equal total weight per occupied norming subcell)

/-- Arm-specific balanced outcome moment. -/
noncomputable def balancedMoment {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ)
    (Q : Fin d → Fin (2 ^ j)) : MultiIndex d m → ℝ :=
  by
    classical
    exact fun a => (Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
      ∑ ℓ : MultiIndex d m,
        (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹ *
        ∑ i : Fin n,
          if (sample i).2.1 = arm ∧
              (sample i).1 ∈ scaledSubcell d j m ε Q ℓ then
            monomial d m (fun k => ((sample i).1 k - cellOrigin d j Q k) /
              dyadicWidth j) a * (sample i).2.2
          else 0

/-- Total arm-specific fit with zero fallback and clipping. -/
noncomputable def armBalancedEstimator {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j : ℕ) (β M : ℝ) (x : Fin d → ℝ) : ℝ :=
  let m := polynomialOrder β
  let ε := (normingSubcells d β).radius
  let Q := cellIndex d j x
  if minimumCellCount sample arm j m ε Q = 0 then 0 else
    let G := balancedGram sample arm j m ε Q
    let b := balancedMoment sample arm j m ε Q
    let θ := G⁻¹ *ᵥ b
    max (-M) (min M
      (∑ a : MultiIndex d m,
        monomial d m (fun k => (x k - cellOrigin d j Q k) / dyadicWidth j) a * θ a))

-- @node: def:balanced-estimator
/-- Treated balanced-subcell estimator using the radius fixed by
`normingSubcells d β` for the entire construction. -/
noncomputable def balancedEstimator {d n : ℕ} (sample : Fin n → Obs d)
    (j : ℕ) (β M : ℝ) (x : Fin d → ℝ) : ℝ :=
  armBalancedEstimator sample true j β M x -- @realizes muhat(treated fit)

-- @node: def:control-balanced-estimator
/-- Control balanced-subcell estimator. -/
noncomputable def controlBalancedEstimator {d n : ℕ} (sample : Fin n → Obs d)
    (j : ℕ) (β M : ℝ) (x : Fin d → ℝ) : ℝ :=
  armBalancedEstimator sample false j β M x -- @realizes muhat0(control fit)

/-- Balanced CATE curve. -/
noncomputable def cateEstimator {d n : ℕ} (sample : Fin n → Obs d)
    (j : ℕ) (β M : ℝ) (x : Fin d → ℝ) : ℝ :=
  balancedEstimator sample j β M x - controlBalancedEstimator sample j β M x
  -- @realizes tauhat(treated fit minus control fit)

end CausalSmith.Stat.GlobalTailDesignRobustCate
