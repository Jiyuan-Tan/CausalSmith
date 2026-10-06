module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Basic
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Nat.Log
public import Mathlib.Probability.Moments.Variance

/-!
Uniform histogram projections, orthogonal outcome bands and known-design cell averaging.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- A positive power-of-two rank. -/
def Dyadic (k : ℕ) : Prop := ∃ l : ℕ, k = 2 ^ l

-- @env: S3
variable (j k L T J : ℕ)

/-- Generic scalar square-integrable outcome tests, with no histogram restriction. -/
abbrev ScalarTestFunction := Lp ℝ 2 unitVolume -- @realizes f(generic scalar L2 test)

/-- Generic finite-dimensional Hilbert-valued square-integrable outcome tests. -/
abbrev HilbertTestFunction (d : ℕ) := Lp (EuclideanSpace ℝ (Fin d)) 2 unitVolume
  -- @realizes f(generic finite-dimensional Hilbert-valued L2 test)

/-- One-based uniform cell map, including the right endpoint in the last cell. -/
def cell (k : ℕ) (x : ℝ) : ℕ :=
  min k (1 + ⌊(k : ℝ) * x⌋₊) -- @realizes cell(min(k,1+floor(kx))) @realizes k(natural cell rank)

/-- Cell restricted to the unit interval. -/
def histogramCell (k l : ℕ) : Set ℝ :=
  {x | x ∈ Set.Icc 0 1 ∧ cell k x = l} -- @realizes ell(one-based bin index)

/-- Outcome projection representer as a function of its second outcome argument. -/
def Phi (j : ℕ) (y yp : ℝ) : ℝ :=
  if cell j yp = cell j y then j else 0 -- @realizes Phi(j times same-cell indicator)

/-- Lebesgue histogram projection of a representative. -/
def outcomeProjection (j : ℕ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  (j : ℝ) * ∫ yp in histogramCell j (cell j y), f yp ∂unitVolume
    -- @realizes Pi(cell average) @realizes j(outcome rank)

/-- Coefficients in the orthonormal rank-J histogram basis. -/
abbrev Hj (J : ℕ) := EuclideanSpace ℝ (Fin J) -- @realizes Hj(orthonormal histogram coefficients)

/-- Midpoint of a histogram cell. -/
def midpoint (J : ℕ) (i : Fin J) : ℝ := ((i : ℝ) + 1 / 2) / J

/-- Function represented by orthonormal histogram coefficients. -/
def histogramFunction {J : ℕ} (f : Hj J) (y : ℝ) : ℝ :=
  ∑ i : Fin J, if cell J y = i.val + 1 then Real.sqrt J * f i else 0

/-- Projection coefficients of an outcome function. -/
def coefficients (J : ℕ) (f : ℝ → ℝ) : Hj J :=
  WithLp.toLp 2 (fun i => Real.sqrt J * ∫ y in histogramCell J (i.val + 1), f y ∂unitVolume)

/-- Coefficient form of the outcome representer. -/
def phiCoefficients (J : ℕ) (y : ℝ) : Hj J :=
  WithLp.toLp 2 (fun i => if cell J y = i.val + 1 then Real.sqrt J else 0)

/-- Coarse projection on final-rank orthonormal coefficients. -/
def coefficientProjection (j J : ℕ) (f : Hj J) : Hj J :=
  WithLp.toLp 2 (fun i => (j : ℝ) / J * 
    ∑ l : Fin J, if cell j (midpoint J l) = cell j (midpoint J i) then f l else 0)

/-- Band zero is Pi_L; positive bands are consecutive dyadic differences. -/
def Qband (L J t : ℕ) (f : Hj J) : Hj J :=
  if t = 0 then coefficientProjection L J f else
    coefficientProjection (2 ^ t * L) J f - coefficientProjection (2 ^ (t - 1) * L) J f
    -- @realizes Qband(Pi_L or Pi_(2^t L)-Pi_(2^(t-1)L)) @realizes t(band index)

/-- Dimension of a dyadic outcome band. -/
def bandDimension (L t : ℕ) : ℕ :=
  if t = 0 then L else 2 ^ (t - 1) * L -- @realizes dt(L or 2^(t-1)L)

/-- Known-design covariate histogram kernel. -/
def covariateKernel (k : ℕ) (x xp : ℝ) : ℝ :=
  if cell k x = cell k xp then k else 0 -- @realizes Kern(k times same-cell indicator)

/-- Covariate cell averaging, for scalar or vector functions. -/
def cellAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (f : ℝ → E) (x : ℝ) : E :=
  ∫ xp, covariateKernel k x xp • f xp ∂unitVolume -- @realizes Ecell(integral kernel averaging)

/-- A final-rank midpoint has exactly its own one-based cell label. -/
-- @node: cell_midpoint_self
lemma cell_midpoint_self (J : ℕ) (i : Fin J) :
    cell J (midpoint J i) = i.val + 1 := by
  have hJ : (0 : ℝ) < J := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hm : (J : ℝ) * midpoint J i = (i.val : ℝ) + 1 / 2 := by
    dsimp [midpoint]
    field_simp
  have hf : ⌊(J : ℝ) * midpoint J i⌋₊ = i.val := by
    rw [hm]
    apply (Nat.floor_eq_iff (by positivity)).2
    constructor <;> linarith
  simp only [cell, hf]
  omega

/-- The finest coefficient projection is the identity, since its fibers are singletons. -/
-- @node: coefficientProjection_self
lemma coefficientProjection_self (J : ℕ) (f : Hj J) :
    coefficientProjection J J f = f := by
  classical
  ext i
  have hJ : (J : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  have he (l : Fin J) : cell J (midpoint J l) = cell J (midpoint J i) ↔ l = i := by
    rw [cell_midpoint_self, cell_midpoint_self]
    constructor
    · intro h; apply Fin.ext; omega
    · rintro rfl; rfl
  change (J : ℝ) / J * (∑ l : Fin J,
    if cell J (midpoint J l) = cell J (midpoint J i) then f l else 0) = f i
  simp [he, hJ]

/-- Coarse coefficient averaging commutes with addition. -/
-- @node: coefficientProjection_add
lemma coefficientProjection_add (j J : ℕ) (f g : Hj J) :
    coefficientProjection j J (f + g) =
      coefficientProjection j J f + coefficientProjection j J g := by
  classical
  ext i
  change (j : ℝ) / J * (∑ l : Fin J,
      if cell j (midpoint J l) = cell j (midpoint J i) then f l + g l else 0) = _
  change (j : ℝ) / J * (∑ l : Fin J,
      if cell j (midpoint J l) = cell j (midpoint J i) then f l + g l else 0) =
    (j : ℝ) / J * (∑ l : Fin J,
      if cell j (midpoint J l) = cell j (midpoint J i) then f l else 0) +
    (j : ℝ) / J * (∑ l : Fin J,
      if cell j (midpoint J l) = cell j (midpoint J i) then g l else 0)
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp

/-- Coarse coefficient averaging commutes with real scaling. -/
-- @node: coefficientProjection_smul
lemma coefficientProjection_smul (j J : ℕ) (c : ℝ) (f : Hj J) :
    coefficientProjection j J (c • f) = c • coefficientProjection j J f := by
  classical
  ext i
  change (j : ℝ) / J * (∑ l : Fin J,
      if cell j (midpoint J l) = cell j (midpoint J i) then c * f l else 0) =
    c * ((j : ℝ) / J * (∑ l : Fin J,
      if cell j (midpoint J l) = cell j (midpoint J i) then f l else 0))
  have he (l : Fin J) :
      (if cell j (midpoint J l) = cell j (midpoint J i) then c * f l else 0) =
      c * (if cell j (midpoint J l) = cell j (midpoint J i) then f l else 0) := by
    split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.mul_sum]
  ring

/-- Coarse coefficient averaging commutes with subtraction. -/
-- @node: coefficientProjection_sub
lemma coefficientProjection_sub (j J : ℕ) (f g : Hj J) :
    coefficientProjection j J (f - g) =
      coefficientProjection j J f - coefficientProjection j J g := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ g, coefficientProjection_add,
    coefficientProjection_smul, neg_one_smul, ← sub_eq_add_neg]

/-- Every band is additive, including the initial coarse band. -/
-- @node: Qband_add
lemma Qband_add (L J t : ℕ) (f g : Hj J) :
    Qband L J t (f + g) = Qband L J t f + Qband L J t g := by
  unfold Qband
  split_ifs
  · exact coefficientProjection_add L J f g
  · rw [coefficientProjection_add, coefficientProjection_add]
    abel

/-- Every band commutes with real scaling. -/
-- @node: Qband_smul
lemma Qband_smul (L J t : ℕ) (c : ℝ) (f : Hj J) :
    Qband L J t (c • f) = c • Qband L J t f := by
  unfold Qband
  split_ifs
  · exact coefficientProjection_smul L J c f
  · rw [coefficientProjection_smul, coefficientProjection_smul, smul_sub]

/-- Band projections commute with differences of coefficient vectors. -/
-- @node: Qband_sub
lemma Qband_sub (L J t : ℕ) (f g : Hj J) :
    Qband L J t (f - g) = Qband L J t f - Qband L J t g := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ g, Qband_add,
    Qband_smul, neg_one_smul, ← sub_eq_add_neg]

/-- The coefficient averaging matrix is symmetric: two midpoints share a cell symmetrically. -/
-- @node: coefficientProjection_inner
lemma coefficientProjection_inner (j J : ℕ) (f g : Hj J) :
    inner ℝ (coefficientProjection j J f) g =
      inner ℝ f (coefficientProjection j J g) := by
  classical
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ i : Fin J, g i * ((j : ℝ) / J * (∑ l : Fin J,
      if cell j (midpoint J l) = cell j (midpoint J i) then f l else 0))) =
    ∑ l : Fin J, ((j : ℝ) / J * (∑ i : Fin J,
      if cell j (midpoint J i) = cell j (midpoint J l) then g i else 0)) * f l
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : cell j (midpoint J l) = cell j (midpoint J i)
  · simp only [if_pos h, if_pos h.symm]
    ring
  · simp only [if_neg h, if_neg (Ne.symm h), mul_zero, zero_mul]

/-- Consecutive differences of symmetric coarse projections are symmetric too. -/
-- @node: Qband_inner
lemma Qband_inner (L J t : ℕ) (f g : Hj J) :
    inner ℝ (Qband L J t f) g = inner ℝ f (Qband L J t g) := by
  unfold Qband
  split_ifs
  · exact coefficientProjection_inner L J f g
  · rw [inner_sub_left, inner_sub_right,
      coefficientProjection_inner, coefficientProjection_inner]

/-- The sum of consecutive bands telescopes to its last coarse projection. -/
-- @node: sum_Qband_eq_projection
lemma sum_Qband_eq_projection (L J T : ℕ) (f : Hj J) :
    ∑ t ∈ Finset.range (T + 1), Qband L J t f =
      coefficientProjection (2 ^ T * L) J f := by
  induction T with
  | zero => simp [Qband]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Qband, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    abel

/-- At the terminal rank the band decomposition recovers the entire coefficient vector. -/
-- @node: sum_Qband_eq_self
lemma sum_Qband_eq_self (L T : ℕ) (f : Hj (2 ^ T * L)) :
    ∑ t ∈ Finset.range (T + 1), Qband L (2 ^ T * L) t f = f := by
  rw [sum_Qband_eq_projection, coefficientProjection_self]

/-- Coarse averaging gives identical coefficients at midpoints in the same coarse cell. -/
-- @node: coefficientProjection_eq_of_cell_eq
lemma coefficientProjection_eq_of_cell_eq (j J : ℕ) (f : Hj J) (i l : Fin J)
    (h : cell j (midpoint J i) = cell j (midpoint J l)) :
    coefficientProjection j J f i = coefficientProjection j J f l := by
  change (j : ℝ) / J * (∑ r : Fin J,
    if cell j (midpoint J r) = cell j (midpoint J i) then f r else 0) = _
  simp only [h]
  rfl

/-- Exact reciprocal fiber sizes make coarse coefficient averaging idempotent. -/
-- @node: coefficientProjection_idempotent_of_fiber_mass
lemma coefficientProjection_idempotent_of_fiber_mass (j J : ℕ)
    (hfiber : ∀ i : Fin J, (j : ℝ) / J *
      ((Finset.univ.filter (fun l : Fin J =>
        cell j (midpoint J l) = cell j (midpoint J i))).card : ℝ) = 1)
    (f : Hj J) :
    coefficientProjection j J (coefficientProjection j J f) = coefficientProjection j J f := by
  classical
  ext i
  change (j : ℝ) / J * (∑ l : Fin J,
    if cell j (midpoint J l) = cell j (midpoint J i)
      then coefficientProjection j J f l else 0) = coefficientProjection j J f i
  have he : (∑ l : Fin J,
      if cell j (midpoint J l) = cell j (midpoint J i)
        then coefficientProjection j J f l else 0) =
      ∑ l ∈ Finset.univ.filter (fun l : Fin J =>
        cell j (midpoint J l) = cell j (midpoint J i)), coefficientProjection j J f i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs with h
    · exact coefficientProjection_eq_of_cell_eq j J f l i h
    · rfl
  rw [he, Finset.sum_const, nsmul_eq_mul, ← mul_assoc, hfiber i, one_mul]

/-- Symmetry and idempotence identify pairing with a projection as its squared norm. -/
-- @node: coefficientProjection_inner_self_of_idempotent
lemma coefficientProjection_inner_self_of_idempotent (j J : ℕ) (f : Hj J)
    (hid : coefficientProjection j J (coefficientProjection j J f) = coefficientProjection j J f) :
    inner ℝ f (coefficientProjection j J f) = ‖coefficientProjection j J f‖ ^ 2 := by
  rw [← hid, ← coefficientProjection_inner, hid, real_inner_self_eq_norm_sq]

/-- The projection residual is orthogonal to every projected coefficient vector. -/
-- @node: coefficientProjection_residual_inner_of_idempotent
lemma coefficientProjection_residual_inner_of_idempotent (j J : ℕ) (f g : Hj J)
    (hid : coefficientProjection j J (coefficientProjection j J g) = coefficientProjection j J g) :
    inner ℝ (f - coefficientProjection j J f) (coefficientProjection j J g) = 0 := by
  rw [inner_sub_left, coefficientProjection_inner, hid, sub_self]

/-- The squared norm splits into the projection and its residual once averaging is idempotent. -/
-- @node: coefficientProjection_norm_sq_decomposition
lemma coefficientProjection_norm_sq_decomposition (j J : ℕ) (f : Hj J)
    (hid : coefficientProjection j J (coefficientProjection j J f) = coefficientProjection j J f) :
    ‖f‖ ^ 2 = ‖coefficientProjection j J f‖ ^ 2 + ‖f - coefficientProjection j J f‖ ^ 2 := by
  rw [norm_sub_sq_real, coefficientProjection_inner_self_of_idempotent j J f hid]
  ring

/-- An idempotent coarse coefficient average cannot increase the Euclidean norm. -/
-- @node: coefficientProjection_norm_le_of_idempotent
lemma coefficientProjection_norm_le_of_idempotent (j J : ℕ) (f : Hj J)
    (hid : coefficientProjection j J (coefficientProjection j J f) = coefficientProjection j J f) :
    ‖coefficientProjection j J f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  have h := coefficientProjection_norm_sq_decomposition j J f hid
  nlinarith [sq_nonneg ‖f - coefficientProjection j J f‖]

/-- Exact reciprocal midpoint-fiber sizes imply contraction of the concrete coarse average. -/
-- @node: coefficientProjection_norm_le_of_fiber_mass
lemma coefficientProjection_norm_le_of_fiber_mass (j J : ℕ)
    (hfiber : ∀ i : Fin J, (j : ℝ) / J *
      ((Finset.univ.filter (fun l : Fin J =>
        cell j (midpoint J l) = cell j (midpoint J i))).card : ℝ) = 1)
    (f : Hj J) : ‖coefficientProjection j J f‖ ≤ ‖f‖ := by
  exact coefficientProjection_norm_le_of_idempotent j J f
    (coefficientProjection_idempotent_of_fiber_mass j J hfiber f)

/-- Two-sided nesting of consecutive coarse averages makes their difference idempotent. -/
-- @node: Qband_idempotent_of_nested
lemma Qband_idempotent_of_nested (L J t : ℕ) (ht : t ≠ 0)
    (hhi : ∀ f : Hj J, coefficientProjection (2 ^ t * L) J
      (coefficientProjection (2 ^ t * L) J f) = coefficientProjection (2 ^ t * L) J f)
    (hlo : ∀ f : Hj J, coefficientProjection (2 ^ (t - 1) * L) J
      (coefficientProjection (2 ^ (t - 1) * L) J f) =
      coefficientProjection (2 ^ (t - 1) * L) J f)
    (hhl : ∀ f : Hj J, coefficientProjection (2 ^ t * L) J
      (coefficientProjection (2 ^ (t - 1) * L) J f) =
      coefficientProjection (2 ^ (t - 1) * L) J f)
    (hlh : ∀ f : Hj J, coefficientProjection (2 ^ (t - 1) * L) J
      (coefficientProjection (2 ^ t * L) J f) =
      coefficientProjection (2 ^ (t - 1) * L) J f)
    (f : Hj J) : Qband L J t (Qband L J t f) = Qband L J t f := by
  simp only [Qband, if_neg ht, coefficientProjection_sub, hhi, hlo, hhl, hlh]
  abel

/-- Symmetric idempotent histogram bands are contractive. -/
-- @node: Qband_norm_le_of_idempotent
lemma Qband_norm_le_of_idempotent (L J t : ℕ) (f : Hj J)
    (hid : Qband L J t (Qband L J t f) = Qband L J t f) :
    ‖Qband L J t f‖ ≤ ‖f‖ := by
  have hinner : inner ℝ f (Qband L J t f) = ‖Qband L J t f‖ ^ 2 := by
    rw [← hid, ← Qband_inner, hid, real_inner_self_eq_norm_sq]
  have hsq := norm_sub_sq_real f (Qband L J t f)
  rw [hinner] at hsq
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  nlinarith [sq_nonneg ‖f - Qband L J t f‖]

/-- Annihilation between two bands makes all vectors in their images orthogonal. -/
-- @node: Qband_inner_eq_zero_of_annihilation
lemma Qband_inner_eq_zero_of_annihilation (L J s t : ℕ) (f g : Hj J)
    (hzero : Qband L J s (Qband L J t g) = 0) :
    inner ℝ (Qband L J s f) (Qband L J t g) = 0 := by
  rw [Qband_inner, hzero, inner_zero_right]

/-- At a rank dividing the final rank, midpoint labels are integer quotient blocks. -/
-- @node: cell_midpoint_mul
lemma cell_midpoint_mul (j r : ℕ) (hj : 0 < j) (hr : 0 < r)
    (i : Fin (j * r)) : cell j (midpoint (j * r) i) = i.val / r + 1 := by
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hm : (j : ℝ) * midpoint (j * r) i = ((i.val : ℝ) + 1 / 2) / r := by
    dsimp [midpoint]
    push_cast
    field_simp
  have hf : ⌊(i.val : ℝ) + 1 / 2⌋₊ = i.val := by
    apply (Nat.floor_eq_iff (by positivity)).2
    constructor <;> linarith
  have hlt : i.val / r < j := (Nat.div_lt_iff_lt_mul hr).2 (by simpa [Nat.mul_comm] using i.isLt)
  simp only [cell, hm, Nat.floor_div_natCast, hf]
  omega

/-- The midpoints in one coarse cell are exactly those with the same quotient block. -/
-- @node: cell_midpoint_mul_eq_iff
lemma cell_midpoint_mul_eq_iff (j r : ℕ) (hj : 0 < j) (hr : 0 < r)
    (i l : Fin (j * r)) :
    cell j (midpoint (j * r) l) = cell j (midpoint (j * r) i) ↔
      l.val / r = i.val / r := by
  rw [cell_midpoint_mul j r hj hr, cell_midpoint_mul j r hj hr]
  omega

/-- Every coarse midpoint fiber contains exactly the refinement factor many indices. -/
-- @node: midpoint_fiber_card_mul
lemma midpoint_fiber_card_mul (j r : ℕ) (hj : 0 < j) (hr : 0 < r)
    (i : Fin (j * r)) :
    (Finset.univ.filter (fun l : Fin (j * r) =>
      cell j (midpoint (j * r) l) = cell j (midpoint (j * r) i))).card = r := by
  classical
  have hq : i.val / r < j := (Nat.div_lt_iff_lt_mul hr).2
    (by simpa [Nat.mul_comm] using i.isLt)
  let f : Fin r → Fin (j * r) := fun u =>
    ⟨i.val / r * r + u.val, by
      have h := Nat.mul_le_mul_right r (Nat.succ_le_of_lt hq)
      have hu := u.isLt
      nlinarith⟩
  have hf (u : Fin r) : (f u).val / r = i.val / r := by
    dsimp [f]
    simp [Nat.add_div, Nat.mod_eq_of_lt u.isLt,
      Nat.div_eq_of_lt u.isLt, hr, Nat.ne_of_gt hr, Nat.not_le_of_gt u.isLt]
  have hinj : Function.Injective f := by
    intro u v h
    have hv := congrArg Fin.val h
    dsimp [f] at hv
    apply Fin.ext
    omega
  have he : Finset.univ.filter (fun l : Fin (j * r) =>
      cell j (midpoint (j * r) l) = cell j (midpoint (j * r) i)) =
      Finset.univ.image f := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      cell_midpoint_mul_eq_iff j r hj hr, Finset.mem_image]
    constructor
    · intro hl
      refine ⟨⟨l.val % r, Nat.mod_lt _ hr⟩, ?_⟩
      apply Fin.ext
      dsimp [f]
      rw [← hl, Nat.mul_comm (l.val / r) r, Nat.div_add_mod]
    · rintro ⟨u, rfl⟩
      exact hf u
  rw [he, Finset.card_image_of_injective _ hinj]
  simp

/-- The coarse normalization is the reciprocal of its concrete midpoint fiber size. -/
-- @node: midpoint_fiber_mass_mul
lemma midpoint_fiber_mass_mul (j r : ℕ) (hj : 0 < j) (hr : 0 < r)
    (i : Fin (j * r)) :
    (j : ℝ) / (j * r) *
      ((Finset.univ.filter (fun l : Fin (j * r) =>
        cell j (midpoint (j * r) l) = cell j (midpoint (j * r) i))).card : ℝ) = 1 := by
  rw [midpoint_fiber_card_mul j r hj hr i]
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  field_simp

/-- Concrete coarse histogram projections at divisor ranks are idempotent. -/
-- @node: coefficientProjection_idempotent_mul
lemma coefficientProjection_idempotent_mul (j r : ℕ) (hj : 0 < j) (hr : 0 < r)
    (f : Hj (j * r)) :
    coefficientProjection j (j * r) (coefficientProjection j (j * r) f) =
      coefficientProjection j (j * r) f := by
  exact coefficientProjection_idempotent_of_fiber_mass j (j * r)
    (by simpa only [Nat.cast_mul] using midpoint_fiber_mass_mul j r hj hr) f

/-- Concrete coarse histogram projections at divisor ranks contract the norm. -/
-- @node: coefficientProjection_norm_le_mul
lemma coefficientProjection_norm_le_mul (j r : ℕ) (hj : 0 < j) (hr : 0 < r)
    (f : Hj (j * r)) : ‖coefficientProjection j (j * r) f‖ ≤ ‖f‖ := by
  exact coefficientProjection_norm_le_of_idempotent j (j * r) f
    (coefficientProjection_idempotent_mul j r hj hr f)

/-- Refining a midpoint cell preserves its enclosing coarse cell. -/
-- @node: midpoint_cell_refinement
lemma midpoint_cell_refinement (j s r : ℕ) (hj : 0 < j) (hs : 0 < s) (hr : 0 < r)
    (i l : Fin ((j * s) * r))
    (h : cell (j * s) (midpoint ((j * s) * r) l) =
      cell (j * s) (midpoint ((j * s) * r) i)) :
    cell j (midpoint ((j * s) * r) l) = cell j (midpoint ((j * s) * r) i) := by
  have hq := (cell_midpoint_mul_eq_iff (j * s) r (Nat.mul_pos hj hs) hr i l).1 h
  have he (v : Fin ((j * s) * r)) :
      cell j (midpoint ((j * s) * r) v) = v.val / (s * r) + 1 := by
    simpa only [midpoint, Fin.val_mk, Nat.mul_assoc] using
      cell_midpoint_mul j (s * r) hj (Nat.mul_pos hs hr)
        (⟨v.val, by simpa only [Nat.mul_assoc] using v.isLt⟩ : Fin (j * (s * r)))
  rw [he l, he i, Nat.mul_comm s r, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul, hq]

/-- A refined concrete projection fixes every vector already averaged at the coarse rank. -/
-- @node: coefficientProjection_fine_coarse_mul
lemma coefficientProjection_fine_coarse_mul (j s r : ℕ)
    (hj : 0 < j) (hs : 0 < s) (hr : 0 < r) (f : Hj ((j * s) * r)) :
    coefficientProjection (j * s) ((j * s) * r)
      (coefficientProjection j ((j * s) * r) f) =
      coefficientProjection j ((j * s) * r) f := by
  classical
  ext i
  change ((j * s : ℕ) : ℝ) / ((j * s) * r : ℕ) *
    (∑ l : Fin ((j * s) * r),
      if cell (j * s) (midpoint ((j * s) * r) l) =
        cell (j * s) (midpoint ((j * s) * r) i)
      then coefficientProjection j ((j * s) * r) f l else 0) = _
  have he : (∑ l : Fin ((j * s) * r),
      if cell (j * s) (midpoint ((j * s) * r) l) =
        cell (j * s) (midpoint ((j * s) * r) i)
      then coefficientProjection j ((j * s) * r) f l else 0) =
      ∑ l ∈ Finset.univ.filter (fun l : Fin ((j * s) * r) =>
        cell (j * s) (midpoint ((j * s) * r) l) =
          cell (j * s) (midpoint ((j * s) * r) i)),
        coefficientProjection j ((j * s) * r) f i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs with h
    · exact coefficientProjection_eq_of_cell_eq j ((j * s) * r) f l i
        (midpoint_cell_refinement j s r hj hs hr i l h)
    · rfl
  rw [he, Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
  have hmass := midpoint_fiber_mass_mul (j * s) r (Nat.mul_pos hj hs) hr i
  push_cast at hmass ⊢
  rw [hmass, one_mul]

/-- Symmetry transfers fine-after-coarse nesting to coarse-after-fine nesting. -/
-- @node: coefficientProjection_coarse_fine_of_fine_coarse
lemma coefficientProjection_coarse_fine_of_fine_coarse (j k J : ℕ)
    (hnest : ∀ f : Hj J, coefficientProjection k J (coefficientProjection j J f) =
      coefficientProjection j J f) (f : Hj J) :
    coefficientProjection j J (coefficientProjection k J f) = coefficientProjection j J f := by
  have he (g : Hj J) :
      inner ℝ (coefficientProjection j J (coefficientProjection k J f)) g =
        inner ℝ (coefficientProjection j J f) g := by
    rw [coefficientProjection_inner, coefficientProjection_inner, hnest,
      coefficientProjection_inner]
  have hz : ‖coefficientProjection j J (coefficientProjection k J f) -
      coefficientProjection j J f‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, he, sub_self]
  exact sub_eq_zero.mp (norm_eq_zero.mp (by
    have hn := norm_nonneg (coefficientProjection j J (coefficientProjection k J f) -
      coefficientProjection j J f)
    nlinarith))

/-- Coarse averaging after refined averaging recovers the same coarse vector. -/
-- @node: coefficientProjection_coarse_fine_mul
lemma coefficientProjection_coarse_fine_mul (j s r : ℕ)
    (hj : 0 < j) (hs : 0 < s) (hr : 0 < r) (f : Hj ((j * s) * r)) :
    coefficientProjection j ((j * s) * r)
      (coefficientProjection (j * s) ((j * s) * r) f) =
      coefficientProjection j ((j * s) * r) f := by
  exact coefficientProjection_coarse_fine_of_fine_coarse j (j * s) ((j * s) * r)
    (coefficientProjection_fine_coarse_mul j s r hj hs hr) f

/-- Positive divisor ranks give two-sided nesting of the concrete projections. -/
-- @node: coefficientProjection_nested_of_dvd
lemma coefficientProjection_nested_of_dvd (j k J : ℕ)
    (hj : 0 < j) (hk : 0 < k) (hJ : 0 < J) (hjk : j ∣ k) (hkJ : k ∣ J)
    (f : Hj J) :
    coefficientProjection k J (coefficientProjection j J f) = coefficientProjection j J f ∧
    coefficientProjection j J (coefficientProjection k J f) = coefficientProjection j J f := by
  rcases hjk with ⟨s, rfl⟩
  rcases hkJ with ⟨r, rfl⟩
  have hs : 0 < s := by nlinarith
  have hr : 0 < r := by nlinarith
  exact ⟨coefficientProjection_fine_coarse_mul j s r hj hs hr f,
    coefficientProjection_coarse_fine_mul j s r hj hs hr f⟩

/-- Dyadic outcome ranks divide every later rank in the same ladder. -/
-- @node: band_rank_dvd
lemma band_rank_dvd (L s t : ℕ) (hst : s ≤ t) : 2 ^ s * L ∣ 2 ^ t * L := by
  refine ⟨2 ^ (t - s), ?_⟩
  have he : 2 ^ t = 2 ^ s * 2 ^ (t - s) := by
    rw [← pow_add, Nat.add_sub_of_le hst]
  rw [he]
  ring

/-- All pairs of ordered dyadic projections satisfy concrete two-sided nesting. -/
-- @node: coefficientProjection_nested_ladder
lemma coefficientProjection_nested_ladder (L T s t : ℕ) (hL : 0 < L)
    (hst : s ≤ t) (htT : t ≤ T) (f : Hj (2 ^ T * L)) :
    coefficientProjection (2 ^ t * L) (2 ^ T * L)
      (coefficientProjection (2 ^ s * L) (2 ^ T * L) f) =
      coefficientProjection (2 ^ s * L) (2 ^ T * L) f ∧
    coefficientProjection (2 ^ s * L) (2 ^ T * L)
      (coefficientProjection (2 ^ t * L) (2 ^ T * L) f) =
      coefficientProjection (2 ^ s * L) (2 ^ T * L) f := by
  exact coefficientProjection_nested_of_dvd _ _ _ (by positivity) (by positivity)
    (by positivity) (band_rank_dvd L s t hst) (band_rank_dvd L t T htT) f

/-- Every concrete dyadic band is idempotent. -/
-- @node: Qband_idempotent_ladder
lemma Qband_idempotent_ladder (L T t : ℕ) (hL : 0 < L) (htT : t ≤ T)
    (f : Hj (2 ^ T * L)) :
    Qband L (2 ^ T * L) t (Qband L (2 ^ T * L) t f) = Qband L (2 ^ T * L) t f := by
  have hn := coefficientProjection_nested_ladder L T
  by_cases ht : t = 0
  · subst t
    simpa only [Qband, ↓reduceIte, pow_zero, one_mul] using
      (hn 0 0 hL (by omega) (by omega) f).1
  · apply Qband_idempotent_of_nested L (2 ^ T * L) t ht
    · intro g; exact (hn t t hL le_rfl htT g).1
    · intro g; exact (hn (t - 1) (t - 1) hL le_rfl (by omega) g).1
    · intro g; exact (hn (t - 1) t hL (by omega) htT g).1
    · intro g; exact (hn (t - 1) t hL (by omega) htT g).2

/-- Earlier bands annihilate every later dyadic band. -/
-- @node: Qband_annihilation_ladder
lemma Qband_annihilation_ladder (L T s t : ℕ) (hL : 0 < L)
    (hst : s < t) (htT : t ≤ T) (f : Hj (2 ^ T * L)) :
    Qband L (2 ^ T * L) s (Qband L (2 ^ T * L) t f) = 0 := by
  have ht : t ≠ 0 := by omega
  have hn := coefficientProjection_nested_ladder L T
  by_cases hs : s = 0
  · subst s
    simp only [Qband, ↓reduceIte, if_neg ht, coefficientProjection_sub]
    have h1 := (hn 0 t hL (by omega) htT f).2
    have h2 := (hn 0 (t - 1) hL (by omega) (by omega) f).2
    simp only [pow_zero, one_mul] at h1 h2
    rw [h1, h2, sub_self]
  · simp only [Qband, if_neg hs, if_neg ht, coefficientProjection_sub]
    rw [(hn s t hL (by omega) htT f).2,
      (hn s (t - 1) hL (by omega) (by omega) f).2,
      (hn (s - 1) t hL (by omega) htT f).2,
      (hn (s - 1) (t - 1) hL (by omega) (by omega) f).2]
    abel

/-- Histograms at nested dyadic ranks have orthogonal bands, contractive projections,
and a telescoping decomposition of the final subspace. -/
-- @node: band_projection_algebra
lemma band_projection_algebra (L T : ℕ) (hL : Dyadic L) :
    let J := 2 ^ T * L
    (∀ f : Hj J, ∑ t ∈ Finset.range (T + 1), Qband L J t f = f) ∧
    (∀ s t, s ≤ T → t ≤ T → s ≠ t → ∀ f g : Hj J,
      inner ℝ (Qband L J s f) (Qband L J t g) = 0) ∧
    (∀ t, t ≤ T → ∀ f : Hj J, ‖Qband L J t f‖ ≤ ‖f‖) := by
  refine ⟨sum_Qband_eq_self L T, ?_⟩
  have hpos : 0 < L := by
    rcases hL with ⟨l, rfl⟩
    positivity
  constructor
  · intro s t hs ht hne f g
    rcases lt_or_gt_of_ne hne with hst | hts
    · exact Qband_inner_eq_zero_of_annihilation L (2 ^ T * L) s t f g
        (Qband_annihilation_ladder L T s t hpos hst ht g)
    · rw [real_inner_comm]
      exact Qband_inner_eq_zero_of_annihilation L (2 ^ T * L) t s g f
        (Qband_annihilation_ladder L T t s hpos hts hs f)
  · intro t ht f
    exact Qband_norm_le_of_idempotent L (2 ^ T * L) t f
      (Qband_idempotent_ladder L T t hpos ht f)

end CausalSmith.Stat.DensityEffectRoughNull
