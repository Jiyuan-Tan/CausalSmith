module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.SigningDecoupling
public import Causalean.Tactic.IntegralLinearity

/-! # Isotropic row signing lower bound

Coordinate second moments control isotropic norms and projections. Direct pairwise
moment bounds handle at most 256 rows. These results support the full signing theorem
assembled in `SigningPartition`, without coordinate independence.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Coordinate second moments make the squared Euclidean norm integrable.](goal) Under [the stated conditions](hyp:hmom). -/
-- @node: isotropic_norm_sq_integrable
lemma isotropic_norm_sq_integrable (r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r)))
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) :
    Integrable (fun v => ‖v‖ ^ 2) P := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  exact integrable_finsetSum Finset.univ (fun a _ => (hmom a).integrable_sq)

/-- [ The diagonal energy of one isotropic row is exactly its dimension.](goal) Under [the stated conditions](hyp:hmom,hiso). -/
-- @node: isotropic_norm_sq_integral
lemma isotropic_norm_sq_integral (r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r)))
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0) :
    (∫ v, ‖v‖ ^ 2 ∂P) = r := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun a _ => (hmom a).integrable_sq)]
  simp only [pow_two, hiso, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- [ Independent rows have expected diagonal energy equal to sample size times dimension.](goal) Under [the stated conditions](hyp:hmom,hiso). -/
-- @node: isotropic_sample_diagonal_integral
lemma isotropic_sample_diagonal_integral (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0) :
    (∫ vs : Fin n → EuclideanSpace ℝ (Fin r), ∑ i, ‖vs i‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => P)) = (n : ℝ) * r := by
  have hi (i : Fin n) : Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) =>
      ‖vs i‖ ^ 2) (Measure.pi (fun _ : Fin n => P)) :=
    (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable
      (isotropic_norm_sq_integrable r P hmom)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have heval (i : Fin n) :
      (∫ vs : Fin n → EuclideanSpace ℝ (Fin r), ‖vs i‖ ^ 2
        ∂Measure.pi (fun _ : Fin n => P)) = r := by
    rw [integral_comp_eval (μ := fun _ : Fin n => P) (i := i)
      (isotropic_norm_sq_integrable r P hmom).aestronglyMeasurable]
    exact isotropic_norm_sq_integral r P hmom hiso
  simp [heval]

/-- [ Expected minimum signing energy is diagonal energy minus at most the expected
maximum off-diagonal fluctuation, the final subtraction in the proof roadmap.](goal) Under [the stated conditions](hyp:hmom,hiso). -/
-- @node: isotropic_signing_lower_of_offDiagonal
lemma isotropic_signing_lower_of_offDiagonal (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0) :
    (n : ℝ) * r - (∫ vs, signingOffDiagonalMax vs ∂Measure.pi (fun _ : Fin n => P)) ≤
      ∫ vs : Fin n → EuclideanSpace ℝ (Fin r),
        ⨅ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ^ 2
          ∂Measure.pi (fun _ : Fin n => P) := by
  have hdiag : Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) =>
      ∑ i, ‖vs i‖ ^ 2) (Measure.pi (fun _ : Fin n => P)) := by
    apply integrable_finsetSum
    intro i _
    exact (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable
      (isotropic_norm_sq_integrable r P hmom)
  have h := integral_mono (hdiag.sub (signingOffDiagonalMax_integrable n r P hmom))
    (signing_min_integrable n r P hmom) signing_min_ge_diagonal_sub_max
  change (∫ vs : Fin n → EuclideanSpace ℝ (Fin r),
    (∑ i, ‖vs i‖ ^ 2) - signingOffDiagonalMax vs ∂Measure.pi (fun _ : Fin n => P)) ≤ _ at h
  rw [integral_sub hdiag (signingOffDiagonalMax_integrable n r P hmom),
    isotropic_sample_diagonal_integral n r P hmom hiso] at h
  exact h

/-- Expand a squared real Euclidean inner product into coordinate moment products. [The asserted mathematical result follows](goal). -/
-- @node: euclidean_inner_sq_expansion
lemma euclidean_inner_sq_expansion {r : ℕ} (u v : EuclideanSpace ℝ (Fin r)) :
    (inner ℝ u v) ^ 2 = ∑ a, ∑ b, (u a * u b) * (v a * v b) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, pow_two,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Coordinate L² moments suffice to integrate every squared fixed-direction projection. Under [the stated conditions](hyp:hmom), [the asserted mathematical result follows](goal). -/
-- @node: isotropic_projection_sq_integrable
lemma isotropic_projection_sq_integrable (r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r)))
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) (u : EuclideanSpace ℝ (Fin r)) :
    Integrable (fun v => (inner ℝ u v) ^ 2) P := by
  simp_rw [euclidean_inner_sq_expansion]
  apply integrable_finsetSum
  intro a _
  apply integrable_finsetSum
  intro b _
  exact ((hmom a).integrable_mul (hmom b)).const_mul (u a * u b)

/-- [ Isotropy controls all fixed-direction projections without coordinate independence.](goal) Under [the stated conditions](hyp:hmom,hiso). -/
-- @node: isotropic_projection_sq_integral
lemma isotropic_projection_sq_integral (r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r)))
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0)
    (u : EuclideanSpace ℝ (Fin r)) :
    (∫ v, (inner ℝ u v) ^ 2 ∂P) = ‖u‖ ^ 2 := by
  simp_rw [euclidean_inner_sq_expansion]
  have hi (a b : Fin r) : Integrable (fun v => (u a * u b) * (v a * v b)) P := by
    simpa only [Pi.mul_apply] using
      ((hmom a).integrable_mul (hmom b)).const_mul (u a * u b)
  have hs (a : Fin r) : Integrable (fun v => ∑ b, (u a * u b) * (v a * v b)) P :=
    integrable_finsetSum Finset.univ (fun b _ => hi a b)
  rw [integral_finsetSum Finset.univ (fun a _ => hs a)]
  simp_rw [integral_finsetSum Finset.univ (fun b _ => hi _ b), integral_const_mul, hiso]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simpa only [pow_two] using (EuclideanSpace.real_norm_sq_eq u).symm

/-- [ The squared inner product of independent isotropic rows is integrable.](goal) Under [the stated conditions](hyp:hmom). -/
-- @node: isotropic_independent_inner_sq_integrable
lemma isotropic_independent_inner_sq_integrable (r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) :
    Integrable (fun vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r) =>
      (inner ℝ vs.1 vs.2) ^ 2) (P.prod P) := by
  simp_rw [euclidean_inner_sq_expansion]
  apply integrable_finsetSum
  intro a _
  apply integrable_finsetSum
  intro b _
  exact ((hmom a).integrable_mul (hmom b)).mul_prod
    ((hmom a).integrable_mul (hmom b))

/-- [ Independent isotropic rows have squared inner-product expectation equal to dimension.](goal) Under [the stated conditions](hyp:hmom,hiso). -/
-- @node: isotropic_independent_inner_sq_integral
lemma isotropic_independent_inner_sq_integral (r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0) :
    (∫ vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r),
      (inner ℝ vs.1 vs.2) ^ 2 ∂P.prod P) = r := by
  simp_rw [euclidean_inner_sq_expansion]
  have hi (a b : Fin r) : Integrable
      (fun vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r) =>
        (vs.1 a * vs.1 b) * (vs.2 a * vs.2 b)) (P.prod P) := by
    simpa only [Pi.mul_apply] using ((hmom a).integrable_mul (hmom b)).mul_prod
      ((hmom a).integrable_mul (hmom b))
  have hs (a : Fin r) : Integrable
      (fun vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r) =>
        ∑ b, (vs.1 a * vs.1 b) * (vs.2 a * vs.2 b)) (P.prod P) :=
    integrable_finsetSum Finset.univ (fun b _ => hi a b)
  rw [integral_finsetSum Finset.univ (fun a _ => hs a)]
  have he (a b : Fin r) :
      (∫ vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r),
        (vs.1 a * vs.1 b) * (vs.2 a * vs.2 b) ∂P.prod P) =
        (if a = b then (1 : ℝ) else 0) * (if a = b then (1 : ℝ) else 0) := by
    exact (integral_prod_mul (μ := P) (ν := P)
      (fun v : EuclideanSpace ℝ (Fin r) => v a * v b)
      (fun v : EuclideanSpace ℝ (Fin r) => v a * v b)).trans
      (by rw [hiso])
  simp_rw [integral_finsetSum Finset.univ (fun b _ => hi _ b), he]
  simp

/-- [ The mean absolute projection is at most the length of its fixed direction.](goal) Under [the stated conditions](hyp:hmom,hiso). -/
-- @node: isotropic_projection_abs_integral_le
lemma isotropic_projection_abs_integral_le (r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0)
    (u : EuclideanSpace ℝ (Fin r)) :
    (∫ v, |inner ℝ u v| ∂P) ≤ ‖u‖ := by
  have hp : MemLp (fun v => inner ℝ u v) 2 P :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (isotropic_projection_sq_integrable r P hmom u)
  have ha : MemLp (fun v => |inner ℝ u v|) 2 P := by simpa using hp.norm
  have hv := variance_nonneg (X := fun v => |inner ℝ u v|) (μ := P)
  rw [variance_eq_sub ha] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  rw [isotropic_projection_sq_integral r P hmom hiso u] at hv
  nlinarith [norm_nonneg u]

/-- [ The mean absolute inner product of independent isotropic rows is at most √r.](goal) Under [the stated conditions](hyp:hmom,hiso). -/
-- @node: isotropic_independent_inner_abs_integral_le
lemma isotropic_independent_inner_abs_integral_le (r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0) :
    (∫ vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r),
      |inner ℝ vs.1 vs.2| ∂P.prod P) ≤ Real.sqrt r := by
  have hp : MemLp
      (fun vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r) =>
        inner ℝ vs.1 vs.2) 2 (P.prod P) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (isotropic_independent_inner_sq_integrable r P hmom)
  have ha : MemLp
      (fun vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r) =>
        |inner ℝ vs.1 vs.2|) 2 (P.prod P) := by simpa using hp.norm
  have hv := variance_nonneg (X := fun vs => |inner ℝ vs.1 vs.2|) (μ := P.prod P)
  rw [variance_eq_sub ha] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  rw [isotropic_independent_inner_sq_integral r P hmom hiso] at hv
  nlinarith [Real.sqrt_nonneg (r : ℝ), Real.sq_sqrt (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

/-- [ Two distinct evaluation rows have the original product law.](goal) Under [the stated conditions](hyp:hij). -/
-- @node: signing_pair_measurePreserving
lemma signing_pair_measurePreserving (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (i j : Fin n) (hij : i ≠ j) :
    MeasurePreserving (fun vs : Fin n → EuclideanSpace ℝ (Fin r) => (vs i, vs j))
      (Measure.pi (fun _ : Fin n => P)) (P.prod P) := by
  have hi := (iIndepFun_pi (μ := fun _ : Fin n => P)
    (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
  refine ⟨by fun_prop, ?_⟩
  simpa only [(measurePreserving_eval (fun _ : Fin n => P) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => P) j).map_eq] using
    hi.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable

/-- [ The pairwise absolute moment bound applies to any two distinct sample rows.](goal) Under [the stated conditions](hyp:hmom,hiso,hij). -/
-- @node: isotropic_sample_inner_abs_integral_le
lemma isotropic_sample_inner_abs_integral_le (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0)
    (i j : Fin n) (hij : i ≠ j) :
    (∫ vs : Fin n → EuclideanSpace ℝ (Fin r), |inner ℝ (vs i) (vs j)|
      ∂Measure.pi (fun _ : Fin n => P)) ≤ Real.sqrt r := by
  have hmap := (signing_pair_measurePreserving n r P i j hij).map_eq
  have heq : (∫ vs : Fin n → EuclideanSpace ℝ (Fin r), |inner ℝ (vs i) (vs j)|
      ∂Measure.pi (fun _ : Fin n => P)) =
      ∫ v : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r),
        |inner ℝ v.1 v.2| ∂P.prod P := by
    rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
  rw [heq]
  exact isotropic_independent_inner_abs_integral_le r P hmom hiso

/-- The triangle inequality bounds every off-diagonal signing by the sum of pair magnitudes. [The asserted mathematical result follows](goal). -/
-- @node: signingOffDiagonalMax_le_pair_sum
lemma signingOffDiagonalMax_le_pair_sum {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) :
    signingOffDiagonalMax vs ≤ ∑ i, ∑ j, if i = j then 0 else |inner ℝ (vs i) (vs j)| := by
  classical
  apply ciSup_le
  intro z
  unfold signingOffDiagonal
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · cases z i <;> cases z j <;> simp [hij, sgn]

/-- Summing distinct-pair moments controls the maximum fluctuation directly,
without contraction; the loose n² count also includes the zero diagonal terms. Under [the stated conditions](hyp:hmom,hiso), [the asserted mathematical result follows](goal). -/
-- @node: isotropic_offDiagonal_integral_le_pair_count
lemma isotropic_offDiagonal_integral_le_pair_count (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0) :
    (∫ vs : Fin n → EuclideanSpace ℝ (Fin r), signingOffDiagonalMax vs
      ∂Measure.pi (fun _ : Fin n => P)) ≤ (n : ℝ) ^ 2 * Real.sqrt r := by
  classical
  have hi (i j : Fin n) : Integrable
      (fun vs : Fin n → EuclideanSpace ℝ (Fin r) =>
        if i = j then 0 else |inner ℝ (vs i) (vs j)|)
      (Measure.pi (fun _ : Fin n => P)) := by
    by_cases hij : i = j
    · simp only [hij, if_true]; exact integrable_zero _ _ _
    · simpa only [hij, if_false, Real.norm_eq_abs] using
        (signing_row_inner_integrable n r P hmom i j).norm
  have hsum (i : Fin n) := integrable_finsetSum Finset.univ (fun j _ => hi i j)
  have h := integral_mono (signingOffDiagonalMax_integrable n r P hmom)
    (integrable_finsetSum Finset.univ (fun i _ => hsum i))
    (fun vs => signingOffDiagonalMax_le_pair_sum vs)
  rw [integral_finsetSum _ (fun i _ => hsum i)] at h
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)] at h
  have hpair (i j : Fin n) :
      (∫ vs : Fin n → EuclideanSpace ℝ (Fin r),
        (if i = j then 0 else |inner ℝ (vs i) (vs j)|)
          ∂Measure.pi (fun _ : Fin n => P)) ≤ Real.sqrt r := by
    by_cases hij : i = j
    · simp only [hij, if_true, integral_zero]; exact Real.sqrt_nonneg _
    · simp only [hij, if_false]
      exact isotropic_sample_inner_abs_integral_le n r P hmom hiso i j hij
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, Real.sqrt (r : ℝ) :=
      h.trans (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j)))
    _ = _ := by simp; ring

/-- [ Direct pairwise second moments give a contraction-free signing bound for
all sample sizes, useful before the sharper large-sample argument is available.](goal) Under [the stated conditions](hyp:hmom,hiso). -/
-- @node: isotropic_signing_lower_pair_count
lemma isotropic_signing_lower_pair_count (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0) :
    (n : ℝ) * r - (n : ℝ) ^ 2 * Real.sqrt r ≤
      ∫ vs : Fin n → EuclideanSpace ℝ (Fin r),
        ⨅ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ^ 2
          ∂Measure.pi (fun _ : Fin n => P) := by
  have hdiag := isotropic_signing_lower_of_offDiagonal n r P hmom hiso
  have hpairs := isotropic_offDiagonal_integral_le_pair_count n r P hmom hiso
  linarith

/-- [ For at most 256 rows, the direct pair count fits within the paper's
16n√(nr) error allowance.](goal) Under [the stated conditions](hyp:hn). -/
-- @node: isotropic_pair_count_error_le
lemma isotropic_pair_count_error_le (n r : ℕ) (hn : n ≤ 256) :
    (n : ℝ) ^ 2 * Real.sqrt r ≤ 16 * n * Real.sqrt ((n : ℝ) * r) := by
  have hnR : (n : ℝ) ≤ 256 := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs := Real.sq_sqrt hn0
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hs16 : Real.sqrt (n : ℝ) ≤ 16 := (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith⟩
  have hnn : (n : ℝ) ≤ 16 * Real.sqrt n := by nlinarith
  rw [Real.sqrt_mul hn0]
  nlinarith [mul_nonneg (mul_nonneg hn0 (Real.sqrt_nonneg (r : ℝ)))
    (sub_nonneg.mpr hnn)]

/-- [ The small-sample portion of the headline follows directly from isotropic
pair moments and diagonal subtraction, with no contraction premise.](goal) Under [the stated conditions](hyp:hn,hmom,hiso). -/
-- @node: isotropic_small_sample_signing_lower
lemma isotropic_small_sample_signing_lower (n r : ℕ) (hn : n ≤ 256)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0) :
    (n : ℝ) * r - (n : ℝ) ^ 2 - 16 * n * Real.sqrt ((n : ℝ) * r) ≤
      ∫ vs : Fin n → EuclideanSpace ℝ (Fin r),
        ⨅ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ^ 2
          ∂Measure.pi (fun _ : Fin n => P) := by
  have hpairs := isotropic_signing_lower_pair_count n r P hmom hiso
  have herr := isotropic_pair_count_error_le n r hn
  nlinarith [sq_nonneg (n : ℝ)]

/-- For two rows, the four signings reduce exactly to the diagonal energy minus twice
 the absolute inner product, as in the roadmap's smallest-sample check. [The asserted mathematical result follows](goal). -/
-- @node: two_row_min_signing_eq
lemma two_row_min_signing_eq {r : ℕ} (u v : EuclideanSpace ℝ (Fin r)) :
    (⨅ z : Signs 2, ‖sgn (z 0) • u + sgn (z 1) • v‖ ^ 2) =
      ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * |inner ℝ u v| := by
  have hb : BddBelow (Set.range (fun z : Signs 2 =>
      ‖sgn (z 0) • u + sgn (z 1) • v‖ ^ 2)) := ⟨0, by rintro _ ⟨z, rfl⟩; positivity⟩
  apply le_antisymm
  · have hp : (⨅ z : Signs 2, ‖sgn (z 0) • u + sgn (z 1) • v‖ ^ 2) ≤ ‖u + v‖ ^ 2 := by
      calc
        _ ≤ ‖sgn true • u + sgn true • v‖ ^ 2 := ciInf_le hb (fun _ => true)
        _ = _ := by simp [sgn]
    have hm : (⨅ z : Signs 2, ‖sgn (z 0) • u + sgn (z 1) • v‖ ^ 2) ≤ ‖u - v‖ ^ 2 := by
      calc
        _ ≤ ‖sgn true • u + sgn false • v‖ ^ 2 := ciInf_le hb (fun i => i == 0)
        _ = _ := by simp [sgn, sub_eq_add_neg]
    rw [norm_add_sq_real] at hp
    rw [norm_sub_sq_real] at hm
    by_cases h : 0 ≤ inner ℝ u v
    · rw [abs_of_nonneg h]
      linarith
    · rw [abs_of_neg (lt_of_not_ge h)]
      linarith
  · apply le_ciInf
    intro z
    have ha := neg_abs_le (inner ℝ u v)
    have hb' := le_abs_self (inner ℝ u v)
    cases z 0 <;> cases z 1 <;>
      simp only [sgn, Bool.false_eq_true, if_false, if_true, one_smul,
        neg_one_smul, norm_add_sq_real, inner_neg_left, inner_neg_right, norm_neg,
        neg_neg] <;> nlinarith

/-- The complete two-row signing lower bound follows from the independent inner-product
moment, with the sharper error 2√r from the roadmap's check. Under [the stated conditions](hyp:hmom,hiso), [the asserted mathematical result follows](goal). -/
-- @node: isotropic_two_row_signing_lower
lemma isotropic_two_row_signing_lower (r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0) :
    2 * (r : ℝ) - 2 * Real.sqrt r ≤
      ∫ vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r),
        ⨅ z : Signs 2, ‖sgn (z 0) • vs.1 + sgn (z 1) • vs.2‖ ^ 2 ∂P.prod P := by
  have hnorm := isotropic_norm_sq_integrable r P hmom
  have hf : Integrable (fun vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r) =>
      ‖vs.1‖ ^ 2) (P.prod P) := hnorm.comp_fst P
  have hg : Integrable (fun vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r) =>
      ‖vs.2‖ ^ 2) (P.prod P) := hnorm.comp_snd P
  have hp : MemLp
      (fun vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r) =>
        inner ℝ vs.1 vs.2) 2 (P.prod P) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (isotropic_independent_inner_sq_integrable r P hmom)
  have ha : Integrable
      (fun vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r) =>
        2 * |inner ℝ vs.1 vs.2|) (P.prod P) := by
    simpa using (hp.integrable (by norm_num)).norm.const_mul 2
  simp_rw [two_row_min_signing_eq]
  integral_linearity
  have he1 : (∫ vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r),
      ‖vs.1‖ ^ 2 ∂P.prod P) = r := by
    simpa using (integral_prod_mul (μ := P) (ν := P)
      (fun v => ‖v‖ ^ 2) (fun _ => (1 : ℝ))).trans
        (by simp [isotropic_norm_sq_integral r P hmom hiso])
  have he2 : (∫ vs : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r),
      ‖vs.2‖ ^ 2 ∂P.prod P) = r := by
    simpa using (integral_prod_mul (μ := P) (ν := P)
      (fun _ => (1 : ℝ)) (fun v => ‖v‖ ^ 2)).trans
        (by simp [isotropic_norm_sq_integral r P hmom hiso])
  rw [he1, he2]
  have h := isotropic_independent_inner_abs_integral_le r P hmom hiso
  linarith

/-- [ At the prescribed dimension threshold, the two error terms consume at most
half of the diagonal energy.](goal) Under [the stated conditions](hyp:hlarge). -/
-- @node: isotropic_signing_error_le_half
lemma isotropic_signing_error_le_half (n r : ℕ) (hlarge : 4096 * n ≤ r) :
    (n : ℝ) ^ 2 + 16 * n * Real.sqrt ((n : ℝ) * r) ≤ (n : ℝ) * r / 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hlargeR : (4096 : ℝ) * n ≤ r := by exact_mod_cast hlarge
  have hnr : (n : ℝ) * r ≤ ((r : ℝ) / 64) ^ 2 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hlargeR)]
  have hsqrt : Real.sqrt ((n : ℝ) * r) ≤ (r : ℝ) / 64 :=
    (Real.sqrt_le_iff).2 ⟨by positivity, hnr⟩
  have herr : 16 * (n : ℝ) * Real.sqrt ((n : ℝ) * r) ≤ (n : ℝ) * r / 4 := by
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hsqrt)]
  have hdiag : (n : ℝ) ^ 2 ≤ (n : ℝ) * r / 4096 := by
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hlargeR)]
  nlinarith [mul_nonneg hn hr]


end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
