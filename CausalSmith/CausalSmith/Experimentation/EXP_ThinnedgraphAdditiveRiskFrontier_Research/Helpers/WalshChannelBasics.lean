module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockPrior
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BaselineTranslationAffinity
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.WalshParseval
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Walsh expansion and channel energy estimates
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- A single-row shifted baseline density for a fixed Boolean sign vector. -/
def rowDensity (d : ℕ) (h : ℝ) (ε : Fin d → Bool) (w : ℝ) : ℝ :=
  cosSqDensity (w - h / (2 * d) * ∑ j, signOf (ε j))

/-- The uniform average of all sign-vector row densities. -/
def refDensity (d : ℕ) (h : ℝ) (w : ℝ) : ℝ :=
  ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool, rowDensity d h ε w

/-- The permutation-symmetric Walsh likelihood coefficient, zero when the reference density
vanishes. -/
def walshCoeff (d : ℕ) (h : ℝ) (s : ℕ) (w : ℝ) : ℝ :=
  if refDensity d h w = 0 then 0 else
    ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool,
      rowDensity d h ε w / refDensity d h w *
        ∏ j ∈ Finset.univ.filter (fun j : Fin d => j.val < s), signOf (ε j)

/-- The squared Walsh coefficient integrated against its reference density. -/
def gamma (d : ℕ) (h : ℝ) (s : ℕ) : ℝ :=
  ∫ w, (walshCoeff d h s w) ^ 2 * refDensity d h w

/-- The total nonconstant Walsh channel energy. -/
def eta (d : ℕ) (h : ℝ) : ℝ := ∑ s ∈ Finset.Icc 1 d, (d.choose s : ℝ) * gamma d h s
/-- The order-weighted nonconstant Walsh channel energy. -/
def etaOne (d : ℕ) (h : ℝ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 d, s * (d.choose s : ℝ) * gamma d h s

/-- Each sign-conditioned response density is a normalized translated baseline.  [For the stated data and conditions](hyp:d,h,ε), [the stated conclusion holds](goal). -/
-- @node: rowDensity_integrable_normalized
lemma rowDensity_integrable_normalized (d : ℕ) (h : ℝ) (ε : Fin d → Bool) :
    Integrable (rowDensity d h ε) ∧ (∫ w, rowDensity d h ε w) = 1 := by
  exact translated_cosSqDensity_integrable_normalized _

/-- All sign-conditioned densities and their uniform average are nonnegative.  [For the stated data and conditions](hyp:d,h,w), [the stated conclusion holds](goal). -/
-- @node: refDensity_nonneg
lemma refDensity_nonneg (d : ℕ) (h w : ℝ) : 0 ≤ refDensity d h w := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun ε _ => cosSqDensity_nonneg _)

/-- The reference density integrates to one, since there are exactly two-to-d sign vectors.  [For the stated data and conditions](hyp:d,h), [the stated conclusion holds](goal). -/
-- @node: refDensity_integrable_normalized
lemma refDensity_integrable_normalized (d : ℕ) (h : ℝ) :
    Integrable (refDensity d h) ∧ (∫ w, refDensity d h w) = 1 := by
  have hi : ∀ ε : Fin d → Bool, Integrable (rowDensity d h ε) :=
    fun ε => (rowDensity_integrable_normalized d h ε).1
  constructor
  · exact (integrable_finsetSum _ (fun ε _ => hi ε)).const_mul _
  · unfold refDensity
    rw [integral_const_mul, integral_finsetSum _ (fun ε _ => hi ε)]
    simp only [(rowDensity_integrable_normalized d h _).2, Finset.sum_const,
      Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
    exact inv_mul_cancel₀ (by positivity)

/-- At a zero of the reference density every component density also vanishes.  [For the stated data and conditions](hyp:d,h,w,hw,ε), [the stated conclusion holds](goal). -/
-- @node: rowDensity_eq_zero_of_refDensity_eq_zero
lemma rowDensity_eq_zero_of_refDensity_eq_zero (d : ℕ) (h w : ℝ)
    (hw : refDensity d h w = 0) (ε : Fin d → Bool) : rowDensity d h ε w = 0 := by
  have hs : (∑ ε : Fin d → Bool, rowDensity d h ε w) = 0 := by
    exact (mul_eq_zero.mp hw).resolve_left (inv_ne_zero (by positivity))
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun ε _ => cosSqDensity_nonneg _)).mp hs ε (Finset.mem_univ _)

/-- The degree-zero coefficient equals one wherever the reference density is positive.  [For the stated data and conditions](hyp:d,h,w,hw), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_zero
lemma walshCoeff_zero (d : ℕ) (h w : ℝ) (hw : 0 < refDensity d h w) :
    walshCoeff d h 0 w = 1 := by
  rw [walshCoeff, if_neg (ne_of_gt hw)]
  simp only [Nat.not_lt_zero, Finset.filter_false, Finset.prod_empty, mul_one]
  rw [← Finset.sum_div, ← mul_div_assoc]
  change refDensity d h w / refDensity d h w = 1
  exact div_self (ne_of_gt hw)

/-- Summing a nonempty sign character over the full Boolean cube gives zero.  [For the stated data and conditions](hyp:d,E,hE), [the stated conclusion holds](goal). -/
-- @node: sign_character_sum_eq_zero
lemma sign_character_sum_eq_zero (d : ℕ) (E : Finset (Fin d)) (hE : E.Nonempty) :
    (∑ ε : Fin d → Bool, ∏ j ∈ E, signOf (ε j)) = 0 := by
  have hp (ε : Fin d → Bool) :
      (∏ j ∈ E, signOf (ε j)) = ∏ j : Fin d, if j ∈ E then signOf (ε j) else 1 := by
    simp
  simp_rw [hp]
  rw [← Fintype.prod_sum (fun (j : Fin d) (b : Bool) => if j ∈ E then signOf b else (1 : ℝ))]
  obtain ⟨j, hj⟩ := hE
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hj, signOf]

/-- Multiplication by the reference density cancels the coefficient's denominator,
including at zero-density points where all component densities vanish.  [For the stated data and conditions](hyp:d,h,s,w), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_mul_refDensity
lemma walshCoeff_mul_refDensity (d : ℕ) (h : ℝ) (s : ℕ) (w : ℝ) :
    walshCoeff d h s w * refDensity d h w =
      ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool,
        rowDensity d h ε w *
          ∏ j ∈ Finset.univ.filter (fun j : Fin d => j.val < s), signOf (ε j) := by
  by_cases hw : refDensity d h w = 0
  · simp [hw, rowDensity_eq_zero_of_refDensity_eq_zero d h w hw]
  · rw [walshCoeff, if_neg hw, mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro ε _
    rw [mul_right_comm, div_mul_cancel₀ _ hw]

/-- Every nonconstant Walsh coefficient has reference-weighted integral zero.  [For the stated data and conditions](hyp:d,h,hd,s,hs), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_centered
lemma walshCoeff_centered (d : ℕ) (h : ℝ) (hd : 1 ≤ d) (s : ℕ) (hs : 1 ≤ s) :
    (∫ w, walshCoeff d h s w * refDensity d h w) = 0 := by
  simp_rw [walshCoeff_mul_refDensity]
  rw [integral_const_mul, integral_finsetSum _ (fun ε _ =>
    (rowDensity_integrable_normalized d h ε).1.mul_const _)]
  simp_rw [integral_mul_const, (rowDensity_integrable_normalized d h _).2, one_mul]
  rw [sign_character_sum_eq_zero, mul_zero]
  refine ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  simpa using (show 0 < s by omega)

/-- Squared Walsh coefficients have nonnegative reference-weighted energy.  [For the stated data and conditions](hyp:d,h,s), [the stated conclusion holds](goal). -/
-- @node: gamma_nonneg
lemma gamma_nonneg (d : ℕ) (h : ℝ) (s : ℕ) : 0 ≤ gamma d h s := by
  exact integral_nonneg (fun w => mul_nonneg (sq_nonneg _) (refDensity_nonneg d h w))

/-- Weighting each nonconstant degree by its positive order increases the energy.  [For the stated data and conditions](hyp:d,h), [the stated conclusion holds](goal). -/
-- @node: eta_nonneg_le_etaOne
lemma eta_nonneg_le_etaOne (d : ℕ) (h : ℝ) :
    0 ≤ eta d h ∧ eta d h ≤ etaOne d h := by
  constructor
  · exact Finset.sum_nonneg (fun s _ => mul_nonneg (Nat.cast_nonneg _) (gamma_nonneg d h s))
  · apply Finset.sum_le_sum
    intro s hs
    have h1 : (1 : ℝ) ≤ s := by exact_mod_cast (Finset.mem_Icc.mp hs).1
    have hg := mul_nonneg (Nat.cast_nonneg (d.choose s) : (0 : ℝ) ≤ d.choose s)
      (gamma_nonneg d h s)
    calc
      (d.choose s : ℝ) * gamma d h s ≤ s * ((d.choose s : ℝ) * gamma d h s) :=
        le_mul_of_one_le_left hg h1
      _ = s * (d.choose s : ℝ) * gamma d h s := by ring

/-- Relabeling coordinates preserves the row likelihood and transports its sign character.  [For the stated data and conditions](hyp:d,h,w,p,E), [the stated conclusion holds](goal). -/
-- @node: rowDensity_character_relabel
lemma rowDensity_character_relabel (d : ℕ) (h w : ℝ) (p : Equiv.Perm (Fin d))
    (E : Finset (Fin d)) :
    (∑ ε : Fin d → Bool, rowDensity d h ε w / refDensity d h w *
      ∏ j ∈ E.map p.toEmbedding, signOf (ε j)) =
    ∑ ε : Fin d → Bool, rowDensity d h ε w / refDensity d h w *
      ∏ j ∈ E, signOf (ε j) := by
  let e := (Equiv.piCongrLeft (fun _ : Fin d => Bool) p).symm
  have hr (ε : Fin d → Bool) : rowDensity d h ε w = rowDensity d h (e ε) w := by
    unfold rowDensity
    congr 2
    congr 1
    exact (Equiv.sum_comp p (fun j => signOf (ε j))).symm
  have hc (ε : Fin d → Bool) :
      (∏ j ∈ E.map p.toEmbedding, signOf (ε j)) = ∏ j ∈ E, signOf (e ε j) := by
    simp [e, Finset.prod_map]
  exact Fintype.sum_equiv e _ _ (fun ε => by rw [hr ε, hc ε])

/-- Equal-size subsets have the same Walsh coefficient, by extending a subset bijection
into a coordinate permutation.  [For the stated data and conditions](hyp:d,h,w,E,T,hcard), [the stated conclusion holds](goal). -/
-- @node: rowDensity_character_card_symmetry
lemma rowDensity_character_card_symmetry (d : ℕ) (h w : ℝ)
    (E T : Finset (Fin d)) (hcard : E.card = T.card) :
    (∑ ε : Fin d → Bool, rowDensity d h ε w / refDensity d h w *
      ∏ j ∈ E, signOf (ε j)) =
    ∑ ε : Fin d → Bool, rowDensity d h ε w / refDensity d h w *
      ∏ j ∈ T, signOf (ε j) := by
  let e : E ≃ T := Fintype.equivOfCardEq (by simpa using hcard)
  let p : Equiv.Perm (Fin d) := e.extendSubtype
  have hm : E.map p.toEmbedding = T := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
      exact e.extendSubtype_mem i hi
    · intro hj
      let i := e.symm ⟨j, hj⟩
      apply Finset.mem_map.mpr
      refine ⟨i.val, i.property, ?_⟩
      change e.extendSubtype i.val = j
      rw [e.extendSubtype_apply_of_mem i.val i.property]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨j, hj⟩)
  rw [← hm]
  exact (rowDensity_character_relabel d h w p E).symm

/-- The canonical first-s coordinates have cardinality s for every s at most d.  [For the stated data and conditions](hyp:d,s,hs), [the stated conclusion holds](goal). -/
-- @node: initial_coordinates_card
lemma initial_coordinates_card (d s : ℕ) (hs : s ≤ d) :
    (Finset.univ.filter (fun j : Fin d => j.val < s)).card = s := by
  by_cases he : s = d
  · subst s
    simp
  · have hsd : s < d := lt_of_le_of_ne hs he
    have hf : Finset.univ.filter (fun j : Fin d => j.val < s) = Finset.Iio ⟨s, hsd⟩ := by
      ext j
      simp [Fin.lt_def]
    rw [hf, Fin.card_Iio]

/-- On positive reference density, the symmetric coefficient agrees with the coefficient
of any subset of the specified size.  [For the stated data and conditions](hyp:d,h,w,E,hw), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_eq_subset_coefficient
lemma walshCoeff_eq_subset_coefficient (d : ℕ) (h w : ℝ) (E : Finset (Fin d))
    (hw : 0 < refDensity d h w) :
    walshCoeff d h E.card w =
      ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool,
        rowDensity d h ε w / refDensity d h w * ∏ j ∈ E, signOf (ε j) := by
  rw [walshCoeff, if_neg (ne_of_gt hw)]
  congr 1
  apply rowDensity_character_card_symmetry
  apply initial_coordinates_card
  exact (Finset.card_le_card (Finset.subset_univ E)).trans_eq (by simp)

/-- The likelihood has its finite permutation-symmetric Walsh expansion.  [For the stated data and conditions](hyp:d,h,w,hw,ε), [the stated conclusion holds](goal). -/
-- @node: rowDensity_walsh_expansion
lemma rowDensity_walsh_expansion (d : ℕ) (h w : ℝ) (hw : 0 < refDensity d h w)
    (ε : Fin d → Bool) :
    rowDensity d h ε w / refDensity d h w =
      ∑ E : Finset (Fin d), walshCoeff d h E.card w * ∏ j ∈ E, signOf (ε j) := by
  simp_rw [walshCoeff_eq_subset_coefficient d h w _ hw]
  exact finite_walsh_inversion d (fun δ => rowDensity d h δ w / refDensity d h w) ε

/-- The global square-root Lipschitz bound controls the squared difference of baseline
 densities, including points crossing the boundary of their support.  [For the stated data and conditions](hyp:x,y), [the stated conclusion holds](goal). -/
-- @node: cosSqDensity_difference_sq_le
lemma cosSqDensity_difference_sq_le (x y : ℝ) :
    (cosSqDensity x - cosSqDensity y) ^ 2 ≤
      32 * Real.pi ^ 2 * (x - y) ^ 2 * (cosSqDensity x + cosSqDensity y) := by
  have hl := baseline_translation_affinity.1.dist_le_mul x y
  simp only [Real.dist_eq, Real.coe_toNNReal (4 * Real.pi) (by positivity : 0 ≤ 4 * Real.pi)] at hl
  have hdiff : (Real.sqrt (cosSqDensity x) - Real.sqrt (cosSqDensity y)) ^ 2 ≤
      (4 * Real.pi) ^ 2 * (x - y) ^ 2 := by
    have hsq := mul_self_le_mul_self (abs_nonneg _) hl
    simpa only [← sq, mul_pow, sq_abs] using hsq
  have hx := Real.sq_sqrt (cosSqDensity_nonneg x)
  have hy := Real.sq_sqrt (cosSqDensity_nonneg y)
  have hsum : (Real.sqrt (cosSqDensity x) + Real.sqrt (cosSqDensity y)) ^ 2 ≤
      2 * (cosSqDensity x + cosSqDensity y) := by
    nlinarith [sq_nonneg (Real.sqrt (cosSqDensity x) - Real.sqrt (cosSqDensity y))]
  calc
    (cosSqDensity x - cosSqDensity y) ^ 2 =
        (Real.sqrt (cosSqDensity x) - Real.sqrt (cosSqDensity y)) ^ 2 *
          (Real.sqrt (cosSqDensity x) + Real.sqrt (cosSqDensity y)) ^ 2 := by
      calc
        _ = (Real.sqrt (cosSqDensity x) ^ 2 - Real.sqrt (cosSqDensity y) ^ 2) ^ 2 := by rw [hx, hy]
        _ = _ := by ring
    _ ≤ ((4 * Real.pi) ^ 2 * (x - y) ^ 2) *
        (2 * (cosSqDensity x + cosSqDensity y)) :=
      mul_le_mul hdiff hsum (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- Reversing one Boolean sign changes the row's sign sum by twice that sign.  [For the stated data and conditions](hyp:d,ε,j), [the stated conclusion holds](goal). -/
-- @node: row_sign_sum_flip
lemma row_sign_sum_flip (d : ℕ) (ε : Fin d → Bool) (j : Fin d) :
    (∑ i, signOf (Function.update ε j (!(ε j)) i)) =
      (∑ i, signOf (ε i)) - 2 * signOf (ε j) := by
  have hs : signOf (!(ε j)) = -signOf (ε j) := by
    cases ε j <;> norm_num [signOf]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self, hs]
  have he : (∑ i ∈ Finset.univ.erase j, signOf (Function.update ε j (!(ε j)) i)) =
      ∑ i ∈ Finset.univ.erase j, signOf (ε i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [he]
  ring

/-- The single-sign flip estimate used in the order-weighted Walsh energy proof.  [For the stated data and conditions](hyp:d,h,w,hd,ε,j), [the stated conclusion holds](goal). -/
-- @node: rowDensity_flip_difference_sq_le
lemma rowDensity_flip_difference_sq_le (d : ℕ) (h w : ℝ) (hd : 1 ≤ d)
    (ε : Fin d → Bool) (j : Fin d) :
    (rowDensity d h ε w - rowDensity d h (Function.update ε j (!(ε j))) w) ^ 2 ≤
      (32 * Real.pi ^ 2 * h ^ 2 / (d : ℝ) ^ 2) *
        (rowDensity d h ε w + rowDensity d h (Function.update ε j (!(ε j))) w) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have he : ((w - h / (2 * d) * ∑ i, signOf (ε i)) -
      (w - h / (2 * d) * ∑ i, signOf (Function.update ε j (!(ε j)) i))) ^ 2 =
      h ^ 2 / (d : ℝ) ^ 2 := by
    rw [row_sign_sum_flip]
    have hs : signOf (ε j) ^ 2 = 1 := by cases ε j <;> norm_num [signOf]
    field_simp
    nlinarith [hs]
  have hb := cosSqDensity_difference_sq_le
    (w - h / (2 * d) * ∑ i, signOf (ε i))
    (w - h / (2 * d) * ∑ i, signOf (Function.update ε j (!(ε j)) i))
  rw [he] at hb
  simpa only [rowDensity, mul_div_assoc] using hb

/-- Reversing one coordinate permutes the Boolean cube, so it preserves the density sum.  [For the stated data and conditions](hyp:d,h,w,j), [the stated conclusion holds](goal). -/
-- @node: rowDensity_sum_flip
lemma rowDensity_sum_flip (d : ℕ) (h w : ℝ) (j : Fin d) :
    (∑ ε : Fin d → Bool, rowDensity d h (Function.update ε j (!(ε j))) w) =
      ∑ ε : Fin d → Bool, rowDensity d h ε w := by
  let flip := fun ε : Fin d → Bool => Function.update ε j (!(ε j))
  have hinv : Function.Involutive flip := by
    intro ε
    funext i
    by_cases hi : i = j
    · subst i; simp [flip]
    · simp [flip, Function.update_of_ne hi]
  let e : (Fin d → Bool) ≃ (Fin d → Bool) :=
    ⟨flip, flip, hinv, hinv⟩
  exact e.sum_comp (fun ε => rowDensity d h ε w)

/-- Averaging the single-coordinate differences cancels the reference denominator.
At zero reference density every summand is zero.  [For the stated data and conditions](hyp:d,h,w,hd,j), [the stated conclusion holds](goal). -/
-- @node: rowDensity_flip_average_le
lemma rowDensity_flip_average_le (d : ℕ) (h w : ℝ) (hd : 1 ≤ d) (j : Fin d) :
    ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool,
      (rowDensity d h ε w - rowDensity d h (Function.update ε j (!(ε j))) w) ^ 2 /
        refDensity d h w ≤ 64 * Real.pi ^ 2 * h ^ 2 / (d : ℝ) ^ 2 := by
  by_cases hw : refDensity d h w = 0
  · simp only [hw, div_zero, Finset.sum_const_zero, mul_zero]
    positivity
  · have hp := lt_of_le_of_ne (refDensity_nonneg d h w) (Ne.symm hw)
    have hb : (∑ ε : Fin d → Bool,
        (rowDensity d h ε w - rowDensity d h (Function.update ε j (!(ε j))) w) ^ 2) ≤
        (32 * Real.pi ^ 2 * h ^ 2 / (d : ℝ) ^ 2) *
          (2 * ∑ ε : Fin d → Bool, rowDensity d h ε w) := by
      calc
        _ ≤ ∑ ε : Fin d → Bool, (32 * Real.pi ^ 2 * h ^ 2 / (d : ℝ) ^ 2) *
            (rowDensity d h ε w + rowDensity d h (Function.update ε j (!(ε j))) w) :=
          Finset.sum_le_sum (fun ε _ => rowDensity_flip_difference_sq_le d h w hd ε j)
        _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib, rowDensity_sum_flip]; ring
    rw [← Finset.sum_div, ← mul_div_assoc]
    apply (div_le_iff₀ hp).2
    have hc := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ ((2 : ℝ) ^ d)⁻¹)
    calc
      _ ≤ _ := hc
      _ = (64 * Real.pi ^ 2 * h ^ 2 / (d : ℝ) ^ 2) * refDensity d h w := by
        unfold refDensity; ring

/-- The row's centered sign sum is bounded by its number of coordinates.  [For the stated data and conditions](hyp:d,ε), [the stated conclusion holds](goal). -/
-- @node: row_sign_sum_abs_le
lemma row_sign_sum_abs_le (d : ℕ) (ε : Fin d → Bool) :
    |∑ j, signOf (ε j)| ≤ (d : ℝ) := by
  calc
    _ ≤ ∑ j, |signOf (ε j)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      have hs (j : Fin d) : |signOf (ε j)| = 1 := by cases ε j <;> norm_num [signOf]
      simp_rw [hs]
      simp

/-- All shifted row densities vanish outside the common enlarged baseline support.  [For the stated data and conditions](hyp:d,h,w,hd,hh,ε,hw), [the stated conclusion holds](goal). -/
-- @node: rowDensity_eq_zero_outside
lemma rowDensity_eq_zero_outside (d : ℕ) (h w : ℝ) (hd : 1 ≤ d) (hh : 0 ≤ h)
    (ε : Fin d → Bool) (hw : 1 / 4 + h / 2 < |w|) : rowDensity d h ε w = 0 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hshift : |h / (2 * d) * ∑ j, signOf (ε j)| ≤ h / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ h / (2 * (d : ℝ)))]
    calc
      _ ≤ h / (2 * d) * d := mul_le_mul_of_nonneg_left (row_sign_sum_abs_le d ε) (by positivity)
      _ = _ := by field_simp
  have hout : ¬ |w - h / (2 * d) * ∑ j, signOf (ε j)| ≤ 1 / 4 := by
    intro hin
    have ht := abs_add_le (w - h / (2 * d) * ∑ j, signOf (ε j))
      (h / (2 * d) * ∑ j, signOf (ε j))
    rw [sub_add_cancel] at ht
    linarith
  exact if_neg hout

/-- The reference density has the same common compact support as its shifted components.  [For the stated data and conditions](hyp:d,h,w,hd,hh,hw), [the stated conclusion holds](goal). -/
-- @node: refDensity_eq_zero_outside
lemma refDensity_eq_zero_outside (d : ℕ) (h w : ℝ) (hd : 1 ≤ d) (hh : 0 ≤ h)
    (hw : 1 / 4 + h / 2 < |w|) : refDensity d h w = 0 := by
  simp [refDensity, rowDensity_eq_zero_outside d h w hd hh _ hw]

/-- The averaged squared density difference under a single coordinate reversal. -/
-- @node: flipEnergy
def flipEnergy (d : ℕ) (h : ℝ) (j : Fin d) (w : ℝ) : ℝ :=
  ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool,
    (rowDensity d h ε w - rowDensity d h (Function.update ε j (!(ε j))) w) ^ 2 /
      refDensity d h w

/-- The averaged flip energy is nonnegative, including at zero reference density.  [For the stated data and conditions](hyp:d,h,w,j), [the stated conclusion holds](goal). -/
-- @node: flipEnergy_nonneg
lemma flipEnergy_nonneg (d : ℕ) (h w : ℝ) (j : Fin d) :
    0 ≤ flipEnergy d h j w := by
  unfold flipEnergy
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun ε _ =>
    div_nonneg (sq_nonneg _) (refDensity_nonneg d h w)))

/-- [A translated baseline row is measurable across the support boundary.](goal) -/
-- @node: rowDensity_measurable
@[fun_prop]
lemma rowDensity_measurable (d : ℕ) (h : ℝ) (ε : Fin d → Bool) :
    Measurable (rowDensity d h ε) := by
  unfold rowDensity cosSqDensity
  have hs : MeasurableSet {w : ℝ | |w - h / (2 * d) * ∑ j, signOf (ε j)| ≤ 1 / 4} :=
    measurableSet_le (by fun_prop) measurable_const
  exact Measurable.ite hs (by fun_prop) measurable_const

/-- [A finite average of the measurable row densities is measurable.](goal) -/
-- @node: refDensity_measurable
@[fun_prop]
lemma refDensity_measurable (d : ℕ) (h : ℝ) : Measurable (refDensity d h) := by
  unfold refDensity
  fun_prop

/-- [The averaged flip energy is measurable despite division at reference-density zeros.](goal) -/
-- @node: flipEnergy_measurable
@[fun_prop]
lemma flipEnergy_measurable (d : ℕ) (h : ℝ) (j : Fin d) :
    Measurable (flipEnergy d h j) := by
  unfold flipEnergy
  fun_prop

/-- The pointwise flip estimate is dominated by a constant on the common support interval.  [For the stated data and conditions](hyp:d,h,hd,hh,j,w), [the stated conclusion holds](goal). -/
-- @node: flipEnergy_le_indicator
lemma flipEnergy_le_indicator (d : ℕ) (h : ℝ) (hd : 1 ≤ d) (hh : 0 ≤ h)
    (j : Fin d) (w : ℝ) :
    flipEnergy d h j w ≤
      (Set.Icc (-(1 / 4 + h / 2)) (1 / 4 + h / 2)).indicator
        (fun _ => 64 * Real.pi ^ 2 * h ^ 2 / (d : ℝ) ^ 2) w := by
  by_cases hw : w ∈ Set.Icc (-(1 / 4 + h / 2)) (1 / 4 + h / 2)
  · rw [Set.indicator_of_mem hw]
    exact rowDensity_flip_average_le d h w hd j
  · rw [Set.indicator_of_notMem hw]
    have hout : 1 / 4 + h / 2 < |w| := lt_of_not_ge (by
      simpa only [abs_le, Set.mem_Icc] using hw)
    have hz := refDensity_eq_zero_outside d h w hd hh hout
    simp [flipEnergy, hz]

/-- Compact support and the flip estimate supply integrability without an extra premise.  [For the stated data and conditions](hyp:d,h,hd,hh,j), [the stated conclusion holds](goal). -/
-- @node: flipEnergy_integrable
lemma flipEnergy_integrable (d : ℕ) (h : ℝ) (hd : 1 ≤ d) (hh : 0 ≤ h)
    (j : Fin d) : Integrable (flipEnergy d h j) := by
  have hi : Integrable ((Set.Icc (-(1 / 4 + h / 2)) (1 / 4 + h / 2)).indicator
      (fun _ : ℝ => 64 * Real.pi ^ 2 * h ^ 2 / (d : ℝ) ^ 2)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const measure_Icc_lt_top.ne)
  apply hi.mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun w => by
    rw [Real.norm_eq_abs, abs_of_nonneg (flipEnergy_nonneg d h w j)]
    exact flipEnergy_le_indicator d h hd hh j w)

/-- Integrating the flip bound costs only the support length, at most three quarters.  [For the stated data and conditions](hyp:d,h,hd,hh,j), [the stated conclusion holds](goal). -/
-- @node: integral_flipEnergy_le
lemma integral_flipEnergy_le (d : ℕ) (h : ℝ) (hd : 1 ≤ d)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (j : Fin d) :
    (∫ w, flipEnergy d h j w) ≤ 48 * Real.pi ^ 2 * h ^ 2 / (d : ℝ) ^ 2 := by
  have hi : Integrable ((Set.Icc (-(1 / 4 + h / 2)) (1 / 4 + h / 2)).indicator
      (fun _ : ℝ => 64 * Real.pi ^ 2 * h ^ 2 / (d : ℝ) ^ 2)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const measure_Icc_lt_top.ne)
  calc
    _ ≤ ∫ w, (Set.Icc (-(1 / 4 + h / 2)) (1 / 4 + h / 2)).indicator
        (fun _ : ℝ => 64 * Real.pi ^ 2 * h ^ 2 / (d : ℝ) ^ 2) w :=
      integral_mono (flipEnergy_integrable d h hd hh.1 j) hi
        (flipEnergy_le_indicator d h hd hh.1 j)
    _ = (1 / 2 + h) * (64 * Real.pi ^ 2 * h ^ 2 / (d : ℝ) ^ 2) := by
      rw [integral_indicator_const _ measurableSet_Icc,
        Real.volume_real_Icc_of_le (by linarith [hh.1])]
      simp only [smul_eq_mul]
      ring
    _ ≤ _ := by
      have hc : 0 ≤ 64 * Real.pi ^ 2 * h ^ 2 / (d : ℝ) ^ 2 := by positivity
      have hb := mul_le_mul_of_nonneg_right (show 1 / 2 + h ≤ (3 / 4 : ℝ) by
        linarith [hh.2]) hc
      convert hb using 1 <;> first | rfl | ring

/-- The sum of the integrated coordinate flips has the desired weighted-energy bound.  [For the stated data and conditions](hyp:d,h,hd,hh), [the stated conclusion holds](goal). -/
-- @node: integrated_flip_sum_le
lemma integrated_flip_sum_le (d : ℕ) (h : ℝ) (hd : 1 ≤ d)
    (hh : h ∈ Set.Icc 0 (1 / 4)) :
    (1 / 4 : ℝ) * ∑ j : Fin d, (∫ w, flipEnergy d h j w) ≤
      12 * Real.pi ^ 2 * h ^ 2 / d := by
  have hb := Finset.sum_le_sum (s := Finset.univ)
    (fun (j : Fin d) _ => integral_flipEnergy_le d h hd hh j)
  have hc := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 1 / 4)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hc
  convert hc using 1 <;> first | rfl | skip
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  field_simp
  ring

/-- At zero amplitude the reference density is the unshifted baseline.  [For the stated data and conditions](hyp:d,w), [the stated conclusion holds](goal). -/
-- @node: refDensity_zero_amplitude
lemma refDensity_zero_amplitude (d : ℕ) (w : ℝ) : refDensity d 0 w = cosSqDensity w := by
  simp only [refDensity, rowDensity, zero_div, zero_mul, sub_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- At zero amplitude all nonconstant Walsh coefficients vanish pointwise.  [For the stated data and conditions](hyp:d,s,w,hd,hs), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_zero_amplitude
lemma walshCoeff_zero_amplitude (d s : ℕ) (w : ℝ) (hd : 1 ≤ d) (hs : 1 ≤ s) :
    walshCoeff d 0 s w = 0 := by
  by_cases hw : refDensity d 0 w = 0
  · simp [walshCoeff, hw]
  · rw [walshCoeff, if_neg hw]
    simp only [rowDensity, zero_div, zero_mul, sub_zero]
    rw [← Finset.mul_sum, sign_character_sum_eq_zero, mul_zero, mul_zero]
    refine ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa using (show 0 < s by omega)

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
