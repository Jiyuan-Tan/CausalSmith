module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Legal cosine priors and pair-feature isotropy

Legality is a conclusion over the constructed polynomial, never a free assumption.
The fixed normalization is independent of every sample and dimension parameter.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Positive integer cosine frequencies have zero mean on the unit interval.](goal) Under [the stated conditions](hyp:ha). -/
-- @node: uniform_cosine_mean_zero
lemma uniform_cosine_mean_zero (a : ℕ) (ha : 0 < a) :
    (∫ u, Real.cos (Real.pi * (a : ℝ) * u)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 0 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_comp_mul_left Real.cos
    (by positivity : Real.pi * (a : ℝ) ≠ 0)]
  have hsin : Real.sin (Real.pi * (a : ℝ)) = 0 := by
    rw [mul_comm]
    exact Real.sin_nat_mul_pi a
  simp [integral_cos, hsin]

/-- Integer cosine frequencies integrate to the constant-frequency indicator. [The asserted mathematical result follows](goal). -/
-- @node: uniform_integer_cosine_mean
lemma uniform_integer_cosine_mean (a : ℤ) :
    (∫ u, Real.cos (Real.pi * (a : ℝ) * u)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = if a = 0 then 1 else 0 := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [if_neg ha, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [intervalIntegral.integral_comp_mul_left Real.cos
      (mul_ne_zero Real.pi_ne_zero (by exact_mod_cast ha))]
    have hsin : Real.sin (Real.pi * (a : ℝ)) = 0 := by
      rw [mul_comm]
      exact Real.sin_int_mul_pi a
    simp [integral_cos, hsin]

/-- The one-dimensional positive-frequency cosine inner products are exactly diagonal. Under [the stated conditions](hyp:ha,hb), [the asserted mathematical result follows](goal). -/
-- @node: uniform_cosine_inner_product
lemma uniform_cosine_inner_product (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∫ u, Real.cos (Real.pi * (a : ℝ) * u) * Real.cos (Real.pi * (b : ℝ) * u)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = if a = b then (1 / 2 : ℝ) else 0 := by
  have hidentity (u : ℝ) :
      Real.cos (Real.pi * (a : ℝ) * u) * Real.cos (Real.pi * (b : ℝ) * u) =
        (1 / 2 : ℝ) * (Real.cos (Real.pi * ((a : ℤ) - b : ℤ) * u) +
          Real.cos (Real.pi * ((a : ℤ) + b : ℤ) * u)) := by
    push_cast
    rw [show Real.pi * ((a : ℝ) - b) * u = Real.pi * a * u - Real.pi * b * u by ring,
      show Real.pi * ((a : ℝ) + b) * u = Real.pi * a * u + Real.pi * b * u by ring,
      Real.cos_sub, Real.cos_add]
    ring
  have hi (k : ℤ) : Integrable (fun u => Real.cos (Real.pi * (k : ℝ) * u))
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    exact Continuous.integrableOn_Icc (by fun_prop)
  simp_rw [hidentity]
  rw [integral_const_mul, integral_add (hi _) (hi _),
    uniform_integer_cosine_mean, uniform_integer_cosine_mean]
  have hab : (a : ℤ) + b ≠ 0 := by omega
  simp [hab, sub_eq_zero]

/-- Every pair-cosine feature is Borel. This uses [the stated conclusion](goal). -/
-- @node: pairFeature_measurable
@[fun_prop] lemma pairFeature_measurable {d L : ℕ} (α : PairIdx d L) :
    Measurable (pairFeature α) := by
  unfold pairFeature
  fun_prop

/-- Pair-cosine features are bounded by two on the entire ambient space. [The asserted mathematical result follows](goal). -/
-- @node: pairFeature_abs_le_two
lemma pairFeature_abs_le_two {d L : ℕ} (α : PairIdx d L) (x : Cube d) :
    |pairFeature α x| ≤ 2 := by
  unfold pairFeature
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [Real.abs_cos_le_one (Real.pi * (α.val.2.1.val + 1 : ℕ) * x α.val.1.1),
    Real.abs_cos_le_one (Real.pi * (α.val.2.2.val + 1 : ℕ) * x α.val.1.2),
    abs_nonneg (Real.cos (Real.pi * (α.val.2.1.val + 1 : ℕ) * x α.val.1.1)),
    abs_nonneg (Real.cos (Real.pi * (α.val.2.2.val + 1 : ℕ) * x α.val.1.2))]

/-- [ Every pair feature is square-integrable under cube sampling.](goal) -/
-- @node: pairFeature_memLp
lemma pairFeature_memLp {d L : ℕ} (α : PairIdx d L) :
    MemLp (pairFeature α) 2 (cubeMeasure d) := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  exact MemLp.of_bound (pairFeature_measurable α).aestronglyMeasurable 2
    (Filter.Eventually.of_forall (fun x => by
      simpa [Real.norm_eq_abs] using pairFeature_abs_le_two α x))

/-- Distinct cube coordinates factor the mean of two scalar functions. Under [the stated conditions](hyp:hjl), [the asserted mathematical result follows](goal). -/
-- @node: cube_integral_two_coordinates
lemma cube_integral_two_coordinates {d : ℕ} (j l : Fin d) (hjl : j ≠ l)
    (f g : ℝ → ℝ) :
    (∫ x, f (x j) * g (x l) ∂cubeMeasure d) =
      (∫ u, f u ∂volume.restrict (Icc (0 : ℝ) 1)) *
      (∫ u, g u ∂volume.restrict (Icc (0 : ℝ) 1)) := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  let factors := fun i : Fin d => fun u : ℝ =>
    (if i = j then f u else 1) * (if i = l then g u else 1)
  have hprod (x : Cube d) : (∏ i, factors i (x i)) = f (x j) * g (x l) := by
    dsimp [factors]
    rw [Finset.prod_mul_distrib]
    simp
  rw [show (fun x : Cube d => f (x j) * g (x l)) =
    (fun x => ∏ i, factors i (x i)) from funext (fun x => (hprod x).symm)]
  rw [cubeMeasure, integral_fintype_prod_eq_prod]
  have hfactor (i : Fin d) : (∫ u, factors i u ∂volume.restrict (Icc (0 : ℝ) 1)) =
      (if i = j then ∫ u, f u ∂volume.restrict (Icc (0 : ℝ) 1) else 1) *
      (if i = l then ∫ u, g u ∂volume.restrict (Icc (0 : ℝ) 1) else 1) := by
    by_cases hij : i = j <;> by_cases hil : i = l <;>
      simp_all [factors]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp

/-- Pair features are centered, including when the ambient dimension is larger than two. [The asserted mathematical result follows](goal). -/
-- @node: pairFeature_mean_zero
lemma pairFeature_mean_zero {d L : ℕ} (α : PairIdx d L) :
    (∫ x, pairFeature α x ∂cubeMeasure d) = 0 := by
  unfold pairFeature
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  simp_rw [← mul_assoc]
  rw [cube_integral_two_coordinates _ _ (ne_of_lt α.property)
    (fun u => Real.cos (Real.pi * (α.val.2.1.val + 1 : ℕ) * u))
    (fun u => Real.cos (Real.pi * (α.val.2.2.val + 1 : ℕ) * u))]
  rw [uniform_cosine_mean_zero _ (Nat.succ_pos _)]
  simp

/-- Features on one original coordinate pair have diagonal frequency inner products. Under [the stated conditions](hyp:hj,hl), [the asserted mathematical result follows](goal). -/
-- @node: pairFeature_same_pair_inner_product
lemma pairFeature_same_pair_inner_product {d L : ℕ} (α β : PairIdx d L)
    (hj : α.val.1.1 = β.val.1.1) (hl : α.val.1.2 = β.val.1.2) :
    (∫ x, pairFeature α x * pairFeature β x ∂cubeMeasure d) =
      if α = β then 1 else 0 := by
  have hidentity (x : Cube d) : pairFeature α x * pairFeature β x =
      4 * ((Real.cos (Real.pi * (α.val.2.1.val + 1 : ℕ) * x α.val.1.1) *
        Real.cos (Real.pi * (β.val.2.1.val + 1 : ℕ) * x α.val.1.1)) *
      (Real.cos (Real.pi * (α.val.2.2.val + 1 : ℕ) * x α.val.1.2) *
        Real.cos (Real.pi * (β.val.2.2.val + 1 : ℕ) * x α.val.1.2))) := by
    simp only [pairFeature, ← hj, ← hl]
    ring
  simp_rw [hidentity]
  rw [integral_const_mul, cube_integral_two_coordinates _ _ (ne_of_lt α.property)
    (fun u => Real.cos (Real.pi * (α.val.2.1.val + 1 : ℕ) * u) *
      Real.cos (Real.pi * (β.val.2.1.val + 1 : ℕ) * u))
    (fun u => Real.cos (Real.pi * (α.val.2.2.val + 1 : ℕ) * u) *
      Real.cos (Real.pi * (β.val.2.2.val + 1 : ℕ) * u))]
  rw [uniform_cosine_inner_product _ _ (Nat.succ_pos _) (Nat.succ_pos _),
    uniform_cosine_inner_product _ _ (Nat.succ_pos _) (Nat.succ_pos _)]
  have heq : α = β ↔ α.val.2.1 = β.val.2.1 ∧ α.val.2.2 = β.val.2.2 := by
    constructor
    · intro h
      subst β
      exact ⟨rfl, rfl⟩
    · rintro ⟨ha, hb⟩
      apply Subtype.ext
      exact Prod.ext (Prod.ext hj hl) (Prod.ext ha hb)
  by_cases ha : α.val.2.1 = β.val.2.1 <;>
    by_cases hb : α.val.2.2 = β.val.2.2 <;>
    norm_num [heq, ha, hb, Nat.add_right_cancel_iff, Fin.val_inj]

/-- [ A coordinate appearing in only one pair makes the two features orthogonal.](goal) Under [the stated conditions](hyp:h). -/
-- @node: pairFeature_unmatched_inner_product
lemma pairFeature_unmatched_inner_product {d L : ℕ} (α β : PairIdx d L)
    (h : ∃ j : Fin d, (j = α.val.1.1 ∨ j = α.val.1.2) ∧
      j ≠ β.val.1.1 ∧ j ≠ β.val.1.2) :
    (∫ x, pairFeature α x * pairFeature β x ∂cubeMeasure d) = 0 := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  let factors := fun i : Fin d => fun u : ℝ =>
    ((if i = α.val.1.1 then Real.cos (Real.pi * (α.val.2.1.val + 1 : ℕ) * u) else 1) *
      (if i = α.val.1.2 then Real.cos (Real.pi * (α.val.2.2.val + 1 : ℕ) * u) else 1)) *
    ((if i = β.val.1.1 then Real.cos (Real.pi * (β.val.2.1.val + 1 : ℕ) * u) else 1) *
      (if i = β.val.1.2 then Real.cos (Real.pi * (β.val.2.2.val + 1 : ℕ) * u) else 1))
  have hprod (x : Cube d) : pairFeature α x * pairFeature β x =
      4 * ∏ i, factors i (x i) := by
    dsimp [factors]
    simp only [Finset.prod_mul_distrib]
    simp only [Nat.cast_add, Nat.cast_one, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    unfold pairFeature
    push_cast
    ring_nf
  simp_rw [hprod]
  rw [integral_const_mul, cubeMeasure, integral_fintype_prod_eq_prod]
  obtain ⟨j, hj, hbj, hbl⟩ := h
  have hz : (∫ u, factors j u ∂volume.restrict (Icc (0 : ℝ) 1)) = 0 := by
    rcases hj with rfl | rfl
    · have hal : α.val.1.1 ≠ α.val.1.2 := ne_of_lt α.property
      simpa [factors, hal, hbj, hbl] using
        uniform_cosine_mean_zero (α.val.2.1.val + 1) (Nat.succ_pos _)
    · have haj : α.val.1.2 ≠ α.val.1.1 := (ne_of_lt α.property).symm
      simpa [factors, haj, hbj, hbl] using
        uniform_cosine_mean_zero (α.val.2.2.val + 1) (Nat.succ_pos _)
  rw [Finset.prod_eq_zero (Finset.mem_univ j) hz, mul_zero]

/-- All pair-cosine coordinates are jointly isotropic under the cube law. [The asserted mathematical result follows](goal). -/
-- @node: pairFeature_cube_inner_product
lemma pairFeature_cube_inner_product {d L : ℕ} (α β : PairIdx d L) :
    (∫ x, pairFeature α x * pairFeature β x ∂cubeMeasure d) =
      if α = β then 1 else 0 := by
  by_cases hj : α.val.1.1 = β.val.1.1
  · by_cases hl : α.val.1.2 = β.val.1.2
    · exact pairFeature_same_pair_inner_product α β hj hl
    · have hne : α ≠ β := by intro he; exact hl (congrArg (fun a => a.val.1.2) he)
      rw [if_neg hne]
      apply pairFeature_unmatched_inner_product
      refine ⟨α.val.1.2, Or.inr rfl, ?_, hl⟩
      rw [← hj]
      exact (ne_of_lt α.property).symm
  · have hne : α ≠ β := by intro he; exact hj (congrArg (fun a => a.val.1.1) he)
    rw [if_neg hne]
    apply pairFeature_unmatched_inner_product
    by_cases hcross : α.val.1.1 = β.val.1.2
    · refine ⟨α.val.1.2, Or.inr rfl, ?_, ?_⟩
      · exact ne_of_gt (lt_trans β.property (hcross ▸ α.property))
      · rw [← hcross]
        exact (ne_of_lt α.property).symm
    · exact ⟨α.val.1.1, Or.inl rfl, hj, hcross⟩

/-- [ The feature index really has the prescribed dimension, including pairs that
share an original coordinate.](goal) -/
-- @node: pairIdx_card
lemma pairIdx_card (d L : ℕ) : Fintype.card (PairIdx d L) = priorDimension d L := by
  let e : PairIdx d L ≃ {jl : Fin d × Fin d // jl.1 < jl.2} × (Fin L × Fin L) :=
    { toFun := fun α => (⟨α.val.1, α.property⟩, α.val.2)
      invFun := fun α => ⟨(α.1.val, α.2), α.1.property⟩
      left_inv := by intro α; rfl
      right_inv := by intro α; rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod]
  have hpair : Fintype.card {jl : Fin d × Fin d // jl.1 < jl.2} = d.choose 2 := by
    rw [Fintype.card_subtype]
    simpa only [Fintype.card_fin] using
      (Fintype.card_product_filter_lt (α := Fin d))
  simp only [hpair, Fintype.card_fin, priorDimension, pairCount, pow_two]

/-- [ The feature inner product extracts a coefficient from any finite cosine expansion.](goal) -/
-- @node: pairFeature_expansion_inner_product
lemma pairFeature_expansion_inner_product {d L : ℕ} (c : PairIdx d L → ℝ)
    (β : PairIdx d L) :
    (∫ x, (∑ α, c α * pairFeature α x) * pairFeature β x ∂cubeMeasure d) = c β := by
  classical
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum (f := fun α x => c α * (pairFeature α x * pairFeature β x))
    Finset.univ (fun α _ =>
    ((pairFeature_memLp α).integrable_mul (pairFeature_memLp β)).const_mul (c α))]
  simp_rw [integral_const_mul, pairFeature_cube_inner_product]
  simp

/-- [ The squared energy of a finite pair-cosine polynomial is its coefficient energy.](goal) -/
-- @node: pairFeature_expansion_second_moment
lemma pairFeature_expansion_second_moment {d L : ℕ} (c : PairIdx d L → ℝ) :
    (∫ x, (∑ α, c α * pairFeature α x) ^ 2 ∂cubeMeasure d) = ∑ α, c α ^ 2 := by
  classical
  have hg : MemLp (fun x => ∑ α, c α * pairFeature α x) 2 (cubeMeasure d) := by
    exact memLp_finsetSum _ (fun α _ => (pairFeature_memLp α).const_mul (c α))
  simp_rw [pow_two]
  simp_rw [Finset.mul_sum]
  simp_rw [show ∀ α x, (∑ β, c β * pairFeature β x) * (c α * pairFeature α x) =
    c α * ((∑ β, c β * pairFeature β x) * pairFeature α x) by intros; ring]
  rw [integral_finsetSum (f := fun α x =>
    c α * ((∑ β, c β * pairFeature β x) * pairFeature α x)) Finset.univ (fun α _ =>
    (hg.integrable_mul (pairFeature_memLp α)).const_mul (c α))]
  simp_rw [integral_const_mul, pairFeature_expansion_inner_product]

/-- [ Fixing one coordinate of a pair feature leaves a centered factor to integrate out.](goal) -/
-- @node: pairFeature_g1_zero
lemma pairFeature_g1_zero {d L : ℕ} (α : PairIdx d L) (j : Fin d) (u : ℝ) :
    g1 (pairFeature α) j u = 0 := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  have hjl : α.val.1.1 ≠ α.val.1.2 := ne_of_lt α.property
  have hcoord (l : Fin d) (a : ℕ) (ha : 0 < a) :
      (∫ y : Cube d, Real.cos (Real.pi * (a : ℝ) * y l) ∂cubeMeasure d) = 0 := by
    rw [cubeMeasure, integral_comp_eval (f := fun u : ℝ => Real.cos (Real.pi * (a : ℝ) * u))
      (μ := fun _ : Fin d => volume.restrict (Icc (0 : ℝ) 1)) (i := l) (by fun_prop)]
    exact uniform_cosine_mean_zero a ha
  by_cases hj : α.val.1.1 = j
  · simp only [g1, pairFeature, Function.update_apply, hj, if_true,
      show α.val.1.2 ≠ j from hj ▸ hjl.symm, if_false]
    rw [integral_const_mul, hcoord _ _ (Nat.succ_pos _), mul_zero]
  · by_cases hl : α.val.1.2 = j
    · simp only [g1, pairFeature, Function.update_apply, hj, hl, if_false, if_true]
      rw [integral_mul_const, integral_const_mul, hcoord _ _ (Nat.succ_pos _)]
      simp
    · simpa only [g1, pairFeature, Function.update_apply, hj, hl, if_false] using
        pairFeature_mean_zero α

/-- [ Fixing coordinates in a finite feature sum preserves integrability.](goal) -/
-- @node: pairFeature_update_integrable
lemma pairFeature_update_integrable {d L : ℕ} (α : PairIdx d L)
    (j : Fin d) (u : ℝ) :
    Integrable (fun y : Cube d => pairFeature α (Function.update y j u)) (cubeMeasure d) := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  apply Integrable.of_bound (by unfold pairFeature; fun_prop) 2
  exact Filter.Eventually.of_forall (fun y => by
    simpa only [Real.norm_eq_abs] using pairFeature_abs_le_two α (Function.update y j u))

/-- A canonical pair marginal retains exactly the feature on that ordered coordinate pair. Under [the stated conditions](hyp:hjl), [the asserted mathematical result follows](goal). -/
-- @node: pairFeature_g2
lemma pairFeature_g2 {d L : ℕ} (α : PairIdx d L) (j l : Fin d)
    (hjl : j < l) (u v : ℝ) :
    g2 (pairFeature α) j l u v =
      if α.val.1.1 = j ∧ α.val.1.2 = l then
        2 * Real.cos (Real.pi * (α.val.2.1.val + 1 : ℕ) * u) *
          Real.cos (Real.pi * (α.val.2.2.val + 1 : ℕ) * v) else 0 := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  have hi (k : Fin d) (a : ℕ) (ha : 0 < a) :
      (∫ t, Real.cos (Real.pi * (a : ℝ) *
        (if k = l then v else if k = j then u else t))
        ∂volume.restrict (Icc (0 : ℝ) 1)) =
      if k = l then Real.cos (Real.pi * (a : ℝ) * v) else
        if k = j then Real.cos (Real.pi * (a : ℝ) * u) else 0 := by
    by_cases hl : k = l <;> by_cases hj : k = j <;>
      simp [hl, hj, ne_of_lt hjl, uniform_cosine_mean_zero a ha]
  simp only [g2, pairFeature_g1_zero, sub_zero]
  unfold pairFeature
  simp only [Function.update_apply]
  conv_lhs => arg 2; ext y; rw [mul_assoc]
  rw [integral_const_mul, cube_integral_two_coordinates _ _ (ne_of_lt α.property)
    (fun t => Real.cos (Real.pi * (α.val.2.1.val + 1 : ℕ) *
      (if α.val.1.1 = l then v else if α.val.1.1 = j then u else t)))
    (fun t => Real.cos (Real.pi * (α.val.2.2.val + 1 : ℕ) *
      (if α.val.1.2 = l then v else if α.val.1.2 = j then u else t)))]
  rw [hi _ _ (Nat.succ_pos _), hi _ _ (Nat.succ_pos _)]
  have hα := α.property
  by_cases h1l : α.val.1.1 = l <;> by_cases h1j : α.val.1.1 = j <;>
    by_cases h2l : α.val.1.2 = l <;> by_cases h2j : α.val.1.2 = j <;>
    simp_all <;> first | omega | ring

/-- The finite pair marginals of a cosine expansion are well-defined integrals. [The asserted mathematical result follows](goal). -/
-- @node: pairFeature_two_updates_integrable
lemma pairFeature_two_updates_integrable {d L : ℕ} (α : PairIdx d L)
    (j l : Fin d) (u v : ℝ) :
    Integrable (fun y : Cube d =>
      pairFeature α (Function.update (Function.update y j u) l v)) (cubeMeasure d) := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  apply Integrable.of_bound (by unfold pairFeature; fun_prop) 2
  exact Filter.Eventually.of_forall (fun y => by
    simpa only [Real.norm_eq_abs] using
      pairFeature_abs_le_two α (Function.update (Function.update y j u) l v))

/-- Uniform-draw transport preserves the pair-feature inner products of any original unit. Under [the stated conditions](hyp:hX), [the asserted mathematical result follows](goal). -/
-- @node: uniformDraw_pairFeature_inner_product
lemma uniformDraw_pairFeature_inner_product {n d L : ℕ}
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → Covariates n d}
    (hX : UniformDraw μ X) (i : Fin n) (α β : PairIdx d L) :
    (∫ ω, pairFeature α (X ω i) * pairFeature β (X ω i) ∂μ) =
      if α = β then 1 else 0 := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  have hm : Measurable (fun x : Covariates n d => pairFeature α (x i) * pairFeature β (x i)) := by
    fun_prop
  rw [← integral_map hX.1.aemeasurable hm.aestronglyMeasurable, hX.2]
  rw [covLaw, integral_comp_eval (μ := fun _ : Fin n => cubeMeasure d) (i := i)
    (by fun_prop : AEStronglyMeasurable
    (fun x : Cube d => pairFeature α x * pairFeature β x) (cubeMeasure d))]
  exact pairFeature_cube_inner_product α β

/-- Finite coefficient realizations of the prior are Borel. This uses [the stated conclusion](goal). -/
-- @node: mXi_measurable
@[fun_prop] lemma mXi_measurable {d L : ℕ} (s : ℝ) (ξ : PairIdx d L → Bool) :
    Measurable (mXi s L ξ) := by
  unfold mXi
  fun_prop

/-- Finite coefficient realizations of the prior are square-integrable. [The asserted mathematical result follows](goal). -/
-- @node: mXi_memLp
lemma mXi_memLp {d L : ℕ} (s : ℝ) (ξ : PairIdx d L → Bool) :
    MemLp (mXi s L ξ) 2 (cubeMeasure d) := by
  unfold mXi
  simpa only [Finset.sum_apply] using
    (memLp_finsetSum' Finset.univ (fun α _ =>
      (pairFeature_memLp α).const_mul (sgn (ξ α)))).const_mul
        (C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹

/-- [ The coefficient prior is centered for each fixed sign realization.](goal) -/
-- @node: mXi_mean_zero
lemma mXi_mean_zero {d L : ℕ} (s : ℝ) (ξ : PairIdx d L → Bool) :
    (∫ x, mXi s L ξ x ∂cubeMeasure d) = 0 := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  unfold mXi
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [integral_const_mul, pairFeature_mean_zero, mul_zero]
    simp
  · intro α _
    exact ((pairFeature_memLp α).integrable (by norm_num)).const_mul _

/-- [ The canonical main effects of every prior realization vanish.](goal) -/
-- @node: mXi_g1_zero
lemma mXi_g1_zero {d L : ℕ} (s : ℝ) (ξ : PairIdx d L → Bool)
    (j : Fin d) (u : ℝ) : g1 (mXi s L ξ) j u = 0 := by
  unfold g1 mXi
  rw [integral_const_mul, integral_finsetSum _ (fun α _ =>
    (pairFeature_update_integrable α j u).const_mul (sgn (ξ α)))]
  simp_rw [integral_const_mul]
  change _ * (∑ α, sgn (ξ α) * g1 (pairFeature α) j u) = 0
  simp_rw [pairFeature_g1_zero]
  simp

/-- Canonical pair effects of the prior are its polynomials on the corresponding pair. Under [the stated conditions](hyp:hjl), [the asserted mathematical result follows](goal). -/
-- @node: mXi_g2
lemma mXi_g2 {d L : ℕ} (s : ℝ) (ξ : PairIdx d L → Bool)
    (j l : Fin d) (hjl : j < l) (u v : ℝ) :
    g2 (mXi s L ξ) j l u v =
      (C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹ *
        ∑ α, if α.val.1.1 = j ∧ α.val.1.2 = l then
          sgn (ξ α) * (2 * Real.cos (Real.pi * (α.val.2.1.val + 1 : ℕ) * u) *
            Real.cos (Real.pi * (α.val.2.2.val + 1 : ℕ) * v)) else 0 := by
  classical
  simp only [g2, mXi_g1_zero, sub_zero]
  unfold mXi
  rw [integral_const_mul, integral_finsetSum _ (fun α _ =>
    (pairFeature_two_updates_integrable α j l u v).const_mul (sgn (ξ α)))]
  simp_rw [integral_const_mul]
  have hg (α : PairIdx d L) :
      (∫ y, pairFeature α (Function.update (Function.update y j u) l v) ∂cubeMeasure d) =
        g2 (pairFeature α) j l u v := by
    simp only [g2, pairFeature_g1_zero, sub_zero]
  simp_rw [hg]
  simp_rw [pairFeature_g2 _ j l hjl, mul_ite, mul_zero]

/-- [ Every cosine-prior realization has exactly its canonical order-two decomposition.](goal) Under [the stated conditions](hyp:hm). -/
-- @node: mXi_orderTwo
lemma mXi_orderTwo {d L : ℕ} (s : ℝ) (ξ : PairIdx d L → Bool)
    (hm : Measurable (mXi s L ξ) ∧ MemLp (mXi s L ξ) 2 (cubeMeasure d) ∧
      (∫ x, mXi s L ξ x ∂cubeMeasure d) = 0) :
    OrderTwo ⟨mXi s L ξ, hm⟩ := by
  classical
  apply Filter.Eventually.of_forall
  intro x
  simp only [mXi_g1_zero, Finset.sum_const_zero, zero_add]
  have hp (j l : Fin d) :
      (if j < l then g2 (mXi s L ξ) j l (x j) (x l) else 0) =
      (C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹ *
        ∑ α, if α.val.1.1 = j ∧ α.val.1.2 = l then sgn (ξ α) * pairFeature α x else 0 := by
    by_cases h : j < l
    · rw [if_pos h, mXi_g2 s ξ j l h]
      congr 1
      apply Finset.sum_congr rfl
      intro α _
      split_ifs with he
      · simp only [pairFeature, he.1, he.2]
      · rfl
    · rw [if_neg h]
      have hz (α : PairIdx d L) : ¬(α.val.1.1 = j ∧ α.val.1.2 = l) := by
        rintro ⟨rfl, rfl⟩
        exact h α.property
      simp [hz]
  simp_rw [hp, ← Finset.mul_sum]
  unfold mXi
  congr 1
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d)))
    (t := (Finset.univ : Finset (PairIdx d L)))]
  apply Finset.sum_congr rfl
  intro α _
  simp only [ite_and, eq_comm]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp

/-- Each prior realization has exactly the squared energy fixed by its normalization. [The asserted mathematical result follows](goal). -/
-- @node: mXi_second_moment
lemma mXi_second_moment {d L : ℕ} (s : ℝ) (ξ : PairIdx d L → Bool) :
    (∫ x, mXi s L ξ x ^ 2 ∂cubeMeasure d) =
      (C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹ ^ 2 *
        priorDimension d L := by
  classical
  unfold mXi
  simp_rw [mul_pow]
  rw [integral_const_mul, pairFeature_expansion_second_moment]
  have hsign (α : PairIdx d L) : sgn (ξ α) ^ 2 = 1 := by
    cases ξ α <;> norm_num [sgn]
  simp [hsign, pairIdx_card]

/-- The prior has a positive number of coordinates at every admitted dimension and cutoff. Under [the stated conditions](hyp:hd,hL), [the asserted mathematical result follows](goal). -/
-- @node: priorDimension_pos
lemma priorDimension_pos {d L : ℕ} (hd : 2 ≤ d) (hL : 1 ≤ L) :
    0 < priorDimension d L := by
  exact Nat.mul_pos (Nat.choose_pos hd) (pow_pos (by omega) 2)

/-- [ The normalized prior has reciprocal cutoff energy, independently of its signs or dimension.](goal) Under [the stated conditions](hyp:hd,hL). -/
-- @node: mXi_second_moment_normalized
lemma mXi_second_moment_normalized {d L : ℕ} (hd : 2 ≤ d) (hL : 1 ≤ L)
    (s : ℝ) (ξ : PairIdx d L → Bool) :
    (∫ x, mXi s L ξ x ^ 2 ∂cubeMeasure d) = (C0 ^ 2 * ((L : ℝ) ^ s) ^ 2)⁻¹ := by
  have hM : (0 : ℝ) < priorDimension d L := by exact_mod_cast priorDimension_pos hd hL
  have hC : 0 < C0 := by unfold C0; positivity
  have hpow : 0 < (L : ℝ) ^ s := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < L by omega)) s
  have hsqrt : Real.sqrt (priorDimension d L) ^ 2 = (priorDimension d L : ℝ) :=
    Real.sq_sqrt hM.le
  rw [mXi_second_moment, inv_pow, mul_pow, mul_pow, hsqrt]
  field_simp

/-- [ The coefficient normalization supplies exactly one unit of the pooled extension budget.](goal) Under [the stated conditions](hyp:hd,hL). -/
-- @node: mXi_coefficient_budget
lemma mXi_coefficient_budget {d L : ℕ} (hd : 2 ≤ d) (hL : 1 ≤ L)
    (s : ℝ) (ξ : PairIdx d L → Bool) :
    C0 ^ 2 * ((L : ℝ) ^ s) ^ 2 *
      (∑ α, ((C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹ * sgn (ξ α)) ^ 2) = 1 := by
  classical
  have hsign (α : PairIdx d L) : sgn (ξ α) ^ 2 = 1 := by
    cases ξ α <;> norm_num [sgn]
  simp only [mul_pow, hsign, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, pairIdx_card]
  rw [mul_comm (priorDimension d L : ℝ), ← mXi_second_moment s ξ,
    mXi_second_moment_normalized hd hL]
  apply mul_inv_cancel₀
  have hC : 0 < C0 := by unfold C0; positivity
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  positivity


end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
