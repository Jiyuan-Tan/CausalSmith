module
public import Causalean.Mathlib.Optimization.KKT
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
Finite fractional-knapsack optimization. This module proves attainment on the
finite policy box, derives the KKT shadow-price identity, and packages primal
attainment with an exact dual representation.
-/

public section

open scoped BigOperators RealInnerProductSpace
open Set

namespace Causalean.Mathlib.Optimization

/-- A finite fractional knapsack with [dimension, weights, item values, budget, and a
nonnegative-budget certificate](hyp:d,p,tau,b,hb) [has a feasible policy that maximizes the
weighted value over every box-constrained policy within budget](goal). -/
lemma finite_knapsack_attains {d : ℕ} (p tau : Fin d → ℝ) (b : ℝ)
    (hb : 0 ≤ b) :
    ∃ pi : EuclideanSpace ℝ (Fin d),
      (∀ j, pi j ∈ Set.Icc (0 : ℝ) 1) ∧
      (∑ j, p j * pi j) ≤ b ∧
      ∀ rho : EuclideanSpace ℝ (Fin d),
        (∀ j, rho j ∈ Set.Icc (0 : ℝ) 1) →
        (∑ j, p j * rho j) ≤ b →
        (∑ j, p j * rho j * tau j) ≤ ∑ j, p j * pi j * tau j := by
  classical
  let box : Set (EuclideanSpace ℝ (Fin d)) :=
    WithLp.toLp 2 '' Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1)
  let cost : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ∑ j, p j * x j
  let value : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ∑ j, p j * x j * tau j
  have hbox : IsCompact box := by
    exact (isCompact_univ_pi fun _ : Fin d => isCompact_Icc).image
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  have hcost : Continuous cost := by
    dsimp [cost]
    fun_prop
  have hvalue : Continuous value := by
    dsimp [value]
    fun_prop
  let K := box ∩ {x | cost x ≤ b}
  have hK : IsCompact K := hbox.inter_right (isClosed_le hcost continuous_const)
  have h0box : (0 : EuclideanSpace ℝ (Fin d)) ∈ box := by
    refine ⟨0, ?_, ?_⟩
    · intro j _
      norm_num
    · rfl
  have h0K : (0 : EuclideanSpace ℝ (Fin d)) ∈ K := by
    exact ⟨h0box, by simpa [cost] using hb⟩
  obtain ⟨pi, hpiK, hpiMax⟩ := hK.exists_isMaxOn ⟨0, h0K⟩ hvalue.continuousOn
  refine ⟨pi, ?_, hpiK.2, ?_⟩
  · rintro j
    obtain ⟨x, hx, rfl⟩ := hpiK.1
    exact hx j (Set.mem_univ j)
  · intro rho hrho hcostrho
    apply hpiMax
    refine ⟨?_, hcostrho⟩
    refine ⟨fun j => rho j, ?_, ?_⟩
    intro j _
    exact hrho j
    ext j
    rfl

/-- For a finite fractional knapsack with [dimension, weights, item values, budget,
nonnegative weights, a box-constrained feasible policy, and its maximizing
certificate](hyp:d,p,tau,b,hp,pi,hpi,hbudget,hmax), [there is a nonnegative shadow price
satisfying complementary slackness and the coordinatewise hinge-value identity](goal). -/
lemma finite_knapsack_kkt {d : ℕ} (p tau : Fin d → ℝ) (b : ℝ)
    (hp : ∀ j, 0 ≤ p j)
    (pi : EuclideanSpace ℝ (Fin d))
    (hpi : ∀ j, pi j ∈ Set.Icc (0 : ℝ) 1)
    (hbudget : (∑ j, p j * pi j) ≤ b)
    (hmax : ∀ rho : EuclideanSpace ℝ (Fin d),
      (∀ j, rho j ∈ Set.Icc (0 : ℝ) 1) →
      (∑ j, p j * rho j) ≤ b →
      (∑ j, p j * rho j * tau j) ≤ ∑ j, p j * pi j * tau j) :
    ∃ lambda : ℝ, 0 ≤ lambda ∧
      lambda * (b - ∑ j, p j * pi j) = 0 ∧
      ∀ j, p j * pi j * tau j =
        lambda * (p j * pi j) + p j * max 0 (tau j - lambda) := by
  classical
  let κ := Option (Fin d ⊕ Fin d)
  let N := Fintype.card κ
  let e : Fin N ≃ κ := (Fintype.equivFin κ).symm
  let sigma : Finset ℕ := Finset.range N
  let pvec : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 p
  let tvec : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun j => p j * tau j)
  let row : κ → EuclideanSpace ℝ (Fin d)
    | none => -pvec
    | some (Sum.inl j) => EuclideanSpace.single j 1
    | some (Sum.inr j) => -EuclideanSpace.single j 1
  let offset : κ → ℝ
    | none => b
    | some (Sum.inl _) => 0
    | some (Sum.inr _) => 1
  let constraint : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun i x =>
    if hi : i < N then inner ℝ x (row (e ⟨i, hi⟩)) + offset (e ⟨i, hi⟩) else 0
  let P : Constrained_OptimizationProblem (EuclideanSpace ℝ (Fin d)) ∅ sigma :=
    { domain := Set.univ
      equality_constraints := fun _ _ => 0
      inequality_constraints := constraint
      eq_ine_not_intersect := by simp
      objective := fun x => inner ℝ x (-tvec) }
  have hinner_p (x : EuclideanSpace ℝ (Fin d)) :
      inner ℝ x pvec = ∑ j, p j * x j := by
    simp [pvec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  have hinner_t (x : EuclideanSpace ℝ (Fin d)) :
      inner ℝ x tvec = ∑ j, p j * x j * tau j := by
    simp [tvec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hconstraint_none (x : EuclideanSpace ℝ (Fin d)) :
      constraint (e.symm none).val x = b - ∑ j, p j * x j := by
    rw [show constraint (e.symm none).val x =
        inner ℝ x (row none) + offset none by
      simp [constraint, (e.symm none).isLt]]
    simp [row, offset, hinner_p]
    ring
  have hconstraint_lower (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
      constraint (e.symm (some (Sum.inl j))).val x = x j := by
    rw [show constraint (e.symm (some (Sum.inl j))).val x =
        inner ℝ x (row (some (Sum.inl j))) + offset (some (Sum.inl j)) by
      simp [constraint, (e.symm (some (Sum.inl j))).isLt]]
    simp [row, offset, EuclideanSpace.inner_single_right]
  have hconstraint_upper (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
      constraint (e.symm (some (Sum.inr j))).val x = 1 - x j := by
    rw [show constraint (e.symm (some (Sum.inr j))).val x =
        inner ℝ x (row (some (Sum.inr j))) + offset (some (Sum.inr j)) by
      simp [constraint, (e.symm (some (Sum.inr j))).isLt]]
    simp [row, offset, EuclideanSpace.inner_single_right]
    ring
  have hfeas : P.FeasPoint pi := by
    refine ⟨Set.mem_univ _, by simp, ?_⟩
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    generalize hc : e ⟨i, hiN⟩ = c
    rcases c with _ | (j | j)
    · have hcode : i = (e.symm none).val := by
        have := congrArg (fun z => (e.symm z).val) hc
        simpa using this
      rw [hcode]
      change constraint (e.symm none).val pi ≥ 0
      rw [hconstraint_none]
      linarith
    · have hcode : i = (e.symm (some (Sum.inl j))).val := by
        have := congrArg (fun z => (e.symm z).val) hc
        simpa using this
      rw [hcode]
      change constraint (e.symm (some (Sum.inl j))).val pi ≥ 0
      rw [hconstraint_lower]
      exact (hpi j).1
    · have hcode : i = (e.symm (some (Sum.inr j))).val := by
        have := congrArg (fun z => (e.symm z).val) hc
        simpa using this
      rw [hcode]
      change constraint (e.symm (some (Sum.inr j))).val pi ≥ 0
      rw [hconstraint_upper]
      linarith [(hpi j).2]
  have hlocal : P.Local_Minimum pi := by
    refine ⟨hfeas, ?_⟩
    apply IsMinOn.localize
    intro rho hrho
    have hrho' : P.FeasPoint rho := hrho
    have hlower (j : Fin d) : 0 ≤ rho j := by
      have hm := hrho'.2.2 (e.symm (some (Sum.inl j))).val
        (Finset.mem_range.mpr (e.symm (some (Sum.inl j))).isLt)
      change constraint (e.symm (some (Sum.inl j))).val rho ≥ 0 at hm
      rwa [hconstraint_lower] at hm
    have hupper (j : Fin d) : rho j ≤ 1 := by
      have hm := hrho'.2.2 (e.symm (some (Sum.inr j))).val
        (Finset.mem_range.mpr (e.symm (some (Sum.inr j))).isLt)
      change constraint (e.symm (some (Sum.inr j))).val rho ≥ 0 at hm
      rw [hconstraint_upper] at hm
      linarith
    have hcostrho : (∑ j, p j * rho j) ≤ b := by
      have hm := hrho'.2.2 (e.symm none).val
        (Finset.mem_range.mpr (e.symm none).isLt)
      change constraint (e.symm none).val rho ≥ 0 at hm
      rw [hconstraint_none] at hm
      linarith
    simpa [P, hinner_t] using neg_le_neg (hmax rho (fun j => ⟨hlower j, hupper j⟩) hcostrho)
  have hdiff : Differentiable ℝ P.objective := by
    intro x
    dsimp [P]
    simpa only [real_inner_comm] using
      (gradient_of_inner_const x (-tvec)).differentiableAt
  have hcont : ∀ i ∈ sigma, ContDiffAt ℝ (1 : ℕ) (P.inequality_constraints i) pi := by
    intro i hi
    dsimp [P, constraint]
    split_ifs with hiN
    · have hc : ContDiff ℝ (1 : ℕ)
          (fun x : EuclideanSpace ℝ (Fin d) =>
            inner ℝ (row (e ⟨i, hiN⟩)) x + offset (e ⟨i, hiN⟩)) := by
        exact (innerSL ℝ (row (e ⟨i, hiN⟩))).contDiff.add contDiff_const
      simpa only [real_inner_comm] using hc.contDiffAt
    · exact contDiffAt_const
  have hlin : P.LinearCQ pi := by
    constructor
    · simp
    · intro i hi
      refine ⟨if hiN : i < N then row (e ⟨i, hiN⟩) else 0,
        if hiN : i < N then offset (e ⟨i, hiN⟩) else 0, ?_⟩
      funext x
      simp only [P, constraint]
      split_ifs <;> simp
  obtain ⟨_, eta, mu, hstationary, hmu, hcomp⟩ :=
    first_order_neccessary_LinearCQ P pi hlocal hdiff (by simp) hcont hlin rfl
  let idx (c : κ) : sigma :=
    ⟨(e.symm c).val, Finset.mem_range.mpr (e.symm c).isLt⟩
  let lambda := mu (idx none)
  let lower (j : Fin d) := mu (idx (some (Sum.inl j)))
  let upper (j : Fin d) := mu (idx (some (Sum.inr j)))
  have hlambda : 0 ≤ lambda := hmu (idx none)
  have hlower_mu (j : Fin d) : 0 ≤ lower j := hmu (idx (some (Sum.inl j)))
  have hupper_mu (j : Fin d) : 0 ≤ upper j := hmu (idx (some (Sum.inr j)))
  have hcomp_budget : lambda * (b - ∑ j, p j * pi j) = 0 := by
    have hc := hcomp (idx none)
    change mu (idx none) * constraint (e.symm none).val pi = 0 at hc
    rwa [hconstraint_none] at hc
  have hcomp_lower (j : Fin d) : lower j * pi j = 0 := by
    have hc := hcomp (idx (some (Sum.inl j)))
    change mu (idx (some (Sum.inl j))) *
      constraint (e.symm (some (Sum.inl j))).val pi = 0 at hc
    rwa [hconstraint_lower] at hc
  have hcomp_upper (j : Fin d) : upper j * (1 - pi j) = 0 := by
    have hc := hcomp (idx (some (Sum.inr j)))
    change mu (idx (some (Sum.inr j))) *
      constraint (e.symm (some (Sum.inr j))).val pi = 0 at hc
    rwa [hconstraint_upper] at hc
  -- Stationarity identifies the reduced costs coordinate by coordinate.
  have hstationary_coord (j : Fin d) :
      p j * (lambda - tau j) - lower j + upper j = 0 := by
    let es : sigma ≃ κ :=
      { toFun := fun q => e ⟨q.val, Finset.mem_range.mp q.property⟩
        invFun := fun c => idx c
        left_inv := by
          intro q
          apply Subtype.ext
          simp [idx]
        right_inv := by
          intro c
          simp [idx] }
    let v : EuclideanSpace ℝ (Fin d) :=
      -tvec - ∑ q : sigma, mu q • row (es q)
    let c0 : ℝ := -∑ q : sigma, mu q * offset (es q)
    have hconstraint_es (q : sigma) (x : EuclideanSpace ℝ (Fin d)) :
        constraint q.val x = inner ℝ x (row (es q)) + offset (es q) := by
      unfold constraint
      rw [dif_pos (Finset.mem_range.mp q.property)]
      simp [es]
    have hLag : (fun x => P.Lagrange_function x eta mu) =
        fun x => inner ℝ v x + c0 := by
      funext x
      simp only [Constrained_OptimizationProblem.Lagrange_function, P,
        Finset.sum_empty, zero_sub]
      simp_rw [hconstraint_es]
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const_zero,
        Finset.card_empty, Nat.cast_zero, zero_mul, sub_zero]
      simp [v, c0, inner_sub_left, inner_neg_left, inner_sum,
        inner_smul_left, inner_smul_right, real_inner_comm]
      ring
    rw [hLag, gradient_add_const] at hstationary
    rw [(gradient_of_inner_const pi v).gradient] at hstationary
    have hvj := congrArg (fun z : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (EuclideanSpace.single j 1) z) hstationary
    have hes_symm (c : κ) : es.symm c = idx c := rfl
    have hsum : (∑ q : sigma,
        inner ℝ (EuclideanSpace.single j 1) (mu q • row (es q))) =
        -lambda * p j + lower j - upper j := by
      rw [Fintype.sum_equiv es
        (fun q : sigma => inner ℝ (EuclideanSpace.single j 1) (mu q • row (es q)))
        (fun c : κ => inner ℝ (EuclideanSpace.single j 1) (mu (es.symm c) • row c))
        (fun q => by rw [es.symm_apply_apply])]
      rw [Fintype.sum_option, Fintype.sum_sum_type]
      simp_rw [inner_smul_right, EuclideanSpace.inner_single_left]
      simp [hes_symm, idx, lambda, lower, upper, row, pvec,
        PiLp.single_apply]
      ring
    simp only [v, inner_sub_right, inner_neg_right, inner_sum] at hvj
    rw [hsum] at hvj
    rw [EuclideanSpace.inner_single_left] at hvj
    simp [tvec] at hvj
    linarith
  refine ⟨lambda, hlambda, hcomp_budget, ?_⟩
  intro j
  by_cases hp0 : p j = 0
  · simp [hp0]
  rcases hpi j with ⟨hpi0, hpi1⟩
  by_cases hj0 : pi j = 0
  · have hu0 : upper j = 0 := by
      have hc := hcomp_upper j
      rw [hj0] at hc
      simpa using hc
    have hred : 0 ≤ lambda - tau j := by
      have hs := hstationary_coord j
      have hp_nonneg : 0 ≤ p j := hp j
      have hp_pos := lt_of_le_of_ne hp_nonneg (Ne.symm hp0)
      rw [hu0] at hs
      nlinarith [hlower_mu j]
    rw [hj0, max_eq_left (by linarith : tau j - lambda ≤ 0)]
    ring
  · have hl0 : lower j = 0 := by
      exact (mul_eq_zero.mp (hcomp_lower j)).resolve_right hj0
    by_cases hj1 : pi j = 1
    · have hs := hstationary_coord j
      rw [hl0] at hs
      have heq : p j * max 0 (tau j - lambda) = p j * (tau j - lambda) := by
        have hp_pos := lt_of_le_of_ne (hp j) (Ne.symm hp0)
        rw [max_eq_right]
        nlinarith [hupper_mu j]
      rw [hj1, heq]
      ring
    · have hu0 : upper j = 0 := by
        apply (mul_eq_zero.mp (hcomp_upper j)).resolve_right
        exact sub_ne_zero.mpr (Ne.symm hj1)
      have hs := hstationary_coord j
      rw [hl0, hu0] at hs
      have ht : tau j = lambda := by
        have hz : lambda - tau j = 0 :=
          (mul_eq_zero.mp (by linarith : p j * (lambda - tau j) = 0)).resolve_left hp0
        linarith
      simp [ht, mul_comm]

/-- A finite fractional knapsack with [dimension, weights, item values, budget,
nonnegative weights, values at most one, and a unit-interval budget
certificate](hyp:d,p,tau,b,hp,ht,hb) [admits a feasible primal policy and a unit-interval
dual price whose objectives are equal](goal). -/
lemma finite_knapsack_dual_witness {d : ℕ} (p tau : Fin d → ℝ) (b : ℝ)
    (hp : ∀ j, 0 ≤ p j) (ht : ∀ j, tau j ≤ 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    ∃ pi : EuclideanSpace ℝ (Fin d),
      (∀ j, pi j ∈ Set.Icc (0 : ℝ) 1) ∧
      (∑ j, p j * pi j) ≤ b ∧
      ∃ lambda ∈ Set.Icc (0 : ℝ) 1,
        (∑ j, p j * pi j * tau j) =
          b * lambda + ∑ j, p j * max 0 (tau j - lambda) := by
  obtain ⟨pi, hpi, hbudget, hmax⟩ := finite_knapsack_attains p tau b hb.1
  obtain ⟨lambda, hlambda, hcomp, hcell⟩ :=
    finite_knapsack_kkt p tau b hp pi hpi hbudget hmax
  have heq : (∑ j, p j * pi j * tau j) =
      b * lambda + ∑ j, p j * max 0 (tau j - lambda) := by
    calc
      _ = ∑ j, (lambda * (p j * pi j) + p j * max 0 (tau j - lambda)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hcell j
      _ = lambda * (∑ j, p j * pi j) +
          ∑ j, p j * max 0 (tau j - lambda) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = b * lambda + ∑ j, p j * max 0 (tau j - lambda) := by
        have : lambda * (∑ j, p j * pi j) = lambda * b := by
          nlinarith [hcomp]
        rw [this]
        ring
  by_cases hlam1 : lambda ≤ 1
  · exact ⟨pi, hpi, hbudget, lambda, ⟨hlambda, hlam1⟩, heq⟩
  · have hhinge : ∑ j, p j * max 0 (tau j - lambda) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [max_eq_left]
      · ring
      · linarith [ht j]
    have hgain_le : (∑ j, p j * pi j * tau j) ≤ ∑ j, p j * pi j := by
      apply Finset.sum_le_sum
      intro j _
      have hppi : 0 ≤ p j * pi j := mul_nonneg (hp j) (hpi j).1
      nlinarith [ht j]
    have hb0 : b = 0 := by
      rw [hhinge] at heq
      have : b * lambda ≤ b := by linarith
      nlinarith [hb.1]
    refine ⟨pi, hpi, hbudget, 1, by norm_num, ?_⟩
    rw [hb0]
    have hhinge1 : ∑ j, p j * max 0 (tau j - 1) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [max_eq_left]
      · ring
      · linarith [ht j]
    rw [hhinge1]
    simpa [hb0, hhinge] using heq

end Causalean.Mathlib.Optimization
