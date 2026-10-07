module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensor

/-!
# Heterogeneous tensor Jackson extraction

This module extracts the coordinatewise trigonometric and even structure of heterogeneous
product Jackson convolution and converts it into a multivariate polynomial with coordinatewise
degree bounds.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For [a coordinate-specific positive order map](hyp:d,hd), [a measurable cube target](hyp:f,hf),
[a real bound B](hyp:B) such that [the target is at most B in absolute value on the cube](hyp:hB),
[a selected coordinate](hyp:i), and [a phase vector fixing the other coordinates](hyp:x), [the
heterogeneous Jackson convolution, as a function of the selected coordinate alone, is a
trigonometric polynomial of degree at most twice (that coordinate's order minus one)](goal). -/
theorem convolution_coord_trig (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (f : (ι → ℝ) → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ x ∈ cube, |f x| ≤ B)
    (i : ι) (x : ι → ℝ) :
    Causalean.Mathlib.Analysis.JacksonApproximation.IsTrigPolyLE (2 * (d i - 1))
      (fun t => convolution d f (Function.update x i t)) := by
  classical
  let J (j : ι) := Causalean.Mathlib.Analysis.JacksonApproximation.jackson (d j)
  let n := 2 * (d i - 1)
  rcases Causalean.Mathlib.Analysis.JacksonApproximation.jackson_isTrigPolyLE
    (d i) (hd i) with ⟨a, b, hab⟩
  let P : (ι → ℝ) → ℝ := fun v => ∏ j ∈ Finset.univ.erase i, J j (x j - v j)
  let W : (ι → ℝ) → ℝ := fun v => f (cosPoint v) * P v
  let A : ℕ → ℝ := fun k => ∫ v in periodBox,
    W v * (a k * Real.cos ((k : ℝ) * v i) - b k * Real.sin ((k : ℝ) * v i))
  let D : ℕ → ℝ := fun k => ∫ v in periodBox,
    W v * (a k * Real.sin ((k : ℝ) * v i) + b k * Real.cos ((k : ℝ) * v i))
  refine ⟨A, D, fun t => ?_⟩
  change convolution d f (Function.update x i t) = _
  rw [convolution_shifted d hd f hf B hB]
  have hcompact : IsCompact (periodBox (ι := ι)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hP : Continuous P := by
    dsimp [P, J]
    fun_prop (disch := exact Causalean.Mathlib.Analysis.JacksonApproximation.continuous_jackson _)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hP.continuousOn
  have hCnonneg : 0 ≤ C := by
    apply le_trans (norm_nonneg (P (fun _ => 0)))
    apply hC
    intro j _
    exact ⟨neg_nonpos.mpr Real.pi_pos.le, Real.pi_pos.le⟩
  have hBnonneg : 0 ≤ B := by
    apply le_trans (abs_nonneg (f (cosPoint (fun _ => 0))))
    apply hB
    intro j
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hWm : Measurable W := by
    have hc : Measurable (cosPoint (ι := ι)) := by
      unfold cosPoint
      fun_prop
    exact (hf.comp hc).mul hP.measurable
  have hWbound (v : ι → ℝ) (hv : v ∈ periodBox) : ‖W v‖ ≤ B * C := by
    have hfbound : ‖f (cosPoint v)‖ ≤ B := by
      simpa [Real.norm_eq_abs] using hB (cosPoint v) (by
        intro j
        exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    calc
      ‖W v‖ = ‖f (cosPoint v)‖ * ‖P v‖ := norm_mul _ _
      _ ≤ B * ‖P v‖ := mul_le_mul_of_nonneg_right hfbound (norm_nonneg _)
      _ ≤ B * C := mul_le_mul_of_nonneg_left (hC v hv) hBnonneg
  have hint (q : (ι → ℝ) → ℝ) (hq : Continuous q) :
      IntegrableOn (fun v => W v * q v) periodBox := by
    obtain ⟨E, hE⟩ := hcompact.exists_bound_of_continuousOn hq.continuousOn
    have hEnonneg : 0 ≤ E := by
      apply le_trans (norm_nonneg (q (fun _ => 0)))
      apply hE
      intro j _
      exact ⟨neg_nonpos.mpr Real.pi_pos.le, Real.pi_pos.le⟩
    apply Measure.integrableOn_of_bounded (hcompact.measure_lt_top.ne)
      ((hWm.mul hq.measurable).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem hcompact.measurableSet] with v hv
    calc
      ‖W v * q v‖ = ‖W v‖ * ‖q v‖ := norm_mul _ _
      _ ≤ (B * C) * ‖q v‖ :=
        mul_le_mul_of_nonneg_right (hWbound v hv) (norm_nonneg _)
      _ ≤ (B * C) * E :=
        mul_le_mul_of_nonneg_left (hE v hv) (mul_nonneg hBnonneg hCnonneg)
  have hq1 (k : ℕ) : Continuous (fun v : ι → ℝ =>
      a k * Real.cos ((k : ℝ) * v i) - b k * Real.sin ((k : ℝ) * v i)) := by
    fun_prop
  have hq2 (k : ℕ) : Continuous (fun v : ι → ℝ =>
      a k * Real.sin ((k : ℝ) * v i) + b k * Real.cos ((k : ℝ) * v i)) := by
    fun_prop
  calc
    (∫ v in periodBox,
      f (cosPoint v) * kernel d (Function.update x i t - v)) =
        ∫ v in periodBox, W v * J i (t - v i) := by
      apply integral_congr_ae
      filter_upwards with v
      dsimp [W, P, kernel]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      have herase :
          (∏ j ∈ Finset.univ.erase i,
            J j (Function.update x i t j - v j)) =
          ∏ j ∈ Finset.univ.erase i, J j (x j - v j) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        simp [Function.update, hji]
      rw [herase]
      simp [Function.update]
      ring
    _ = ∫ v in periodBox,
        ∑ k ∈ Finset.range (n + 1),
          (W v * (a k * Real.cos ((k : ℝ) * v i) -
              b k * Real.sin ((k : ℝ) * v i)) * Real.cos ((k : ℝ) * t) +
            W v * (a k * Real.sin ((k : ℝ) * v i) +
              b k * Real.cos ((k : ℝ) * v i)) * Real.sin ((k : ℝ) * t)) := by
      apply integral_congr_ae
      filter_upwards with v
      change W v * Causalean.Mathlib.Analysis.JacksonApproximation.jackson (d i)
        (t - v i) = _
      rw [hab (t - v i), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [show (k : ℝ) * (t - v i) = (k : ℝ) * t - (k : ℝ) * v i by ring,
        Real.cos_sub, Real.sin_sub]
      ring
    _ = ∑ k ∈ Finset.range (n + 1),
        (A k * Real.cos ((k : ℝ) * t) +
          D k * Real.sin ((k : ℝ) * t)) := by
      have hterm (k : ℕ) : IntegrableOn (fun v : ι → ℝ =>
          W v * (a k * Real.cos ((k : ℝ) * v i) -
            b k * Real.sin ((k : ℝ) * v i)) * Real.cos ((k : ℝ) * t) +
          W v * (a k * Real.sin ((k : ℝ) * v i) +
            b k * Real.cos ((k : ℝ) * v i)) * Real.sin ((k : ℝ) * t))
          periodBox := by
        exact (hint _ (hq1 k)).mul_const _ |>.add ((hint _ (hq2 k)).mul_const _)
      rw [integral_finsetSum (Finset.range (n + 1)) (fun k hk => hterm k)]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [A, D]
      rw [integral_add]
      · rw [integral_mul_const, integral_mul_const]
      · exact (hint _ (hq1 k)).mul_const _
      · exact (hint _ (hq2 k)).mul_const _

/-- For [a coordinate-specific order map](hyp:d), [a cube target](hyp:f), [a
selected coordinate](hyp:i), and [a phase vector fixing the other coordinates](hyp:x), [the
heterogeneous Jackson convolution is an even function of the selected coordinate](goal). -/
theorem convolution_coord_even (d : ι → ℕ)
    (f : (ι → ℝ) → ℝ)
    (i : ι) (x : ι → ℝ) :
    Function.Even (fun t => convolution d f (Function.update x i t)) := by
  classical
  let e : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
    MeasurableEquiv.piCongrRight fun j =>
      if j = i then MeasurableEquiv.neg ℝ else MeasurableEquiv.refl ℝ
  have he_apply (u : ι → ℝ) : e u = Function.update u i (-u i) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [e, MeasurableEquiv.piCongrRight, Function.update]
    · simp [e, MeasurableEquiv.piCongrRight, Function.update, hji]
  have hem : MeasurePreserving e volume volume := by
    rw [volume_pi]
    apply measurePreserving_pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa [e] using Measure.measurePreserving_neg (volume : Measure ℝ)
    · simpa [e, hji] using MeasurePreserving.id (volume : Measure ℝ)
  have he_box : e ⁻¹' periodBox = periodBox (ι := ι) := by
    ext u
    simp only [Set.mem_preimage, periodBox, Set.mem_pi, Set.mem_univ, forall_true_left,
      he_apply, Set.mem_Icc]
    constructor <;> intro h j
    · by_cases hji : j = i
      · subst j
        have hi := h i
        simp [Function.update] at hi
        constructor <;> linarith
      · simpa [Function.update, hji] using h j
    · by_cases hji : j = i
      · subst j
        have hi := h i
        simp [Function.update]
        constructor <;> linarith
      · simpa [Function.update, hji] using h j
  intro t
  unfold convolution
  calc
    (∫ u in periodBox,
        f (cosPoint (Function.update x i (-t) - u)) * kernel d u) =
      ∫ u in periodBox,
        f (cosPoint (Function.update x i t - Function.update u i (-u i))) *
          kernel d (Function.update u i (-u i)) := by
        apply integral_congr_ae
        filter_upwards with u
        congr 1
        · congr 1
          funext j
          by_cases hji : j = i
          · subst j
            simp only [cosPoint, Pi.sub_apply, Function.update_self]
            rw [show -t - u i = -(t - -u i) by ring, Real.cos_neg]
          · simp [cosPoint, hji]
        · unfold kernel
          apply Finset.prod_congr rfl
          intro j hj
          by_cases hji : j = i
          · subst j
            simp only [Function.update_self]
            exact (Causalean.Mathlib.Analysis.JacksonApproximation.jackson_even (d i) (u i)).symm
          · simp [Function.update, hji]
    _ = ∫ u in periodBox,
        f (cosPoint (Function.update x i t - u)) * kernel d u := by
      simpa only [he_apply, he_box] using
        (hem.setIntegral_preimage_emb e.measurableEmbedding
          (fun u => f (cosPoint (Function.update x i t - u)) * kernel d u) periodBox)

/-- [A coordinate-specific degree map](hyp:d), [a phase function](hyp:q), [its coordinatewise trigonometric degree bounds](hyp:htrig), and [its coordinatewise evenness](hyp:heven) imply that [the phase function has a multivariate polynomial representation in coordinate cosines with the same bounds](goal). -/
theorem polynomial_of_coord_even_trig (d : ι → ℕ) (q : (ι → ℝ) → ℝ)
    (htrig : ∀ i x,
      Causalean.Mathlib.Analysis.JacksonApproximation.IsTrigPolyLE (2 * (d i - 1))
        (fun t => q (Function.update x i t)))
    (heven : ∀ i x, Function.Even (fun t => q (Function.update x i t))) :
    ∃ p : MvPolynomial ι ℝ,
      (∀ x : ι → ℝ, MvPolynomial.eval (cosPoint x) p = q x) ∧
      (∀ γ ∈ p.support, ∀ i, γ i ≤ 2 * (d i - 1)) := by
  classical
  let D : ι → ℕ := fun i => 2 * (d i - 1)
  have hfin : ∀ (N : ℕ) (D : Fin N → ℕ) (q : (Fin N → ℝ) → ℝ),
      (∀ i x, Causalean.Mathlib.Analysis.JacksonApproximation.IsTrigPolyLE (D i)
        (fun t => q (Function.update x i t))) →
      (∀ i x, Function.Even (fun t => q (Function.update x i t))) →
      ∃ p : MvPolynomial (Fin N) ℝ,
        (∀ x, MvPolynomial.eval (fun i => Real.cos (x i)) p = q x) ∧
        (∀ m ∈ p.support, ∀ i, m i ≤ D i) := by
    intro N
    induction N with
    | zero =>
        intro D q ht he
        refine ⟨MvPolynomial.C (q 0), ?_, ?_⟩
        · intro x
          rw [MvPolynomial.eval_C]
          exact congrArg q (Subsingleton.elim 0 x)
        · intro m hm i
          exact Fin.elim0 i
    | succ N ih =>
        intro D q ht he
        have hpoly_degree
            (k : ℕ) (a b : Fin (N + 1)) (r : Polynomial ℝ) (hr : r.natDegree ≤ k) :
            (r.toMvPolynomial a).degreeOf b ≤ if b = a then k else 0 := by
          rw [r.as_sum_range_C_mul_X_pow' (lt_of_le_of_lt hr (Nat.lt_succ_self k))]
          simp only [map_sum, map_mul, map_pow, Polynomial.toMvPolynomial_C,
            Polynomial.toMvPolynomial_X]
          refine (MvPolynomial.degreeOf_sum_le b (Finset.range (k + 1))
            (fun l => MvPolynomial.C (r.coeff l) * MvPolynomial.X a ^ l)).trans ?_
          apply Finset.sup_le
          intro l hl
          refine (MvPolynomial.degreeOf_mul_le b _ _).trans ?_
          rw [MvPolynomial.degreeOf_C]
          by_cases hba : b = a
          · subst b
            simp only [if_true, zero_add, MvPolynomial.degreeOf_X_self_pow]
            exact Nat.le_of_lt_succ (Finset.mem_range.mp hl)
          · rw [MvPolynomial.degreeOf_X_pow_of_ne l hba]
            simp
        let n := D 0
        let node : Fin (n + 1) → ℝ := fun j => (j : ℝ) / (n + 1 : ℝ)
        let angle : Fin (n + 1) → ℝ := fun j => Real.arccos (node j)
        have hnode_nonneg (j : Fin (n + 1)) : 0 ≤ node j := by
          dsimp [node]
          positivity
        have hnode_le_one (j : Fin (n + 1)) : node j ≤ 1 := by
          dsimp [node]
          rw [div_le_one (by positivity : (0 : ℝ) < n + 1)]
          exact_mod_cast (Nat.le_trans (Nat.le_of_lt_succ j.isLt)
            (Nat.le_add_right n 1))
        have hcos_angle (j : Fin (n + 1)) : Real.cos (angle j) = node j := by
          exact Real.cos_arccos (le_trans (by norm_num) (hnode_nonneg j))
            (hnode_le_one j)
        have hnode_inj : Function.Injective node := by
          intro j k hjk
          dsimp [node] at hjk
          have hden : (n + 1 : ℝ) ≠ 0 := by positivity
          have : (j : ℝ) = (k : ℝ) := (div_left_inj' hden).mp hjk
          exact Fin.ext (by exact_mod_cast this)
        let qtail : Fin (n + 1) → (Fin N → ℝ) → ℝ := fun j y =>
          q (Fin.cons (angle j) y)
        have htail_trig (j : Fin (n + 1)) (i : Fin N) (y : Fin N → ℝ) :
            Causalean.Mathlib.Analysis.JacksonApproximation.IsTrigPolyLE (D i.succ)
              (fun t => qtail j (Function.update y i t)) := by
          have h := ht i.succ (Fin.cons (angle j) y)
          simpa only [qtail, Fin.cons_update] using h
        have htail_even (j : Fin (n + 1)) (i : Fin N) (y : Fin N → ℝ) :
            Function.Even (fun t => qtail j (Function.update y i t)) := by
          have h := he i.succ (Fin.cons (angle j) y)
          simpa only [qtail, Fin.cons_update] using h
        have hchoice (j : Fin (n + 1)) := ih (D ∘ Fin.succ) (qtail j)
          (htail_trig j) (htail_even j)
        let ptail : Fin (n + 1) → MvPolynomial (Fin N) ℝ := fun j =>
          Classical.choose (hchoice j)
        have hptail (j : Fin (n + 1)) :
            (∀ y, MvPolynomial.eval (fun i => Real.cos (y i)) (ptail j) = qtail j y) ∧
            (∀ m ∈ (ptail j).support, ∀ i, m i ≤ D i.succ) := by
          exact Classical.choose_spec (hchoice j)
        let basis : Fin (n + 1) → Polynomial ℝ := fun j =>
          Lagrange.basis Finset.univ node j
        let p : MvPolynomial (Fin (N + 1)) ℝ :=
          ∑ j, MvPolynomial.rename Fin.succ (ptail j) *
            (basis j).toMvPolynomial 0
        have hbdeg (j : Fin (n + 1)) : (basis j).natDegree ≤ n := by
          dsimp [basis]
          rw [Lagrange.natDegree_basis hnode_inj.injOn (Finset.mem_univ j),
            Finset.card_univ, Fintype.card_fin]
          omega
        have hrename_degree (j : Fin (n + 1)) (i : Fin (N + 1)) :
            (MvPolynomial.rename Fin.succ (ptail j)).degreeOf i ≤
              if i = 0 then 0 else D i := by
          refine Fin.cases ?_ (fun k => ?_) i
          · simp only [if_true]
            apply MvPolynomial.degreeOf_le_iff.mpr
            intro m hm
            rw [MvPolynomial.support_rename_of_injective (Fin.succ_injective N)] at hm
            rcases Finset.mem_image.mp hm with ⟨m', hm', rfl⟩
            have hnot : (0 : Fin (N + 1)) ∉ Set.range Fin.succ := by
              rintro ⟨k, hk⟩
              exact Fin.ne_of_gt (Fin.succ_pos k) hk
            rw [Finsupp.mapDomain_of_notMem_range m' 0 hnot]
          · simp only [Fin.succ_ne_zero, if_false]
            rw [MvPolynomial.degreeOf_rename_of_injective (Fin.succ_injective N)]
            exact MvPolynomial.degreeOf_le_iff.mpr
              (fun m hm => (hptail j).2 m hm k)
        refine ⟨p, ?_, ?_⟩
        · intro x
          let sec : ℝ → ℝ := fun t => q (Fin.cons t (x ∘ Fin.succ))
          have hu (t : ℝ) : Function.update x 0 t = Fin.cons t (x ∘ Fin.succ) := by
            funext k
            refine Fin.cases ?_ (fun l => ?_) k <;> simp
          have hs_trig : Causalean.Mathlib.Analysis.JacksonApproximation.IsTrigPolyLE n sec := by
            have h := ht 0 x
            convert h using 1
            funext t
            dsimp [sec]
            exact congrArg q (hu t).symm
          have hs_even : Function.Even sec := by
            have h := he 0 x
            intro t
            dsimp [sec]
            calc
              q (Fin.cons (-t) (x ∘ Fin.succ)) = q (Function.update x 0 (-t)) :=
                congrArg q (hu (-t)).symm
              _ = q (Function.update x 0 t) := h t
              _ = q (Fin.cons t (x ∘ Fin.succ)) := congrArg q (hu t)
          rcases Causalean.Mathlib.Analysis.JacksonApproximation.even_trigPoly_exists_polynomial
              hs_trig hs_even with ⟨r, hrdeg, hr⟩
          have hr_degree : r.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
            rw [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
            calc
              r.degree ≤ (r.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
              _ < ((n + 1 : ℕ) : WithBot ℕ) := by
                exact_mod_cast (Nat.lt_succ_of_le hrdeg)
          have hinterp := Lagrange.eq_interpolate
            (s := (Finset.univ : Finset (Fin (n + 1))))
            (v := node) hnode_inj.injOn hr_degree
          change MvPolynomial.eval (fun i => Real.cos (x i)) p = q x
          rw [show q x = sec (x 0) by
            congr 1
            funext k
            refine Fin.cases ?_ (fun l => ?_) k <;> simp]
          rw [← hr (x 0), hinterp]
          simp only [p, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
            MvPolynomial.eval_rename, MvPolynomial.eval_toMvPolynomial,
            Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
            Polynomial.eval_mul, Polynomial.eval_C]
          apply Finset.sum_congr rfl
          intro j hj
          have hcos_tail : (fun i => Real.cos (x i)) ∘ Fin.succ =
              (fun i => Real.cos ((x ∘ Fin.succ) i)) := by rfl
          rw [hcos_tail, (hptail j).1]
          rw [show qtail j (x ∘ Fin.succ) = sec (angle j) by rfl,
            ← hr (angle j), hcos_angle]
        · intro m hm i
          refine (MvPolynomial.monomial_le_degreeOf i hm).trans ?_
          dsimp [p]
          refine (MvPolynomial.degreeOf_sum_le i Finset.univ
            (fun j => MvPolynomial.rename Fin.succ (ptail j) *
              (basis j).toMvPolynomial 0)).trans ?_
          apply Finset.sup_le
          intro j hj
          refine (MvPolynomial.degreeOf_mul_le i _ _).trans ?_
          have hbd := hpoly_degree n (0 : Fin (N + 1)) i
            (basis j) (hbdeg j)
          have hrd := hrename_degree j i
          refine (add_le_add hrd hbd).trans ?_
          refine Fin.cases ?_ (fun k => ?_) i <;> simp [n]
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let q' : (Fin (Fintype.card ι) → ℝ) → ℝ := fun x => q (x ∘ e)
  let D' : Fin (Fintype.card ι) → ℕ := D ∘ e.symm
  have ht' (i : Fin (Fintype.card ι)) (x : Fin (Fintype.card ι) → ℝ) :
      Causalean.Mathlib.Analysis.JacksonApproximation.IsTrigPolyLE (D' i)
        (fun t => q' (Function.update x i t)) := by
    convert htrig (e.symm i) (x ∘ e) using 1
    · simp [D', D]
    · funext t
      change q ((Function.update x i t) ∘ e) =
        q (Function.update (x ∘ e) (e.symm i) t)
      apply congrArg q
      funext j
      by_cases hji : e j = i
      · have hj : j = e.symm i := by simp [← hji]
        subst j
        simp [Function.update]
      · have hj : j ≠ e.symm i := by
          intro h
          apply hji
          simpa [h] using e.apply_symm_apply i
        simp [Function.update, hji, hj]
  have he' (i : Fin (Fintype.card ι)) (x : Fin (Fintype.card ι) → ℝ) :
      Function.Even (fun t => q' (Function.update x i t)) := by
    convert heven (e.symm i) (x ∘ e) using 1
    funext t
    change q ((Function.update x i t) ∘ e) =
      q (Function.update (x ∘ e) (e.symm i) t)
    apply congrArg q
    funext j
    by_cases hji : e j = i
    · have hj : j = e.symm i := by simp [← hji]
      subst j
      simp [Function.update]
    · have hj : j ≠ e.symm i := by
        intro h
        apply hji
        simpa [h] using e.apply_symm_apply i
      simp [Function.update, hji, hj]
  rcases hfin (Fintype.card ι) D' q' ht' he' with ⟨p', hp', hb'⟩
  refine ⟨MvPolynomial.rename e.symm p', ?_, ?_⟩
  · intro x
    rw [MvPolynomial.eval_rename]
    have hx : (cosPoint x) ∘ e.symm = fun i => Real.cos ((x ∘ e.symm) i) := rfl
    rw [hx, hp']
    exact congrArg q (funext fun i => by simp [e.symm_apply_apply])
  · intro m hm i
    rw [MvPolynomial.support_rename_of_injective e.symm.injective] at hm
    rcases Finset.mem_image.mp hm with ⟨m', hm', rfl⟩
    have h := hb' m' hm' (e i)
    simpa [D', D, Finsupp.mapDomain_apply e.symm.injective] using h

/-- For [a coordinate-specific positive order map](hyp:d,hd), [a measurable cube target](hyp:f,hf),
and [a real bound B](hyp:B) such that [the target is at most B in absolute value on the
cube](hyp:hB), [there is a multivariate polynomial that reproduces the heterogeneous Jackson
convolution at the coordinatewise cosines of every phase vector and whose degree in each variable
is at most twice (that coordinate's order minus one)](goal). -/
theorem convolution_exists_polynomial (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (f : (ι → ℝ) → ℝ)
    (hf : Measurable f)
    (B : ℝ) (hB : ∀ x ∈ cube, |f x| ≤ B) :
    ∃ p : MvPolynomial ι ℝ,
      (∀ x : ι → ℝ, MvPolynomial.eval (cosPoint x) p = convolution d f x) ∧
      (∀ γ ∈ p.support, ∀ i, γ i ≤ 2 * (d i - 1)) := by
  exact polynomial_of_coord_even_trig d (convolution d f)
    (fun i x => convolution_coord_trig d hd f hf B hB i x)
    (fun i x => convolution_coord_even d f i x)

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensor
