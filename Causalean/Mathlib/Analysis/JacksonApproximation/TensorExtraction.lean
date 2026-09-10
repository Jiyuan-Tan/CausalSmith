import Causalean.Mathlib.Analysis.JacksonApproximation.Tensor

/-!
# Coordinatewise extraction of tensor Jackson convolutions

This module proves the periodic translation and coordinatewise trigonometric structure of tensor
Jackson convolution, extracts a multivariate algebraic polynomial, and derives its Lipschitz
approximation error.
-/

namespace Causalean.Mathlib.Analysis.JacksonApproximation

open MeasureTheory Real
open scoped BigOperators

private theorem integral_periodBox_succ {d : ℕ}
    (F : (Fin (d + 1) → ℝ) → ℝ) (hF : Continuous F) :
    (∫ u in periodBox (d + 1), F u) =
      ∫ t in Set.Icc (-Real.pi) Real.pi,
        ∫ v in periodBox d, F (Fin.insertNth 0 t v) := by
  let e : ℝ × (Fin d → ℝ) ≃ᵐ (Fin (d + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm _
  have he : e ⁻¹' periodBox (d + 1) =
      Set.Icc (-Real.pi) Real.pi ×ˢ periodBox d := by
    ext z
    simp only [Set.mem_preimage, periodBox, Set.mem_ofPred_eq, Set.mem_prod,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk]
    constructor
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩
    · rintro ⟨h0, hs⟩ i
      refine Fin.cases h0 (fun j => ?_) i
      exact hs j
  rw [← hem.setIntegral_preimage_emb e.measurableEmbedding, he,
    Measure.volume_eq_prod, setIntegral_prod]
  · rfl
  · have hc : Continuous (fun z : ℝ × (Fin d → ℝ) => F (Fin.insertNth 0 z.1 z.2)) := by
      fun_prop
    simpa only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk] using
      hc.continuousOn.integrableOn_compact
      (isCompact_Icc.prod (by
        rw [show periodBox d = {u | ∀ i, u i ∈ Set.Icc (-Real.pi) Real.pi} by rfl]
        exact isCompact_pi_infinite fun _ => isCompact_Icc))


private theorem periodBox_reflect_coord {d : ℕ}
    (F : (Fin d → ℝ) → ℝ) (hF : Continuous F) (i : Fin d) :
    (∫ u in periodBox d, F (Function.update u i (-u i))) =
      ∫ u in periodBox d, F u := by
  classical
  let e : (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) :=
    MeasurableEquiv.piCongrRight fun j =>
      if j = i then MeasurableEquiv.neg ℝ else MeasurableEquiv.refl ℝ
  have he_apply (u : Fin d → ℝ) : e u = Function.update u i (-u i) := by
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
  have he_box : e ⁻¹' periodBox d = periodBox d := by
    ext u
    simp only [Set.mem_preimage, periodBox, Set.mem_ofPred_eq, he_apply]
    constructor <;> intro h j
    · by_cases hji : j = i
      · subst j
        have hi := h i
        simp [Function.update] at hi
        change -Real.pi ≤ u i ∧ u i ≤ Real.pi
        constructor <;> linarith
      · simpa [Function.update, hji] using h j
    · by_cases hji : j = i
      · subst j
        have hi := h i
        change -Real.pi ≤ u i ∧ u i ≤ Real.pi at hi
        simp [Function.update]
        constructor <;> linarith
      · simpa [Function.update, hji] using h j
  calc
    (∫ u in periodBox d, F (Function.update u i (-u i))) =
        ∫ u in periodBox d, F (e u) := by simp only [he_apply]
    _ = ∫ u in periodBox d, F u := by
      simpa only [he_box] using
        (hem.setIntegral_preimage_emb e.measurableEmbedding F (periodBox d))

private theorem periodBox_translate {d : ℕ}
    (F : (Fin d → ℝ) → ℝ) (hF : Continuous F)
    (hper : ∀ (i : Fin d) (y : Fin d → ℝ),
      Function.Periodic (fun t => F (Function.update y i t)) (2 * Real.pi))
    (x : Fin d → ℝ) :
    (∫ u in periodBox d, F (x - u)) = ∫ u in periodBox d, F u := by
  induction d with
  | zero =>
      congr 1
      funext u
      congr 1
      funext i
      exact Fin.elim0 i
  | succ d ih =>
      rw [integral_periodBox_succ _ (by fun_prop)]
      have hxsub (t : ℝ) (v : Fin d → ℝ) :
          x - Fin.insertNth 0 t v =
            Fin.insertNth 0 (x 0 - t) ((x ∘ Fin.succ) - v) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp
      simp_rw [hxsub]
      have hinner (t : ℝ) :
          (∫ v in periodBox d,
              F (Fin.insertNth 0 (x 0 - t) ((x ∘ Fin.succ) - v))) =
            ∫ v in periodBox d, F (Fin.insertNth 0 (x 0 - t) v) := by
        let G : (Fin d → ℝ) → ℝ := fun v => F (Fin.insertNth 0 (x 0 - t) v)
        apply ih G
        · dsimp [G]
          fun_prop
        · intro i y
          dsimp [G]
          have hp := hper i.succ (Fin.insertNth 0 (x 0 - t) y)
          intro s
          change G (Function.update y i (s + 2 * Real.pi)) =
            G (Function.update y i s)
          dsimp [G]
          have hu (r : ℝ) :
              Fin.insertNth 0 (x 0 - t) (Function.update y i r) =
                (Function.update (Fin.insertNth 0 (x 0 - t) y) i.succ r :
                  Fin (d + 1) → ℝ) := by
            funext j
            refine Fin.cases ?_ (fun k => ?_) j
            · have hne : (0 : Fin (d + 1)) ≠ i.succ :=
                ne_of_lt (Fin.succ_pos i)
              simp [Function.update, hne]
            · by_cases hki : k = i
              · subst k
                simp
              · simp [hki]
          rw [hu, hu]
          exact hp s
      simp_rw [hinner]
      let A : ℝ → ℝ := fun s => ∫ v in periodBox d, F (Fin.insertNth 0 s v)
      have hAc : Continuous A := by
        apply continuous_parametric_integral_of_continuous
        · change Continuous (fun z : ℝ × (Fin d → ℝ) =>
            F (Fin.insertNth 0 z.1 z.2))
          fun_prop
        · rw [show periodBox d = {u | ∀ i, u i ∈ Set.Icc (-Real.pi) Real.pi} by rfl]
          exact isCompact_pi_infinite fun _ => isCompact_Icc
      have hAp : Function.Periodic A (2 * Real.pi) := by
        intro s
        apply integral_congr_ae
        filter_upwards
        intro v
        have hp := hper 0 (Fin.insertNth 0 s v) s
        simpa using hp
      rw [show (fun t => ∫ v in periodBox d, F (Fin.insertNth 0 (x 0 - t) v)) =
          fun t => A (x 0 - t) by rfl]
      rw [show (∫ t in Set.Icc (-Real.pi) Real.pi, A (x 0 - t)) =
          ∫ t in (-Real.pi)..Real.pi, A (x 0 - t) by
        rw [intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
          ← integral_Icc_eq_integral_Ioc]]
      rw [intervalIntegral.integral_comp_sub_left]
      have hshift := hAp.intervalIntegral_add_eq (x 0 - Real.pi) (-Real.pi)
      have heq : (∫ t in (x 0 - Real.pi)..(x 0 - -Real.pi), A t) =
          ∫ t in (-Real.pi)..Real.pi, A t := by
        convert hshift using 1 <;> ring
      rw [heq]
      rw [intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
        ← integral_Icc_eq_integral_Ioc]
      rw [integral_periodBox_succ F hF]

private lemma toMvPolynomial_degreeOf_le {σ : Type*} [DecidableEq σ]
    (n : ℕ) (i j : σ) (p : Polynomial ℝ) (hp : p.natDegree ≤ n) :
    (p.toMvPolynomial i).degreeOf j ≤ if j = i then n else 0 := by
  rw [p.as_sum_range_C_mul_X_pow'
    (lt_of_le_of_lt hp (Nat.lt_succ_self n))]
  simp only [map_sum, map_mul, map_pow, Polynomial.toMvPolynomial_C,
    Polynomial.toMvPolynomial_X]
  refine (MvPolynomial.degreeOf_sum_le j (Finset.range (n + 1))
    (fun k => MvPolynomial.C (p.coeff k) * MvPolynomial.X i ^ k)).trans ?_
  apply Finset.sup_le
  intro k hk
  refine (MvPolynomial.degreeOf_mul_le j _ _).trans ?_
  rw [MvPolynomial.degreeOf_C]
  by_cases hji : j = i
  · subst j
    simp only [if_true, zero_add, MvPolynomial.degreeOf_X_self_pow]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  · rw [MvPolynomial.degreeOf_X_pow_of_ne k hji]
    simp

private lemma toMvPolynomial_totalDegree_le {σ : Type*} [DecidableEq σ]
    (n : ℕ) (i : σ) (p : Polynomial ℝ) (hp : p.natDegree ≤ n) :
    (p.toMvPolynomial i).totalDegree ≤ n := by
  rw [p.as_sum_range_C_mul_X_pow'
    (lt_of_le_of_lt hp (Nat.lt_succ_self n))]
  simp only [map_sum, map_mul, map_pow, Polynomial.toMvPolynomial_C,
    Polynomial.toMvPolynomial_X]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow, zero_add]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)

private lemma trigPoly_periodic {n : ℕ} {q : ℝ → ℝ}
    (hq : IsTrigPolyLE n q) : Function.Periodic q (2 * Real.pi) := by
  classical
  rcases hq with ⟨a, b, hq⟩
  intro t
  rw [hq, hq]
  apply Finset.sum_congr rfl
  intro k hk
  have hc : Real.cos ((k : ℝ) * (t + 2 * Real.pi)) =
      Real.cos ((k : ℝ) * t) := by
    rw [show (k : ℝ) * (t + 2 * Real.pi) =
        (k : ℝ) * t + k * (2 * Real.pi) by push_cast; ring,
      Real.cos_add_nat_mul_two_pi]
  have hs : Real.sin ((k : ℝ) * (t + 2 * Real.pi)) =
      Real.sin ((k : ℝ) * t) := by
    rw [show (k : ℝ) * (t + 2 * Real.pi) =
        (k : ℝ) * t + k * (2 * Real.pi) by push_cast; ring,
      Real.sin_add_nat_mul_two_pi]
  rw [hc, hs]

private lemma tensorConvolution_shifted {d K : ℕ} (hK : 0 < K)
    (f : (Fin d → ℝ) → ℝ) (hf : ContinuousOn f (normalizedCube d))
    (x : Fin d → ℝ) :
    tensorConvolution K f x =
      ∫ v in periodBox d, f (cosPoint v) * tensorJackson K d (x - v) := by
  have hfcos : Continuous (fun v : Fin d → ℝ => f (cosPoint v)) := by
    apply hf.comp_continuous
    · unfold cosPoint
      fun_prop
    · exact fun v => cosPoint_mem_normalizedCube v
  have hjc : Continuous (tensorJackson K d) := by
    unfold tensorJackson
    fun_prop
  have hjp : Function.Periodic (jackson K) (2 * Real.pi) :=
    trigPoly_periodic (jackson_isTrigPolyLE K hK)
  let F : (Fin d → ℝ) → ℝ := fun v =>
    f (cosPoint v) * tensorJackson K d (x - v)
  have hFc : Continuous F := by
    dsimp [F]
    exact hfcos.mul (hjc.comp (by fun_prop))
  have hFp : ∀ (i : Fin d) (y : Fin d → ℝ),
      Function.Periodic (fun t => F (Function.update y i t)) (2 * Real.pi) := by
    intro i y t
    dsimp [F, tensorJackson, cosPoint]
    congr 1
    · congr 1
      funext j
      by_cases hji : j = i
      · subst j
        simp only [cosPoint, Function.update, if_pos rfl]
        change Real.cos (t + 2 * Real.pi) = Real.cos t
        exact Real.cos_add_two_pi t
      · simp only [cosPoint, Function.update]
        split <;> simp_all
    · apply Finset.prod_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j
        simp only [Function.update, if_pos rfl]
        change jackson K (x i - (t + 2 * Real.pi)) = jackson K (x i - t)
        convert (hjp (x i - t - 2 * Real.pi)).symm using 1 <;> ring
      · simp only [Function.update]
        split <;> simp_all
  unfold tensorConvolution
  have ht := periodBox_translate F hFc hFp x
  dsimp [F] at ht
  convert ht using 1
  · apply integral_congr_ae
    filter_upwards
    intro u
    congr 1
    · congr 1
      funext i
      change u i = x i - (x i - u i)
      ring

private lemma tensorConvolution_coord_even {d K : ℕ} (hK : 0 < K)
    (f : (Fin d → ℝ) → ℝ) (hf : ContinuousOn f (normalizedCube d))
    (x : Fin d → ℝ) (i : Fin d) :
    tensorConvolution K f (Function.update x i (-x i)) =
      tensorConvolution K f x := by
  have hfcos : Continuous (fun v : Fin d → ℝ => f (cosPoint v)) := by
    apply hf.comp_continuous
    · unfold cosPoint
      fun_prop
    · exact fun v => cosPoint_mem_normalizedCube v
  have hjc : Continuous (tensorJackson K d) := by
    unfold tensorJackson
    fun_prop
  let F : (Fin d → ℝ) → ℝ := fun u =>
    f (cosPoint (x - u)) * tensorJackson K d u
  have hFc : Continuous F := by
    dsimp [F]
    exact (hfcos.comp (by fun_prop)).mul hjc
  unfold tensorConvolution
  calc
    (∫ u in periodBox d,
        f (cosPoint (Function.update x i (-x i) - u)) * tensorJackson K d u) =
      ∫ u in periodBox d, F (Function.update u i (-u i)) := by
        apply integral_congr_ae
        filter_upwards
        intro u
        dsimp [F, cosPoint, tensorJackson]
        congr 1
        · congr 1
          funext j
          simp only [cosPoint, Pi.sub_apply]
          by_cases hji : j = i
          · subst j
            simp only [Function.update]
            split <;> simp_all
            change Real.cos (-x i - u i) = Real.cos (x i + u i)
            rw [show -x i - u i = -(x i + u i) by ring, Real.cos_neg]
          · simp only [Function.update]
            split <;> simp_all
        · apply Finset.prod_congr rfl
          intro j hj
          by_cases hji : j = i
          · subst j
            simp only [Function.update]
            split <;> simp_all
            change jackson K (u i) = jackson K (-u i)
            exact (jackson_even K (u i)).symm
          · simp only [Function.update]
            split <;> simp_all
    _ = ∫ u in periodBox d, F u := periodBox_reflect_coord F hFc i

private lemma tensorConvolution_coord_trig {d K : ℕ} (hK : 0 < K)
    (f : (Fin d → ℝ) → ℝ) (hf : ContinuousOn f (normalizedCube d))
    (x : Fin d → ℝ) (i : Fin d) :
    IsTrigPolyLE (2 * (K - 1))
      (fun t => tensorConvolution K f (Function.update x i t)) := by
  classical
  let n := 2 * (K - 1)
  rcases jackson_isTrigPolyLE K hK with ⟨a, b, hab⟩
  let W : (Fin d → ℝ) → ℝ := fun v =>
    f (cosPoint v) * ∏ j ∈ Finset.univ.erase i, jackson K (x j - v j)
  let A : ℕ → ℝ := fun k =>
    ∫ v in periodBox d,
      W v * (a k * Real.cos ((k : ℝ) * v i) -
        b k * Real.sin ((k : ℝ) * v i))
  let B : ℕ → ℝ := fun k =>
    ∫ v in periodBox d,
      W v * (a k * Real.sin ((k : ℝ) * v i) +
        b k * Real.cos ((k : ℝ) * v i))
  refine ⟨A, B, fun t => ?_⟩
  change tensorConvolution K f (Function.update x i t) = _
  rw [tensorConvolution_shifted hK f hf]
  have hcompact : IsCompact (periodBox d) := by
    rw [show periodBox d = {u | ∀ j, u j ∈ Set.Icc (-Real.pi) Real.pi} by rfl]
    exact isCompact_pi_infinite fun _ => isCompact_Icc
  have hW : Continuous W := by
    dsimp [W]
    apply Continuous.mul
    · apply hf.comp_continuous
      · unfold cosPoint
        fun_prop
      · exact fun v => cosPoint_mem_normalizedCube v
    · fun_prop
  have hint (k : ℕ) : IntegrableOn (fun v : Fin d → ℝ =>
      W v * (a k * Real.cos ((k : ℝ) * v i) -
        b k * Real.sin ((k : ℝ) * v i)) * Real.cos ((k : ℝ) * t) +
      W v * (a k * Real.sin ((k : ℝ) * v i) +
        b k * Real.cos ((k : ℝ) * v i)) * Real.sin ((k : ℝ) * t))
      (periodBox d) := by
    exact (by fun_prop : Continuous (fun v : Fin d → ℝ =>
      W v * (a k * Real.cos ((k : ℝ) * v i) -
        b k * Real.sin ((k : ℝ) * v i)) * Real.cos ((k : ℝ) * t) +
      W v * (a k * Real.sin ((k : ℝ) * v i) +
        b k * Real.cos ((k : ℝ) * v i)) * Real.sin ((k : ℝ) * t))).continuousOn
        |>.integrableOn_compact hcompact
  calc
    (∫ v in periodBox d,
      f (cosPoint v) * tensorJackson K d (Function.update x i t - v)) =
      ∫ v in periodBox d, W v * jackson K (t - v i) := by
        apply integral_congr_ae
        filter_upwards
        intro v
        dsimp [W, tensorJackson]
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        have herase :
            (∏ j ∈ Finset.univ.erase i,
                jackson K (Function.update x i t j - v j)) =
              ∏ j ∈ Finset.univ.erase i, jackson K (x j - v j) := by
          apply Finset.prod_congr rfl
          intro j hj
          have hji : j ≠ i := Finset.ne_of_mem_erase hj
          simp [Function.update, hji]
        rw [herase]
        simp [Function.update]
        ring
    _ = ∫ v in periodBox d,
        ∑ k ∈ Finset.range (n + 1),
          (W v * (a k * Real.cos ((k : ℝ) * v i) -
              b k * Real.sin ((k : ℝ) * v i)) * Real.cos ((k : ℝ) * t) +
            W v * (a k * Real.sin ((k : ℝ) * v i) +
              b k * Real.cos ((k : ℝ) * v i)) * Real.sin ((k : ℝ) * t)) := by
        apply integral_congr_ae
        filter_upwards
        intro v
        have htv := hab (t - v i)
        rw [htv]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [show (k : ℝ) * (t - v i) = (k : ℝ) * t - (k : ℝ) * v i by ring,
          Real.cos_sub, Real.sin_sub]
        ring
    _ = ∑ k ∈ Finset.range (n + 1),
        (A k * Real.cos ((k : ℝ) * t) +
          B k * Real.sin ((k : ℝ) * t)) := by
        rw [integral_finsetSum (Finset.range (n + 1)) (fun k hk => hint k)]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [A, B]
        rw [integral_add]
        · rw [integral_mul_const, integral_mul_const]
        · exact (by fun_prop : Continuous (fun v : Fin d → ℝ =>
            W v * (a k * Real.cos ((k : ℝ) * v i) -
              b k * Real.sin ((k : ℝ) * v i)) * Real.cos ((k : ℝ) * t))).continuousOn
              |>.integrableOn_compact hcompact
        · exact (by fun_prop : Continuous (fun v : Fin d → ℝ =>
            W v * (a k * Real.sin ((k : ℝ) * v i) +
              b k * Real.cos ((k : ℝ) * v i)) * Real.sin ((k : ℝ) * t))).continuousOn
              |>.integrableOn_compact hcompact

private theorem exists_mvPolynomial_of_coord_even_trig {d n : ℕ}
    (q : (Fin d → ℝ) → ℝ)
    (htrig : ∀ (i : Fin d) (x : Fin d → ℝ),
      IsTrigPolyLE n (fun t => q (Function.update x i t)))
    (heven : ∀ (i : Fin d) (x : Fin d → ℝ),
      Function.Even (fun t => q (Function.update x i t))) :
    ∃ p : MvPolynomial (Fin d) ℝ,
      (∀ x, MvPolynomial.eval (cosPoint x) p = q x) ∧
      (∀ m ∈ p.support, ∀ i, m i ≤ n) ∧
      p.totalDegree ≤ d * n := by
  induction d with
  | zero =>
      refine ⟨MvPolynomial.C (q 0), ?_, ?_, ?_⟩
      · intro (x : Fin 0 → ℝ)
        rw [MvPolynomial.eval_C]
        exact congrArg q (Subsingleton.elim 0 x)
      · intro m hm i
        exact Fin.elim0 i
      · simp
  | succ d ih =>
      classical
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
      let qtail : Fin (n + 1) → (Fin d → ℝ) → ℝ := fun j y =>
        q (Fin.cons (angle j) y)
      have htail_trig (j : Fin (n + 1)) (i : Fin d) (y : Fin d → ℝ) :
          IsTrigPolyLE n (fun t => qtail j (Function.update y i t)) := by
        have h := htrig i.succ (Fin.cons (angle j) y)
        simpa only [qtail, Fin.cons_update] using h
      have htail_even (j : Fin (n + 1)) (i : Fin d) (y : Fin d → ℝ) :
          Function.Even (fun t => qtail j (Function.update y i t)) := by
        have h := heven i.succ (Fin.cons (angle j) y)
        simpa only [qtail, Fin.cons_update] using h
      have hchoice (j : Fin (n + 1)) := ih (qtail j) (htail_trig j) (htail_even j)
      let ptail : Fin (n + 1) → MvPolynomial (Fin d) ℝ := fun j =>
        Classical.choose (hchoice j)
      have hptail (j : Fin (n + 1)) :
          (∀ y, MvPolynomial.eval (cosPoint y) (ptail j) = qtail j y) ∧
          (∀ m ∈ (ptail j).support, ∀ i, m i ≤ n) ∧
          (ptail j).totalDegree ≤ d * n := by
        dsimp [ptail]
        exact Classical.choose_spec (hchoice j)
      let basis : Fin (n + 1) → Polynomial ℝ := fun j =>
        Lagrange.basis Finset.univ node j
      let p : MvPolynomial (Fin (d + 1)) ℝ :=
        ∑ j, MvPolynomial.rename Fin.succ (ptail j) *
          (basis j).toMvPolynomial 0
      have hbdeg (j : Fin (n + 1)) : (basis j).natDegree ≤ n := by
        dsimp [basis]
        rw [Lagrange.natDegree_basis hnode_inj.injOn (Finset.mem_univ j),
          Finset.card_univ, Fintype.card_fin]
        omega
      have hrename_degree (j : Fin (n + 1)) (i : Fin (d + 1)) :
          (MvPolynomial.rename Fin.succ (ptail j)).degreeOf i ≤
            if i = 0 then 0 else n := by
        refine Fin.cases ?_ (fun k => ?_) i
        · simp only [if_pos rfl]
          apply MvPolynomial.degreeOf_le_iff.mpr
          intro m hm
          rw [MvPolynomial.support_rename_of_injective (Fin.succ_injective d)] at hm
          rcases Finset.mem_image.mp hm with ⟨m', hm', rfl⟩
          have hnot : (0 : Fin (d + 1)) ∉ Set.range Fin.succ := by
            rintro ⟨k, hk⟩
            exact Fin.ne_of_gt (Fin.succ_pos k) hk
          rw [Finsupp.mapDomain_of_notMem_range m' 0 hnot]
          simp
        · simp only [Fin.succ_ne_zero, if_false]
          rw [MvPolynomial.degreeOf_rename_of_injective (Fin.succ_injective d)]
          exact MvPolynomial.degreeOf_le_iff.mpr
            (fun m hm => (hptail j).2.1 m hm k)
      refine ⟨p, ?_, ?_⟩
      · intro x
        let sec : ℝ → ℝ := fun t => q (Fin.cons t (x ∘ Fin.succ))
        have hu (t : ℝ) : Function.update x 0 t = Fin.cons t (x ∘ Fin.succ) := by
          funext k
          refine Fin.cases ?_ (fun l => ?_) k <;> simp
        have hs_trig : IsTrigPolyLE n sec := by
          have h := htrig 0 x
          convert h using 1
          funext t
          dsimp [sec]
          exact congrArg q (hu t).symm
        have hs_even : Function.Even sec := by
          have h := heven 0 x
          intro t
          dsimp [sec]
          calc
            q (Fin.cons (-t) (x ∘ Fin.succ)) = q (Function.update x 0 (-t)) :=
              congrArg q (hu (-t)).symm
            _ = q (Function.update x 0 t) := h t
            _ = q (Fin.cons t (x ∘ Fin.succ)) := congrArg q (hu t)
        rcases even_trigPoly_exists_polynomial hs_trig hs_even with
          ⟨r, hrdeg, hr⟩
        have hr_degree : r.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
          rw [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
          calc
            r.degree ≤ (r.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
            _ < ((n + 1 : ℕ) : WithBot ℕ) := by
              exact_mod_cast (Nat.lt_succ_of_le hrdeg)
        have hinterp := Lagrange.eq_interpolate
          (s := (Finset.univ : Finset (Fin (n + 1))))
          (v := node) hnode_inj.injOn hr_degree
        change MvPolynomial.eval (cosPoint x) p = q x
        rw [show q x = sec (x 0) by
          congr 1
          funext k
          refine Fin.cases ?_ (fun l => ?_) k <;> simp [sec]]
        rw [← hr (x 0), hinterp]
        simp only [p, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
          MvPolynomial.eval_rename, MvPolynomial.eval_toMvPolynomial,
          Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
          Polynomial.eval_mul, Polynomial.eval_C]
        apply Finset.sum_congr rfl
        intro j hj
        have hcos_tail : cosPoint x ∘ Fin.succ = cosPoint (x ∘ Fin.succ) := by rfl
        rw [hcos_tail, (hptail j).1]
        simp only [Function.comp_apply, cosPoint]
        rw [show qtail j (x ∘ Fin.succ) = sec (angle j) by rfl,
          ← hr (angle j), hcos_angle]
      · constructor
        · intro m hm i
          refine (MvPolynomial.monomial_le_degreeOf i hm).trans ?_
          dsimp [p]
          refine (MvPolynomial.degreeOf_sum_le i Finset.univ
            (fun j => MvPolynomial.rename Fin.succ (ptail j) *
              (basis j).toMvPolynomial 0)).trans ?_
          apply Finset.sup_le
          intro j hj
          refine (MvPolynomial.degreeOf_mul_le i _ _).trans ?_
          refine (add_le_add (hrename_degree j i)
            (toMvPolynomial_degreeOf_le n 0 i (basis j) (hbdeg j))).trans ?_
          refine Fin.cases ?_ (fun k => ?_) i <;> simp
        · dsimp [p]
          apply MvPolynomial.totalDegree_finsetSum_le
          intro j hj
          refine (MvPolynomial.totalDegree_mul _ _).trans ?_
          calc
            (MvPolynomial.rename Fin.succ (ptail j)).totalDegree +
                ((basis j).toMvPolynomial 0).totalDegree ≤
              (ptail j).totalDegree + n := add_le_add
                (MvPolynomial.totalDegree_rename_le Fin.succ (ptail j))
                (toMvPolynomial_totalDegree_le n (0 : Fin (d + 1))
                  (basis j) (hbdeg j))
            _ ≤ d * n + n := Nat.add_le_add_right (hptail j).2.2 n
            _ = (d + 1) * n := (Nat.succ_mul d n).symm



/-- For [a finite dimension](hyp:d), [integer order K](hyp:K) that is [strictly positive](hyp:hK),
and [a function](hyp:f) that [is continuous on the normalized cube](hyp:hf), [its tensor
Jackson convolution is represented after the cosine change of coordinates by a multivariate
polynomial with the stated coordinate and total-degree bounds](goal).
-/
theorem tensorConvolution_exists_mvPolynomial {d K : ℕ} (hK : 0 < K)
    (f : (Fin d → ℝ) → ℝ) (hf : ContinuousOn f (normalizedCube d)) :
    ∃ p : MvPolynomial (Fin d) ℝ,
      (∀ x : Fin d → ℝ, MvPolynomial.eval (cosPoint x) p = tensorConvolution K f x) ∧
      (∀ m ∈ p.support, ∀ i, m i ≤ 2 * (K - 1)) ∧
      p.totalDegree ≤ d * (2 * (K - 1)) := by
  apply exists_mvPolynomial_of_coord_even_trig (q := tensorConvolution K f)
  · exact fun i x => tensorConvolution_coord_trig hK f hf x i
  · intro i x t
    have h := tensorConvolution_coord_even hK f hf
      (Function.update x i t) i
    simpa [Function.update] using h

/-- For [a finite dimension](hyp:d), [integer order K](hyp:K) that is [strictly positive](hyp:hK),
[a function](hyp:f), [a nonnegative Lipschitz constant](hyp:L,hL), [continuity on the
normalized cube](hyp:hf), [the stated local coordinatewise Lipschitz bound](hyp:hlip), and [a
point in period coordinates](hyp:x), [tensor Jackson convolution approximates the cosine lift
there within thirty-two times dimension times the Lipschitz constant divided by K](goal).
-/
theorem tensorConvolution_approx_lipschitz {d K : ℕ} (hK : 0 < K)
    (f : (Fin d → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ContinuousOn f (normalizedCube d))
    (hlip : ∀ x ∈ normalizedCube d, ∀ y ∈ normalizedCube d,
      |f x - f y| ≤ L * ∑ i, |x i - y i|)
    (x : Fin d → ℝ) :
    |tensorConvolution K f x - f (cosPoint x)| ≤ 32 * (d : ℝ) * L / (K : ℝ) := by
  classical
  have hcompact : IsCompact (periodBox d) := by
    rw [show periodBox d = {u | ∀ i, u i ∈ Set.Icc (-Real.pi) Real.pi} by rfl]
    exact isCompact_pi_infinite fun _ ↦ isCompact_Icc
  have hcos : Continuous (fun u : Fin d → ℝ ↦ cosPoint (x - u)) := by
    apply continuous_pi
    intro i
    change Continuous (fun u : Fin d → ℝ ↦ Real.cos (x i - u i))
    fun_prop
  have hfcos : Continuous (fun u : Fin d → ℝ ↦ f (cosPoint (x - u))) := by
    simpa [Function.comp_def] using
      hf.comp_continuous hcos (fun u ↦ cosPoint_mem_normalizedCube (x - u))
  have hkernel : Continuous (tensorJackson K d) := by
    unfold tensorJackson
    fun_prop
  have hconvInt : IntegrableOn
      (fun u : Fin d → ℝ ↦ f (cosPoint (x - u)) * tensorJackson K d u)
      (periodBox d) :=
    (hfcos.mul hkernel).continuousOn.integrableOn_compact hcompact
  have hconstInt : IntegrableOn
      (fun u : Fin d → ℝ ↦ f (cosPoint x) * tensorJackson K d u)
      (periodBox d) :=
    (continuous_const.mul hkernel).continuousOn.integrableOn_compact hcompact
  have hdiffInt : IntegrableOn
      (fun u : Fin d → ℝ ↦
        (f (cosPoint (x - u)) - f (cosPoint x)) * tensorJackson K d u)
      (periodBox d) :=
    ((hfcos.sub continuous_const).mul hkernel).continuousOn.integrableOn_compact hcompact
  have hmomentInt (i : Fin d) : IntegrableOn
      (fun u : Fin d → ℝ ↦ |u i| * tensorJackson K d u) (periodBox d) := by
    exact ((continuous_abs.comp (continuous_apply i)).mul hkernel).continuousOn
      |>.integrableOn_compact hcompact
  have hboundInt : IntegrableOn
      (fun u : Fin d → ℝ ↦ L * ∑ i, |u i| * tensorJackson K d u) (periodBox d) := by
    exact (continuous_const.mul (continuous_finsetSum _ fun i _ ↦
      (continuous_abs.comp (continuous_apply i)).mul hkernel)).continuousOn
      |>.integrableOn_compact hcompact
  have hdiff : tensorConvolution K f x - f (cosPoint x) =
      ∫ u in periodBox d,
        (f (cosPoint (x - u)) - f (cosPoint x)) * tensorJackson K d u := by
    unfold tensorConvolution
    calc
      (∫ u in periodBox d, f (cosPoint (x - u)) * tensorJackson K d u) -
          f (cosPoint x) =
          (∫ u in periodBox d, f (cosPoint (x - u)) * tensorJackson K d u) -
            f (cosPoint x) * (∫ u in periodBox d, tensorJackson K d u) := by
              rw [tensorJackson_integral_eq_one hK, mul_one]
      _ = (∫ u in periodBox d, f (cosPoint (x - u)) * tensorJackson K d u) -
            ∫ u in periodBox d, f (cosPoint x) * tensorJackson K d u := by
              rw [integral_const_mul]
      _ = ∫ u in periodBox d,
          (f (cosPoint (x - u)) * tensorJackson K d u -
            f (cosPoint x) * tensorJackson K d u) :=
              (integral_sub hconvInt hconstInt).symm
      _ = ∫ u in periodBox d,
          (f (cosPoint (x - u)) - f (cosPoint x)) * tensorJackson K d u := by
            apply integral_congr_ae
            filter_upwards
            intro u
            ring
  rw [hdiff]
  calc
    |∫ u in periodBox d,
        (f (cosPoint (x - u)) - f (cosPoint x)) * tensorJackson K d u| ≤
        ∫ u in periodBox d,
          |(f (cosPoint (x - u)) - f (cosPoint x)) * tensorJackson K d u| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ u in periodBox d, L * ∑ i, |u i| * tensorJackson K d u := by
      apply setIntegral_mono hdiffInt.abs hboundInt
      intro u
      change |(f (cosPoint (x - u)) - f (cosPoint x)) * tensorJackson K d u| ≤
        L * ∑ i, |u i| * tensorJackson K d u
      rw [abs_mul, abs_of_nonneg (tensorJackson_nonneg hK u)]
      calc
        |f (cosPoint (x - u)) - f (cosPoint x)| * tensorJackson K d u ≤
            (L * ∑ i, |u i|) * tensorJackson K d u := by
          apply mul_le_mul_of_nonneg_right _ (tensorJackson_nonneg hK u)
          refine (hlip _ (cosPoint_mem_normalizedCube _) _
            (cosPoint_mem_normalizedCube _)).trans ?_
          apply mul_le_mul_of_nonneg_left _ hL
          apply Finset.sum_le_sum
          intro i _
          simpa [cosPoint] using Real.abs_cos_sub_cos_le ((x - u) i) (x i)
        _ = L * ∑ i, |u i| * tensorJackson K d u := by
          rw [mul_assoc, Finset.sum_mul]
    _ = L * ∑ i, ∫ u in periodBox d, |u i| * tensorJackson K d u := by
      rw [integral_const_mul]
      rw [integral_finsetSum Finset.univ (fun i _ ↦ hmomentInt i)]
    _ ≤ L * ∑ _i : Fin d, 32 / (K : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hL
      apply Finset.sum_le_sum
      intro i _
      rw [tensorJackson_first_moment_eq hK i]
      exact jackson_first_moment K hK
    _ = 32 * (d : ℝ) * L / (K : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end Causalean.Mathlib.Analysis.JacksonApproximation
