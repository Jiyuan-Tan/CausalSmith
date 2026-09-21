/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Substrate.Archive.PoissonAddOnePoincare.Scalar
public import Causalean.Mathlib.Probability.VarianceProd
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.ProductMeasure

/-!
# Finite-product tensorization of Poisson add-one Poincaré inequalities

This module tensorizes variance over `Measure.pi`, using coordinate replacement to express
conditional variances and add-one increments. It also provides a nested paired-coordinate
form whose sample space is directly of the shape `i → j → Nat × Nat`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace CausalSmith.Substrate.PoissonAddOnePoincare

noncomputable section

/-- Replace coordinate `i` of a dependent finite product point by `y`. -/
def coordinateReplace
    {iota : Type*} [DecidableEq iota] {X : iota → Type*}
    (i : iota) (x : (j : iota) → X j) (y : X i) : (j : iota) → X j :=
  Function.update x i y

/-- The add-one increment of a statistic in coordinate `i`. -/
def coordinateAddOne
    {iota : Type*} [DecidableEq iota]
    (i : iota) (F : (iota → Nat) → Real) (x : iota → Nat) : Real :=
  F (Function.update x i (x i + 1)) - F x

/-- The finite product law of independent Poisson coordinates with the supplied rates. -/
def poissonPi
    {iota : Type*} [Fintype iota] (lambda : iota → NNReal) :
    Measure (iota → Nat) :=
  Measure.pi fun i ↦ poissonMeasure (lambda i)

private lemma memLp_integral_prod_right
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (nu : Measure B)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (H : A × B → Real) (hH : MemLp H 2 (mu.prod nu)) :
    MemLp (fun b ↦ ∫ a, H (a, b) ∂mu) 2 nu := by
  have hsq : Integrable (fun z ↦ H z ^ 2) (mu.prod nu) := hH.integrable_sq
  have hm : AEStronglyMeasurable (fun b ↦ ∫ a, H (a, b) ∂mu) nu :=
    hH.aestronglyMeasurable.prod_swap.integral_prod_right'
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  have hq : Integrable (fun b ↦ ∫ a, H (a, b) ^ 2 ∂mu) nu :=
    hsq.integral_prod_right
  apply hq.mono_nonneg (hm.pow 2) (ae_of_all _ fun _ ↦ sq_nonneg _)
  filter_upwards [hH.aestronglyMeasurable.prod_swap.prodMk_left, hsq.prod_left_ae]
    with b hbmeas hbsq
  have hb : MemLp (fun a ↦ H (a, b)) 2 mu :=
    (memLp_two_iff_integrable_sq hbmeas).2 hbsq
  have hv := variance_nonneg (fun a ↦ H (a, b)) mu
  rw [variance_eq_sub hb] at hv
  simpa only [Pi.pow_apply] using (sub_nonneg.mp hv)

private lemma variance_integral_prod_right_le_integral_variance
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (nu : Measure B)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (H : A × B → Real) (hH : MemLp H 2 (mu.prod nu)) :
    variance (fun b ↦ ∫ a, H (a, b) ∂mu) nu ≤
      ∫ a, variance (fun b ↦ H (a, b)) nu ∂mu := by
  let m : B → Real := fun b ↦ ∫ a, H (a, b) ∂mu
  let r : A → Real := fun a ↦ ∫ b, H (a, b) ∂nu
  let G : A × B → Real := fun z ↦ H z - r z.1
  have hm : MemLp m 2 nu := memLp_integral_prod_right mu nu H hH
  have hr : MemLp r 2 mu := by
    have hs := memLp_integral_prod_right nu mu (H ∘ Prod.swap)
      (hH.comp_measurePreserving Measure.measurePreserving_swap)
    simpa only [r, Function.comp_apply, Prod.swap_prod_mk] using hs
  have hG : MemLp G 2 (mu.prod nu) := by
    exact hH.sub (hr.comp_fst nu)
  have hHint : Integrable H (mu.prod nu) := hH.integrable (by norm_num)
  have hmean : (∫ a, r a ∂mu) = ∫ b, m b ∂nu := by
    rw [show (∫ a, r a ∂mu) = ∫ z, H z ∂(mu.prod nu) by
      exact (integral_prod H hHint).symm]
    exact integral_prod_symm H hHint
  have hcenter :
      (fun b ↦ m b - ∫ b, m b ∂nu) =ᵐ[nu] fun b ↦ ∫ a, G (a, b) ∂mu := by
    filter_upwards [hHint.prod_left_ae] with b hb
    rw [show (∫ a, G (a, b) ∂mu) = m b - ∫ a, r a ∂mu by
      simp only [G]
      rw [integral_sub hb (hr.integrable (by norm_num))]]
    rw [hmean]
  have hsq : Integrable (fun z ↦ G z ^ 2) (mu.prod nu) := hG.integrable_sq
  have hbound : ∀ᵐ b ∂nu, (∫ a, G (a, b) ∂mu) ^ 2 ≤ ∫ a, G (a, b) ^ 2 ∂mu := by
    filter_upwards [hG.aestronglyMeasurable.prod_swap.prodMk_left, hsq.prod_left_ae]
      with b hbmeas hbsq
    have hb : MemLp (fun a ↦ G (a, b)) 2 mu :=
      (memLp_two_iff_integrable_sq hbmeas).2 hbsq
    have hv := variance_nonneg (fun a ↦ G (a, b)) mu
    rw [variance_eq_sub hb] at hv
    exact sub_nonneg.mp hv
  calc
    variance m nu = ∫ b, (m b - ∫ b, m b ∂nu) ^ 2 ∂nu :=
      variance_eq_integral hm.aemeasurable
    _ = ∫ b, (∫ a, G (a, b) ∂mu) ^ 2 ∂nu :=
      integral_congr_ae (hcenter.fun_comp fun x ↦ x ^ 2)
    _ ≤ ∫ b, ∫ a, G (a, b) ^ 2 ∂mu ∂nu := by
      exact integral_mono_ae (memLp_integral_prod_right mu nu G hG).integrable_sq
        hsq.integral_prod_right hbound
    _ = ∫ a, ∫ b, G (a, b) ^ 2 ∂nu ∂mu := by
      exact (integral_prod_symm _ hsq).symm.trans (integral_prod _ hsq)
    _ = ∫ a, variance (fun b ↦ H (a, b)) nu ∂mu := by
      apply integral_congr_ae
      filter_upwards [hH.aestronglyMeasurable.prodMk_left,
        hH.integrable_sq.prod_right_ae] with a hameas hasq
      have ha : MemLp (fun b ↦ H (a, b)) 2 nu :=
        (memLp_two_iff_integrable_sq hameas).2 hasq
      rw [variance_eq_integral ha.aemeasurable]

private lemma variance_prod_le_integral_variance_add_integral_variance
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (nu : Measure B)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (H : A × B → Real) (hH : MemLp H 2 (mu.prod nu)) :
    variance H (mu.prod nu) ≤
      (∫ b, variance (fun a ↦ H (a, b)) mu ∂nu) +
        ∫ a, variance (fun b ↦ H (a, b)) nu ∂mu := by
  let m : B → Real := fun b ↦ ∫ a, H (a, b) ∂mu
  have hm : MemLp m 2 nu := memLp_integral_prod_right mu nu H hH
  have hsection : ∀ᵐ b ∂nu, MemLp (fun a ↦ H (a, b)) 2 mu := by
    filter_upwards [hH.aestronglyMeasurable.prod_swap.prodMk_left,
      hH.integrable_sq.prod_left_ae] with b hbmeas hbsq
    exact (memLp_two_iff_integrable_sq hbmeas).2 hbsq
  rw [Causalean.Mathlib.Probability.variance_prod_eq_integral_variance_add
    mu nu H m hH hsection hm (ae_of_all nu fun _ ↦ rfl)]
  have hc := variance_integral_prod_right_le_integral_variance mu nu H hH
  exact add_le_add_right hc _

private lemma integrable_variance_prod_right
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (nu : Measure B)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (H : A × B → Real) (hH : MemLp H 2 (mu.prod nu)) :
    Integrable (fun a ↦ variance (fun b ↦ H (a, b)) nu) mu := by
  let r : A → Real := fun a ↦ ∫ b, H (a, b) ∂nu
  have hr : MemLp r 2 mu := by
    have hs := memLp_integral_prod_right nu mu (H ∘ Prod.swap)
      (hH.comp_measurePreserving Measure.measurePreserving_swap)
    simpa only [r, Function.comp_apply, Prod.swap_prod_mk] using hs
  have hq : Integrable (fun a ↦ ∫ b, H (a, b) ^ 2 ∂nu) mu :=
    hH.integrable_sq.integral_prod_left
  apply (hq.sub hr.integrable_sq).congr
  filter_upwards [hH.aestronglyMeasurable.prodMk_left,
    hH.integrable_sq.prod_right_ae] with a hameas hasq
  have ha : MemLp (fun b ↦ H (a, b)) 2 nu :=
    (memLp_two_iff_integrable_sq hameas).2 hasq
  rw [variance_eq_sub ha]
  rfl

private lemma integrable_fin_coordinateVariance
    {n : Nat} {X : Fin n → Type*} [(i : Fin n) → MeasurableSpace (X i)]
    (mu : (i : Fin n) → Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (F : ((i : Fin n) → X i) → Real) (hF : MemLp F 2 (Measure.pi mu))
    (i : Fin n) :
    Integrable (fun x ↦ variance (fun y ↦ F (Function.update x i y)) (mu i))
      (Measure.pi mu) := by
  rcases n with _ | n
  · exact Fin.elim0 i
  · let e := MeasurableEquiv.piFinSuccAbove X i
    let tailMu : (j : Fin n) → Measure (X (i.succAbove j)) :=
      fun j ↦ mu (i.succAbove j)
    let H : X i × ((j : Fin n) → X (i.succAbove j)) → Real := fun z ↦ F (e.symm z)
    have hmp := measurePreserving_piFinSuccAbove mu i
    have hH : MemLp H 2 ((mu i).prod (Measure.pi tailMu)) := by
      change MemLp (F ∘ e.symm) 2
        ((mu i).prod (Measure.pi fun j ↦ mu (i.succAbove j)))
      exact hF.comp_measurePreserving hmp.symm
    have hswap : MemLp (H ∘ Prod.swap) 2 ((Measure.pi tailMu).prod (mu i)) :=
      hH.comp_measurePreserving Measure.measurePreserving_swap
    have hv : Integrable
        (fun z ↦ variance (fun y ↦ H (y, z)) (mu i)) (Measure.pi tailMu) := by
      simpa only [Function.comp_apply, Prod.swap_prod_mk] using
        integrable_variance_prod_right (Measure.pi tailMu) (mu i) (H ∘ Prod.swap) hswap
    have hvprod : Integrable
        (fun z : X i × ((j : Fin n) → X (i.succAbove j)) ↦
          variance (fun y ↦ H (y, z.2)) (mu i))
        ((mu i).prod (Measure.pi tailMu)) := hv.comp_snd (mu i)
    have hc := hmp.integrable_comp_of_integrable hvprod
    convert hc using 1
    funext x
    congr 1
    funext y
    simp [H, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

private theorem variance_pi_fin
    (n : Nat) {X : Fin n → Type*} [(i : Fin n) → MeasurableSpace (X i)]
    (mu : (i : Fin n) → Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (F : ((i : Fin n) → X i) → Real) (hF : MemLp F 2 (Measure.pi mu)) :
    variance F (Measure.pi mu) ≤
      ∑ i : Fin n, ∫ x,
        variance (fun y ↦ F (Function.update x i y)) (mu i) ∂(Measure.pi mu) := by
  induction n with
  | zero =>
      let x₀ : (i : Fin 0) → X i := fun i ↦ Fin.elim0 i
      have hconst : F = fun _ ↦ F x₀ := by
        funext x
        congr 1
        funext i
        exact Fin.elim0 i
      rw [hconst]
      rw [variance_eq_sub (memLp_const (μ := Measure.pi mu) (F x₀))]
      simp
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove X 0
      let tailMu : (j : Fin n) → Measure (X ((0 : Fin (n + 1)).succAbove j)) :=
        fun j ↦ mu ((0 : Fin (n + 1)).succAbove j)
      let H : X 0 × ((j : Fin n) → X ((0 : Fin (n + 1)).succAbove j)) → Real :=
        fun z ↦ F (e.symm z)
      have hmp := measurePreserving_piFinSuccAbove mu 0
      have hH : MemLp H 2 ((mu 0).prod (Measure.pi tailMu)) := by
        change MemLp (F ∘ e.symm) 2
          ((mu 0).prod (Measure.pi fun j ↦ mu ((0 : Fin (n + 1)).succAbove j)))
        exact hF.comp_measurePreserving hmp.symm
      have hvar : variance F (Measure.pi mu) =
          variance H ((mu 0).prod (Measure.pi tailMu)) := by
        have hv := hmp.variance_fun_comp hH.aemeasurable
        calc
          variance F (Measure.pi mu) =
              variance (H ∘ e) (Measure.pi mu) := by
            congr 1
            funext x
            exact congrArg F (e.symm_apply_apply x).symm
          _ = variance H ((mu 0).prod (Measure.pi tailMu)) := by
            change variance (H ∘ e) (Measure.pi mu) =
              variance H ((mu 0).prod
                (Measure.pi fun j ↦ mu ((0 : Fin (n + 1)).succAbove j)))
            change variance (H ∘ e) (Measure.pi mu) = _ at hv
            exact hv
      have hslices : ∀ᵐ a ∂mu 0, MemLp (fun x ↦ H (a, x)) 2 (Measure.pi tailMu) := by
        filter_upwards [hH.aestronglyMeasurable.prodMk_left,
          hH.integrable_sq.prod_right_ae] with a hameas hasq
        exact (memLp_two_iff_integrable_sq hameas).2 hasq
      have hihae : ∀ᵐ a ∂mu 0,
          variance (fun x ↦ H (a, x)) (Measure.pi tailMu) ≤
            ∑ j : Fin n, ∫ x,
              variance (fun y ↦ H (a, Function.update x j y)) (tailMu j)
                ∂(Measure.pi tailMu) := by
        filter_upwards [hslices] with a ha
        exact ih tailMu (fun x ↦ H (a, x)) ha
      have hleft : Integrable
          (fun a ↦ variance (fun x ↦ H (a, x)) (Measure.pi tailMu)) (mu 0) :=
        integrable_variance_prod_right (mu 0) (Measure.pi tailMu) H hH
      have hright_each (j : Fin n) : Integrable (fun a ↦
          ∫ x, variance (fun y ↦ H (a, Function.update x j y)) (tailMu j)
            ∂(Measure.pi tailMu)) (mu 0) := by
        let K : X 0 × ((k : Fin n) → X ((0 : Fin (n + 1)).succAbove k)) → Real :=
          fun z ↦
          variance (fun y ↦ H (z.1, Function.update z.2 j y)) (tailMu j)
        have hcFull := integrable_fin_coordinateVariance mu F hF
          ((0 : Fin (n + 1)).succAbove j)
        have hcProd : Integrable K ((mu 0).prod (Measure.pi tailMu)) := by
          apply (hmp.integrable_comp_emb e.measurableEmbedding).mp
          have hk : K ∘ e = fun x ↦
              variance (fun y ↦ F (Function.update x ((0 : Fin (n + 1)).succAbove j) y))
                (mu ((0 : Fin (n + 1)).succAbove j)) := by
            funext x
            simp only [K, Function.comp_apply, tailMu]
            apply congrArg
              (fun f ↦ variance f (mu ((0 : Fin (n + 1)).succAbove j)))
            funext y
            apply congrArg F
            change Fin.insertNth 0 (x 0) (Function.update (Fin.removeNth 0 x) j y) =
              Function.update x ((0 : Fin (n + 1)).succAbove j) y
            rw [Fin.insertNth_update, Fin.insertNth_self_removeNth]
          change Integrable (K ∘ e) (Measure.pi mu)
          rw [hk]
          exact hcFull
        simpa only [K] using hcProd.integral_prod_left
      have hright : Integrable (fun a ↦
          ∑ j : Fin n, ∫ x,
            variance (fun y ↦ H (a, Function.update x j y)) (tailMu j)
              ∂(Measure.pi tailMu)) (mu 0) := by
        exact integrable_finsetSum Finset.univ (fun j _ ↦ hright_each j)
      have htensor := variance_prod_le_integral_variance_add_integral_variance
        (mu 0) (Measure.pi tailMu) H hH
      have hstep : variance H ((mu 0).prod (Measure.pi tailMu)) ≤
          (∫ x, variance (fun a ↦ H (a, x)) (mu 0) ∂(Measure.pi tailMu)) +
            ∫ a, ∑ j : Fin n, ∫ x,
              variance (fun y ↦ H (a, Function.update x j y)) (tailMu j)
                ∂(Measure.pi tailMu) ∂(mu 0) :=
        htensor.trans (add_le_add_right (integral_mono_ae hleft hright hihae) _)
      rw [hvar]
      calc
        variance H ((mu 0).prod (Measure.pi tailMu)) ≤ _ := hstep
        _ = (∫ x, variance (fun y ↦ F (Function.update x 0 y)) (mu 0)
              ∂(Measure.pi mu)) +
            ∑ j : Fin n, ∫ x,
              variance (fun y ↦ F (Function.update x ((0 : Fin (n + 1)).succAbove j) y))
                (mu ((0 : Fin (n + 1)).succAbove j))
                ∂(Measure.pi mu) := by
          rw [integral_finsetSum Finset.univ (fun j _ ↦ hright_each j)]
          congr 1
          · let K₀ : X 0 × ((k : Fin n) → X ((0 : Fin (n + 1)).succAbove k)) → Real :=
              fun z ↦
                variance (fun y ↦ H (y, z.2)) (mu 0)
            have hk₀ : K₀ ∘ e = fun x ↦
                variance (fun y ↦ F (Function.update x 0 y)) (mu 0) := by
              funext x
              simp only [K₀, Function.comp_apply]
              apply congrArg (fun f ↦ variance f (mu 0))
              funext y
              apply congrArg F
              change Fin.insertNth 0 y (Fin.removeNth 0 x) = Function.update x 0 y
              exact Fin.insertNth_removeNth 0 y x
            have hcFull := integrable_fin_coordinateVariance mu F hF 0
            have hcProd : Integrable K₀ ((mu 0).prod (Measure.pi tailMu)) := by
              apply (hmp.integrable_comp_emb e.measurableEmbedding).mp
              change Integrable (K₀ ∘ e) (Measure.pi mu)
              rw [hk₀]
              exact hcFull
            have hi := hmp.integral_comp' K₀
            have hi' : (∫ x, variance (fun y ↦ F (Function.update x 0 y)) (mu 0)
                  ∂(Measure.pi mu)) = ∫ z, K₀ z ∂((mu 0).prod (Measure.pi tailMu)) := by
              rw [← hk₀]
              change (∫ x, (K₀ ∘ e) x ∂(Measure.pi mu)) = _
              exact hi
            have hp := integral_prod K₀ hcProd
            have hp' : (∫ z, K₀ z ∂((mu 0).prod (Measure.pi tailMu))) =
                ∫ x, variance (fun y ↦ H (y, x)) (mu 0) ∂(Measure.pi tailMu) := by
              simpa [K₀] using hp
            exact hp'.symm.trans hi'.symm
          · apply Finset.sum_congr rfl
            intro j _
            let K : X 0 × ((k : Fin n) → X ((0 : Fin (n + 1)).succAbove k)) → Real :=
              fun z ↦
                variance (fun y ↦ H (z.1, Function.update z.2 j y)) (tailMu j)
            have hk : K ∘ e = fun x ↦
                variance (fun y ↦ F (Function.update x ((0 : Fin (n + 1)).succAbove j) y))
                  (mu ((0 : Fin (n + 1)).succAbove j)) := by
              funext x
              simp only [K, Function.comp_apply, tailMu]
              apply congrArg
                (fun f ↦ variance f (mu ((0 : Fin (n + 1)).succAbove j)))
              funext y
              apply congrArg F
              change Fin.insertNth 0 (x 0) (Function.update (Fin.removeNth 0 x) j y) =
                Function.update x ((0 : Fin (n + 1)).succAbove j) y
              rw [Fin.insertNth_update, Fin.insertNth_self_removeNth]
            have hcFull := integrable_fin_coordinateVariance mu F hF
              ((0 : Fin (n + 1)).succAbove j)
            have hcProd : Integrable K ((mu 0).prod (Measure.pi tailMu)) := by
              apply (hmp.integrable_comp_emb e.measurableEmbedding).mp
              change Integrable (K ∘ e) (Measure.pi mu)
              rw [hk]
              exact hcFull
            have hi := hmp.integral_comp' K
            have hi' : (∫ x,
                  variance (fun y ↦ F (Function.update x ((0 : Fin (n + 1)).succAbove j) y))
                    (mu ((0 : Fin (n + 1)).succAbove j))
                    ∂(Measure.pi mu)) = ∫ z, K z ∂((mu 0).prod (Measure.pi tailMu)) := by
              rw [← hk]
              change (∫ x, (K ∘ e) x ∂(Measure.pi mu)) = _
              exact hi
            have hp := integral_prod K hcProd
            exact hp.symm.trans hi'.symm
        _ = _ := by
          simp only [Fin.zero_succAbove]
          rw [Fin.sum_univ_succ]
          rfl

/-- The variance of a square-integrable statistic under a finite product probability law is
at most the sum of the expected variances obtained by resampling one coordinate at a time. -/
theorem variance_pi_le_sum_integral_coordinateVariance
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {X : iota → Type*} [(i : iota) → MeasurableSpace (X i)]
    (mu : (i : iota) → Measure (X i))
    [∀ i, IsProbabilityMeasure (mu i)]
    (F : ((i : iota) → X i) → Real)
    (hF : MemLp F 2 (Measure.pi mu)) :
    variance F (Measure.pi mu) ≤
      ∑ i : iota, ∫ x,
        variance (fun y ↦ F (coordinateReplace i x y)) (mu i)
          ∂(Measure.pi mu) := by
  classical
  let e : Fin (Fintype.card iota) ≃ iota := (Fintype.equivFin iota).symm
  let phi := MeasurableEquiv.piCongrLeft X e
  let nu : (k : Fin (Fintype.card iota)) → Measure (X (e k)) := fun k ↦ mu (e k)
  let G : ((k : Fin (Fintype.card iota)) → X (e k)) → Real := F ∘ phi
  have hmp := measurePreserving_piCongrLeft mu e
  have hG : MemLp G 2 (Measure.pi nu) := by
    exact hF.comp_measurePreserving hmp
  have h := variance_pi_fin (Fintype.card iota) nu G hG
  have hvar := hmp.variance_fun_comp hF.aemeasurable
  rw [show variance F (Measure.pi mu) = variance G (Measure.pi nu) by
    exact hvar.symm]
  calc
    variance G (Measure.pi nu) ≤ ∑ k, ∫ z,
        variance (fun y ↦ G (Function.update z k y)) (nu k) ∂(Measure.pi nu) := h
    _ = ∑ k, ∫ x,
        variance (fun y ↦ F (coordinateReplace (e k) x y)) (mu (e k))
          ∂(Measure.pi mu) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← hmp.integral_comp']
      apply integral_congr_ae
      filter_upwards with z
      congr 1
      funext y
      apply congrArg F
      funext a
      obtain ⟨j, rfl⟩ := e.surjective a
      by_cases hj : j = k
      · subst j
        simp [phi, coordinateReplace, MeasurableEquiv.piCongrLeft_apply_apply]
      · simp [phi, coordinateReplace, MeasurableEquiv.piCongrLeft_apply_apply, hj]
    _ = _ := e.sum_comp (fun i ↦ ∫ x,
      variance (fun y ↦ F (coordinateReplace i x y)) (mu i) ∂(Measure.pi mu))

private lemma poisson_fin_coordinate_bound
    {n : Nat} (lambda : Fin n → NNReal) (F : (Fin n → Nat) → Real)
    (hF : MemLp F 2 (poissonPi lambda))
    (hD : ∀ i, MemLp (coordinateAddOne i F) 2 (poissonPi lambda))
    (i : Fin n) :
    (∫ x, variance (fun y ↦ F (Function.update x i y))
        (poissonMeasure (lambda i)) ∂(poissonPi lambda)) ≤
      (lambda i : Real) *
        ∫ x, (coordinateAddOne i F x) ^ 2 ∂(poissonPi lambda) := by
  rcases n with _ | n
  · exact Fin.elim0 i
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Nat) i
  let tailMu : (j : Fin n) → Measure Nat :=
    fun j ↦ poissonMeasure (lambda (i.succAbove j))
  let H : Nat × (Fin n → Nat) → Real := fun z ↦ F (e.symm z)
  let DH : Nat × (Fin n → Nat) → Real :=
    fun z ↦ addOne (fun y ↦ H (y, z.2)) z.1
  have hmp := measurePreserving_piFinSuccAbove
    (fun k : Fin (n + 1) ↦ poissonMeasure (lambda k)) i
  have hH : MemLp H 2 ((poissonMeasure (lambda i)).prod (Measure.pi tailMu)) := by
    change MemLp (F ∘ e.symm) 2 _
    exact hF.comp_measurePreserving hmp.symm
  have hDHcomp : DH ∘ e = coordinateAddOne i F := by
    funext x
    simp [DH, H, e, addOne, coordinateAddOne,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hDH : MemLp DH 2 ((poissonMeasure (lambda i)).prod (Measure.pi tailMu)) := by
    have heq : DH = coordinateAddOne i F ∘ e.symm := by
      funext z
      have hz := congrFun hDHcomp (e.symm z)
      simpa [Function.comp_apply] using hz
    rw [heq]
    exact (hD i).comp_measurePreserving hmp.symm
  have hslices : ∀ᵐ z ∂Measure.pi tailMu,
      MemLp (fun y ↦ H (y, z)) 2 (poissonMeasure (lambda i)) := by
    filter_upwards [hH.aestronglyMeasurable.prod_swap.prodMk_left,
      hH.integrable_sq.prod_left_ae] with z hzmeas hzsq
    exact (memLp_two_iff_integrable_sq hzmeas).2 hzsq
  have hDslices : ∀ᵐ z ∂Measure.pi tailMu,
      MemLp (addOne (fun y ↦ H (y, z))) 2 (poissonMeasure (lambda i)) := by
    filter_upwards [hDH.aestronglyMeasurable.prod_swap.prodMk_left,
      hDH.integrable_sq.prod_left_ae] with z hzmeas hzsq
    exact (memLp_two_iff_integrable_sq hzmeas).2 hzsq
  have hsliceBound : ∀ᵐ z ∂Measure.pi tailMu,
      variance (fun y ↦ H (y, z)) (poissonMeasure (lambda i)) ≤
        (lambda i : Real) * ∫ y, (addOne (fun a ↦ H (a, z)) y) ^ 2
          ∂(poissonMeasure (lambda i)) := by
    filter_upwards [hslices, hDslices] with z hz hDz
    exact poisson_addOne_poincare (lambda i) (fun y ↦ H (y, z)) hz hDz
  have hleft : Integrable
      (fun z ↦ variance (fun y ↦ H (y, z)) (poissonMeasure (lambda i)))
      (Measure.pi tailMu) := by
    have hs := hH.comp_measurePreserving Measure.measurePreserving_swap
    simpa only [Function.comp_apply, Prod.swap_prod_mk] using
      integrable_variance_prod_right (Measure.pi tailMu)
        (poissonMeasure (lambda i)) (H ∘ Prod.swap) hs
  have hright : Integrable (fun z ↦
      (lambda i : Real) * ∫ y, (addOne (fun a ↦ H (a, z)) y) ^ 2
        ∂(poissonMeasure (lambda i))) (Measure.pi tailMu) := by
    exact hDH.integrable_sq.integral_prod_right.const_mul _
  have hint := integral_mono_ae hleft hright hsliceBound
  have hleftEq :
      (∫ x, variance (fun y ↦ F (Function.update x i y))
          (poissonMeasure (lambda i)) ∂(poissonPi lambda)) =
        ∫ z, variance (fun y ↦ H (y, z)) (poissonMeasure (lambda i))
          ∂(Measure.pi tailMu) := by
    let V : Nat × (Fin n → Nat) → Real := fun z ↦
      variance (fun y ↦ H (y, z.2)) (poissonMeasure (lambda i))
    have hVe : V ∘ e = fun x ↦ variance (fun y ↦ F (Function.update x i y))
        (poissonMeasure (lambda i)) := by
      funext x
      simp only [V, Function.comp_apply]
      apply congrArg (fun f ↦ variance f (poissonMeasure (lambda i)))
      funext y
      apply congrArg F
      change Fin.insertNth i y (Fin.removeNth i x) = Function.update x i y
      exact Fin.insertNth_removeNth i y x
    have hVprod : Integrable V
        ((poissonMeasure (lambda i)).prod (Measure.pi tailMu)) := hleft.comp_snd _
    rw [← hVe]
    calc
      (∫ x, (V ∘ e) x ∂Measure.pi (fun k ↦ poissonMeasure (lambda k))) =
          ∫ z, V z ∂((poissonMeasure (lambda i)).prod (Measure.pi tailMu)) :=
        hmp.integral_comp' V
      _ = _ := by
        rw [integral_prod_symm V hVprod]
        simp [V]
  have hrightEq :
      (∫ z, (lambda i : Real) * ∫ y, (addOne (fun a ↦ H (a, z)) y) ^ 2
          ∂(poissonMeasure (lambda i)) ∂(Measure.pi tailMu)) =
        (lambda i : Real) *
          ∫ x, (coordinateAddOne i F x) ^ 2 ∂(poissonPi lambda) := by
    have hp := integral_prod_symm (fun z ↦ DH z ^ 2) hDH.integrable_sq
    have hm := hmp.integral_comp' (fun z ↦ DH z ^ 2)
    calc
      (∫ z, (lambda i : Real) * ∫ y, (addOne (fun a ↦ H (a, z)) y) ^ 2
          ∂(poissonMeasure (lambda i)) ∂(Measure.pi tailMu)) =
          (lambda i : Real) * ∫ z, ∫ y, DH (y, z) ^ 2
            ∂(poissonMeasure (lambda i)) ∂(Measure.pi tailMu) := by
        rw [integral_const_mul]
      _ = (lambda i : Real) * ∫ z, DH z ^ 2
          ∂((poissonMeasure (lambda i)).prod (Measure.pi tailMu)) := by rw [hp]
      _ = (lambda i : Real) * ∫ x, DH (e x) ^ 2
          ∂(Measure.pi fun k ↦ poissonMeasure (lambda k)) := by rw [hm]
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        rw [show DH (e x) = coordinateAddOne i F x by
          exact congrFun hDHcomp x]
  rw [hleftEq, ← hrightEq]
  exact hint

private theorem poissonPi_fin_addOne_poincare
    (n : Nat) (lambda : Fin n → NNReal) (F : (Fin n → Nat) → Real)
    (hF : MemLp F 2 (poissonPi lambda))
    (hD : ∀ i, MemLp (coordinateAddOne i F) 2 (poissonPi lambda)) :
    variance F (poissonPi lambda) ≤
      ∑ i : Fin n, (lambda i : Real) *
        ∫ x, (coordinateAddOne i F x) ^ 2 ∂(poissonPi lambda) := by
  calc
    variance F (poissonPi lambda) ≤ ∑ i : Fin n, ∫ x,
        variance (fun y ↦ F (Function.update x i y)) (poissonMeasure (lambda i))
          ∂(poissonPi lambda) :=
      variance_pi_fin n (fun i ↦ poissonMeasure (lambda i)) F hF
    _ ≤ _ := Finset.sum_le_sum fun i _ ↦ poisson_fin_coordinate_bound lambda F hF hD i

private lemma piCongrLeft_update_const
    {alpha beta Y : Type*} [DecidableEq alpha] [DecidableEq beta]
    [MeasurableSpace Y] (e : alpha ≃ beta) (z : alpha → Y) (k : alpha) (y : Y) :
    MeasurableEquiv.piCongrLeft (fun _ : beta ↦ Y) e (Function.update z k y) =
      Function.update (MeasurableEquiv.piCongrLeft (fun _ : beta ↦ Y) e z) (e k) y := by
  funext a
  obtain ⟨j, rfl⟩ := e.surjective a
  by_cases hj : j = k
  · subst j
    simp [MeasurableEquiv.piCongrLeft_apply_apply]
  · simp [MeasurableEquiv.piCongrLeft_apply_apply, hj]

/-- A square-integrable statistic of finitely many independent Poisson coordinates has
variance at most the sum, over coordinates, of the rate times the expected squared
coordinate add-one increment. -/
theorem poissonPi_addOne_poincare
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (lambda : iota → NNReal) (F : (iota → Nat) → Real)
    (hF : MemLp F 2 (poissonPi lambda))
    (hD : ∀ i, MemLp (coordinateAddOne i F) 2 (poissonPi lambda)) :
    variance F (poissonPi lambda) ≤
      ∑ i : iota, (lambda i : Real) *
        ∫ x, (coordinateAddOne i F x) ^ 2 ∂(poissonPi lambda) := by
  classical
  let e : Fin (Fintype.card iota) ≃ iota := (Fintype.equivFin iota).symm
  let phi := MeasurableEquiv.piCongrLeft (fun _ : iota ↦ Nat) e
  let lambda' : Fin (Fintype.card iota) → NNReal := fun k ↦ lambda (e k)
  let G : (Fin (Fintype.card iota) → Nat) → Real := F ∘ phi
  have hmp := measurePreserving_piCongrLeft
    (fun i ↦ poissonMeasure (lambda i)) e
  have hG : MemLp G 2 (poissonPi lambda') :=
    hF.comp_measurePreserving hmp
  have hDG (k : Fin (Fintype.card iota)) :
      MemLp (coordinateAddOne k G) 2 (poissonPi lambda') := by
    have heq : coordinateAddOne k G = coordinateAddOne (e k) F ∘ phi := by
      funext z
      simp only [coordinateAddOne, G, Function.comp_apply]
      rw [piCongrLeft_update_const e z k (z k + 1)]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rw [heq]
    exact (hD (e k)).comp_measurePreserving hmp
  have hfin := poissonPi_fin_addOne_poincare (Fintype.card iota) lambda' G hG hDG
  have hvar := hmp.variance_fun_comp hF.aemeasurable
  rw [show variance F (poissonPi lambda) = variance G (poissonPi lambda') by
    exact hvar.symm]
  calc
    variance G (poissonPi lambda') ≤ ∑ k, (lambda' k : Real) *
        ∫ z, (coordinateAddOne k G z) ^ 2 ∂(poissonPi lambda') := hfin
    _ = ∑ k, (lambda (e k) : Real) *
        ∫ x, (coordinateAddOne (e k) F x) ^ 2 ∂(poissonPi lambda) := by
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      change (∫ z, (coordinateAddOne k G z) ^ 2
          ∂Measure.pi (fun j ↦ poissonMeasure (lambda (e j)))) =
        ∫ x, (coordinateAddOne (e k) F x) ^ 2
          ∂Measure.pi (fun i ↦ poissonMeasure (lambda i))
      rw [← hmp.integral_comp']
      apply integral_congr_ae
      filter_upwards with z
      simp only [coordinateAddOne, G, Function.comp_apply]
      rw [piCongrLeft_update_const e z k (z k + 1)]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
    _ = _ := e.sum_comp (fun i ↦ (lambda i : Real) *
      ∫ x, (coordinateAddOne i F x) ^ 2 ∂(poissonPi lambda))

/-- The nested product law with two independent Poisson counts at each `(i,j)` cell. -/
def nestedPairedPoissonMeasure
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal) :
    Measure (iota → kappa → Nat × Nat) :=
  Measure.pi fun i ↦ Measure.pi fun j ↦
    (poissonMeasure (lambda₁ i j)).prod (poissonMeasure (lambda₂ i j))

/-- Add one to the first Poisson count in nested cell `(i,j)`. -/
def nestedPairAddOneFst
    {iota kappa : Type*} [DecidableEq iota] [DecidableEq kappa]
    (i : iota) (j : kappa)
    (F : (iota → kappa → Nat × Nat) → Real)
    (x : iota → kappa → Nat × Nat) : Real :=
  F (Function.update x i
      (Function.update (x i) j ((x i j).1 + 1, (x i j).2))) - F x

/-- Add one to the second Poisson count in nested cell `(i,j)`. -/
def nestedPairAddOneSnd
    {iota kappa : Type*} [DecidableEq iota] [DecidableEq kappa]
    (i : iota) (j : kappa)
    (F : (iota → kappa → Nat × Nat) → Real)
    (x : iota → kappa → Nat × Nat) : Real :=
  F (Function.update x i
      (Function.update (x i) j ((x i j).1, (x i j).2 + 1))) - F x

private lemma measurePreserving_piCurry_probability
    {alpha : Type*} {beta : alpha → Type*}
    [Fintype alpha] [∀ i, Fintype (beta i)]
    {X : (i : alpha) → beta i → Type*} [∀ i j, MeasurableSpace (X i j)]
    (mu : (i : alpha) → (j : beta i) → Measure (X i j))
    [∀ i j, IsProbabilityMeasure (mu i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry X)
      (Measure.pi fun p : Sigma beta ↦ mu p.1 p.2)
      (Measure.pi fun i ↦ Measure.pi (mu i)) := by
  refine ⟨(MeasurableEquiv.piCurry X).measurable, ?_⟩
  simpa only [Measure.infinitePi_eq_pi] using Measure.infinitePi_map_piCurry mu

private lemma measurePreserving_piCongrRight_probability
    {alpha : Type*} [Fintype alpha]
    {X Y : alpha → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (mu : (i : alpha) → Measure (X i)) (nu : (i : alpha) → Measure (Y i))
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, IsProbabilityMeasure (nu i)]
    (e : ∀ i, X i ≃ᵐ Y i) (he : ∀ i, MeasurePreserving (e i) (mu i) (nu i)) :
    MeasurePreserving (MeasurableEquiv.piCongrRight e) (Measure.pi mu) (Measure.pi nu) := by
  refine ⟨(MeasurableEquiv.piCongrRight e).measurable, ?_⟩
  change (Measure.pi mu).map (fun x i ↦ e i (x i)) = Measure.pi nu
  rw [Measure.pi_map_pi fun i ↦ (he i).measurable.aemeasurable]
  congr 1
  funext i
  exact (he i).map_eq

/-- For a nested finite array of independent Poisson pairs, variance is bounded by the sum
of the two rate-weighted expected squared add-one increments in every cell. -/
theorem nestedPairedPoisson_addOne_poincare
    {iota kappa : Type*}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [DecidableEq kappa]
    (lambda₁ lambda₂ : iota → kappa → NNReal)
    (F : (iota → kappa → Nat × Nat) → Real)
    (hF : MemLp F 2 (nestedPairedPoissonMeasure lambda₁ lambda₂))
    (hD₁ : ∀ i j, MemLp
      (nestedPairAddOneFst (iota := iota) (kappa := kappa) i j F) 2
      (nestedPairedPoissonMeasure lambda₁ lambda₂))
    (hD₂ : ∀ i j, MemLp
      (nestedPairAddOneSnd (iota := iota) (kappa := kappa) i j F) 2
      (nestedPairedPoissonMeasure lambda₁ lambda₂)) :
    variance F (nestedPairedPoissonMeasure lambda₁ lambda₂) ≤
      Finset.univ.sum (fun i : iota ↦ Finset.univ.sum (fun j : kappa ↦
        ((lambda₁ i j : Real) *
            ∫ x : iota → kappa → Nat × Nat,
              (nestedPairAddOneFst (iota := iota) (kappa := kappa)
                (i : iota) (j : kappa) F x) ^ 2
              ∂(nestedPairedPoissonMeasure lambda₁ lambda₂)) +
          ((lambda₂ i j : Real) *
            ∫ x : iota → kappa → Nat × Nat,
              (nestedPairAddOneSnd (iota := iota) (kappa := kappa)
                (i : iota) (j : kappa) F x) ^ 2
              ∂(nestedPairedPoissonMeasure lambda₁ lambda₂)))) := by
  classical
  let flatIndex := Sigma fun _ : iota ↦ Sigma fun _ : kappa ↦ Fin 2
  let flatLambda : flatIndex → NNReal := fun p ↦
    Fin.cases (lambda₁ p.1 p.2.1) (fun _ ↦ lambda₂ p.1 p.2.1) p.2.2
  let e₁ := MeasurableEquiv.piCurry
    (fun (_ : iota) (_ : Sigma fun _ : kappa ↦ Fin 2) ↦ Nat)
  let e₂ := MeasurableEquiv.piCongrRight (fun _ : iota ↦
    MeasurableEquiv.piCurry (fun (_ : kappa) (_ : Fin 2) ↦ Nat))
  let e₃ := MeasurableEquiv.piCongrRight (fun _ : iota ↦
    MeasurableEquiv.piCongrRight (fun _ : kappa ↦
      MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ Nat)))
  let e := e₁.trans (e₂.trans e₃)
  let mu₀ : Measure (flatIndex → Nat) := poissonPi flatLambda
  let mu₁ : Measure (iota → (Sigma fun _ : kappa ↦ Fin 2) → Nat) :=
    Measure.pi fun i ↦ Measure.pi fun q ↦ poissonMeasure (flatLambda ⟨i, q⟩)
  let mu₂ : Measure (iota → kappa → Fin 2 → Nat) :=
    Measure.pi fun i ↦ Measure.pi fun j ↦ Measure.pi fun b ↦
      poissonMeasure (flatLambda ⟨i, ⟨j, b⟩⟩)
  let mu₃ : Measure (iota → kappa → Nat × Nat) :=
    nestedPairedPoissonMeasure lambda₁ lambda₂
  have hmp₁ : MeasurePreserving e₁ mu₀ mu₁ := by
    simpa [e₁, mu₀, mu₁, poissonPi, flatIndex] using
      (measurePreserving_piCurry_probability
        (fun (i : iota) (q : Sigma fun _ : kappa ↦ Fin 2) ↦
          poissonMeasure (flatLambda ⟨i, q⟩)))
  have hmp₂ : MeasurePreserving e₂ mu₁ mu₂ := by
    apply measurePreserving_piCongrRight_probability
    intro i
    simpa [mu₁, mu₂, e₂] using
      (measurePreserving_piCurry_probability
        (fun (j : kappa) (b : Fin 2) ↦ poissonMeasure (flatLambda ⟨i, ⟨j, b⟩⟩)))
  have hmp₃ : MeasurePreserving e₃ mu₂ mu₃ := by
    apply measurePreserving_piCongrRight_probability
    intro i
    apply measurePreserving_piCongrRight_probability
    intro j
    convert (measurePreserving_piFinTwo (fun b : Fin 2 ↦
      poissonMeasure (Fin.cases (lambda₁ i j) (fun _ ↦ lambda₂ i j) b))) using 1
    · simp [mu₂, mu₃, e₃, nestedPairedPoissonMeasure, flatLambda]
      congr 2
  have hmp : MeasurePreserving e mu₀ mu₃ := by
    exact hmp₃.comp (hmp₂.comp hmp₁)
  have he_apply (z : flatIndex → Nat) (i : iota) (j : kappa) :
      e z i j = (z ⟨i, ⟨j, 0⟩⟩, z ⟨i, ⟨j, 1⟩⟩) := by
    rfl
  have he_update_fst (z : flatIndex → Nat) (i : iota) (j : kappa) :
      e (Function.update z ⟨i, ⟨j, 0⟩⟩ (z ⟨i, ⟨j, 0⟩⟩ + 1)) =
        Function.update (e z) i
          (Function.update (e z i) j ((e z i j).1 + 1, (e z i j).2)) := by
    funext i' j'
    rw [he_apply]
    by_cases hi : i' = i <;> by_cases hj : j' = j
    · subst i'
      subst j'
      simp [he_apply]
    · subst i'
      simp [he_apply, hj]
    · simp [he_apply, hi]
    · simp [he_apply, hi]
  have he_update_snd (z : flatIndex → Nat) (i : iota) (j : kappa) :
      e (Function.update z ⟨i, ⟨j, 1⟩⟩ (z ⟨i, ⟨j, 1⟩⟩ + 1)) =
        Function.update (e z) i
          (Function.update (e z i) j ((e z i j).1, (e z i j).2 + 1)) := by
    funext i' j'
    rw [he_apply]
    by_cases hi : i' = i <;> by_cases hj : j' = j
    · subst i'
      subst j'
      simp [he_apply]
    · subst i'
      simp [he_apply, hj]
    · simp [he_apply, hi]
    · simp [he_apply, hi]
  let G : (flatIndex → Nat) → Real := F ∘ e
  have hG : MemLp G 2 mu₀ := hF.comp_measurePreserving hmp
  have hDpoint_fst (i : iota) (j : kappa) :
      coordinateAddOne ⟨i, ⟨j, 0⟩⟩ G = nestedPairAddOneFst i j F ∘ e := by
    funext z
    simp only [coordinateAddOne, G, Function.comp_apply, nestedPairAddOneFst]
    rw [he_update_fst]
  have hDpoint_snd (i : iota) (j : kappa) :
      coordinateAddOne ⟨i, ⟨j, 1⟩⟩ G = nestedPairAddOneSnd i j F ∘ e := by
    funext z
    simp only [coordinateAddOne, G, Function.comp_apply, nestedPairAddOneSnd]
    rw [he_update_snd]
  have hDG (p : flatIndex) : MemLp (coordinateAddOne p G) 2 mu₀ := by
    rcases p with ⟨i, j, b⟩
    have hb : b = 0 ∨ b = 1 := by omega
    rcases hb with rfl | rfl
    ·
      rw [hDpoint_fst]
      exact (hD₁ i j).comp_measurePreserving hmp
    ·
      rw [hDpoint_snd]
      exact (hD₂ i j).comp_measurePreserving hmp
  have hflat := poissonPi_addOne_poincare flatLambda G hG hDG
  have henergy_fst (i : iota) (j : kappa) :
      (∫ z, (coordinateAddOne ⟨i, ⟨j, 0⟩⟩ G z) ^ 2 ∂mu₀) =
        ∫ x, (nestedPairAddOneFst i j F x) ^ 2 ∂mu₃ := by
    rw [← hmp.integral_comp']
    apply integral_congr_ae
    filter_upwards with z
    rw [congrFun (hDpoint_fst i j) z]
    rfl
  have henergy_snd (i : iota) (j : kappa) :
      (∫ z, (coordinateAddOne ⟨i, ⟨j, 1⟩⟩ G z) ^ 2 ∂mu₀) =
        ∫ x, (nestedPairAddOneSnd i j F x) ^ 2 ∂mu₃ := by
    rw [← hmp.integral_comp']
    apply integral_congr_ae
    filter_upwards with z
    rw [congrFun (hDpoint_snd i j) z]
    rfl
  have hvar := hmp.variance_fun_comp hF.aemeasurable
  rw [show variance F mu₃ = variance G mu₀ by exact hvar.symm]
  calc
    variance G mu₀ ≤ ∑ p : flatIndex, (flatLambda p : Real) *
        ∫ z, (coordinateAddOne p G z) ^ 2 ∂mu₀ := hflat
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro j _
      rw [Fin.sum_univ_two, henergy_fst, henergy_snd]
      congr 2

end

end CausalSmith.Substrate.PoissonAddOnePoincare
