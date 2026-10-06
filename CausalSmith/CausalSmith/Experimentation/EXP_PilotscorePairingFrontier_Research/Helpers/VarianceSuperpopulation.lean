module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Basic
public import Mathlib.Probability.CondVar

/-! # Superpopulation variance algebra

This module collects the measure-theoretic variance identities used to lift the
fixed-wave matched-pair calculation to the iid superpopulation experiment.
-/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The sum of the two outcome residuals has conditional mean zero given the
covariate. -/
lemma condExp_sum_outcome_residual_eq_zero
    (P : Measure (UnitRecord d))
    (hP : IsProbabilityMeasure P)
    (h0 : Integrable (fun u : UnitRecord d => u.2.1) P)
    (h1 : Integrable (fun u : UnitRecord d => u.2.2) P) :
    P[fun u => (u.2.2 + u.2.1) -
        (regression1 P u + regression0 P u) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[P] 0 := by
  letI : IsProbabilityMeasure P := hP
  have hm : MeasurableSpace.comap Prod.fst inferInstance ≤
      (inferInstance : MeasurableSpace (UnitRecord d)) := measurable_fst.comap_le
  have hr1 : Integrable (regression1 P) P := by
    exact integrable_condExp
  have hr0 : Integrable (regression0 P) P := by
    exact integrable_condExp
  have hrs : Integrable (fun u => regression1 P u + regression0 P u) P :=
    hr1.add hr0
  have hregsm : StronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance]
      (fun u : UnitRecord d => regression1 P u + regression0 P u) := by
    exact stronglyMeasurable_condExp.add stronglyMeasurable_condExp
  have hregce :
      P[fun u => regression1 P u + regression0 P u |
        MeasurableSpace.comap Prod.fst inferInstance] =
        fun u => regression1 P u + regression0 P u :=
    condExp_of_stronglyMeasurable (μ := P) hm hregsm hrs
  calc
    P[fun u => (u.2.2 + u.2.1) -
        (regression1 P u + regression0 P u) |
          MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[P]
        P[fun u => u.2.2 + u.2.1 |
          MeasurableSpace.comap Prod.fst inferInstance] -
          P[fun u => regression1 P u + regression0 P u |
            MeasurableSpace.comap Prod.fst inferInstance] :=
      condExp_sub (h1.add h0) hrs (MeasurableSpace.comap Prod.fst inferInstance)
    _ =ᵐ[P] (P[fun u => u.2.2 |
          MeasurableSpace.comap Prod.fst inferInstance] +
        P[fun u => u.2.1 | MeasurableSpace.comap Prod.fst inferInstance]) -
        (fun u => regression1 P u + regression0 P u) := by
      exact (condExp_add h1 h0 (MeasurableSpace.comap Prod.fst inferInstance)).sub
        (Filter.EventuallyEq.of_eq hregce)
    _ =ᵐ[P] 0 := by
      filter_upwards [] with u
      simp only [regression1, regression0, Pi.add_apply, Pi.sub_apply]
      change _ = (0 : ℝ)
      ring

/-- Expanding a square around an arbitrary constant splits it into population
variance and the squared displacement of that constant from the mean. -/
lemma integral_sq_sub_const_eq_realVariance_add_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (c : ℝ) (hμ : IsProbabilityMeasure μ)
    (hf : MemLp f 2 μ) :
    (∫ x, (f x - c) ^ 2 ∂μ) =
      realVariance μ f + ((∫ x, f x ∂μ) - c) ^ 2 := by
  letI : IsProbabilityMeasure μ := hμ
  have hfint : Integrable f μ := hf.integrable (by norm_num)
  have hfsq : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have hconst : Integrable (fun _ : α => c ^ 2) μ := integrable_const _
  have hleft :
      (∫ x, (f x - c) ^ 2 ∂μ) =
        (∫ x, f x ^ 2 ∂μ) - 2 * c * (∫ x, f x ∂μ) + c ^ 2 := by
    calc
      (∫ x, (f x - c) ^ 2 ∂μ) =
          ∫ x, (f x ^ 2 - (2 * c) * f x) + c ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
      _ = (∫ x, f x ^ 2 - (2 * c) * f x ∂μ) +
          ∫ _ : α, c ^ 2 ∂μ :=
        integral_add (hfsq.sub (hfint.const_mul (2 * c))) hconst
      _ = ((∫ x, f x ^ 2 ∂μ) - ∫ x, (2 * c) * f x ∂μ) +
          ∫ _ : α, c ^ 2 ∂μ := by
        rw [integral_sub hfsq (hfint.const_mul (2 * c))]
      _ = _ := by
        rw [integral_const_mul, integral_const]
        simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hleft]
  unfold realVariance
  have hvar :
      (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) =
        (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
    let a := ∫ y, f y ∂μ
    calc
      (∫ x, (f x - a) ^ 2 ∂μ) =
          ∫ x, (f x ^ 2 - (2 * a) * f x) + a ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
      _ = (∫ x, f x ^ 2 - (2 * a) * f x ∂μ) +
          ∫ _ : α, a ^ 2 ∂μ :=
        integral_add (hfsq.sub (hfint.const_mul (2 * a))) (integrable_const _)
      _ = ((∫ x, f x ^ 2 ∂μ) - ∫ x, (2 * a) * f x ∂μ) +
          ∫ _ : α, a ^ 2 ∂μ := by
        rw [integral_sub hfsq (hfint.const_mul (2 * a))]
      _ = _ := by
        rw [integral_const_mul, integral_const]
        simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
        dsimp [a]
        ring
  rw [hvar]
  ring

/-- The variance of an iid sample average is the one-observation variance
divided by the number of observations. -/
lemma realVariance_iid_average {α : Type*} [MeasurableSpace α] {N : ℕ}
    (P : Measure α) (hP : IsProbabilityMeasure P) (f : α → ℝ)
    (hf : MemLp f 2 P) (hN : 0 < N) :
    (N : ℝ) * realVariance (Measure.pi fun _ : Fin N => P)
      (fun us => (N : ℝ)⁻¹ * ∑ i : Fin N, f (us i)) =
      realVariance P f := by
  letI : IsProbabilityMeasure P := hP
  let μN := Measure.pi fun _ : Fin N => P
  let S : (Fin N → α) → ℝ := fun us => ∑ i : Fin N, f (us i)
  have hS : MemLp S 2 μN := by
    apply memLp_finset_sum Finset.univ
    intro i _
    exact hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => P) i)
  have hmean : MemLp (fun us => (N : ℝ)⁻¹ * S us) 2 μN := hS.const_mul _
  have hrv_mean : realVariance μN (fun us => (N : ℝ)⁻¹ * S us) =
      Var[fun us => (N : ℝ)⁻¹ * S us; μN] :=
    (variance_eq_integral hmean.aemeasurable).symm
  have hrv_f : realVariance P f = Var[f; P] :=
    (variance_eq_integral hf.aemeasurable).symm
  rw [hrv_mean, hrv_f, variance_const_mul]
  change (N : ℝ) * ((N : ℝ)⁻¹ ^ 2 *
    Var[fun us => ∑ i : Fin N, f (us i); Measure.pi fun _ : Fin N => P]) = Var[f; P]
  have hfun : (fun us : Fin N → α => ∑ i : Fin N, f (us i)) =
      ∑ i : Fin N, fun us => f (us i) := by
    funext us
    simp
  rw [hfun]
  rw [variance_sum_pi (fun _ : Fin N => hf)]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- For the two potential outcomes, the variance of their difference plus the
second moment of the treated-plus-control residual equals the semiparametric
efficiency expression. -/
lemma outcome_difference_variance_add_sum_residual_sq
    (P : Measure (UnitRecord d)) (hP : IsProbabilityMeasure P)
    (h0 : Integrable (fun u : UnitRecord d => u.2.1 ^ 2) P)
    (h1 : Integrable (fun u : UnitRecord d => u.2.2 ^ 2) P) :
    realVariance P (fun u => u.2.2 - u.2.1) +
        (∫ u, ((u.2.2 + u.2.1) -
          (regression1 P u + regression0 P u)) ^ 2 ∂P) =
      efficiencyBound P := by
  letI : IsProbabilityMeasure P := hP
  let y1 : UnitRecord d → ℝ := fun u => u.2.2
  let y0 : UnitRecord d → ℝ := fun u => u.2.1
  let t : UnitRecord d → ℝ := y1 - y0
  let q : UnitRecord d → ℝ := regression1 P - regression0 P
  let e1 : UnitRecord d → ℝ := y1 - regression1 P
  let e0 : UnitRecord d → ℝ := y0 - regression0 P
  have hy1 : MemLp y1 2 P := (memLp_two_iff_integrable_sq (by fun_prop)).2 h1
  have hy0 : MemLp y0 2 P := (memLp_two_iff_integrable_sq (by fun_prop)).2 h0
  have ht : MemLp t 2 P := hy1.sub hy0
  have hm : MeasurableSpace.comap Prod.fst inferInstance ≤
      (inferInstance : MeasurableSpace (UnitRecord d)) := measurable_fst.comap_le
  have hce : P[t | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[P] q := by
    simpa [t, q, y1, y0, regression1, regression0] using
      condExp_sub (hy1.integrable (by norm_num)) (hy0.integrable (by norm_num))
        (MeasurableSpace.comap Prod.fst inferInstance)
  have hq : MemLp q 2 P := by
    dsimp [q, regression1, regression0]
    exact (hy1.condExp (by norm_num)).sub (hy0.condExp (by norm_num))
  have he1 : MemLp e1 2 P := by
    dsimp [e1, y1, regression1]
    exact hy1.sub (hy1.condExp (by norm_num))
  have he0 : MemLp e0 2 P := by
    dsimp [e0, y0, regression0]
    exact hy0.sub (hy0.condExp (by norm_num))
  have hcond :
      (∫ u, Var[t; P | MeasurableSpace.comap Prod.fst inferInstance] u ∂P) =
        ∫ u, (t u - q u) ^ 2 ∂P := by
    unfold condVar
    calc
      (∫ u, P[(t - P[t | MeasurableSpace.comap Prod.fst inferInstance]) ^ 2 |
          MeasurableSpace.comap Prod.fst inferInstance] u ∂P) =
          ∫ u, ((t - P[t | MeasurableSpace.comap Prod.fst inferInstance]) ^ 2) u ∂P :=
        integral_condExp hm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hce] with u hu
        simp only [Pi.pow_apply, Pi.sub_apply, hu]
  have hvar :
      realVariance P t = (∫ u, (t u - q u) ^ 2 ∂P) + realVariance P q := by
    have htot := integral_condVar_add_variance_condExp
      (m := MeasurableSpace.comap Prod.fst inferInstance) hm ht
    have htvar : realVariance P t = Var[t; P] :=
      (variance_eq_integral ht.aemeasurable).symm
    have hqvar : realVariance P q = Var[q; P] :=
      (variance_eq_integral hq.aemeasurable).symm
    rw [hcond, variance_congr hce, ← htvar, ← hqvar] at htot
    linarith
  have hresminus : Integrable (fun u => (t u - q u) ^ 2) P :=
    (ht.sub hq).integrable_sq
  have hresplus : Integrable (fun u => (e1 u + e0 u) ^ 2) P :=
    (he1.add he0).integrable_sq
  have hresid :
      (∫ u, (t u - q u) ^ 2 ∂P) +
          (∫ u, (e1 u + e0 u) ^ 2 ∂P) =
        2 * ∫ u, (e1 u ^ 2 + e0 u ^ 2) ∂P := by
    calc
      (∫ u, (t u - q u) ^ 2 ∂P) +
          (∫ u, (e1 u + e0 u) ^ 2 ∂P) =
          ∫ u, (t u - q u) ^ 2 + (e1 u + e0 u) ^ 2 ∂P :=
        (integral_add hresminus hresplus).symm
      _ = ∫ u, 2 * (e1 u ^ 2 + e0 u ^ 2) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with u
        dsimp [t, q, e1, e0, y1, y0]
        ring
      _ = _ := integral_const_mul 2 _
  unfold efficiencyBound
  have hplusfun : (fun u : UnitRecord d =>
      ((u.2.2 + u.2.1) - (regression1 P u + regression0 P u)) ^ 2) =
      fun u => (e1 u + e0 u) ^ 2 := by
    funext u
    dsimp [e1, e0, y1, y0]
    ring
  rw [hplusfun]
  change realVariance P t + (∫ u, (e1 u + e0 u) ^ 2 ∂P) =
    realVariance P q + 2 * ∫ u, (e1 u ^ 2 + e0 u ^ 2) ∂P
  rw [hvar]
  linarith

end CausalSmith.Experimentation.PilotscorePairingFrontier
