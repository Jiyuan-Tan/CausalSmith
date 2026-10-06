module

public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.WeakLaw

/-!
# Vector conditional bootstrap weak laws

This module derives finite-dimensional norm-valued bootstrap weak laws from the scalar result,
using coordinate projections and a finite union bound.
-/

public section

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators Topology

noncomputable section

variable {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  {mu : Measure Omega} {P : Measure X}

private theorem euclidean_norm_le_sum_abs
    {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ ≤ ∑ j, |v j| := by
  rw [EuclideanSpace.norm_eq]
  apply (Real.sqrt_le_iff).2
  constructor
  · exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  · simpa [Real.norm_eq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := Finset.univ) (f := fun j ↦ |v j|)
        (fun j hj ↦ abs_nonneg (v j)))

private theorem finMean_apply
    {d n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    (finMean v) j = finMean (fun i ↦ v i j) := by
  unfold finMean
  simp [Finset.sum_apply]

private theorem euclidean_norm_event_subset
    {A : Type*} {d : ℕ} (hd : d ≠ 0)
    (v : A → EuclideanSpace ℝ (Fin d)) (epsilon : ℝ) :
    {x | epsilon < ‖v x‖} ⊆
      ⋃ j : Fin d, {x | epsilon / d < |v x j|} := by
  intro x hx
  by_contra hnot
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at hnot
  have hsum :
      ∑ j : Fin d, |v x j| ≤ ∑ _j : Fin d, epsilon / d :=
    Finset.sum_le_sum fun j hj ↦ hnot j
  have hcard : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hsum_eq : (∑ _j : Fin d, epsilon / d) = epsilon := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have := (euclidean_norm_le_sum_abs (v x)).trans hsum
  rw [hsum_eq] at this
  exact (not_lt_of_ge this) hx

/-- **Finite-dimensional conditional bootstrap weak law.** For [an iid sample](hyp:S) and a
[measurable integrable vector statistic](hyp:g,hg,hg_int), for almost every data sequence and
every positive tolerance, [the conditional probability that the resample vector mean differs
in norm from the data vector mean tends to zero](goal). -/
theorem bootstrapMeanVec_sub_dataMean_tendsto_zero_ae
    {d : ℕ} (S : IIDSample Omega X mu P)
    (g : X → EuclideanSpace ℝ (Fin d))
    (hg : Measurable g) (hg_int : Integrable g P) :
    ∀ᵐ omega ∂mu, ∀ epsilon : ℝ, 0 < epsilon →
      Tendsto
        (fun n ↦ (bootstrapResample (S.sampleVector n omega)).real
          {xstar | epsilon <
            ‖finMean (fun i ↦ g (xstar i)) -
              finMean (fun i ↦ g (S.sampleVector n omega i))‖})
        atTop (𝓝 0) := by
  have hcoord : ∀ᵐ omega ∂mu, ∀ j : Fin d, ∀ epsilon : ℝ, 0 < epsilon →
      Tendsto
        (fun n ↦ (bootstrapResample (S.sampleVector n omega)).real
          {xstar | epsilon <
            |finMean (fun i ↦ g (xstar i) j) -
              finMean (fun i ↦ g (S.sampleVector n omega i) j)|})
        atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro j
    exact bootstrapMean_sub_dataMean_tendsto_zero_ae S
      (fun x ↦ g x j) (by fun_prop) (hg_int.eval_piLp j)
  filter_upwards [hcoord] with omega homega
  intro epsilon hepsilon
  by_cases hd : d = 0
  · subst d
    have hvzero : ∀ n (xstar : Fin n → X),
        finMean (fun i ↦ g (xstar i)) -
          finMean (fun i ↦ g (S.sampleVector n omega i)) = 0 :=
      fun n xstar ↦ Subsingleton.elim _ _
    simp_rw [hvzero, norm_zero, not_lt_of_ge hepsilon.le]
    simp
  · let eta : ℝ := epsilon / d
    have heta : 0 < eta := by
      dsimp [eta]
      positivity
    have hsum : Tendsto
        (fun n ↦ ∑ j : Fin d,
          (bootstrapResample (S.sampleVector n omega)).real
            {xstar | eta <
              |finMean (fun i ↦ g (xstar i) j) -
                finMean (fun i ↦ g (S.sampleVector n omega i) j)|})
        atTop (𝓝 0) := by
      simpa using tendsto_finset_sum Finset.univ
        (fun j hj ↦ homega j eta heta)
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ measureReal_nonneg
    · filter_upwards [eventually_ne_atTop 0] with n hn
      let data : Fin n → X := S.sampleVector n omega
      let V : (Fin n → X) → EuclideanSpace ℝ (Fin d) := fun xstar ↦
        finMean (fun i ↦ g (xstar i)) -
          finMean (fun i ↦ g (data i))
      have hset :
          {xstar | epsilon < ‖V xstar‖} ⊆
            ⋃ j : Fin d, {xstar | eta <
              |finMean (fun i ↦ g (xstar i) j) -
                finMean (fun i ↦ g (data i) j)|} := by
        have hs := euclidean_norm_event_subset hd V epsilon
        simpa only [V, eta, finMean_apply, PiLp.sub_apply] using hs
      let _ : IsProbabilityMeasure (bootstrapResample data) :=
        bootstrapResample_isProbabilityMeasure data hn
      calc
        (bootstrapResample (S.sampleVector n omega)).real
            {xstar | epsilon <
              ‖finMean (fun i ↦ g (xstar i)) -
                finMean (fun i ↦ g (S.sampleVector n omega i))‖} =
            (bootstrapResample data).real {xstar | epsilon < ‖V xstar‖} := rfl
        _ ≤ (bootstrapResample data).real
            (⋃ j : Fin d, {xstar | eta <
              |finMean (fun i ↦ g (xstar i) j) -
                finMean (fun i ↦ g (data i) j)|}) :=
          measureReal_mono hset (measure_ne_top _ _)
        _ ≤ ∑ j : Fin d, (bootstrapResample data).real
            {xstar | eta <
              |finMean (fun i ↦ g (xstar i) j) -
                finMean (fun i ↦ g (data i) j)|} :=
          measureReal_iUnion_fintype_le _
    · exact hsum

/-- For [an iid sample](hyp:S) and a [measurable integrable finite-dimensional
statistic](hyp:g,hg,hg_int), for almost every data sequence and every positive tolerance, [the
conditional bootstrap vector mean converges to the population vector mean](goal). -/
theorem bootstrapMeanVec_sub_populationMean_tendsto_zero_ae
    {d : ℕ} (S : IIDSample Omega X mu P)
    (g : X → EuclideanSpace ℝ (Fin d))
    (hg : Measurable g) (hg_int : Integrable g P) :
    ∀ᵐ omega ∂mu, ∀ epsilon : ℝ, 0 < epsilon →
      Tendsto
        (fun n ↦ (bootstrapResample (S.sampleVector n omega)).real
          {xstar | epsilon <
            ‖finMean (fun i ↦ g (xstar i)) - ∫ x, g x ∂P‖})
        atTop (𝓝 0) := by
  have hcoord : ∀ᵐ omega ∂mu, ∀ j : Fin d, ∀ epsilon : ℝ, 0 < epsilon →
      Tendsto
        (fun n ↦ (bootstrapResample (S.sampleVector n omega)).real
          {xstar | epsilon <
            |finMean (fun i ↦ g (xstar i) j) - ∫ x, g x j ∂P|})
        atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro j
    exact bootstrapMean_sub_populationMean_tendsto_zero_ae S
      (fun x ↦ g x j) (by fun_prop) (hg_int.eval_piLp j)
  filter_upwards [hcoord] with omega homega
  intro epsilon hepsilon
  by_cases hd : d = 0
  · subst d
    have hvzero : ∀ n (xstar : Fin n → X),
        finMean (fun i ↦ g (xstar i)) - ∫ x, g x ∂P = 0 :=
      fun n xstar ↦ Subsingleton.elim _ _
    simp_rw [hvzero, norm_zero, not_lt_of_ge hepsilon.le]
    simp
  · let eta : ℝ := epsilon / d
    have heta : 0 < eta := by
      dsimp [eta]
      positivity
    have hsum : Tendsto
        (fun n ↦ ∑ j : Fin d,
          (bootstrapResample (S.sampleVector n omega)).real
            {xstar | eta <
              |finMean (fun i ↦ g (xstar i) j) - ∫ x, g x j ∂P|})
        atTop (𝓝 0) := by
      simpa using tendsto_finset_sum Finset.univ
        (fun j hj ↦ homega j eta heta)
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ measureReal_nonneg
    · filter_upwards [eventually_ne_atTop 0] with n hn
      let data : Fin n → X := S.sampleVector n omega
      let V : (Fin n → X) → EuclideanSpace ℝ (Fin d) := fun xstar ↦
        finMean (fun i ↦ g (xstar i)) - ∫ x, g x ∂P
      have hint : ∀ j : Fin d,
          (∫ x, g x ∂P) j = ∫ x, g x j ∂P :=
        eval_integral_piLp (fun j ↦ hg_int.eval_piLp j)
      have hset :
          {xstar | epsilon < ‖V xstar‖} ⊆
            ⋃ j : Fin d, {xstar | eta <
              |finMean (fun i ↦ g (xstar i) j) - ∫ x, g x j ∂P|} := by
        have hs := euclidean_norm_event_subset hd V epsilon
        simpa only [V, eta, finMean_apply, PiLp.sub_apply, hint] using hs
      let _ : IsProbabilityMeasure (bootstrapResample data) :=
        bootstrapResample_isProbabilityMeasure data hn
      calc
        (bootstrapResample (S.sampleVector n omega)).real
            {xstar | epsilon <
              ‖finMean (fun i ↦ g (xstar i)) - ∫ x, g x ∂P‖} =
            (bootstrapResample data).real {xstar | epsilon < ‖V xstar‖} := rfl
        _ ≤ (bootstrapResample data).real
            (⋃ j : Fin d, {xstar | eta <
              |finMean (fun i ↦ g (xstar i) j) - ∫ x, g x j ∂P|}) :=
          measureReal_mono hset (measure_ne_top _ _)
        _ ≤ ∑ j : Fin d, (bootstrapResample data).real
            {xstar | eta <
              |finMean (fun i ↦ g (xstar i) j) - ∫ x, g x j ∂P|} :=
          measureReal_iUnion_fintype_le _
    · exact hsum

end

end Causalean.Stat
