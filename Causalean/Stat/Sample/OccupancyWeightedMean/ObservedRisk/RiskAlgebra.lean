module
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.Basic

/-!
# Real-mark collision-risk algebra

The identities and elementary bounds here separate outcome noise from the
matched-cell design center. They use only an observed law and include the
zero-usable fallback and population-null cells.
-/

public section

namespace Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

open MeasureTheory Causalean.Stat
open scoped BigOperators

variable {Ω κ : Type} [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

omit [DecidableEq κ] in
/-- The observed arm-center envelope itself forces the real scale to be
nonnegative under a probability law, since some measurable cell is inhabited. -/
theorem center_envelope_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (epsilon M rho : ℝ)
    (h : ObservedAssumptions μ X A Y center epsilon M rho) : 0 ≤ M := by
  -- A probability law makes Ω, hence κ via X, nonempty. Then use
  -- 0 ≤ |center a k| ≤ M.
  obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure μ
  exact le_trans (abs_nonneg _) (h.center_envelope true (X ω))

omit [DecidableEq κ] in
/-- The observed population contrast has magnitude at most twice the arm-center
envelope under a probability law. -/
theorem populationContrast_abs_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (epsilon M rho : ℝ)
    (h : ObservedAssumptions μ X A Y center epsilon M rho) :
    |populationContrast μ X center| ≤ 2 * M := by
  -- Sum the cell masses to one; each contrast has absolute value at most 2M.
  classical
  have hmass : (∑ k : κ, cellMass μ X k) = 1 := by
    have hsum := sum_measureReal_preimage_singleton
      (μ := μ) (s := (Finset.univ : Finset κ)) (f := X)
      (hf := by intro k hk; exact h.X_measurable (measurableSet_singleton k))
      (h := by
        intro k hk
        exact ne_of_lt <| lt_of_le_of_lt (measure_mono (Set.subset_univ _))
          (by simp [IsProbabilityMeasure.measure_univ]))
    simpa [cellMass, groupEvent, Measure.real, Set.preimage] using hsum
  have hM : 0 ≤ M := center_envelope_nonneg μ X A Y center epsilon M rho h
  have hbound (k : κ) :
      |cellMass μ X k * (center true k - center false k)| ≤ cellMass μ X k * (2 * M) := by
    have hcell : 0 ≤ cellMass μ X k := ENNReal.toReal_nonneg
    have htrue := h.center_envelope true k
    have hfalse := h.center_envelope false k
    rw [abs_mul, abs_of_nonneg hcell]
    apply mul_le_mul_of_nonneg_left _ hcell
    rw [abs_le]
    constructor <;> rcases abs_le.mp htrue with ⟨htl, htu⟩
      <;> rcases abs_le.mp hfalse with ⟨hfl, hfu⟩ <;> linarith
  calc
    |populationContrast μ X center| = |∑ k : κ, cellMass μ X k *
        (center true k - center false k)| := rfl
    _ ≤ ∑ k : κ, |cellMass μ X k * (center true k - center false k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : κ, cellMass μ X k * (2 * M) := Finset.sum_le_sum (by
      intro k hk; exact hbound k)
    _ = 2 * M := by rw [← Finset.sum_mul, hmass, one_mul]

/-- Almost every iid sample places observations only in cells of positive
observed population mass; hence every empirically matched cell is supported.
The finite-cell hypothesis is essential: an atomless cell law gives zero mass
to every realized singleton. Prove the claim by taking the finite union of
null cell events, then the finite union over sample coordinates. -/
theorem usable_supported_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (hX : Measurable X) (hA : Measurable A)
    (n : ℕ) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ),
      ∀ k, matchedCell X A z k → 0 < cellMass μ X k := by
  classical
  have hcell (k : κ) (hk : cellMass μ X k = 0) :
      ∀ᵐ ω ∂μ, X ω ≠ k := by
    have hfinite : μ (groupEvent X k) ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _))
        (by simp [IsProbabilityMeasure.measure_univ]))
    have hnull : μ (groupEvent X k) = 0 :=
      (measureReal_eq_zero_iff (s := groupEvent X k)).mp (by
        simpa [cellMass, Measure.real] using hk)
    exact ae_iff.mpr (by simpa [groupEvent] using hnull)
  have hall : ∀ᵐ ω ∂μ, ∀ k : κ, X ω = k → 0 < cellMass μ X k := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : cellMass μ X k = 0
    · exact (hcell k hk).mono (by intro ω hω heq; exact False.elim (hω heq))
    · filter_upwards [] with ω
      intro _
      exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hk)
  have hcoords : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i : Fin n, ∀ k : κ, X (z i) = k → 0 < cellMass μ X k :=
    (Filter.eventually_all.2 fun i =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => μ) (i := i)).eventually hall)
  filter_upwards [hcoords] with z hz k hk
  obtain ⟨i, hi⟩ : ∃ i : Fin n, X (z i) = k := by
    have hcount : 0 < groupArmCount X A z false k := hk.1
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hcount
    exact ⟨i, (Finset.mem_filter.mp hi).2.1⟩
  exact hz i k hi

/-- The collision estimator minus its design center is exactly the
occupancy-weighted difference of guarded arm-cell residual means, even when
the usable total is zero. -/
theorem collision_sub_designCenter_eq_residual {n : ℕ}
    (μ : Measure Ω) (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (z : Fin n → Ω) :
    collisionEstimator X A Y z - designCenter X A center z =
      occupancyWeightedResidual μ X A Y center z := by
  classical
  have hsum (a : Bool) (k : κ) :
      armSum X A Y z a k = armResidualSum X A Y center z a k +
        (groupArmCount X A z a k : ℝ) * center a k := by
    simp only [armSum, armResidualSum, supportedArmGroupResidual,
      groupArmCount]
    rw [Finset.card_eq_sum_ones]
    push_cast
    rw [Finset.sum_mul]
    simp_rw [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : X (z i) = k ∧ A (z i) = a <;>
      simp [armGroupEvent, armGroupResidual, h]
  have hmean (a : Bool) (k : κ)
      (hc : 0 < groupArmCount X A z a k) :
      armMean X A Y z a k =
        armResidualMean X A Y center z a k + center a k := by
    have hne : (groupArmCount X A z a k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hc)
    unfold armMean armResidualMean
    rw [if_pos hc, if_pos hc]
    change (groupArmCount X A z a k : ℝ)⁻¹ * armSum X A Y z a k =
      (groupArmCount X A z a k : ℝ)⁻¹ *
        armResidualSum X A Y center z a k + center a k
    rw [hsum]
    field_simp
  by_cases ht : 0 < usableTotal X A z
  · unfold collisionEstimator designCenter occupancyWeightedResidual
    simp only [ht, ↓reduceIte, div_eq_inv_mul]
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hu : matchedCell X A z k
    · simp only [hu, ↓reduceIte]
      rw [hmean true k hu.2, hmean false k hu.1]
      ring
    · simp [hu]
  · unfold collisionEstimator designCenter occupancyWeightedResidual
    simp [ht]

/-- Approximate homogeneity bounds squared design bias on supported samples;
if no cell is usable, the zero fallback incurs at most four envelope squares. -/
theorem designCenter_bias_sq_le {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (epsilon M rho : ℝ)
    (h : ObservedAssumptions μ X A Y center epsilon M rho)
    (z : Fin n → Ω)
    (hsupport : ∀ k, matchedCell X A z k → 0 < cellMass μ X k) :
    (designCenter X A center z - populationContrast μ X center) ^ 2 ≤
      M ^ 2 * (rho ^ 2 + if usableTotal X A z = 0 then 4 else 0) := by
  -- Positive total: use a nonnegative weighted average of deviations.
  -- Zero total: designCenter=0 and populationContrast_abs_le gives 4M².
  classical
  let p := populationContrast μ X center
  let B := M * rho
  let w : κ → ℝ := fun k =>
    if matchedCell X A z k then (groupCount X A z k : ℝ) else 0
  let d : κ → ℝ := fun k => center true k - center false k - p
  have htotal : (∑ k : κ, w k) = (usableTotal X A z : ℝ) := by
    dsimp [w]
    exact_mod_cast (show (∑ k : κ, if matchedCell X A z k then
      groupCount X A z k else 0) = usableTotal X A z from rfl)
  by_cases ht : 0 < usableTotal X A z
  · have htR : (0 : ℝ) < (usableTotal X A z : ℝ) := by exact_mod_cast ht
    have hnum : (∑ k : κ, w k * d k) =
        (∑ k : κ, if matchedCell X A z k then
          (groupCount X A z k : ℝ) * (center true k - center false k) else 0) -
          (usableTotal X A z : ℝ) * p := by
      rw [← htotal, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hu : matchedCell X A z k <;> simp [w, d, hu]; ring
    have hcenter : designCenter X A center z - p =
        (∑ k : κ, w k * d k) / (usableTotal X A z : ℝ) := by
      rw [hnum]
      unfold designCenter
      simp only [ht, ↓reduceIte]
      field_simp
    have hterm (k : κ) : |w k * d k| ≤ w k * B := by
      by_cases hu : matchedCell X A z k
      · have hc := h.homogeneity k (hsupport k hu)
        dsimp [w, d, B]
        simp only [hu, ↓reduceIte, abs_mul]
        rw [abs_of_nonneg (show 0 ≤ (groupCount X A z k : ℝ) by positivity)]
        simpa [p] using mul_le_mul_of_nonneg_left hc
          (show 0 ≤ (groupCount X A z k : ℝ) by positivity)
      · simp [w, hu]
    have hbound : |∑ k : κ, w k * d k| ≤ (usableTotal X A z : ℝ) * B := by
      calc
        |∑ k : κ, w k * d k| ≤ ∑ k : κ, |w k * d k| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : κ, w k * B := Finset.sum_le_sum (by
          intro k hk; exact hterm k)
        _ = (usableTotal X A z : ℝ) * B := by rw [← Finset.sum_mul, htotal]
    have habs : |designCenter X A center z - p| ≤ B := by
      rw [hcenter, abs_div, abs_of_pos htR]
      exact (div_le_iff₀ htR).2 (by simpa [mul_comm] using hbound)
    have hB : 0 ≤ B := le_trans (abs_nonneg _) habs
    have hsq := (sq_le_sq₀ (abs_nonneg _) hB).2 habs
    rw [sq_abs] at hsq
    simpa [p, B, (Nat.ne_of_gt ht), mul_pow] using hsq
  · have ht0 : usableTotal X A z = 0 := by omega
    have hp := populationContrast_abs_le μ X A Y center epsilon M rho h
    have hM : 0 ≤ M := center_envelope_nonneg μ X A Y center epsilon M rho h
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * M)).2 hp
    rw [sq_abs] at hsq
    have hdesign : designCenter X A center z = 0 := by simp [designCenter, ht0]
    rw [hdesign, ht0]
    simp only [ite_true, zero_sub, neg_sq]
    nlinarith [mul_nonneg (sq_nonneg M) (sq_nonneg rho)]

/-- Measurable cell, arm, and outcome maps make the guarded collision estimator
measurable on every finite iid sample space. -/
@[fun_prop] theorem measurable_collisionEstimator {n : ℕ}
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y) :
    Measurable (collisionEstimator (n := n) X A Y) := by
  classical
  have heq : collisionEstimator (n := n) X A Y =
      occupancyWeightedResidual (n := n) (0 : Measure Ω) X A Y (fun _ _ => 0) := by
    funext z
    unfold collisionEstimator occupancyWeightedResidual
    split_ifs <;> simp only [armMean, div_eq_inv_mul]
  rw [heq]
  exact measurable_occupancyWeightedResidual (0 : Measure Ω) X A Y
    (fun _ _ => 0) hX hA hY

/-- The centered design statistic has a finite second moment under bounded
arm-cell centers and an observed probability law. -/
theorem designCenter_sub_target_memLp {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (epsilon M rho : ℝ)
    (h : ObservedAssumptions μ X A Y center epsilon M rho) :
    MemLp (fun z : Fin n → Ω =>
      designCenter X A center z - populationContrast μ X center)
      2 (Measure.pi (fun _ : Fin n => μ)) := by
  -- The design center is a convex average of contrasts bounded by 2M,
  -- or zero. Combine with populationContrast_abs_le and MemLp.of_bound.
  classical
  have hM : 0 ≤ M := center_envelope_nonneg μ X A Y center epsilon M rho h
  have hmeas : Measurable (designCenter (n := n) X A center) := by
    unfold designCenter
    have ht := measurable_usableGroupTotal (n := n) X A h.X_measurable h.A_measurable
    apply Measurable.ite (measurableSet_lt measurable_const ht)
    · apply Measurable.div
      · apply Finset.measurable_sum
        intro k hk
        apply Measurable.ite
          (measurableSet_usableGroup X A h.X_measurable h.A_measurable k)
        · exact ((Measurable.of_discrete : Measurable fun m : ℕ => (m : ℝ)).comp
            (measurable_groupCount X A h.X_measurable h.A_measurable k)).mul measurable_const
        · exact measurable_const
      · exact (Measurable.of_discrete : Measurable fun m : ℕ => (m : ℝ)).comp ht
    · exact measurable_const
  have hbound (z : Fin n → Ω) : |designCenter X A center z| ≤ 2 * M := by
    by_cases ht : 0 < usableTotal X A z
    · have htR : (0 : ℝ) < usableTotal X A z := by exact_mod_cast ht
      have hterm (k : κ) :
          |(if matchedCell X A z k then
              (groupCount X A z k : ℝ) * (center true k - center false k) else 0)| ≤
            (if matchedCell X A z k then (groupCount X A z k : ℝ) else 0) * (2 * M) := by
        by_cases hk : matchedCell X A z k
        · simp only [hk, ↓reduceIte, abs_mul]
          rw [abs_of_nonneg (by positivity : 0 ≤ (groupCount X A z k : ℝ))]
          have hc : |center true k - center false k| ≤ 2 * M := by
            rw [abs_le]
            constructor <;> rcases abs_le.mp (h.center_envelope true k) with ⟨htl, htu⟩
              <;> rcases abs_le.mp (h.center_envelope false k) with ⟨hfl, hfu⟩
              <;> linarith
          exact mul_le_mul_of_nonneg_left hc (by positivity)
        · simp [hk]
      have hsum :
          |∑ k : κ, if matchedCell X A z k then
            (groupCount X A z k : ℝ) * (center true k - center false k) else 0| ≤
          (usableTotal X A z : ℝ) * (2 * M) := by
        calc
          _ ≤ ∑ k : κ, |if matchedCell X A z k then
              (groupCount X A z k : ℝ) * (center true k - center false k) else 0| :=
                Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k : κ, (if matchedCell X A z k then
              (groupCount X A z k : ℝ) else 0) * (2 * M) :=
                Finset.sum_le_sum (by intro k hk; exact hterm k)
          _ = (usableTotal X A z : ℝ) * (2 * M) := by
            rw [← Finset.sum_mul]
            congr 1
            exact_mod_cast (show (∑ k : κ, if matchedCell X A z k then
              groupCount X A z k else 0) = usableTotal X A z from rfl)
      unfold designCenter
      simp only [ht, ↓reduceIte, abs_div, abs_of_pos htR]
      exact (div_le_iff₀ htR).2 (by simpa [mul_comm] using hsum)
    · have ht0 : usableTotal X A z = 0 := by omega
      simp [designCenter, ht0, hM]
  have hp := populationContrast_abs_le μ X A Y center epsilon M rho h
  apply MemLp.of_bound (hmeas.sub measurable_const).aestronglyMeasurable (4 * M)
  filter_upwards [] with z
  rw [Real.norm_eq_abs]
  exact (abs_sub _ _).trans (by linarith [hbound z])

/-- Given [a sample size, observed probability law, finite cell setting,
observed maps, centers, and envelope parameters](hyp:n,μ,X,A,Y,center,epsilon,M,rho)
and [the observed-law assumptions](hyp:h), [the collision error has a finite
second moment](goal). -/
theorem collision_sub_target_memLp {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (epsilon M rho : ℝ)
    (h : ObservedAssumptions μ X A Y center epsilon M rho) :
    MemLp (fun z : Fin n → Ω =>
      collisionEstimator X A Y z - populationContrast μ X center)
      2 (Measure.pi (fun _ : Fin n => μ)) := by
  -- Rewrite estimator - designCenter with the preceding identity; use
  -- Causalean.Stat.occupancyWeightedResidual_memLp_two and add design L2.
  have hres := occupancyWeightedResidual_memLp_two (n := n) μ X A Y center
    h.X_measurable h.A_measurable h.Y_measurable h.residual_L2
  have hdesign := designCenter_sub_target_memLp (n := n) μ X A Y center epsilon M rho h
  convert hres.add hdesign using 1
  funext z
  change collisionEstimator X A Y z - populationContrast μ X center =
    occupancyWeightedResidual μ X A Y center z +
      (designCenter X A center z - populationContrast μ X center)
  rw [← collision_sub_designCenter_eq_residual μ X A Y center z]
  ring

end Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk
