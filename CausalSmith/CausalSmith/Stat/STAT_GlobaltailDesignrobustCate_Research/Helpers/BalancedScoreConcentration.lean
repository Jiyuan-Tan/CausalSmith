module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedBias
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedConcentration

/-! # Concentration of the actual balanced residual score

Roadmap (11)--(13): disjoint norming subcells and bounded tensor monomials
control the squared coordinate weights of the balanced score. The bounded
independent-residual inequality then controls this score and its inverse-Gram
prediction uniformly over the normalized cube, on a fixed design fiber.
The identification of the observational conditional law is a separate step.
-/
@[expose] public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix NNReal

/-- Per-observation scalar weight in a coordinate of the balanced score. -/
-- @node: balancedCoordinateWeight
noncomputable def balancedCoordinateWeight {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (a : MultiIndex d m) (i : Fin n) : ℝ := by
  classical
  exact ∑ ℓ : MultiIndex d m,
    if (sample i).2.1 = arm ∧ (sample i).1 ∈ scaledSubcell d j m ε Q ℓ then
      (Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
        (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹ *
        monomial d m (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j) a
    else 0

/-- The empirical score is a weighted sum over observations, with weights
fixed when covariates and arm indicators are fixed. -/
-- @node: balancedScore_eq_weightedSum
lemma balancedScore_eq_weightedSum {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (r : Fin n → ℝ) (a : MultiIndex d m) :
    balancedScore sample arm j m ε Q r a =
      ∑ i, balancedCoordinateWeight sample arm j m ε Q a i * r i := by
  classical
  simp only [balancedScore, balancedCoordinateWeight, Finset.mul_sum,
    Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

/-- Bounded monomials and disjoint subcells give the score-coordinate
variance proxy `1 / (R N_Q)` in equation (11), for either arm. -/
-- @node: balancedCoordinateWeight_sq_sum_le
lemma balancedCoordinateWeight_sq_sum_le {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j : ℕ) (β : ℝ) (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q) (a : MultiIndex d (polynomialOrder β)) :
    (∑ i, balancedCoordinateWeight sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q a i ^ 2) ≤
      1 / ((Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
        (minimumCellCount sample arm j (polynomialOrder β)
          (normingSubcells d β).radius Q : ℝ)) := by
  classical
  unfold balancedCoordinateWeight
  have hsq (i : Fin n) := sum_sq_of_unique_selection
    (fun ℓ => (sample i).2.1 = arm ∧ (sample i).1 ∈ scaledSubcell d j (polynomialOrder β)
      (normingSubcells d β).radius Q ℓ)
    (fun ℓ => (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ)⁻¹ *
      (subcellCount sample arm j (polynomialOrder β)
        (normingSubcells d β).radius Q ℓ : ℝ)⁻¹ *
      monomial d (polynomialOrder β)
        (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j) a)
    (fun b c hb hc => scaledSubcell_unique j β Q (sample i).1 b c hb.2 hc.2)
  simp_rw [hsq]
  rw [Finset.sum_comm]
  apply le_trans _ (balancedWeights_sq_sum_le sample arm j (polynomialOrder β)
    (normingSubcells d β).radius Q hcount)
  apply Finset.sum_le_sum
  intro ℓ _
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · have hm := monomial_abs_le_one _
      (scaledSubcell_normalized_mem_cube j β Q ℓ _ hi.2) a
    have hm2 : (monomial d (polynomialOrder β)
        (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j) a) ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg (monomial d (polynomialOrder β)
        (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j) a),
        sq_abs (monomial d (polynomialOrder β)
        (fun k => ((sample i).1 k - cellOrigin d j Q k) / dyadicWidth j) a)]
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left hm2 (sq_nonneg _)).trans_eq (mul_one _)
  · exact le_rfl

/-- On a fixed design fiber the actual balanced score obeys the coordinate
union bound, with the squared weights derived from the estimator itself. -/
-- @node: balancedScore_coordinates_abs_tail
lemma balancedScore_coordinates_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    {d n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sample : Fin n → Obs d) (arm : Bool) (j : ℕ) (β : ℝ)
    (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q)
    (ξ : Fin n → Ω → ℝ) (b : ℝ≥0) (hindep : iIndepFun ξ μ)
    (hmeas : ∀ i, AEMeasurable (ξ i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b)
    (hcenter : ∀ i, ∫ ω, ξ i ω ∂μ = 0) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | ∃ a, t < |balancedScore sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q (fun i => ξ i ω) a|} ≤
      2 * Fintype.card (MultiIndex d (polynomialOrder β)) *
        Real.exp (-t ^ 2 / (2 * ((b : ℝ) ^ 2 /
          ((Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
            (minimumCellCount sample arm j (polynomialOrder β)
              (normingSubcells d β).radius Q : ℝ))))) := by
  let v : ℝ≥0 := ⟨(b : ℝ) ^ 2 /
    ((Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
      (minimumCellCount sample arm j (polynomialOrder β)
        (normingSubcells d β).radius Q : ℝ)), by positivity⟩
  simp_rw [balancedScore_eq_weightedSum]
  apply weightedResidualCoordinates_abs_tail μ ξ
    (balancedCoordinateWeight sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q) b v hindep hmeas hbound hcenter _ t ht
  intro a
  have h := mul_le_mul_of_nonneg_left
    (balancedCoordinateWeight_sq_sum_le sample arm j β Q hcount a) (sq_nonneg (b : ℝ))
  have hv : (v : ℝ) = (b : ℝ) ^ 2 /
      ((Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
        (minimumCellCount sample arm j (polynomialOrder β)
          (normingSubcells d β).radius Q : ℝ)) := rfl
  rw [hv]
  simpa only [mul_one_div] using h

/-- The inverse-Gram prediction is uniformly controlled by coordinate bounds
on the score; unlike a response bound, this applies directly to random noise. -/
-- @node: balancedScore_prediction_of_coordinate_bounds
lemma balancedScore_prediction_of_coordinate_bounds {d n : ℕ}
    (sample : Fin n → Obs d) (arm : Bool) (j : ℕ) (β : ℝ)
    (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q)
    (r : Fin n → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hscore : ∀ a, |balancedScore sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q r a| ≤ E)
    (u : Fin d → ℝ) (hu : u ∈ cube d) :
    let m := polynomialOrder β
    let ε := (normingSubcells d β).radius
    let G := balancedGram sample arm j m ε Q
    |∑ a, monomial d m u a *
      (G⁻¹ *ᵥ balancedScore sample arm j m ε Q r) a| ≤
        (Fintype.card (MultiIndex d m) : ℝ) * E /
          (referenceLowerEigenvalue d m / 2) := by
  dsimp only
  apply coercive_prediction_abs_le
  · exact half_pos (referenceLowerEigenvalue_pos d (polynomialOrder β))
  · exact hE
  · exact armBalanced_gram sample arm j β Q hcount _
  · exact armBalancedGram_normalEquation sample arm j β Q hcount _
  · exact hscore
  · exact monomial_abs_le_one u hu

/-- Equation (13) on a fixed design fiber: the inverse balanced Gram fit has
a uniform prediction tail. No independence between score coordinates is needed. -/
-- @node: balancedScore_prediction_abs_tail
lemma balancedScore_prediction_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    {d n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sample : Fin n → Obs d) (arm : Bool) (j : ℕ) (β : ℝ)
    (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q)
    (ξ : Fin n → Ω → ℝ) (b : ℝ≥0) (hindep : iIndepFun ξ μ)
    (hmeas : ∀ i, AEMeasurable (ξ i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b)
    (hcenter : ∀ i, ∫ ω, ξ i ω ∂μ = 0) (t : ℝ) (ht : 0 ≤ t) :
    let m := polynomialOrder β
    let ε := (normingSubcells d β).radius
    let G := balancedGram sample arm j m ε Q
    let R : ℝ := Fintype.card (MultiIndex d m)
    let c := referenceLowerEigenvalue d m / 2
    μ.real {ω | ∃ u ∈ cube d,
      t < |∑ a, monomial d m u a *
        (G⁻¹ *ᵥ balancedScore sample arm j m ε Q (fun i => ξ i ω)) a|} ≤
      2 * R * Real.exp (-(c * t / R) ^ 2 /
        (2 * ((b : ℝ) ^ 2 / (R * (minimumCellCount sample arm j m ε Q : ℝ))))) := by
  classical
  dsimp only
  let R : ℝ := Fintype.card (MultiIndex d (polynomialOrder β))
  let c := referenceLowerEigenvalue d (polynomialOrder β) / 2
  have hR : 0 < R := by dsimp [R]; exact_mod_cast Fintype.card_pos
  have hc : 0 < c := half_pos (referenceLowerEigenvalue_pos d (polynomialOrder β))
  let E := c * t / R
  have hE : 0 ≤ E := div_nonneg (mul_nonneg hc.le ht) hR.le
  have hcancel : R * E / c = t := by dsimp [E]; field_simp
  apply le_trans (measureReal_mono (h₂ := measure_ne_top μ _) ?_)
    (balancedScore_coordinates_abs_tail μ sample arm j β Q hcount ξ b
      hindep hmeas hbound hcenter E hE)
  intro ω hω
  obtain ⟨u, hu, hlarge⟩ := hω
  change ∃ a, E < |balancedScore sample arm j (polynomialOrder β)
    (normingSubcells d β).radius Q (fun i => ξ i ω) a|
  by_contra hsmall
  have hscore : ∀ a, |balancedScore sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q (fun i => ξ i ω) a| ≤ E := by
    intro a
    exact le_of_not_gt (fun ha => hsmall ⟨a, ha⟩)
  have hpred := balancedScore_prediction_of_coordinate_bounds sample arm j β Q
    hcount (fun i => ξ i ω) E hE hscore u hu
  change |∑ a, monomial d (polynomialOrder β) u a *
    ((balancedGram sample arm j (polynomialOrder β) (normingSubcells d β).radius Q)⁻¹ *ᵥ
      balancedScore sample arm j (polynomialOrder β) (normingSubcells d β).radius Q
        (fun i => ξ i ω)) a| ≤ R * E / c at hpred
  rw [hcancel] at hpred
  exact (not_lt_of_ge hpred) hlarge

/-- With bounded residuals `2M`, the fixed-fiber prediction bound has exactly
the minimum-count Gaussian form of (13); its constants depend only on geometry. -/
-- @node: balancedScore_prediction_gaussian_tail
lemma balancedScore_prediction_gaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    {d n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sample : Fin n → Obs d) (arm : Bool) (j : ℕ) (β M : ℝ) (hM : 0 < M)
    (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q)
    (ξ : Fin n → Ω → ℝ) (hindep : iIndepFun ξ μ)
    (hmeas : ∀ i, AEMeasurable (ξ i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ 2 * M)
    (hcenter : ∀ i, ∫ ω, ξ i ω ∂μ = 0) (t : ℝ) (ht : 0 ≤ t) :
    let m := polynomialOrder β
    let ε := (normingSubcells d β).radius
    let G := balancedGram sample arm j m ε Q
    let R : ℝ := Fintype.card (MultiIndex d m)
    μ.real {ω | ∃ u ∈ cube d,
      t < |∑ a, monomial d m u a *
        (G⁻¹ *ᵥ balancedScore sample arm j m ε Q (fun i => ξ i ω)) a|} ≤
      (2 * R) * Real.exp (-(referenceLowerEigenvalue d m ^ 2 / (32 * R)) *
        (minimumCellCount sample arm j m ε Q : ℝ) * t ^ 2 / M ^ 2) := by
  dsimp only
  let b : ℝ≥0 := ⟨2 * M, by positivity⟩
  have hb : (b : ℝ) = 2 * M := rfl
  have htail := balancedScore_prediction_abs_tail μ sample arm j β Q hcount
    ξ b hindep hmeas (by simpa only [hb] using hbound) hcenter t ht
  dsimp only at htail
  rw [hb] at htail
  have hR : (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) ≠ 0 :=
    by exact_mod_cast Fintype.card_ne_zero
  have hN : (minimumCellCount sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hcount).ne'
  convert htail using 1 <;> congr 2 <;> field_simp <;> ring

end CausalSmith.Stat.GlobalTailDesignRobustCate
