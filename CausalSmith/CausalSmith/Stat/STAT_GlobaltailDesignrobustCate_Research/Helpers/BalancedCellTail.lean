module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedScoreConcentration

/-! # Actual estimator tails on fixed design fibers

Roadmap (13)--(14): varying outcomes while holding covariates and treatment
indicators fixed preserves counts, Gram matrices, and residual-score weights.
Combining the Taylor bias with the score tail bounds the actual clipped cell
fit. Empty subcells obey the same exponential bound because its exponent is zero.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

/-- Subcell counts depend only on covariates and treatment indicators. -/
-- @node: subcellCount_congr_design
lemma subcellCount_congr_design {d n : ℕ} (s s' : Fin n → Obs d)
    (hX : ∀ i, (s' i).1 = (s i).1) (hA : ∀ i, (s' i).2.1 = (s i).2.1)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (ℓ : MultiIndex d m) :
    subcellCount s' arm j m ε Q ℓ = subcellCount s arm j m ε Q ℓ := by
  classical
  simp only [subcellCount, hX, hA]

/-- Minimum counts are constant on each complete-design fiber. -/
-- @node: minimumCellCount_congr_design
lemma minimumCellCount_congr_design {d n : ℕ} (s s' : Fin n → Obs d)
    (hX : ∀ i, (s' i).1 = (s i).1) (hA : ∀ i, (s' i).2.1 = (s i).2.1)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j)) :
    minimumCellCount s' arm j m ε Q = minimumCellCount s arm j m ε Q := by
  unfold minimumCellCount
  simp_rw [subcellCount_congr_design s s' hX hA]

/-- The balanced Gram matrix is constant on a complete-design fiber. -/
-- @node: balancedGram_congr_design
lemma balancedGram_congr_design {d n : ℕ} (s s' : Fin n → Obs d)
    (hX : ∀ i, (s' i).1 = (s i).1) (hA : ∀ i, (s' i).2.1 = (s i).2.1)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j)) :
    balancedGram s' arm j m ε Q = balancedGram s arm j m ε Q := by
  classical
  funext a b
  simp only [balancedGram, subcellCount_congr_design s s' hX hA, hX, hA]

/-- Arbitrary residual scores use the same weights on a complete-design fiber. -/
-- @node: balancedScore_congr_design
lemma balancedScore_congr_design {d n : ℕ} (s s' : Fin n → Obs d)
    (hX : ∀ i, (s' i).1 = (s i).1) (hA : ∀ i, (s' i).2.1 = (s i).2.1)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j)) (r : Fin n → ℝ) :
    balancedScore s' arm j m ε Q r = balancedScore s arm j m ε Q r := by
  classical
  funext a
  simp only [balancedScore, subcellCount_congr_design s s' hX hA, hX, hA]

/-- Residuals outside the fitted arm have zero score weight. Masking them
makes centering a condition only on the relevant arm of the design fiber. -/
-- @node: balancedScore_mask_arm
lemma balancedScore_mask_arm {d n : ℕ} (s : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j)) (r : Fin n → ℝ) :
    balancedScore s arm j m ε Q r =
      balancedScore s arm j m ε Q (fun i => if (s i).2.1 = arm then r i else 0) := by
  classical
  funext a
  unfold balancedScore
  congr 1
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (s i).2.1 = arm
  · simp only [if_pos hi]
  · simp only [hi, false_and, if_false]

/-- The actual clipped treated estimator has a Gaussian cell tail on every
fixed design fiber, including its empty-subcell fallback. The hypotheses on
residuals are the probabilistic conclusions to be supplied by conditional-law
identification, rather than premises added to the paper theorem. -/
-- @node: treated_balancedEstimator_fixedDesign_cell_tail
lemma treated_balancedEstimator_fixedDesign_cell_tail (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B : ℝ, 0 < B ∧ ∀ P : Law d, LawClass d β γ C L M P →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (n j : ℕ) (s : Fin n → Obs d) (S : Ω → Fin n → Obs d),
        (∀ ω i, (S ω i).1 = (s i).1) →
        (∀ ω i, (S ω i).2.1 = (s i).2.1) →
        let ξ := fun i ω =>
          if (s i).2.1 = true then (S ω i).2.2 - P.mu1 (s i).1 else 0
        iIndepFun ξ μ → (∀ i, AEMeasurable (ξ i) μ) →
        (∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ 2 * M) →
        (∀ i, ∫ ω, ξ i ω ∂μ = 0) →
        ∀ (Q : Fin d → Fin (2 ^ j)) (t : ℝ), 0 ≤ t →
        μ.real {ω | ∃ x ∈ cube d, cellIndex d j x = Q ∧
          B * L * (dyadicWidth j) ^ β + t <
            |balancedEstimator (S ω) j β M x - P.mu1 x|} ≤
          (2 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ)) *
            Real.exp (-(referenceLowerEigenvalue d (polynomialOrder β) ^ 2 /
              (32 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ))) *
              (minimumCellCount s true j (polynomialOrder β)
                (normingSubcells d β).radius Q : ℝ) * t ^ 2 / M ^ 2) := by
  obtain ⟨B, hB, hbias⟩ := treated_balancedEstimator_bias_noise d β γ C L M hparam
  refine ⟨B, hB, ?_⟩
  intro P hP Ω _ μ _ n j s S hX hA
  dsimp only
  intro hindep hmeas hbound hcenter Q t ht
  by_cases hcount : 0 < minimumCellCount s true j (polynomialOrder β)
      (normingSubcells d β).radius Q
  · have htail := balancedScore_prediction_gaussian_tail μ s true j β M
      hparam.2.2.2.2.2 Q hcount
      (fun i ω => if (s i).2.1 = true then (S ω i).2.2 - P.mu1 (s i).1 else 0)
      hindep hmeas hbound hcenter t ht
    dsimp only at htail
    apply le_trans (measureReal_mono (h₂ := measure_ne_top μ _) ?_) htail
    intro ω hω
    obtain ⟨x, hx, hQ, hlarge⟩ := hω
    have hN := minimumCellCount_congr_design s (S ω) (hX ω) (hA ω)
      true j (polynomialOrder β) (normingSubcells d β).radius Q
    have hoccupied : 0 < minimumCellCount (S ω) true j (polynomialOrder β)
        (normingSubcells d β).radius (cellIndex d j x) := by
      rw [hQ, hN]
      exact hcount
    have h := hbias P hP n j (S ω) x hx hoccupied
    rw [hQ, balancedGram_congr_design s (S ω) (hX ω) (hA ω)] at h
    simp_rw [hX ω] at h
    rw [balancedScore_congr_design s (S ω) (hX ω) (hA ω),
      balancedScore_mask_arm] at h
    refine ⟨(fun k => (x k - cellOrigin d j Q k) / dyadicWidth j),
      normalizedDyadicPoint_mem_cube d j Q x hx hQ, ?_⟩
    linarith
  · have hzero : minimumCellCount s true j (polynomialOrder β)
        (normingSubcells d β).radius Q = 0 := by omega
    rw [hzero]
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Real.exp_zero, mul_one]
    have hprob : μ.real {ω | ∃ x ∈ cube d, cellIndex d j x = Q ∧
        B * L * (dyadicWidth j) ^ β + t <
          |balancedEstimator (S ω) j β M x - P.mu1 x|} ≤ 1 :=
      measureReal_le_one
    have hR : (1 : ℝ) ≤ Fintype.card (MultiIndex d (polynomialOrder β)) := by
      exact_mod_cast Fintype.card_pos
    linarith

end CausalSmith.Stat.GlobalTailDesignRobustCate
