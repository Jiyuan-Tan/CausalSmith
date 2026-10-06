module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedCellTail

/-! # Control estimator bias and conditional cell tail

Roadmap (C11)--(C14): the control Taylor approximation, arm-independent
normal equations, and bounded residual score concentration bound the clipped
control fit on each fixed design fiber, including empty subcells.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

/-- One positive constant controls the occupied-cell deterministic control
bias uniformly over laws, samples, bandwidths, and cells. -/
-- @node: control_balancedScore_bias
lemma control_balancedScore_bias (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B : ℝ, 0 < B ∧ ∀ P : Law d, CATEClass d β γ C L M κ P →
      ∀ (n j : ℕ) (sample : Fin n → Obs d) (Q : Fin d → Fin (2 ^ j)),
        0 < minimumCellCount sample false j (polynomialOrder β) (normingSubcells d β).radius Q →
        ∀ x ∈ cube d, x ∈ dyadicCell d j Q →
          let m := polynomialOrder β
          let ε := (normingSubcells d β).radius
          let G := balancedGram sample false j m ε Q
          |(∑ a, monomial d m (fun k => (x k - cellOrigin d j Q k) / dyadicWidth j) a *
            (G⁻¹ *ᵥ balancedScore sample false j m ε Q (fun i => P.mu0 (sample i).1)) a) -
              P.mu0 x| ≤ B * L * (dyadicWidth j) ^ β := by
  obtain ⟨BT, hBT, hTaylor⟩ := control_dyadic_tensor_approx d β L hparam.2.1 hparam.2.2.2.2.1
  let A : ℝ := 1 + (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) /
    (referenceLowerEigenvalue d (polynomialOrder β) / 2)
  have hA : 0 < A := by
    have hlam := referenceLowerEigenvalue_pos d (polynomialOrder β)
    dsimp [A]
    positivity
  refine ⟨A * BT, mul_pos hA hBT, ?_⟩
  intro P hP n j sample Q hcount x hx hQ
  obtain ⟨θ, hθ⟩ := hTaylor P hP.controlHolder j Q
  have hE : 0 ≤ BT * L * (dyadicWidth j) ^ β := by
    have hL := hparam.2.2.2.2.1
    have hh := (dyadicWidth_mem_Ioc j).1
    positivity
  have h := balancedScore_fit_bias_le sample false j β Q hcount P.mu0 θ
    (BT * L * (dyadicWidth j) ^ β) hE (by
      intro z hz hzQ
      simpa only [mul_comm] using hθ z hz hzQ) x hx hQ
  convert h using 1
  dsimp [A]
  ring

/-- The actual clipped control estimator has deterministic bias plus the
inverse-Gram residual prediction on every occupied cell (roadmap (C11)--(C14)).
Only the probability bound for the second term remains stochastic. -/
-- @node: control_balancedEstimator_bias_noise
lemma control_balancedEstimator_bias_noise (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B : ℝ, 0 < B ∧ ∀ P : Law d, CATEClass d β γ C L M κ P →
      ∀ (n j : ℕ) (sample : Fin n → Obs d) (x : Fin d → ℝ), x ∈ cube d →
        let m := polynomialOrder β
        let ε := (normingSubcells d β).radius
        let Q := cellIndex d j x
        let G := balancedGram sample false j m ε Q
        0 < minimumCellCount sample false j m ε Q →
        |controlBalancedEstimator sample j β M x - P.mu0 x| ≤
          B * L * (dyadicWidth j) ^ β +
            |∑ a, monomial d m (fun k => (x k - cellOrigin d j Q k) / dyadicWidth j) a *
              (G⁻¹ *ᵥ balancedScore sample false j m ε Q
                (fun i => (sample i).2.2 - P.mu0 (sample i).1)) a| := by
  classical
  obtain ⟨B, hB, hbias⟩ := control_balancedScore_bias d β γ C L M κ hparam
  refine ⟨B, hB, ?_⟩
  intro P hP n j sample x hx
  dsimp only
  intro hcount
  let m := polynomialOrder β
  let ε := (normingSubcells d β).radius
  let Q := cellIndex d j x
  let G := balancedGram sample false j m ε Q
  let v := monomial d m (fun k => (x k - cellOrigin d j Q k) / dyadicWidth j)
  let mean : MultiIndex d m → ℝ := G⁻¹ *ᵥ
    balancedScore sample false j m ε Q (fun i => P.mu0 (sample i).1)
  let fit : MultiIndex d m → ℝ := G⁻¹ *ᵥ balancedMoment sample false j m ε Q
  let noise : MultiIndex d m → ℝ := G⁻¹ *ᵥ
    balancedScore sample false j m ε Q (fun i => (sample i).2.2 - P.mu0 (sample i).1)
  have hcoef : noise = fit - mean := by
    dsimp [noise, fit, mean]
    rw [balancedScore_sub, Matrix.mulVec_sub, balancedMoment_eq_score]
  have hsplit : (∑ a, v a * fit a) - P.mu0 x =
      ((∑ a, v a * mean a) - P.mu0 x) + (∑ a, v a * noise a) := by
    rw [hcoef]
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hfit : |(∑ a, v a * fit a) - P.mu0 x| ≤
      B * L * (dyadicWidth j) ^ β + |∑ a, v a * noise a| := by
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add
      (hbias P hP n j sample Q hcount x hx rfl) (le_refl _))
  have hnonzero : minimumCellCount sample false j m ε Q ≠ 0 := Nat.ne_of_gt hcount
  change |controlBalancedEstimator sample j β M x - P.mu0 x| ≤ _
  unfold controlBalancedEstimator armBalancedEstimator
  dsimp only
  rw [if_neg hnonzero]
  exact (clipping_abs_sub_le M _ _ (hP.semantics.2.2.2.2.2 x hx)).trans hfit

/-- The actual clipped control estimator has a Gaussian cell tail on every
fixed design fiber, including its empty-subcell fallback. The hypotheses on
residuals are the probabilistic conclusions to be supplied by conditional-law
identification, rather than premises added to the paper theorem. -/
-- @node: control_balancedEstimator_fixedDesign_cell_tail
lemma control_balancedEstimator_fixedDesign_cell_tail (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B : ℝ, 0 < B ∧ ∀ P : Law d, CATEClass d β γ C L M κ P →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (n j : ℕ) (s : Fin n → Obs d) (S : Ω → Fin n → Obs d),
        (∀ ω i, (S ω i).1 = (s i).1) →
        (∀ ω i, (S ω i).2.1 = (s i).2.1) →
        let ξ := fun i ω =>
          if (s i).2.1 = false then (S ω i).2.2 - P.mu0 (s i).1 else 0
        iIndepFun ξ μ → (∀ i, AEMeasurable (ξ i) μ) →
        (∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ 2 * M) →
        (∀ i, ∫ ω, ξ i ω ∂μ = 0) →
        ∀ (Q : Fin d → Fin (2 ^ j)) (t : ℝ), 0 ≤ t →
        μ.real {ω | ∃ x ∈ cube d, cellIndex d j x = Q ∧
          B * L * (dyadicWidth j) ^ β + t <
            |controlBalancedEstimator (S ω) j β M x - P.mu0 x|} ≤
          (2 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ)) *
            Real.exp (-(referenceLowerEigenvalue d (polynomialOrder β) ^ 2 /
              (32 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ))) *
              (minimumCellCount s false j (polynomialOrder β)
                (normingSubcells d β).radius Q : ℝ) * t ^ 2 / M ^ 2) := by
  obtain ⟨B, hB, hbias⟩ := control_balancedEstimator_bias_noise d β γ C L M κ hparam
  refine ⟨B, hB, ?_⟩
  intro P hP Ω _ μ _ n j s S hX hA
  dsimp only
  intro hindep hmeas hbound hcenter Q t ht
  by_cases hcount : 0 < minimumCellCount s false j (polynomialOrder β)
      (normingSubcells d β).radius Q
  · have htail := balancedScore_prediction_gaussian_tail μ s false j β M
      hparam.2.2.2.2.2 Q hcount
      (fun i ω => if (s i).2.1 = false then (S ω i).2.2 - P.mu0 (s i).1 else 0)
      hindep hmeas hbound hcenter t ht
    dsimp only at htail
    apply le_trans (measureReal_mono (h₂ := measure_ne_top μ _) ?_) htail
    intro ω hω
    obtain ⟨x, hx, hQ, hlarge⟩ := hω
    have hN := minimumCellCount_congr_design s (S ω) (hX ω) (hA ω)
      false j (polynomialOrder β) (normingSubcells d β).radius Q
    have hoccupied : 0 < minimumCellCount (S ω) false j (polynomialOrder β)
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
  · have hzero : minimumCellCount s false j (polynomialOrder β)
        (normingSubcells d β).radius Q = 0 := by omega
    rw [hzero]
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Real.exp_zero, mul_one]
    have hprob : μ.real {ω | ∃ x ∈ cube d, cellIndex d j x = Q ∧
        B * L * (dyadicWidth j) ^ β + t <
          |controlBalancedEstimator (S ω) j β M x - P.mu0 x|} ≤ 1 :=
      measureReal_le_one
    have hR : (1 : ℝ) ≤ Fintype.card (MultiIndex d (polynomialOrder β)) := by
      exact_mod_cast Fintype.card_pos
    linarith

end CausalSmith.Stat.GlobalTailDesignRobustCate
