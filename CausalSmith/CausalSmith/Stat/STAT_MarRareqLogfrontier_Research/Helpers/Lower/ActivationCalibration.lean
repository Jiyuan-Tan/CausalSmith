module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.IntervalThresholds
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationCoverage
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.MomentPriors

/-! Ceiling-degree calibration of the actual activated cutoff. The rounding
allowance changes only the numerical effective-size threshold in (9). -/

public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:η,n,q,hη,hN,hell), [the stated mathematical conclusion holds](goal). -/
-- @node: activation_mean_le_factorial_order
lemma activation_mean_le_factorial_order (η : ℝ) (n : ℕ) (q : ℝ)
    (hη : 0 ≤ η) (hN : 0 < effectiveSize n q) (hell : 1 ≤ logScale n q) :
    (n : ℝ) * (rareMass η n q * (q * lowerEndpoint n q)) ≤
      (2 * η) * (lowerDegree n q + 1 : ℕ) := by
  have hn0 : 0 < (n : ℝ) := by
    have h : 0 < (n : ℝ) * q := hN
    exact (mul_pos_iff.mp h).elim (fun h => h.1)
      (fun h => False.elim (not_lt_of_ge (Nat.cast_nonneg n) h.1))
  have hq0 : 0 < q := (mul_pos_iff.mp hN).elim (fun h => h.2)
    (fun h => False.elim (not_lt_of_ge (Nat.cast_nonneg n) h.1))
  have hL : 0 < logScale n q := by linarith
  have hK : (lowerDegree n q : ℝ) ≤ 2 * logScale n q := by
    have h := Nat.ceil_lt_add_one hL.le
    simpa only [lowerDegree] using h.le.trans (by linarith)
  have hKr : 0 ≤ (lowerDegree n q : ℝ) := by positivity
  have hsq : (lowerDegree n q : ℝ) ^ 2 ≤
      2 * logScale n q * (lowerDegree n q + 1 : ℕ) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hK hKr]
  have heq : (n : ℝ) * (rareMass η n q * (q * lowerEndpoint n q)) =
      η * (lowerDegree n q : ℝ) ^ 2 / logScale n q := by
    unfold rareMass lowerEndpoint effectiveSize at *
    field_simp [ne_of_gt hn0, ne_of_gt hq0]
  rw [heq]
  apply (div_le_iff₀ hL).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsq hη]

/-- Given [the specified inputs and assumptions](hyp:n,q,hN,hell), [the stated mathematical conclusion holds](goal). -/
-- @node: activation_factorial_ratio_le_exp
lemma activation_factorial_ratio_le_exp (n : ℕ) (q : ℝ)
    (hN : 0 < effectiveSize n q) (hell : 1 ≤ logScale n q) :
    ((n : ℝ) * (rareMass (Real.exp (-32)) n q * (q * lowerEndpoint n q))) ^
        (lowerDegree n q + 1) / ((lowerDegree n q + 1).factorial : ℝ) ≤
      Real.exp (-30 * logScale n q) := by
  let r := lowerDegree n q + 1
  have hmean := activation_mean_le_factorial_order (Real.exp (-32)) n q
    (Real.exp_nonneg _) hN hell
  have hdegree : logScale n q ≤ (r : ℝ) := by
    have h := Nat.le_ceil (logScale n q)
    dsimp [r, lowerDegree]
    push_cast
    linarith
  have hcoef : 2 * Real.exp (-32) ≤ Real.exp (-31) := by
    rw [show (-31 : ℝ) = 1 + -32 by norm_num, Real.exp_add]
    have h := Real.add_one_le_exp (1 : ℝ)
    nlinarith [Real.exp_pos (-32)]
  have hnonneg : 0 ≤ (n : ℝ) *
      (rareMass (Real.exp (-32)) n q * (q * lowerEndpoint n q)) := by
    unfold rareMass lowerEndpoint effectiveSize at *
    have : 0 < (n : ℝ) * q := hN
    have hn : 0 < (n : ℝ) := by
      by_contra h
      have : n = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n))
      simp [this] at hN
    have hq : 0 < q := ((mul_pos_iff.mp hN).resolve_right (by rintro ⟨h, _⟩; linarith)).2
    positivity
  calc
    _ ≤ ((Real.exp (-31)) * (r : ℝ)) ^ r / (r.factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ hnonneg
        (hmean.trans (mul_le_mul_of_nonneg_right hcoef (by positivity))) r
    _ = Real.exp (-31) ^ r * ((r : ℝ) ^ r / (r.factorial : ℝ)) := by ring
    _ ≤ Real.exp (-31) ^ r * Real.exp (r : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp r (by positivity) r)
        (by positivity)
    _ = Real.exp (-30 * (r : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-30 * logScale n q) := Real.exp_le_exp.mpr (by linarith)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hd,hq,hslice,π,hπ), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_cutoff_le_exp
lemma activatedAugmentedMixture_cutoff_le_exp (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : 0 < q) (hslice : RareArrivalSlice n q)
    {π : Measure ℝ} (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π) :
    (activatedAugmentedMixture (Real.exp (-32)) n d q π).real
      {s | ¬ ∀ x : Fin d, x.val < rareCount (Real.exp (-32)) n d q →
        (∑ i ∈ Finset.univ.filter (fun i => (s i).2.X = x),
          if (s i).1 then 1 else 0) ≤ lowerDegree n q} ≤
      Real.exp (32 - 28 * logScale n q) := by
  have hN : 0 < effectiveSize n q := by unfold effectiveSize; positivity
  have hell : 1 ≤ logScale n q := by
    unfold logScale
    have h := Real.log_le_log (Real.exp_pos (1 : ℝ))
      (show Real.exp 1 ≤ Real.exp 1 + effectiveSize n q by linarith)
    simpa using h
  have hb : 0 < rareMass (Real.exp (-32)) n q := by unfold rareMass; positivity
  have hcap : (rareCount (Real.exp (-32)) n d q : ℝ) ≤
      effectiveSize n q * logScale n q / (2 * Real.exp (-32)) := by
    have h := rareCount_mass_le_half (Real.exp (-32)) n d q hb
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.exp (-32))).mpr
    dsimp [rareMass] at h
    have h' := (div_le_iff₀ (by positivity :
      0 < effectiveSize n q * logScale n q)).mp (show
        (rareCount (Real.exp (-32)) n d q : ℝ) * Real.exp (-32) /
          (effectiveSize n q * logScale n q) ≤ 1 / 2 by
          simpa [mul_div_assoc] using h)
    nlinarith
  have hNexp : effectiveSize n q ≤ Real.exp (logScale n q) := by
    rw [logScale, Real.exp_log (by positivity)]
    linarith [Real.exp_pos (1 : ℝ)]
  have hLexp : logScale n q ≤ Real.exp (logScale n q) := by
    linarith [Real.add_one_le_exp (logScale n q)]
  have hprod : effectiveSize n q * logScale n q ≤ Real.exp (2 * logScale n q) := by
    rw [show 2 * logScale n q = logScale n q + logScale n q by ring, Real.exp_add]
    exact mul_le_mul hNexp hLexp (by linarith) (Real.exp_nonneg _)
  apply (activatedAugmentedMixture_factorial_cutoff_bound (Real.exp (-32)) n d
    (lowerDegree n q) q hn hd hb hq hslice hπ).trans
  calc
    _ ≤ (effectiveSize n q * logScale n q / (2 * Real.exp (-32))) *
        Real.exp (-30 * logScale n q) :=
      mul_le_mul hcap (activation_factorial_ratio_le_exp n q hN hell)
        (by unfold lowerEndpoint; positivity)
        (div_nonneg (mul_nonneg hN.le (by linarith)) (by positivity))
    _ ≤ (Real.exp (2 * logScale n q) / Real.exp (-32)) *
        Real.exp (-30 * logScale n q) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact (div_le_div_of_nonneg_left (mul_nonneg hN.le (by linarith)) (Real.exp_pos (-32))
        (by linarith [Real.exp_pos (-32)])).trans
          (div_le_div_of_nonneg_right hprod (Real.exp_nonneg (-32)))
    _ = _ := by
      rw [← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring

/-- Given [the specified inputs and assumptions](hyp:u,n,d,q,hu,hn,hd,hq,hslice,π,hπ,hlarge), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_cutoff_budget
lemma activatedAugmentedMixture_cutoff_budget (u : ℝ) (n d : ℕ) (q : ℝ)
    (hu : 0 < u) (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : 0 < q)
    (hslice : RareArrivalSlice n q)
    {π : Measure ℝ} (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π)
    (hlarge : Real.exp ((32 - Real.log (u / 16)) / 28) ≤ effectiveSize n q) :
    (activatedAugmentedMixture (Real.exp (-32)) n d q π).real
      {s | ¬ ∀ x : Fin d, x.val < rareCount (Real.exp (-32)) n d q →
        (∑ i ∈ Finset.univ.filter (fun i => (s i).2.X = x),
          if (s i).1 then 1 else 0) ≤ lowerDegree n q} ≤ u / 16 := by
  have hlog := Real.log_le_log
    (Real.exp_pos ((32 - Real.log (u / 16)) / 28))
    (hlarge.trans (show effectiveSize n q ≤ Real.exp 1 + effectiveSize n q by
      linarith [Real.exp_pos (1 : ℝ)]))
  rw [Real.log_exp] at hlog
  change (32 - Real.log (u / 16)) / 28 ≤ logScale n q at hlog
  apply (activatedAugmentedMixture_cutoff_le_exp n d q hn hd hq hslice hπ).trans
  calc
    Real.exp (32 - 28 * logScale n q) ≤ Real.exp (Real.log (u / 16)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = u / 16 := Real.exp_log (by positivity)

/-- Given [the specified inputs and assumptions](hyp:n,d,M,q,α,hn,hd,hq,hslice,π₀,π₁,h₀,h₁,hm,hgap,hα,hα1,hM,hgrid,hJ,hlarge), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_interval_minimax_calibrated
lemma activatedAugmentedMixture_interval_minimax_calibrated
    (n d M : ℕ) (q α : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : 0 < q) (hslice : RareArrivalSlice n q)
    {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (hm : ∀ v : ℕ, v ≤ lowerDegree n q → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (hgap : 1 / 12 ≤ (∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀)
    (hα : 0 ≤ α) (hα1 : α < 1) (hM : 1 ≤ M)
    (hgrid : 8 / (1 - α) ≤ (M : ℝ))
    (hJ : 18432 * (M : ℝ) ^ 2 / (1 - α) ≤
      (rareCount (Real.exp (-32)) n d q : ℝ))
    (hlarge : Real.exp ((32 - Real.log ((1 - α) / 16)) / 28) ≤ effectiveSize n q) :
    (21 * (1 - α) / 32) * ((rareCount (Real.exp (-32)) n d q : ℝ) *
      rareMass (Real.exp (-32)) n q *
      ((∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀)) ≤ intervalLengthRisk n d q α := by
  have hN : 0 < effectiveSize n q := by unfold effectiveSize; positivity
  have hell : 1 ≤ logScale n q := by
    unfold logScale
    have h := Real.log_le_log (Real.exp_pos (1 : ℝ))
      (show Real.exp 1 ≤ Real.exp 1 + effectiveSize n q by linarith)
    simpa using h
  have hb : 0 < rareMass (Real.exp (-32)) n q := by unfold rareMass; positivity
  apply activatedAugmentedMixture_interval_minimax_of_cutoff (Real.exp (-32)) n d M q α
    hn hd hb hq hslice h₀ h₁ (lowerDegree n q) hm hgap hα hα1 hM hgrid hJ
  exact activatedAugmentedMixture_cutoff_budget (1 - α) n d q (by linarith)
    hn hd hq hslice (finiteReciprocalPrior_interpolate h₀ h₁ (by simp)) hlarge

/-- Given [the specified inputs and assumptions](hyp:n,q,hK), [the stated mathematical conclusion holds](goal). -/
-- @node: interval_ordered_reciprocal_priors
lemma interval_ordered_reciprocal_priors
    (n : ℕ) (q : ℝ) (hK : 2 ≤ lowerDegree n q) :
    ∃ π₀ π₁ : Measure ℝ,
      FiniteReciprocalPrior (lowerEndpoint n q) π₀ ∧
      FiniteReciprocalPrior (lowerEndpoint n q) π₁ ∧
      (∀ v : ℕ, v ≤ lowerDegree n q → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁) ∧
      1 / 12 ≤ (∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀ := by
  obtain ⟨π₀, π₁, hp₀, hp₁, ⟨s₀, s₁, hs₀, hs₁, hm₀, hm₁⟩, hm, hgap⟩ :=
    moment_matched_reciprocal_priors (lowerDegree n q) hK
  have h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀ :=
    ⟨hp₀, s₀, hs₀, hm₀⟩
  have h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁ :=
    ⟨hp₁, s₁, hs₁, hm₁⟩
  by_cases horder : (∫ z, z⁻¹ ∂π₀) ≤ ∫ z, z⁻¹ ∂π₁
  · refine ⟨π₀, π₁, h₀, h₁, hm, ?_⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr horder)] using hgap
  · refine ⟨π₁, π₀, h₁, h₀, fun v hv => (hm v hv).symm, ?_⟩
    rw [abs_of_nonpos (by linarith)] at hgap
    linarith

/-- Given [the specified inputs and assumptions](hyp:α,hα,hα1), [the stated mathematical conclusion holds](goal). -/
-- @node: interval_activated_large_regime
lemma interval_activated_large_regime
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) :
    ∃ (T : ℝ) (D : ℕ) (cAct : ℝ), 1 ≤ T ∧ 1 ≤ D ∧ 0 < cAct ∧
      ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d → 0 < q → q ≤ 1 →
        RareArrivalSlice n q → T ≤ effectiveSize n q →
          (D : ℝ) ≤ (2 * rareMass (Real.exp (-32)) n q)⁻¹ ∧
          (D ≤ rareCount (Real.exp (-32)) n d q →
            cAct * min 1 ((d : ℝ) / (effectiveSize n q * logScale n q)) ≤
              intervalLengthRisk n d q α) := by
  let u := 1 - α
  let η := Real.exp (-32)
  let M := Nat.ceil (8 / u) + 1
  let D := Nat.ceil (18432 * (M : ℝ) ^ 2 / u) + 1
  have hu : 0 < u := by dsimp [u]; linarith
  obtain ⟨hM, hgridInv, hD, hDreal⟩ := interval_activation_grid_thresholds u hu
  have hD' : 1 ≤ D := hD
  have hη : 0 < η := Real.exp_pos _
  have hηsmall : η ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (32 : ℝ)
    dsimp [η]
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos 32)).mpr
    linarith
  let T := max 1 (max (Real.exp 2) (max (4 * η)
    (max (2 * η * D) (Real.exp ((32 - Real.log (u / 16)) / 28)))))
  let cAct := (21 * u / 32) * (η / 24)
  refine ⟨T, D, cAct, le_max_left _ _, hD, by dsimp [cAct]; positivity, ?_⟩
  intro n d q hn hd hq _hq1 hslice hlarge
  have hN : 0 < effectiveSize n q := by unfold effectiveSize; positivity
  have hell : 1 ≤ logScale n q := by
    unfold logScale
    have h := Real.log_le_log (Real.exp_pos (1 : ℝ))
      (show Real.exp 1 ≤ Real.exp 1 + effectiveSize n q by linarith)
    simpa using h
  have hTexp : Real.exp 2 ≤ effectiveSize n q :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hTmass : 4 * η ≤ effectiveSize n q :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hlarge))
  have hTcap : 2 * η * D ≤ effectiveSize n q :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge)))
  have hTtail : Real.exp ((32 - Real.log (u / 16)) / 28) ≤ effectiveSize n q :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge)))
  refine ⟨interval_capacity_of_large_size η D n q hη hN hell hTcap, ?_⟩
  intro hJ
  change D ≤ rareCount η n d q at hJ
  have hK : 2 ≤ lowerDegree n q := by
    have hlog := Real.log_le_log (Real.exp_pos (2 : ℝ))
      (hTexp.trans (show effectiveSize n q ≤ Real.exp 1 + effectiveSize n q by
        linarith [Real.exp_pos (1 : ℝ)]))
    rw [Real.log_exp] at hlog
    have hceil := Nat.le_ceil (logScale n q)
    have : (2 : ℝ) ≤ (lowerDegree n q : ℝ) := hlog.trans hceil
    exact_mod_cast this
  obtain ⟨π₀, π₁, h₀, h₁, hm, hgap⟩ :=
    interval_ordered_reciprocal_priors n q hK
  have hJreal : 18432 * (M : ℝ) ^ 2 / (1 - α) ≤ (rareCount η n d q : ℝ) :=
    hDreal.trans (Nat.cast_le.mpr hJ)
  have hgrid : 8 / (1 - α) ≤ (M : ℝ) := by
    have h := Nat.le_ceil (8 / u)
    dsimp [M]
    push_cast
    dsimp [u] at h
    linarith
  have hlength := activatedAugmentedMixture_interval_minimax_calibrated n d M q α
    hn hd hq hslice h₀ h₁ hm hgap hα hα1 hM hgrid hJreal hTtail
  have hbsmall : rareMass η n q ≤ 1 / 4 := by
    unfold rareMass
    apply (div_le_iff₀ (by positivity : 0 < effectiveSize n q * logScale n q)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hell hN.le]
  have hd2 : 2 ≤ d := by
    have hc : rareCount η n d q ≤ d - 1 := min_le_left _ _
    omega
  have hsep : (rareCount η n d q : ℝ) * rareMass η n q / 12 ≤
      (rareCount η n d q : ℝ) * rareMass η n q *
        ((∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀) := by
    have hb : 0 < rareMass η n q := by unfold rareMass; positivity
    nlinarith [mul_le_mul_of_nonneg_left hgap
      (mul_nonneg (Nat.cast_nonneg (rareCount η n d q)) hb.le)]
  have hwidth := interval_prior_segment_width_lower η _ n d q hη hηsmall hd2 hN
    (by linarith) hbsmall hsep
  have hfinal : cAct * min 1 ((d : ℝ) / (effectiveSize n q * logScale n q)) ≤
      (21 * (1 - α) / 32) * ((rareCount η n d q : ℝ) * rareMass η n q *
        ((∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀)) := by
    simpa only [cAct, u, mul_assoc] using
      mul_le_mul_of_nonneg_left hwidth (show 0 ≤ 21 * (1 - α) / 32 by positivity)
  exact hfinal.trans hlength

end CausalSmith.Stat.MarRareqLogfrontier
