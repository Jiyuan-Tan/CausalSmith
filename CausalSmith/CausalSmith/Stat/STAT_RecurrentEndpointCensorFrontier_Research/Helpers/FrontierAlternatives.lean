module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.MinimaxLowerRisk

/-! # Amplitude-controlled frontier alternatives

The genuine endpoint and critical constructions retain a quadratic sample KL
coefficient independent of amplitude, together with their target separations.
-/

public section

open MeasureTheory Set


namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- In either endpoint regime the same legal pair has quadratic KL and
root-frontier target separation. The coefficient is chosen before amplitude. -/
-- @node: frontier_twoPoint_family
lemma frontier_twoPoint_family (c : ClassConstants)
    (hNonempty : ∃ P : SubjectLaw, ModelClass c P) (hk : 1 ≤ c.kappa) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ u : ℝ, 0 < u → u ≤ r →
      ∃ δ : ℝ, ∃ N : ℕ, 0 < δ ∧ 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        ∃ P₀ P₁ : SubjectLaw, ModelClass c P₀ ∧ ModelClass c P₁ ∧
          InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw P₀ n) < ⊤ ∧
          (InformationTheory.klDiv (sampleLaw P₁ n) (sampleLaw P₀ n)).toReal ≤ C * u ^ 2 ∧
          δ * Real.sqrt (riskScale c n) ≤ |causalTarget P₁ - causalTarget P₀| := by
  obtain ⟨P, hP⟩ := hNonempty
  obtain ⟨cut⟩ := nonempty_cutoffData c
  let Pbase := midpointBaseline c P
  have hbase : ModelClass c Pbase := midpointBaseline_modelClass c P hP
  have hintBase := (hbase.armMean_integrand_intervalIntegrable true).sub
    (hbase.armMean_integrand_intervalIntegrable false)
  by_cases heq : c.kappa = 1
  · obtain ⟨C, hC, r, hr, hw⟩ :=
      exists_criticalPerturb_KL_witnesses_quadratic c P hP cut heq
    refine ⟨C, r, hC, hr, ?_⟩
    intro u hu hur
    obtain ⟨K, N, hK, hKeq, hN, hwitness⟩ := hw u hu hur
    obtain ⟨δ, Nsep, hδ, hNsep, hsep⟩ :=
      exists_criticalDirection_integral_rate_lower c P cut hu
    refine ⟨δ, max N Nsep, hδ, hN.trans (le_max_left _ _), ?_⟩
    intro n hn
    obtain ⟨P₁, hm, hp, hh, hf, hc, hr, ht, hkeq, hkbound⟩ :=
      hwitness n ((le_max_left _ _).trans hn)
    have hfinite := (midpointPerturb_sampleKL_finite c P hP P₁ hm n hp hh hf hc).1
    refine ⟨Pbase, P₁, hbase, hm, hfinite, ?_, ?_⟩
    · rwa [hKeq] at hkbound
    · have htarget := critical_causalTarget_sub_eq_integral c P₁ Pbase cut u n
        hm.causalTarget_eq_survival_intensity_contrast hbase.causalTarget_eq_survival_intensity_contrast
        ((hm.armMean_integrand_intervalIntegrable true).sub
          (hm.armMean_integrand_intervalIntegrable false)) hintBase hh hf ht
      rw [htarget]
      have hs := (hsep n ((le_max_right _ _).trans hn)).trans (le_abs_self _)
      simpa only [riskScale, if_neg (not_lt_of_ge hk), if_pos heq] using hs
  · let C := (3 / 2 : ℝ) * c.gMax *
      (endpointBumpBound c cut ^ 2 / midpointLambda c)
    have hC : 0 < C := by
      have hg := c.gMin_pos.trans c.gMin_lt
      have hb := endpointBumpBound_pos c cut
      have hl := c.lambdaMin_pos.trans (midpoint_strict_bounds c).1
      dsimp [C]
      positivity
    refine ⟨C, endpointModelRadius c cut, hC, endpointModelRadius_pos c cut, ?_⟩
    intro u hu hur
    obtain ⟨K, N, hK, hKeq, hN, hwitness⟩ :=
      exists_endpointPerturb_KL_witnesses_quadratic c P hP cut hu hur
    let δ := midpointSurvivalFloor c P * u * endpointBumpMass c cut
    have hδ : 0 < δ := (endpointDirection_integral_rate_lower c P cut hu (by omega : 1 ≤ (1 : ℕ))).1
    refine ⟨δ, N, hδ, hN, ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := by omega
    obtain ⟨P₁, hm, hp, hh, hf, hc, hr, ht, hkeq, hkbound⟩ := hwitness n hn
    have hfinite := (midpointPerturb_sampleKL_finite c P hP P₁ hm n hp hh hf hc).1
    refine ⟨Pbase, P₁, hbase, hm, hfinite, ?_, ?_⟩
    · rwa [hKeq] at hkbound
    · have htarget := endpoint_causalTarget_sub_eq_integral c P₁ Pbase cut u
        (endpointBandwidth c n)
        hm.causalTarget_eq_survival_intensity_contrast hbase.causalTarget_eq_survival_intensity_contrast
        ((hm.armMean_integrand_intervalIntegrable true).sub
          (hm.armMean_integrand_intervalIntegrable false)) hintBase hh hf
        (by simpa only [endpointBandwidth_eq] using ht)
      rw [htarget]
      have hs := (endpointDirection_integral_rate_lower c P cut hu hn1).2.trans (le_abs_self _)
      have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hq : 0 ≤ (n : ℝ) ^ (-(c.beta + 1) / (2 * c.beta + c.kappa + 1)) :=
        (Real.rpow_pos_of_pos hnreal _).le
      have hsq : ((n : ℝ) ^ (-(c.beta + 1) / (2 * c.beta + c.kappa + 1))) ^ 2 =
          riskScale c n := by
        rw [riskScale, if_neg (not_lt_of_ge hk), if_neg heq,
          ← Real.rpow_mul_natCast hnreal.le]
        congr 1
        ring
      rw [← hsq, Real.sqrt_sq hq]
      exact hs

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
