import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ConcentrationCore

/-! Uniform concentration of the finite-product observable summary. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set

/-- The five-block empirical summary concentrates uniformly, including the empty-arm event. -/
-- @node: lem:uniform-summary-concentration
lemma uniform_summary_concentration
    (k dx dz : ℕ) (pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    ∃ C0 : ℝ, ConcentrationConstantDomain C0 ∧
      ∀ (L : ℝ) (n : ℕ), 1 ≤ L → 1 ≤ n →
      ∀ (P : Measure (FullData k dx dz))
      (_hP : IsProbabilityMeasure P),
      letI := _hP
      UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P →
      ∀ eta : ℝ, TailLevelDomain eta →
        (sampleLaw (n := n) P).real
          {sample | C0 * L * Real.sqrt (Real.log (C0 / eta) / n) <
            dS (empSummary sample) (obsSummary P)} ≤ eta ∧
        ∀ t : Bool,
          (sampleLaw (n := n) P).real {sample | armCount t sample = 0} =
              (1 - (obsLaw P).real {o | o.T = t}) ^ n ∧
            (sampleLaw (n := n) P).real {sample | armCount t sample = 0} ≤
              (1 - k * pi0) ^ n := by
  let cardR : ℝ := Fintype.card (SummaryCoord dx dz)
  let Ksmall : ℝ := 16 * entryNormConstant dz dx / (k * pi0) + dx
  let Klarge : ℝ := 4 * (entryNormConstant dz dx + 1) + dx + 1
  let C0 : ℝ := max (cardR + 1) (max (2 * Ksmall) (4 * Klarge / (k * pi0)))
  refine ⟨C0, ?_, ?_⟩
  · have hcard0 : 0 ≤ cardR := by positivity
    exact le_trans (by linarith) (le_max_left _ _)
  intro L n hL hn P hP
  letI := hP
  intro hM eta hEta
  rcases hEta with ⟨heta, hetaHalf⟩
  have hn0 : 0 < n := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hk)
  have hkpi : 0 < (k : ℝ) * pi0 := mul_pos hk0 hpi
  have hcard0 : 0 ≤ cardR := by positivity
  have hC_card : cardR ≤ C0 := le_trans (by linarith) (le_max_left _ _)
  have hC1 : 1 ≤ C0 := le_trans (by linarith) (le_max_left _ _)
  have hCpos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC1
  let s : ℝ := Real.sqrt (Real.log (C0 / eta) / n)
  let beta : ℝ := 2 * s
  let badDev : Set (Fin n → Obs dx dz) := {sample | ∃ c : SummaryCoord dx dz,
    summaryCoordScale L c * beta ≤
      |(n : ℝ)⁻¹ * ∑ i, summaryCoordStat c (sample i) -
        ∫ o, summaryCoordStat c o ∂obsLaw P|}
  let badSupport : Set (Fin n → Obs dx dz) := {sample | ¬ ∀ i c,
    |summaryCoordStat c (sample i)| ≤ summaryCoordScale L c}
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hbeta0 : 0 ≤ beta := mul_nonneg (by norm_num) hs0
  have hbadDev : (sampleLaw (n := n) P).real badDev ≤ eta := by
    have hUnion : (sampleLaw (n := n) P).real badDev ≤
        ∑ c : SummaryCoord dx dz, (sampleLaw (n := n) P).real
          {sample | summaryCoordScale L c * beta ≤
            |(n : ℝ)⁻¹ * ∑ i, summaryCoordStat c (sample i) -
              ∫ o, summaryCoordStat c o ∂obsLaw P|} := by
      rw [show badDev = ⋃ c : SummaryCoord dx dz,
          {sample | summaryCoordScale L c * beta ≤
            |(n : ℝ)⁻¹ * ∑ i, summaryCoordStat c (sample i) -
              ∫ o, summaryCoordStat c o ∂obsLaw P|} by
        ext sample
        simp [badDev]]
      exact measureReal_iUnion_fintype_le _
    have hcoord (c : SummaryCoord dx dz) :
        (sampleLaw (n := n) P).real
          {sample | summaryCoordScale L c * beta ≤
            |(n : ℝ)⁻¹ * ∑ i, summaryCoordStat c (sample i) -
              ∫ o, summaryCoordStat c o ∂obsLaw P|} ≤ 2 * (eta / C0) ^ 2 := by
      simpa [beta, s] using summaryCoord_deviation_probability P hM hL hn0 heta
        (by linarith : eta < 1) hC1 c
    calc
      _ ≤ ∑ _c : SummaryCoord dx dz, 2 * (eta / C0) ^ 2 :=
        hUnion.trans (Finset.sum_le_sum fun _ _ => hcoord _)
      _ = cardR * (2 * (eta / C0) ^ 2) := by
        simp [cardR]
      _ ≤ C0 * (2 * (eta / C0) ^ 2) := by gcongr
      _ = 2 * eta ^ 2 / C0 := by field_simp
      _ ≤ 2 * eta ^ 2 := by
        rw [div_le_iff₀ hCpos]
        nlinarith [sq_nonneg eta]
      _ ≤ eta := by nlinarith
  have hbadSupport : (sampleLaw (n := n) P).real badSupport = 0 := by
    have hae := sample_summaryCoordSupport_ae P hM hL (n := n)
    have hz : sampleLaw (n := n) P badSupport = 0 := by
      rw [← ae_iff]
      simpa [badSupport] using hae
    simp [Measure.real, hz]
  have hRiskSubset :
      {sample | C0 * L * s < dS (empSummary sample) (obsSummary P)} ⊆
        badDev ∪ badSupport := by
    intro sample hrisk
    change C0 * L * s < dS (empSummary sample) (obsSummary P) at hrisk
    by_cases hsupp : ∀ i c,
        |summaryCoordStat c (sample i)| ≤ summaryCoordScale L c
    · left
      by_contra hnot
      have hdev : ∀ c : SummaryCoord dx dz,
          |(n : ℝ)⁻¹ * ∑ i, summaryCoordStat c (sample i) -
            ∫ o, summaryCoordStat c o ∂obsLaw P| < summaryCoordScale L c * beta := by
        intro c
        have hc : ¬ summaryCoordScale L c * beta ≤
            |(n : ℝ)⁻¹ * ∑ i, summaryCoordStat c (sample i) -
              ∫ o, summaryCoordStat c o ∂obsLaw P| := by
          intro hc
          exact hnot (by exact ⟨c, hc⟩)
        exact lt_of_not_ge hc
      have hdS : dS (empSummary sample) (obsSummary P) ≤ C0 * L * s := by
        by_cases hsmall : beta < (k : ℝ) * pi0 / 2
        · have hraw := empSummary_error_of_small_deviations P hM hL hpi hn0
              hbeta0 hsmall sample hdev
          have hCsmall : 2 * Ksmall ≤ C0 :=
            le_trans (le_max_left _ _) (le_max_right _ _)
          calc
            _ ≤ Ksmall * L * beta := by simpa [Ksmall] using hraw
            _ = (2 * Ksmall) * L * s := by simp [beta]; ring
            _ ≤ C0 * L * s := by gcongr
        · have hraw := empSummary_error_on_support P hM hL hpi hn0 sample hsupp
          have hsLower : (k : ℝ) * pi0 / 4 ≤ s := by
            dsimp [beta] at hsmall
            linarith
          have hClarge : 4 * Klarge / ((k : ℝ) * pi0) ≤ C0 :=
            le_trans (le_max_right _ _) (le_max_right _ _)
          calc
            _ ≤ Klarge * L := by simpa [Klarge] using hraw
            _ ≤ (4 * Klarge / ((k : ℝ) * pi0)) * L * s := by
              have hKlarge0 : 0 ≤ Klarge := by
                dsimp [Klarge]
                have he := entryNormConstant_nonneg dz dx
                positivity
              have hfactor : 1 ≤ 4 * s / ((k : ℝ) * pi0) := by
                rw [le_div_iff₀ hkpi]
                linarith
              calc
                Klarge * L ≤ Klarge * L * (4 * s / ((k : ℝ) * pi0)) :=
                  by
                    simpa using (mul_le_mul_of_nonneg_left hfactor
                      (mul_nonneg hKlarge0 (le_trans zero_le_one hL)))
                _ = (4 * Klarge / ((k : ℝ) * pi0)) * L * s := by
                  field_simp
            _ ≤ C0 * L * s := by
              simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hClarge
                (mul_nonneg (le_trans zero_le_one hL) hs0))
      exact (not_lt_of_ge hdS) hrisk
    · right
      simpa [badSupport] using hsupp
  have hRisk : (sampleLaw (n := n) P).real
      {sample | C0 * L * s < dS (empSummary sample) (obsSummary P)} ≤ eta := by
    calc
      _ ≤ (sampleLaw (n := n) P).real (badDev ∪ badSupport) :=
        measureReal_mono hRiskSubset
      _ ≤ (sampleLaw (n := n) P).real badDev +
          (sampleLaw (n := n) P).real badSupport := measureReal_union_le _ _
      _ ≤ eta := by rw [hbadSupport, add_zero]; exact hbadDev
  constructor
  · simpa [s] using hRisk
  intro t
  have hempty : (sampleLaw (n := n) P).real {sample | armCount t sample = 0} =
      (1 - (obsLaw P).real {o | o.T = t}) ^ n := by
    rw [show {sample : Fin n → Obs dx dz | armCount t sample = 0} =
        Set.pi Set.univ (fun _ => {o | o.T ≠ t}) by
      ext sample
      simp [armCount, Finset.card_eq_zero]]
    rw [sampleLaw, Measure.real, Measure.pi_pi]
    simp only [Finset.prod_const]
    rw [Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
    congr 1
    rw [show {o : Obs dx dz | o.T ≠ t} = {o | o.T = t}ᶜ by ext; simp]
    change (obsLaw P).real ({o | o.T = t}ᶜ) = _
    rw [measureReal_compl]
    · simp
    · exact measurable_obs_T (measurableSet_singleton t)
  refine ⟨hempty, hempty.trans_le ?_⟩
  have hqLower : (k : ℝ) * pi0 ≤ (obsLaw P).real {o | o.T = t} := by
    rw [show {o : Obs dx dz | o.T = t} = obsArm t by rfl, obsLaw_real_obsArm]
    exact arm_mass_lower_of_latentArmPositivity P hM.latentArmPositivity t
  have hqUpper : (obsLaw P).real {o | o.T = t} ≤ 1 := measureReal_le_one
  have hbase0 : 0 ≤ 1 - (obsLaw P).real {o | o.T = t} := by linarith
  apply pow_le_pow_left₀ hbase0 (by linarith) n

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
