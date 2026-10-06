module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedMeasurability
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CateLowerInformation
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CateLowerRisk
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.ControlCellTail
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.ControlRate
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.ControlResiduals
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.ControlTail
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.T_SharpMinimax

/-! # Smooth-control CATE rate -/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped ENNReal BigOperators

-- @node: supLoss_sub_le
/-- The sup-norm error of a contrast is bounded by the sum of its arm errors. -/
lemma supLoss_sub_le {d : ℕ} (f₁ f₀ g₁ g₀ : (Fin d → ℝ) → ℝ) :
    supLoss (fun x => f₁ x - f₀ x) (fun x => g₁ x - g₀ x) ≤
      supLoss f₁ g₁ + supLoss f₀ g₀ := by
  apply iSup_le
  intro x
  have htriangle : |(f₁ x - f₀ x) - (g₁ x - g₀ x)| ≤
      |f₁ x - g₁ x| + |f₀ x - g₀ x| := by
    calc
      _ = |(f₁ x - g₁ x) + -(f₀ x - g₀ x)| := by congr 1; ring
      _ ≤ |f₁ x - g₁ x| + |-(f₀ x - g₀ x)| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  exact (ENNReal.ofReal_le_ofReal htriangle).trans
    (ENNReal.ofReal_add_le.trans (add_le_add
      (le_iSup (fun x : cube d => ENNReal.ofReal |f₁ x - g₁ x|) x)
      (le_iSup (fun x : cube d => ENNReal.ofReal |f₀ x - g₀ x|) x)))

-- @node: lawRisk_sub_le
/-- Expected sup-norm error of any two fitted curves is bounded by their
armwise risks, provided one arm loss is measurable. -/
lemma lawRisk_sub_le {d n : ℕ} (P : Law d)
    (f₁ f₀ : (Fin n → Obs d) → (Fin d → ℝ) → ℝ)
    (g₁ g₀ : (Fin d → ℝ) → ℝ)
    (h₁ : AEMeasurable (fun sample => supLoss (f₁ sample) g₁) (P.sample n)) :
    lawRisk P (fun sample x => f₁ sample x - f₀ sample x) (fun x => g₁ x - g₀ x) ≤
      lawRisk P f₁ g₁ + lawRisk P f₀ g₀ := by
  unfold lawRisk
  calc
    _ ≤ ∫⁻ sample, supLoss (f₁ sample) g₁ + supLoss (f₀ sample) g₀ ∂P.sample n := by
      apply lintegral_mono
      intro sample
      exact supLoss_sub_le _ _ _ _
    _ = _ := lintegral_add_left' h₁ _

-- @node: cateEstimator_lawRisk_le
/-- Integrating the contrast triangle inequality gives roadmap (C20).
One measurable arm loss suffices for Lebesgue-integral additivity. -/
lemma cateEstimator_lawRisk_le {d n : ℕ} (P : Law d) (j : ℕ) (β M : ℝ)
    (h₁ : AEMeasurable
      (fun sample : Fin n → Obs d => supLoss (balancedEstimator sample j β M) P.mu1)
      (P.sample n)) :
    lawRisk P (fun sample : Fin n → Obs d => cateEstimator sample j β M) P.tau ≤
      lawRisk P (fun sample : Fin n → Obs d => balancedEstimator sample j β M) P.mu1 +
      lawRisk P (fun sample : Fin n → Obs d => controlBalancedEstimator sample j β M) P.mu0 := by
  exact lawRisk_sub_le P _ _ _ _ h₁

-- @node: cateEstimator_lawRisk_rate_of_arm_bounds
/-- Armwise risk bounds at a common rate add to the CATE risk bound. -/
lemma cateEstimator_lawRisk_rate_of_arm_bounds {d n : ℕ} (P : Law d)
    (j : ℕ) (β M K₁ K₀ r : ℝ) (hK₁ : 0 ≤ K₁) (hK₀ : 0 ≤ K₀) (hr : 0 ≤ r)
    (hmeas : AEMeasurable
      (fun sample : Fin n → Obs d => supLoss (balancedEstimator sample j β M) P.mu1)
      (P.sample n))
    (h₁ : lawRisk P (fun sample : Fin n → Obs d => balancedEstimator sample j β M)
      P.mu1 ≤ ENNReal.ofReal (K₁ * r))
    (h₀ : lawRisk P (fun sample : Fin n → Obs d => controlBalancedEstimator sample j β M)
      P.mu0 ≤ ENNReal.ofReal (K₀ * r)) :
    lawRisk P (fun sample : Fin n → Obs d => cateEstimator sample j β M) P.tau ≤
      ENNReal.ofReal ((K₁ + K₀) * r) := by
  calc
    _ ≤ _ := cateEstimator_lawRisk_le P j β M hmeas
    _ ≤ ENNReal.ofReal (K₁ * r) + ENNReal.ofReal (K₀ * r) := add_le_add h₁ h₀
    _ = ENNReal.ofReal ((K₁ + K₀) * r) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hK₁ hr) (mul_nonneg hK₀ hr), add_mul]

-- @node: controlBalancedEstimator_range
/-- Clipping keeps the control fit inside the outcome range, even at zero counts. -/
lemma controlBalancedEstimator_range {d n : ℕ} (sample : Fin n → Obs d)
    (j : ℕ) (β M : ℝ) (hM : 0 ≤ M) (x : Fin d → ℝ) :
    controlBalancedEstimator sample j β M x ∈ Set.Icc (-M) M := by
  unfold controlBalancedEstimator armBalancedEstimator
  dsimp only
  split_ifs
  · exact ⟨by linarith, hM⟩
  · exact ⟨le_max_left _ _, (max_le_iff).2 ⟨by linarith, min_le_left _ _⟩⟩

/-- Roadmap (C17): the logarithmic stochastic scale converts the control
union bound into a bandwidth-independent Gaussian deviation bound. -/
-- @node: control_balancedEstimator_log_deviation
lemma control_balancedEstimator_log_deviation (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M) (hκ : 0 < κ) :
    ∃ B K A : ℝ, 0 < B ∧ 0 < K ∧ 0 < A ∧
      ∀ (n j : ℕ), 1 ≤ n → ∀ P : Law d, CATEClass d β γ C L M κ P →
      ∀ u : ℝ, 1 ≤ u →
        (P.sample n).real {sample | supLoss (controlBalancedEstimator sample j β M) P.mu0 >
          ENNReal.ofReal (B * L * (dyadicWidth j) ^ β + u *
            (A * M * Real.sqrt (Real.log (2 / dyadicWidth j) /
              ((n : ℝ) * (dyadicWidth j) ^ d))))} ≤
          K * Real.exp (-Real.log 2 * u ^ 2) := by
  obtain ⟨B, K, c, hB, hK, hc, htail⟩ :=
    control_balancedEstimator_global_tail d β γ C L M κ hparam hκ
  let A := Real.sqrt (((d : ℝ) + 1) / c)
  have hA : 0 < A := by dsimp [A]; positivity
  have hA2 : A ^ 2 = ((d : ℝ) + 1) / c := by
    dsimp [A]; rw [Real.sq_sqrt (by positivity)]
  refine ⟨B, K, A, hB, hK, hA, ?_⟩
  intro n j hn P hP u hu
  let h := dyadicWidth j
  have hh : 0 < h := (dyadicWidth_mem_Ioc j).1
  have hh1 : h ≤ 1 := (dyadicWidth_mem_Ioc j).2
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hM : 0 < M := hparam.2.2.2.2.2
  have hL : 0 < L := hparam.2.2.2.2.1
  have hlog : 0 < Real.log (2 / h) := Real.log_pos (by
    apply (lt_div_iff₀ hh).2; linarith)
  let t := u * (A * M * Real.sqrt (Real.log (2 / h) / ((n : ℝ) * h ^ d)))
  have ht : 0 < t := by dsimp [t]; positivity
  have hbound (sample : Fin n → Obs d) :
      supLoss (controlBalancedEstimator sample j β M) P.mu0 ≤ ENNReal.ofReal (2 * M) := by
    apply supLoss_le_two_mul_of_range
    · intro x _; exact controlBalancedEstimator_range sample j β M hM.le x
    · exact hP.semantics.2.2.2.2.2
  by_cases htM : t ≤ 2 * M
  · have heq : -c * (n : ℝ) * h ^ d * t ^ 2 / M ^ 2 =
        -((d : ℝ) + 1) * u ^ 2 * Real.log (2 / h) := by
      dsimp [t]
      rw [mul_pow, mul_pow, mul_pow, hA2,
        Real.sq_sqrt (by positivity)]
      field_simp
    have htbound := htail n j hn P hP t ht htM
    change (P.sample n).real _ ≤ _
    apply htbound.trans
    change K / h ^ d * Real.exp (-c * (n : ℝ) * h ^ d * t ^ 2 / M ^ 2) ≤ _
    rw [heq]
    exact controlLog_gaussian_envelope d hh hh1 hu hK.le
  · have hempty : {sample : Fin n → Obs d |
        supLoss (controlBalancedEstimator sample j β M) P.mu0 >
          ENNReal.ofReal (B * L * h ^ β + t)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro sample hx
      have hb : 0 ≤ B * L * h ^ β := by positivity
      exact (not_lt_of_ge ((hbound sample).trans (ENNReal.ofReal_le_ofReal
        (by linarith : 2 * M ≤ B * L * h ^ β + t)))) hx
    change (P.sample n).real _ ≤ _
    rw [hempty]
    simp only [measureReal_empty]
    positivity

/-- Roadmap (C18): layer cake integrates the normalized control tail,
using probability at most one below the logarithmic threshold. -/
-- @node: control_balancedEstimator_log_risk
lemma control_balancedEstimator_log_risk (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M) (hκ : 0 < κ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ (n j : ℕ), 1 ≤ n → ∀ P : Law d,
      CATEClass d β γ C L M κ P →
      lawRisk P (fun sample : Fin n → Obs d => controlBalancedEstimator sample j β M)
        P.mu0 ≤ ENNReal.ofReal (K₀ * (L * (dyadicWidth j) ^ β +
          M * Real.sqrt (Real.log (2 / dyadicWidth j) /
            ((n : ℝ) * (dyadicWidth j) ^ d)))) := by
  obtain ⟨B, K, A, hB, hK, hA, htail⟩ :=
    control_balancedEstimator_log_deviation d β γ C L M κ hparam hκ
  let H := (1 + K) * Real.exp (Real.log 2) / Real.log 2
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨H * max B A, mul_pos hH (hB.trans_le (le_max_left _ _)), ?_⟩
  intro n j hn P hP
  let : IsProbabilityMeasure (P.sample n) :=
    sample_isProbabilityMeasure P hP.iid hP.consistency (by omega)
  have hM : 0 < M := hparam.2.2.2.2.2
  have hL : 0 < L := hparam.2.2.2.2.1
  have hh : 0 < dyadicWidth j := (dyadicWidth_mem_Ioc j).1
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < Real.log (2 / dyadicWidth j) := Real.log_pos (by
    apply (lt_div_iff₀ hh).2
    linarith [(dyadicWidth_mem_Ioc j).2])
  let v := M * Real.sqrt (Real.log (2 / dyadicWidth j) /
    ((n : ℝ) * (dyadicWidth j) ^ d))
  have hv : 0 < v := by dsimp [v]; positivity
  have hfinite (sample : Fin n → Obs d) :
      supLoss (controlBalancedEstimator sample j β M) P.mu0 ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    apply supLoss_le_two_mul_of_range
    · intro x _; exact controlBalancedEstimator_range sample j β M hM.le x
    · exact hP.semantics.2.2.2.2.2
  have hmeas : AEMeasurable
      (fun sample : Fin n → Obs d => supLoss (controlBalancedEstimator sample j β M) P.mu0)
      (P.sample n) := by
    exact (armBalancedEstimator_supLoss_measurable false j β M P.mu0
      (holderOnCube_continuousOn hparam.2.1 hP.controlHolder)).aemeasurable
  have hmoment := gaussianTail_ennreal_lintegral_le (P.sample n)
    (fun sample : Fin n → Obs d => supLoss (controlBalancedEstimator sample j β M) P.mu0)
    hmeas hfinite (B * L * (dyadicWidth j) ^ β) (A * v) K (Real.log 2)
    (by positivity) (mul_pos hA hv) hK hc (by
      intro u hu
      simpa only [v, mul_assoc] using htail n j hn P hP u hu)
  apply hmoment.trans
  apply ENNReal.ofReal_le_ofReal
  change H * (B * L * (dyadicWidth j) ^ β + A * v) ≤
    (H * max B A) * (L * (dyadicWidth j) ^ β + v)
  rw [mul_assoc H]
  apply mul_le_mul_of_nonneg_left _ hH.le
  calc
    _ = B * (L * (dyadicWidth j) ^ β) + A * v := by ring
    _ ≤ max B A * (L * (dyadicWidth j) ^ β) + max B A * v :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hv.le)
    _ = _ := by ring

-- @node: cateEstimator_supLoss_le_four_mul
/-- The CATE loss is at most four times the outcome bound, as used to cover
finitely many small sample sizes after roadmap (C20). -/
lemma cateEstimator_supLoss_le_four_mul {d n : ℕ} (sample : Fin n → Obs d)
    (j : ℕ) (β γ C L M κ : ℝ) (P : Law d)
    (hP : CATEClass d β γ C L M κ P) :
    supLoss (cateEstimator sample j β M) P.tau ≤ ENNReal.ofReal (4 * M) := by
  have hM : 0 ≤ M := hP.parameters.2.2.2.2.2.le
  have hcontrol : supLoss (controlBalancedEstimator sample j β M) P.mu0 ≤
      ENNReal.ofReal (2 * M) := by
    apply supLoss_le_two_mul_of_range
    · intro x _
      exact controlBalancedEstimator_range sample j β M hM x
    · exact hP.semantics.2.2.2.2.2
  calc
    _ ≤ _ := supLoss_sub_le _ _ _ _
    _ ≤ ENNReal.ofReal (2 * M) + ENNReal.ofReal (2 * M) :=
      add_le_add (balancedEstimator_supLoss_le_two_mul sample j β γ C L M P
        hP.toLawClass) hcontrol
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- Integrating the clipping bound controls every positive sample size,
without requiring measurability of the loss for this upper bound. -/
-- @node: cateEstimator_lawRisk_le_four_mul
lemma cateEstimator_lawRisk_le_four_mul {d n : ℕ} (j : ℕ)
    (β γ C L M κ : ℝ) (P : Law d)
    (hP : CATEClass d β γ C L M κ P) (hn : 1 ≤ n) :
    lawRisk P (fun sample : Fin n → Obs d => cateEstimator sample j β M) P.tau ≤
      ENNReal.ofReal (4 * M) := by
  let : IsProbabilityMeasure (P.sample n) :=
    sample_isProbabilityMeasure P hP.iid hP.consistency (by omega)
  unfold lawRisk
  calc
    _ ≤ ∫⁻ _sample, ENNReal.ofReal (4 * M) ∂P.sample n :=
      lintegral_mono (fun sample =>
        cateEstimator_supLoss_le_four_mul sample j β γ C L M κ P hP)
    _ = _ := by simp

/-- A bounded risk with an eventual positive-rate bound has a uniform bound
at that rate: a finite sum of the small-sample constants covers the prefix. -/
-- @node: uniformRisk_rate_of_eventual
lemma uniformRisk_rate_of_eventual {Ι : Type*} (risk : ℕ → Ι → ENNReal)
    (r : ℕ → ℝ) (H K : ℝ) (N : ℕ) (hH : 0 ≤ H) (hK : 0 < K)
    (hr : ∀ n, 1 ≤ n → 0 < r n)
    (hbound : ∀ n, 1 ≤ n → ∀ i, risk n i ≤ ENNReal.ofReal H)
    (heventual : ∀ n, N ≤ n → 1 ≤ n → ∀ i,
      risk n i ≤ ENNReal.ofReal (K * r n)) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ n, 1 ≤ n → ∀ i,
      risk n i ≤ ENNReal.ofReal (K' * r n) := by
  let S : ℝ := ∑ k ∈ Finset.range N, H / r (k + 1)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ =>
    div_nonneg hH (hr (k + 1) (by omega)).le)
  refine ⟨K + S, by positivity, ?_⟩
  intro n hn i
  by_cases hN : N ≤ n
  · apply (heventual n hN hn i).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (by linarith) (hr n hn).le
  · have hterm : H / r n ≤ S := by
      have hmem : n - 1 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
      have hsum := Finset.single_le_sum
        (fun k (_ : k ∈ Finset.range N) =>
          div_nonneg hH (hr (k + 1) (by omega)).le) hmem
      simpa only [Nat.sub_add_cancel hn] using hsum
    apply (hbound n hn i).trans
    apply ENNReal.ofReal_le_ofReal
    have hmul := mul_le_mul_of_nonneg_right hterm (hr n hn).le
    rw [div_mul_cancel₀ _ (hr n hn).ne'] at hmul
    have hKS : S ≤ K + S := by linarith
    exact hmul.trans (mul_le_mul_of_nonneg_right hKS (hr n hn).le)

/-- Roadmap (C20) combines the established treated rate with an eventual
control rate, then covers the finite prefix using the clipped CATE loss. -/
-- @node: cateEstimator_uniform_rate_of_control_rate
lemma cateEstimator_uniform_rate_of_control_rate (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M)
    (K₀ : ℝ) (hK₀ : 0 < K₀) (N : ℕ)
    (hcontrol : ∀ n, N ≤ n → 1 ≤ n → ∀ P : Law d,
      CATEClass d β γ C L M κ P →
        AEMeasurable
          (fun sample : Fin n → Obs d =>
            supLoss (balancedEstimator sample (fixedLevel d n β γ) β M) P.mu1)
          (P.sample n) ∧
        lawRisk P (fun sample : Fin n → Obs d =>
          controlBalancedEstimator sample (fixedLevel d n β γ) β M) P.mu0 ≤
            ENNReal.ofReal (K₀ * rate d n β γ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ n, 1 ≤ n → ∀ P : Law d,
      CATEClass d β γ C L M κ P →
        lawRisk P (fun sample : Fin n → Obs d =>
          cateEstimator sample (fixedLevel d n β γ) β M) P.tau ≤
            ENNReal.ofReal (K * rate d n β γ) := by
  obtain ⟨K₁, hK₁, htreated⟩ := fixed_bandwidth_rate_bound d β γ C L M hparam
  let risk : ℕ → {P : Law d // CATEClass d β γ C L M κ P} → ENNReal :=
    fun n P => lawRisk P.val (fun sample : Fin n → Obs d =>
      cateEstimator sample (fixedLevel d n β γ) β M) P.val.tau
  obtain ⟨K, hK, hrate⟩ := uniformRisk_rate_of_eventual risk
    (fun n => rate d n β γ) (4 * M) (K₁ + K₀) N
    (by have := hparam.2.2.2.2.2; positivity) (by positivity)
    (by intro n hn; have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        unfold rate; positivity)
    (by intro n hn P; exact cateEstimator_lawRisk_le_four_mul _ _ _ _ _ _ _
          P.val P.property hn)
    (by
      intro n hN hn P
      obtain ⟨hmeas, hzero⟩ := hcontrol n hN hn P.val P.property
      exact cateEstimator_lawRisk_rate_of_arm_bounds P.val _ β M K₁ K₀
        (rate d n β γ) hK₁.le hK₀.le (by unfold rate; positivity)
        hmeas (htreated n hn P.val P.property.toLawClass) hzero)
  exact ⟨K, hK, fun n hn P hP => hrate n hn ⟨P, hP⟩⟩

/-- Roadmap (C18)--(C19): a control-arm logarithmic risk bound at the
rounded bandwidth implies a sharp-rate bound, with a fixed class constant. -/
-- @node: controlBalancedEstimator_rate_of_log_bound
lemma controlBalancedEstimator_rate_of_log_bound {d n : ℕ} {β γ C L M K₀ : ℝ}
    (hparam : ParameterDomain d β γ C L M) (hn : 1 ≤ n)
    (hK₀ : 0 ≤ K₀) (P : Law d)
    (hcontrol : lawRisk P (fun sample : Fin n → Obs d =>
      controlBalancedEstimator sample (fixedLevel d n β γ) β M) P.mu0 ≤
        ENNReal.ofReal (K₀ * (L * (rateBandwidth d n β γ) ^ β +
          M * Real.sqrt (Real.log (2 / rateBandwidth d n β γ) /
            ((n : ℝ) * (rateBandwidth d n β γ) ^ (d : ℝ)))))) :
    lawRisk P (fun sample : Fin n → Obs d =>
      controlBalancedEstimator sample (fixedLevel d n β γ) β M) P.mu0 ≤
        ENNReal.ofReal ((K₀ * (L + M *
          (Real.sqrt ((2 : ℝ) ^ (effectiveDimension d γ - d) /
            (effectiveDimension d γ - d)) *
            (2 : ℝ) ^ (effectiveDimension d γ / 2)))) * rate d n β γ) := by
  apply hcontrol.trans
  apply ENNReal.ofReal_le_ofReal
  have hb := rateBandwidth_bias_le hparam.1 hn hparam.2.1 hparam.2.2.1
  have hs := controlLog_rateBandwidth_le hparam.1 hn hparam.2.1 hparam.2.2.1
  have hL : 0 ≤ L := hparam.2.2.2.2.1.le
  have hM : 0 ≤ M := hparam.2.2.2.2.2.le
  have h := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hb hL)
      (mul_le_mul_of_nonneg_left hs hM)) hK₀
  simpa only [mul_add, add_mul, mul_assoc] using h

/-- The concrete logarithmic control bound (C18), together with one
measurable arm loss, now supplies the already-proved CATE assembly (C20). -/
-- @node: cateEstimator_uniform_rate_of_control_log_bound
lemma cateEstimator_uniform_rate_of_control_log_bound (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M)
    (K₀ : ℝ) (hK₀ : 0 < K₀) (N : ℕ)
    (hcontrol : ∀ n, N ≤ n → 1 ≤ n → ∀ P : Law d,
      CATEClass d β γ C L M κ P →
        AEMeasurable
          (fun sample : Fin n → Obs d =>
            supLoss (balancedEstimator sample (fixedLevel d n β γ) β M) P.mu1)
          (P.sample n) ∧
        lawRisk P (fun sample : Fin n → Obs d =>
          controlBalancedEstimator sample (fixedLevel d n β γ) β M) P.mu0 ≤
            ENNReal.ofReal (K₀ * (L * (rateBandwidth d n β γ) ^ β +
              M * Real.sqrt (Real.log (2 / rateBandwidth d n β γ) /
                ((n : ℝ) * (rateBandwidth d n β γ) ^ (d : ℝ)))))) :
    ∃ K : ℝ, 0 < K ∧ ∀ n, 1 ≤ n → ∀ P : Law d,
      CATEClass d β γ C L M κ P →
        lawRisk P (fun sample : Fin n → Obs d =>
          cateEstimator sample (fixedLevel d n β γ) β M) P.tau ≤
            ENNReal.ofReal (K * rate d n β γ) := by
  let A := Real.sqrt ((2 : ℝ) ^ (effectiveDimension d γ - d) /
    (effectiveDimension d γ - d)) * (2 : ℝ) ^ (effectiveDimension d γ / 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hL : 0 < L := hparam.2.2.2.2.1
  have hM : 0 < M := hparam.2.2.2.2.2
  apply cateEstimator_uniform_rate_of_control_rate d β γ C L M κ hparam
    (K₀ * (L + M * A)) (by positivity) N
  intro n hN hn P hP
  obtain ⟨hmeas, hbound⟩ := hcontrol n hN hn P hP
  exact ⟨hmeas, controlBalancedEstimator_rate_of_log_bound hparam hn hK₀.le P hbound⟩

/-- Roadmap (C18)--(C20): the explicit control risk bound and the treated
sharp rate yield the CATE upper bound for every positive sample size. -/
-- @node: cateEstimator_uniform_upper_rate
lemma cateEstimator_uniform_upper_rate (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M) (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ n, 1 ≤ n → ∀ P : Law d,
      CATEClass d β γ C L M κ P →
        lawRisk P (fun sample : Fin n → Obs d =>
          cateEstimator sample (fixedLevel d n β γ) β M) P.tau ≤
            ENNReal.ofReal (K * rate d n β γ) := by
  obtain ⟨K₀, hK₀, hcontrol⟩ :=
    control_balancedEstimator_log_risk d β γ C L M κ hparam hκ
  apply cateEstimator_uniform_rate_of_control_log_bound d β γ C L M κ hparam K₀ hK₀ 0
  intro n _ hn P hP
  refine ⟨(balancedEstimator_supLoss_measurable (fixedLevel d n β γ) β M P.mu1
    (holderOnCube_continuousOn hparam.2.1 hP.toLawClass.treatedHolder)).aemeasurable, ?_⟩
  simpa only [rateBandwidth, Real.rpow_natCast] using
    hcontrol n (fixedLevel d n β γ) hn P hP

-- @node: prop:cate-rate
/-- Under compatible one-sided control overlap, the clipped difference of
balanced arm fits attains the sharp CATE rate, and a zero-control subclass
gives the matching minimax lower bound. -/
theorem cate_rate (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M)
    (hκ : 0 < κ ∧ κ < 1)
    (hcompat : 1 ≤ C * (1 - κ) ^ (tailExponent γ)) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∃ N₀ : ℕ,
      (∀ n : ℕ, 1 ≤ n →
        ∀ P : Law d, CATEClass d β γ C L M κ P →
          lawRisk P
            (fun sample : Fin n → Obs d => cateEstimator sample (fixedLevel d n β γ) β M)
            P.tau ≤ ENNReal.ofReal (K * rate d n β γ)) ∧
      (∀ n : ℕ, N₀ ≤ n →
        ENNReal.ofReal (c * rate d n β γ) ≤
          zeroControlCATERisk d n β γ C L M κ) := by
  obtain ⟨K, hK, hupper⟩ :=
    cateEstimator_uniform_upper_rate d β γ C L M κ hparam hκ.1
  suffices hlower : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ENNReal.ofReal (c * rate d n β γ) ≤
        zeroControlCATERisk d n β γ C L M κ by
    obtain ⟨c, hc, N₀, hlower⟩ := hlower
    exact ⟨c, K, hc, hK, N₀, hupper, hlower⟩
  obtain ⟨δ₀, hδ₀, hδM, hclass⟩ :=
    cateLowerPair_uniform_zeroControlCATEClass d β γ C L M κ hparam hκ hcompat
  have hinfo : ∀ (n j : ℕ), 1 ≤ n →
      InformationTheory.klDiv
        ((cateLowerPair d β (tailExponent γ) (C ^ (-1 / tailExponent γ))
          (dyadicWidth j) δ₀ M true).sample n)
        ((cateLowerPair d β (tailExponent γ) (C ^ (-1 / tailExponent γ))
          (dyadicWidth j) δ₀ M false).sample n) ≤
        ENNReal.ofReal ((n : ℝ) * (dyadicWidth j) ^
          (2 * β + effectiveDimension d γ)) := by
    intro n j _hn
    rcases hparam with ⟨hd, hβ, hγ, hC, hL, hM⟩
    have hq : 0 < tailExponent γ := by unfold tailExponent; linarith
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
    have hs : 0 ≤ C ^ (-1 / tailExponent γ) :=
      (Real.rpow_pos_of_pos hCpos _).le
    have hs1 : C ^ (-1 / tailExponent γ) ≤ 1 := by
      have hsκ := cateLowerScale_compatible (tailExponent γ) C κ hq hCpos hκ.2 hcompat
      linarith [hκ.1]
    exact cateLowerPair_product_klDiv_le_unit d n β γ _ (dyadicWidth j) δ₀ M
      hd hγ hs hs1 hβ hδ₀.le (dyadicWidth_mem_Ioc j).1 (dyadicWidth_mem_Ioc j).2 hM hδM
  obtain ⟨c, hc, hlower⟩ :=
    cateLowerPair_lower_rate_of_information d β γ C L M κ δ₀ hparam hδ₀ hclass hinfo
  exact ⟨c, hc, 1, hlower⟩

end CausalSmith.Stat.GlobalTailDesignRobustCate
