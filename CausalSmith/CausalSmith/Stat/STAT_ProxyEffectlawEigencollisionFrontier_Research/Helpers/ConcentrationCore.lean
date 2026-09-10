import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ObservedLawAdapters
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ObservedMarginAssembly
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ConditionalMomentAdapters
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ModelSpectralConstruction
import Causalean.Stat.Concentration.TailBounds.Hoeffding
import Causalean.Stat.Sample.PiTransport

/-! Scalar concentration, ratio stability, and deterministic summary bounds. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set

-- @node: SummaryCoord
inductive SummaryCoord (dx dz : ℕ)
  | matrix (weighted arm : Bool) (i : Fin dz) (j : Fin dx)
  | mean (j : Fin dx)
  | arm (t : Bool)
  deriving Fintype

-- @node: summaryCoordStat
noncomputable def summaryCoordStat {dx dz : ℕ} : SummaryCoord dx dz → Obs dx dz → ℝ
  | .matrix weighted t i j => fun o =>
      if o.T = t then (if weighted then o.Y else 1) * o.Z i * o.X j else 0
  | .mean j => fun o => o.X j
  | .arm t => fun o => if o.T = t then 1 else 0

-- @node: summaryCoordScale
def summaryCoordScale {dx dz : ℕ} (L : ℝ) : SummaryCoord dx dz → ℝ
  | .matrix .. => L
  | .mean .. => L
  | .arm .. => 1

-- @node: product_hoeffding
lemma product_hoeffding {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    {f : X → ℝ} (hf : Measurable f) {a b : ℝ} (hab : a < b)
    (hbound : ∀ᵐ x ∂P, f x ∈ Set.Icc a b) (n : ℕ) (hn : 0 < n)
    {eps : ℝ} (heps : 0 ≤ eps) :
    (Measure.pi (fun _ : Fin n => P)).real
      {sample | eps ≤ |(n : ℝ)⁻¹ * ∑ i, f (sample i) - ∫ x, f x ∂P|} ≤
      2 * Real.exp (-2 * n * eps ^ 2 / (b - a) ^ 2) := by
  let S := Causalean.Stat.iidSample_infinitePi P
  let mu := Measure.infinitePi (fun _ : ℕ => P)
  let psi : (ℕ → X) → (Fin n → X) := fun w i => S.Z i w
  let E : Set (Fin n → X) :=
    {sample | eps ≤ |(n : ℝ)⁻¹ * ∑ i, f (sample i) - ∫ x, f x ∂P|}
  have hE : MeasurableSet E := by
    exact measurableSet_Ici.preimage <| (Measurable.abs <| Measurable.sub
      (Measurable.mul measurable_const
        (Finset.measurable_sum Finset.univ fun i _ => hf.comp (measurable_pi_apply i)))
      measurable_const)
  have hpsi : Measurable psi := Causalean.Stat.iidSample_finN_measurable S n
  have hpush : Measure.map psi mu = Measure.pi (fun _ : Fin n => P) :=
    Causalean.Stat.iidSample_finN_pushforward S n
  have hpre : psi ⁻¹' E =
      {w | eps ≤ |S.sampleMean f n w - ∫ x, f x ∂P|} := by
    ext w
    simp only [E, psi, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [Causalean.Stat.IIDSample.sampleMean, ← Fin.sum_univ_eq_sum_range]
  rw [← hpush, Measure.real, Measure.map_apply hpsi hE, ← Measure.real]
  rw [hpre]
  exact Causalean.Stat.Concentration.hoeffding_abs_ge S hf hab hbound n hn heps

-- @node: summaryCoordStat_measurable
lemma summaryCoordStat_measurable {dx dz : ℕ} (a : SummaryCoord dx dz) :
    Measurable (summaryCoordStat a) := by
  cases a with
  | matrix weighted t i j =>
      apply Measurable.ite
      · exact measurable_obs_T (measurableSet_singleton t)
      · cases weighted
        · have hZ : Measurable (fun o : Obs dx dz => o.Z i) :=
            (measurable_pi_apply i).comp measurable_obs_Z
          have hX : Measurable (fun o : Obs dx dz => o.X j) :=
            (measurable_pi_apply j).comp measurable_obs_X
          convert hZ.mul hX using 1 <;> ext o <;> simp
        · have hZ : Measurable (fun o : Obs dx dz => o.Z i) :=
            (measurable_pi_apply i).comp measurable_obs_Z
          have hX : Measurable (fun o : Obs dx dz => o.X j) :=
            (measurable_pi_apply j).comp measurable_obs_X
          convert (measurable_obs_Y.mul hZ).mul hX using 1 <;> ext o <;>
            simp [summaryCoordStat, mul_assoc]
      · exact measurable_const
  | mean j => exact (measurable_pi_apply j).comp measurable_obs_X
  | arm t =>
      exact Measurable.ite (measurable_obs_T (measurableSet_singleton t))
        measurable_const measurable_const

-- @node: summaryCoordStat_ae_bound
lemma summaryCoordStat_ae_bound {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (hL : 1 ≤ L) (a : SummaryCoord dx dz) :
    ∀ᵐ o ∂obsLaw P, |summaryCoordStat a o| ≤ summaryCoordScale L a := by
  change ∀ᵐ o ∂obsLaw P, |summaryCoordStat a o| ∈ Set.Iic (summaryCoordScale L a)
  rw [obsLaw, ae_map_iff (obsMap_measurable k dx dz).aemeasurable
    ((summaryCoordStat_measurable a).abs measurableSet_Iic)]
  cases a with
  | matrix weighted t i j =>
      cases weighted
      · filter_upwards [hM.boundedProxyProduct] with w hw
        by_cases ht : w.T = t
        · simpa [summaryCoordStat, summaryCoordScale, obsMap, ht, outerProduct] using
            (abs_matrix_entry_le_matrixCLM_norm (outerProduct w.Z w.X) i j).trans hw
        · simp [summaryCoordStat, summaryCoordScale, obsMap, ht, le_trans zero_le_one hL]
      · filter_upwards [hM.boundedOutcomeProxyProduct] with w hw
        by_cases ht : w.T = t
        · simpa [summaryCoordStat, summaryCoordScale, obsMap, ht, outerProduct,
            mul_assoc] using
            (abs_matrix_entry_le_matrixCLM_norm (w.Y • outerProduct w.Z w.X) i j).trans hw
        · simp [summaryCoordStat, summaryCoordScale, obsMap, ht, le_trans zero_le_one hL]
  | mean j =>
      filter_upwards [hM.boundedX] with w hw
      have hj := PiLp.norm_apply_le (WithLp.toLp 2 w.X : Euc dx) j
      have hw' : ‖(WithLp.toLp 2 w.X : Euc dx)‖ ≤ L := by
        simpa [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using hw
      simpa [summaryCoordStat, summaryCoordScale, obsMap, Real.norm_eq_abs] using hj.trans hw'
  | arm t =>
      filter_upwards [] with w
      by_cases ht : w.T = t <;> simp [summaryCoordStat, summaryCoordScale, obsMap, ht]

-- @node: summaryCoordStat_integral
lemma summaryCoordStat_integral {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (hpi : 0 < pi0) : ∀ a : SummaryCoord dx dz,
    ∫ o, summaryCoordStat a o ∂obsLaw P = match a with
      | .matrix false false i j => (obsLaw P).real (obsArm false) * (obsSummary P).M0 i j
      | .matrix false true i j => (obsLaw P).real (obsArm true) * (obsSummary P).M1 i j
      | .matrix true false i j => (obsLaw P).real (obsArm false) * (obsSummary P).N0 i j
      | .matrix true true i j => (obsLaw P).real (obsArm true) * (obsSummary P).N1 i j
      | .mean j => (obsSummary P).mX j
      | .arm t => (obsLaw P).real (obsArm t) := by
  intro a
  cases a with
  | mean j => rfl
  | arm t =>
      rw [show summaryCoordStat (.arm t) = (obsArm t).indicator (fun _ => 1) by
        funext o; by_cases ho : o.T = t <;> simp [summaryCoordStat, obsArm, ho]]
      rw [integral_indicator (measurableSet_obsArm_generic t)]
      simp [Measure.restrict_apply_univ]
  | matrix weighted t i j =>
      let f : Obs dx dz → ℝ := fun o =>
        (if weighted then o.Y else 1) * o.Z i * o.X j
      have hf : Measurable f := by
        cases weighted
        · have hZ : Measurable (fun o : Obs dx dz => o.Z i) :=
            (measurable_pi_apply i).comp measurable_obs_Z
          have hX : Measurable (fun o : Obs dx dz => o.X j) :=
            (measurable_pi_apply j).comp measurable_obs_X
          convert hZ.mul hX using 1 <;> ext o <;> simp [f]
        · have hZ : Measurable (fun o : Obs dx dz => o.Z i) :=
            (measurable_pi_apply i).comp measurable_obs_Z
          have hX : Measurable (fun o : Obs dx dz => o.X j) :=
            (measurable_pi_apply j).comp measurable_obs_X
          convert (measurable_obs_Y.mul hZ).mul hX using 1 <;> ext o <;>
            simp [f, mul_assoc]
      have hq : 0 < (obsLaw P).real (obsArm t) := by
        rw [obsLaw_real_obsArm]
        have hl := arm_mass_lower_of_latentArmPositivity P hM.latentArmPositivity t
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (by
          have hk := hM.coreDomain.1
          omega : 0 < k)
        nlinarith
      rw [show summaryCoordStat (.matrix weighted t i j) = (obsArm t).indicator f by
        funext o; by_cases ho : o.T = t <;> simp [summaryCoordStat, obsArm, f, ho]]
      rw [integral_indicator (measurableSet_obsArm_generic t)]
      have hq0 : (obsLaw P).real (obsArm t) ≠ 0 := ne_of_gt hq
      cases weighted <;> cases t <;>
        simp only [obsSummary, f, conditionalMean] <;>
        field_simp <;> simp

-- @node: summaryCoordStat_arm_sampleMean
lemma summaryCoordStat_arm_sampleMean {n dx dz : ℕ} (sample : Fin n → Obs dx dz)
    (t : Bool) :
    (n : ℝ)⁻¹ * ∑ i, summaryCoordStat (.arm t) (sample i) =
      (armCount t sample : ℝ) / n := by
  have hsum : (∑ i, summaryCoordStat (.arm t) (sample i)) =
      (armCount t sample : ℝ) := by
    rw [armCount, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ht : (sample i).T = t <;> simp [summaryCoordStat, ht]
  rw [hsum]
  simp [div_eq_mul_inv, mul_comm]

-- @node: summaryCoordStat_matrix_sampleMean
lemma summaryCoordStat_matrix_sampleMean {n dx dz : ℕ}
    (sample : Fin n → Obs dx dz) (weighted t : Bool) (a : Fin dz) (b : Fin dx) :
    (n : ℝ)⁻¹ * ∑ i, summaryCoordStat (.matrix weighted t a b) (sample i) =
      (n : ℝ)⁻¹ * ∑ i, if (sample i).T = t then
        (if weighted then (sample i).Y else 1) * (sample i).Z a * (sample i).X b else 0 := by
  rfl

-- @node: populationArmCoord
noncomputable def populationArmCoord {k dx dz : ℕ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (weighted t : Bool) (a : Fin dz) (b : Fin dx) : ℝ :=
  if weighted then observedOutcomeProxyMoment (obsSummary P) t a b
  else observedProxyMoment (obsSummary P) t a b

-- @node: empiricalArmMatrix_entry_error
lemma empiricalArmMatrix_entry_error {k dx dz n : ℕ} {L pi0 sigma0 beta : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (hL : 1 ≤ L) (hpi : 0 < pi0) (hn : 0 < n)
    (hbeta0 : 0 ≤ beta) (hbeta : beta < k * pi0 / 2)
    (sample : Fin n → Obs dx dz)
    (hdev : ∀ c : SummaryCoord dx dz,
      |(n : ℝ)⁻¹ * ∑ i, summaryCoordStat c (sample i) -
        ∫ o, summaryCoordStat c o ∂obsLaw P| < summaryCoordScale L c * beta)
    (weighted t : Bool) (a : Fin dz) (b : Fin dx) :
    |empiricalArmMatrix weighted t sample a b - populationArmCoord P weighted t a b| ≤
      4 * L * beta / (k * pi0) := by
  let q := (obsLaw P).real (obsArm t)
  let qhat := (armCount t sample : ℝ) / n
  let rhat := (n : ℝ)⁻¹ * ∑ i, summaryCoordStat (.matrix weighted t a b) (sample i)
  let M := populationArmCoord P weighted t a b
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqLower : k * pi0 ≤ q := by
    dsimp [q]
    rw [obsLaw_real_obsArm]
    exact arm_mass_lower_of_latentArmPositivity P hM.latentArmPositivity t
  have harm := hdev (.arm t)
  rw [summaryCoordStat_arm_sampleMean sample t, summaryCoordStat_integral P hM hpi (.arm t)] at harm
  simp only [summaryCoordScale] at harm
  have hqhat : k * pi0 / 2 < qhat := by
    dsimp [qhat, q] at harm ⊢
    rw [abs_lt] at harm
    linarith
  have hk0Nat : 0 < k := by
    have hk := hM.coreDomain.1
    omega
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk0Nat
  have hkpi : 0 < k * pi0 := mul_pos hk0 hpi
  have hqhat0 : 0 < qhat := lt_of_lt_of_le (half_pos hkpi) hqhat.le
  have hcount : 0 < armCount t sample := by
    by_contra hc
    have hc0 : armCount t sample = 0 := Nat.eq_zero_of_not_pos hc
    simp [qhat, hc0] at hqhat0
  have hMbound : |M| ≤ L := by
    dsimp [M, populationArmCoord]
    have henv := observedSummary_envelopes_of_model P hM.coreDomain.1 hM.coreDomain.2.1
      hL hpi hM
    cases weighted
    · exact (abs_matrix_entry_le_matrixCLM_norm _ a b).trans (henv.1 t).1
    · exact (abs_matrix_entry_le_matrixCLM_norm _ a b).trans (henv.1 t).2
  have hr := hdev (.matrix weighted t a b)
  rw [summaryCoordStat_integral P hM hpi (.matrix weighted t a b)] at hr
  have hr' : |rhat - q * M| < L * beta := by
    dsimp [rhat, q, M, populationArmCoord]
    cases weighted <;> cases t <;> simpa [summaryCoordScale,
      observedProxyMoment, observedOutcomeProxyMoment] using hr
  have hformula : empiricalArmMatrix weighted t sample a b = rhat / qhat := by
    dsimp [rhat, qhat]
    unfold empiricalArmMatrix
    have hmax : max (1 : ℝ) (armCount t sample : ℝ) = armCount t sample :=
      max_eq_right (by exact_mod_cast hcount)
    rw [hmax]
    rw [summaryCoordStat_matrix_sampleMean]
    field_simp
  rw [hformula]
  have hden : k * pi0 / 2 ≤ qhat := hqhat.le
  have hnum : |(rhat - q * M) + (q - qhat) * M| ≤ 2 * L * beta := by
    calc
      |_ + _| ≤ |rhat - q * M| + |(q - qhat) * M| := abs_add_le _ _
      _ ≤ L * beta + beta * L := by
        apply add_le_add hr'.le
        rw [abs_mul]
        have hqdev : |q - qhat| ≤ beta := by
          simpa [abs_sub_comm] using harm.le
        exact mul_le_mul hqdev hMbound (abs_nonneg _) hbeta0
      _ = 2 * L * beta := by ring
  have heq : rhat / qhat - M = ((rhat - q * M) + (q - qhat) * M) / qhat := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hqhat0]
  apply (div_le_div_of_nonneg_right hnum hqhat0.le).trans
  have hdenpos : 0 < k * pi0 / 2 := half_pos hkpi
  have hnum0 : 0 ≤ 2 * L * beta := by positivity
  calc
    2 * L * beta / qhat ≤ 2 * L * beta / (k * pi0 / 2) :=
      div_le_div_of_nonneg_left hnum0 hdenpos hden
    _ = 4 * L * beta / (k * pi0) := by field_simp; ring

-- @node: empSummary_error_of_small_deviations
lemma empSummary_error_of_small_deviations {k dx dz n : ℕ}
    {L pi0 sigma0 beta : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (hL : 1 ≤ L) (hpi : 0 < pi0) (hn : 0 < n)
    (hbeta0 : 0 ≤ beta) (hbeta : beta < k * pi0 / 2)
    (sample : Fin n → Obs dx dz)
    (hdev : ∀ c : SummaryCoord dx dz,
      |(n : ℝ)⁻¹ * ∑ i, summaryCoordStat c (sample i) -
        ∫ o, summaryCoordStat c o ∂obsLaw P| < summaryCoordScale L c * beta) :
    dS (empSummary sample) (obsSummary P) ≤
      (16 * entryNormConstant dz dx / (k * pi0) + dx) * L * beta := by
  have hk0Nat : 0 < k := by have hk := hM.coreDomain.1; omega
  have hkpi : 0 < (k : ℝ) * pi0 := mul_pos (Nat.cast_pos.mpr hk0Nat) hpi
  have hentry (weighted t : Bool) (a : Fin dz) (b : Fin dx) :=
    empiricalArmMatrix_entry_error P hM hL hpi hn hbeta0 hbeta sample hdev weighted t a b
  have hblock (weighted t : Bool) :
      ‖matrixCLM (empiricalArmMatrix weighted t sample -
        (if weighted then observedOutcomeProxyMoment (obsSummary P) t
         else observedProxyMoment (obsSummary P) t))‖ ≤
        entryNormConstant dz dx * (4 * L * beta / (k * pi0)) := by
    cases weighted
    · have hm :=
        (matrixNorm_le_entryBound
          (empiricalArmMatrix false t sample - observedProxyMoment (obsSummary P) t)
          (4 * L * beta / (k * pi0)) (by positivity) (fun a b => by
            simpa [populationArmCoord] using hentry false t a b))
      simp only [Bool.false_eq_true, ↓reduceIte]
      change ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap)
        (empiricalArmMatrix false t sample - observedProxyMoment (obsSummary P) t)‖ ≤ _
      simpa only [Matrix.l2_opNorm_def] using hm
    · have hm :=
        (matrixNorm_le_entryBound
          (empiricalArmMatrix true t sample - observedOutcomeProxyMoment (obsSummary P) t)
          (4 * L * beta / (k * pi0)) (by positivity) (fun a b => by
            simpa [populationArmCoord] using hentry true t a b))
      simp only [↓reduceIte]
      change ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap)
        (empiricalArmMatrix true t sample - observedOutcomeProxyMoment (obsSummary P) t)‖ ≤ _
      simpa only [Matrix.l2_opNorm_def] using hm
  have hmean : Real.sqrt (∑ j, ((empSummary sample).mX j - (obsSummary P).mX j) ^ 2) ≤
      (dx : ℝ) * (L * beta) := by
    have hnorm := eucNorm_le_card_mul_bound
      (WithLp.toLp 2 ((empSummary sample).mX - (obsSummary P).mX) : Euc dx)
      (L * beta) (mul_nonneg (by linarith) hbeta0) (by
        intro j
        have hj := hdev (.mean j)
        rw [summaryCoordStat_integral P hM hpi (.mean j)] at hj
        simpa [empSummary, summaryCoordStat, summaryCoordScale, Real.norm_eq_abs] using hj.le)
    simpa [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using hnorm
  unfold dS
  have h0 := hblock false false
  have h1 := hblock false true
  have h2 := hblock true false
  have h3 := hblock true true
  simp [empSummary, observedProxyMoment, observedOutcomeProxyMoment] at h0 h1 h2 h3
  simp only [empSummary] at hmean
  simp only [empSummary]
  calc
    _ ≤ 4 * (entryNormConstant dz dx * (4 * L * beta / (k * pi0))) +
        (dx : ℝ) * (L * beta) := by linarith
    _ = (16 * entryNormConstant dz dx / (k * pi0) + dx) * L * beta := by
      field_simp
      ring

-- @node: abs_fin_average_le
lemma abs_fin_average_le {n : ℕ} (hn : 0 < n) {f : Fin n → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ i, |f i| ≤ B) :
    |(n : ℝ)⁻¹ * ∑ i, f i| ≤ B := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    |(n : ℝ)⁻¹ * ∑ i, f i| = (n : ℝ)⁻¹ * |∑ i, f i| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hnR)]
    _ ≤ (n : ℝ)⁻¹ * ∑ i, |f i| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, B := by
      gcongr with i
      exact hf i
    _ = B := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

-- @node: empiricalArmMatrix_entry_bound
lemma empiricalArmMatrix_entry_bound {n dx dz : ℕ} {L : ℝ}
    (hL : 0 ≤ L) (sample : Fin n → Obs dx dz)
    (hsupport : ∀ i c, |summaryCoordStat c (sample i)| ≤ summaryCoordScale L c)
    (weighted t : Bool) (a : Fin dz) (b : Fin dx) :
    |empiricalArmMatrix weighted t sample a b| ≤ L := by
  by_cases hc : armCount t sample = 0
  · have hall : ∀ i : Fin n, (sample i).T ≠ t := by
      intro i hi
      have hmem : i ∈ Finset.univ.filter (fun j => (sample j).T = t) := by simp [hi]
      have hc' : Finset.univ.filter (fun j => (sample j).T = t) = ∅ :=
        Finset.card_eq_zero.mp (by simpa [armCount] using hc)
      rw [hc'] at hmem
      simpa using hmem
    simp [empiricalArmMatrix, hc, hall, hL]
  · have hcpos : 0 < armCount t sample := Nat.pos_of_ne_zero hc
    have hcR : (0 : ℝ) < armCount t sample := by exact_mod_cast hcpos
    unfold empiricalArmMatrix
    rw [max_eq_right (by exact_mod_cast hcpos), ← div_eq_inv_mul, abs_div, abs_of_pos hcR]
    have hsum :
        |∑ i, if (sample i).T = t then
          (if weighted then (sample i).Y else 1) * (sample i).Z a * (sample i).X b else 0| ≤
          (armCount t sample : ℝ) * L := by
      calc
        |∑ i, if (sample i).T = t then
            (if weighted then (sample i).Y else 1) * (sample i).Z a * (sample i).X b else 0| ≤
          ∑ i, |if (sample i).T = t then
            (if weighted then (sample i).Y else 1) * (sample i).Z a * (sample i).X b else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ (∑ i ∈ Finset.univ.filter (fun i => (sample i).T = t), L) := by
          rw [Finset.sum_filter]
          apply Finset.sum_le_sum
          intro i hi
          by_cases hit : (sample i).T = t
          · simpa [hit, summaryCoordStat, summaryCoordScale] using
              hsupport i (.matrix weighted t a b)
          · simp [hit, hL]
        _ = (armCount t sample : ℝ) * L := by
          simp [armCount]
    rw [div_le_iff₀ hcR]
    simpa [mul_comm] using hsum

-- @node: empSummary_error_on_support
lemma empSummary_error_on_support {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (hL : 1 ≤ L) (hpi : 0 < pi0) (hn : 0 < n)
    (sample : Fin n → Obs dx dz)
    (hsupport : ∀ i c, |summaryCoordStat c (sample i)| ≤ summaryCoordScale L c) :
    dS (empSummary sample) (obsSummary P) ≤
      (4 * (entryNormConstant dz dx + 1) + dx + 1) * L := by
  have henv := observedSummary_envelopes_of_model P hM.coreDomain.1 hM.coreDomain.2.1
    hL hpi hM
  have hempBlock (weighted t : Bool) :
      ‖matrixCLM (empiricalArmMatrix weighted t sample)‖ ≤
        entryNormConstant dz dx * L := by
    have hm := matrixNorm_le_entryBound (empiricalArmMatrix weighted t sample) L
      (by linarith) (fun a b => empiricalArmMatrix_entry_bound (by linarith) sample
        hsupport weighted t a b)
    change ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap)
      (empiricalArmMatrix weighted t sample)‖ ≤ _
    simpa only [Matrix.l2_opNorm_def] using hm
  have hdiff (weighted t : Bool) :
      ‖matrixCLM (empiricalArmMatrix weighted t sample -
        (if weighted then observedOutcomeProxyMoment (obsSummary P) t
         else observedProxyMoment (obsSummary P) t))‖ ≤
        (entryNormConstant dz dx + 1) * L := by
    have heq : matrixCLM (empiricalArmMatrix weighted t sample -
        (if weighted then observedOutcomeProxyMoment (obsSummary P) t
         else observedProxyMoment (obsSummary P) t)) =
        matrixCLM (empiricalArmMatrix weighted t sample) -
          matrixCLM (if weighted then observedOutcomeProxyMoment (obsSummary P) t
            else observedProxyMoment (obsSummary P) t) := by
      ext x i
      simp [matrixCLM, Matrix.toEuclideanLin_apply]
    rw [heq]
    apply (norm_sub_le _ _).trans
    calc
      ‖matrixCLM (empiricalArmMatrix weighted t sample)‖ +
          ‖matrixCLM (if weighted then observedOutcomeProxyMoment (obsSummary P) t
            else observedProxyMoment (obsSummary P) t)‖ ≤
          entryNormConstant dz dx * L + L := by
        gcongr
        · exact hempBlock weighted t
        · cases weighted
          · exact (henv.1 t).1
          · exact (henv.1 t).2
      _ = _ := by ring
  have hempMeanCoord (j : Fin dx) : |(empSummary sample).mX j| ≤ L := by
    simpa [empSummary, summaryCoordStat, summaryCoordScale] using
      abs_fin_average_le hn (le_trans zero_le_one hL) (fun i => hsupport i (.mean j))
  have hempMean : ‖(WithLp.toLp 2 (empSummary sample).mX : Euc dx)‖ ≤ (dx : ℝ) * L :=
    eucNorm_le_card_mul_bound _ L (by linarith) (by
      intro j
      simpa [Real.norm_eq_abs] using hempMeanCoord j)
  have hmeanDiff : ‖(WithLp.toLp 2 ((empSummary sample).mX - (obsSummary P).mX) : Euc dx)‖ ≤
      ((dx : ℝ) + 1) * L := by
    calc
      _ ≤ ‖(WithLp.toLp 2 (empSummary sample).mX : Euc dx)‖ +
          ‖(WithLp.toLp 2 (obsSummary P).mX : Euc dx)‖ := norm_sub_le _ _
      _ ≤ (dx : ℝ) * L + L := add_le_add hempMean henv.2
      _ = _ := by ring
  have hmeanDiff' :
      Real.sqrt (∑ i, ((empSummary sample).mX i - (obsSummary P).mX i) ^ 2) ≤
        ((dx : ℝ) + 1) * L := by
    simpa [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using hmeanDiff
  unfold dS
  have h0 := hdiff false false
  have h1 := hdiff false true
  have h2 := hdiff true false
  have h3 := hdiff true true
  simp only [Bool.false_eq_true, ↓reduceIte, ge_iff_le] at h0 h1 h2 h3
  have h0' : ‖matrixCLM (empiricalArmMatrix false false sample - (obsSummary P).M0)‖ ≤
      (entryNormConstant dz dx + 1) * L := by simpa [observedProxyMoment] using h0
  have h1' : ‖matrixCLM (empiricalArmMatrix false true sample - (obsSummary P).M1)‖ ≤
      (entryNormConstant dz dx + 1) * L := by simpa [observedProxyMoment] using h1
  have h2' : ‖matrixCLM (empiricalArmMatrix true false sample - (obsSummary P).N0)‖ ≤
      (entryNormConstant dz dx + 1) * L := by simpa [observedOutcomeProxyMoment] using h2
  have h3' : ‖matrixCLM (empiricalArmMatrix true true sample - (obsSummary P).N1)‖ ≤
      (entryNormConstant dz dx + 1) * L := by simpa [observedOutcomeProxyMoment] using h3
  simp only [empSummary] at hmeanDiff'
  simp only [empSummary]
  calc
    _ ≤ 4 * ((entryNormConstant dz dx + 1) * L) + ((dx : ℝ) + 1) * L := by
      linarith [hmeanDiff', h0', h1', h2', h3']
    _ = (4 * (entryNormConstant dz dx + 1) + dx + 1) * L := by ring

-- @node: measurableSet_summaryCoordSupport
lemma measurableSet_summaryCoordSupport {dx dz : ℕ} (L : ℝ) :
    MeasurableSet {o : Obs dx dz | ∀ c : SummaryCoord dx dz,
      |summaryCoordStat c o| ≤ summaryCoordScale L c} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun c =>
    measurableSet_Iic.preimage (summaryCoordStat_measurable c).abs

-- @node: sample_summaryCoordSupport_ae
lemma sample_summaryCoordSupport_ae {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (hL : 1 ≤ L) :
    ∀ᵐ sample ∂sampleLaw (n := n) P, ∀ i c,
      |summaryCoordStat c (sample i)| ≤ summaryCoordScale L c := by
  let G : Set (Obs dx dz) := {o | ∀ c : SummaryCoord dx dz,
    |summaryCoordStat c o| ≤ summaryCoordScale L c}
  have hGmeas : MeasurableSet G := measurableSet_summaryCoordSupport L
  have hGae : ∀ᵐ o ∂obsLaw P, o ∈ G := by
    change ∀ᵐ o ∂obsLaw P, ∀ c : SummaryCoord dx dz,
      |summaryCoordStat c o| ≤ summaryCoordScale L c
    rw [ae_all_iff]
    exact fun c => summaryCoordStat_ae_bound P hM hL c
  have hGone : obsLaw P G = 1 := (mem_ae_iff_prob_eq_one hGmeas).mp hGae
  have hset : {sample : Fin n → Obs dx dz | ∀ i c,
      |summaryCoordStat c (sample i)| ≤ summaryCoordScale L c} =
      Set.pi Set.univ (fun _ => G) := by
    ext sample
    simp [G]
  rw [show (∀ᵐ sample ∂sampleLaw (n := n) P, ∀ i c,
      |summaryCoordStat c (sample i)| ≤ summaryCoordScale L c) ↔
      {sample : Fin n → Obs dx dz | ∀ i c,
        |summaryCoordStat c (sample i)| ≤ summaryCoordScale L c} ∈
          ae (sampleLaw (n := n) P) by rfl]
  have hPiMeas : MeasurableSet (Set.pi (Set.univ : Set (Fin n)) (fun _ => G)) :=
    (measurableSet_pi Set.countable_univ).2 (Or.inl fun _ _ => hGmeas)
  rw [hset, mem_ae_iff_prob_eq_one hPiMeas]
  rw [sampleLaw, Measure.pi_pi]
  simp [hGone]

-- @node: summaryCoord_deviation_probability
lemma summaryCoord_deviation_probability {k dx dz n : ℕ} {L pi0 sigma0 C eta : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (hL : 1 ≤ L) (hn : 0 < n) (heta : 0 < eta) (hetaUpper : eta < 1)
    (hC : 1 ≤ C)
    (c : SummaryCoord dx dz) :
    (sampleLaw (n := n) P).real
      {sample | summaryCoordScale L c *
          (2 * Real.sqrt (Real.log (C / eta) / n)) ≤
        |(n : ℝ)⁻¹ * ∑ i, summaryCoordStat c (sample i) -
          ∫ o, summaryCoordStat c o ∂obsLaw P|} ≤
      2 * (eta / C) ^ 2 := by
  have hscale : 0 < summaryCoordScale L c := by
    cases c <;> simp [summaryCoordScale] <;> linarith
  have hratio : 1 < C / eta := by
    apply (lt_div_iff₀ heta).2
    nlinarith [hetaUpper]
  have hlog : 0 < Real.log (C / eta) := Real.log_pos hratio
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 ≤ Real.sqrt (Real.log (C / eta) / n) := Real.sqrt_nonneg _
  have hbound : ∀ᵐ o ∂obsLaw P, summaryCoordStat c o ∈
      Set.Icc (-summaryCoordScale L c) (summaryCoordScale L c) := by
    filter_upwards [summaryCoordStat_ae_bound P hM hL c] with o ho
    rw [Set.mem_Icc]
    exact (abs_le.mp ho)
  have hH := product_hoeffding (obsLaw P) (summaryCoordStat_measurable c)
    (neg_lt_self hscale) hbound n hn
    (eps := summaryCoordScale L c *
      (2 * Real.sqrt (Real.log (C / eta) / n)))
    (mul_nonneg hscale.le (mul_nonneg (by norm_num) hsqrt))
  rw [sampleLaw]
  apply hH.trans_eq
  have hsqrtSq : (Real.sqrt (Real.log (C / eta) / n)) ^ 2 =
      Real.log (C / eta) / n := Real.sq_sqrt (div_nonneg hlog.le hnR.le)
  rw [show -2 * (n : ℝ) *
      (summaryCoordScale L c * (2 * Real.sqrt (Real.log (C / eta) / n))) ^ 2 /
        (summaryCoordScale L c - -summaryCoordScale L c) ^ 2 =
      -2 * Real.log (C / eta) by
    rw [mul_pow]
    rw [show (2 * Real.sqrt (Real.log (C / eta) / (n : ℝ))) ^ 2 =
      4 * (Real.sqrt (Real.log (C / eta) / (n : ℝ))) ^ 2 by ring, hsqrtSq]
    field_simp
    ring]
  rw [show -2 * Real.log (C / eta) =
      -Real.log (C / eta) + -Real.log (C / eta) by ring,
    Real.exp_add, Real.exp_neg, Real.exp_log (lt_trans zero_lt_one hratio)]
  field_simp


end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

