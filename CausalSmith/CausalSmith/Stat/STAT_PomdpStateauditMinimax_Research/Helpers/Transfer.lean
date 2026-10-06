module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.CollisionTV
public import Causalean.Stat.Minimax.LeCam
public import Causalean.Stat.Minimax.LIntegralRisk

/-! # Transfer of unaudited two-point testing bounds to every audited estimator. -/

public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory
open scoped ENNReal

-- @node: permutationMixture_sqRisk_exists_atom
/-- A finite uniform mixture cannot have larger extended squared risk than every
one of its fixed-permutation atoms. -/
lemma permutationMixture_sqRisk_exists_atom {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m) (eta : ℝ)
    (est : AuditedRecord T 1 (n * m) k → ℝ) (theta : ℝ) :
    ∃ π : Fin n × Fin m ≃ Fin (n * m),
      Causalean.Stat.sqRiskLIntegral (permutationMixture M hm eta) est theta ≤
        Causalean.Stat.sqRiskLIntegral
          (auditedLaw eta (cloneModel M hm π)) est theta := by
  letI : Nonempty (Fin n × Fin m ≃ Fin (n * m)) := ⟨finProdFinEquiv⟩
  let c : ℝ≥0∞ := ENNReal.ofReal
    (1 / (Fintype.card (Fin n × Fin m ≃ Fin (n * m)) : ℝ))
  obtain ⟨π, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun π : Fin n × Fin m ≃ Fin (n * m) =>
      Causalean.Stat.sqRiskLIntegral
        (auditedLaw eta (cloneModel M hm π)) est theta) Finset.univ_nonempty
  refine ⟨π, ?_⟩
  have hc : c * (Fintype.card (Fin n × Fin m ≃ Fin (n * m)) : ℝ≥0∞) = 1 := by
    dsimp [c]
    rw [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast
      (Fintype.card_pos : 0 < Fintype.card (Fin n × Fin m ≃ Fin (n * m)))),
      ENNReal.ofReal_natCast]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.ne_of_gt
      (Fintype.card_pos : 0 < Fintype.card (Fin n × Fin m ≃ Fin (n * m)))))
      (by simp)
  have hsum :
      (∑ σ : Fin n × Fin m ≃ Fin (n * m),
        c * Causalean.Stat.sqRiskLIntegral
          (auditedLaw eta (cloneModel M hm σ)) est theta) ≤
      ∑ _σ : Fin n × Fin m ≃ Fin (n * m),
        c * Causalean.Stat.sqRiskLIntegral
          (auditedLaw eta (cloneModel M hm π)) est theta := by
    apply Finset.sum_le_sum
    intro σ hσ
    exact mul_le_mul_of_nonneg_left (hmax σ hσ) bot_le
  calc
    Causalean.Stat.sqRiskLIntegral (permutationMixture M hm eta) est theta =
        ∑ σ : Fin n × Fin m ≃ Fin (n * m),
          c * Causalean.Stat.sqRiskLIntegral
            (auditedLaw eta (cloneModel M hm σ)) est theta := by
      simp only [Causalean.Stat.sqRiskLIntegral, permutationMixture,
        lintegral_finsetSum_measure, lintegral_smul_measure, smul_eq_mul, c]
    _ ≤ _ := hsum
    _ = Causalean.Stat.sqRiskLIntegral
          (auditedLaw eta (cloneModel M hm π)) est theta := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc
        (Fintype.card (Fin n × Fin m ≃ Fin (n * m)) : ℝ≥0∞) *
            (c * Causalean.Stat.sqRiskLIntegral
              (auditedLaw eta (cloneModel M hm π)) est theta) =
          (c * (Fintype.card (Fin n × Fin m ≃ Fin (n * m)) : ℝ≥0∞)) *
            Causalean.Stat.sqRiskLIntegral
              (auditedLaw eta (cloneModel M hm π)) est theta := by ac_rfl
        _ = _ := by rw [hc, one_mul]

-- @node: twoPoint_sqRiskLIntegral_tv
/-- Testing the sign of a real estimator gives the exact two-point squared-risk
lower bound in terms of total variation, including infinite risks. -/
lemma twoPoint_sqRiskLIntegral_tv {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (a : ℝ) (ha : 0 ≤ a) (est : Ω → ℝ) (hest : Measurable est) :
    ENNReal.ofReal ((a ^ 2 / 2) * (1 - Causalean.Stat.tvDist P Q)) ≤
      max (Causalean.Stat.sqRiskLIntegral P est a)
        (Causalean.Stat.sqRiskLIntegral Q est (-a)) := by
  let A : Set Ω := {z | est z < 0}
  have hA : MeasurableSet A := measurableSet_lt hest measurable_const
  have htest := Causalean.Stat.one_sub_tvDist_le_test (μ := P) (ν := Q) hA
  have htest_en : ENNReal.ofReal (1 - Causalean.Stat.tvDist P Q) ≤ P A + Q Aᶜ := by
    have h := ENNReal.ofReal_le_ofReal htest
    rw [ENNReal.ofReal_add measureReal_nonneg (measureReal_nonneg : 0 ≤ Q.real Aᶜ)] at h
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top P A),
      ENNReal.ofReal_toReal (measure_ne_top Q Aᶜ)] using h
  have hP : ENNReal.ofReal (a ^ 2) * P A ≤
      Causalean.Stat.sqRiskLIntegral P est a := by
    unfold Causalean.Stat.sqRiskLIntegral
    calc
      ENNReal.ofReal (a ^ 2) * P A =
          ∫⁻ _z in A, ENNReal.ofReal (a ^ 2) ∂P := (setLIntegral_const _ _).symm
      _ = ∫⁻ z, A.indicator (fun _ => ENNReal.ofReal (a ^ 2)) z ∂P :=
        (lintegral_indicator hA _).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal ((est z - a) ^ 2) ∂P := by
        apply lintegral_mono
        intro z
        by_cases hz : z ∈ A
        · rw [Set.indicator_of_mem hz]
          apply ENNReal.ofReal_le_ofReal
          have : est z < 0 := hz
          nlinarith
        · rw [Set.indicator_of_notMem hz]
          exact bot_le
  have hQ : ENNReal.ofReal (a ^ 2) * Q Aᶜ ≤
      Causalean.Stat.sqRiskLIntegral Q est (-a) := by
    unfold Causalean.Stat.sqRiskLIntegral
    calc
      ENNReal.ofReal (a ^ 2) * Q Aᶜ =
          ∫⁻ _z in Aᶜ, ENNReal.ofReal (a ^ 2) ∂Q := (setLIntegral_const _ _).symm
      _ = ∫⁻ z, Aᶜ.indicator (fun _ => ENNReal.ofReal (a ^ 2)) z ∂Q :=
        (lintegral_indicator hA.compl _).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal ((est z - -a) ^ 2) ∂Q := by
        apply lintegral_mono
        intro z
        by_cases hz : z ∈ Aᶜ
        · rw [Set.indicator_of_mem hz]
          apply ENNReal.ofReal_le_ofReal
          have : 0 ≤ est z := le_of_not_gt hz
          nlinarith
        · rw [Set.indicator_of_notMem hz]
          exact bot_le
  have hsum : ENNReal.ofReal (a ^ 2) * (P A + Q Aᶜ) ≤
      Causalean.Stat.sqRiskLIntegral P est a +
        Causalean.Stat.sqRiskLIntegral Q est (-a) := by
    rw [mul_add]
    exact add_le_add hP hQ
  have hmax : Causalean.Stat.sqRiskLIntegral P est a +
        Causalean.Stat.sqRiskLIntegral Q est (-a) ≤
      2 * max (Causalean.Stat.sqRiskLIntegral P est a)
        (Causalean.Stat.sqRiskLIntegral Q est (-a)) := by
    calc
      _ ≤ max (Causalean.Stat.sqRiskLIntegral P est a)
          (Causalean.Stat.sqRiskLIntegral Q est (-a)) +
        max (Causalean.Stat.sqRiskLIntegral P est a)
          (Causalean.Stat.sqRiskLIntegral Q est (-a)) :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = _ := by ring
  have htv : ENNReal.ofReal (a ^ 2) *
      ENNReal.ofReal (1 - Causalean.Stat.tvDist P Q) ≤
      2 * max (Causalean.Stat.sqRiskLIntegral P est a)
        (Causalean.Stat.sqRiskLIntegral Q est (-a)) :=
    (mul_le_mul_of_nonneg_left htest_en bot_le).trans (hsum.trans hmax)
  have hnonneg : 0 ≤ 1 - Causalean.Stat.tvDist P Q := by
    linarith [Causalean.Stat.tvDist_le_one (μ := P) (ν := Q)]
  rw [← ENNReal.ofReal_mul (by positivity)] at htv
  have hcoef : ENNReal.ofReal ((a ^ 2 / 2) * (1 - Causalean.Stat.tvDist P Q)) =
      (ENNReal.ofReal (a ^ 2 * (1 - Causalean.Stat.tvDist P Q))) / 2 := by
    have heq : (a ^ 2 / 2) * (1 - Causalean.Stat.tvDist P Q) =
        (a ^ 2 * (1 - Causalean.Stat.tvDist P Q)) / 2 := by ring
    rw [heq]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hcoef]
  exact (ENNReal.div_le_iff_le_mul (by norm_num) (by norm_num)).2 (by simpa [mul_comm] using htv)

-- @node: audited_tv_triangle
/-- Triangle inequality for testing total variation of probability laws. -/
lemma audited_tv_triangle {Ω : Type*} [MeasurableSpace Ω]
    (P Q R : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    Causalean.Stat.tvDist P R ≤
      Causalean.Stat.tvDist P Q + Causalean.Stat.tvDist Q R := by
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  intro A
  have hPQ := Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := P) (ν := Q) A.2
  have hQR := Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := Q) (ν := R) A.2
  exact (abs_sub_le _ _ _).trans (add_le_add hPQ hQR)

-- @node: clone_mixture_tv_transfer_bounds
/-- The common fresh-label channel and both collision losses bound the testing
distance between the two fixed-permutation mixtures. -/
lemma clone_mixture_tv_transfer_bounds {T n k m : Nat} {t0 zeta C : ℝ}
    (Mp Mm : PomdpModel T 1 n k) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hMp : FixedOverlapClass t0 zeta C Mp)
    (hMm : FixedOverlapClass t0 zeta C Mm)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    Causalean.Stat.tvDist (permutationMixture Mp hm eta)
      (permutationMixture Mm hm eta) ≤
      Causalean.Stat.tvDist (obsLaw Mp) (obsLaw Mm) +
        2 * collisionEnvelope T eta m ∧
    Causalean.Stat.tvDist (permutationMixture Mp hm eta)
      (permutationMixture Mm hm eta) ≤
      Causalean.Stat.tvDist (obsLaw Mp) (obsLaw Mm) +
        eta ^ 2 * T * (T - 1) / (m : ℝ) := by
  have hp := overflow_safe_fixed_permutation_tv Mp hn hm hMp.1.pomdp
    hMp.1.randomization hMp.1.start eta ⟨heta, rfl⟩ auditRecord_atomic_labels
  have hm' := overflow_safe_fixed_permutation_tv Mm hn hm hMm.1.pomdp
    hMm.1.randomization hMm.1.start eta ⟨heta, rfl⟩ auditRecord_atomic_labels
  letI : IsProbabilityMeasure (permutationMixture Mp hm eta) :=
    permutationMixture_prob Mp hm eta heta
  letI : IsProbabilityMeasure (permutationMixture Mm hm eta) :=
    permutationMixture_prob Mm hm eta heta
  letI : IsProbabilityMeasure (obsLaw Mp) :=
    Measure.isProbabilityMeasure_map (by unfold obsProj currentState actionAt rewardAt; fun_prop)
  letI : IsProbabilityMeasure (obsLaw Mm) :=
    Measure.isProbabilityMeasure_map (by unfold obsProj currentState actionAt rewardAt; fun_prop)
  letI : IsMarkovKernel (freshKernel (T := T) (k := k) hn hm eta) :=
    freshKernel_markov hn hm eta heta
  letI : IsProbabilityMeasure (freshLabelLaw Mp hn hm eta) := by
    unfold freshLabelLaw
    infer_instance
  letI : IsProbabilityMeasure (freshLabelLaw Mm hn hm eta) := by
    unfold freshLabelLaw
    infer_instance
  have htriangle := audited_tv_triangle
    (permutationMixture Mp hm eta) (freshLabelLaw Mp hn hm eta)
    (permutationMixture Mm hm eta)
  have htriangle' := audited_tv_triangle
    (freshLabelLaw Mp hn hm eta) (freshLabelLaw Mm hn hm eta)
    (permutationMixture Mm hm eta)
  rw [Causalean.Stat.tvDist_symm (freshLabelLaw Mm hn hm eta)
      (permutationMixture Mm hm eta)] at htriangle'
  have hbase := freshLabelLaw_tv_eq_obsLaw Mp Mm hn hm eta heta
  have hfirst : Causalean.Stat.tvDist (permutationMixture Mp hm eta)
      (permutationMixture Mm hm eta) ≤
      Causalean.Stat.tvDist (obsLaw Mp) (obsLaw Mm) +
        2 * collisionEnvelope T eta m := by
    have hp' := hp.2.2.2.2.2.1
    have hm'' := hm'.2.2.2.2.2.1
    calc
      _ ≤ Causalean.Stat.tvDist (permutationMixture Mp hm eta)
            (freshLabelLaw Mp hn hm eta) +
          Causalean.Stat.tvDist (freshLabelLaw Mp hn hm eta)
            (permutationMixture Mm hm eta) := htriangle
      _ ≤ Causalean.Stat.tvDist (permutationMixture Mp hm eta)
            (freshLabelLaw Mp hn hm eta) +
          Causalean.Stat.tvDist (freshLabelLaw Mp hn hm eta)
            (freshLabelLaw Mm hn hm eta) +
          Causalean.Stat.tvDist (permutationMixture Mm hm eta)
            (freshLabelLaw Mm hn hm eta) := by linarith
      _ ≤ _ := by rw [hbase]; linarith
  refine ⟨hfirst, ?_⟩
  have hbound := hp.2.2.2.2.1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hscaled : 2 * collisionEnvelope T eta m ≤
      eta ^ 2 * T * (T - 1) / (m : ℝ) := by
    calc
      _ ≤ 2 * (eta ^ 2 * T * (T - 1) / (2 * m : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = _ := by field_simp
  calc
    _ ≤ Causalean.Stat.tvDist (obsLaw Mp) (obsLaw Mm) +
        2 * collisionEnvelope T eta m := hfirst
    _ ≤ _ := by simpa [add_comm] using
      (add_le_add_left hscaled (Causalean.Stat.tvDist (obsLaw Mp) (obsLaw Mm)))

-- @node: lem:overflow-safe-all-procedure-transfer
/-- The common fresh-label kernel transfers the observed-path testing distance to
fixed-permutation audited mixtures, and a mixture lower bound has a legal fixed atom
witness for every measurable audited estimator. -/
lemma overflow_safe_all_procedure_transfer {T n k m : Nat} {t0 zeta C : ℝ}
    (Mp Mm : PomdpModel T 1 n k) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hC : 1 ≤ C)
    (hMp : FixedOverlapClass t0 zeta C Mp)
    (hMm : FixedOverlapClass t0 zeta C Mm)
    (hpol : Mp.b = Mm.b ∧ Mp.e = Mm.e)
    (eta a : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) (ha : 0 ≤ a)
    (hplus : targetValue Mp = a) (hminus : targetValue Mm = -a) :
    (Causalean.Stat.tvDist (permutationMixture Mp hm eta)
      (permutationMixture Mm hm eta) ≤
      Causalean.Stat.tvDist (obsLaw Mp) (obsLaw Mm) +
        2 * collisionEnvelope T eta m) ∧
    (Causalean.Stat.tvDist (permutationMixture Mp hm eta)
      (permutationMixture Mm hm eta) ≤
      Causalean.Stat.tvDist (obsLaw Mp) (obsLaw Mm) +
        eta ^ 2 * T * (T - 1) / (m : ℝ)) ∧
    (∀ est : AuditedRecord T 1 (n * m) k → ℝ, Measurable est →
      ∃ (v : Bool) (π : Fin n × Fin m ≃ Fin (n * m)),
        FixedOverlapClass t0 zeta C
          (cloneModel (if v then Mp else Mm) hm π) ∧
        ENNReal.ofReal ((a ^ 2 / 2) *
          (1 - Causalean.Stat.tvDist (permutationMixture Mp hm eta)
            (permutationMixture Mm hm eta))) ≤
          Causalean.Stat.sqRiskLIntegral
            (auditedLaw eta (cloneModel (if v then Mp else Mm) hm π)) est
            (targetValue (cloneModel (if v then Mp else Mm) hm π))) := by
  have htv := clone_mixture_tv_transfer_bounds Mp Mm hn hm hMp hMm eta heta
  refine ⟨htv.1, htv.2, ?_⟩
  intro est hest
  letI : IsProbabilityMeasure (permutationMixture Mp hm eta) :=
    permutationMixture_prob Mp hm eta heta
  letI : IsProbabilityMeasure (permutationMixture Mm hm eta) :=
    permutationMixture_prob Mm hm eta heta
  have htwo := twoPoint_sqRiskLIntegral_tv
    (permutationMixture Mp hm eta) (permutationMixture Mm hm eta) a ha est hest
  rcases le_max_iff.mp htwo with hplusRisk | hminusRisk
  · obtain ⟨π, hπ⟩ := permutationMixture_sqRisk_exists_atom Mp hm eta est a
    have hclone := clone_preservation Mp hMp.1.t0_pos hn hm π hMp
    refine ⟨true, π, by simpa using hclone.1, ?_⟩
    simpa [hclone.2.1, hplus] using hplusRisk.trans hπ
  · obtain ⟨π, hπ⟩ := permutationMixture_sqRisk_exists_atom Mm hm eta est (-a)
    have hclone := clone_preservation Mm hMm.1.t0_pos hn hm π hMm
    refine ⟨false, π, by simpa using hclone.1, ?_⟩
    simpa [hclone.2.1, hminus] using hminusRisk.trans hπ

end CausalSmith.Stat.PomdpStateauditMinimax
