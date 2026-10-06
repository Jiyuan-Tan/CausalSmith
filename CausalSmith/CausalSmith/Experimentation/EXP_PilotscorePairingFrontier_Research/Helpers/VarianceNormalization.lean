module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Basic
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.BindIntegral
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.OracleSpacing
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.VarianceAdaptiveResidual
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.VarianceAdaptiveResidualPaper
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.VarianceSuperpopulation
public import Causalean.Experimentation.MatchedPairDesign.Variance

/-! # Paired estimator variance normalization -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

variable {d m N : ℕ} {β L cX CX cg Cg h c0 c1 C1 C2 : ℝ}

open MeasureTheory
open scoped BigOperators ENNReal

private lemma matchingDesign_aemeasurable_of_ae_domain
    (P : Measure (UnitRecord d)) (D : Design m N d)
    (hD : MatchingDesignClass D)
    (hdom : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      designInput w ∈ designDomain m N d) :
    AEMeasurable (fun w : WaveInput m N d => D (designInput w))
      (latentTwoWaveLaw (m := m) (N := N) P) := by
  have hdesign_meas : MeasurableSet (designDomain m N d) := by
    unfold designDomain cube
    measurability
  have hinput_meas : Measurable (designInput (m := m) (N := N) (d := d)) := by
    unfold designInput
    fun_prop
  have hmap_ae : ∀ᵐ v ∂(latentTwoWaveLaw (m := m) (N := N) P).map designInput,
      v ∈ designDomain m N d :=
    (ae_map_iff hinput_meas.aemeasurable hdesign_meas).2 hdom
  have hDmap : AEMeasurable D
      ((latentTwoWaveLaw (m := m) (N := N) P).map designInput) := by
    rw [← Measure.restrict_eq_self_of_ae_mem hmap_ae]
    exact aemeasurable_restrict_of_measurable_subtype hdesign_meas hD.2.1
  exact hDmap.comp_measurable hinput_meas

private lemma pairedExperimentKernel_measurable :
    Measurable (fun p : WaveInput m N d × Match N =>
      (pairedCoinLaw p.2).map (fun z => (p.1, z))) := by
  classical
  let c : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-(N : ℝ) / 2))
  have hterm (z : Fin N → Bool) : Measurable
      (fun p : WaveInput m N d × Match N =>
        if paired p.2 z then c • Measure.dirac (p.1, z) else 0) := by
    apply Measurable.ite
    · exact measurable_snd
        (MeasurableSet.of_discrete : MeasurableSet {M : Match N | paired M z})
    · have hp : Measurable (fun p : WaveInput m N d × Match N => (p.1, z)) :=
        Measurable.prod measurable_fst measurable_const
      have hd : Measurable (fun p : WaveInput m N d × Match N =>
          Measure.dirac (p.1, z)) := Measure.measurable_dirac.comp hp
      apply Measure.measurable_of_measurable_coe
      intro s hs
      simp only [Measure.smul_apply, smul_eq_mul]
      exact measurable_const.mul ((Measure.measurable_coe hs).comp hd)
    · exact measurable_const
  have hrhs : Measurable (fun p : WaveInput m N d × Match N =>
      ∑ z : Fin N → Bool,
        if paired p.2 z then c • Measure.dirac (p.1, z) else 0) :=
    Finset.measurable_fun_sum Finset.univ (fun z _ => hterm z)
  convert hrhs using 1
  funext p
  unfold pairedCoinLaw
  rw [Measure.map_finset_sum']
  · apply Finset.sum_congr rfl
    intro z _
    by_cases hz : paired p.2 z
    · simp only [hz, if_true, Measure.map_smul]
      congr 1
      apply Measure.ext
      intro s hs
      rw [Measure.map_apply (by fun_prop) hs]
      have hp : Measurable (fun z : Fin N → Bool => (p.1, z)) :=
        Measurable.prod measurable_const measurable_id
      simp only [Measure.dirac_apply' _ (hs.preimage hp),
        Measure.dirac_apply' _ hs]
      rfl
    · simp [hz]
  · fun_prop

private lemma pairedExperimentKernel_aemeasurable
    (P : Measure (UnitRecord d)) (D : Design m N d)
    (hM : AEMeasurable (fun w : WaveInput m N d => D (designInput w))
      (latentTwoWaveLaw (m := m) (N := N) P)) :
    AEMeasurable (fun w : WaveInput m N d =>
      (pairedCoinLaw (D (designInput w))).map (fun z => (w, z)))
      (latentTwoWaveLaw (m := m) (N := N) P) := by
  exact pairedExperimentKernel_measurable.comp_aemeasurable
    (measurable_id.aemeasurable.prodMk hM)

private lemma integral_experimentLaw_eq_iterated
    (P : Measure (UnitRecord d)) (D : Design m N d)
    (f : WaveInput m N d × (Fin N → Bool) → ℝ)
    (hM : AEMeasurable (fun w : WaveInput m N d => D (designInput w))
      (latentTwoWaveLaw (m := m) (N := N) P))
    (hf : Integrable f (experimentLaw (m := m) (N := N) P
      (fun w => pairedCoinLaw (D (designInput w))))) :
    (∫ wz, f wz ∂experimentLaw (m := m) (N := N) P
      (fun w => pairedCoinLaw (D (designInput w)))) =
      ∫ w, ∫ z, f (w, z) ∂pairedCoinLaw (D (designInput w))
        ∂latentTwoWaveLaw (m := m) (N := N) P := by
  unfold experimentLaw
  let κ : WaveInput m N d → Measure (WaveInput m N d × (Fin N → Bool)) :=
    fun w => (pairedCoinLaw (D (designInput w))).map (fun z => (w, z))
  have hκ : AEMeasurable κ (latentTwoWaveLaw (m := m) (N := N) P) :=
    pairedExperimentKernel_aemeasurable P D hM
  rw [integral_bind_real _ κ f hκ hf]
  apply integral_congr_ae
  have hsection : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      AEMeasurable f (κ w) := hκ.ae_of_bind hf.aemeasurable
  filter_upwards [hsection] with w hw
  exact integral_map (by fun_prop) hw.aestronglyMeasurable

private abbrev PairRep (M : Match N) := {i : Fin N // i < M.val i}

private def pairRepPosition (M : Match N) : PairRep M × Bool → Fin N :=
  fun p => if p.2 then M.val p.1.val else p.1.val

private lemma pairRepPosition_bijective (M : Match N) :
    Function.Bijective (pairRepPosition M) := by
  constructor
  · rintro ⟨a, u⟩ ⟨b, v⟩ huv
    fin_cases u <;> fin_cases v
    · simp only [pairRepPosition, if_true] at huv
      have hrev := congrArg M.val huv
      have hab : a.val = b.val := by simpa only [M.property.1] using hrev
      exact Prod.ext (Subtype.ext hab) rfl
    · change M.val a.val = b.val at huv
      have hrev := congrArg M.val huv
      rw [M.property.1] at hrev
      have hab : a.val < b.val := a.property.trans_eq huv
      have hba : b.val < a.val := b.property.trans_eq hrev.symm
      omega
    · change a.val = M.val b.val at huv
      have hrev := congrArg M.val huv
      rw [M.property.1] at hrev
      have hab : a.val < b.val := a.property.trans_eq hrev
      have hba : b.val < a.val := b.property.trans_eq huv.symm
      omega
    · simp only [pairRepPosition, if_false] at huv
      exact Prod.ext (Subtype.ext huv) rfl
  · intro i
    by_cases hi : i < M.val i
    · exact ⟨(⟨i, hi⟩, false), by simp [pairRepPosition]⟩
    · have hine : M.val i ≠ i := M.property.2 i
      have hlt : M.val i < i := lt_of_le_of_ne (le_of_not_gt hi) hine
      exact ⟨(⟨M.val i, by simpa only [M.property.1] using hlt⟩, true), by
        simp [pairRepPosition, M.property.1]⟩

private noncomputable def pairRepEquiv (M : Match N) : PairRep M × Bool ≃ Fin N :=
  Equiv.ofBijective (pairRepPosition M) (pairRepPosition_bijective M)

private lemma pairRepEquiv_rep (M : Match N) (r : PairRep M) :
    pairRepEquiv M (r, false) = r.val := rfl

private lemma pairRepEquiv_partner (M : Match N) (r : PairRep M) :
    pairRepEquiv M (r, true) = M.val r.val := rfl

private lemma pairRepEquiv_symm_rep (M : Match N) (r : PairRep M) :
    (pairRepEquiv M).symm r.val = (r, false) := by
  rw [Equiv.symm_apply_eq]
  rfl

private lemma pairRepEquiv_symm_partner (M : Match N) (r : PairRep M) :
    (pairRepEquiv M).symm (M.val r.val) = (r, true) := by
  rw [Equiv.symm_apply_eq]
  rfl

private noncomputable def pairedAssignmentEquiv (M : Match N) :
    (PairRep M → Bool) ≃ {z : Fin N → Bool // paired M z} where
  toFun c := ⟨fun i =>
    let p := (pairRepEquiv M).symm i
    if p.2 then !c p.1 else c p.1, by
      intro i
      obtain ⟨⟨r, b⟩, rfl⟩ := (pairRepEquiv M).surjective i
      fin_cases b
      · dsimp
        rw [pairRepEquiv_partner,
          M.property.1, pairRepEquiv_symm_rep, pairRepEquiv_symm_partner]
        simp
      · dsimp
        rw [pairRepEquiv_rep,
          pairRepEquiv_symm_rep, pairRepEquiv_symm_partner]
        simp⟩
  invFun z := fun r => z.val (pairRepEquiv M (r, false))
  left_inv c := by
    funext r
    dsimp
    rw [pairRepEquiv_rep, pairRepEquiv_symm_rep]
    simp
  right_inv z := by
    apply Subtype.ext
    funext i
    obtain ⟨⟨r, b⟩, rfl⟩ := (pairRepEquiv M).surjective i
    fin_cases b
    · dsimp
      rw [pairRepEquiv_partner, pairRepEquiv_symm_partner]
      simp only [Prod.fst, Prod.snd, if_true, pairRepEquiv_rep]
      exact (z.property r.val).symm
    · dsimp
      rw [pairRepEquiv_rep, pairRepEquiv_symm_rep]
      simp [pairRepEquiv_rep]

private lemma card_pairRep (M : Match N) (hN : Even N) :
    Fintype.card (PairRep M) = N / 2 := by
  obtain ⟨k, hk⟩ := hN
  have hc := Fintype.card_congr (pairRepEquiv M)
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at hc
  omega

private noncomputable def pairedAssignments (M : Match N) : Finset (Fin N → Bool) :=
  @Finset.filter _ (paired M) (Classical.decPred (paired M)) Finset.univ

private lemma sum_pairedAssignments_eq (M : Match N) (f : (Fin N → Bool) → ℝ) :
    ∑ z ∈ pairedAssignments M, f z =
      ∑ c : PairRep M → Bool, f ((pairedAssignmentEquiv M c).val) := by
  classical
  rw [show pairedAssignments M = Finset.univ.filter (paired M) by rfl]
  rw [Finset.sum_subtype (p := paired M) (Finset.univ.filter (paired M)) (by simp) f]
  exact (Equiv.sum_comp (pairedAssignmentEquiv M)
    (fun z => f z.val)).symm

private lemma integral_pairedCoinLaw (M : Match N) (f : (Fin N → Bool) → ℝ) :
    ∫ z, f z ∂pairedCoinLaw M =
      ∑ z ∈ pairedAssignments M, (2 : ℝ) ^ (-(N : ℝ) / 2) * f z := by
  classical
  unfold pairedCoinLaw
  rw [integral_finsetSum_measure]
  · rw [show pairedAssignments M = Finset.univ.filter (paired M) by
      rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : paired M z
    · simp only [hz, if_true, integral_smul_measure, integral_dirac, smul_eq_mul]
      rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (by norm_num) _)]
    · simp [hz]
  · intro z _
    by_cases hz : paired M z
    · simp only [hz, if_true]
      exact (integrable_dirac (by simp)).smul_measure (by simp)
    · simp [hz]

private lemma matchedPairDesign_expectation_eq_uniform (M : Match N)
    (F : (PairRep M → Bool) → ℝ) :
    (Causalean.Experimentation.MatchedPairDesign.matchedPairDesign
      (P := PairRep M)).E F =
      (2 : ℝ) ^ (-(Fintype.card (PairRep M) : ℝ)) * ∑ c, F c := by
  unfold Causalean.Experimentation.MatchedPairDesign.matchedPairDesign
    Causalean.Experimentation.MatchedPairDesign.pairCoinDesign
    Causalean.Experimentation.DesignBased.FiniteDesign.E
  simp only [Causalean.Experimentation.DesignBased.prodDesign_p]
  have hp (c : PairRep M → Bool) :
      (∏ i, (Causalean.Experimentation.DesignBased.coinDesign (1 / 2 : ℝ)
        (by norm_num) (by norm_num)).p (c i)) =
        (2 : ℝ) ^ (-(Fintype.card (PairRep M) : ℝ)) := by
    have hone (i : PairRep M) :
        (Causalean.Experimentation.DesignBased.coinDesign (1 / 2 : ℝ)
          (by norm_num) (by norm_num)).p (c i) = 1 / 2 := by
      cases c i <;> norm_num [Causalean.Experimentation.DesignBased.coinDesign]
    simp_rw [hone]
    simp only [Finset.prod_const, Finset.card_univ, nsmul_eq_mul, one_mul]
    rw [show (1 / 2 : ℝ) ^ Fintype.card (PairRep M) =
        (2 : ℝ) ^ (-(Fintype.card (PairRep M) : ℝ)) by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
      rw [one_div, inv_pow]]
  simp_rw [hp]
  rw [← Finset.mul_sum]

private lemma integral_pairedCoinLaw_eq_matchedPairDesign (M : Match N)
    (hN : Even N) (f : (Fin N → Bool) → ℝ) :
    ∫ z, f z ∂pairedCoinLaw M =
      (Causalean.Experimentation.MatchedPairDesign.matchedPairDesign
        (P := PairRep M)).E
          (fun c => f ((pairedAssignmentEquiv M c).val)) := by
  rw [integral_pairedCoinLaw, matchedPairDesign_expectation_eq_uniform,
    ← Finset.mul_sum, sum_pairedAssignments_eq]
  congr 1
  rw [card_pairRep M hN]
  obtain ⟨k, hk⟩ := hN
  have hhalf : ((N / 2 : ℕ) : ℝ) = (N : ℝ) / 2 := by
    have hNk : N / 2 = k := by omega
    rw [hNk, hk]
    norm_num
  rw [hhalf]
  congr 1
  ring

private lemma pairedCoinLaw_probability (M : Match N) (hN : Even N) :
    IsProbabilityMeasure (pairedCoinLaw M) := by
  constructor
  rw [← ENNReal.toReal_eq_one_iff]
  change (pairedCoinLaw M).real Set.univ = 1
  have h := integral_pairedCoinLaw_eq_matchedPairDesign M hN
    (fun _ => (1 : ℝ))
  simpa only [integral_const, smul_eq_mul, mul_one,
    Causalean.Experimentation.DesignBased.FiniteDesign.E_const] using h

private lemma experimentLaw_map_fst
    (P : Measure (UnitRecord d)) (D : Design m N d)
    (hM : AEMeasurable (fun w : WaveInput m N d => D (designInput w))
      (latentTwoWaveLaw (m := m) (N := N) P))
    (hN : Even N) :
    (experimentLaw (m := m) (N := N) P
      (fun w => pairedCoinLaw (D (designInput w)))).map Prod.fst =
      latentTwoWaveLaw (m := m) (N := N) P := by
  let μ := latentTwoWaveLaw (m := m) (N := N) P
  let κ : WaveInput m N d → Measure (WaveInput m N d × (Fin N → Bool)) :=
    fun w => (pairedCoinLaw (D (designInput w))).map (fun z => (w, z))
  have hκ : AEMeasurable κ μ := pairedExperimentKernel_aemeasurable P D hM
  unfold experimentLaw
  change (μ.bind κ).map Prod.fst = μ
  ext s hs
  rw [Measure.map_apply measurable_fst hs,
    Measure.bind_apply (hs.preimage measurable_fst) hκ]
  have hmass : ∀ w, κ w (Prod.fst ⁻¹' s) = s.indicator 1 w := by
    intro w
    by_cases hw : w ∈ s
    · rw [Set.indicator_of_mem hw]
      change (pairedCoinLaw (D (designInput w))).map (fun z => (w, z))
          (Prod.fst ⁻¹' s) = 1
      rw [Measure.map_apply (by fun_prop) (hs.preimage measurable_fst)]
      rw [show (fun z : Fin N → Bool => (w, z)) ⁻¹' (Prod.fst ⁻¹' s) = Set.univ by
        ext z
        simp [hw]]
      exact (pairedCoinLaw_probability (D (designInput w)) hN).measure_univ
    · rw [Set.indicator_of_notMem hw]
      change (pairedCoinLaw (D (designInput w))).map (fun z => (w, z))
          (Prod.fst ⁻¹' s) = 0
      rw [Measure.map_apply (by fun_prop) (hs.preimage measurable_fst)]
      rw [show (fun z : Fin N → Bool => (w, z)) ⁻¹' (Prod.fst ⁻¹' s) = ∅ by
        ext z
        simp [hw], measure_empty]
  simp_rw [hmass]
  rw [lintegral_indicator_one hs]

private lemma latentTwoWaveLaw_probability
    (P : Measure (UnitRecord d)) (hP : IsProbabilityMeasure P) :
    IsProbabilityMeasure (latentTwoWaveLaw (m := m) (N := N) P) := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure (pilotUnitLaw P) := pilotUnitLaw_probability P hP
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  unfold latentTwoWaveLaw
  infer_instance

private lemma experimentLaw_probability
    (P : Measure (UnitRecord d)) (D : Design m N d)
    (hP : IsProbabilityMeasure P)
    (hM : AEMeasurable (fun w : WaveInput m N d => D (designInput w))
      (latentTwoWaveLaw (m := m) (N := N) P))
    (hN : Even N) :
    IsProbabilityMeasure (experimentLaw (m := m) (N := N) P
      (fun w => pairedCoinLaw (D (designInput w)))) := by
  constructor
  have hmap := experimentLaw_map_fst P D hM hN
  have huniv := congrArg (fun μ : Measure (WaveInput m N d) => μ Set.univ) hmap
  rw [Measure.map_apply measurable_fst MeasurableSet.univ] at huniv
  simpa using huniv.trans
    (latentTwoWaveLaw_probability (m := m) (N := N) P hP).measure_univ

private noncomputable def fixedPairY1 (M : Match N) (w : WaveInput m N d) :
    PairRep M → Bool → ℝ :=
  fun r b => (w.1.2 (pairRepEquiv M (r, !b))).2.2

private noncomputable def fixedPairY0 (M : Match N) (w : WaveInput m N d) :
    PairRep M → Bool → ℝ :=
  fun r b => (w.1.2 (pairRepEquiv M (r, !b))).2.1

private lemma pairedEstimator_assignmentEquiv (M : Match N) (hN : Even N)
    (hN2 : 2 ≤ N) (w : WaveInput m N d) (c : PairRep M → Bool) :
    pairedEstimator N (w, (pairedAssignmentEquiv M c).val) =
      Causalean.Experimentation.MatchedPairDesign.matchedPairEstimator
        (fixedPairY1 M w) (fixedPairY0 M w) c := by
  unfold pairedEstimator
    Causalean.Experimentation.MatchedPairDesign.matchedPairEstimator
    Causalean.Experimentation.MatchedPairDesign.pairContribution
  rw [← Equiv.sum_comp (pairRepEquiv M)]
  rw [Fintype.sum_prod_type]
  have hcard := card_pairRep M hN
  have hNpos : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hcardpos : (Fintype.card (PairRep M) : ℝ) ≠ 0 := by
    rw [hcard]
    exact_mod_cast (show N / 2 ≠ 0 by omega)
  have hNcard : (N : ℝ) = 2 * Fintype.card (PairRep M) := by
    obtain ⟨k, hk⟩ := hN
    have hNk : N / 2 = k := by omega
    rw [hcard, hNk, hk]
    norm_num
    ring
  have hterm (r : PairRep M) :
      ∑ b : Bool,
        ((1 + signed ((pairedAssignmentEquiv M c).val (pairRepEquiv M (r, b)))) *
            (w.1.2 (pairRepEquiv M (r, b))).2.2 -
          (1 - signed ((pairedAssignmentEquiv M c).val (pairRepEquiv M (r, b)))) *
            (w.1.2 (pairRepEquiv M (r, b))).2.1) =
        2 * (fixedPairY1 M w r (c r) - fixedPairY0 M w r (!(c r))) := by
    cases hc : c r <;>
      simp [pairedAssignmentEquiv, fixedPairY1, fixedPairY0, pairRepEquiv_rep,
        pairRepEquiv_partner, pairRepEquiv_symm_rep, pairRepEquiv_symm_partner,
        signed, hc] <;> ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  rw [hNcard]
  field_simp

private lemma abs_pairedEstimator_le_outcome_envelope
    (hN2 : 2 ≤ N) (w : WaveInput m N d) (z : Fin N → Bool) :
    |pairedEstimator N (w, z)| ≤
      2 * (N : ℝ)⁻¹ * ∑ i : Fin N,
        (|(w.1.2 i).2.2| + |(w.1.2 i).2.1|) := by
  unfold pairedEstimator
  have hNnonneg : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  rw [abs_mul, abs_of_nonneg hNnonneg]
  calc
    (N : ℝ)⁻¹ *
        |∑ i : Fin N,
          ((1 + signed (z i)) * (w.1.2 i).2.2 -
            (1 - signed (z i)) * (w.1.2 i).2.1)| ≤
        (N : ℝ)⁻¹ * ∑ i : Fin N,
          |(1 + signed (z i)) * (w.1.2 i).2.2 -
            (1 - signed (z i)) * (w.1.2 i).2.1| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hNnonneg
    _ ≤ (N : ℝ)⁻¹ * ∑ i : Fin N,
          2 * (|(w.1.2 i).2.2| + |(w.1.2 i).2.1|) := by
      gcongr with i
      cases hz : z i
      · have h0 : 2 * |(w.1.2 i).2.1| ≤
            2 * (|(w.1.2 i).2.2| + |(w.1.2 i).2.1|) :=
          mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left (abs_nonneg (w.1.2 i).2.2)) (by norm_num)
        calc
          |(1 + signed false) * (w.1.2 i).2.2 -
              (1 - signed false) * (w.1.2 i).2.1| =
              2 * |(w.1.2 i).2.1| := by
                norm_num [signed, abs_mul]
          _ ≤ 2 * (|(w.1.2 i).2.2| + |(w.1.2 i).2.1|) := h0
      · have h1 : 2 * |(w.1.2 i).2.2| ≤
            2 * (|(w.1.2 i).2.2| + |(w.1.2 i).2.1|) :=
          mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (abs_nonneg (w.1.2 i).2.1)) (by norm_num)
        calc
          |(1 + signed true) * (w.1.2 i).2.2 -
              (1 - signed true) * (w.1.2 i).2.1| =
              2 * |(w.1.2 i).2.2| := by
                norm_num [signed, abs_mul]
          _ ≤ 2 * (|(w.1.2 i).2.2| + |(w.1.2 i).2.1|) := h1
    _ = 2 * (N : ℝ)⁻¹ * ∑ i : Fin N,
          (|(w.1.2 i).2.2| + |(w.1.2 i).2.1|) := by
      rw [← Finset.mul_sum]
      ring

private lemma outcomeEnvelope_memLp_latent
    (P : Measure (UnitRecord d)) (hP : IsProbabilityMeasure P)
    (h0 : Integrable (fun u : UnitRecord d => u.2.1 ^ 2) P)
    (h1 : Integrable (fun u : UnitRecord d => u.2.2 ^ 2) P) :
    MemLp (fun w : WaveInput m N d =>
      2 * (N : ℝ)⁻¹ * ∑ i : Fin N,
        (|(w.1.2 i).2.2| + |(w.1.2 i).2.1|)) 2
      (latentTwoWaveLaw (m := m) (N := N) P) := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure (pilotUnitLaw P) := pilotUnitLaw_probability P hP
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  have hy0 : MemLp (fun u : UnitRecord d => u.2.1) 2 P :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 h0
  have hy1 : MemLp (fun u : UnitRecord d => u.2.2) 2 P :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 h1
  have hmain : MemLp (fun us : Fin N → UnitRecord d =>
      2 * (N : ℝ)⁻¹ * ∑ i : Fin N,
        (|(us i).2.2| + |(us i).2.1|)) 2
      (Measure.pi fun _ : Fin N => P) := by
    apply MemLp.const_mul
    apply memLp_finset_sum Finset.univ
    intro i _
    exact ((hy1.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin N => P) i)).abs.add
        (hy0.comp_measurePreserving
          (measurePreserving_eval (fun _ : Fin N => P) i)).abs)
  unfold latentTwoWaveLaw
  exact hmain.comp_measurePreserving
    (measurePreserving_snd.comp measurePreserving_fst)

private lemma pairedEstimator_memLp_experiment
    (P : Measure (UnitRecord d)) (D : Design m N d)
    (hP : IsProbabilityMeasure P)
    (h0 : Integrable (fun u : UnitRecord d => u.2.1 ^ 2) P)
    (h1 : Integrable (fun u : UnitRecord d => u.2.2 ^ 2) P)
    (hM : AEMeasurable (fun w : WaveInput m N d => D (designInput w))
      (latentTwoWaveLaw (m := m) (N := N) P))
    (hN : Even N) (hN2 : 2 ≤ N) :
    MemLp (pairedEstimator N) 2
      (experimentLaw (m := m) (N := N) P
        (fun w => pairedCoinLaw (D (designInput w)))) := by
  let ν := experimentLaw (m := m) (N := N) P
    (fun w => pairedCoinLaw (D (designInput w)))
  let μ := latentTwoWaveLaw (m := m) (N := N) P
  have hfst : MeasurePreserving (Prod.fst :
      WaveInput m N d × (Fin N → Bool) → WaveInput m N d) ν μ :=
    ⟨measurable_fst, experimentLaw_map_fst P D hM hN⟩
  have henv : MemLp (fun w : WaveInput m N d =>
      2 * (N : ℝ)⁻¹ * ∑ i : Fin N,
        (|(w.1.2 i).2.2| + |(w.1.2 i).2.1|)) 2 μ :=
    outcomeEnvelope_memLp_latent P hP h0 h1
  have henv' := henv.comp_measurePreserving hfst
  apply henv'.mono'
  · unfold pairedEstimator
    fun_prop
  · filter_upwards [] with wz
    rcases wz with ⟨w, z⟩
    simpa only [Real.norm_eq_abs, Function.comp_apply] using
      abs_pairedEstimator_le_outcome_envelope hN2 w z

private lemma fixed_pairedEstimator_integral (M : Match N) (hN : Even N)
    (hN2 : 2 ≤ N) (w : WaveInput m N d) :
    ∫ z, pairedEstimator N (w, z) ∂pairedCoinLaw M =
      (N : ℝ)⁻¹ * ∑ i : Fin N, ((w.1.2 i).2.2 - (w.1.2 i).2.1) := by
  rw [integral_pairedCoinLaw_eq_matchedPairDesign M hN]
  have hfun : (fun c : PairRep M → Bool =>
      pairedEstimator N (w, (pairedAssignmentEquiv M c).val)) =
      Causalean.Experimentation.MatchedPairDesign.matchedPairEstimator
        (fixedPairY1 M w) (fixedPairY0 M w) := by
    funext c
    exact pairedEstimator_assignmentEquiv M hN hN2 w c
  rw [hfun]
  rw [Causalean.Experimentation.MatchedPairDesign.E_matchedPairEstimator]
  · unfold Causalean.Experimentation.MatchedPairDesign.sate
    rw [← Equiv.sum_comp (pairRepEquiv M)]
    rw [Fintype.sum_prod_type]
    simp only [fixedPairY1, fixedPairY0, Fin.sum_univ_two, Bool.not_true,
      Bool.not_false, pairRepEquiv_rep, pairRepEquiv_partner]
    have hcard := card_pairRep M hN
    have hNcard : (N : ℝ) = 2 * Fintype.card (PairRep M) := by
      obtain ⟨k, hk⟩ := hN
      have hNk : N / 2 = k := by omega
      rw [hcard, hNk, hk]
      norm_num
      ring
    rw [hNcard]
    have hsum :
        (∑ p : PairRep M, ∑ b : Bool,
          ((w.1.2 (pairRepEquiv M (p, !b))).2.2 -
            (w.1.2 (pairRepEquiv M (p, !b))).2.1)) =
        ∑ p : PairRep M, ∑ b : Bool,
          ((w.1.2 (pairRepEquiv M (p, b))).2.2 -
            (w.1.2 (pairRepEquiv M (p, b))).2.1) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Fintype.sum_bool, Fintype.sum_bool]
      simp
      ring
    rw [hsum, div_eq_mul_inv]
    ring
  · rw [card_pairRep M hN]
    omega

private lemma pairedEstimator_integral_eq_latent_average
    (P : Measure (UnitRecord d)) (D : Design m N d)
    (hM : AEMeasurable (fun w : WaveInput m N d => D (designInput w))
      (latentTwoWaveLaw (m := m) (N := N) P))
    (hN : Even N) (hN2 : 2 ≤ N)
    (hint : Integrable (pairedEstimator N)
      (experimentLaw (m := m) (N := N) P
        (fun w => pairedCoinLaw (D (designInput w))))) :
    (∫ wz, pairedEstimator N wz ∂experimentLaw (m := m) (N := N) P
      (fun w => pairedCoinLaw (D (designInput w)))) =
      ∫ w, (N : ℝ)⁻¹ * ∑ i : Fin N,
        ((w.1.2 i).2.2 - (w.1.2 i).2.1)
        ∂latentTwoWaveLaw (m := m) (N := N) P := by
  rw [integral_experimentLaw_eq_iterated P D (pairedEstimator N) hM hint]
  apply integral_congr_ae
  filter_upwards [] with w
  exact fixed_pairedEstimator_integral (D (designInput w)) hN hN2 w

private lemma latent_average_integral_eq_ate
    (P : Measure (UnitRecord d))
    (hP : IsProbabilityMeasure P)
    (h0 : Integrable (fun u : UnitRecord d => u.2.1 ^ 2) P)
    (h1 : Integrable (fun u : UnitRecord d => u.2.2 ^ 2) P)
    (hN2 : 2 ≤ N) :
    (∫ w, (N : ℝ)⁻¹ * ∑ i : Fin N,
      ((w.1.2 i).2.2 - (w.1.2 i).2.1)
      ∂latentTwoWaveLaw (m := m) (N := N) P) = ate P := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure (pilotUnitLaw P) := pilotUnitLaw_probability P hP
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  let f : UnitRecord d → ℝ := fun u => u.2.2 - u.2.1
  have hf : Integrable f P := by
    apply Integrable.sub
    · exact ((memLp_two_iff_integrable_sq (by fun_prop)).2 h1).integrable (by norm_num)
    · exact ((memLp_two_iff_integrable_sq (by fun_prop)).2 h0).integrable (by norm_num)
  have hcoord (i : Fin N) :
      (∫ us, f (us i) ∂Measure.pi fun _ : Fin N => P) = ∫ u, f u ∂P := by
    let hmp := measurePreserving_eval (fun _ : Fin N => P) i
    have hmap := integral_map hmp.aemeasurable (hmp.map_eq ▸ hf.aestronglyMeasurable)
    rw [hmp.map_eq] at hmap
    exact hmap.symm
  have hcoord_int (i : Fin N) :
      Integrable (fun us : MainSample N d => f (us i))
        (Measure.pi fun _ : Fin N => P) :=
    (measurePreserving_eval (fun _ : Fin N => P) i).integrable_comp_of_integrable hf
  unfold latentTwoWaveLaw
  let G : PilotSample m d × MainSample N d → ℝ := fun z =>
    (N : ℝ)⁻¹ * ∑ i : Fin N, f (z.2 i)
  change (∫ w, G w.1
      ∂((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
        (Measure.pi fun _ : Fin N => P)).prod randomizerLaw) = _
  rw [integral_fun_fst G]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  let H : MainSample N d → ℝ := fun us =>
    (N : ℝ)⁻¹ * ∑ i : Fin N, f (us i)
  change (∫ z, H z.2
      ∂(Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
        (Measure.pi fun _ : Fin N => P)) = _
  rw [integral_fun_snd H]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  dsimp [H]
  rw [integral_const_mul,
    integral_finset_sum Finset.univ (fun i _ => hcoord_int i)]
  simp_rw [hcoord]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  unfold ate f
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp

private lemma latent_average_realVariance
    (P : Measure (UnitRecord d))
    (hP : IsProbabilityMeasure P)
    (h0 : Integrable (fun u : UnitRecord d => u.2.1 ^ 2) P)
    (h1 : Integrable (fun u : UnitRecord d => u.2.2 ^ 2) P)
    (hN2 : 2 ≤ N) :
    (N : ℝ) * realVariance (latentTwoWaveLaw (m := m) (N := N) P)
      (fun w => (N : ℝ)⁻¹ * ∑ i : Fin N,
        ((w.1.2 i).2.2 - (w.1.2 i).2.1)) =
      realVariance P (fun u => u.2.2 - u.2.1) := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure (pilotUnitLaw P) := pilotUnitLaw_probability P hP
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  let f : UnitRecord d → ℝ := fun u => u.2.2 - u.2.1
  let A : MainSample N d → ℝ := fun us =>
    (N : ℝ)⁻¹ * ∑ i : Fin N, f (us i)
  have hf : MemLp f 2 P := by
    apply MemLp.sub
    · exact (memLp_two_iff_integrable_sq (by fun_prop)).2 h1
    · exact (memLp_two_iff_integrable_sq (by fun_prop)).2 h0
  have hA : MemLp A 2 (Measure.pi fun _ : Fin N => P) := by
    apply MemLp.const_mul
    apply memLp_finset_sum Finset.univ
    intro i _
    exact hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => P) i)
  have hproj : MeasurePreserving
      (fun w : WaveInput m N d => w.1.2)
      (latentTwoWaveLaw (m := m) (N := N) P)
      (Measure.pi fun _ : Fin N => P) := by
    unfold latentTwoWaveLaw
    exact measurePreserving_snd.comp measurePreserving_fst
  have hcomp : realVariance (latentTwoWaveLaw (m := m) (N := N) P)
      (fun w => A w.1.2) =
      realVariance (Measure.pi fun _ : Fin N => P) A := by
    rw [show realVariance (latentTwoWaveLaw (m := m) (N := N) P)
          (fun w => A w.1.2) =
        ProbabilityTheory.variance (fun w => A w.1.2)
          (latentTwoWaveLaw (m := m) (N := N) P) by
        exact (ProbabilityTheory.variance_eq_integral
          (hA.comp_measurePreserving hproj).aemeasurable).symm]
    rw [show realVariance (Measure.pi fun _ : Fin N => P) A =
        ProbabilityTheory.variance A (Measure.pi fun _ : Fin N => P) by
      exact (ProbabilityTheory.variance_eq_integral hA.aemeasurable).symm]
    exact hproj.variance_fun_comp hA.aemeasurable
  change (N : ℝ) * realVariance (latentTwoWaveLaw (m := m) (N := N) P)
      (fun w => A w.1.2) = realVariance P f
  rw [hcomp]
  exact realVariance_iid_average P hP f hf (by omega)

private lemma fixed_pairedEstimator_variance (M : Match N) (hN : Even N)
    (hN2 : 2 ≤ N) (w : WaveInput m N d) :
    realVariance (pairedCoinLaw M) (fun z => pairedEstimator N (w, z)) =
      (Causalean.Experimentation.MatchedPairDesign.matchedPairDesign
        (P := PairRep M)).Var
          (Causalean.Experimentation.MatchedPairDesign.matchedPairEstimator
            (fixedPairY1 M w) (fixedPairY0 M w)) := by
  let T : (Fin N → Bool) → ℝ := fun z => pairedEstimator N (w, z)
  let T' := Causalean.Experimentation.MatchedPairDesign.matchedPairEstimator
    (fixedPairY1 M w) (fixedPairY0 M w)
  let μ := Causalean.Experimentation.MatchedPairDesign.matchedPairDesign
    (P := PairRep M)
  have hpoint (c : PairRep M → Bool) :
      T ((pairedAssignmentEquiv M c).val) = T' c :=
    pairedEstimator_assignmentEquiv M hN hN2 w c
  have hmean : (∫ z, T z ∂pairedCoinLaw M) = μ.E T' := by
    rw [integral_pairedCoinLaw_eq_matchedPairDesign M hN]
    apply Finset.sum_congr rfl
    intro c _
    dsimp only [T, T', μ]
    rw [pairedEstimator_assignmentEquiv M hN hN2 w c]
  unfold realVariance Causalean.Experimentation.DesignBased.FiniteDesign.Var
  rw [integral_pairedCoinLaw_eq_matchedPairDesign M hN]
  apply Finset.sum_congr rfl
  intro c _
  dsimp only [T, T', μ]
  rw [pairedEstimator_assignmentEquiv M hN hN2 w c, hmean]

private lemma fixed_pairedEstimator_variance_formula (M : Match N) (hN : Even N)
    (hN2 : 2 ≤ N) (w : WaveInput m N d) :
    realVariance (pairedCoinLaw M) (fun z => pairedEstimator N (w, z)) =
      (∑ r : PairRep M,
        (Causalean.Experimentation.MatchedPairDesign.pairImbalance
          (fixedPairY1 M w) (fixedPairY0 M w) r) ^ 2) /
        (4 * (Fintype.card (PairRep M) : ℝ) ^ 2) := by
  rw [fixed_pairedEstimator_variance M hN hN2 w]
  exact Causalean.Experimentation.MatchedPairDesign.Var_matchedPairEstimator
    (fixedPairY1 M w) (fixedPairY0 M w)

private lemma fixed_pairedEstimator_variance_all_units (M : Match N) (hN : Even N)
    (hN2 : 2 ≤ N) (w : WaveInput m N d) :
    (N : ℝ) * realVariance (pairedCoinLaw M) (fun z => pairedEstimator N (w, z)) =
      (2 * (N : ℝ))⁻¹ * ∑ i : Fin N,
        (((w.1.2 i).2.2 + (w.1.2 i).2.1) -
          ((w.1.2 (M.val i)).2.2 + (w.1.2 (M.val i)).2.1)) ^ 2 := by
  classical
  rw [fixed_pairedEstimator_variance_formula M hN hN2 w]
  have hsum :
      (∑ i : Fin N,
        (((w.1.2 i).2.2 + (w.1.2 i).2.1) -
          ((w.1.2 (M.val i)).2.2 + (w.1.2 (M.val i)).2.1)) ^ 2) =
        2 * ∑ r : PairRep M,
          (Causalean.Experimentation.MatchedPairDesign.pairImbalance
            (fixedPairY1 M w) (fixedPairY0 M w) r) ^ 2 := by
    rw [← Equiv.sum_comp (pairRepEquiv M), Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Fintype.sum_bool]
    simp only [Bool.not_true, Bool.not_false, pairRepEquiv_rep, pairRepEquiv_partner, M.property.1,
      Causalean.Experimentation.MatchedPairDesign.pairImbalance,
      fixedPairY1, fixedPairY0]
    ring
  rw [hsum]
  have hcard := card_pairRep M hN
  have hNcard : (N : ℝ) = 2 * Fintype.card (PairRep M) := by
    obtain ⟨k, hk⟩ := hN
    have hNk : N / 2 = k := by omega
    rw [hcard, hNk, hk]
    norm_num
    ring
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [hNcard]
  field_simp
  <;> ring

private lemma experiment_realVariance_eq_iterated_fixed
    (P : Measure (UnitRecord d)) (D : Design m N d)
    (hP : IsProbabilityMeasure P)
    (hM : AEMeasurable (fun w : WaveInput m N d => D (designInput w))
      (latentTwoWaveLaw (m := m) (N := N) P))
    (hN : Even N) (hN2 : 2 ≤ N)
    (hmem : MemLp (pairedEstimator N) 2
      (experimentLaw (m := m) (N := N) P
        (fun w => pairedCoinLaw (D (designInput w))))) :
    realVariance (experimentLaw (m := m) (N := N) P
        (fun w => pairedCoinLaw (D (designInput w)))) (pairedEstimator N) =
      ∫ w, realVariance (pairedCoinLaw (D (designInput w)))
          (fun z => pairedEstimator N (w, z)) +
        (((N : ℝ)⁻¹ * ∑ i : Fin N,
            ((w.1.2 i).2.2 - (w.1.2 i).2.1)) -
          ∫ wz, pairedEstimator N wz
            ∂experimentLaw (m := m) (N := N) P
              (fun w => pairedCoinLaw (D (designInput w)))) ^ 2
        ∂latentTwoWaveLaw (m := m) (N := N) P := by
  let ν := experimentLaw (m := m) (N := N) P
    (fun w => pairedCoinLaw (D (designInput w)))
  letI : IsProbabilityMeasure ν := experimentLaw_probability P D hP hM hN
  let c : ℝ := ∫ wz, pairedEstimator N wz ∂ν
  have hcenter : MemLp (fun wz => pairedEstimator N wz - c) 2 ν :=
    hmem.sub (memLp_const c)
  have hsq : Integrable (fun wz => (pairedEstimator N wz - c) ^ 2) ν :=
    hcenter.integrable_sq
  change (∫ wz, (pairedEstimator N wz - c) ^ 2 ∂ν) = _
  rw [integral_experimentLaw_eq_iterated P D _ hM hsq]
  apply integral_congr_ae
  filter_upwards [] with w
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure (pairedCoinLaw (D (designInput w))) :=
    pairedCoinLaw_probability (D (designInput w)) hN
  have hfixed : MemLp (fun z => pairedEstimator N (w, z)) 2
      (pairedCoinLaw (D (designInput w))) := by
    apply MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable
      (2 * (N : ℝ)⁻¹ * ∑ i : Fin N,
        (|(w.1.2 i).2.2| + |(w.1.2 i).2.1|))
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs] using
      abs_pairedEstimator_le_outcome_envelope hN2 w z
  have hident := integral_sq_sub_const_eq_realVariance_add_sq
    (pairedCoinLaw (D (designInput w))) (fun z => pairedEstimator N (w, z))
      c inferInstance hfixed
  have hmean := fixed_pairedEstimator_integral (D (designInput w)) hN hN2 w
  rw [hmean] at hident
  simpa only [ν, c] using hident

/-- Finite second moments and a half-sum regression version give the exact
mean and variance normalization for every measurable matching design. -/
lemma variance_normalization_L2 (P : Measure (UnitRecord d))
    (g : XSpace d → ℝ) (D : Design m N d)
    (hP : IsProbabilityMeasure P)
    (h0 : Integrable (fun u : UnitRecord d => u.2.1 ^ 2) P)
    (h1 : Integrable (fun u : UnitRecord d => u.2.2 ^ 2) P)
    (hscore : IsHalfSumVersion P g)
    (hD : MatchingDesignClass D)
    (hdom : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      designInput w ∈ designDomain m N d)
    (hm : 1 ≤ m)
    (hN : Even N) (hN2 : 2 ≤ N) :
    (∫ wz, pairedEstimator N wz ∂experimentLaw (m := m) (N := N) P
      (fun w => pairedCoinLaw (D (designInput w)))) = ate P ∧
      (N : ℝ) * realVariance (experimentLaw (m := m) (N := N) P
        (fun w => pairedCoinLaw (D (designInput w))))
        (pairedEstimator N) = efficiencyBound P + 4 * risk P g D := by
  have hM : AEMeasurable (fun w : WaveInput m N d => D (designInput w))
      (latentTwoWaveLaw (m := m) (N := N) P) :=
    matchingDesign_aemeasurable_of_ae_domain P D hD hdom
  have hkernel : AEMeasurable (fun w : WaveInput m N d =>
      (pairedCoinLaw (D (designInput w))).map (fun z => (w, z)))
      (latentTwoWaveLaw (m := m) (N := N) P) :=
    pairedExperimentKernel_aemeasurable P D hM
  have hmem : MemLp (pairedEstimator N) 2
      (experimentLaw (m := m) (N := N) P
        (fun w => pairedCoinLaw (D (designInput w)))) :=
    pairedEstimator_memLp_experiment P D hP h0 h1 hM hN hN2
  letI : IsProbabilityMeasure (experimentLaw (m := m) (N := N) P
      (fun w => pairedCoinLaw (D (designInput w)))) :=
    experimentLaw_probability P D hP hM hN
  have hint := hmem.integrable (by norm_num)
  constructor
  · rw [pairedEstimator_integral_eq_latent_average P D hM hN hN2 hint]
    exact latent_average_integral_eq_ate P hP h0 h1 hN2
  · rw [experiment_realVariance_eq_iterated_fixed P D hP hM hN hN2 hmem]
    rw [pairedEstimator_integral_eq_latent_average P D hM hN hN2 hint]
    have hmean := latent_average_integral_eq_ate (m := m) P hP h0 h1 hN2
    rw [hmean]
    letI : IsProbabilityMeasure P := hP
    letI : IsProbabilityMeasure (pilotUnitLaw P) := pilotUnitLaw_probability P hP
    letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
    let μ := latentTwoWaveLaw (m := m) (N := N) P
    letI : IsProbabilityMeasure μ := by
      dsimp [μ]
      exact latentTwoWaveLaw_probability P hP
    let A : WaveInput m N d → ℝ := fun w =>
      (N : ℝ)⁻¹ * ∑ i : Fin N, ((w.1.2 i).2.2 - (w.1.2 i).2.1)
    have hA : MemLp A 2 μ := by
      let f : UnitRecord d → ℝ := fun u => u.2.2 - u.2.1
      have hf : MemLp f 2 P := by
        exact ((memLp_two_iff_integrable_sq (by fun_prop)).2 h1).sub
          ((memLp_two_iff_integrable_sq (by fun_prop)).2 h0)
      have hmain : MeasurePreserving (fun w : WaveInput m N d => w.1.2)
          μ (Measure.pi fun _ : Fin N => P) := by
        dsimp [μ, latentTwoWaveLaw]
        exact measurePreserving_snd.comp measurePreserving_fst
      apply MemLp.const_mul
      apply memLp_finset_sum Finset.univ
      intro i _
      exact hf.comp_measurePreserving
        ((measurePreserving_eval (fun _ : Fin N => P) i).comp hmain)
    have hcenter : Integrable (fun w => (A w - ate P) ^ 2) μ :=
      (hA.sub (memLp_const (ate P))).integrable_sq
    have hmatch := adaptive_matched_square_integrable P g D hP h0 h1 hscore hD hdom
    have hpoint : ∀ w : WaveInput m N d,
        (N : ℝ) * realVariance (pairedCoinLaw (D (designInput w)))
            (fun z => pairedEstimator N (w, z)) =
          (2 * (N : ℝ))⁻¹ * ∑ i : Fin N,
            (((w.1.2 i).2.2 + (w.1.2 i).2.1) -
              ((w.1.2 ((D (designInput w)).val i)).2.2 +
                (w.1.2 ((D (designInput w)).val i)).2.1)) ^ 2 :=
      fun w => fixed_pairedEstimator_variance_all_units
        (D (designInput w)) hN hN2 w
    change (N : ℝ) * (∫ w,
      realVariance (pairedCoinLaw (D (designInput w)))
          (fun z => pairedEstimator N (w, z)) + (A w - ate P) ^ 2 ∂μ) = _
    rw [show (N : ℝ) * (∫ w,
        realVariance (pairedCoinLaw (D (designInput w)))
            (fun z => pairedEstimator N (w, z)) + (A w - ate P) ^ 2 ∂μ) =
        ∫ w, (N : ℝ) *
          (realVariance (pairedCoinLaw (D (designInput w)))
            (fun z => pairedEstimator N (w, z)) + (A w - ate P) ^ 2) ∂μ by
      rw [integral_const_mul]]
    rw [show (∫ w, (N : ℝ) *
        (realVariance (pairedCoinLaw (D (designInput w)))
          (fun z => pairedEstimator N (w, z)) + (A w - ate P) ^ 2) ∂μ) =
        ∫ w, (2 * (N : ℝ))⁻¹ * ∑ i : Fin N,
            (((w.1.2 i).2.2 + (w.1.2 i).2.1) -
              ((w.1.2 ((D (designInput w)).val i)).2.2 +
                (w.1.2 ((D (designInput w)).val i)).2.1)) ^ 2 +
          (N : ℝ) * (A w - ate P) ^ 2 ∂μ by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [mul_add, hpoint w]]
    rw [integral_add hmatch (hcenter.const_mul (N : ℝ)),
      adaptive_matched_square_integral P g D hP h0 h1 hscore hD hdom (by omega)]
    have hvar : (∫ w, (A w - ate P) ^ 2 ∂μ) = realVariance μ A := by
      unfold realVariance
      rw [hmean]
    rw [integral_const_mul, hvar, latent_average_realVariance P hP h0 h1 hN2]
    rw [← outcome_difference_variance_add_sum_residual_sq P hP h0 h1]
    ring

-- @node: lem:variance-normalization
lemma variance_normalization (P : Measure (UnitRecord d))
    (g : XSpace d → ℝ) (D : Design m N d)
    (hclass : RegularScoreClass P g L β cX CX cg Cg)
    (hD : MatchingDesignClass D)
    (hm : 1 ≤ m)
    (hN : Even N) (hN2 : 2 ≤ N) :
    (∫ wz, pairedEstimator N wz ∂experimentLaw (m := m) (N := N) P
      (fun w => pairedCoinLaw (D (designInput w)))) = ate P ∧
      (N : ℝ) * realVariance (experimentLaw (m := m) (N := N) P
        (fun w => pairedCoinLaw (D (designInput w))))
        (pairedEstimator N) = efficiencyBound P + 4 * risk P g D := by
  have hscore : IsHalfSumVersion P g := hclass.half_sum_version
  haveI : IsProbabilityMeasure P := hclass.covariate_density.1
  have h0 : Integrable (fun u : UnitRecord d => u.2.1 ^ 2) P := by
    apply Integrable.of_mem_Icc (0 : ℝ) 1
    · fun_prop
    · filter_upwards [hclass.bounded_outcomes] with u hu
      constructor <;> nlinarith [hu.1.1, hu.1.2]
  have h1 : Integrable (fun u : UnitRecord d => u.2.2 ^ 2) P := by
    apply Integrable.of_mem_Icc (0 : ℝ) 1
    · fun_prop
    · filter_upwards [hclass.bounded_outcomes] with u hu
      constructor <;> nlinarith [hu.2.1, hu.2.2]
  have hdom : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      designInput w ∈ designDomain m N d :=
    latentTwoWaveLaw_designDomain_ae P g hclass
  exact variance_normalization_L2 P g D inferInstance h0 h1 hscore hD hdom hm hN hN2

end CausalSmith.Experimentation.PilotscorePairingFrontier
