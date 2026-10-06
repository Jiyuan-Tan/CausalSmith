module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.OracleSpacing
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.VarianceAdaptiveResidualIntegration
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.VarianceSuperpopulation
public import Causalean.Mathlib.MeasureTheory.ConditionalExpectationTransport
/-!
# Paper bridge for adaptive residual orthogonality

This module constructs measurable score and design representatives, applies the
staged finite-product conditional-residual API on a reassociated latent law, and
transports the resulting orthogonality identities back to the paper experiment.
-/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

open Causalean.Mathlib.Probability.Independence.Conditional.FiniteProductResidual

variable {d m N : ℕ}

private lemma adaptive_residual_orthogonality
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ) (D : Design m N d)
    (hP : IsProbabilityMeasure P)
    (h0 : Integrable (fun u : UnitRecord d => u.2.1 ^ 2) P)
    (h1 : Integrable (fun u : UnitRecord d => u.2.2 ^ 2) P)
    (hscore : IsHalfSumVersion P g) (hD : MatchingDesignClass D)
    (hdom : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      designInput w ∈ designDomain m N d) :
    let r : UnitRecord d → ℝ := fun u =>
      (u.2.2 + u.2.1) - (regression1 P u + regression0 P u)
    (∫ w, ∑ i : Fin N,
      (g (w.1.2 i).1 - g (w.1.2 ((D (designInput w)).val i)).1) * r (w.1.2 i)
        ∂latentTwoWaveLaw (m := m) (N := N) P) = 0 ∧
    (∫ w, ∑ i : Fin N,
      r (w.1.2 i) * r (w.1.2 ((D (designInput w)).val i))
        ∂latentTwoWaveLaw (m := m) (N := N) P) = 0 ∧
    Integrable (fun w => ∑ i : Fin N,
      (r (w.1.2 i) - r (w.1.2 ((D (designInput w)).val i))) ^ 2)
        (latentTwoWaveLaw (m := m) (N := N) P) ∧
    Integrable (fun w => ∑ i : Fin N,
      (g (w.1.2 i).1 - g (w.1.2 ((D (designInput w)).val i)).1) *
        (r (w.1.2 i) - r (w.1.2 ((D (designInput w)).val i))))
        (latentTwoWaveLaw (m := m) (N := N) P) ∧
    Integrable (fun w => ∑ i : Fin N,
      (((w.1.2 i).2.2 + (w.1.2 i).2.1) -
        ((w.1.2 ((D (designInput w)).val i)).2.2 +
          (w.1.2 ((D (designInput w)).val i)).2.1)) ^ 2)
        (latentTwoWaveLaw (m := m) (N := N) P) := by
  classical
  letI : IsProbabilityMeasure P := hP
  let pilotLaw : Measure (PilotSample m d) :=
    Measure.pi fun _ : Fin m => pilotUnitLaw P
  let sideLaw : Measure (PilotSample m d × ℝ) := pilotLaw.prod randomizerLaw
  let mainLaw : Measure (MainSample N d) := Measure.pi fun _ : Fin N => P
  letI : IsProbabilityMeasure (pilotUnitLaw P) := pilotUnitLaw_probability P hP
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  letI : IsProbabilityMeasure pilotLaw := by dsimp [pilotLaw]; infer_instance
  letI : IsProbabilityMeasure sideLaw := by dsimp [sideLaw]; infer_instance
  have hreorder : MeasurePreserving
      (reassocSwap : (PilotSample m d × ℝ) × MainSample N d → WaveInput m N d)
      (productLaw sideLaw P)
      (latentTwoWaveLaw (m := m) (N := N) P) := by
    change MeasurePreserving reassocSwap ((pilotLaw.prod randomizerLaw).prod mainLaw)
      ((pilotLaw.prod mainLaw).prod randomizerLaw)
    exact measurePreserving_reassocSwap pilotLaw randomizerLaw mainLaw
  let sumReg : UnitRecord d → ℝ := fun u =>
    (1 / 2 : ℝ) * (regression1 P u + regression0 P u)
  have hsumReg : StronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance] sumReg := by
    exact (stronglyMeasurable_condExp.add stronglyMeasurable_condExp).const_mul (1 / 2)
  obtain ⟨q, hq, hqcomp⟩ :=
    Causalean.Mathlib.MeasureTheory.exists_measurable_real_comp_of_stronglyMeasurable_comap
      hsumReg
  let r : UnitRecord d → ℝ := fun u =>
    (u.2.2 + u.2.1) - (regression1 P u + regression0 P u)
  have hr : Measurable r := by
    have hreg : Measurable (fun u : UnitRecord d => regression1 P u + regression0 P u) :=
      (stronglyMeasurable_condExp.add stronglyMeasurable_condExp).mono
        measurable_fst.comap_le |>.measurable
    exact (by fun_prop : Measurable fun u : UnitRecord d => u.2.2 + u.2.1).sub hreg
  have hy1 : MemLp (fun u : UnitRecord d => u.2.2) 2 P :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 h1
  have hy0 : MemLp (fun u : UnitRecord d => u.2.1) 2 P :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 h0
  have hreg1 : MemLp (regression1 P) 2 P := hy1.condExp (by norm_num)
  have hreg0 : MemLp (regression0 P) 2 P := hy0.condExp (by norm_num)
  have hr2 : MemLp r 2 P := by
    dsimp [r]
    exact (hy1.add hy0).sub (hreg1.add hreg0)
  have hq2 : MemLp (fun u : UnitRecord d => q u.1) 2 P := by
    apply (memLp_congr_ae ?_).mp ((hreg1.add hreg0).const_mul (1 / 2 : ℝ))
    filter_upwards [] with u
    exact congrFun hqcomp u
  have hzero := condExp_sum_outcome_residual_eq_zero P hP
    (hy0.integrable (by norm_num)) (hy1.integrable (by norm_num))
  let inputLaw := (latentTwoWaveLaw (m := m) (N := N) P).map designInput
  have hdesign_meas : MeasurableSet (designDomain m N d) := by
    unfold designDomain cube
    measurability
  have hinput : Measurable (designInput (m := m) (N := N) (d := d)) := by
    unfold designInput
    fun_prop
  have hmapmem : ∀ᵐ v ∂inputLaw, v ∈ designDomain m N d := by
    exact (ae_map_iff hinput.aemeasurable hdesign_meas).2 hdom
  have hDae : AEMeasurable D inputLaw := by
    rw [← Measure.restrict_eq_self_of_ae_mem hmapmem]
    exact aemeasurable_restrict_of_measurable_subtype hdesign_meas hD.2.1
  let Dm : Design m N d := hDae.mk D
  have hDm : Measurable Dm := hDae.measurable_mk
  have hDeqLatent : (fun w : WaveInput m N d => Dm (designInput w)) =ᵐ[
      latentTwoWaveLaw (m := m) (N := N) P]
      fun w => D (designInput w) := by
    exact ae_of_ae_map hinput.aemeasurable hDae.ae_eq_mk.symm
  have hDeqProduct := hreorder.quasiMeasurePreserving.ae_eq hDeqLatent
  have hscoreq : (fun u : UnitRecord d => g u.1) =ᵐ[P] fun u => q u.1 := by
    filter_upwards [hscore] with u hu
    have hc := congrFun hqcomp u
    dsimp [sumReg] at hc
    calc
      g u.1 = (regression1 P u + regression0 P u) / 2 := hu
      _ = (1 / 2 : ℝ) * (regression1 P u + regression0 P u) := by ring
      _ = q u.1 := hc
  have hcoordq (i : Fin N) :
      (fun az : (PilotSample m d × ℝ) × MainSample N d => g (az.2 i).1) =ᵐ[
        productLaw sideLaw P] fun az => q (az.2 i).1 :=
    (measurePreserving_selectedRecord sideLaw P i).quasiMeasurePreserving.ae_eq hscoreq
  let M : (PilotSample m d × ℝ) × MainCovariates N d → Match N := fun ax =>
    Dm (ax.1.1, ax.2, ax.1.2)
  have hM : Measurable M := by
    apply hDm.comp
    exact (measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hqcoord (i : Fin N) : MemLp
      (fun az : (PilotSample m d × ℝ) × MainSample N d => q (az.2 i).1) 2
      (productLaw sideLaw P) :=
    hq2.comp_measurePreserving (measurePreserving_selectedRecord sideLaw P i)
  have hrcoord (i : Fin N) : MemLp
      (fun az : (PilotSample m d × ℝ) × MainSample N d => r (az.2 i)) 2
      (productLaw sideLaw P) :=
    hr2.comp_measurePreserving (measurePreserving_selectedRecord sideLaw P i)
  have hscoreInt (i : Fin N) : Integrable (fun az :
      (PilotSample m d × ℝ) × MainSample N d =>
      (q (az.2 i).1 - q (az.2 ((M (covariateInfo Prod.fst az)).val i)).1) *
        r (az.2 i)) (productLaw sideLaw P) := by
    have hterms (j : Fin N) : Integrable (fun az :
        (PilotSample m d × ℝ) × MainSample N d =>
        (if (M (covariateInfo Prod.fst az)).val i = j then 1 else 0) *
          q (az.2 j).1 * r (az.2 i)) (productLaw sideLaw P) := by
      have hp := (hqcoord j).integrable_mul (hrcoord i)
      have hmidx : Measurable (fun az : (PilotSample m d × ℝ) × MainSample N d =>
          (M (covariateInfo Prod.fst az)).val i) :=
        (measurable_of_finite (fun M' : Match N => M'.val i)).comp
          (hM.comp (measurable_covariateInfo measurable_fst))
      have hs : MeasurableSet {az : (PilotSample m d × ℝ) × MainSample N d |
          (M (covariateInfo Prod.fst az)).val i = j} :=
        measurableSet_eq_fun hmidx measurable_const
      apply (hp.indicator hs).congr
      filter_upwards [] with az
      by_cases h : (M (covariateInfo Prod.fst az)).val i = j <;>
        simp [Set.indicator, h]
    have hsel : Integrable (fun az : (PilotSample m d × ℝ) × MainSample N d =>
        (∑ j : Fin N, if (M (covariateInfo Prod.fst az)).val i = j then
          q (az.2 j).1 else 0) * r (az.2 i)) (productLaw sideLaw P) := by
      rw [show (fun az => (∑ j : Fin N, if (M (covariateInfo Prod.fst az)).val i = j
          then q (az.2 j).1 else 0) * r (az.2 i)) =
          fun az => ∑ j : Fin N, (if (M (covariateInfo Prod.fst az)).val i = j
            then 1 else 0) * q (az.2 j).1 * r (az.2 i) by
        funext az; simp_rw [Finset.sum_mul]; apply Finset.sum_congr rfl
        intro j _; by_cases h : (M (covariateInfo Prod.fst az)).val i = j <;> simp [h]]
      exact integrable_finset_sum Finset.univ fun j _ => hterms j
    have hfirst := (hqcoord i).integrable_mul (hrcoord i)
    apply (hfirst.sub hsel).congr
    filter_upwards [] with az
    have hs : (∑ j : Fin N, if (M (covariateInfo Prod.fst az)).val i = j then
        q (az.2 j).1 else 0) = q (az.2 ((M (covariateInfo Prod.fst az)).val i)).1 := by
      rw [Finset.sum_eq_single ((M (covariateInfo Prod.fst az)).val i)]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    change q (az.2 i).1 * r (az.2 i) -
        (∑ j : Fin N, if (M (covariateInfo Prod.fst az)).val i = j then
          q (az.2 j).1 else 0) * r (az.2 i) =
      (q (az.2 i).1 - q (az.2 ((M (covariateInfo Prod.fst az)).val i)).1) *
        r (az.2 i)
    rw [hs]
    ring
  have hresInt (i j : Fin N) : Integrable (fun az :
      (PilotSample m d × ℝ) × MainSample N d =>
      (if (M (covariateInfo Prod.fst az)).val i = j then 1 else 0) *
        r (az.2 i) * r (az.2 j)) (productLaw sideLaw P) := by
    have hp := (hrcoord i).integrable_mul (hrcoord j)
    have hmidx : Measurable (fun az : (PilotSample m d × ℝ) × MainSample N d =>
        (M (covariateInfo Prod.fst az)).val i) :=
      (measurable_of_finite (fun M' : Match N => M'.val i)).comp
        (hM.comp (measurable_covariateInfo measurable_fst))
    have hs : MeasurableSet {az : (PilotSample m d × ℝ) × MainSample N d |
        (M (covariateInfo Prod.fst az)).val i = j} :=
      measurableSet_eq_fun hmidx measurable_const
    apply (hp.indicator hs).congr
    filter_upwards [] with az
    by_cases h : (M (covariateInfo Prod.fst az)).val i = j <;>
      simp [Set.indicator, h]
  have hzscore := integral_sum_adaptive_score_mul_residual_eq_zero
    sideLaw P Prod.fst r q M measurable_fst hr hq hM
      (hr2.integrable (by norm_num)) hzero hscoreInt
  have hzres := integral_sum_residual_mul_adaptive_match_eq_zero
    sideLaw P Prod.fst r M measurable_fst hr hM
      (hr2.integrable (by norm_num)) hzero hresInt
  have hrpair := integrable_sum_adaptive_pair_mul sideLaw P Prod.fst
    r r M measurable_fst hM hr2 hr2
  have hrsq : Integrable (fun az : (PilotSample m d × ℝ) × MainSample N d =>
      ∑ i : Fin N, (r (az.2 i)) ^ 2) (productLaw sideLaw P) :=
    integrable_finset_sum Finset.univ fun i _ => (hrcoord i).integrable_sq
  have hrdiff : Integrable (fun az : (PilotSample m d × ℝ) × MainSample N d =>
      ∑ i : Fin N, (r (az.2 i) -
        r (az.2 ((M (covariateInfo Prod.fst az)).val i))) ^ 2)
      (productLaw sideLaw P) := by
    apply ((hrsq.const_mul 2).sub (hrpair.const_mul 2)).congr
    filter_upwards [] with az
    exact (sum_sq_sub_match (M (covariateInfo Prod.fst az))
      (fun i => r (az.2 i))).symm
  have hcross : Integrable (fun az : (PilotSample m d × ℝ) × MainSample N d =>
      ∑ i : Fin N, (q (az.2 i).1 -
        q (az.2 ((M (covariateInfo Prod.fst az)).val i)).1) *
        (r (az.2 i) - r (az.2 ((M (covariateInfo Prod.fst az)).val i))))
      (productLaw sideLaw P) := by
    apply ((integrable_finset_sum Finset.univ fun i _ => hscoreInt i).const_mul 2).congr
    filter_upwards [] with az
    exact (sum_score_mul_residual_sub_match (M (covariateInfo Prod.fst az))
      (fun i => q (az.2 i).1) (fun i => r (az.2 i))).symm
  let s : UnitRecord d → ℝ := fun u => u.2.2 + u.2.1
  have hs2 : MemLp s 2 P := hy1.add hy0
  have hspair := integrable_sum_adaptive_pair_mul sideLaw P Prod.fst
    s s M measurable_fst hM hs2 hs2
  have hscoord (i : Fin N) : MemLp
      (fun az : (PilotSample m d × ℝ) × MainSample N d => s (az.2 i)) 2
      (productLaw sideLaw P) :=
    hs2.comp_measurePreserving (measurePreserving_selectedRecord sideLaw P i)
  have hssq : Integrable (fun az : (PilotSample m d × ℝ) × MainSample N d =>
      ∑ i : Fin N, (s (az.2 i)) ^ 2) (productLaw sideLaw P) :=
    integrable_finset_sum Finset.univ fun i _ => (hscoord i).integrable_sq
  have hsdiff : Integrable (fun az : (PilotSample m d × ℝ) × MainSample N d =>
      ∑ i : Fin N, (s (az.2 i) -
        s (az.2 ((M (covariateInfo Prod.fst az)).val i))) ^ 2)
      (productLaw sideLaw P) := by
    apply ((hssq.const_mul 2).sub (hspair.const_mul 2)).congr
    filter_upwards [] with az
    exact (sum_sq_sub_match (M (covariateInfo Prod.fst az))
      (fun i => s (az.2 i))).symm
  have hcoordq_all : ∀ᵐ az ∂productLaw sideLaw P, ∀ i : Fin N,
      g (az.2 i).1 = q (az.2 i).1 := ae_all_iff.2 hcoordq
  constructor
  · rw [← hreorder.integral_comp reassocSwapEquiv.measurableEmbedding]
    calc
      _ = ∫ az, ∑ i : Fin N,
          (q (az.2 i).1 - q (az.2 ((M (covariateInfo Prod.fst az)).val i)).1) *
            r (az.2 i) ∂productLaw sideLaw P := by
        apply integral_congr_ae
        filter_upwards [hDeqProduct, hcoordq_all]
          with az hDa hga
        change Dm (az.1.1, (fun k => (az.2 k).1), az.1.2) =
          D (az.1.1, (fun k => (az.2 k).1), az.1.2) at hDa
        change (∑ i : Fin N,
            (g (az.2 i).1 - g (az.2 ((D
              (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i)).1) * r (az.2 i)) =
          ∑ i : Fin N,
            (q (az.2 i).1 - q (az.2 ((Dm
              (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i)).1) * r (az.2 i)
        rw [← hDa]
        apply Finset.sum_congr rfl
        intro i _
        rw [hga i, hga ((Dm
          (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i)]
      _ = 0 := hzscore
  · constructor
    · rw [← hreorder.integral_comp reassocSwapEquiv.measurableEmbedding]
      calc
        _ = ∫ az, ∑ i : Fin N,
          r (az.2 i) * r (az.2 ((M (covariateInfo Prod.fst az)).val i))
          ∂productLaw sideLaw P := by
          apply integral_congr_ae
          filter_upwards [hDeqProduct] with az hDa
          change Dm (az.1.1, (fun k => (az.2 k).1), az.1.2) =
            D (az.1.1, (fun k => (az.2 k).1), az.1.2) at hDa
          change (∑ i : Fin N, r (az.2 i) * r (az.2 ((D
              (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i))) =
            ∑ i : Fin N, r (az.2 i) * r (az.2 ((Dm
              (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i))
          rw [← hDa]
        _ = 0 := hzres
    · constructor
      · apply (hreorder.integrable_comp_emb reassocSwapEquiv.measurableEmbedding).mp
        apply hrdiff.congr
        filter_upwards [hDeqProduct] with az hDa
        change Dm (az.1.1, (fun k => (az.2 k).1), az.1.2) =
          D (az.1.1, (fun k => (az.2 k).1), az.1.2) at hDa
        change (∑ i : Fin N, (r (az.2 i) - r (az.2 ((Dm
            (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i))) ^ 2) =
          ∑ i : Fin N, (r (az.2 i) - r (az.2 ((D
            (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i))) ^ 2
        rw [hDa]
      · constructor
        · apply (hreorder.integrable_comp_emb reassocSwapEquiv.measurableEmbedding).mp
          apply hcross.congr
          filter_upwards [hDeqProduct, hcoordq_all] with az hDa hga
          change Dm (az.1.1, (fun k => (az.2 k).1), az.1.2) =
            D (az.1.1, (fun k => (az.2 k).1), az.1.2) at hDa
          change (∑ i : Fin N, (q (az.2 i).1 - q (az.2 ((Dm
              (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i)).1) *
                (r (az.2 i) - r (az.2 ((Dm
                  (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i)))) =
            ∑ i : Fin N, (g (az.2 i).1 - g (az.2 ((D
              (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i)).1) *
                (r (az.2 i) - r (az.2 ((D
                  (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i)))
          rw [← hDa]
          apply Finset.sum_congr rfl
          intro i _
          rw [hga i, hga ((Dm
            (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i)]
        · apply (hreorder.integrable_comp_emb reassocSwapEquiv.measurableEmbedding).mp
          apply hsdiff.congr
          filter_upwards [hDeqProduct] with az hDa
          change Dm (az.1.1, (fun k => (az.2 k).1), az.1.2) =
            D (az.1.1, (fun k => (az.2 k).1), az.1.2) at hDa
          change (∑ i : Fin N, (s (az.2 i) - s (az.2 ((Dm
              (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i))) ^ 2) =
            ∑ i : Fin N,
              (((az.2 i).2.2 + (az.2 i).2.1) -
                ((az.2 ((D (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i)).2.2 +
                  (az.2 ((D (az.1.1, (fun k => (az.2 k).1), az.1.2)).val i)).2.1)) ^ 2
          dsimp [s]
          rw [hDa]

/-- The fixed-pair matched square contributes one residual second moment and
four times the normalized score-matching risk. -/
lemma adaptive_matched_square_integrable
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ) (D : Design m N d)
    (hP : IsProbabilityMeasure P)
    (h0 : Integrable (fun u : UnitRecord d => u.2.1 ^ 2) P)
    (h1 : Integrable (fun u : UnitRecord d => u.2.2 ^ 2) P)
    (hscore : IsHalfSumVersion P g) (hD : MatchingDesignClass D)
    (hdom : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      designInput w ∈ designDomain m N d) :
    Integrable (fun w => (2 * (N : ℝ))⁻¹ * ∑ i : Fin N,
      (((w.1.2 i).2.2 + (w.1.2 i).2.1) -
        ((w.1.2 ((D (designInput w)).val i)).2.2 +
          (w.1.2 ((D (designInput w)).val i)).2.1)) ^ 2)
      (latentTwoWaveLaw (m := m) (N := N) P) := by
  exact (adaptive_residual_orthogonality P g D hP h0 h1 hscore hD hdom).2.2.2.2.const_mul _

lemma adaptive_matched_square_integral
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ) (D : Design m N d)
    (hP : IsProbabilityMeasure P)
    (h0 : Integrable (fun u : UnitRecord d => u.2.1 ^ 2) P)
    (h1 : Integrable (fun u : UnitRecord d => u.2.2 ^ 2) P)
    (hscore : IsHalfSumVersion P g) (hD : MatchingDesignClass D)
    (hdom : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      designInput w ∈ designDomain m N d) (hN : 0 < N) :
    (∫ w, (2 * (N : ℝ))⁻¹ * ∑ i : Fin N,
      (((w.1.2 i).2.2 + (w.1.2 i).2.1) -
        ((w.1.2 ((D (designInput w)).val i)).2.2 +
          (w.1.2 ((D (designInput w)).val i)).2.1)) ^ 2
      ∂latentTwoWaveLaw (m := m) (N := N) P) =
      (∫ u, ((u.2.2 + u.2.1) -
        (regression1 P u + regression0 P u)) ^ 2 ∂P) + 4 * risk P g D := by
  classical
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure (pilotUnitLaw P) := pilotUnitLaw_probability P hP
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  let μ := latentTwoWaveLaw (m := m) (N := N) P
  let r : UnitRecord d → ℝ := fun u =>
    (u.2.2 + u.2.1) - (regression1 P u + regression0 P u)
  let S : WaveInput m N d → ℝ := fun w => ∑ i : Fin N,
    (((w.1.2 i).2.2 + (w.1.2 i).2.1) -
      ((w.1.2 ((D (designInput w)).val i)).2.2 +
        (w.1.2 ((D (designInput w)).val i)).2.1)) ^ 2
  let Q : WaveInput m N d → ℝ := fun w => ∑ i : Fin N,
    (g (w.1.2 i).1 - g (w.1.2 ((D (designInput w)).val i)).1) ^ 2
  let R : WaveInput m N d → ℝ := fun w => ∑ i : Fin N,
    (r (w.1.2 i) - r (w.1.2 ((D (designInput w)).val i))) ^ 2
  let C : WaveInput m N d → ℝ := fun w => ∑ i : Fin N,
    (g (w.1.2 i).1 - g (w.1.2 ((D (designInput w)).val i)).1) *
      (r (w.1.2 i) - r (w.1.2 ((D (designInput w)).val i)))
  have ho := adaptive_residual_orthogonality P g D hP h0 h1 hscore hD hdom
  have hSint : Integrable S μ := ho.2.2.2.2
  have hRint : Integrable R μ := ho.2.2.1
  have hCint : Integrable C μ := ho.2.2.2.1
  have hmain : MeasurePreserving (fun w : WaveInput m N d => w.1.2)
      μ (Measure.pi fun _ : Fin N => P) := by
    dsimp [μ, latentTwoWaveLaw]
    exact measurePreserving_snd.comp measurePreserving_fst
  have hscorecoord (i : Fin N) :
      (fun w : WaveInput m N d => g (w.1.2 i).1) =ᵐ[μ]
        fun w => (regression1 P (w.1.2 i) + regression0 P (w.1.2 i)) / 2 :=
    ((measurePreserving_eval (fun _ : Fin N => P) i).comp hmain).quasiMeasurePreserving.ae_eq
      hscore
  have hscoreall : ∀ᵐ w ∂μ, ∀ i : Fin N,
      g (w.1.2 i).1 =
        (regression1 P (w.1.2 i) + regression0 P (w.1.2 i)) / 2 :=
    ae_all_iff.2 hscorecoord
  have hdecomp : S =ᵐ[μ] fun w => 4 * Q w + R w + 4 * C w := by
    filter_upwards [hscoreall] with w hw
    apply matched_square_decomposition (D (designInput w))
      (fun i => (w.1.2 i).2.2 + (w.1.2 i).2.1)
      (fun i => g (w.1.2 i).1) (fun i => r (w.1.2 i))
    intro i
    dsimp [r]
    rw [hw i]
    ring
  have hQint : Integrable Q μ := by
    apply (((hSint.sub hRint).sub (hCint.const_mul 4)).const_mul (1 / 4 : ℝ)).congr
    filter_upwards [hdecomp] with w hw
    change (1 / 4 : ℝ) * (S w - R w - 4 * C w) = Q w
    rw [hw]
    ring
  have hCzero : (∫ w, C w ∂μ) = 0 := by
    have hz := ho.1
    have hid : C = fun w => 2 * ∑ i : Fin N,
        (g (w.1.2 i).1 - g (w.1.2 ((D (designInput w)).val i)).1) *
          r (w.1.2 i) := by
      funext w
      exact sum_score_mul_residual_sub_match (D (designInput w))
        (fun i => g (w.1.2 i).1) (fun i => r (w.1.2 i))
    rw [hid, integral_const_mul, hz, mul_zero]
  have hr2 : MemLp r 2 P := by
    have hy1 : MemLp (fun u : UnitRecord d => u.2.2) 2 P :=
      (memLp_two_iff_integrable_sq (by fun_prop)).2 h1
    have hy0 : MemLp (fun u : UnitRecord d => u.2.1) 2 P :=
      (memLp_two_iff_integrable_sq (by fun_prop)).2 h0
    dsimp [r]
    exact (hy1.add hy0).sub
      ((hy1.condExp (by norm_num)).add (hy0.condExp (by norm_num)))
  have hrsumint : Integrable (fun w : WaveInput m N d =>
      ∑ i : Fin N, (r (w.1.2 i)) ^ 2) μ := by
    apply integrable_finset_sum Finset.univ
    intro i _
    exact (hr2.comp_measurePreserving
      ((measurePreserving_eval (fun _ : Fin N => P) i).comp hmain)).integrable_sq
  have hrpairint : Integrable (fun w : WaveInput m N d => ∑ i : Fin N,
      r (w.1.2 i) * r (w.1.2 ((D (designInput w)).val i))) μ := by
    apply ((hrsumint.const_mul 2).sub hRint).const_mul (1 / 2 : ℝ) |>.congr
    filter_upwards [] with w
    change (1 / 2 : ℝ) * (2 * (∑ i : Fin N, (r (w.1.2 i)) ^ 2) -
        ∑ i : Fin N, (r (w.1.2 i) -
          r (w.1.2 ((D (designInput w)).val i))) ^ 2) =
      ∑ i : Fin N, r (w.1.2 i) * r (w.1.2 ((D (designInput w)).val i))
    rw [sum_sq_sub_match (D (designInput w)) (fun i => r (w.1.2 i))]
    ring
  have hRval : (∫ w, R w ∂μ) =
      2 * (N : ℝ) * ∫ u, (r u) ^ 2 ∂P := by
    have hcross := ho.2.1
    rw [show (∫ w, R w ∂μ) =
        ∫ w, (2 * ∑ i : Fin N, (r (w.1.2 i)) ^ 2 -
          2 * ∑ i : Fin N, r (w.1.2 i) *
            r (w.1.2 ((D (designInput w)).val i))) ∂μ by
      apply integral_congr_ae
      filter_upwards [] with w
      exact sum_sq_sub_match (D (designInput w)) (fun i => r (w.1.2 i))]
    rw [integral_sub (hrsumint.const_mul 2) (hrpairint.const_mul 2),
      integral_const_mul, integral_const_mul, hcross, mul_zero, sub_zero]
    have hcoord (i : Fin N) : (∫ w : WaveInput m N d, (r (w.1.2 i)) ^ 2 ∂μ) =
        ∫ u, (r u) ^ 2 ∂P := by
      let hp := (measurePreserving_eval (fun _ : Fin N => P) i).comp
        (measurePreserving_snd.comp measurePreserving_fst :
          MeasurePreserving (fun w : WaveInput m N d => w.1.2) μ
            (Measure.pi fun _ : Fin N => P))
      have haestrong : AEStronglyMeasurable (fun u => (r u) ^ 2)
          (Measure.map (fun w : WaveInput m N d => w.1.2 i) μ) := by
        change AEStronglyMeasurable (fun u => (r u) ^ 2)
          (Measure.map (Function.eval i ∘ Prod.snd ∘ Prod.fst) μ)
        rw [hp.map_eq]
        exact hr2.integrable_sq.aestronglyMeasurable
      have himap := integral_map (μ := μ)
        hp.measurable.aemeasurable haestrong
      rw [hp.map_eq] at himap
      exact himap.symm
    have hsumval : (∫ w : WaveInput m N d,
        ∑ i : Fin N, (r (w.1.2 i)) ^ 2 ∂μ) =
        (N : ℝ) * ∫ u, (r u) ^ 2 ∂P := by
      calc
        _ = ∑ i : Fin N, ∫ w : WaveInput m N d, (r (w.1.2 i)) ^ 2 ∂μ := by
          exact integral_finset_sum Finset.univ (fun i _ =>
            (hr2.comp_measurePreserving
              ((measurePreserving_eval (fun _ : Fin N => P) i).comp hmain)).integrable_sq)
        _ = _ := by
          simp_rw [hcoord]
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [hsumval]
    ring
  have hQval : (∫ w, Q w ∂μ) = 2 * (N : ℝ) * risk P g D := by
    unfold risk pairLoss
    dsimp [Q, μ]
    rw [integral_div, integral_const_mul]
    field_simp
  change (∫ w, (2 * (N : ℝ))⁻¹ * S w ∂μ) = _
  rw [integral_const_mul]
  rw [integral_congr_ae hdecomp]
  have hintparts : (∫ w, 4 * Q w + R w + 4 * C w ∂μ) =
      4 * (∫ w, Q w ∂μ) + (∫ w, R w ∂μ) + 4 * (∫ w, C w ∂μ) := by
    calc
      _ = (∫ w, 4 * Q w + R w ∂μ) + ∫ w, 4 * C w ∂μ := by
        exact integral_add ((hQint.const_mul 4).add hRint) (hCint.const_mul 4)
      _ = _ := by
        rw [integral_add (hQint.const_mul 4) hRint, integral_const_mul,
          integral_const_mul]
  rw [hintparts, hCzero, hQval, hRval]
  dsimp [r]
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

end CausalSmith.Experimentation.PilotscorePairingFrontier
