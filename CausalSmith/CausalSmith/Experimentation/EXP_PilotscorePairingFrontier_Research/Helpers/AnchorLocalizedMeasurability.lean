module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.AnchorVariance
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.LocalizedConverse

/-!
# Common-law measurability for anchor localized risks

This file transports the existing localized-loss machinery from regular bounded
models to arbitrary laws in `AnchorClass`.  The canonical anchor score supplies
exactly the Hölder regularity needed to replace it by a measurable clamped
version on the cube supporting the common-law representation.
-/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open Causalean.Stat.Nonparametric.HistogramRegression

/-- The [part of the pair loss charged to a measurable cell](goal), for a
[score](hyp:g), [cell](hyp:Q), [main sample](hyp:x), and [matching](hyp:M). -/
noncomputable def anchorLocalizedPairLoss {d N : ℕ} (g : XSpace d → ℝ)
    (Q : Set (XSpace d)) (x : MainCovariates N d) (M : Match N) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin N,
    Q.indicator (fun _ => (g (x i) - g (x (M.val i))) ^ 2) (x i)

/-- The [cell-localized pair loss](hyp:g,Q,x,M) is [nonnegative](goal). -/
lemma anchorLocalizedPairLoss_nonneg {d N : ℕ} (g : XSpace d → ℝ)
    (Q : Set (XSpace d)) (x : MainCovariates N d) (M : Match N) :
    0 ≤ anchorLocalizedPairLoss g Q x M := by
  unfold anchorLocalizedPairLoss
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  by_cases hmem : x i ∈ Q
  · simp [Set.indicator_of_mem hmem, sq_nonneg]
  · simp [Set.indicator_of_notMem hmem]

/-- The [cell-localized pair loss](hyp:g,Q,x,M) is [bounded by the full pair
loss](goal). -/
lemma anchorLocalizedPairLoss_le_pairLoss {d N : ℕ} (g : XSpace d → ℝ)
    (Q : Set (XSpace d)) (x : MainCovariates N d) (M : Match N) :
    anchorLocalizedPairLoss g Q x M ≤ pairLoss g x M := by
  unfold anchorLocalizedPairLoss pairLoss
  gcongr with i
  by_cases hi : x i ∈ Q
  · simp [Set.indicator_of_mem hi]
  · simp [Set.indicator_of_notMem hi, sq_nonneg]

/-- The [expected normalized cell-localized pair loss](goal) for a
[unit law](hyp:P), [score](hyp:g), [cell](hyp:Q), and [design](hyp:D), written
under the common pilot/cube/randomizer product law. -/
noncomputable def anchorLocalizedCubeRisk {d m N : ℕ}
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (Q : Set (XSpace d)) (D : Design m N d) : ℝ :=
  ∫ z, anchorLocalizedPairLoss g Q z.2.1 (D z) / (N : ℝ)
    ∂((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
      ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw))

/-- The common-law full-risk integrand is strongly measurable for an
[anchor-class law](hyp:hclass) and a supplied [Hölder score](hyp:hL,hβ,hg), under an
[admissible design](hyp:hD) and the [uniform cube marginal](hyp:hcov).
[Strong measurability under the pilot/cube/randomizer product law](goal) follows.
-/
lemma anchorDesignRiskIntegrand_aestronglyMeasurable {d m N : ℕ} {L β cX CX : ℝ}
    (P : Measure (UnitRecord d)) (hclass : AnchorClass P β cX CX)
    (g : XSpace d → ℝ) (hL : 0 < L) (hβ : 0 < β) (hg : HolderScore g L β)
    (hcov : P.map Prod.fst = cubeMeasure d) (D : Design m N d)
    (hD : MatchingDesignClass D) :
    AEStronglyMeasurable
      (fun z : PilotSample m d × MainCovariates N d × ℝ =>
        pairLoss g z.2.1 (D z) / (N : ℝ))
      ((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
        ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)) := by
  letI : IsProbabilityMeasure P := hclass.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    histogram_pilotUnitLaw_probability P hclass.covariate_density.1
  letI : IsProbabilityMeasure (cubeMeasure d) := by
    rw [← hcov]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  let target := (Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
    ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)
  have hcube : MeasurableSet (cube d) := by unfold cube; measurability
  let clamp : XSpace d → Cube d := fun x =>
    ⟨WithLp.toLp 2 (fun i => min 1 (max 0 (x i))), fun i => ⟨by simp, by simp⟩⟩
  have hclamp : Measurable clamp := by dsimp [clamp]; fun_prop
  let g' : XSpace d → ℝ := fun x => g (clamp x).val.ofLp
  have hg' : Measurable g' :=
    (measurable_paperCubeScore g hL hβ hg).comp hclamp
  have hg'eq (x : XSpace d) (hx : x ∈ cube d) : g' x = g x := by
    dsimp [g']
    apply congrArg g
    funext i
    simp [clamp, max_eq_right (hx i).1, min_eq_right (hx i).2]
  have hcubeae : ∀ᵐ x ∂cubeMeasure d, x ∈ cube d := by
    unfold cubeMeasure
    exact ae_restrict_mem hcube
  have hmain : ∀ᵐ xs ∂Measure.pi (fun _ : Fin N => cubeMeasure d),
      ∀ i, xs i ∈ cube d := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hcubeae
  have htargetMain : ∀ᵐ z ∂target, ∀ i, z.2.1 i ∈ cube d := by
    dsimp [target]
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [] with p
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [hmain] with xs hxs
    filter_upwards [] with u
    exact hxs
  have hinput : Measurable (designInput (m := m) (N := N) (d := d)) := by
    unfold designInput
    fun_prop
  have hmap := latentTwoWaveLaw_map_designInput (m := m) (N := N) P
    hclass.covariate_density.1 hcov
  have hdom := anchorClass_latentTwoWaveLaw_designDomain_ae
    (m := m) (N := N) P hclass
  have htargetDom : ∀ᵐ z ∂target, z ∈ designDomain m N d := by
    change ∀ᵐ z ∂((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
      ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)),
        z ∈ designDomain m N d
    rw [← hmap]
    exact (ae_map_iff hinput.aemeasurable
      (by unfold designDomain cube; measurability)).2 hdom
  have hDAE : AEMeasurable D target := by
    rw [← Measure.restrict_eq_self_of_ae_mem htargetDom]
    exact aemeasurable_restrict_of_measurable_subtype
      (by unfold designDomain cube; measurability) hD.2.1
  let scores : PilotSample m d × MainCovariates N d × ℝ → Fin N → ℝ :=
    fun z i => g' (z.2.1 i)
  have hscores : Measurable scores := by
    rw [measurable_pi_iff]
    intro i
    exact hg'.comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hPairMap : Measurable (fun t : (Fin N → ℝ) × Match N =>
      ((1 / 2 : ℝ) * ∑ i : Fin N, (t.1 i - t.1 (t.2.val i)) ^ 2) / (N : ℝ)) := by
    classical
    have hEval (i : Fin N) :
        Measurable (fun t : (Fin N → ℝ) × Match N => t.1 (t.2.val i)) := by
      have heq : (fun t : (Fin N → ℝ) × Match N => t.1 (t.2.val i)) =
          fun t => ∑ j : Fin N, if t.2.val i = j then t.1 j else 0 := by
        funext t
        simp
      rw [heq]
      apply Finset.measurable_sum
      intro j hj
      exact Measurable.ite
        ((measurableSet_singleton j).preimage
          ((measurable_from_top : Measurable (fun M : Match N => M.val i)).comp
            measurable_snd))
        ((measurable_pi_apply j).comp measurable_fst) measurable_const
    apply Measurable.div_const
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact (((measurable_pi_apply i).comp measurable_fst).sub (hEval i)).pow_const 2
  have hmeas' : AEMeasurable
      (fun z => pairLoss g' z.2.1 (D z) / (N : ℝ)) target := by
    have hp := hscores.aemeasurable.prodMk hDAE
    convert hPairMap.comp_aemeasurable hp using 1
    funext z
    simp [scores, pairLoss]
  refine hmeas'.aestronglyMeasurable.congr ?_
  filter_upwards [htargetMain] with z hz
  simp only [pairLoss]
  apply congrArg (fun t : ℝ => t / (N : ℝ))
  apply congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
  apply Finset.sum_congr rfl
  intro i hi
  rw [hg'eq _ (hz i), hg'eq _ (hz ((D z).val i))]

/-- For an [anchor-class law](hyp:hclass), a supplied [Hölder score](hyp:hL,hβ,hg),
[uniform covariate marginal](hyp:hcov), and an [admissible design](hyp:hD), the
[common-law full-risk integrand is integrable](goal) when the main wave is
nonempty](hyp:hN). -/
lemma anchorDesignRiskIntegrand_integrable {d m N : ℕ} {L β cX CX : ℝ}
    (P : Measure (UnitRecord d)) (hclass : AnchorClass P β cX CX)
    (g : XSpace d → ℝ) (hL : 0 < L) (hβ : 0 < β) (hg : HolderScore g L β)
    (hcov : P.map Prod.fst = cubeMeasure d) (D : Design m N d)
    (hD : MatchingDesignClass D) (hN : 1 ≤ N) :
    Integrable
      (fun z : PilotSample m d × MainCovariates N d × ℝ =>
        pairLoss g z.2.1 (D z) / (N : ℝ))
      ((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
        ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)) := by
  letI : IsProbabilityMeasure P := hclass.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    histogram_pilotUnitLaw_probability P hclass.covariate_density.1
  letI : IsProbabilityMeasure (cubeMeasure d) := by
    rw [← hcov]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  let target := (Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
    ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)
  have hmeas := anchorDesignRiskIntegrand_aestronglyMeasurable
    P hclass g hL hβ hg hcov D hD
  have hcube : MeasurableSet (cube d) := by unfold cube; measurability
  have hcubeae : ∀ᵐ x ∂cubeMeasure d, x ∈ cube d := by
    unfold cubeMeasure
    exact ae_restrict_mem hcube
  have hmain : ∀ᵐ xs ∂Measure.pi (fun _ : Fin N => cubeMeasure d),
      ∀ i, xs i ∈ cube d := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hcubeae
  have htargetMain : ∀ᵐ z ∂target, ∀ i, z.2.1 i ∈ cube d := by
    dsimp [target]
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [] with p
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [hmain] with xs hxs
    filter_upwards [] with u
    exact hxs
  let C : ℝ := L * (d : ℝ) ^ (β / 2)
  let R : ℝ := (1 / 2 : ℝ) * C ^ 2
  refine Integrable.mono' (integrable_const R) hmeas ?_
  filter_upwards [htargetMain] with z hz
  have hC : 0 ≤ C := mul_nonneg hL.le (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hterm (i : Fin N) :
      (g (z.2.1 i) - g (z.2.1 ((D z).val i))) ^ 2 ≤ C ^ 2 := by
    have habs := holder_score_cube_oscillation g hL.le hβ.le hg
      (z.2.1 i) (z.2.1 ((D z).val i)) (hz i) (hz ((D z).val i))
    have habsC : |g (z.2.1 i) - g (z.2.1 ((D z).val i))| ≤ C := by
      simpa [C] using habs
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 habsC
  have hsum :
      ∑ i : Fin N, (g (z.2.1 i) - g (z.2.1 ((D z).val i))) ^ 2 ≤
        (N : ℝ) * C ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin N, C ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = (N : ℝ) * C ^ 2 := by simp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnonneg : 0 ≤ pairLoss g z.2.1 (D z) / (N : ℝ) := by
    unfold pairLoss
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  dsimp [R]
  unfold pairLoss
  apply (div_le_iff₀ hNpos).2
  nlinarith

/-- Under the same [anchor-class](hyp:hclass), [Hölder score](hyp:hL,hβ,hg),
[marginal](hyp:hcov), and [design](hyp:hD) assumptions, the [localized
common-law risk integrand is integrable](goal) for every [measurable cell](hyp:hQ)
and [nonempty main wave](hyp:hN). -/
lemma anchorLocalizedDesignRiskIntegrand_integrable {d m N : ℕ} {L β cX CX : ℝ}
    (P : Measure (UnitRecord d)) (hclass : AnchorClass P β cX CX)
    (g : XSpace d → ℝ) (hL : 0 < L) (hβ : 0 < β) (hg : HolderScore g L β)
    (hcov : P.map Prod.fst = cubeMeasure d) (Q : Set (XSpace d))
    (hQ : MeasurableSet Q) (D : Design m N d) (hD : MatchingDesignClass D)
    (hN : 1 ≤ N) :
    Integrable
      (fun z : PilotSample m d × MainCovariates N d × ℝ =>
        anchorLocalizedPairLoss g Q z.2.1 (D z) / (N : ℝ))
      ((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
        ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)) := by
  have hfull := anchorDesignRiskIntegrand_integrable P hclass g hL hβ hg hcov D hD hN
  letI : IsProbabilityMeasure P := hclass.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    histogram_pilotUnitLaw_probability P hclass.covariate_density.1
  letI : IsProbabilityMeasure (cubeMeasure d) := by
    rw [← hcov]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  let target := (Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
    ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)
  have hcube : MeasurableSet (cube d) := by unfold cube; measurability
  let clamp : XSpace d → Cube d := fun x =>
    ⟨WithLp.toLp 2 (fun i => min 1 (max 0 (x i))), fun i => ⟨by simp, by simp⟩⟩
  have hclamp : Measurable clamp := by dsimp [clamp]; fun_prop
  let g' : XSpace d → ℝ := fun x => g (clamp x).val.ofLp
  have hg' : Measurable g' :=
    (measurable_paperCubeScore g hL hβ hg).comp hclamp
  have hg'eq (x : XSpace d) (hx : x ∈ cube d) : g' x = g x := by
    dsimp [g']
    apply congrArg g
    funext i
    simp [clamp, max_eq_right (hx i).1, min_eq_right (hx i).2]
  have hcubeae : ∀ᵐ x ∂cubeMeasure d, x ∈ cube d := by
    unfold cubeMeasure
    exact ae_restrict_mem hcube
  have hmain : ∀ᵐ xs ∂Measure.pi (fun _ : Fin N => cubeMeasure d),
      ∀ i, xs i ∈ cube d := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hcubeae
  have htargetMain : ∀ᵐ z ∂target, ∀ i, z.2.1 i ∈ cube d := by
    dsimp [target]
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [] with p
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [hmain] with xs hxs
    filter_upwards [] with u
    exact hxs
  have hinput : Measurable (designInput (m := m) (N := N) (d := d)) := by
    unfold designInput
    fun_prop
  have hmap := latentTwoWaveLaw_map_designInput (m := m) (N := N) P
    hclass.covariate_density.1 hcov
  have hdom := anchorClass_latentTwoWaveLaw_designDomain_ae
    (m := m) (N := N) P hclass
  have htargetDom : ∀ᵐ z ∂target, z ∈ designDomain m N d := by
    change ∀ᵐ z ∂((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
      ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)),
        z ∈ designDomain m N d
    rw [← hmap]
    exact (ae_map_iff hinput.aemeasurable
      (by unfold designDomain cube; measurability)).2 hdom
  have hDAE : AEMeasurable D target := by
    rw [← Measure.restrict_eq_self_of_ae_mem htargetDom]
    exact aemeasurable_restrict_of_measurable_subtype
      (by unfold designDomain cube; measurability) hD.2.1
  let scores : PilotSample m d × MainCovariates N d × ℝ → Fin N → ℝ :=
    fun z i => g' (z.2.1 i)
  have hscores : Measurable scores := by
    rw [measurable_pi_iff]
    intro i
    exact hg'.comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  let main : PilotSample m d × MainCovariates N d × ℝ → MainCovariates N d :=
    fun z => z.2.1
  have hmainMeas : Measurable main := measurable_fst.comp measurable_snd
  have hPairMap : Measurable
      (fun t : ((Fin N → ℝ) × MainCovariates N d) × Match N =>
        ((1 / 2 : ℝ) * ∑ i : Fin N,
          Q.indicator (fun _ => (t.1.1 i - t.1.1 (t.2.val i)) ^ 2)
            (t.1.2 i)) / (N : ℝ)) := by
    classical
    have hEval (i : Fin N) : Measurable
        (fun t : ((Fin N → ℝ) × MainCovariates N d) × Match N =>
          t.1.1 (t.2.val i)) := by
      have heq : (fun t : ((Fin N → ℝ) × MainCovariates N d) × Match N =>
          t.1.1 (t.2.val i)) =
          fun t => ∑ j : Fin N, if t.2.val i = j then t.1.1 j else 0 := by
        funext t
        simp
      rw [heq]
      apply Finset.measurable_sum
      intro j hj
      exact Measurable.ite
        ((measurableSet_singleton j).preimage
          ((measurable_from_top : Measurable (fun M : Match N => M.val i)).comp
            measurable_snd))
        ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
        measurable_const
    apply Measurable.div_const
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    have hterm : Measurable
        (fun t : ((Fin N → ℝ) × MainCovariates N d) × Match N =>
          (t.1.1 i - t.1.1 (t.2.val i)) ^ 2) :=
      (((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).sub
        (hEval i)).pow_const 2
    exact hterm.indicator (hQ.preimage
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)))
  have hmeas' : AEMeasurable
      (fun z => anchorLocalizedPairLoss g' Q z.2.1 (D z) / (N : ℝ)) target := by
    have hp := (hscores.prodMk hmainMeas).aemeasurable.prodMk hDAE
    convert hPairMap.comp_aemeasurable hp using 1
    funext z
    simp [scores, main, anchorLocalizedPairLoss]
  have hlocmeas : AEStronglyMeasurable
      (fun z => anchorLocalizedPairLoss g Q z.2.1 (D z) / (N : ℝ)) target := by
    refine hmeas'.aestronglyMeasurable.congr ?_
    filter_upwards [htargetMain] with z hz
    unfold anchorLocalizedPairLoss
    apply congrArg (fun t : ℝ => t / (N : ℝ))
    apply congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hiQ : z.2.1 i ∈ Q
    · simp only [Set.indicator_of_mem hiQ]
      rw [hg'eq _ (hz i), hg'eq _ (hz ((D z).val i))]
    · simp [Set.indicator_of_notMem hiQ]
  refine Integrable.mono' hfull hlocmeas ?_
  filter_upwards [] with z
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hloc0 := anchorLocalizedPairLoss_nonneg g Q z.2.1 (D z)
  have hle := anchorLocalizedPairLoss_le_pairLoss g Q z.2.1 (D z)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hloc0 hNpos.le)]
  exact div_le_div_of_nonneg_right hle hNpos.le

end CausalSmith.Experimentation.PilotscorePairingFrontier
