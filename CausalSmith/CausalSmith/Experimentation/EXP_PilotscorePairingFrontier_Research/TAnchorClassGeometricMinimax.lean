module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.AnchorHypercubeGap
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.AnchorLocalizedConverse
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.AnchorRiskCongruence
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.AnchorUpper
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.GaussianAnchorInformation
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.TRegularDensityHypercube
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.TSelectorUpper
public import Mathlib.Data.Real.Pointwise

/-! # Pilot-augmented Hölder anchor minimax theorem -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open Causalean.Stat.Nonparametric.HistogramRegression
open scoped Pointwise

variable {d m N : ℕ} {β cX CX : ℝ}

noncomputable def anchorScore (P : Measure (UnitRecord d))
    (h : AnchorClass P β cX CX) : XSpace d → ℝ :=
  Classical.choose h.score_version

noncomputable def anchorRisk (P : Measure (UnitRecord d))
    (h : AnchorClass P β cX CX) (D : Design m N d) : ℝ :=
  risk P (anchorScore P h) D

noncomputable def anchorMinimaxRisk (d m N : ℕ) (β cX CX : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ D : Design m N d, MatchingDesignClass D ∧
    v = sSup {r : ℝ | ∃ P : Measure (UnitRecord d),
      ∃ h : AnchorClass P β cX CX, r = anchorRisk P h D}}

noncomputable def anchorExcessVarianceRisk (d m N : ℕ) (β cX CX : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ D : Design m N d, MatchingDesignClass D ∧
    v = sSup {r : ℝ | ∃ P : Measure (UnitRecord d),
      ∃ _h : AnchorClass P β cX CX,
      r = (N : ℝ) * realVariance
        (experimentLaw (m := m) (N := N) P
          (fun w => pairedCoinLaw (D (designInput w)))) (pairedEstimator N) -
          efficiencyBound P}}

-- @node: anchor_geometric_risk_bound_high_dim
lemma anchor_geometric_risk_bound_high_dim (d m N : ℕ) (β cX CX : ℝ)
    (hd : 2 ≤ d) (hN : Even N) (hN2 : 2 ≤ N)
    (P : Measure (UnitRecord d)) (h : AnchorClass P β cX CX) :
    anchorRisk (m := m) (N := N) P h
      (fun input : PilotSample m d × MainCovariates N d × ℝ =>
        geometricMatching input.2.1 hN hN2) ≤
      ((1 / 2 : ℝ) * (32 * (d : ℝ)) ^ β) *
        (N : ℝ) ^ (-2 * β / d) := by
  have hβ0 : 0 < β := h.parameters.2.1
  have hβ1 : β ≤ 1 := h.parameters.2.2.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let g := anchorScore P h
  have hg : HolderScore g 1 β := (Classical.choose_spec h.score_version).2
  have hcube_meas : MeasurableSet (cube d) := by
    unfold cube
    measurability
  have hXmap : ∀ᵐ x ∂P.map Prod.fst, x ∈ cube d := by
    change cube d ∈ ae (P.map Prod.fst)
    rw [mem_ae_iff]
    apply h.covariate_density.2.1
    simp [cubeMeasure, hcube_meas]
  have hX : ∀ᵐ u ∂P, u.1 ∈ cube d :=
    ae_of_ae_map measurable_fst.aemeasurable hXmap
  letI : IsProbabilityMeasure P := h.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) := pilotUnitLaw_probability P h.covariate_density.1
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  have hmains : ∀ᵐ us ∂Measure.pi (fun _ : Fin N => P),
      ∀ i, (us i).1 ∈ cube d := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hX
  have hdom : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      ∀ i, (w.1.2 i).1 ∈ cube d := by
    unfold latentTwoWaveLaw
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [] with pilot
    filter_upwards [hmains] with us hus
    filter_upwards [] with u
    exact hus
  let B : ℝ := ((1 / 2 : ℝ) * (32 * (d : ℝ)) ^ β *
    (N : ℝ) ^ (1 - 2 * β / d)) / (N : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      pairLoss g (fun i => (w.1.2 i).1)
          (geometricMatching (fun i => (w.1.2 i).1) hN hN2) / (N : ℝ) ≤ B := by
    filter_upwards [hdom] with w hw
    have hcost := geometric_pairLoss_holder_rate hd hN hN2 g 1 β
      (by norm_num) hβ0 hβ1 hg (fun i => (w.1.2 i).1) hw
    exact (div_le_div_iff_of_pos_right hNpos).2 (by simpa using hcost)
  have hnonneg : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      0 ≤ pairLoss g (fun i => (w.1.2 i).1)
          (geometricMatching (fun i => (w.1.2 i).1) hN hN2) / (N : ℝ) := by
    filter_upwards [] with w
    unfold pairLoss
    positivity
  letI : IsProbabilityMeasure (latentTwoWaveLaw (m := m) (N := N) P) := by
    unfold latentTwoWaveLaw
    infer_instance
  unfold anchorRisk risk
  change (∫ w, pairLoss g (fun i => (w.1.2 i).1)
    (geometricMatching (fun i => (w.1.2 i).1) hN hN2) / (N : ℝ)
      ∂latentTwoWaveLaw (m := m) (N := N) P) ≤ _
  have hrisk := integral_mono_of_nonneg hnonneg (integrable_const B) hbound
  have hformula : B =
      ((1 / 2 : ℝ) * (32 * (d : ℝ)) ^ β) *
        (N : ℝ) ^ (-2 * β / d) := by
    calc
      B = ((1 / 2 : ℝ) * (32 * (d : ℝ)) ^ β) *
          ((N : ℝ) ^ (1 - 2 * β / d) * (N : ℝ) ^ (-1 : ℝ)) := by
            dsimp [B]
            rw [div_eq_mul_inv, ← Real.rpow_neg_one]
            ring
      _ = _ := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  simpa [g, hformula] using hrisk

private lemma anchor_risk_nonnegative (P : Measure (UnitRecord d))
    (h : AnchorClass P β cX CX) (D : Design m N d) :
    0 ≤ anchorRisk P h D := by
  unfold anchorRisk risk
  apply integral_nonneg
  intro w
  unfold pairLoss
  positivity

private lemma anchor_risk_le_envelope (hN : 1 ≤ N)
    (P : Measure (UnitRecord d)) (h : AnchorClass P β cX CX)
    (D : Design m N d) :
    anchorRisk P h D ≤ (1 / 2 : ℝ) * (d : ℝ) ^ β := by
  let g := anchorScore P h
  have hg : HolderScore g 1 β := (Classical.choose_spec h.score_version).2
  have hdom := anchorClass_latentTwoWaveLaw_designDomain_ae
    (m := m) (N := N) P h
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbound : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      pairLoss g (fun i => (w.1.2 i).1) (D (designInput w)) / (N : ℝ) ≤
        (1 / 2 : ℝ) * (d : ℝ) ^ β := by
    filter_upwards [hdom] with w hw
    have hterm (i : Fin N) :
        (g (w.1.2 i).1 - g (w.1.2 ((D (designInput w)).val i)).1) ^ 2 ≤
          (d : ℝ) ^ β := by
      have ha := holder_score_cube_oscillation g (by norm_num) h.parameters.2.1.le hg
        (w.1.2 i).1 (w.1.2 ((D (designInput w)).val i)).1
        (hw.2.1 i) (hw.2.1 ((D (designInput w)).val i))
      have hd0 : 0 ≤ (d : ℝ) ^ (β / 2) := Real.rpow_nonneg (Nat.cast_nonneg d) _
      have hs := (sq_le_sq₀ (abs_nonneg _) hd0).2 (by simpa using ha)
      rw [sq_abs] at hs
      calc
        _ ≤ ((d : ℝ) ^ (β / 2)) ^ 2 := hs
        _ = (d : ℝ) ^ β := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg d)]
          congr 1
          ring
    unfold pairLoss
    apply (div_le_iff₀ hNr).2
    calc
      (1 / 2 : ℝ) * ∑ i : Fin N,
          (g (w.1.2 i).1 - g (w.1.2 ((D (designInput w)).val i)).1) ^ 2 ≤
          (1 / 2 : ℝ) * ((N : ℝ) * (d : ℝ) ^ β) := by
            gcongr
            calc
              _ ≤ ∑ _i : Fin N, (d : ℝ) ^ β :=
                Finset.sum_le_sum fun i _ => hterm i
              _ = _ := by simp
      _ = ((1 / 2 : ℝ) * (d : ℝ) ^ β) * (N : ℝ) := by ring
  letI : IsProbabilityMeasure P := h.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    pilotUnitLaw_probability P h.covariate_density.1
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  letI : IsProbabilityMeasure (latentTwoWaveLaw (m := m) (N := N) P) := by
    unfold latentTwoWaveLaw
    infer_instance
  unfold anchorRisk risk
  have hnonneg : 0 ≤ᵐ[latentTwoWaveLaw (m := m) (N := N) P]
      fun w => pairLoss g (fun i => (w.1.2 i).1) (D (designInput w)) / (N : ℝ) := by
    filter_upwards [] with w
    unfold pairLoss
    positivity
  have hmono := integral_mono_of_nonneg hnonneg (integrable_const _) hbound
  simpa [g] using hmono

/-- The geometric design obeys the anchor-class rate uniformly in every
positive dimension. -/
-- @node: anchor_geometric_risk_bound
lemma anchor_geometric_risk_bound (d m N : ℕ) (β cX CX : ℝ)
    (hN : Even N) (hN2 : 2 ≤ N)
    (P : Measure (UnitRecord d)) (h : AnchorClass P β cX CX) :
    anchorRisk (m := m) (N := N) P h
      (fun input => geometricMatching input.2.1 hN hN2) ≤
      max ((1 / 2 : ℝ) * 2 ^ β * (1 / cX ^ 2) ^ β)
          ((1 / 2 : ℝ) * (32 * (d : ℝ)) ^ β) *
        (N : ℝ) ^ (-2 * β / d) := by
  rcases d with _ | d
  · have hd := h.parameters.1
    omega
  rcases d with _ | d
  · have hr := anchor_geometric_risk_bound_one_dim_raw m N β cX CX
      h.parameters.2.1 h.parameters.2.2.1 h.parameters.2.2.2.1
      (h.parameters.2.2.2.2.1.trans h.parameters.2.2.2.2.2)
      hN hN2 P (anchorScore P h) (Classical.choose_spec h.score_version).2
      h.covariate_density
    apply hr.trans
    change ((1 / 2 : ℝ) * 2 ^ β * (1 / cX ^ 2) ^ β) *
        (N : ℝ) ^ (-2 * β) ≤ _
    norm_num
    gcongr
    exact le_max_left _ _
  · exact (anchor_geometric_risk_bound_high_dim (d + 2) m N β cX CX
      (by omega) hN hN2 P h).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _))

private lemma anchor_lower_witness (d : ℕ) (β cX CX : ℝ)
    (hpars : ValidAnchorParameters d β cX CX) :
    ∃ c : ℝ, 0 < c ∧ ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
      ∀ D : Design m N d, MatchingDesignClass D →
        ∃ P : Measure (UnitRecord d), ∃ h : AnchorClass P β cX CX,
          c * (N : ℝ) ^ (-2 * β / d) ≤ anchorRisk P h D := by
  classical
  have hreg : ValidClassParameters d β (3 / 4 : ℝ) cX CX 1 3 := by
    rcases hpars with ⟨hd, hβ0, hβ1, hcX, hcX1, hCX⟩
    exact ⟨hd, hβ0, hβ1, by norm_num, hcX, hcX1, hCX,
      by norm_num, by norm_num, by norm_num⟩
  obtain ⟨h0, c0, c1, C1, C2, κ, ε, A, Bconst,
      hh0, hc0, hc1, hC1, hC2, hκ, hε, hA, hBconst, hfam⟩ :=
    (regular_density_hypercube d β (3 / 4 : ℝ) cX CX 1 3 hreg).2 (by norm_num)
  obtain ⟨cmesh, hcmesh, hmesh⟩ :=
    exists_reciprocal_mesh_for_joint_rate d β (min h0 (1 / 2)) 1
      hpars.1 hpars.2.1 (lt_min hh0 (by norm_num)) (by norm_num)
  let c : ℝ := (c0 ^ 2 * c1 ^ 2 * Real.exp (-1) / 8) * cmesh
  refine ⟨c, mul_pos (by positivity) hcmesh, ?_⟩
  intro m N hm hN D hD
  obtain ⟨q, hq, hqh0, hocc, _hpilot, hrate⟩ := hmesh 1 N (by omega) hN
  let h : ℝ := (q : ℝ)⁻¹
  have hh : 0 < h := by dsimp [h]; positivity
  have hh0' : h ≤ h0 := hqh0.trans (min_le_left _ _)
  have hhsmall : h ≤ 1 / 2 := hqh0.trans (min_le_right _ _)
  have hrate' : cmesh * (N : ℝ) ^ (-2 * β / d) ≤ h ^ (2 * β) := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hdN : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hpars.1
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hdN
    have hpow : (N : ℝ) ^ (-(2 * β) / d) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos hNreal
      have hn : -(2 * β) ≤ 0 := by linarith [hpars.2.1]
      exact div_nonpos_of_nonpos_of_nonneg hn hdR.le
    norm_num at hrate
    rw [min_eq_left hpow] at hrate
    have hexp : -(2 * β) / (d : ℝ) = -2 * β / d := by ring
    rw [hexp] at hrate
    simpa [h] using hrate
  obtain ⟨K, Q, ψ, B, g, base, amplitude, hKlo, hKhi, hQside, hdisj,
      hB, hψ, hamp, hg, hflip, hfold, hmodel, hcov, hklold⟩ := (hfam q hq hh0').2
  have hamp_pos : 0 < amplitude :=
    lt_of_lt_of_le (mul_pos hc1 (Real.rpow_pos_of_pos hh _)) hamp
  have hψmeas : ∀ j, Measurable (fun x : Cube d => ψ j x.val.ofLp) := by
    intro j
    exact measurable_hypercube_bump_on_cube g base amplitude (3 / 4 : ℝ) β ψ
      hg hamp_pos (by norm_num) hpars.2.1 (fun θ => (hmodel θ).holder_score)
      (fun _ => false) j
  let clamp : XSpace d → Cube d := fun x =>
    ⟨WithLp.toLp 2 (fun i => min 1 (max 0 (x i))), fun i => ⟨by simp, by simp⟩⟩
  have hclamp : Measurable clamp := by dsimp [clamp]; fun_prop
  have hclampeq (x : XSpace d) (hx : x ∈ cube d) : (clamp x).val.ofLp = x := by
    funext i
    simp [clamp, max_eq_right (hx i).1, min_eq_right (hx i).2]
  let gt : (Fin K → Bool) → XSpace d → ℝ := fun θ x =>
    g θ (clamp x).val.ofLp
  have hgtmeas : ∀ θ, Measurable (gt θ) := by
    intro θ
    exact (measurable_paperCubeScore (g θ) (by norm_num) hpars.2.1
      (hmodel θ).holder_score).comp hclamp
  have hgteq (θ) (x : XSpace d) (hx : x ∈ cube d) : gt θ x = g θ x := by
    simp [gt, hclampeq x hx]
  have hgtholder : ∀ θ, HolderScore (gt θ) 1 β := by
    intro θ x hx y hy
    rw [hgteq θ x hx, hgteq θ y hy]
    exact ((hmodel θ).holder_score x hx y hy).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (3 / 4 : ℝ) ≤ 1)
        (Real.rpow_nonneg (by unfold euclideanDistance; positivity) _))
  let gapB : ℝ := 16 * (3 / 4 : ℝ) ^ 2 * h ^ ((d : ℝ) + 2 * β)
  have hgapB : 0 < gapB := by dsimp [gapB]; positivity
  let v : NNReal := ⟨(m : ℝ) * gapB, (mul_nonneg (Nat.cast_nonneg m) hgapB.le)⟩
  have hv : v ≠ 0 := by
    apply ne_of_gt
    change 0 < (m : ℝ) * gapB
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    exact mul_pos hmR hgapB
  let P : (Fin K → Bool) → Measure (UnitRecord d) := fun θ =>
    gaussianAnchorLaw (gt θ) v
  let ha : ∀ θ, AnchorClass (P θ) β cX CX := fun θ =>
    gaussianAnchorClass (gt θ) v hv (hgtmeas θ) hpars (hgtholder θ)
  have hPcov : ∀ θ, (P θ).map Prod.fst = cubeMeasure d := by
    intro θ
    exact gaussianAnchorLaw_map_fst (gt θ) v (hgtmeas θ)
  have hcubeae : ∀ᵐ x ∂cubeMeasure d, x ∈ cube d := by
    unfold cubeMeasure
    exact ae_restrict_mem (by unfold cube; measurability)
  have hgap : ∀ θ j,
      Integrable (fun x => (gt θ x - gt (flipCoordinate θ j) x) ^ 2)
          (cubeMeasure d) ∧
        (∫ x, (gt θ x - gt (flipCoordinate θ j) x) ^ 2 ∂cubeMeasure d) ≤ gapB := by
    intro θ j
    obtain ⟨hi, hb⟩ := hypercube_flip_sq_gap_integrable_and_integral_le_of_fields
      Q g hQside hflip hmodel hcov hpars.1 hpars.2.1 hpars.2.2.1
      (by norm_num) hh hhsmall θ j
    have hae : (fun x => (gt θ x - gt (flipCoordinate θ j) x) ^ 2) =ᵐ[cubeMeasure d]
        fun x => (g θ x - g (flipCoordinate θ j) x) ^ 2 := by
      filter_upwards [hcubeae] with x hx
      rw [hgteq θ x hx, hgteq (flipCoordinate θ j) x hx]
    refine ⟨hi.congr hae.symm, ?_⟩
    rw [integral_congr_ae hae]
    exact hb
  have hkl : ∀ θ j, InformationTheory.klDiv
      (Measure.pi fun _ : Fin m => pilotUnitLaw (P θ))
      (Measure.pi fun _ : Fin m => pilotUnitLaw (P (flipCoordinate θ j))) ≤
        ENNReal.ofReal 1 := by
    intro θ j
    have hk := gaussianAnchorPilotProduct_klDiv_le_of_integral m
      (gt θ) (gt (flipCoordinate θ j)) v hv (hgtmeas θ)
      (hgtmeas (flipCoordinate θ j)) (hgap θ j).1 gapB hgapB.le (hgap θ j).2
    have hvreal : (v : ℝ) = (m : ℝ) * gapB := rfl
    simpa [P, hvreal, ne_of_gt hgapB,
      show (m : ℝ) ≠ 0 by exact_mod_cast (show m ≠ 0 by omega)] using hk
  obtain ⟨θ, hrisk⟩ := anchor_hypercube_localized_risk_witness Q ψ B g base amplitude
    hKlo hQside hdisj hB hψ hamp hg (by norm_num) hpars.2.1
    (fun θ => (hmodel θ).holder_score) hψmeas P ha hPcov hkl hc0 hc1 hh hN hocc D hD
  refine ⟨P θ, ha θ, ?_⟩
  have hhalfgt : IsHalfSumVersion (P θ) (gt θ) := by
    exact gaussianAnchorLaw_isHalfSumVersion (gt θ) v (hgtmeas θ)
      (holderScore_integrable_sq_cube (gt θ) β (hgtmeas θ) hpars.2.1.le
        (hgtholder θ))
  have hhalfg : IsHalfSumVersion (P θ) (g θ) := by
    filter_upwards [(show ∀ᵐ u ∂P θ, u.1 ∈ cube d by
      have hmapped : ∀ᵐ x ∂(P θ).map Prod.fst, x ∈ cube d := by
        rw [hPcov θ]
        exact hcubeae
      exact ae_of_ae_map measurable_fst.aemeasurable hmapped), hhalfgt] with u hu heq
    rw [← hgteq θ u.1 hu]
    exact heq
  have heqrisk := risk_eq_of_isHalfSumVersion (P θ) (ha θ).covariate_density.1
    (g θ) (anchorScore (P θ) (ha θ)) hhalfg
    (Classical.choose_spec (ha θ).score_version).1 D
  unfold anchorRisk
  rw [← heqrisk]
  have hscale := mul_le_mul_of_nonneg_left hrate'
    (show 0 ≤ c0 ^ 2 * c1 ^ 2 * Real.exp (-1) / 8 by positivity)
  have hscale' : c * (N : ℝ) ^ (-2 * β / d) ≤
      (c0 ^ 2 * c1 ^ 2 * Real.exp (-1) / 8) * h ^ (2 * β) := by
    simpa [c, mul_assoc] using hscale
  exact hscale'.trans hrisk

private lemma geometricMatching_anchor_designClass (m d N : ℕ)
    (hN : Even N) (hN2 : 2 ≤ N) :
    MatchingDesignClass (fun input : PilotSample m d × MainCovariates N d × ℝ =>
      geometricMatching input.2.1 hN hN2) := by
  let D : Design m N d := fun input => geometricMatching input.2.1 hN hN2
  have hmeas : Measurable D :=
    (geometricMatching_measurable hN hN2).comp (measurable_fst.comp measurable_snd)
  refine ⟨⟨hN, hN2⟩, hmeas.comp measurable_subtype_coe, ?_⟩
  intro P _
  exact pairedRandomization_of_measurable D hmeas P

private lemma anchor_excess_variance_eq_four_minimax (d m N : ℕ) (β cX CX : ℝ)
    (hm : 1 ≤ m) (hN : Even N) (hN2 : 2 ≤ N) :
    anchorExcessVarianceRisk d m N β cX CX =
      4 * anchorMinimaxRisk d m N β cX CX := by
  let S (D : Design m N d) : Set ℝ :=
    {r | ∃ P : Measure (UnitRecord d), ∃ h : AnchorClass P β cX CX,
      r = anchorRisk P h D}
  let T (D : Design m N d) : Set ℝ :=
    {r | ∃ P : Measure (UnitRecord d), ∃ h : AnchorClass P β cX CX,
      r = (N : ℝ) * realVariance
        (experimentLaw (m := m) (N := N) P
          (fun w => pairedCoinLaw (D (designInput w)))) (pairedEstimator N) -
          efficiencyBound P}
  have hsets (D : Design m N d) (hD : MatchingDesignClass D) :
      T D = (4 : ℝ) • S D := by
    ext r
    constructor
    · rintro ⟨P, h, rfl⟩
      refine Set.mem_smul_set.mpr ⟨anchorRisk P h D, ⟨P, h, rfl⟩, ?_⟩
      have hv := (anchorClass_variance_normalization P h D hD hm hN hN2).2
      dsimp only [smul_eq_mul]
      unfold anchorRisk anchorScore
      linarith [hv]
    · intro hr
      obtain ⟨v, ⟨P, h, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hr
      refine ⟨P, h, ?_⟩
      have hv := (anchorClass_variance_normalization P h D hD hm hN hN2).2
      dsimp only [smul_eq_mul]
      unfold anchorRisk anchorScore
      linarith [hv]
  have houter :
      {v : ℝ | ∃ D : Design m N d, MatchingDesignClass D ∧ v = sSup (T D)} =
        (4 : ℝ) • {v : ℝ | ∃ D : Design m N d,
          MatchingDesignClass D ∧ v = sSup (S D)} := by
    ext v
    constructor
    · rintro ⟨D, hD, rfl⟩
      refine Set.mem_smul_set.mpr ⟨sSup (S D), ⟨D, hD, rfl⟩, ?_⟩
      rw [hsets D hD, Real.sSup_smul_of_nonneg (by norm_num)]
    · intro hv
      obtain ⟨u, ⟨D, hD, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hv
      refine ⟨D, hD, ?_⟩
      rw [hsets D hD, Real.sSup_smul_of_nonneg (by norm_num)]
  change sInf {v : ℝ | ∃ D : Design m N d, MatchingDesignClass D ∧ v = sSup (T D)} =
    4 * sInf {v : ℝ | ∃ D : Design m N d, MatchingDesignClass D ∧ v = sSup (S D)}
  rw [houter, Real.sInf_smul_of_nonneg (by norm_num)]
  rfl

-- @node: thm:anchor-class-geometric-minimax
theorem anchor_class_geometric_minimax (d : ℕ) (β cX CX : ℝ)
    (hpars : ValidAnchorParameters d β cX CX) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ m N : ℕ, 1 ≤ m → (hN : Even N) → (hN2 : 2 ≤ N) →
        (∀ P : Measure (UnitRecord d), ∀ h : AnchorClass P β cX CX,
          anchorRisk (m := m) (N := N) P h
            (fun input : PilotSample m d × MainCovariates N d × ℝ =>
              geometricMatching input.2.1 hN hN2) ≤
              C * (N : ℝ) ^ (-2 * β / d)) ∧
        (∀ D : Design m N d, MatchingDesignClass D →
          ∃ P : Measure (UnitRecord d), ∃ h : AnchorClass P β cX CX,
            c * (N : ℝ) ^ (-2 * β / d) ≤ anchorRisk P h D) ∧
        c * (N : ℝ) ^ (-2 * β / d) ≤ anchorMinimaxRisk d m N β cX CX ∧
        anchorMinimaxRisk d m N β cX CX ≤ C * (N : ℝ) ^ (-2 * β / d) ∧
        (∀ D : Design m N d, MatchingDesignClass D →
          ∀ P : Measure (UnitRecord d), ∀ h : AnchorClass P β cX CX,
            (∫ wz, pairedEstimator N wz ∂experimentLaw (m := m) (N := N) P
              (fun w => pairedCoinLaw (D (designInput w)))) = ate P ∧
            (N : ℝ) * realVariance
              (experimentLaw (m := m) (N := N) P
                (fun w => pairedCoinLaw (D (designInput w))))
              (pairedEstimator N) - efficiencyBound P = 4 * anchorRisk P h D) ∧
        anchorExcessVarianceRisk d m N β cX CX =
          4 * anchorMinimaxRisk d m N β cX CX := by
  obtain ⟨c, hc, hlower⟩ := anchor_lower_witness d β cX CX hpars
  let C0 : ℝ := max ((1 / 2 : ℝ) * 2 ^ β * (1 / cX ^ 2) ^ β)
    ((1 / 2 : ℝ) * (32 * (d : ℝ)) ^ β)
  let C : ℝ := max C0 c
  have hC0 : 0 < C0 := by
    dsimp [C0]
    have hdR : 0 < (d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hpars.1)
    exact lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨c, C, hc, le_max_right _ _, ?_⟩
  intro m N hm hN hN2
  have hN1 : 1 ≤ N := by omega
  let Dgeo : Design m N d := fun input => geometricMatching input.2.1 hN hN2
  have hDgeo : MatchingDesignClass Dgeo :=
    geometricMatching_anchor_designClass m d N hN hN2
  have hupper (P : Measure (UnitRecord d)) (h : AnchorClass P β cX CX) :
      anchorRisk P h Dgeo ≤ C * (N : ℝ) ^ (-2 * β / d) := by
    exact (anchor_geometric_risk_bound d m N β cX CX hN hN2 P h).trans
      (mul_le_mul_of_nonneg_right (le_max_left C0 c)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  have hlowerD (D : Design m N d) (hD : MatchingDesignClass D) :=
    hlower m N hm hN1 D hD
  have hminLower : c * (N : ℝ) ^ (-2 * β / d) ≤
      anchorMinimaxRisk d m N β cX CX := by
    unfold anchorMinimaxRisk
    apply le_csInf
    · exact ⟨sSup {r : ℝ | ∃ P : Measure (UnitRecord d),
        ∃ h : AnchorClass P β cX CX, r = anchorRisk P h Dgeo}, Dgeo, hDgeo, rfl⟩
    rintro v ⟨D, hD, rfl⟩
    let S : Set ℝ := {r | ∃ P : Measure (UnitRecord d),
      ∃ h : AnchorClass P β cX CX, r = anchorRisk P h D}
    obtain ⟨P, h, hr⟩ := hlowerD D hD
    have hb : BddAbove S := by
      refine ⟨(1 / 2 : ℝ) * (d : ℝ) ^ β, ?_⟩
      rintro r ⟨P', h', rfl⟩
      exact anchor_risk_le_envelope hN1 P' h' D
    exact hr.trans (le_csSup hb ⟨P, h, rfl⟩)
  have houterBelow : BddBelow
      {v : ℝ | ∃ D : Design m N d, MatchingDesignClass D ∧
        v = sSup {r : ℝ | ∃ P : Measure (UnitRecord d),
          ∃ h : AnchorClass P β cX CX, r = anchorRisk P h D}} := by
    refine ⟨0, ?_⟩
    rintro v ⟨D, hD, rfl⟩
    let S : Set ℝ := {r | ∃ P : Measure (UnitRecord d),
      ∃ h : AnchorClass P β cX CX, r = anchorRisk P h D}
    obtain ⟨P, h, _⟩ := hlowerD D hD
    have hb : BddAbove S := by
      refine ⟨(1 / 2 : ℝ) * (d : ℝ) ^ β, ?_⟩
      rintro r ⟨P', h', rfl⟩
      exact anchor_risk_le_envelope hN1 P' h' D
    exact (anchor_risk_nonnegative P h D).trans (le_csSup hb ⟨P, h, rfl⟩)
  have hsupGeo : sSup {r : ℝ | ∃ P : Measure (UnitRecord d),
      ∃ h : AnchorClass P β cX CX, r = anchorRisk P h Dgeo} ≤
      C * (N : ℝ) ^ (-2 * β / d) := by
    obtain ⟨P0, h0, _⟩ := hlowerD Dgeo hDgeo
    apply csSup_le
    · exact ⟨anchorRisk P0 h0 Dgeo, ⟨P0, h0, rfl⟩⟩
    · rintro r ⟨P, h, rfl⟩
      exact hupper P h
  have hminUpper : anchorMinimaxRisk d m N β cX CX ≤
      C * (N : ℝ) ^ (-2 * β / d) := by
    unfold anchorMinimaxRisk
    exact (csInf_le houterBelow ⟨Dgeo, hDgeo, rfl⟩).trans hsupGeo
  refine ⟨?_, hlowerD, hminLower, hminUpper, ?_,
    anchor_excess_variance_eq_four_minimax d m N β cX CX hm hN hN2⟩
  · intro P h
    exact hupper P h
  · intro D hD P h
    have hv := anchorClass_variance_normalization P h D hD hm hN hN2
    refine ⟨hv.1, ?_⟩
    unfold anchorRisk anchorScore
    dsimp only at hv
    rw [hv.2]
    ring

end CausalSmith.Experimentation.PilotscorePairingFrontier
