import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionLocalInverse
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionExclusionApplication
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionWitnessEmbedding
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.TConfidenceUnionCoverage

/-!
# Non-effective four-margin contraction

A uniform but non-computable local radius and explicit linear modulus for arbitrary PSD covariance
regions.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set
open scoped Matrix.Norms.L2Operator ENNReal Topology
open Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine

-- @node: thm:non-effective-four-margin-contraction
/-- Four true-side margins and one feasible-candidate condition-number bound yield a uniform
non-effective local radius controlling both outer radius and operator-metric diameter. [Under the stated hypotheses](hyp:hp,hm,hc,gamma0_pos,zeta0_pos,zeta0_le_one,one_le_kappabar,one_le_Mbar) [this conclusion](goal) applies. -/
theorem non_effective_four_margin_contraction
    {p m c : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m) (hc : c < m)
    (gamma0 zeta0 kappabar Mbar : ℚ)
    (gamma0_pos : 0 < gamma0) (zeta0_pos : 0 < zeta0) (zeta0_le_one : zeta0 ≤ 1)
    (one_le_kappabar : 1 ≤ kappabar) (one_le_Mbar : 1 ≤ Mbar) :
    ∃ r0 : ℝ, 0 < r0 ∧
      ∀ (W : BackshiftSystem p m c) (V : InferenceWorld p m),
        BackshiftNormalization W →
        (nonnegative_shifts : NonnegativeShifts W) →
        HonestCovarianceModel W →
        W.invariantNoise.PosSemidef →
        (gamma0 : ℝ) ≤ affineSeparation W.dimension_at_least_two W.honest
          W.honest_card W.shifts nonnegative_shifts →
        (zeta0 : ℝ) ≤ normalizationSlack W.structural →
        matrixConditionNumber W.structural ≤ (kappabar : ℝ) →
        matrixScaleBound W.honest W.invariantNoise W.covariance W.shifts ≤ (Mbar : ℝ) →
        CandidateConditionBound (c := c) V.currentRegions (kappabar : ℝ) →
        coverageEvent W V.currentRegions →
        honestRegionRadius V W.honest ⟨W.covariance, W.covariance_psd⟩ ≤
          ENNReal.ofReal r0 →
        ∃ union_nonempty : (confidenceUnion c V).Nonempty,
          opOuterRadius (confidenceUnion c V) union_nonempty W.structural ≤
            ENNReal.ofReal (contractionC0 p (gamma0 : ℝ) (Mbar : ℝ) (kappabar : ℝ)) *
              honestRegionRadius V W.honest ⟨W.covariance, W.covariance_psd⟩ ∧
          Metric.ediam (confidenceUnion c V) ≤
            2 * ENNReal.ofReal
              (contractionC0 p (gamma0 : ℝ) (Mbar : ℝ) (kappabar : ℝ)) *
                honestRegionRadius V W.honest ⟨W.covariance, W.covariance_psd⟩ := by
  classical
  have hp0 : 0 < p := by omega
  have hγ : 0 < (gamma0 : ℝ) := by exact_mod_cast gamma0_pos
  have hζ : 0 < (zeta0 : ℝ) := by exact_mod_cast zeta0_pos
  have hκ : 1 ≤ (kappabar : ℝ) := by exact_mod_cast one_le_kappabar
  have hM : 0 < (Mbar : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast one_le_Mbar)
  by_cases hcount : 3 ≤ m - 2 * c
  · let L := contractionL0 p (kappabar : ℝ)
    have hL : 1 ≤ L := one_le_conditionRoot hp0 hκ
    let ρ := pairwiseLocalRadius p (Mbar : ℝ) (gamma0 : ℝ) L (kappabar : ℝ)
    have hρ : 0 < ρ := pairwiseLocalRadius_pos hp0 hM hγ hL
      (lt_of_lt_of_le zero_lt_one hκ)
    let R := contractionEmbeddingRadius p (kappabar : ℝ) (Mbar : ℝ)
    obtain ⟨ε₀, hε₀, htol⟩ := exists_uniformContractionLocalTolerance hp hc hcount
      (κ := (kappabar : ℝ)) (M := (Mbar : ℝ)) (R := R) hζ hγ hρ
    let q := pairwiseResidualRadius p (Mbar : ℝ) (gamma0 : ℝ) L
    have hq : 0 < q := pairwiseResidualRadius_pos hM hγ hL
    let r0 := min 1 (min (ε₀ / (m + 1 : ℝ)) (q / (2 * L ^ 2)))
    have hmden : 0 < (m + 1 : ℝ) := by positivity
    have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
    have hr0 : 0 < r0 := by
      dsimp [r0]
      positivity
    refine ⟨r0, hr0, ?_⟩
    intro W V backshift_normalization nonnegative_shifts honest_covariance_model
      invariant_noise_psd affine_margin slack_margin condition_margin scale_margin
      candidate_bound covered radius_small
    have htrue_mem := confidence_union_coverage W V backshift_normalization
      nonnegative_shifts honest_covariance_model invariant_noise_psd covered
    let union_nonempty : (confidenceUnion c V).Nonempty := ⟨W.structural, htrue_mem⟩
    let rad := honestRegionRadius V W.honest ⟨W.covariance, W.covariance_psd⟩
    have hrad_top : rad ≠ ⊤ := by
      intro htop
      change rad ≤ ENNReal.ofReal r0 at radius_small
      rw [htop] at radius_small
      simpa using radius_small
    let r : ℝ := rad.toReal
    have hr : 0 ≤ r := ENNReal.toReal_nonneg
    have hr_le_r0 : r ≤ r0 := by
      have := ENNReal.toReal_mono (by simp) radius_small
      simpa [r, rad, ENNReal.toReal_ofReal hr0.le] using this
    have hr_one : r ≤ 1 := hr_le_r0.trans (min_le_left _ _)
    have hr_eps : (m : ℝ) * r ≤ ε₀ := by
      have hsmall := hr_le_r0.trans (min_le_right _ _)
      have hdiv := hsmall.trans (min_le_left _ _)
      have hmle : (m : ℝ) ≤ m + 1 := by norm_num
      calc
        (m : ℝ) * r ≤ (m : ℝ) * (ε₀ / (m + 1 : ℝ)) := by gcongr
        _ ≤ (m + 1 : ℝ) * (ε₀ / (m + 1 : ℝ)) := by
          gcongr
        _ = ε₀ := by field_simp
    have hr_small : 2 * L ^ 2 * r ≤ q := by
      have hsmall := hr_le_r0.trans (min_le_right _ _)
      have hdiv := hsmall.trans (min_le_right _ _)
      have hden : 0 < 2 * L ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hLpos)
      calc
        2 * L ^ 2 * r ≤ 2 * L ^ 2 * (q / (2 * L ^ 2)) := by gcongr
        _ = q := by field_simp
    have hpoint : ∀ A ∈ confidenceUnion c V,
        ‖A - W.structural‖ ≤
          contractionC0 p (gamma0 : ℝ) (Mbar : ℝ) (kappabar : ℝ) * r := by
      intro A hA
      obtain ⟨X⟩ := exists_confidenceCandidateWitness (c := c) V hA
      have hover : m - 2 * c ≤ (W.honest ∩ X.fitted).card :=
        overlap_card_lower_bound W.honest X.fitted (by simp [W.honest_card])
          (by simp [X.fitted_card])
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hover
      have hSH : S ⊆ W.honest := fun e he => (Finset.mem_inter.mp (hSsub he)).1
      have hSX : S ⊆ X.fitted := fun e he => (Finset.mem_inter.mp (hSsub he)).2
      have hSpower : S ∈ W.honest.powersetCard (W.honest.card - c) := by
        rw [Finset.mem_powersetCard]
        refine ⟨hSH, ?_⟩
        rw [hScard, W.honest_card]
        simp only [honestCount]
        omega
      haveI : Nonempty {e // e ∈ S} :=
        Finset.nonempty_coe_sort.mpr (Finset.card_pos.mp (by omega))
      have herr : ∀ e ∈ S, ‖X.covariance e - W.covariance e‖ ≤ r := by
        intro e he
        have hed := edist_le_honestRegionRadius V W.honest
          ⟨W.covariance, W.covariance_psd⟩ (hSH he) (X.covariance_mem e)
        rw [edist_dist, dist_eq_norm] at hed
        have hof : ENNReal.ofReal ‖X.covariance e - W.covariance e‖ ≤
            ENNReal.ofReal r := by
          rw [ENNReal.ofReal_toReal hrad_top]
          exact hed
        exact (ENNReal.ofReal_le_ofReal_iff hr).mp hof
      have hAcond := matrixConditionNumber_le_of_mem_confidenceUnion V candidate_bound hA
      let z := retainedUniformContractionAmbient W X S
      have hz : z ∈ uniformContractionFeasible S (zeta0 : ℝ) (kappabar : ℝ)
          (Mbar : ℝ) (gamma0 : ℝ) R := by
        exact retainedUniformContractionAmbient_mem_feasible_of_affineSeparation hp W X S
          hκ hγ backshift_normalization nonnegative_shifts honest_covariance_model
          invariant_noise_psd slack_margin condition_margin hAcond scale_margin affine_margin
          hSpower hSX herr hr hr_one
      have hres : uniformContractionResidual S z ≤ ε₀ := by
        calc
          uniformContractionResidual S z ≤ S.card * r :=
            uniformContractionResidual_retained_le_card_mul W X S herr
          _ ≤ (m : ℝ) * r := by
            gcongr
            simpa [Environment] using Finset.card_le_univ (s := S)
          _ ≤ ε₀ := hr_eps
      have hlocal : InReferenceNeighborhood ρ W.structural A := by
        simpa [z, R, ρ, retainedUniformContractionAmbient] using htol S z (by
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ S, hScard⟩) hz hres
      exact opNorm_candidate_sub_structural_le_contractionC0 hp W X S hSH hSX hSpower
        backshift_normalization honest_covariance_model nonnegative_shifts hγ hM hκ hr
        affine_margin scale_margin condition_margin hAcond herr (by simpa [L, q] using hr_small)
        (by simpa [L, ρ] using hlocal)
    have houter := opOuterRadius_le_of_forall_opNorm (confidenceUnion c V) union_nonempty
      W.structural (contractionC0 p (gamma0 : ℝ) (Mbar : ℝ) (kappabar : ℝ)) rad
      hrad_top (by unfold contractionC0 contractionK0; positivity) (by simpa [r, rad] using hpoint)
    refine ⟨union_nonempty, houter, ?_⟩
    calc
      Metric.ediam (confidenceUnion c V) ≤
          2 * opOuterRadius (confidenceUnion c V) union_nonempty W.structural :=
        ediam_le_two_mul_opOuterRadius (confidenceUnion c V) union_nonempty W.structural
      _ ≤ 2 * (ENNReal.ofReal
          (contractionC0 p (gamma0 : ℝ) (Mbar : ℝ) (kappabar : ℝ)) * rad) := by
        gcongr
      _ = 2 * ENNReal.ofReal
          (contractionC0 p (gamma0 : ℝ) (Mbar : ℝ) (kappabar : ℝ)) * rad := by
        rw [mul_assoc]
  · refine ⟨1, by norm_num, ?_⟩
    intro W V backshift_normalization nonnegative_shifts honest_covariance_model
      invariant_noise_psd affine_margin _slack_margin _condition_margin _scale_margin
      _candidate_bound _covered _radius_small
    have hsmall : W.honest.card - c < 3 := by
      rw [W.honest_card]
      simp only [honestCount]
      omega
    unfold affineSeparation at affine_margin
    rw [if_pos hsmall] at affine_margin
    exfalso
    linarith

-- keep: public asymptotic corollary of the headline contraction theorem.
/-- Along covered outcomes with the same candidate condition-number bound, honest-region radii
converging to zero force both confidence-union radii to converge to zero. [Under the stated hypotheses](hyp:hp,hm,hc,gamma0_pos,zeta0_pos,zeta0_le_one,one_le_kappabar,one_le_Mbar,honest_covariance_model,affine_margin,slack_margin,condition_margin,scale_margin,candidate_bound,covered) [this conclusion](goal) applies. -/
lemma non_effective_four_margin_convergence
    {p m c : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m) (hc : c < m)
    (gamma0 zeta0 kappabar Mbar : ℚ)
    (gamma0_pos : 0 < gamma0) (zeta0_pos : 0 < zeta0) (zeta0_le_one : zeta0 ≤ 1)
    (one_le_kappabar : 1 ≤ kappabar) (one_le_Mbar : 1 ≤ Mbar)
    (W : BackshiftSystem p m c)
    (backshift_normalization : BackshiftNormalization W)
    (nonnegative_shifts : NonnegativeShifts W)
    (honest_covariance_model : HonestCovarianceModel W)
    (invariant_noise_psd : W.invariantNoise.PosSemidef)
    (affine_margin : (gamma0 : ℝ) ≤ affineSeparation W.dimension_at_least_two
      W.honest W.honest_card W.shifts nonnegative_shifts)
    (slack_margin : (zeta0 : ℝ) ≤ normalizationSlack W.structural)
    (condition_margin : matrixConditionNumber W.structural ≤ (kappabar : ℝ))
    (scale_margin :
      matrixScaleBound W.honest W.invariantNoise W.covariance W.shifts ≤ (Mbar : ℝ))
    (V : ℕ → InferenceWorld p m)
    (candidate_bound : ∀ i,
      CandidateConditionBound (c := c) (V i).currentRegions (kappabar : ℝ))
    (covered : ∀ i, coverageEvent W (V i).currentRegions)
    (radius_tends_to_zero :
      Filter.Tendsto
        (fun i ↦ honestRegionRadius (V i) W.honest
          ⟨W.covariance, W.covariance_psd⟩)
        Filter.atTop (nhds 0)) :
    ∃ union_nonempty : ∀ i, (confidenceUnion c (V i)).Nonempty,
      Filter.Tendsto
          (fun i ↦ opOuterRadius (confidenceUnion c (V i))
            (union_nonempty i) W.structural)
          Filter.atTop (nhds 0) ∧
        Filter.Tendsto
          (fun i ↦ Metric.ediam (confidenceUnion c (V i)))
          Filter.atTop (nhds 0) := by
  obtain ⟨r0, hr0, hcontraction⟩ :=
    non_effective_four_margin_contraction hp hm hc gamma0 zeta0 kappabar Mbar
      gamma0_pos zeta0_pos zeta0_le_one one_le_kappabar one_le_Mbar
  let radius : ℕ → ℝ≥0∞ := fun i ↦
    honestRegionRadius (V i) W.honest ⟨W.covariance, W.covariance_psd⟩
  let C : ℝ≥0∞ :=
    ENNReal.ofReal (contractionC0 p (gamma0 : ℝ) (Mbar : ℝ) (kappabar : ℝ))
  have hradius : Filter.Tendsto radius Filter.atTop (nhds 0) := radius_tends_to_zero
  have heventually_small : ∀ᶠ i in Filter.atTop, radius i ≤ ENNReal.ofReal r0 := by
    rw [ENNReal.tendsto_nhds_zero] at hradius
    exact hradius (ENNReal.ofReal r0) (ENNReal.ofReal_pos.mpr hr0)
  have hnonempty : ∀ i, (confidenceUnion c (V i)).Nonempty := fun i ↦
    ⟨W.structural, confidence_union_coverage W (V i) backshift_normalization
      nonnegative_shifts honest_covariance_model invariant_noise_psd (covered i)⟩
  have hbounds : ∀ᶠ i in Filter.atTop,
      opOuterRadius (confidenceUnion c (V i)) (hnonempty i) W.structural ≤ C * radius i ∧
        Metric.ediam (confidenceUnion c (V i)) ≤ 2 * C * radius i := by
    filter_upwards [heventually_small] with i hi
    simpa [radius, C] using
      (hcontraction W (V i) backshift_normalization nonnegative_shifts
        honest_covariance_model invariant_noise_psd affine_margin slack_margin condition_margin
        scale_margin (candidate_bound i) (covered i) hi).choose_spec
  have hC : C ≠ ⊤ := by simp [C]
  have hC_radius : Filter.Tendsto (fun i ↦ C * radius i) Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hradius (Or.inr hC)
  have htwoC_radius :
      Filter.Tendsto (fun i ↦ 2 * C * radius i) Filter.atTop (nhds 0) := by
    have htwoC : 2 * C ≠ (⊤ : ℝ≥0∞) := ENNReal.mul_ne_top (by simp) hC
    simpa [mul_assoc] using ENNReal.Tendsto.const_mul hradius (Or.inr htwoC)
  refine ⟨hnonempty, ?_, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC_radius
      (Filter.Eventually.of_forall fun _ ↦ bot_le) (hbounds.mono fun _ hi ↦ hi.1)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htwoC_radius
      (Filter.Eventually.of_forall fun _ ↦ bot_le) (hbounds.mono fun _ hi ↦ hi.2)

end CausalSmith.ExactID.RobustBackshiftUniformDistance
