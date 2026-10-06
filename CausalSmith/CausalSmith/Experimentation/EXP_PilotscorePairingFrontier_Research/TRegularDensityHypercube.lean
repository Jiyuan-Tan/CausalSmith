module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedDensity
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedDensityTransfer
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedConstruction
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedGeometryBounds
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedCardinality
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedBranches
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedBranchAssembly
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedCoverage
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedFoldPushforward
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedFubini
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedFubiniDensity
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedIntervalPartition
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedCellPushforward
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedDensityAssembly
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedReflectedDensity
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedReflectedReindex
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSliceAgreement
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSliceMeasurability
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSliceLaw
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedJointDensity
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedCubeDensity
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedCubeBounds
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedRegularPushforward
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedModelAssembly
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedAdditiveRepresentation
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedKLAssembly
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedHolderBounds
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedScalarLipschitz
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedHolderScore
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedModelConstruction
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedLinearFamily
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedFamilyPackaging
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSmallMesh
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedPerturbedCoverage
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSignedCoverage
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSignedEnvelope
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSignedPushforward
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedScoreAlgebra
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedScoreLocality
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedPushforward
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedPerturbedPushforward
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.Information
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.Geometry
public import Mathlib.MeasureTheory.Measure.Support

/-! # Radius necessity and regular-density likelihood hypercube -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

-- @node: regular_score_interval_in_support
lemma regular_score_interval_in_support {d : ℕ} {P : Measure (UnitRecord d)}
    {g : XSpace d → ℝ} {cg Cg : ℝ}
    (hP : IsProbabilityMeasure P) (hcg : 0 < cg)
    (hreg : RegularScorePushforward P g cg Cg) :
    scoreInterval ⊆ (P.map (fun u => g u.1)).support := by
  let ν : Measure ℝ := P.map (fun u => g u.1)
  let ρ : Measure ℝ := (volume : Measure ℝ).restrict scoreInterval
  letI : IsProbabilityMeasure P := hP
  haveI : SFinite ν := inferInstance
  haveI : SigmaFinite ρ := inferInstance
  have hreg' : ν ≪ ρ ∧
      ∀ᵐ t ∂ρ, cg ≤ (ν.rnDeriv ρ t).toReal ∧
        (ν.rnDeriv ρ t).toReal ≤ Cg := by
    simpa [RegularScorePushforward, ν, ρ] using hreg
  have hpos : ∀ᵐ t ∂ρ, ν.rnDeriv ρ t ≠ 0 := by
    filter_upwards [hreg'.2] with t ht
    intro hz
    simp [hz] at ht
    linarith
  have hρν : ρ ≪ ν := by
    rw [← Measure.withDensity_rnDeriv_eq ν ρ hreg'.1]
    exact withDensity_absolutelyContinuous' (Measure.measurable_rnDeriv ν ρ).aemeasurable
      hpos
  have hmid : Set.Ioo (1 / 4 : ℝ) (3 / 4 : ℝ) ⊆ ν.support := by
    intro t ht
    apply hρν.support_mono
    apply Measure.interior_inter_support
    constructor
    · simpa [scoreInterval, interior_Icc] using ht
    · simpa using (show t ∈ (volume : Measure ℝ).support by
        simp [Measure.support_eq_univ])
  have hclosed : IsClosed ν.support := Measure.isClosed_support
  have hcl : Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) ⊆ ν.support := by
    rw [← closure_Ioo (by norm_num : (1 / 4 : ℝ) ≠ 3 / 4)]
    exact closure_minimal hmid hclosed
  simpa [scoreInterval, ν] using hcl

private lemma exists_folded_static_parameters {d : ℕ} {L cg Cg : ℝ}
    (hd : 1 ≤ d) (hL : 1 / 2 < L) (hcg : cg < 2) (hCg : 2 < Cg) :
    ∃ κ ε A Bconst : ℝ,
      0 < κ ∧ 0 < ε ∧ 0 < A ∧ 0 < Bconst ∧
      Bconst * ε ≤ 1 ∧
      A * ε ≤ (min (1 - cg / 2) (Cg / 2 - 1)) / 4 ∧
      1 / 2 + A * κ < L ∧
      1 / 2 + 96 * (d : ℝ) * ε ≤ L ∧
      256 * ε ≤ min (2 - cg) (Cg - 2) ∧
      ε ≤ 1 / 128 ∧
      (128 * (d : ℝ)) * ε ≤ 1 ∧
      1 / 2 + (128 * (d : ℝ)) * κ < L ∧
      24 * ε < min (1 - cg / 2) (Cg / 2 - 1) := by
  let δ : ℝ := min (1 - cg / 2) (Cg / 2 - 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by linarith)
  -- The transverse product has up to `d` simultaneous slope contributions.
  -- This dimension-dependent constant dominates its `32*d` mesh modulus.
  let D : ℝ := 128 * (d : ℝ)
  let η : ℝ := min (min 1 δ) (L - 1 / 2)
  refine ⟨(L - 1 / 2) / (4 * D), η / (8 * D), D, D, ?_⟩
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : 0 < D := by dsimp [D]; positivity
  have hminpos : 0 < min 1 δ := lt_min zero_lt_one hδ
  have hηpos : 0 < η := by
    dsimp [η]
    exact lt_min hminpos (sub_pos.mpr hL)
  have hηone : η ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hηdelta : η ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  have hηgap : η ≤ L - 1 / 2 := min_le_right _ _
  constructor
  · exact div_pos (sub_pos.mpr hL) (mul_pos (by norm_num) hD)
  constructor
  · exact div_pos hηpos (mul_pos (by norm_num) hD)
  constructor
  · exact hD
  constructor
  · exact hD
  constructor
  · have hcancel : D * (η / (8 * D)) = η / 8 := by
      field_simp
    rw [hcancel]
    nlinarith
  constructor
  · have hcancel : D * (η / (8 * D)) = η / 8 := by
      field_simp
    rw [hcancel]
    nlinarith
  constructor
  · have hcancel : D * ((L - 1 / 2) / (4 * D)) = (L - 1 / 2) / 4 := by
      field_simp
    rw [hcancel]
    nlinarith
  constructor
  · have hcancel : 96 * (d : ℝ) * (η / (8 * D)) = 3 * η / 32 := by
      dsimp [D]
      field_simp
      ring
    rw [hcancel]
    nlinarith
  constructor
  · have hcancel : 256 * (η / (8 * D)) = η / (4 * (d : ℝ)) := by
      dsimp [D]
      field_simp
      norm_num
    have hdiv : η / (4 * (d : ℝ)) ≤ η / 4 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)).2
      nlinarith
    have hminscale : min (2 - cg) (Cg - 2) = 2 * δ := by
      dsimp [δ]
      rcases le_total (1 - cg / 2) (Cg / 2 - 1) with hab | hba
      · rw [min_eq_left hab]
        rw [min_eq_left] <;> nlinarith
      · rw [min_eq_right hba]
        rw [min_eq_right] <;> nlinarith
    rw [hcancel, hminscale]
    exact hdiv.trans (by nlinarith)
  constructor
  · apply (div_le_iff₀ (mul_pos (by norm_num) hD)).2
    have hD128 : (128 : ℝ) ≤ D := by dsimp [D]; nlinarith
    nlinarith
  constructor
  · have hcancel : D * (η / (8 * D)) = η / 8 := by field_simp
    dsimp [D]
    rw [show (128 * (d : ℝ)) * (η / (8 * D)) = D * (η / (8 * D)) by rfl,
      hcancel]
    nlinarith
  constructor
  · have hcancel : D * ((L - 1 / 2) / (4 * D)) = (L - 1 / 2) / 4 := by
      field_simp
    dsimp [D]
    rw [show (128 * (d : ℝ)) * ((L - 1 / 2) / (4 * D)) =
      D * ((L - 1 / 2) / (4 * D)) by rfl, hcancel]
    nlinarith
  · have hcancel : 24 * (η / (8 * D)) = 3 * η / D := by
      field_simp
      norm_num
    rw [hcancel]
    apply (div_lt_iff₀ hD).2
    have hD128 : (128 : ℝ) ≤ D := by dsimp [D]; nlinarith
    have hmul : 128 * δ ≤ D * δ :=
      mul_le_mul_of_nonneg_right hD128 hδ.le
    nlinarith

-- @node: thm:regular-density-hypercube
theorem regular_density_hypercube (d : ℕ) (β L cX CX cg Cg : ℝ)
    (hpars : ValidClassParameters d β L cX CX cg Cg) :
    ((∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
        RegularScoreModel P g L β cX CX cg Cg) →
      1 / (2 * (d : ℝ) ^ (β / 2)) ≤ L) ∧
    (1 / 2 < L →
      ∃ h0 c0 c1 C1 C2 κ ε A Bconst : ℝ,
        0 < h0 ∧ 0 < c0 ∧ 0 < c1 ∧ 0 < C1 ∧ 0 < C2 ∧
        0 < κ ∧ 0 < ε ∧ 0 < A ∧ 0 < Bconst ∧
        ∀ q : ℕ, 0 < q → (q : ℝ)⁻¹ ≤ h0 → -- @realizes q(positive reciprocal mesh integer)
          (β < 1 → FoldedParameterConditions q β L cg Cg (q : ℝ)⁻¹ κ ε A Bconst) ∧
          HypercubeFamily d β L cX CX cg Cg (q : ℝ)⁻¹ c0 c1 C1 C2 κ ε A Bconst) := by
  constructor
  · rintro ⟨P, g, hmodel⟩
    rcases hpars with ⟨hd, hβpos, _, hLpos, _, _, _, hcg, _, _⟩
    let ν : Measure ℝ := P.map (fun u => g u.1)
    let S : Set ℝ := g '' cube d
    let B : ℝ := L * (d : ℝ) ^ (β / 2)
    have hβ : 0 ≤ β := hβpos.le
    have hL : 0 ≤ L := hLpos.le
    have hbottom : (1 / 4 : ℝ) ∈ ν.support :=
      regular_score_interval_in_support hmodel.covariate_density.1
        hcg hmodel.regular_score_pushforward
        (by norm_num [scoreInterval])
    have htop : (3 / 4 : ℝ) ∈ ν.support :=
      regular_score_interval_in_support hmodel.covariate_density.1
        hcg hmodel.regular_score_pushforward
        (by norm_num [scoreInterval])
    have hνne : ν ≠ 0 := by
      intro hz
      simp [hz] at hbottom
    have hq : AEMeasurable (fun u : UnitRecord d => g u.1) P :=
      AEMeasurable.of_map_ne_zero hνne
    have hcubeae : ∀ᵐ u ∂P, u.1 ∈ cube d := by
      have hc : ∀ᵐ x ∂cubeMeasure d, x ∈ cube d := by
        have hmeas : MeasurableSet (cube d) := by
          exact MeasurableSet.univ_pi' (fun _ : Fin d => measurableSet_Icc)
        exact ae_restrict_mem hmeas
      have hc' : ∀ᵐ x ∂P.map Prod.fst, x ∈ cube d :=
        hmodel.covariate_density.2.1.ae_le hc
      exact ae_of_ae_map (by fun_prop) hc'
    have hSae : ∀ᵐ t ∂ν, t ∈ closure S := by
      apply (ae_map_iff hq isClosed_closure.measurableSet).2
      filter_upwards [hcubeae] with u hu
      exact subset_closure ⟨u.1, hu, rfl⟩
    have hsupp : ν.support ⊆ closure S :=
      Measure.support_subset_of_isClosed isClosed_closure hSae
    have hbound (a b : ℝ) (ha : a ∈ S) (hb : b ∈ S) : |a - b| ≤ B := by
      rcases ha with ⟨x, hx, rfl⟩
      rcases hb with ⟨y, hy, rfl⟩
      exact holder_score_cube_oscillation g hL hβ hmodel.holder_score x y hx hy
    have hbound_top (a : ℝ) (ha : a ∈ S) : |a - 3 / 4| ≤ B := by
      have hclosed : IsClosed {b : ℝ | |a - b| ≤ B} := by
        exact isClosed_le (by fun_prop : Continuous fun b : ℝ => |a - b|) continuous_const
      have hsub : S ⊆ {b : ℝ | |a - b| ≤ B} :=
        fun b hb => hbound a b ha hb
      exact closure_minimal hsub hclosed (hsupp htop)
    have hclosed : IsClosed {a : ℝ | |a - 3 / 4| ≤ B} := by
      exact isClosed_le (by fun_prop : Continuous fun a : ℝ => |a - 3 / 4|) continuous_const
    have hsub : S ⊆ {a : ℝ | |a - 3 / 4| ≤ B} :=
      fun a ha => hbound_top a ha
    have hgap : (1 / 2 : ℝ) ≤ B := by
      have hh := closure_minimal hsub hclosed (hsupp hbottom)
      norm_num at hh ⊢
      exact hh
    have hdpos : 0 < (d : ℝ) ^ (β / 2) := by positivity
    dsimp [B] at hgap
    apply (div_le_iff₀ (by positivity : 0 < 2 * (d : ℝ) ^ (β / 2))).2
    nlinarith
  · intro hL
    have hd : 1 ≤ d := hpars.1
    have hbeta0 : 0 < β := hpars.2.1
    have hbeta1 : β ≤ 1 := hpars.2.2.1
    have hcg : cg < 2 := hpars.2.2.2.2.2.2.2.2.1
    have hCg : 2 < Cg := hpars.2.2.2.2.2.2.2.2.2
    obtain ⟨κ, ε, A, Bconst, hκ, hε, hA, hB, hBε, hAε, hAκ,
      hlinearHolder, hlinearError, hε128, hDε, hDκ, hδε⟩ :=
      exists_folded_static_parameters hd hL hcg hCg
    let c0 : ℝ := (1 / 16 : ℝ) ^ d
    let c1 : ℝ := min (ε * κ / 2) ε
    let C2 : ℝ := 8 * ε ^ 2 * κ ^ 2 + 32 * ε ^ 2
    have hc0 : 0 < c0 := by dsimp [c0]; positivity
    have hc1 : 0 < c1 := by
      dsimp [c1]
      exact lt_min (by positivity) hε
    have hC2 : 0 < C2 := by
      dsimp [C2]
      nlinarith [sq_pos_of_pos hε, sq_nonneg κ]
    by_cases hbeta : β < 1
    · let δ : ℝ := min (1 - cg / 2) (Cg / 2 - 1)
      obtain ⟨h0, hh0, hthreshold⟩ := exists_folded_power_threshold (delta := δ)
        hbeta0 hbeta hκ hε.le (by simpa [δ] using hδε)
      refine ⟨h0, c0, c1, 1, C2, κ, ε, A, Bconst,
        hh0, hc0, hc1, by norm_num, hC2, hκ, hε, hA, hB, ?_⟩
      intro q hq hhq
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have hh : 0 < (q : ℝ)⁻¹ := inv_pos.mpr hqR
      obtain ⟨h24, hscalePow, herrorPow, hampPow⟩ :=
        hthreshold (q : ℝ)⁻¹ hh hhq
      have hq24 : 24 ≤ q := by
        rw [inv_eq_one_div] at h24
        have hi : (1 : ℝ) ≤ (1 / 24) * q :=
          (div_le_iff₀ hqR).mp h24
        exact_mod_cast (show (24 : ℝ) ≤ q by nlinarith)
      have han := folded_analytic_bounds_of_power_bounds hh hbeta0 hbeta hκ hε.le
        hscalePow herrorPow hampPow
      constructor
      · intro _
        exact ⟨hq, rfl, hbeta0, hbeta, hκ, hε, hA, hB, hBε, hAε,
          hAκ, han.1, han.2.1⟩
      · obtain ⟨K, Q, psi, B, hgeo⟩ := exists_foldedGeometry (lt_of_lt_of_le (by omega) hd) q hq
        simpa [c0, c1, C2] using hgeo.hypercubeFamily hq24 hpars hκ hε hε128 hDε
          (fun _ => hDκ.le) (fun _ => han.1) (fun _ => han.2.1)
          (fun _ => han.2.2) (fun heq => by linarith)
          (fun heq => by linarith)
    · have hbetaEq : β = 1 := le_antisymm hbeta1 (not_lt.mp hbeta)
      subst β
      refine ⟨1 / 24, c0, c1, 1, C2, κ, ε, A, Bconst,
        by norm_num, hc0, hc1, by norm_num, hC2, hκ, hε, hA, hB, ?_⟩
      intro q hq hhq
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have hq24 : 24 ≤ q := by
        rw [inv_eq_one_div] at hhq
        have hi : (1 : ℝ) ≤ (1 / 24) * q :=
          (div_le_iff₀ hqR).mp hhq
        exact_mod_cast (show (24 : ℝ) ≤ q by nlinarith)
      constructor
      · intro hfalse
        exact (lt_irrefl (1 : ℝ) hfalse).elim
      · obtain ⟨K, Q, psi, B, hgeo⟩ := exists_foldedGeometry
          (lt_of_lt_of_le (by omega) hd) q hq
        simpa [c0, c1, C2] using hgeo.hypercubeFamily hq24 hpars hκ hε hε128 hDε
          (fun hfalse => (lt_irrefl (1 : ℝ) hfalse).elim)
          (fun hfalse => (lt_irrefl (1 : ℝ) hfalse).elim)
          (fun hfalse => (lt_irrefl (1 : ℝ) hfalse).elim)
          (fun hfalse => (lt_irrefl (1 : ℝ) hfalse).elim)
          (fun _ => hlinearHolder) (fun _ => hlinearError)

end CausalSmith.Experimentation.PilotscorePairingFrontier
