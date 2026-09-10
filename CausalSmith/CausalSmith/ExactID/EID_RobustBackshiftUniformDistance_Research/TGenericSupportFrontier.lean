import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.GenericAffineOccupancy
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.TSharpReplacementRadius

/-!
# Generic sparse-support frontier

The almost-sure support-incidence formula and its uniform robust-identification criterion.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open MeasureTheory Set

/-- The finite support-pattern inequality from the generic occupancy formula. -/
def supportFrontierCriterion {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool) (c : ℕ) : Prop :=
  ∀ k l : Fin p, k < l → genericOccupancy I Z k l < I.card - c

-- @node: prop:generic-support-frontier
/-- On one probability-one event the occupancy formula holds simultaneously and the finite
support inequality is equivalent to uniform singleton recovery over the full PSD model class. [Under the stated hypotheses](hyp:hp,hm,hc,hH) [this conclusion](goal) applies. -/
theorem generic_support_frontier {Ωsample : Type*} [MeasurableSpace Ωsample]
    (μ : Measure Ωsample) [IsProbabilityMeasure μ]
    {p m c : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m) (hc : c < m)
    (H : Finset (Environment m))
    (hH : H.card = honestCount m c) (Z : Environment m → Fin p → Bool)
    (a : Ωsample → Environment m → Fin p → ℝ)
    (generic_active_amplitudes : GenericActiveAmplitudes H Z μ a) :
    ∀ᵐ ω ∂μ,
      (∀ k l : Fin p, k < l →
        maxLineOccupancy H (fun e j ↦ if Z e j then a ω e j else 0) k l =
          genericOccupancy H Z k l) ∧
      (supportFrontierCriterion H Z c ↔
        ∀ W : BackshiftSystem p m c,
          W.honest = H →
          SupportFactorization H Z (a ω) W.shifts →
          BackshiftNormalization W → NonnegativeShifts W → HonestCovarianceModel W →
          W.invariantNoise.PosSemidef →
          compatibleSet p m c ⟨W.covariance, W.covariance_psd⟩ = {W.structural}) ∧
      (¬ supportFrontierCriterion H Z c →
        ∃ (W : BackshiftSystem p m c) (D' : RealMatrix p),
          W.honest = H ∧ SupportFactorization H Z (a ω) W.shifts ∧
          BackshiftNormalization W ∧ NonnegativeShifts W ∧ HonestCovarianceModel W ∧
          W.invariantNoise.PosDef ∧ (∀ e, (W.covariance e).PosDef) ∧
          D' ≠ W.structural ∧
          W.structural ∈ compatibleSet p m c ⟨W.covariance, W.covariance_psd⟩ ∧
          D' ∈ compatibleSet p m c ⟨W.covariance, W.covariance_psd⟩) ∧
      (supportFrontierCriterion H Z c → 2 * c + 3 ≤ m) ∧
      (2 * c + 3 ≤ m →
        ∃ Zgood : Environment m → Fin p → Bool,
          (∀ e k, Zgood e k = true) ∧ supportFrontierCriterion H Zgood c) := by
  filter_upwards
    [generic_affine_occupancy hp H Z a μ generic_active_amplitudes,
      genericActiveAmplitudes_ae_positive H Z a μ generic_active_amplitudes]
    with ω hoccupancy hpositive
  have hmasked (W : BackshiftSystem p m c) (hWH : W.honest = H)
      (hfactor : SupportFactorization H Z (a ω) W.shifts) :
      ∀ k l : Fin p, k < l →
        maxLineOccupancy W.honest W.shifts k l = genericOccupancy H Z k l := by
    intro k l hkl
    calc
      maxLineOccupancy W.honest W.shifts k l =
          maxLineOccupancy H (fun e j ↦ if Z e j then a ω e j else 0) k l := by
            rw [hWH]
            apply maxLineOccupancy_congr_on
            intro e he
            funext j
            exact hfactor.1 e he j
      _ = genericOccupancy H Z k l := hoccupancy k l hkl
  let s0 : Environment m → Fin p → ℝ := fun e j ↦
    if e ∈ H then if Z e j then a ω e j else 0 else 0
  have hs0 : ∀ e j, 0 ≤ s0 e j := by
    intro e j
    by_cases he : e ∈ H
    · by_cases hZ : Z e j = true
      · exact le_of_lt (by
          simpa [s0, he, hZ, activeProjection] using hpositive ⟨(e, j), he, hZ⟩)
      · simp [s0, he, hZ]
    · simp [s0, he]
  let Sigma0 : Environment m → RealMatrix p := fun e ↦ 1 + Matrix.diagonal (s0 e)
  have hSigma0pd : ∀ e, (Sigma0 e).PosDef := by
    intro e
    exact Matrix.PosDef.one.add_posSemidef (Matrix.PosSemidef.diagonal (hs0 e))
  let W0 : BackshiftSystem p m c :=
    { dimension_at_least_two := hp
      environment_nonempty := hm
      corruption_lt := hc
      honest := H
      honest_card := hH
      covariance := Sigma0
      covariance_psd := fun e ↦ (hSigma0pd e).posSemidef
      structural := 1
      structural_invertible := by simp
      invariantNoise := 1
      invariantNoise_symmetric := by simp
      shifts := s0 }
  have hW0H : W0.honest = H := rfl
  have hW0factor : SupportFactorization H Z (a ω) W0.shifts := by
    constructor
    · intro e he j
      simp [W0, s0, he]
    · intro e he j hZ
      exact hpositive ⟨(e, j), he, hZ⟩
  have hW0norm : BackshiftNormalization W0 := by
    dsimp [BackshiftNormalization, W0, admissibleSet]
    refine ⟨by simp, by simp, ?_⟩
    rw [sub_self]
    unfold cycleProduct
    have hz : simpleCycleWeight (0 : RealMatrix p) = fun _ ↦ 0 := by
      funext σ
      by_cases hσ : σ.IsCycle ∧ 2 ≤ σ.support.card
      · simp only [simpleCycleWeight, if_pos hσ]
        obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < σ.support.card)
        rw [Finset.prod_eq_zero hi]
        simp
      · simp [simpleCycleWeight, hσ]
    rw [hz]
    generalize (Finset.univ : Finset (Equiv.Perm (Fin p))) = S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert σ S hσ ih => simp [Finset.fold_insert hσ, ih]
  have hW0nonneg : NonnegativeShifts W0 := by
    intro e he j
    exact hs0 e j
  have hW0model : HonestCovarianceModel W0 := by
    intro e he
    simp [W0, Sigma0]
  have hW0psd : W0.invariantNoise.PosSemidef := Matrix.PosDef.one.posSemidef
  have hdelta_of_fail (hfail : ¬ supportFrontierCriterion H Z c) :
      envDeletionDistance W0.honest W0.shifts ≤ c := by
    apply Nat.le_of_not_gt
    intro hgt
    apply hfail
    intro k l hkl
    have hall := (envDeletionDistance_gt_iff hp W0.honest W0.shifts c).1 hgt k l hkl
    rw [hmasked W0 hW0H hW0factor k l hkl, hW0H] at hall
    exact hall
  refine ⟨hoccupancy, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro hcriterion W hWH hfactor hnorm hnonneg hmodel hpsd
      have hdelta : envDeletionDistance W.honest W.shifts > c :=
        (envDeletionDistance_gt_iff hp W.honest W.shifts c).2 (by
          intro k l hkl
          rw [hmasked W hWH hfactor k l hkl, hWH]
          exact hcriterion k l hkl)
      exact (sharp_replacement_radius W hnorm hnonneg hmodel hpsd).2.1 hdelta
    · intro huniform
      by_contra hfail
      obtain ⟨Winterior, D', hIH, hIs, hIpd, hcovpd, hInorm, hInonneg,
          hImodel, hD'ne, hImem, hD'mem⟩ :=
        (sharp_replacement_radius W0 hW0norm hW0nonneg hW0model hW0psd).2.2.2
          (hdelta_of_fail hfail)
      have hIfactor : SupportFactorization H Z (a ω) Winterior.shifts := by
        rw [hIs]
        exact hW0factor
      have hsingleton := huniform Winterior hIH hIfactor hInorm hInonneg hImodel
        hIpd.posSemidef
      have hEq : D' = Winterior.structural := by
        have : D' ∈ ({Winterior.structural} : Set (RealMatrix p)) := by
          rwa [← hsingleton]
        simpa using this
      exact hD'ne hEq
  · intro hfail
    obtain ⟨Winterior, D', hIH, hIs, hIpd, hcovpd, hInorm, hInonneg,
        hImodel, hD'ne, hImem, hD'mem⟩ :=
      (sharp_replacement_radius W0 hW0norm hW0nonneg hW0model hW0psd).2.2.2
        (hdelta_of_fail hfail)
    refine ⟨Winterior, D', hIH, ?_, hInorm, hInonneg, hImodel, hIpd, hcovpd,
      hD'ne, hImem, hD'mem⟩
    rw [hIs]
    exact hW0factor
  · intro hcriterion
    let k0 : Fin p := ⟨0, by omega⟩
    let k1 : Fin p := ⟨1, by omega⟩
    have h01 : k0 < k1 := by exact Fin.mk_lt_mk.mpr (by omega)
    have hpair := hcriterion k0 k1 h01
    have hforced : min 2 H.card ≤ genericOccupancy H Z k0 k1 := by
      simp only [genericOccupancy]
      omega
    simp only [honestCount] at hH
    omega
  · intro hcount
    let Zgood : Environment m → Fin p → Bool := fun _ _ ↦ true
    refine ⟨Zgood, by simp [Zgood], ?_⟩
    intro k l hkl
    have hHcard : 3 ≤ H.card := by
      simp only [honestCount] at hH
      omega
    have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
    have hgen : genericOccupancy H Zgood k l = 2 := by
      simp [genericOccupancy, incidenceCount, Zgood, hHne]
      omega
    rw [hgen]
    simp only [honestCount] at hH
    omega

end CausalSmith.ExactID.RobustBackshiftUniformDistance
