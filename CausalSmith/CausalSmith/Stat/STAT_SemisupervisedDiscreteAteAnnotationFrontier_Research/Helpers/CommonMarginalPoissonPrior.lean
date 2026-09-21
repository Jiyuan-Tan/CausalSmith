module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalPrior
public import Causalean.Stat.Minimax.TotalVariation
public import Causalean.Stat.Minimax.Mixture.MomentMatched.SupportLocalized

/-! Scale specialization of the common-marginal rare-cell prior. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

/-- The generalized all-bandwidth realization interface supplied by the
uniform-intensity construction. -/
structure CommonMarginalPoissonPriorFamily {eps : Real}
    (calibration : CommonMarginalCalibration eps)
    (C rho : Real) : Prop where
  boundConstant_pos : 0 < C
  rho_mem : rho ∈ Set.Ioo (0 : Real) 1
  realize : ∀ (n m L : Nat), 1 ≤ n → 2 ≤ L →
    ∀ (u v B a : Real) (k d : Nat),
    2 ≤ d → 0 ≤ u → 0 ≤ v → 0 < u + v →
    (u + v) * B ≤ calibration.uniformBandwidthConstant * L → 0 < B →
    a = calibration.gamma * B / (L : Real) ^ 2 →
    k * a ≤ calibration.dualGap → k + 1 ≤ d →
    ∃ R : CommonMarginalRecipe calibration n m d L B a k,
      CommonMarginalPoissonPriorWitness
        (u := u) (v := v) (C := C) (rho := rho) R

/-- A witness produced at an explicitly named exact bandwidth scale.  Keeping
the numerator constant and denominator as indices of the witness lets the
uniform Poisson specialization use `bε L / (u + v)`, while the C55
fixed-sample construction uses the different, paper-facing scale
`b₀ L / (n + m)`.  Both remain strictly narrower than the inequality-only
`CommonMarginalPoissonPriorWitness`. -/
structure CommonMarginalExactPoissonPriorWitness {eps : Real}
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a u v C rho : Real}
    (bandwidthScale bandwidthDenominator : Real)
    (R : CommonMarginalRecipe calibration n m d L B a k) : Prop where
  sampleSize_pos : 1 ≤ n
  degree_ge_two : 2 ≤ L
  dimension_ge_two : 2 ≤ d
  labeledIntensity_nonneg : 0 ≤ u
  auxiliaryIntensity_nonneg : 0 ≤ v
  totalIntensity_pos : 0 < u + v
  rareCount_fit : k + 1 ≤ d
  bandwidthDenominator_pos : 0 < bandwidthDenominator
  bandwidth_eq : B = bandwidthScale * L / bandwidthDenominator
  bandwidth_bound : (u + v) * B ≤
    calibration.uniformBandwidthConstant * L
  bandwidth_pos : 0 < B
  shift_eq : a = calibration.gamma * B / (L : Real) ^ 2
  rareShiftSmall : k * a ≤ calibration.dualGap
  labeledIntensity_eq : R.labeledIntensity = u
  auxiliaryIntensity_eq : R.auxiliaryIntensity = v
  bounds : CommonMarginalBounds R u v calibration.dualGap C rho
  witness : CommonMarginalPoissonPriorWitness
    (u := u) (v := v) (C := C) (rho := rho) R

/-- Quantitative closure of the canonical C55 recipe.  These are outputs of
the epsilon-only calibration construction, rather than premises imposed on the
fixed-sample transfer or on the converse.  Every clause refers to the single
exact-bandwidth recipe stored in `H`. -/
structure CommonMarginalCanonicalCertificate {eps : Real}
    {calibration : CommonMarginalCalibration eps}
    {n m d : Nat} (Cfixed cSmall cFloor C rho : Real)
    (H : CommonMarginalPriorHandle calibration n m d) : Prop where
  degree_ge_two : 2 ≤ H.L
  transferBandwidthConstants :
    2 * Cfixed * calibration.bandwidthConstant ≤
      calibration.uniformBandwidthConstant
  bandwidthClosure :
    (commonMarginalLabeledIntensity Cfixed n +
        commonMarginalAuxiliaryIntensity Cfixed n m) * H.B ≤
      calibration.uniformBandwidthConstant * H.L
  rareShiftSmall : H.recipe.finiteAtomConstruction →
    H.k * H.a ≤ calibration.dualGap
  sameTable :
    randomAuxTableLaw (commonMarginalPriorOf H false) =
      randomAuxTableLaw (commonMarginalPriorOf H true)
  poissonPriorWitness : H.recipe.finiteAtomConstruction →
    CommonMarginalExactPoissonPriorWitness
      calibration.bandwidthConstant (n + m : Nat) H.recipe
      (u := commonMarginalLabeledIntensity Cfixed n)
      (v := commonMarginalAuxiliaryIntensity Cfixed n m)
      (C := C) (rho := rho)
  bounds : H.recipe.finiteAtomConstruction →
    CommonMarginalBounds H.recipe
      (commonMarginalLabeledIntensity Cfixed n)
      (commonMarginalAuxiliaryIntensity Cfixed n m)
      calibration.dualGap C rho
  mixtureTV : H.recipe.finiteAtomConstruction →
    Causalean.Stat.tvDist H.recipe.rawExperiment0 H.recipe.rawExperiment1 ≤ 1 / 8
  centerSeparation : H.recipe.finiteAtomConstruction →
    commonMarginalDelta H ≤
      |rawPriorCenter H.recipe true - rawPriorCenter H.recipe false|
  varianceAbsorption : H.recipe.finiteAtomConstruction →
    H.k * H.B * H.a ≤ cSmall * commonMarginalDelta H ^ 2
  transferredRisk : H.recipe.finiteAtomConstruction →
    cFloor * commonMarginalDelta H ^ 2 ≤ minimaxRisk n m d eps
  floorRisk : cFloor / n ≤ minimaxRisk n m d eps
  dimensionNonparametric : H.recipe.finiteAtomConstruction →
    calibration.dimensionConstant * commonMarginalDimensionTerm n m d ≤
      commonMarginalDelta H ^ 2
  dimensionParametric : ¬H.recipe.finiteAtomConstruction →
    calibration.dimensionConstant * commonMarginalDimensionTerm n m d ≤
      cFloor / n

-- @node: lem:common-marginal-poisson-prior
/-- The exact `B = bε L / (u + v)` specialization of the uniform-intensity
common-marginal construction.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma common_marginal_poisson_prior {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∃ calibration : CommonMarginalCalibration eps, ∃ C rho : Real,
      0 < C ∧ rho ∈ Set.Ioo (0 : Real) 1 ∧
      ∀ (n m L : Nat), 1 ≤ n → 2 ≤ L →
      ∀ (u v : Real) (k d : Nat),
        2 ≤ d → 0 ≤ u → 0 ≤ v → 0 < u + v →
        let B := calibration.uniformBandwidthConstant * L / (u + v)
        let a := calibration.gamma * B / (L : Real) ^ 2
        k * a ≤ calibration.dualGap → k + 1 ≤ d →
        ∃ R : CommonMarginalRecipe calibration n m d L B a k,
          CommonMarginalExactPoissonPriorWitness
            calibration.uniformBandwidthConstant (u + v)
            (u := u) (v := v) (C := C) (rho := rho) R := by
  rcases common_marginal_uniform_intensity eps heps heps2 with
    ⟨calibration, C, rho, hC, hrho, _hclosure, hrealize⟩
  refine ⟨calibration, C, rho, hC, hrho, ?_⟩
  intro n m L hn hL u v k d hd hu hv huv
  dsimp only
  intro hka hkd
  let B : Real := calibration.uniformBandwidthConstant * L / (u + v)
  let a : Real := calibration.gamma * B / (L : Real) ^ 2
  have hLpos : (0 : Real) < L := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hL)
  have hBpos : 0 < B := by
    exact div_pos
      (mul_pos calibration.uniformBandwidthConstant_pos hLpos) huv
  have hband :
      (u + v) * B ≤ calibration.uniformBandwidthConstant * L := by
    have huv_ne : u + v ≠ 0 := ne_of_gt huv
    dsimp [B]
    field_simp
    exact le_rfl
  rcases hrealize n m L hn hL u v B a k d hd hu hv huv hband hBpos
      (by rfl) hka hkd with ⟨R, hRu, hRv, _hprior0, _hprior1, hbounds⟩
  refine ⟨R, ?_⟩
  exact
    { sampleSize_pos := hn
      degree_ge_two := hL
      dimension_ge_two := hd
      labeledIntensity_nonneg := hu
      auxiliaryIntensity_nonneg := hv
      totalIntensity_pos := huv
      rareCount_fit := hkd
      bandwidthDenominator_pos := huv
      bandwidth_eq := rfl
      bandwidth_bound := hband
      bandwidth_pos := hBpos
      shift_eq := rfl
      rareShiftSmall := hka
      labeledIntensity_eq := hRu
      auxiliaryIntensity_eq := hRv
      bounds := hbounds
      witness :=
        { bandwidth_bound := hband
          bandwidth_pos := hBpos
          shift_eq := rfl
          rareShiftSmall := hka
          labeledIntensity_eq := hRu
          auxiliaryIntensity_eq := hRv
          bounds := hbounds } }

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
