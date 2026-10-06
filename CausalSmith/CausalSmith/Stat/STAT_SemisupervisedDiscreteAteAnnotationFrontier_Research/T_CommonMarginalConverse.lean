module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalTransfer
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.ParametricCommonMarginalRecipe
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.ParametricLabelFloor
public import Causalean.Stat.Minimax.TotalVariation
public import Causalean.Stat.Minimax.FuzzyHypotheses

/-! The common-treatment-marginal minimax converse. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

-- @node: thm:common-marginal-converse
/-- Explicit fuzzy priors with the same entire random `(X,A)` table force the
annotation-frontier lower bound, including the constant-risk regime.  The
canonical certificate and its fixed transfer constants are consumed internally;
the public conclusion exposes only the positive epsilon-dependent constant, the
regime-dependent prior handle, equality of its random table laws, and the
headline minimax lower bound.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
theorem common_marginal_converse {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∃ c : Real, 0 < c ∧ -- @realizes \(c_\epsilon\)(positive; depends only on epsilon)
      ∃ calibration : CommonMarginalCalibration eps,
        ∀ (n m d : Nat), 1 ≤ n → 2 ≤ d →
          ∃ H : CommonMarginalPriorHandle calibration n m d,
            randomAuxTableLaw (commonMarginalPriorOf H false) =
                randomAuxTableLaw (commonMarginalPriorOf H true) ∧
            c * frontierRate n m d ≤ minimaxRisk n m d eps := by
  -- Obtain the fixed transfer rule and the inhabited certificate family from
  -- `common_marginal_canonical_certificate_family`.  Its transfer-rule
  -- conjunct is the exact rule of `fixed_sample_common_marginal_transfer`.
  -- Both that rule and this conclusion use `H.recipe`; no second recipe is
  -- frozen or substituted.
  rcases common_marginal_canonical_certificate_family with
    ⟨Cfixed, cRisk, hCfixed, hcRisk, hfamily⟩
  rcases hfamily eps heps heps2 with
    ⟨calibration, CBound, rho, cSmall, cFloor, hCBound, hrho, hcSmall,
      hcFloor, hcFloorRisk, htransfer, hconstruct⟩
  let c := min (cFloor / 2)
    (min (calibration.dimensionConstant / 2)
      (cFloor * calibration.dimensionConstant / 2))
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (half_pos hcFloor)
      (lt_min (half_pos calibration.dimensionConstant_pos)
        (half_pos (mul_pos hcFloor calibration.dimensionConstant_pos)))
  refine ⟨c, hc, calibration, ?_⟩
  intro n m d hn hd
  rcases hconstruct n m d hn hd with ⟨H, hcert⟩
  have hexact : H.recipe.finiteAtomConstruction →
      CommonMarginalExactPoissonPriorWitness
        calibration.bandwidthConstant (n + m : Nat) H.recipe
        (u := commonMarginalLabeledIntensity Cfixed n)
        (v := commonMarginalAuxiliaryIntensity Cfixed n m)
        (C := CBound) (rho := rho) :=
    hcert.poissonPriorWitness
  have hfixed : H.recipe.finiteAtomConstruction →
      cRisk * commonMarginalDelta H ^ 2 ≤ minimaxRisk n m d eps := by
    intro hfinite
    have hwitness := hexact hfinite
    have ha : 0 < H.a := by
      rw [hwitness.shift_eq]
      have hL : (0 : Real) < H.L := by
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hwitness.degree_ge_two)
      exact div_pos (mul_pos calibration.gamma_pos hwitness.bandwidth_pos)
        (sq_pos_of_pos hL)
    have hlower : 0 ≤ commonMarginalDelta H := by
      exact mul_nonneg
        (mul_nonneg calibration.dualGap_pos.le (Nat.cast_nonneg _)) ha.le
    have hsep := hcert.centerSeparation hfinite
    have hvarianceActual : H.k * H.B * H.a ≤ cSmall *
        |rawPriorCenter H.recipe true - rawPriorCenter H.recipe false| ^ 2 :=
      (hcert.varianceAbsorption hfinite).trans
        (mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ hlower (abs_nonneg _)).2 hsep) hcSmall.le)
    have hactual := htransfer n m d H hn hd hwitness
      (hcert.mixtureTV hfinite) hvarianceActual
    exact (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hlower (abs_nonneg _)).2 hsep) hcRisk.le).trans hactual
  refine ⟨H, hcert.sameTable, ?_⟩
  let q : Real := (d : Real) ^ 2 /
    (((n + m : Nat) : Real) ^ 2 * logEN n ^ 2)
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hnpos : (0 : Real) < n := by exact_mod_cast hn
  have hinv : 0 ≤ 1 / (n : Real) := (one_div_nonneg.mpr hnpos.le)
  have hdim : 0 ≤ commonMarginalDimensionTerm n m d := by
    rw [commonMarginalDimensionTerm]
    exact le_min (by norm_num) hq
  have hfront : frontierRate n m d ≤
      1 / (n : Real) + commonMarginalDimensionTerm n m d := by
    rw [frontierRate, commonMarginalDimensionTerm]
    change min 1 (1 / (n : Real) + q) ≤ 1 / (n : Real) + min 1 q
    by_cases hq1 : q ≤ 1
    · rw [min_eq_right hq1]
      exact min_le_right _ _
    · rw [min_eq_left (le_of_lt (lt_of_not_ge hq1))]
      exact (min_le_left _ _).trans (by linarith)
  have hcFloor_nonneg : 0 ≤ cFloor := hcFloor.le
  have hc_left : c ≤ cFloor / 2 := by
    exact min_le_left _ _
  have hc_dim : c ≤ calibration.dimensionConstant / 2 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hc_product : c ≤ cFloor * calibration.dimensionConstant / 2 := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hfloor : cFloor * (1 / (n : Real)) ≤ minimaxRisk n m d eps := by
    simpa [div_eq_mul_inv] using hcert.floorRisk
  by_cases hfinite : H.recipe.finiteAtomConstruction
  · have hdimensionRisk :
        cFloor * (calibration.dimensionConstant *
            commonMarginalDimensionTerm n m d) ≤ minimaxRisk n m d eps := by
      calc
        cFloor * (calibration.dimensionConstant *
              commonMarginalDimensionTerm n m d)
            ≤ cFloor * commonMarginalDelta H ^ 2 := by
              gcongr
              exact hcert.dimensionNonparametric hfinite
        _ ≤ minimaxRisk n m d eps := hcert.transferredRisk hfinite
    calc
      c * frontierRate n m d ≤
          c * (1 / (n : Real) + commonMarginalDimensionTerm n m d) := by
            gcongr
      _ = c * (1 / (n : Real)) +
          c * commonMarginalDimensionTerm n m d := by ring
      _ ≤ (cFloor / 2) * (1 / (n : Real)) +
          (cFloor * calibration.dimensionConstant / 2) *
            commonMarginalDimensionTerm n m d := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hc_left hinv)
              (mul_le_mul_of_nonneg_right hc_product hdim)
      _ = (cFloor * (1 / (n : Real)) +
          cFloor * (calibration.dimensionConstant *
            commonMarginalDimensionTerm n m d)) / 2 := by ring
      _ ≤ (minimaxRisk n m d eps + minimaxRisk n m d eps) / 2 := by
            gcongr
      _ = minimaxRisk n m d eps := by ring
  · calc
      c * frontierRate n m d ≤
          c * (1 / (n : Real) + commonMarginalDimensionTerm n m d) := by
            gcongr
      _ = c * (1 / (n : Real)) +
          c * commonMarginalDimensionTerm n m d := by ring
      _ ≤ (cFloor / 2) * (1 / (n : Real)) +
          (calibration.dimensionConstant / 2) *
            commonMarginalDimensionTerm n m d := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hc_left hinv)
              (mul_le_mul_of_nonneg_right hc_dim hdim)
      _ = (cFloor * (1 / (n : Real)) +
          calibration.dimensionConstant *
            commonMarginalDimensionTerm n m d) / 2 := by ring
      _ ≤ (cFloor * (1 / (n : Real)) +
          cFloor * (1 / (n : Real))) / 2 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            apply add_le_add le_rfl
            simpa [div_eq_mul_inv] using hcert.dimensionParametric hfinite
      _ = cFloor / n := by ring
      _ ≤ minimaxRisk n m d eps := hcert.floorRisk

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
