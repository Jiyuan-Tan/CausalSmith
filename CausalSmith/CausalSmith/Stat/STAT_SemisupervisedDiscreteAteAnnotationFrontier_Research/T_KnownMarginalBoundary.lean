module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Basic
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.ChiSquaredTwoPoint
public import Causalean.Stat.Minimax.TotalVariation
public import CausalSmith.Mathlib.InformationTheory.ProductChiSquared
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.KnownMarginalBoundary

/-! The parametric boundary of the exact-known-marginal experiment. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

-- @node: thm:known-marginal-boundary
/-- The known-marginal minimax risk is uniformly of order `1/n`.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
theorem known_marginal_boundary {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∃ c C : Real,
      0 < c ∧ c ≤ C ∧
      -- @realizes c_\epsilon(positive lower constant depending only on epsilon)
      -- @realizes C_\epsilon(finite upper constant depending only on epsilon)
      ∀ (n d : Nat), 1 ≤ n → 2 ≤ d →
      c / n ≤ knownMarginalRisk n d eps ∧
        knownMarginalRisk n d eps ≤ C / n := by
  refine ⟨1 / 100, 2 * eps⁻¹, by norm_num, ?_, ?_⟩
  · rw [← div_eq_mul_inv]
    exact (le_div_iff₀ heps).2 (by nlinarith)
  · intro n d hn hd
    constructor
    · letI : Nonempty (Fin d) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_two hd⟩⟩
      let delta : Real := (2 / 5) / Real.sqrt n
      have hnR : (0 : Real) < n := by exact_mod_cast hn
      have hd0 : 0 ≤ delta := by dsimp [delta]; positivity
      have hdsq : delta ^ 2 = 4 / (25 * (n : Real)) := by
        dsimp [delta]
        rw [div_pow, Real.sq_sqrt hnR.le]
        ring
      let hv0 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_null
        (C := Fin d) (m₀ := (1 / 2 : Real)) (g₀ := (1 / 2 : Real))
        (g₁ := (1 / 2 : Real))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have hdu : (1 / 2 : Real) + delta ≤ 1 := by
        have hs : 1 ≤ Real.sqrt (n : Real) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
        have : delta ≤ 2 / 5 := by
          dsimp [delta]
          exact div_le_self (by norm_num) hs
        linarith
      let hv1 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_pert
        (C := Fin d) (m₀ := (1 / 2 : Real)) (g₀ := (1 / 2 : Real))
        (g₁ := (1 / 2 : Real)) (δ := delta)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd0 hdu
      let P0 := parametricFloorNullLaw hv0
      let P1 := parametricFloorPertLaw hv1
      let MP0 : ClassLaw d eps := ⟨P0, parametricFloorNullLaw_model hd heps heps2 hv0⟩
      let MP1 : ClassLaw d eps := ⟨P1, parametricFloorPertLaw_model hd heps heps2 hv1⟩
      have hreg : (n : Real) * ((1 / 2 : Real) * delta ^ 2 /
          ((1 / 2 : Real) * (1 - 1 / 2))) ≤ Real.log 2 := by
        rw [hdsq]
        have hlog : (8 / 25 : Real) ≤ Real.log 2 :=
          le_trans (by norm_num) (le_of_lt Real.log_two_gt_d9)
        convert hlog using 1 <;> field_simp [hnR.ne'] <;> ring
      have htv : Causalean.Stat.tvDist (labeledProductLaw P0 n)
          (labeledProductLaw P1 n) ≤ 1 / 2 := by
        simpa [P0, P1, parametricFloorNullLaw, parametricFloorPertLaw,
          labeledProductLaw, obsLaw, Causalean.Estimation.MinimaxATE.productLaw,
          Causalean.Estimation.MinimaxATE.obsLaw] using
          (Causalean.Estimation.MinimaxATE.Parametric.tvDist_productLaw_le_half
            hv0 hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) hreg)
      have htable : auxTableOf P0 = auxTableOf P1 := by
        funext z
        rcases z with ⟨x, a⟩
        cases a <;>
          simp [auxTableOf, armMass, P0, P1, parametricFloorNullLaw_jointMass,
            parametricFloorPertLaw_jointMass,
            Causalean.Estimation.MinimaxATE.obsReal,
            Causalean.Estimation.MinimaxATE.Parametric.mC,
            Causalean.Estimation.MinimaxATE.Parametric.gNull,
            Causalean.Estimation.MinimaxATE.Parametric.gPert]
        all_goals ring
      have hsep : 2 * (delta / 2) ≤ |ateFunctional MP0.1 - ateFunctional MP1.1| := by
        rw [show ateFunctional MP0.1 = 0 by
          simpa [MP0, P0] using parametricFloorNullLaw_ate hv0,
          show ateFunctional MP1.1 = delta by
          simpa [MP1, P1] using parametricFloorPertLaw_ate hv1]
        rw [show 2 * (delta / 2) = delta by ring, zero_sub, abs_neg, abs_of_nonneg hd0]
      have hlow := knownMarginalRisk_ge_two_model_tv MP0 MP1
        (by simpa [MP0, MP1] using htable) (s := delta / 2) (by positivity) hsep
        (by simpa [MP0, MP1] using htv)
      calc
        1 / 100 / (n : Real) = (delta / 2) ^ 2 / 4 := by
          rw [show (delta / 2) ^ 2 = delta ^ 2 / 4 by ring, hdsq]
          ring
        _ ≤ knownMarginalRisk n d eps := hlow
    · have hu := knownMarginalRisk_upper heps n d hn hd
      simpa [div_eq_mul_inv] using hu

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
