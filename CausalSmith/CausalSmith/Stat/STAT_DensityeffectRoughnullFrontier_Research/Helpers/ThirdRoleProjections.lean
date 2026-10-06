module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CovariateKernelMoments
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.WeightedObservedMeans

/-! Exact pair and singleton projections of the observable third-order kernel.
These are the independent-role integrations in (10) and (12) of the covariance
roadmap; in particular, eliminating the middle role costs no extra rank. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Two matching-cell kernels collapse to an endpoint kernel times one row. -/
-- @node: covariateKernel_chain
lemma covariateKernel_chain (q : ℕ) (x z w : ℝ) :
    covariateKernel q x z * covariateKernel q z w =
      covariateKernel q x w * covariateKernel q x z := by
  unfold covariateKernel
  by_cases hxz : cell q x = cell q z
  · rw [if_pos hxz]
    simp only [← hxz]
    ring
  · rw [if_neg hxz]
    simp

/-- Integrating a weighted middle covariate gives its cell mean and the endpoint kernel. -/
-- @node: integral_middle_design_kernel
lemma integral_middle_design_kernel (q : ℕ) (u : ℝ → ℝ) (x w : ℝ) :
    (∫ z, covariateKernel q x z * u z * covariateKernel q z w ∂unitVolume) =
      covariateKernel q x w * cellAverage q u x := by
  have he (z : ℝ) : covariateKernel q x z * u z * covariateKernel q z w =
      covariateKernel q x w * (covariateKernel q x z * u z) := by
    calc
      _ = (covariateKernel q x z * covariateKernel q z w) * u z := by ring
      _ = _ := by rw [covariateKernel_chain]; ring
  simp_rw [he]
  rw [integral_const_mul]
  rfl

/-- Eliminating the observable middle treatment role gives the same weighted-cell identity. -/
-- @node: integral_middle_Rres_kernel
lemma integral_middle_Rres_kernel (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx q : ℕ) (a : Bool) (x w : ℝ) :
    (∫ o, covariateKernel q x (X o) * Rres train mx a o *
      covariateKernel q (X o) w ∂P.law) =
      covariateKernel q x w * cellAverage q (uerr P train mx a) x := by
  have he (o : Omega) : covariateKernel q x (X o) * Rres train mx a o *
      covariateKernel q (X o) w =
      covariateKernel q x w * (Rres train mx a o * covariateKernel q (X o) x) := by
    rw [covariateKernel_symm q (X o) x]
    calc
      _ = (covariateKernel q x (X o) * covariateKernel q (X o) w) *
          Rres train mx a o := by ring
      _ = _ := by rw [covariateKernel_chain]; ring
  simp_rw [he]
  rw [integral_const_mul, integral_Rres_covariateKernel P hModel train mx q a]

/-- Eliminating the observable outcome role gives the coefficient-error cell mean. -/
-- @node: integral_Vres_covariateKernel
lemma integral_Vres_covariateKernel (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (a : Bool) (x : ℝ) :
    (∫ o, covariateKernel q x (X o) • Vres train mx my J a o ∂P.law) =
      cellAverage q (fun z => coefficients J (verr P train mx my a z)) x := by
  exact integral_Vres_covariate_test P train mx my J a
    (covariateKernel q x) (by fun_prop)
    (chain_finite_range_precomp (finite_range_covariateKernel q) (fun z => (x, z)))

/-- Holding the first two roles fixed gives the pair projection for overlap {1,2}. -/
-- @node: third_role_projection_pair12
lemma third_role_projection_pair12 (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (a : Bool) (o1 o2 : Omega) :
    (∫ o3, (Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * covariateKernel q (X o2) (X o3)) •
        Vres train mx my J a o3 ∂P.law) =
      (Rres train mx a o1 * covariateKernel q (X o1) (X o2) * Rres train mx a o2) •
        cellAverage q (fun z => coefficients J (verr P train mx my a z)) (X o2) := by
  simp_rw [mul_smul]
  rw [integral_smul, integral_smul, integral_smul, integral_Vres_covariateKernel]

/-- Holding the endpoint roles fixed gives the pair projection for overlap {1,3}. -/
-- @node: third_role_projection_pair13
lemma third_role_projection_pair13 (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (a : Bool) (o1 o3 : Omega) :
    (∫ o2, (Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * covariateKernel q (X o2) (X o3)) •
        Vres train mx my J a o3 ∂P.law) =
      (Rres train mx a o1 * covariateKernel q (X o1) (X o3) *
        cellAverage q (uerr P train mx a) (X o1)) • Vres train mx my J a o3 := by
  rw [integral_smul_const]
  have he (o2 : Omega) : Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * covariateKernel q (X o2) (X o3) =
      Rres train mx a o1 * (covariateKernel q (X o1) (X o2) *
        Rres train mx a o2 * covariateKernel q (X o2) (X o3)) := by ring
  simp_rw [he]
  rw [integral_const_mul, integral_middle_Rres_kernel P hModel]
  simp only [mul_assoc]

/-- Holding the last two roles fixed gives the pair projection for overlap {2,3}. -/
-- @node: third_role_projection_pair23
lemma third_role_projection_pair23 (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (a : Bool) (o2 o3 : Omega) :
    (∫ o1, (Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * covariateKernel q (X o2) (X o3)) •
        Vres train mx my J a o3 ∂P.law) =
      (Rres train mx a o2 * covariateKernel q (X o2) (X o3) *
        cellAverage q (uerr P train mx a) (X o2)) • Vres train mx my J a o3 := by
  rw [integral_smul_const]
  simp_rw [integral_mul_const, integral_Rres_covariateKernel P hModel train mx q a]
  congr 1
  ring

/-- A matching-cell kernel transports a cell average to either endpoint. -/
-- @node: covariateKernel_smul_cellAverage
lemma covariateKernel_smul_cellAverage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (q : ℕ) (v : ℝ → E) (x z : ℝ) :
    covariateKernel q x z • cellAverage q v z =
      covariateKernel q x z • cellAverage q v x := by
  by_cases h : cell q x = cell q z
  · rw [cellAverage_eq_of_cell_eq q v x z h]
  · simp [covariateKernel, h]

/-- Holding only the first role fixed gives the first singleton in (10). -/
-- @node: third_role_projection_singleton1
lemma third_role_projection_singleton1 (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (a : Bool) (o1 : Omega) :
    (∫ o2, ∫ o3, (Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * covariateKernel q (X o2) (X o3)) •
        Vres train mx my J a o3 ∂P.law ∂P.law) =
      (Rres train mx a o1 * cellAverage q (uerr P train mx a) (X o1)) •
        cellAverage q (fun z => coefficients J (verr P train mx my a z)) (X o1) := by
  simp_rw [third_role_projection_pair12]
  have he (o2 : Omega) :
      (Rres train mx a o1 * covariateKernel q (X o1) (X o2) * Rres train mx a o2) •
        cellAverage q (fun z => coefficients J (verr P train mx my a z)) (X o2) =
      (Rres train mx a o1 * Rres train mx a o2 * covariateKernel q (X o2) (X o1)) •
        cellAverage q (fun z => coefficients J (verr P train mx my a z)) (X o1) := by
    rw [show Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
        Rres train mx a o2 = Rres train mx a o1 * Rres train mx a o2 *
        covariateKernel q (X o1) (X o2) by ring,
      mul_smul, covariateKernel_smul_cellAverage, ← mul_smul,
      covariateKernel_symm q (X o1) (X o2)]
  simp_rw [he]
  rw [integral_smul_const]
  simp_rw [mul_assoc, integral_const_mul, integral_Rres_covariateKernel P hModel train mx q a]

/-- Holding only the middle role fixed gives the second singleton in (10). -/
-- @node: third_role_projection_singleton2
lemma third_role_projection_singleton2 (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (a : Bool) (o2 : Omega) :
    (∫ o1, ∫ o3, (Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * covariateKernel q (X o2) (X o3)) •
        Vres train mx my J a o3 ∂P.law ∂P.law) =
      (Rres train mx a o2 * cellAverage q (uerr P train mx a) (X o2)) •
        cellAverage q (fun z => coefficients J (verr P train mx my a z)) (X o2) := by
  simp_rw [third_role_projection_pair12]
  rw [integral_smul_const]
  simp_rw [integral_mul_const, integral_Rres_covariateKernel P hModel train mx q a]
  rw [mul_comm]

/-- Holding only the outcome role fixed gives the squared cell mean in (10). -/
-- @node: third_role_projection_singleton3
lemma third_role_projection_singleton3 (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (hq : 0 < q) (a : Bool) (o3 : Omega) :
    (∫ o : Omega × Omega, (Rres train mx a o.1 * covariateKernel q (X o.1) (X o.2) *
      Rres train mx a o.2 * covariateKernel q (X o.2) (X o3)) •
        Vres train mx my J a o3 ∂P.law.prod P.law) =
      (cellAverage q (uerr P train mx a) (X o3)) ^ 2 • Vres train mx my J a o3 := by
  rw [integral_smul_const, integral_treatment_pair_kernel P hModel train mx q hq a]

end CausalSmith.Stat.DensityEffectRoughNull
