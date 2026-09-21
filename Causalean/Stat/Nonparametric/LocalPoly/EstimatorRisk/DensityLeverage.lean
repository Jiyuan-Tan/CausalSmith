/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.Factorization
public import Causalean.Stat.Nonparametric.LocalPoly.Rate

/-!
# Density-based local-polynomial leverage bounds under shape positive definiteness

Derives explicit leverage constants from density and kernel moments, conditional on a positive
definite density-weighted shape matrix.

This module turns the abstract population-matrix leverage hypotheses for an interior
local-polynomial fit into explicit density and kernel-moment constants. The earlier
`LocalPoly.Rate.population_scaling_of_conj` reduced the leverage scaling to a bandwidth-free shape
matrix `T` with assumed `(T⁻¹)₀₀ ≤ cInv` and `T₀₀ ≤ cTop`; here those constants become
**explicit density + kernel-moment quantities**:

`cInv = (G⁻¹)₀₀ / cDesign`,   `cTop = CDesign · G₀₀`,

with `G = weightMomentMatrix p K` the pure kernel-moment matrix. In addition to density-window
bounds and positive definiteness of `G`, both headline theorems assume positive definiteness of the
density-weighted shape matrix `T`; this module does not derive that condition. The chain is:

`popDesignMatrix_factor`  (S = (Nh)·D T D, change of variables)
  → `DensityConstants`     ((T⁻¹)₀₀ ≤ (G⁻¹)₀₀/cDesign, T₀₀ ≤ CDesign·G₀₀ via Loewner sandwich)
  → diagonal-conjugation scaling  ((S⁻¹)₀₀ ≤ cInv/(Nh), S₀₀ ≤ cTop·(Nh))
  → `localPoly_inv00_rate` / `localPoly_leverage_bound`.

The resulting `localPoly_density_inv00_rate` and `localPoly_density_leverage_bound` formulate the
good design event in the rescaled polynomial basis.  Writing `D = diag(1,h,...,h^p)` and
`M = D B D`, the empirical matrix `B = D⁻¹ M D⁻¹` is compared directly with `(Nh) • T`.
This is the nonvacuous local-polynomial normalization: the intercept leverage is unchanged because
`D₀₀ = 1`.
-/

public section

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators
open Matrix

variable {p : ℕ}

/-- **Conditional `O(1/(Nh))` leverage bound with explicit density constants.** Fix [a
bandwidth `h > 0`](hyp:hh), [a sample size `N` with `N > 0`](hyp:hN), and [a density lower bound
`cDesign > 0`](hyp:hcD). Let the kernel `K` be [nonnegative](hyp:hKnn) and [supported in
`[-1,1]`](hyp:hKsupp), with [both centered-monomial integrands — against the shape weight
`K·p(t+h·)` and against the pure kernel `K`](hyp:hintT,hintG) — integrable, [the pure kernel-moment
matrix `G` positive definite](hyp:hGpd), and [the kernel shape matrix `T` positive
definite](hyp:hTpd); suppose [the design density obeys `cDesign ≤ p` on the window
`|a − t| ≤ h`](hyp:hlo). Write [the unscaled empirical moment matrix as `M = D B D`, where `B` is
the empirical Gram matrix in the rescaled polynomial basis](hyp:hMfactor). On the good design event
where [the inverse row sums of `(Nh)T` are bounded by a nonnegative constant `c`](hyp:hc,hBrow),
[the rescaled empirical matrix `B` lies entrywise within a nonnegative scale `η`](hyp:hη,hclose)
of `(Nh)T`, and where the regime constants are small enough
([`c·(p+1)·η ≤ 1/2`](hyp:hsmall) and [`2c²(p+1)η` is at most the explicit density + kernel-moment
constant `cInv/(Nh)`](hyp:hpert)), then [the empirical moment matrix `M` is invertible and its
intercept leverage obeys the explicit interior rate `(M⁻¹)₀₀ ≤ 2·cInv/(Nh)`, with
`cInv = (G⁻¹)₀₀/cDesign` an explicit density and kernel-moment constant](goal). The positive
definiteness of `T` remains an assumption. -/
theorem localPoly_density_inv00_rate {N : ℕ} {h cDesign η c t : ℝ} {K pdens : ℝ → ℝ}
    {M B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ}
    (hh : 0 < h) (hN : 0 < (N : ℝ)) (hcD : 0 < cDesign)
    (hKnn : ∀ u, 0 ≤ K u) (hKsupp : ∀ u, 1 < |u| → K u = 0)
    (hintT : ∀ j k : Fin (p + 1),
      Integrable (fun u => (K u * pdens (t + h * u)) * (u ^ (j : ℕ) * u ^ (k : ℕ))))
    (hintG : ∀ j k : Fin (p + 1),
      Integrable (fun u => K u * (u ^ (j : ℕ) * u ^ (k : ℕ))))
    (hGpd : (weightMomentMatrix p K).PosDef)
    (hTpd : (weightMomentMatrix p (fun u => K u * pdens (t + h * u))).PosDef)
    (hlo : ∀ a, |a - t| ≤ h → cDesign ≤ pdens a)
    (hMfactor : M = Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)) * B *
      Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)))
    (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hBrow : ∀ i, (∑ j, |(((N : ℝ) * h) •
      weightMomentMatrix p (fun u => K u * pdens (t + h * u)))⁻¹ i j|) ≤ c)
    (hclose : ∀ j k, |B j k - ((N : ℝ) * h) *
      weightMomentMatrix p (fun u => K u * pdens (t + h * u)) j k| ≤ η)
    (hsmall : c * ((p + 1 : ℕ) * η) ≤ 1 / 2)
    (hpert : 2 * c ^ 2 * ((p + 1 : ℕ) * η)
      ≤ ((weightMomentMatrix p K)⁻¹ 0 0 / cDesign) / ((N : ℝ) * h)) :
    IsUnit M.det
      ∧ M⁻¹ 0 0 ≤ 2 * (((weightMomentMatrix p K)⁻¹ 0 0 / cDesign) / ((N : ℝ) * h)) := by
  set G := weightMomentMatrix p K with hG
  set T := weightMomentMatrix p (fun u => K u * pdens (t + h * u)) with hT
  set R : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := ((N : ℝ) * h) • T with hRdef
  -- Loewner sandwich (lower): `cDesign · (wᵀ G w) ≤ wᵀ T w`.
  have hsand_lower : ∀ w : Fin (p + 1) → ℝ,
      cDesign * (w ⬝ᵥ (G *ᵥ w)) ≤ w ⬝ᵥ (T *ᵥ w) := fun w =>
    weightMomentMatrix_quadForm_sandwich hcD.le hintT hintG
      (kernelDensity_lower_dom hh hKnn hKsupp hlo) w
  have hTinv00 : T⁻¹ 0 0 ≤ (weightMomentMatrix p K)⁻¹ 0 0 / cDesign :=
    inv00_le_of_quadForm_sandwich hTpd hGpd hcD hsand_lower
  have hTunit : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hTpd.isUnit
  let κ : ℝ := (N : ℝ) * h
  have hκ : κ ≠ 0 := (mul_pos hN hh).ne'
  have hone : ∀ _i : Fin (p + 1), (1 : ℝ) ≠ 0 := fun _ => one_ne_zero
  have hone0 : (fun _j : Fin (p + 1) => (1 : ℝ)) 0 = 1 := rfl
  have hRfactor : R = κ •
      (Matrix.diagonal (fun _j : Fin (p + 1) => (1 : ℝ)) * T *
        Matrix.diagonal (fun _j : Fin (p + 1) => (1 : ℝ))) := by
    simp [R, κ]
  obtain ⟨hRunit, hRinv00_eq⟩ :=
    inv00_diag_conj (κ := κ) hκ hone hone0 hTunit hRfactor
  have hRinv00 : R⁻¹ 0 0 ≤ ((weightMomentMatrix p K)⁻¹ 0 0 / cDesign) / ((N : ℝ) * h) := by
    rw [hRinv00_eq]
    have hκnonneg : 0 ≤ κ⁻¹ := inv_nonneg.mpr (mul_pos hN hh).le
    calc
      κ⁻¹ * T⁻¹ 0 0 ≤ κ⁻¹ * ((weightMomentMatrix p K)⁻¹ 0 0 / cDesign) :=
        mul_le_mul_of_nonneg_left hTinv00 hκnonneg
      _ = ((weightMomentMatrix p K)⁻¹ 0 0 / cDesign) / ((N : ℝ) * h) := by
        simp [κ, div_eq_mul_inv, mul_comm]
  have hcloseR : ∀ j k, |B j k - R j k| ≤ η := by
    intro j k
    simpa [R, T, Matrix.smul_apply, smul_eq_mul] using hclose j k
  obtain ⟨hBunit, hBinv00⟩ :=
    localPoly_inv00_rate hRunit hBrow hcloseR hsmall hRinv00 hpert
  have hd : ∀ i : Fin (p + 1), h ^ (i : ℕ) ≠ 0 := fun i => pow_ne_zero _ hh.ne'
  have hd0 : (fun j : Fin (p + 1) => h ^ (j : ℕ)) 0 = 1 := by simp
  have hMfactor' : M = (1 : ℝ) •
      (Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)) * B *
        Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ))) := by
    simpa using hMfactor
  obtain ⟨hMunit, hMinv00_eq⟩ :=
    inv00_diag_conj (κ := (1 : ℝ)) one_ne_zero hd hd0 hBunit hMfactor'
  refine ⟨hMunit, ?_⟩
  rw [hMinv00_eq]
  simpa [G] using hBinv00

/-- **Conditional bandwidth-free density bound on the leverage product.** Fix [a bandwidth
`h > 0`](hyp:hh), [a sample size `N > 0`](hyp:hN), and density-window bounds
[`0 < cDesign`](hyp:hcD) [with `cDesign ≤ CDesign`](hyp:hcCD). Let the kernel `K` be
[nonnegative](hyp:hKnn) and [supported in `[-1,1]`](hyp:hKsupp), with [both centered-monomial
integrands integrable](hyp:hintT,hintG), [the pure kernel-moment matrix `G` positive
definite](hyp:hGpd), and [the kernel shape matrix `T` positive definite](hyp:hTpd); suppose the
design density obeys [the lower window bound `cDesign ≤ p`](hyp:hlo) and [the upper window bound
`p ≤ CDesign`](hyp:hhi) on `|a − t| ≤ h`. Write [the unscaled empirical moment matrix as
`M = D B D`, with `B` in the rescaled polynomial basis](hyp:hMfactor). On the good design event —
[the inverse row sums of `(Nh)T` bounded by a nonnegative `c`](hyp:hc,hBrow), [the rescaled
empirical matrix `B` entrywise within a nonnegative scale `η`](hyp:hη,hclose) of `(Nh)T`, with
[the regime constants small (`c·(p+1)·η ≤ 1/2`)](hyp:hsmall), [the perturbation bound
`2c²(p+1)η ≤ cInv/(Nh)`](hyp:hpert), and [`η` at most `Nh`](hyp:hηle) — and given [the rescaled
total weight `B₀₀` is nonnegative](hyp:hB00) and [the rescaled inverse leverage `(B⁻¹)₀₀` is
nonnegative](hyp:hBinv00),
then [the geometric mean of the total weight and the inverse leverage is bounded by the
bandwidth-free density constant `√(M₀₀·(M⁻¹)₀₀) ≤ √(2·cInv·(cTop+1))`, with
`cInv = (G⁻¹)₀₀/cDesign` and `cTop = CDesign·G₀₀`](goal). Via `equivKernelWeight_abs_sum_sq_le`
this controls the `ℓ¹` bias leverage `∑ᵢ|Sᵢ|` by a bandwidth-free constant. -/
theorem localPoly_density_leverage_bound {N : ℕ} {h cDesign CDesign η c t : ℝ} {K pdens : ℝ → ℝ}
    {M B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ}
    (hh : 0 < h) (hN : 0 < (N : ℝ)) (hcD : 0 < cDesign) (hcCD : cDesign ≤ CDesign)
    (hKnn : ∀ u, 0 ≤ K u) (hKsupp : ∀ u, 1 < |u| → K u = 0)
    (hintT : ∀ j k : Fin (p + 1),
      Integrable (fun u => (K u * pdens (t + h * u)) * (u ^ (j : ℕ) * u ^ (k : ℕ))))
    (hintG : ∀ j k : Fin (p + 1),
      Integrable (fun u => K u * (u ^ (j : ℕ) * u ^ (k : ℕ))))
    (hGpd : (weightMomentMatrix p K).PosDef)
    (hTpd : (weightMomentMatrix p (fun u => K u * pdens (t + h * u))).PosDef)
    (hlo : ∀ a, |a - t| ≤ h → cDesign ≤ pdens a)
    (hhi : ∀ a, |a - t| ≤ h → pdens a ≤ CDesign)
    (hMfactor : M = Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)) * B *
      Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)))
    (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hBrow : ∀ i, (∑ j, |(((N : ℝ) * h) •
      weightMomentMatrix p (fun u => K u * pdens (t + h * u)))⁻¹ i j|) ≤ c)
    (hclose : ∀ j k, |B j k - ((N : ℝ) * h) *
      weightMomentMatrix p (fun u => K u * pdens (t + h * u)) j k| ≤ η)
    (hsmall : c * ((p + 1 : ℕ) * η) ≤ 1 / 2)
    (hpert : 2 * c ^ 2 * ((p + 1 : ℕ) * η)
      ≤ ((weightMomentMatrix p K)⁻¹ 0 0 / cDesign) / ((N : ℝ) * h))
    (hηle : η ≤ (N : ℝ) * h) (hB00 : 0 ≤ B 0 0) (hBinv00 : 0 ≤ B⁻¹ 0 0) :
    Real.sqrt (M 0 0 * M⁻¹ 0 0)
      ≤ Real.sqrt (2 * ((weightMomentMatrix p K)⁻¹ 0 0 / cDesign)
          * (CDesign * (weightMomentMatrix p K) 0 0 + 1)) := by
  set G := weightMomentMatrix p K with hG
  set T := weightMomentMatrix p (fun u => K u * pdens (t + h * u)) with hT
  set R : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := ((N : ℝ) * h) • T with hRdef
  have hsand_lower : ∀ w : Fin (p + 1) → ℝ,
      cDesign * (w ⬝ᵥ (G *ᵥ w)) ≤ w ⬝ᵥ (T *ᵥ w) := fun w =>
    weightMomentMatrix_quadForm_sandwich hcD.le hintT hintG
      (kernelDensity_lower_dom hh hKnn hKsupp hlo) w
  have hsand_upper : ∀ w : Fin (p + 1) → ℝ,
      w ⬝ᵥ (T *ᵥ w) ≤ CDesign * (w ⬝ᵥ (G *ᵥ w)) := fun w =>
    weightMomentMatrix_quadForm_sandwich_upper (hcD.le.trans hcCD) hintT hintG
      (kernelDensity_upper_dom hh hKnn hKsupp hhi) w
  have hTinv00 : T⁻¹ 0 0 ≤ G⁻¹ 0 0 / cDesign :=
    inv00_le_of_quadForm_sandwich hTpd hGpd hcD hsand_lower
  have hT00 : T 0 0 ≤ CDesign * G 0 0 := entry00_le_of_quadForm_sandwich hsand_upper
  have hTunit : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hTpd.isUnit
  let κ : ℝ := (N : ℝ) * h
  have hκ : κ ≠ 0 := (mul_pos hN hh).ne'
  have hone : ∀ _i : Fin (p + 1), (1 : ℝ) ≠ 0 := fun _ => one_ne_zero
  have hone0 : (fun _j : Fin (p + 1) => (1 : ℝ)) 0 = 1 := rfl
  have hRfactor : R = κ •
      (Matrix.diagonal (fun _j : Fin (p + 1) => (1 : ℝ)) * T *
        Matrix.diagonal (fun _j : Fin (p + 1) => (1 : ℝ))) := by
    simp [R, κ]
  obtain ⟨hRunit, hRinv00eq⟩ :=
    inv00_diag_conj (κ := κ) hκ hone hone0 hTunit hRfactor
  have hR00eq := top00_diag_conj (κ := κ) hone0 hRfactor
  have hRinv00 : R⁻¹ 0 0 ≤ (G⁻¹ 0 0 / cDesign) / ((N : ℝ) * h) := by
    rw [hRinv00eq]
    have hκnonneg : 0 ≤ κ⁻¹ := inv_nonneg.mpr (mul_pos hN hh).le
    calc
      κ⁻¹ * T⁻¹ 0 0 ≤ κ⁻¹ * (G⁻¹ 0 0 / cDesign) :=
        mul_le_mul_of_nonneg_left hTinv00 hκnonneg
      _ = (G⁻¹ 0 0 / cDesign) / ((N : ℝ) * h) := by
        simp [κ, div_eq_mul_inv, mul_comm]
  have hR00 : R 0 0 ≤ (CDesign * G 0 0) * ((N : ℝ) * h) := by
    rw [hR00eq]
    exact mul_le_mul_of_nonneg_left hT00 (mul_pos hN hh).le |>.trans_eq (by ring)
  have hGinv00_nn : 0 ≤ G⁻¹ 0 0 := by
    have h := hGpd.posSemidef.inv.dotProduct_mulVec_nonneg (Pi.single (0 : Fin (p + 1)) (1 : ℝ))
    rw [inv00_eq_quadForm G]; simpa using h
  have hcInv_nn : 0 ≤ G⁻¹ 0 0 / cDesign := div_nonneg hGinv00_nn hcD.le
  have hcloseR : ∀ j k, |B j k - R j k| ≤ η := by
    intro j k
    simpa [R, T, Matrix.smul_apply, smul_eq_mul] using hclose j k
  have hBlev := localPoly_leverage_bound (mul_pos hN hh) hRunit
    hBrow hcloseR hsmall hRinv00 hpert hR00 hηle hB00 hBinv00
  have hd : ∀ i : Fin (p + 1), h ^ (i : ℕ) ≠ 0 := fun i => pow_ne_zero _ hh.ne'
  have hd0 : (fun j : Fin (p + 1) => h ^ (j : ℕ)) 0 = 1 := by simp
  obtain ⟨hBunit, _⟩ :=
    localPoly_inv00_rate hRunit hBrow hcloseR hsmall hRinv00 hpert
  have hMfactor' : M = (1 : ℝ) •
      (Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)) * B *
        Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ))) := by
    simpa using hMfactor
  obtain ⟨_hMunit, hMinv00eq⟩ :=
    inv00_diag_conj (κ := (1 : ℝ)) one_ne_zero hd hd0 hBunit hMfactor'
  have hM00eq := top00_diag_conj (κ := (1 : ℝ)) hd0 hMfactor'
  rw [hMinv00eq, hM00eq]
  simpa using hBlev

end Causalean.Stat.Nonparametric
