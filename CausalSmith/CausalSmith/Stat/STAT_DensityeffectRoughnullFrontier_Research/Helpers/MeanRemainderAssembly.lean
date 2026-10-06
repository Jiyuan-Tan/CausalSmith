module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CellProjectionMeans

/-! Exact multiband assembly of the three corrected-mean remainders from (21)--(22).
The band telescoping identity is applied to the unaveraged product before inserting
correction-cell products. All integrability follows from model and pilot envelopes. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Projecting the reversed third-order cell remainder reverses the difference of role means. -/
-- @node: coefficients_integrated_cell_remainder_reverse
lemma coefficients_integrated_cell_remainder_reverse (k J : ℕ) (hk : 0 < k)
    (g : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (unitVolume.prod unitVolume)) (n : ℕ)
    (hgf : Integrable (fun z : ℝ × ℝ => (g z.1) ^ n * f z.1 z.2)
      (unitVolume.prod unitVolume)) :
    coefficients J (fun y => ∫ x,
      (cellAverage k g x) ^ n * cellAverage k (fun z => f z y) x -
        (g x) ^ n * f x y ∂unitVolume) =
    (∫ x, (cellAverage k g x) ^ n •
      cellAverage k (fun z => coefficients J (f z)) x ∂unitVolume) -
    (∫ x, coefficients J (fun y => (g x) ^ n * f x y) ∂unitVolume) := by
  have h := coefficients_integrated_cell_remainder k J hk g f hf n hgf
  have hneg : (fun y => ∫ x,
      (cellAverage k g x) ^ n * cellAverage k (fun z => f z y) x -
        (g x) ^ n * f x y ∂unitVolume) =
      (fun y => -(∫ x, (g x) ^ n * f x y -
        (cellAverage k g x) ^ n * cellAverage k (fun z => f z y) x ∂unitVolume)) := by
    funext y
    rw [← integral_neg]
    congr 1
    funext x
    ring
  rw [hneg]
  have hn := coefficients_const_mul J (-1) (fun y => ∫ x,
    (g x) ^ n * f x y -
      (cellAverage k g x) ^ n * cellAverage k (fun z => f z y) x ∂unitVolume)
  simp only [neg_one_mul, neg_one_smul] at hn
  rw [hn, h, neg_sub]

/-- The second remainder is the unaveraged product minus the bandwise cell products. -/
-- @node: sum_Qband_integrated_cell_remainder
lemma sum_Qband_integrated_cell_remainder {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my L T : ℕ) (kt : ℕ → ℕ)
    (hkt : ∀ t, t ≤ T → 0 < kt t) (a : Bool) :
    (∑ t ∈ Finset.range (T + 1), Qband L (2 ^ T * L) t
      (coefficients (2 ^ T * L) (fun y => ∫ x,
        uerr P train mx a x * verr P train mx my a x y -
        cellAverage (kt t) (uerr P train mx a) x *
          cellAverage (kt t) (fun z => verr P train mx my a z y) x ∂unitVolume))) =
    (∫ x, coefficients (2 ^ T * L) (fun y =>
      uerr P train mx a x * verr P train mx my a x y) ∂unitVolume) -
    (∑ t ∈ Finset.range (T + 1), Qband L (2 ^ T * L) t
      (∫ x, cellAverage (kt t) (uerr P train mx a) x •
        cellAverage (kt t) (fun z => coefficients (2 ^ T * L)
          (verr P train mx my a z)) x ∂unitVolume)) := by
  have hv : Integrable (Function.uncurry (verr P train mx my a))
      (unitVolume.prod unitVolume) := by
    change Integrable (fun z : ℝ × ℝ => verr P train mx my a z.1 z.2) _
    simpa only [pow_zero, one_mul] using
      integrable_uerr_pow_mul_verr_joint P hModel train mx my a 0
  have huv := integrable_uerr_pow_mul_verr_joint P hModel train mx my a 1
  have he t (ht : t ∈ Finset.range (T + 1)) :=
    coefficients_integrated_cell_remainder (kt t) (2 ^ T * L)
      (hkt t (by have := Finset.mem_range.mp ht; omega))
      (uerr P train mx a) (verr P train mx my a) hv 1 huv
  have hsum := Finset.sum_congr rfl (fun t ht => congrArg (Qband L (2 ^ T * L) t) (he t ht))
  simp only [pow_one, Qband_sub] at hsum
  rw [hsum, Finset.sum_sub_distrib, sum_Qband_eq_self]

/-- The projected arm mean has precisely the three remainders in the paper identity. -/
-- @node: corrected_mean_multiband_arm_identity
lemma corrected_mean_multiband_arm_identity {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my L T q : ℕ) (kt : ℕ → ℕ)
    (hq : 0 < q) (hkt : ∀ t, t ≤ T → 0 < kt t) (a : Bool) :
    (∫ x, pilotCoefficients train mx my (2 ^ T * L) a x ∂unitVolume) +
    (∫ x, coefficients (2 ^ T * L) (verr P train mx my a x) ∂unitVolume) -
    (∑ t ∈ Finset.range (T + 1), Qband L (2 ^ T * L) t
      (∫ x, cellAverage (kt t) (uerr P train mx a) x •
        cellAverage (kt t) (fun z => coefficients (2 ^ T * L)
          (verr P train mx my a z)) x ∂unitVolume)) +
    (∫ x, (cellAverage q (uerr P train mx a) x) ^ 2 •
      cellAverage q (fun z => coefficients (2 ^ T * L)
        (verr P train mx my a z)) x ∂unitVolume) -
    coefficients (2 ^ T * L) (marginalDensity P a) =
    coefficients (2 ^ T * L) (fun y => ∫ x,
      (uerr P train mx a x) ^ 3 * werr P train mx my a x y ∂unitVolume) +
    (∑ t ∈ Finset.range (T + 1), Qband L (2 ^ T * L) t
      (coefficients (2 ^ T * L) (fun y => ∫ x,
        uerr P train mx a x * verr P train mx my a x y -
        cellAverage (kt t) (uerr P train mx a) x *
          cellAverage (kt t) (fun z => verr P train mx my a z y) x ∂unitVolume))) +
    coefficients (2 ^ T * L) (fun y => ∫ x,
      (cellAverage q (uerr P train mx a) x) ^ 2 *
        cellAverage q (fun z => verr P train mx my a z y) x -
      (uerr P train mx a x) ^ 2 * verr P train mx my a x y ∂unitVolume) := by
  have hv : Integrable (Function.uncurry (verr P train mx my a))
      (unitVolume.prod unitVolume) := by
    change Integrable (fun z : ℝ × ℝ => verr P train mx my a z.1 z.2) _
    simpa only [pow_zero, one_mul] using
      integrable_uerr_pow_mul_verr_joint P hModel train mx my a 0
  rw [sum_Qband_integrated_cell_remainder P hModel train mx my L T kt hkt a,
    coefficients_integrated_cell_remainder_reverse q (2 ^ T * L) hq
      (uerr P train mx a) (verr P train mx my a) hv 2
      (integrable_uerr_pow_mul_verr_joint P hModel train mx my a 2)]
  have hc := corrected_mean_projected_arm_identity P hModel train mx my (2 ^ T * L) a
  rw [← hc]
  abel

/-- The identifying contrast projection is the signed sum of the two marginal projections. -/
-- @node: coefficients_delta_eq_signed_marginals
lemma coefficients_delta_eq_signed_marginals (P : ObsLaw) (hModel : Model P) (J : ℕ) :
    coefficients J (delta P) =
      ∑ a : Bool, (if a then (1 : ℝ) else -1) •
        coefficients J (marginalDensity P a) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have htrue := (integrable_eta_joint P hModel true).integral_prod_right
  have hfalse := (integrable_eta_joint P hModel false).integral_prod_right
  have hd := coefficients_const_mul_sub J 1 (marginalDensity P true)
    (marginalDensity P false) htrue hfalse
  change coefficients J (fun y => marginalDensity P true y - marginalDensity P false y) = _
  simpa [Fintype.sum_bool, sub_eq_add_neg] using hd

/-- Taking the signed arm difference yields the entire exact remainder vector. -/
-- @node: corrected_mean_projected_contrast_identity
lemma corrected_mean_projected_contrast_identity {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my L T q : ℕ) (kt : ℕ → ℕ)
    (hq : 0 < q) (hkt : ∀ t, t ≤ T → 0 < kt t) :
    (∑ a : Bool, (if a then (1 : ℝ) else -1) •
      ((∫ x, pilotCoefficients train mx my (2 ^ T * L) a x ∂unitVolume) +
      (∫ x, coefficients (2 ^ T * L) (verr P train mx my a x) ∂unitVolume) -
      (∑ t ∈ Finset.range (T + 1), Qband L (2 ^ T * L) t
        (∫ x, cellAverage (kt t) (uerr P train mx a) x •
          cellAverage (kt t) (fun z => coefficients (2 ^ T * L)
            (verr P train mx my a z)) x ∂unitVolume)) +
      (∫ x, (cellAverage q (uerr P train mx a) x) ^ 2 •
        cellAverage q (fun z => coefficients (2 ^ T * L)
          (verr P train mx my a z)) x ∂unitVolume))) -
    coefficients (2 ^ T * L) (delta P) =
      meanRemainder P train mx my L T (2 ^ T * L) q kt := by
  rw [coefficients_delta_eq_signed_marginals P hModel, ← Finset.sum_sub_distrib]
  unfold meanRemainder
  apply Finset.sum_congr rfl
  intro a _
  rw [← smul_sub, corrected_mean_multiband_arm_identity P hModel train mx my L T q kt hq hkt a]

end CausalSmith.Stat.DensityEffectRoughNull
