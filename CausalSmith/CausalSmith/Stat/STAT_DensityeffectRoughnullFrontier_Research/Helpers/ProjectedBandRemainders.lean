module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.BandRemainderNorms
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.HighBandRemainders

/-! Projection of the integrated correction-cell covariances and the multiband bias bound (27). -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- A function constant on each correction cell is integrable under the uniform design. -/
-- @node: integrable_histogram_cellwise_vector
lemma integrable_histogram_cellwise_vector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (k : ℕ) (hk : 0 < k) (f : ℝ → E)
    (c : Fin k → E)
    (hc : ∀ i, ∀ᵐ x ∂unitVolume.restrict (histogramCell k (i.val + 1)), f x = c i) :
    Integrable f unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hi : ∀ i : Fin k, IntegrableOn f (histogramCell k (i.val + 1)) unitVolume :=
    fun i => (integrable_const (c i)).congr (Filter.EventuallyEq.symm (hc i))
  have h := integrableOn_finite_iUnion.mpr hi
  rw [histogramCells_cover k hk] at h
  simpa only [IntegrableOn, unitVolume, Measure.restrict_restrict measurableSet_Icc,
    Set.inter_self] using h

/-- Integrating a vector-valued correction-cell average preserves its design integral. -/
-- @node: integral_cellAverage_vector
lemma integral_cellAverage_vector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (k : ℕ) (hk : 0 < k) (f : ℝ → E)
    (hf : Integrable f unitVolume) :
    (∫ x, cellAverage k f x ∂unitVolume) = ∫ x, f x ∂unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hc (i : Fin k) : ∀ᵐ x ∂unitVolume.restrict (histogramCell k (i.val + 1)),
      cellAverage k f x = ∫ z, f z ∂correctionCellLaw k i := by
    filter_upwards [ae_restrict_mem (measurableSet_histogramCell k (i.val + 1))] with x hx
    exact cellAverage_eq_correctionCellLaw k i f x hx.2
  have hi (i : Fin k) : IntegrableOn (cellAverage k f) (histogramCell k (i.val + 1))
      unitVolume := (integrable_const _).congr (Filter.EventuallyEq.symm (hc i))
  have hsplit (g : ℝ → E)
      (hg : ∀ i : Fin k, IntegrableOn g (histogramCell k (i.val + 1)) unitVolume) :
      (∫ x, g x ∂unitVolume) =
        ∑ i : Fin k, ∫ x in histogramCell k (i.val + 1), g x ∂unitVolume := by
    have h := integral_iUnion_fintype (fun i : Fin k =>
      measurableSet_histogramCell k (i.val + 1)) (histogramCells_disjoint k) hg
    rw [histogramCells_cover k hk] at h
    simpa only [unitVolume, Measure.restrict_restrict measurableSet_Icc, Set.inter_self] using h
  rw [hsplit _ hi, hsplit f (fun _ => hf.integrableOn)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_congr_ae (hc i), integral_const]
  have hm : (unitVolume.restrict (histogramCell k (i.val + 1))).real Set.univ = 1 / (k : ℝ) := by
    simpa [measureReal_def] using histogramCell_mass_eq k hk i
  rw [hm, correctionCellLaw, integral_smul_measure]
  simp only [ENNReal.toReal_natCast, smul_smul]
  have hn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp [hn]

/-- A finite-dimensional outcome band commutes with integration of integrable vectors. -/
-- @node: Qband_integral
lemma Qband_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (L J t : ℕ) (f : α → Hj J) (hf : Integrable f μ) :
    Qband L J t (∫ x, f x ∂μ) = ∫ x, Qband L J t (f x) ∂μ := by
  let A : Hj J →ₗ[ℝ] Hj J :=
    { toFun := Qband L J t
      map_add' := Qband_add L J t
      map_smul' := Qband_smul L J t }
  exact (A.toContinuousLinearMap.integral_comp_comm hf).symm

/-- The same band commutes with correction-cell averaging. -/
-- @node: Qband_cellAverage
lemma Qband_cellAverage (k L J t : ℕ) (f : ℝ → Hj J)
    (hf : Integrable f unitVolume) (x : ℝ) :
    Qband L J t (cellAverage k f x) = cellAverage k (fun z => Qband L J t (f z)) x := by
  have hker : Integrable (fun z => covariateKernel k x z • f z) unitVolume := by
    have hm : Measurable (fun z => covariateKernel k x z) := by fun_prop
    apply hf.bdd_smul (k : ℝ) hm.aestronglyMeasurable
    filter_upwards [] with z
    unfold covariateKernel
    split_ifs <;> simp
  unfold cellAverage
  rw [Qband_integral unitVolume L J t _ hker]
  simp_rw [Qband_smul]

/-- Bands preserve integrability as continuous linear maps on the coefficient space. -/
-- @node: integrable_Qband
lemma integrable_Qband {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (L J t : ℕ) (f : α → Hj J) (hf : Integrable f μ) :
    Integrable (fun x => Qband L J t (f x)) μ := by
  let A : Hj J →ₗ[ℝ] Hj J :=
    { toFun := Qband L J t
      map_add' := Qband_add L J t
      map_smul' := Qband_smul L J t }
  exact A.toContinuousLinearMap.integrable_comp hf

/-- The projected second remainder is the integral of the band cell covariances. -/
-- @node: Qband_coefficients_integrated_covariance
lemma Qband_coefficients_integrated_covariance (k L J t : ℕ) (hk : 0 < k)
    (g : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (unitVolume.prod unitVolume))
    (hgf : Integrable (fun z : ℝ × ℝ => g z.1 * f z.1 z.2)
      (unitVolume.prod unitVolume)) :
    Qband L J t (coefficients J (fun y => ∫ x,
      g x * f x y - cellAverage k g x * cellAverage k (fun z => f z y) x ∂unitVolume)) =
    ∫ x, cellAverage k (fun z => g z • Qband L J t (coefficients J (f z))) x -
      cellAverage k g x • cellAverage k (fun z => Qband L J t (coefficients J (f z))) x
        ∂unitVolume := by
  have hc := integrable_covariate_coefficients J f hf
  have hgc : Integrable (fun x => g x • coefficients J (f x)) unitVolume := by
    simpa only [coefficients_const_mul] using
      integrable_covariate_coefficients J (fun x y => g x * f x y) hgf
  have hp : Integrable (fun x => cellAverage k g x •
      cellAverage k (fun z => coefficients J (f z)) x) unitVolume := by
    apply integrable_histogram_cellwise_vector k hk _
      (fun i => (∫ z, g z ∂correctionCellLaw k i) •
        (∫ z, coefficients J (f z) ∂correctionCellLaw k i))
    intro i
    filter_upwards [ae_restrict_mem (measurableSet_histogramCell k (i.val + 1))] with x hx
    rw [cellAverage_eq_correctionCellLaw k i _ x hx.2,
      cellAverage_eq_correctionCellLaw k i _ x hx.2]
  have hband : Integrable (fun x => g x • Qband L J t (coefficients J (f x))) unitVolume := by
    simpa only [Qband_smul] using integrable_Qband unitVolume L J t _ hgc
  have hbp : Integrable (fun x => cellAverage k g x •
      cellAverage k (fun z => Qband L J t (coefficients J (f z))) x) unitVolume := by
    simpa only [Qband_smul, Qband_cellAverage k L J t _ hc] using
      integrable_Qband unitVolume L J t _ hp
  have hav : Integrable (cellAverage k (fun x => g x •
      Qband L J t (coefficients J (f x)))) unitVolume := by
    apply integrable_histogram_cellwise_vector k hk _
      (fun i => ∫ z, g z • Qband L J t (coefficients J (f z)) ∂correctionCellLaw k i)
    intro i
    filter_upwards [ae_restrict_mem (measurableSet_histogramCell k (i.val + 1))] with x hx
    exact cellAverage_eq_correctionCellLaw k i _ x hx.2
  have he := coefficients_integrated_cell_remainder k J hk g f hf 1 (by simpa using hgf)
  simp only [pow_one, coefficients_const_mul] at he
  rw [he, Qband_sub, Qband_integral unitVolume L J t _ hgc,
    Qband_integral unitVolume L J t _ hp]
  simp_rw [Qband_smul, Qband_cellAverage k L J t _ hc]
  rw [integral_sub hav hbp, integral_cellAverage_vector k hk _ hband]

/-- The actual projected high-band remainder inherits the 2400 k⁻¹ᐟ¹⁰/d bound. -/
-- @node: high_band_remainder_coefficients_norm_le
lemma high_band_remainder_coefficients_norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my k L T t : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hmy : Dyadic my) (hL : Dyadic L) (hmyL : my ≤ L) (ht : 0 < t) (htT : t ≤ T)
    (a : Bool) :
    ‖Qband L (2 ^ T * L) t (coefficients (2 ^ T * L) (fun y => ∫ x,
      uerr P train mx a x * verr P train mx my a x y -
      cellAverage k (uerr P train mx a) x *
        cellAverage k (fun z => verr P train mx my a z y) x ∂unitVolume))‖ ≤
      2400 * (k : ℝ) ^ (-1 / 10 : ℝ) / ((2 ^ (t - 1) * L : ℕ) : ℝ) := by
  have hv : Integrable (Function.uncurry (verr P train mx my a))
      (unitVolume.prod unitVolume) := by
    change Integrable (fun z : ℝ × ℝ => verr P train mx my a z.1 z.2) _
    simpa only [pow_zero, one_mul] using
      integrable_uerr_pow_mul_verr_joint P hModel train mx my a 0
  rw [Qband_coefficients_integrated_covariance k L (2 ^ T * L) t hk
    (uerr P train mx a) (verr P train mx my a) hv
    (by simpa only [pow_one] using integrable_uerr_pow_mul_verr_joint P hModel train mx my a 1)]
  exact integrated_high_band_cell_covariance_norm_le P hModel train mx my k L T t
    hmx hk hdiv hmy hL hmyL ht htT a

/-- The concrete second remainder satisfies the orthogonal multiband allowance in (27). -/
-- @node: goodPilot_multiband_remainder_norm_le
lemma goodPilot_multiband_remainder_norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my K L T : ℕ) (kt : ℕ → ℕ)
    (hmx : 0 < mx) (hmy : Dyadic my) (hL : Dyadic L) (hmyL : my ≤ L)
    (hkt : ∀ t, t ≤ T → 0 < kt t) (hdiv : ∀ t, t ≤ T → mx ∣ kt t)
    (hzero : kt 0 = K) (hG : GoodPilot P train C0 mx my)
    (hh : hAllow C0 m mx my ≤ 1) (a : Bool) :
    ‖∑ t ∈ Finset.range (T + 1), Qband L (2 ^ T * L) t
      (coefficients (2 ^ T * L) (fun y => ∫ x,
        uerr P train mx a x * verr P train mx my a x y -
        cellAverage (kt t) (uerr P train mx a) x *
          cellAverage (kt t) (fun z => verr P train mx my a z y) x ∂unitVolume))‖ ≤
      2800 * (K : ℝ) ^ (-1 / 5 : ℝ) +
        2400 * Real.sqrt (∑ t ∈ Finset.range T,
          (kt (t + 1) : ℝ) ^ (-1 / 5 : ℝ) / ((2 ^ t * L : ℕ) : ℝ) ^ 2) := by
  have hJ : 0 < 2 ^ T * L := by
    rcases hL with ⟨l, rfl⟩
    positivity
  apply multiband_remainder_norm_le_of_band_bounds K L T hL kt
  · have h := (band_projection_algebra L T hL).2.2 0 (by omega)
      (coefficients (2 ^ T * L) (fun y => ∫ x,
        uerr P train mx a x * verr P train mx my a x y -
        cellAverage (kt 0) (uerr P train mx a) x *
          cellAverage (kt 0) (fun z => verr P train mx my a z y) x ∂unitVolume))
    exact h.trans (by
      simpa only [hzero] using goodPilot_covariance_coefficients_norm_le P hModel train C0
        mx my (kt 0) (2 ^ T * L) hmx (hkt 0 (by omega)) hJ (hdiv 0 (by omega)) hG hh a)
  · intro t ht
    have htT : t + 1 ≤ T := by have := Finset.mem_range.mp ht; omega
    have h := high_band_remainder_coefficients_norm_le P hModel train mx my (kt (t + 1))
      L T (t + 1) hmx (hkt _ htT) (hdiv _ htT) hmy hL hmyL (by omega) htT a
    have hn : 0 ≤ 2400 * (kt (t + 1) : ℝ) ^ (-1 / 10 : ℝ) /
        ((2 ^ t * L : ℕ) : ℝ) := by positivity
    simp only [Nat.add_sub_cancel] at h
    have hs := (sq_le_sq₀ (norm_nonneg _) hn).2 h
    have hp : ((kt (t + 1) : ℝ) ^ (-1 / 10 : ℝ)) ^ 2 =
        (kt (t + 1) : ℝ) ^ (-1 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    simpa only [div_pow, mul_pow, hp, mul_div_assoc] using hs

/-- Summing the two arm remainders gives the public bias allowance with constant 2²⁴. -/
-- @node: goodPilot_meanRemainder_norm_le
lemma goodPilot_meanRemainder_norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (hm : 1 ≤ m) (train : Fin m → Omega) (C0 : ℝ)
    (mx my K L T q : ℕ) (kt : ℕ → ℕ)
    (hmx : 0 < mx) (hq : 0 < q) (hdivq : mx ∣ q)
    (hmy : Dyadic my) (hL : Dyadic L) (hmyL : my ≤ L)
    (hkt : ∀ t, t ≤ T → 0 < kt t) (hdiv : ∀ t, t ≤ T → mx ∣ kt t)
    (hzero : kt 0 = K) (hG : GoodPilot P train C0 mx my)
    (hh : hAllow C0 m mx my ≤ 1) :
    ‖meanRemainder P train mx my L T (2 ^ T * L) q kt‖ ≤
      BAllow (2 ^ 24) (hAllow C0 m mx my) m K L T q kt := by
  let h := hAllow C0 m mx my
  let S := Real.sqrt (∑ t ∈ Finset.range T,
    (kt (t + 1) : ℝ) ^ (-1 / 5 : ℝ) / ((2 ^ t * L : ℕ) : ℝ) ^ 2)
  let b := 64 * h ^ 4 + (2800 * (K : ℝ) ^ (-1 / 5 : ℝ) + 2400 * S) +
    27200 * h * (q : ℝ) ^ (-1 / 5 : ℝ)
  have hJ : 0 < 2 ^ T * L := by rcases hL with ⟨l, rfl⟩; positivity
  have harm (a : Bool) :
      ‖coefficients (2 ^ T * L) (fun y => ∫ x,
        (uerr P train mx a x) ^ 3 * werr P train mx my a x y ∂unitVolume) +
      (∑ t ∈ Finset.range (T + 1), Qband L (2 ^ T * L) t
        (coefficients (2 ^ T * L) (fun y => ∫ x,
          uerr P train mx a x * verr P train mx my a x y -
          cellAverage (kt t) (uerr P train mx a) x *
            cellAverage (kt t) (fun z => verr P train mx my a z y) x ∂unitVolume))) +
      coefficients (2 ^ T * L) (fun y => ∫ x,
        (cellAverage q (uerr P train mx a) x) ^ 2 *
          cellAverage q (fun z => verr P train mx my a z y) x -
          (uerr P train mx a x) ^ 2 * verr P train mx my a x y ∂unitVolume)‖ ≤ b := by
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        (goodPilot_cubic_remainder_coefficients_norm_le P hModel train C0 mx my
          (2 ^ T * L) hJ hG a)
        (goodPilot_multiband_remainder_norm_le P hModel train C0 mx my K L T kt
          hmx hmy hL hmyL hkt hdiv hzero hG hh a)))
      (goodPilot_squared_error_coefficients_norm_le P hModel train C0 mx my q
        (2 ^ T * L) hmx hq hJ hdivq hG hh a))
  have htwo : ‖meanRemainder P train mx my L T (2 ^ T * L) q kt‖ ≤ 2 * b := by
    unfold meanRemainder
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _a : Bool, b := by
        apply Finset.sum_le_sum
        intro a _
        rw [norm_smul, Real.norm_eq_abs]
        have hs : |if a then (1 : ℝ) else -1| = 1 := by cases a <;> norm_num
        rw [hs, one_mul]
        exact harm a
      _ = 2 * b := by simp
  apply htwo.trans
  rw [BAllow, if_neg (by omega : m ≠ 0)]
  have hn := goodPilot_allowance_nonneg P hModel train C0 mx my hG
  have hK : 0 ≤ (K : ℝ) ^ (-1 / 5 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hqnon : 0 ≤ h * (q : ℝ) ^ (-1 / 5 : ℝ) := mul_nonneg hn
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  dsimp [b, h, S] at *
  nlinarith [pow_nonneg hn 4]

end CausalSmith.Stat.DensityEffectRoughNull
