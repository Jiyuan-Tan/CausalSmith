module
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Causalean.Stat.CLT.FiniteIidTriangular.Gaussian
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotCDFIdentity

/-!
# Gaussian limit for the conditional adaptive pilot row

This module instantiates the finite bounded iid triangular-row central limit theorem with
the genuine adaptive main-release mass and centered score. It also transfers the generic
row-length normalization to the paper's root-total-sample normalization.
-/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open Filter MeasureTheory ProbabilityTheory Topology Causalean.Stat
open Causalean.Stat.CLT.FiniteIidTriangular
open scoped BigOperators

private lemma tendsto_moving_of_monotone_pointwise
    (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (t : ℕ → ℝ) (x : ℝ)
    (hmono : ∀ n, Monotone (F n)) (hcont : ContinuousAt G x)
    (hpoint : ∀ y, Tendsto (fun n => F n y) atTop (nhds (G y)))
    (ht : Tendsto t atTop (nhds x)) :
    Tendsto (fun n => F n (t n)) atTop (nhds (G x)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨d, hd, hmap⟩ :=
      (Metric.continuousAt_iff.1 hcont) (G x - a) (sub_pos.mpr ha)
    let y := x - d / 2
    have hyx : y < x := by dsimp [y]; linarith
    have hyd : dist y x < d := by
      rw [Real.dist_eq]
      dsimp [y]
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hGy : a < G y := by
      have hm := hmap hyd
      rw [Real.dist_eq] at hm
      linarith [neg_abs_le (G y - G x)]
    have hFy : ∀ᶠ n in atTop, a < F n y :=
      (tendsto_order.1 (hpoint y)).1 a hGy
    have hyt : ∀ᶠ n in atTop, y < t n :=
      (tendsto_order.1 ht).1 y hyx
    filter_upwards [hFy, hyt] with n hFn htn
    exact hFn.trans_le (hmono n htn.le)
  · intro b hb
    obtain ⟨d, hd, hmap⟩ :=
      (Metric.continuousAt_iff.1 hcont) (b - G x) (sub_pos.mpr hb)
    let z := x + d / 2
    have hxz : x < z := by dsimp [z]; linarith
    have hzd : dist z x < d := by
      rw [Real.dist_eq]
      dsimp [z]
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hGz : G z < b := by
      have hm := hmap hzd
      rw [Real.dist_eq] at hm
      linarith [le_abs_self (G z - G x)]
    have hFz : ∀ᶠ n in atTop, F n z < b :=
      (tendsto_order.1 (hpoint z)).2 b hGz
    have htz : ∀ᶠ n in atTop, t n < z :=
      (tendsto_order.1 ht).2 z hxz
    filter_upwards [hFz, htz] with n hFn htn
    exact (hmono n htn.le).trans_lt hFn

private def pilotSubsequenceRowModel
    (theta h : TrialParameter) (eta : ℕ → TrialParameter)
    (p eps : ℝ) (m phi : ℕ → ℕ)
    (hselect : StrongSaddleSelection p eps select)
    (hp : InteriorAssignment p) (htheta : InteriorMeans theta)
    (heta : ∀ k, InteriorMeans (eta k)) (heps : 0 < eps)
    (hsub : PilotSublinear m) (hphi : StrictMono phi)
    (hetalim : Tendsto eta atTop (nhds theta)) : RowModel (Fin 14) where
  N k := adaptiveMainSize m (phi k)
  w k s := adaptiveMainMass select (adaptiveTrueParam theta h (phi k)) (eta k)
    p eps s
  f k s := adaptivePilotRowScore select theta h (fun _ => eta k)
    p eps hselect hp heps (phi k) s
  B := 2 * pilotPhiUpper p eps
  v₀ := adaptivePilotLimitVariance select theta p eps hselect hp htheta heps
  length_tendsto := (adaptiveMainSize_tendsto_atTop m hsub).comp hphi.tendsto_atTop
  mass_nonneg k s := adaptiveMainMass_nonneg select _ _ p eps hselect hp
    (adaptiveTrueParam_interior theta h (phi k) htheta) (heta k) heps s
  mass_one k := adaptiveMainMass_sum select _ _ p eps hselect hp (heta k) heps
  centered k := adaptivePilotRowScore_centered select theta h (fun _ => eta k)
    p eps hselect hp (fun _ => heta k) heps (phi k)
  bound k s := adaptivePilotRowScore_abs_le select theta h (fun _ => eta k)
    p eps hselect hp htheta (fun _ => heta k) heps (phi k) s
  variance_tendsto := by
    have htrue : Tendsto (fun k => adaptiveTrueParam theta h (phi k)) atTop (nhds theta) :=
      (adaptiveTrueParam_tendsto theta h htheta).comp hphi.tendsto_atTop
    have hpair : Tendsto (fun k =>
        (adaptiveTrueParam theta h (phi k), eta k)) atTop (nhds (theta, theta)) :=
      htrue.prodMk_nhds hetalim
    have hv := (continuousAt_adaptiveScoreVariance_diag select theta p eps hselect hp htheta heps).tendsto.comp hpair
    change Tendsto (fun k => ∑ s : Fin 14,
      adaptiveMainMass select (adaptiveTrueParam theta h (phi k)) (eta k) p eps s *
        (adaptivePilotRowScore select theta h (fun _ => eta k)
          p eps hselect hp heps (phi k) s) ^ 2)
      atTop (nhds (Vstar theta p eps))
    convert hv using 1
    · funext k
      exact adaptivePilotRow_secondMoment_eq select theta h (fun _ => eta k)
        p eps hselect hp (fun _ => heta k) heps (phi k)
    · simp [adaptiveScoreVariance_diag select theta p eps hselect hp htheta heps]
  variance_pos := adaptivePilotLimitVariance_pos select theta p eps hselect hp htheta heps

/-- Along every strict sample-size subsequence and every convergent sequence of interior
pilot selectors, the actual centered conditional main-row CDF converges to the oracle
Gaussian CDF under root-total-sample scaling. For [the displayed inputs and conditions](hyp:theta,h,p,eps,m), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:hselect,hp,htheta,heps,hsub,x,phi,hphi,eta,heta,hetalim), these specify the stated inputs. -/
theorem adaptivePilotRowScaledCDF_subsequence_tendsto_gaussian
    (theta h : TrialParameter) (p eps : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p eps select)
    (hp : InteriorAssignment p) (htheta : InteriorMeans theta)
    (heps : 0 < eps) (hsub : PilotSublinear m)
    (x : ℝ) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (eta : ℕ → TrialParameter) (heta : ∀ k, InteriorMeans (eta k))
    (hetalim : Tendsto eta atTop (nhds theta)) :
    Tendsto (fun k => adaptivePilotRowScaledCDF select theta h
      (fun _ => eta k) p eps m hselect hp heps (phi k) x) atTop
      (nhds ((gaussianMeasure 0 (Vstar theta p eps)).real (Set.Iic x))) := by
  let M := pilotSubsequenceRowModel select theta h eta p eps m phi hselect hp htheta heta heps
    hsub hphi hetalim
  let a : ℕ → ℝ := fun k =>
    Real.sqrt (((phi k : ℕ) : ℝ) / (adaptiveMainSize m (phi k) : ℝ))
  let t : ℕ → ℝ := fun k => x / a k
  have ha : Tendsto a atTop (nhds 1) := by
    exact (adaptive_row_main_sqrt_ratio_tendsto_one m hsub).comp hphi.tendsto_atTop
  have ht : Tendsto t atTop (nhds x) := by
    change Tendsto ((fun _ : ℕ => x) / a) atTop (nhds x)
    simpa using tendsto_const_nhds.div ha one_ne_zero
  have hMpoint (y : ℝ) : Tendsto (fun k => M.normalizedCDF k y) atTop
      (nhds (cdf (gaussianReal 0 M.v₀) y)) :=
    M.normalizedCDF_tendsto_gaussian y
  have hMmono (k : ℕ) : Monotone (M.normalizedCDF k) := by
    intro y z hyz
    unfold RowModel.normalizedCDF RowModel.expect
    apply Finset.sum_le_sum
    intro v _
    apply mul_le_mul_of_nonneg_left _ (M.mass_nonnegative k v)
    change (if M.normalizedSum k v ≤ y then 1 else 0) ≤
      if M.normalizedSum k v ≤ z then 1 else 0
    split_ifs with hy hz
    · exact le_rfl
    · exact (hz (hy.trans hyz)).elim
    · exact zero_le_one
    · exact le_rfl
  have hmoving : Tendsto (fun k => M.normalizedCDF k (t k)) atTop
      (nhds (cdf (gaussianReal 0 M.v₀) x)) :=
    tendsto_moving_of_monotone_pointwise (fun k => M.normalizedCDF k)
      (cdf (gaussianReal 0 M.v₀)) t x hMmono
      (Causalean.Stat.continuous_cdf_gaussianReal_zero M.variance_pos).continuousAt
      hMpoint ht
  have heq : ∀ᶠ k in atTop,
      adaptivePilotRowScaledCDF select theta h (fun _ => eta k)
        p eps m hselect hp heps (phi k) x = M.normalizedCDF k (t k) := by
    have hN : ∀ᶠ k in atTop, 0 < adaptiveMainSize m (phi k) := by
      exact (M.length_tendsto.eventually (eventually_ge_atTop 1)).mono
        (fun k hk => hk)
    filter_upwards [hN] with k hNk
    classical
    unfold adaptivePilotRowScaledCDF RowModel.normalizedCDF RowModel.expect
    apply Finset.sum_congr rfl
    intro v _
    dsimp only [adaptivePilotRowProductMass, adaptivePilotRowMass,
      M, pilotSubsequenceRowModel, RowModel.mass,
      RowModel.normalizedSum, RowModel.scoreSum, t, a]
    have hNr : 0 < (adaptiveMainSize m (phi k) : ℝ) := by exact_mod_cast hNk
    have hphir : 0 < (phi k : ℝ) := by
      have hle : adaptiveMainSize m (phi k) ≤ phi k := by
        unfold adaptiveMainSize
        omega
      exact_mod_cast lt_of_lt_of_le hNk hle
    have hsN : 0 < Real.sqrt (adaptiveMainSize m (phi k) : ℝ) :=
      Real.sqrt_pos.2 hNr
    have hsa : 0 < Real.sqrt ((phi k : ℝ) /
        (adaptiveMainSize m (phi k) : ℝ)) := Real.sqrt_pos.2 (div_pos hphir hNr)
    let S : ℝ := ∑ j, adaptivePilotRowScore select theta h (fun _ => eta k)
      p eps hselect hp heps (phi k) (v j)
    change
      (∏ j, adaptiveMainMass select (adaptiveTrueParam theta h (phi k)) (eta k)
          p eps (v j)) *
        (if Real.sqrt (phi k : ℝ) *
            (adaptiveMainSize m (phi k) : ℝ)⁻¹ * S ≤ x then 1 else 0) =
      (∏ j, adaptiveMainMass select (adaptiveTrueParam theta h (phi k)) (eta k)
          p eps (v j)) *
        (if (Real.sqrt (adaptiveMainSize m (phi k) : ℝ))⁻¹ * S ≤
            x / Real.sqrt ((phi k : ℝ) / (adaptiveMainSize m (phi k) : ℝ))
          then 1 else 0)
    have hscale : Real.sqrt (phi k : ℝ) *
          (adaptiveMainSize m (phi k) : ℝ)⁻¹ * S ≤ x ↔
        (Real.sqrt (adaptiveMainSize m (phi k) : ℝ))⁻¹ * S ≤
          x / Real.sqrt ((phi k : ℝ) /
            (adaptiveMainSize m (phi k) : ℝ)) := by
      rw [le_div_iff₀ hsa]
      rw [show Real.sqrt (phi k : ℝ) *
          (adaptiveMainSize m (phi k) : ℝ)⁻¹ * S =
          (Real.sqrt (adaptiveMainSize m (phi k) : ℝ))⁻¹ * S *
            Real.sqrt ((phi k : ℝ) / (adaptiveMainSize m (phi k) : ℝ)) by
        rw [Real.sqrt_div (Nat.cast_nonneg (phi k))]
        field_simp
        rw [Real.sq_sqrt hNr.le]
        ring]
    by_cases hc : Real.sqrt (phi k : ℝ) *
        (adaptiveMainSize m (phi k) : ℝ)⁻¹ * S ≤ x
    · rw [if_pos hc, if_pos (hscale.mp hc)]
    · rw [if_neg hc, if_neg (fun hz => hc (hscale.mpr hz))]
  have hfinal := hmoving.congr' (heq.mono fun _ hk => hk.symm)
  have htarget : cdf (gaussianReal 0 M.v₀) x =
      (gaussianMeasure 0 (Vstar theta p eps)).real (Set.Iic x) := by
    change cdf (gaussianReal 0 (adaptivePilotLimitVariance select theta p eps hselect hp htheta heps)) x = _
    rw [ProbabilityTheory.cdf_eq_real]
    unfold gaussianMeasure
    have hv : 0 ≤ Vstar theta p eps :=
      (inv_pos.mpr (Jstar_pos_interior theta p eps hp htheta heps)).le
    have hvar : adaptivePilotLimitVariance select theta p eps hselect hp htheta heps =
        (Vstar theta p eps).toNNReal := by
      apply NNReal.eq
      change Vstar theta p eps = max (Vstar theta p eps) 0
      exact (max_eq_left hv).symm
    rw [hvar]
  rw [htarget] at hfinal
  exact hfinal

end CausalSmith.Stat.LdpAteEfficiencySurface
