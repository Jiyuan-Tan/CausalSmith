module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.PacketSmoothRemainder
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Integration by parts for the localized packet

The two integrations retain the endpoint slopes on each smooth arc.
These boundary terms supply the kink atoms in roadmap (25).
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory

/-- Finite Fourier construction supplies all differentiability needed for integration by parts, without extra packet regularity hypotheses. The [stated conclusion](goal) holds. -/
-- @node: contDiff_packetAntideriv
@[fun_prop] lemma contDiff_packetAntideriv (N : ℕ) :
    ContDiff ℝ 2 (packetAntideriv N) := by
  unfold packetAntideriv
  fun_prop


-- @node: packet_arc_integration_by_parts
/-- Twice integration by parts on one smooth arc, with the actual translated Jackson packet. The endpoint slopes are retained rather than discarded. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hN,hf,hf',hc), the [stated conclusion](goal) holds. -/
lemma packet_arc_integration_by_parts {N : ℕ} (hN : 2 ≤ N)
    (θ a b : ℝ) (f f' f'' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t)
    (hc : Continuous f'') :
    (∫ t in a..b, f t * packetOscillation N (t - θ)) =
      f b * deriv (packetAntideriv N) (b - θ) -
        f a * deriv (packetAntideriv N) (a - θ) -
        f' b * packetAntideriv N (b - θ) +
        f' a * packetAntideriv N (a - θ) +
        ∫ t in a..b, f'' t * packetAntideriv N (t - θ) := by
  have hG := contDiff_packetAntideriv N
  have hdG := hG.differentiable (by norm_num)
  have hdG' := hG.differentiable_deriv_two
  have hcG' := hG.continuous_deriv (by norm_num)
  have hfirst (t : ℝ) : HasDerivAt (fun s => packetAntideriv N (s - θ))
      (deriv (packetAntideriv N) (t - θ)) t := by
    simpa only [Function.comp_def, mul_one, id_eq] using
      (hdG (t - θ)).hasDerivAt.comp t ((hasDerivAt_id t).sub_const θ)
  have hsecond (t : ℝ) : HasDerivAt (fun s => deriv (packetAntideriv N) (s - θ))
      (packetOscillation N (t - θ)) t := by
    obtain ⟨c, C, hc, hcC, hp⟩ := jackson_packet_localization
    have he := (hp N hN).2.2.2.2.2.2.1 (t - θ)
    simpa only [he, mul_one, Function.comp_def, id_eq] using
      (hdG' (t - θ)).hasDerivAt.comp t ((hasDerivAt_id t).sub_const θ)
  have hcF' : Continuous f' := continuous_iff_continuousAt.mpr
    (fun t => (hf' t).continuousAt)
  have hi1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => hf t) (fun t ht => hsecond t)
    (hcF'.intervalIntegrable a b)
    ((show Continuous (fun t => packetOscillation N (t - θ)) from
      by unfold packetOscillation packetKernel; fun_prop (disch := exact
        Causalean.Mathlib.Analysis.JacksonApproximation.continuous_jackson _)
      ).intervalIntegrable a b)
  have hi2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => hf' t) (fun t ht => hfirst t)
    (hc.intervalIntegrable a b)
    ((hcG'.comp (by fun_prop)).intervalIntegrable a b)
  rw [hi1, hi2]
  ring


-- @node: packetKink_intensity_speed
/-- The exact intensity and speed at the two kinks. The speed determines the atomic mass, uniformly in the overlap parameter. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
lemma packetKink_intensity_speed {M : ℝ} (hM : 2 ≤ M) :
    let θ := Real.arccos (2 / M - 1)
    packetIntensity M θ = 1 ∧
      (M / 2) * Real.sin θ = Real.sqrt (M - 1) := by
  dsimp only
  let θ := Real.arccos (2 / M - 1)
  have hm : 0 < M := by linarith
  have hr : 2 / M ≤ 1 := (div_le_one hm).2 hM
  have hc : Real.cos θ = 2 / M - 1 :=
    Real.cos_arccos (by linarith [div_pos (by norm_num : (0 : ℝ) < 2) hm])
      (by linarith)
  have hz : packetIntensity M θ = 1 := by
    unfold packetIntensity
    rw [hc]
    field_simp
    ring
  refine ⟨hz, ?_⟩
  have hv := packetIntensity_speed_sq M θ
  rw [hz] at hv
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (Real.arccos_nonneg (2 / M - 1)) (Real.arccos_le_pi _)
  have hp : 0 ≤ (M / 2) * Real.sin θ := mul_nonneg (by positivity) hs
  have hroot := Real.sq_sqrt (show 0 ≤ M - 1 by linarith)
  have hrootpos := Real.sqrt_nonneg (M - 1)
  change (M / 2) * Real.sin θ = Real.sqrt (M - 1)
  nlinarith


-- @node: packetKink_smooth_arcs
/-- On the central arc the intensity is strictly above one; on the outer arcs it is strictly below one. Endpoints are excluded to retain kink atoms. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
lemma packetKink_smooth_arcs {M : ℝ} (hM : 2 ≤ M) :
    let θ := Real.arccos (2 / M - 1)
    (∀ t ∈ Set.Ioo (-θ) θ, 1 < packetIntensity M t) ∧
    (∀ t ∈ Set.Ioo (-Real.pi) (-θ), packetIntensity M t < 1) ∧
    (∀ t ∈ Set.Ioo θ Real.pi, packetIntensity M t < 1) := by
  dsimp only
  let θ := Real.arccos (2 / M - 1)
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθpi : θ ≤ Real.pi := Real.arccos_le_pi _
  have hz := (packetKink_intensity_speed hM).1
  change packetIntensity M θ = 1 at hz
  have hpos : 0 < M / 2 := by linarith
  have heven (t : ℝ) : packetIntensity M (-t) = packetIntensity M t := by
    simp only [packetIntensity, Real.cos_neg]
  have hright (t : ℝ) (ht : t ∈ Set.Ioo θ Real.pi) : packetIntensity M t < 1 := by
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hθ0 ht.2.le ht.1
    rw [← hz]
    exact mul_lt_mul_of_pos_left (by linarith) hpos
  refine ⟨?_, ?_, fun t ht => hright t ht⟩
  · intro t ht
    have habs : |t| < θ := abs_lt.mpr ⟨ht.1, ht.2⟩
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t) hθpi habs
    rw [Real.cos_abs] at hc
    rw [← hz]
    exact mul_lt_mul_of_pos_left (by linarith) hpos
  · intro t ht
    rw [← heven t]
    exact hright (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩


-- @node: packetAntideriv_deriv_periodic
/-- Differentiating the periodic Fourier series retains the circle period, so the outer boundary terms cancel in integration by parts. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetAntideriv_deriv_periodic (N : ℕ) :
    Function.Periodic (deriv (packetAntideriv N)) (2 * Real.pi) := by
  intro t
  have he : (fun s => packetAntideriv N (s + 2 * Real.pi)) = packetAntideriv N :=
    funext (packetAntideriv_periodic N)
  have hd := congrArg (fun f : ℝ → ℝ => deriv f t) he
  rw [deriv_comp_add_const] at hd
  exact hd


-- @node: packetRemainder_integration_by_parts
/-- Twice integration by parts on the three smooth arcs, with both derivative jumps retained. This is roadmap (25), for any translated packet center. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hN,hM,hε,hεhi), the [stated conclusion](goal) holds. -/
lemma packetRemainder_integration_by_parts {N : ℕ} (hN : 2 ≤ N)
    {M ε : ℝ} (hM : 2 ≤ M) (hε : 0 ≤ ε) (hεhi : ε ≤ 1 / 2) (center : ℝ) :
    let θ := Real.arccos (2 / M - 1)
    (∫ t in Set.Icc (-Real.pi) Real.pi,
      packetRemainder ε (packetIntensity M t) * packetOscillation N (t - center) /
        (2 * Real.pi)) =
    (∫ t in Set.Icc (-Real.pi) Real.pi,
      packetSmoothCurvature M ε t * packetAntideriv N (t - center) /
        (2 * Real.pi)) +
      (Real.sqrt (M - 1) / 2) / (2 * Real.pi) *
        (packetAntideriv N (θ - center) + packetAntideriv N (-θ - center)) := by
  dsimp only
  let θ := Real.arccos (2 / M - 1)
  let f₀ := fun t => ε * (1 - packetIntensity M t)
  let v₀ := fun t => ε * (M / 2) * Real.sin t
  let a₀ := fun t => ε * (M / 2) * Real.cos t
  let f₁ := fun t => (1 - 2 * ε) * (packetIntensity M t - 1) /
    (1 + packetIntensity M t)
  let v₁ := fun t => 2 * (1 - 2 * ε) * (-(M / 2) * Real.sin t) /
    (1 + packetIntensity M t) ^ 2
  let F := fun t => packetRemainder ε (packetIntensity M t) *
    packetOscillation N (t - center)
  let R := fun t => packetSmoothCurvature M ε t * packetAntideriv N (t - center)
  have hm : 0 ≤ M := by linarith
  have hd (t : ℝ) : 1 + packetIntensity M t ≠ 0 := by
    have hz := (packetIntensity_mem_Icc hm t).1
    linarith
  have hf₀ (t : ℝ) : HasDerivAt f₀ (v₀ t) t := by
    dsimp [f₀, v₀]
    convert ((packetIntensity_hasDerivAt M t).const_sub 1).const_mul ε using 1 <;>
      first | rfl | ring
  have hv₀ (t : ℝ) : HasDerivAt v₀ (a₀ t) t :=
    (Real.hasDerivAt_sin t).const_mul (ε * (M / 2))
  have hf₁ (t : ℝ) : HasDerivAt f₁ (v₁ t) t := packetUpperBranch_hasDerivAt hm ε t
  have hv₁ (t : ℝ) : HasDerivAt v₁ (packetUpperCurvature M ε t) t :=
    packetUpperSlope_hasDerivAt hm ε t
  have ha₁ : Continuous (packetUpperCurvature M ε) := by
    unfold packetUpperCurvature
    fun_prop (disch := intro t; exact pow_ne_zero _ (hd t))
  have hleft := packet_arc_integration_by_parts hN center (-Real.pi) (-θ)
    f₀ v₀ a₀ hf₀ hv₀ (by fun_prop)
  have hmiddle := packet_arc_integration_by_parts hN center (-θ) θ
    f₁ v₁ (packetUpperCurvature M ε) hf₁ hv₁ ha₁
  have hright := packet_arc_integration_by_parts hN center θ Real.pi
    f₀ v₀ a₀ hf₀ hv₀ (by fun_prop)
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθpi : θ ≤ Real.pi := Real.arccos_le_pi _
  obtain ⟨hcentral, houterleft, houterright⟩ := packetKink_smooth_arcs hM
  have hlo : -Real.pi ≤ -θ := by linarith
  have hmid : -θ ≤ θ := by linarith
  have hhi : θ ≤ Real.pi := hθpi
  have hF : Continuous F := by
    dsimp [F, packetRemainder]
    unfold packetOscillation packetKernel
    fun_prop (disch := first | exact hd _ | exact
      Causalean.Mathlib.Analysis.JacksonApproximation.continuous_jackson _)
  have hRi : IntervalIntegrable R volume (-Real.pi) Real.pi := by
    have hi : IntervalIntegrable (packetSmoothCurvature M ε) volume (-Real.pi) Real.pi :=
      (show IntegrableOn (packetSmoothCurvature M ε) (Set.uIcc (-Real.pi) Real.pi) volume
        by
          rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
          exact packetSmoothCurvature_integrable hm hε hεhi).intervalIntegrable
    exact hi.mul_continuousOn
      (show ContinuousOn (fun t => packetAntideriv N (t - center))
        (Set.uIcc (-Real.pi) Real.pi) by fun_prop)
  have he₀ (t : ℝ) (ht : packetIntensity M t < 1) :
      packetRemainder ε (packetIntensity M t) = f₀ t ∧
        packetSmoothCurvature M ε t = a₀ t := by
    simp [packetRemainder, packetSmoothCurvature, f₀, a₀, ht,
      max_eq_left (by linarith : 0 ≤ 1 - packetIntensity M t),
      max_eq_right (by linarith : packetIntensity M t - 1 ≤ 0)]
  have he₁ (t : ℝ) (ht : 1 < packetIntensity M t) :
      packetRemainder ε (packetIntensity M t) = f₁ t ∧
        packetSmoothCurvature M ε t = packetUpperCurvature M ε t := by
    simp [packetRemainder, packetSmoothCurvature, f₁, ht, not_lt.mpr ht.le,
      max_eq_right (by linarith : 1 - packetIntensity M t ≤ 0),
      max_eq_left (by linarith : 0 ≤ packetIntensity M t - 1)]
  have hFl : (∫ t in -Real.pi..-θ, F t) =
      ∫ t in -Real.pi..-θ, f₀ t * packetOscillation N (t - center) :=
    intervalIntegral.integral_congr_Ioo_of_le hlo
      (fun t ht => congrArg (fun x => x * packetOscillation N (t - center))
        (he₀ t (houterleft t ht)).1)
  have hFm : (∫ t in -θ..θ, F t) =
      ∫ t in -θ..θ, f₁ t * packetOscillation N (t - center) :=
    intervalIntegral.integral_congr_Ioo_of_le hmid
      (fun t ht => congrArg (fun x => x * packetOscillation N (t - center))
        (he₁ t (hcentral t ht)).1)
  have hFr : (∫ t in θ..Real.pi, F t) =
      ∫ t in θ..Real.pi, f₀ t * packetOscillation N (t - center) :=
    intervalIntegral.integral_congr_Ioo_of_le hhi
      (fun t ht => congrArg (fun x => x * packetOscillation N (t - center))
        (he₀ t (houterright t ht)).1)
  have hRl : (∫ t in -Real.pi..-θ, R t) =
      ∫ t in -Real.pi..-θ, a₀ t * packetAntideriv N (t - center) :=
    intervalIntegral.integral_congr_Ioo_of_le hlo
      (fun t ht => congrArg (fun x => x * packetAntideriv N (t - center))
        (he₀ t (houterleft t ht)).2)
  have hRm : (∫ t in -θ..θ, R t) =
      ∫ t in -θ..θ, packetUpperCurvature M ε t * packetAntideriv N (t - center) :=
    intervalIntegral.integral_congr_Ioo_of_le hmid
      (fun t ht => congrArg (fun x => x * packetAntideriv N (t - center))
        (he₁ t (hcentral t ht)).2)
  have hRr : (∫ t in θ..Real.pi, R t) =
      ∫ t in θ..Real.pi, a₀ t * packetAntideriv N (t - center) :=
    intervalIntegral.integral_congr_Ioo_of_le hhi
      (fun t ht => congrArg (fun x => x * packetAntideriv N (t - center))
        (he₀ t (houterright t ht)).2)
  have hFsplit : (∫ t in -Real.pi..Real.pi, F t) =
      (∫ t in -Real.pi..-θ, F t) + (∫ t in -θ..θ, F t) +
        (∫ t in θ..Real.pi, F t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (-Real.pi) (-θ)) (hF.intervalIntegrable (-θ) θ),
      intervalIntegral.integral_add_adjacent_intervals
        (hF.intervalIntegrable (-Real.pi) θ) (hF.intervalIntegrable θ Real.pi)]
  have hRsplit : (∫ t in -Real.pi..Real.pi, R t) =
      (∫ t in -Real.pi..-θ, R t) + (∫ t in -θ..θ, R t) +
        (∫ t in θ..Real.pi, R t) := by
    have hil := hRi.mono_set (show Set.uIcc (-Real.pi) (-θ) ⊆
      Set.uIcc (-Real.pi) Real.pi by
        rw [Set.uIcc_of_le hlo, Set.uIcc_of_le (by linarith [Real.pi_pos])]
        exact Set.Icc_subset_Icc le_rfl (by linarith))
    have him := hRi.mono_set (show Set.uIcc (-θ) θ ⊆ Set.uIcc (-Real.pi) Real.pi by
      rw [Set.uIcc_of_le hmid, Set.uIcc_of_le (by linarith [Real.pi_pos])]
      exact Set.Icc_subset_Icc hlo hhi)
    have hir := hRi.mono_set (show Set.uIcc θ Real.pi ⊆ Set.uIcc (-Real.pi) Real.pi by
      rw [Set.uIcc_of_le hhi, Set.uIcc_of_le (by linarith [Real.pi_pos])]
      exact Set.Icc_subset_Icc (by linarith) le_rfl)
    rw [intervalIntegral.integral_add_adjacent_intervals hil him,
      intervalIntegral.integral_add_adjacent_intervals (hil.trans him) hir]
  obtain ⟨hz, hs⟩ := packetKink_intensity_speed hM
  change packetIntensity M θ = 1 at hz
  change (M / 2) * Real.sin θ = Real.sqrt (M - 1) at hs
  have hzneg : packetIntensity M (-θ) = 1 := by
    simpa only [packetIntensity, Real.cos_neg] using hz
  have hperiod := packetAntideriv_deriv_periodic N (-Real.pi - center)
  have harg : -Real.pi - center + 2 * Real.pi = Real.pi - center := by ring
  rw [harg] at hperiod
  have hboundary : f₀ θ = 0 ∧ f₀ (-θ) = 0 ∧ f₁ θ = 0 ∧ f₁ (-θ) = 0 := by
    simp [f₀, f₁, hz, hzneg]
  have hvpos : v₀ θ - v₁ θ = Real.sqrt (M - 1) / 2 := by
    dsimp [v₀, v₁]
    rw [hz]
    norm_num
    nlinarith only [hs]
  have hvneg : v₁ (-θ) - v₀ (-θ) = Real.sqrt (M - 1) / 2 := by
    dsimp [v₀, v₁]
    rw [hzneg, Real.sin_neg]
    norm_num
    nlinarith only [hs]
  have hmain : (∫ t in -Real.pi..Real.pi, F t) =
      (∫ t in -Real.pi..Real.pi, R t) +
        (Real.sqrt (M - 1) / 2) *
          (packetAntideriv N (θ - center) + packetAntideriv N (-θ - center)) := by
    rw [hFsplit, hFl, hFm, hFr, hleft, hmiddle, hright,
      hRsplit, hRl, hRm, hRr]
    rcases hboundary with ⟨hb₀, hb₀n, hb₁, hb₁n⟩
    rw [hb₀, hb₀n, hb₁, hb₁n]
    have hep : f₀ Real.pi = ε := by simp [f₀, packetIntensity]
    have hen : f₀ (-Real.pi) = ε := by simp [f₀, packetIntensity]
    have hsp : v₀ Real.pi = 0 := by simp [v₀]
    have hsn : v₀ (-Real.pi) = 0 := by simp [v₀]
    rw [hep, hen, hsp, hsn, hperiod]
    linear_combination packetAntideriv N (θ - center) * hvpos +
      packetAntideriv N (-θ - center) * hvneg
  rw [integral_div, integral_div, integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  change (∫ t in -Real.pi..Real.pi, F t) / (2 * Real.pi) =
    (∫ t in -Real.pi..Real.pi, R t) / (2 * Real.pi) + _
  rw [hmain]
  ring


-- @node: packetAntideriv_even
/-- Evenness of the finite cosine antiderivative identifies the opposite kink in the exact response formula. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetAntideriv_even (N : ℕ) (u : ℝ) :
    packetAntideriv N (-u) = packetAntideriv N u := by
  unfold packetAntideriv
  simp only [mul_neg, Real.cos_neg]


-- @node: packetRemainder_response_lower
/-- The uniform lower response of one localized packet, roadmap (28). The universal scale suppresses both the opposite kink and the smooth term; no response bound or integration identity is assumed. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetRemainder_response_lower :
    ∃ (c : ℝ) (A : ℕ), 0 < c ∧ 1 ≤ A ∧
      ∀ (K : ℕ) (M ε : ℝ), 2 ≤ K → 2 ≤ M → M ≤ (K : ℝ) ^ 2 →
        0 ≤ ε → ε ≤ 1 / 2 →
        c * Real.sqrt M / K ≤
          |∫ t in Set.Icc (-Real.pi) Real.pi,
            packetRemainder ε (packetIntensity M t) *
              packetOscillation (A * K) (t - Real.arccos (2 / M - 1)) /
                (2 * Real.pi)| := by
  obtain ⟨c, Ccenter, hc, _, hpacket⟩ := jackson_packet_localization
  obtain ⟨Co, hCo, hopposite⟩ := packetKink_antideriv_bound
  obtain ⟨Cs, hCs, hsmooth⟩ := packetSmoothRemainder_bound
  obtain ⟨A, hA⟩ := exists_nat_gt
    (max 1 (max (2 * Co / c) (32 * Real.pi * Cs / c)))
  have hA1R : (1 : ℝ) ≤ A := (le_max_left _ _).trans hA.le
  have hA1 : 1 ≤ A := by exact_mod_cast hA1R
  have hAR : (0 : ℝ) < A := by linarith only [hA1R]
  have hAo : 2 * Co ≤ c * (A : ℝ) ^ 2 := by
    have ha : 2 * Co / c ≤ A :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hA.le)
    have hb := (div_le_iff₀ hc).mp ha
    have hsq : (A : ℝ) ≤ (A : ℝ) ^ 2 := by nlinarith only [hA1R]
    nlinarith only [hb, mul_le_mul_of_nonneg_left hsq hc.le]
  have hAs : 32 * Real.pi * Cs ≤ c * (A : ℝ) := by
    have ha : 32 * Real.pi * Cs / c ≤ A :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hA.le)
    simpa only [mul_comm] using (div_le_iff₀ hc).mp ha
  refine ⟨c / (32 * Real.pi * A), A, by positivity, hA1, ?_⟩
  intro K M ε hK hM hMhi hε hεhi
  let N := A * K
  let θ := Real.arccos (2 / M - 1)
  have hN : 2 ≤ N := by dsimp [N]; nlinarith only [hA1, hK]
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hNcast : (N : ℝ) = (A : ℝ) * K := by simp only [N, Nat.cast_mul]
  have hm : 0 ≤ M := by linarith only [hM]
  have hroot : 0 < Real.sqrt M := Real.sqrt_pos.2 (by linarith only [hM])
  have hrootK : Real.sqrt M ≤ K := by
    nlinarith only [Real.sq_sqrt hm, hMhi, Real.sqrt_nonneg M, hk]
  have hcenter : c / (N : ℝ) ≤ |packetAntideriv N 0| :=
    (hpacket N hN).2.2.2.2.2.2.2.2.1
  have hsmall : |packetAntideriv N (2 * θ)| ≤ c / (2 * N) := by
    apply (hopposite N M hN hM).trans
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ 3)
      (by positivity : (0 : ℝ) < 2 * N)).mpr
    have hh : 2 * Co * M ≤ c * (N : ℝ) ^ 2 := by
      calc
        _ ≤ 2 * Co * (K : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hMhi (by positivity)
        _ ≤ (c * (A : ℝ) ^ 2) * (K : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hAo (sq_nonneg _)
        _ = _ := by rw [hNcast]; ring
    nlinarith only [mul_le_mul_of_nonneg_right hh hn.le]
  have hsum : c / (2 * N) ≤ |packetAntideriv N 0 + packetAntideriv N (2 * θ)| := by
    have hh := abs_add_le (packetAntideriv N 0 + packetAntideriv N (2 * θ))
      (-packetAntideriv N (2 * θ))
    simp only [add_neg_cancel_right, abs_neg] at hh
    have he : c / (N : ℝ) = 2 * (c / (2 * N)) := by ring
    rw [he] at hcenter
    linarith only [hh, hcenter, hsmall]
  have hrootlo : Real.sqrt M / 2 ≤ Real.sqrt (M - 1) := by
    nlinarith only [Real.sq_sqrt hm, Real.sq_sqrt (show 0 ≤ M - 1 by linarith),
      Real.sqrt_nonneg M, Real.sqrt_nonneg (M - 1), hM]
  have hatom : c * Real.sqrt M / (16 * Real.pi * N) ≤
      |(Real.sqrt (M - 1) / 2) / (2 * Real.pi) *
        (packetAntideriv N 0 + packetAntideriv N (2 * θ))| := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt (M - 1) / 2) /
      (2 * Real.pi))]
    have hcoeff : Real.sqrt M / (8 * Real.pi) ≤
        (Real.sqrt (M - 1) / 2) / (2 * Real.pi) := by
      calc
        _ = (Real.sqrt M / 4) / (2 * Real.pi) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hrootlo]) (by positivity)
    calc
      _ = (Real.sqrt M / (8 * Real.pi)) * (c / (2 * N)) := by ring
      _ ≤ _ := mul_le_mul hcoeff hsum (by positivity) (by positivity)
  have hrem := hsmooth N M ε θ hN hm hε hεhi
  have hremSmall : Cs * M / (N : ℝ) ^ 2 ≤
      c * Real.sqrt M / (32 * Real.pi * N) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ 2)
      (by positivity : (0 : ℝ) < 32 * Real.pi * N)).mpr
    have hh : 32 * Real.pi * Cs * Real.sqrt M ≤ c * (N : ℝ) := by
      calc
        _ ≤ 32 * Real.pi * Cs * (K : ℝ) :=
          mul_le_mul_of_nonneg_left hrootK (by positivity)
        _ ≤ (c * A) * (K : ℝ) := mul_le_mul_of_nonneg_right hAs hk.le
        _ = _ := by rw [hNcast]; ring
    have hh' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg M)) hn.le
    rw [mul_assoc (32 * Real.pi * Cs), Real.mul_self_sqrt hm] at hh'
    nlinarith only [hh']
  have he := packetRemainder_integration_by_parts hN hM hε hεhi θ
  change (∫ t in Set.Icc (-Real.pi) Real.pi,
      packetRemainder ε (packetIntensity M t) * packetOscillation N (t - θ) /
        (2 * Real.pi)) =
    (∫ t in Set.Icc (-Real.pi) Real.pi,
      packetSmoothCurvature M ε t * packetAntideriv N (t - θ) / (2 * Real.pi)) +
        (Real.sqrt (M - 1) / 2) / (2 * Real.pi) *
          (packetAntideriv N (θ - θ) + packetAntideriv N (-θ - θ)) at he
  have harg : -θ - θ = -(2 * θ) := by ring
  simp only [sub_self, harg, packetAntideriv_even] at he
  rw [he]
  have hh := abs_add_le
    ((∫ t in Set.Icc (-Real.pi) Real.pi,
      packetSmoothCurvature M ε t * packetAntideriv N (t - θ) / (2 * Real.pi)) +
        (Real.sqrt (M - 1) / 2) / (2 * Real.pi) *
          (packetAntideriv N 0 + packetAntideriv N (2 * θ)))
    (-(∫ t in Set.Icc (-Real.pi) Real.pi,
      packetSmoothCurvature M ε t * packetAntideriv N (t - θ) / (2 * Real.pi)))
  simp only [add_neg_cancel_comm, abs_neg] at hh
  have hscale : (c / (32 * Real.pi * A)) * Real.sqrt M / K =
      c * Real.sqrt M / (32 * Real.pi * N) := by rw [hNcast]; ring
  have htwice : c * Real.sqrt M / (16 * Real.pi * N) =
      2 * (c * Real.sqrt M / (32 * Real.pi * N)) := by ring
  rw [hscale]
  rw [htwice] at hatom
  linarith only [hh, hatom, hrem, hremSmall]

end CausalSmith.Stat.OptvalueVanishingoverlapRate
