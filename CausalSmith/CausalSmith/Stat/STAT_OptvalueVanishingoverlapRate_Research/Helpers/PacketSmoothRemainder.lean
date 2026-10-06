module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.PacketKinkSeparation
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Smooth remainder in the packet response

Roadmap (22) and (25): the absolutely continuous curvature of the scalar
kink composition is uniformly bounded by a constant times M. Its pairing
with the localized twice antiderivative is therefore of order M/N².
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory


-- @node: packetRemainder
/-- The nonlinear remainder after subtracting the affine term in roadmap (10). For the displayed parameters, packetRemainder is the object specified by this definition. -/
 noncomputable def packetRemainder (ε z : ℝ) : ℝ := ε * max (1 - z) 0 + (1 - 2 * ε) * max (z - 1) 0 / (1 + z) -- @node: packetUpperCurvature 
/-- The curvature on the upper smooth arc, by the chain rule. For the displayed parameters, packetUpperCurvature is the object specified by this definition. -/
 noncomputable def packetUpperCurvature (M ε t : ℝ) : ℝ := -4 * (1 - 2 * ε) * (-(M / 2) * Real.sin t) ^ 2 / (1 + packetIntensity M t) ^ 3 + 2 * (1 - 2 * ε) * (-(M / 2) * Real.cos t) / (1 + packetIntensity M t) ^ 2 -- @node: packetSmoothCurvature 
/-- The density of the smooth second derivative; values at the two kinks are set to zero, since the derivative jumps are handled separately as atoms. For the displayed parameters, packetSmoothCurvature is the object specified by this definition. -/
 noncomputable def packetSmoothCurvature (M ε t : ℝ) : ℝ := if packetIntensity M t < 1 then ε * (M / 2) * Real.cos t else if 1 < packetIntensity M t then packetUpperCurvature M ε t else 0 
/-- The affine term and the nonlinear remainder recover the original functional. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hz), the [stated conclusion](goal) holds. -/
lemma phiEps_eq_packetRemainder {z : ℝ} (hz : 0 ≤ z) (ε : ℝ) :
    phiEpsFormula ε z = ε * (z - 1) + packetRemainder ε z := by
  have hd : 1 + z ≠ 0 := by linarith
  unfold phiEpsFormula packetRemainder
  by_cases h : 1 ≤ z
  · rw [max_eq_left (by linarith : 0 ≤ z - 1),
      max_eq_right (by linarith : 1 - z ≤ 0)]
    field_simp
    ring
  · rw [max_eq_right (by linarith : z - 1 ≤ 0),
      max_eq_left (by linarith : 0 ≤ 1 - z)]
    ring


-- @node: packetIntensity_hasDerivAt
/-- The cosine coordinate has the derivative used in roadmap (11). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetIntensity_hasDerivAt (M t : ℝ) :
    HasDerivAt (packetIntensity M) (-(M / 2) * Real.sin t) t := by
  convert ((Real.hasDerivAt_cos t).const_add 1).const_mul (M / 2) using 1 <;>
    first | rfl | ring


-- @node: packetIntensity_speed_sq
/-- The squared coordinate speed is z(M-z), keeping the curvature bound linear in M rather than quadratic. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetIntensity_speed_sq (M t : ℝ) :
    (-(M / 2) * Real.sin t) ^ 2 =
      packetIntensity M t * (M - packetIntensity M t) := by
  have h := Real.sin_sq_add_cos_sq t
  unfold packetIntensity
  nlinarith [sq_nonneg M]


-- @node: packetUpperBranch_hasDerivAt
/-- The upper smooth branch has the rational slope stated in roadmap (22). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
lemma packetUpperBranch_hasDerivAt {M : ℝ} (hM : 0 ≤ M) (ε t : ℝ) :
    HasDerivAt (fun s => (1 - 2 * ε) *
      (packetIntensity M s - 1) / (1 + packetIntensity M s))
      (2 * (1 - 2 * ε) * (-(M / 2) * Real.sin t) /
        (1 + packetIntensity M t) ^ 2) t := by
  have hd : 1 + packetIntensity M t ≠ 0 := by
    have := (packetIntensity_mem_Icc hM t).1
    linarith
  convert (((packetIntensity_hasDerivAt M t).sub_const 1).const_mul
      (1 - 2 * ε)).div ((packetIntensity_hasDerivAt M t).const_add 1) hd using 1 <;>
    first | rfl | (field_simp; ring)


-- @node: packetUpperSlope_hasDerivAt
/-- Differentiating the upper slope gives the actual chain-rule curvature. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
lemma packetUpperSlope_hasDerivAt {M : ℝ} (hM : 0 ≤ M) (ε t : ℝ) :
    HasDerivAt (fun s => 2 * (1 - 2 * ε) * (-(M / 2) * Real.sin s) /
      (1 + packetIntensity M s) ^ 2) (packetUpperCurvature M ε t) t := by
  have hd : 1 + packetIntensity M t ≠ 0 := by
    have := (packetIntensity_mem_Icc hM t).1
    linarith
  convert ((((Real.hasDerivAt_sin t).const_mul (-(M / 2))).const_mul
      (2 * (1 - 2 * ε))).div
      (((packetIntensity_hasDerivAt M t).const_add 1).pow 2)
      (pow_ne_zero 2 hd)) using 1 <;>
    first | rfl | (dsimp [packetUpperCurvature]; field_simp; ring)


-- @node: packetSmoothCurvature_eq_second_deriv
/-- On either open smooth arc the curvature density is exactly the ordinary second derivative of the nonlinear remainder composed with z(t). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM,ht), the [stated conclusion](goal) holds. -/
lemma packetSmoothCurvature_eq_second_deriv {M : ℝ} (hM : 0 ≤ M)
    (ε t : ℝ) (ht : packetIntensity M t ≠ 1) :
    deriv (deriv (fun s => packetRemainder ε (packetIntensity M s))) t =
      packetSmoothCurvature M ε t := by
  rcases lt_or_gt_of_ne ht with h | h
  · have hevent : ∀ᶠ s in nhds t, packetIntensity M s < 1 :=
      (continuous_packetIntensity M).continuousAt.eventually_lt continuousAt_const h
    have heq : (fun s => packetRemainder ε (packetIntensity M s)) =ᶠ[nhds t]
        (fun s => ε * (1 - packetIntensity M s)) := by
      filter_upwards [hevent] with s hs
      simp only [packetRemainder, max_eq_left (by linarith : 0 ≤ 1 - packetIntensity M s),
        max_eq_right (by linarith : packetIntensity M s - 1 ≤ 0), mul_zero, zero_div, add_zero]
    rw [heq.deriv.deriv_eq]
    have hfirst : deriv (fun s => ε * (1 - packetIntensity M s)) =
        (fun s => ε * (M / 2) * Real.sin s) := by
      funext s
      convert (((packetIntensity_hasDerivAt M s).const_sub 1).const_mul ε).deriv using 1 <;> ring
    rw [hfirst]
    rw [show packetSmoothCurvature M ε t = ε * (M / 2) * Real.cos t by
      simp [packetSmoothCurvature, h]]
    exact ((Real.hasDerivAt_sin t).const_mul (ε * (M / 2))).deriv
  · have hevent : ∀ᶠ s in nhds t, 1 < packetIntensity M s :=
      continuousAt_const.eventually_lt (continuous_packetIntensity M).continuousAt h
    have heq : (fun s => packetRemainder ε (packetIntensity M s)) =ᶠ[nhds t]
        (fun s => (1 - 2 * ε) * (packetIntensity M s - 1) /
          (1 + packetIntensity M s)) := by
      filter_upwards [hevent] with s hs
      simp only [packetRemainder, max_eq_right (by linarith : 1 - packetIntensity M s ≤ 0),
        max_eq_left (by linarith : 0 ≤ packetIntensity M s - 1), mul_zero, zero_add]
    rw [heq.deriv.deriv_eq]
    have hfirst : deriv (fun s => (1 - 2 * ε) * (packetIntensity M s - 1) /
        (1 + packetIntensity M s)) =
        (fun s => 2 * (1 - 2 * ε) * (-(M / 2) * Real.sin s) /
          (1 + packetIntensity M s) ^ 2) := by
      funext s
      exact (packetUpperBranch_hasDerivAt hM ε s).deriv
    rw [hfirst, (packetUpperSlope_hasDerivAt hM ε t).deriv]
    simp [packetSmoothCurvature, h, not_lt.mpr h.le]


-- @node: packetUpperCurvature_bound
/-- The smooth upper-arc curvature is bounded by 5M, uniformly in ε. The speed identity is essential here: estimating the sine factor alone would give the wrong power of M. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM,hε,hεhi), the [stated conclusion](goal) holds. -/
lemma packetUpperCurvature_bound {M ε : ℝ} (hM : 0 ≤ M)
    (hε : 0 ≤ ε) (hεhi : ε ≤ 1 / 2) (t : ℝ) :
    |packetUpperCurvature M ε t| ≤ 5 * M := by
  let z := packetIntensity M t
  have hz : 0 ≤ z := (packetIntensity_mem_Icc hM t).1
  have hzM : z ≤ M := (packetIntensity_mem_Icc hM t).2
  have ha : 0 ≤ 1 - 2 * ε := by linarith
  have ha1 : 1 - 2 * ε ≤ 1 := by linarith
  have hd : 0 < 1 + z := by linarith
  have hd2 : 1 ≤ (1 + z) ^ 2 := by nlinarith
  have hd3 : z ≤ (1 + z) ^ 3 := by nlinarith [sq_nonneg z, mul_nonneg hz (sq_nonneg z)]
  have hv : (-(M / 2) * Real.sin t) ^ 2 ≤ M * (1 + z) ^ 3 := by
    rw [packetIntensity_speed_sq]
    change z * (M - z) ≤ _
    calc
      _ ≤ M * z := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hd3 hM
  have hfirst : |-4 * (1 - 2 * ε) * (-(M / 2) * Real.sin t) ^ 2 /
      (1 + z) ^ 3| ≤ 4 * M := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg ha,
      abs_of_nonneg (sq_nonneg (-(M / 2) * Real.sin t)), abs_of_pos (pow_pos hd 3)]
    norm_num
    apply (div_le_iff₀ (pow_pos hd 3)).2
    have hv' := mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 4)
    have hcoef := mul_le_mul_of_nonneg_right ha1
      (sq_nonneg (-(M / 2) * Real.sin t))
    nlinarith
  have hcos : |Real.cos t| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
  have hsecond : |2 * (1 - 2 * ε) * (-(M / 2) * Real.cos t) /
      (1 + z) ^ 2| ≤ M := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg ha, abs_of_nonneg (by positivity : 0 ≤ M / 2),
      abs_of_pos (pow_pos hd 2)]
    norm_num
    apply (div_le_iff₀ (pow_pos hd 2)).2
    calc
      _ ≤ 2 * 1 * (M / 2 * 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ha1 (by norm_num))
          (mul_le_mul_of_nonneg_left hcos (by positivity)) (by positivity) (by norm_num)
      _ = M := by ring
      _ ≤ M * (1 + z) ^ 2 := le_mul_of_one_le_right hM hd2
  exact (abs_add_le _ _).trans (by
    change |-4 * (1 - 2 * ε) * (-(M / 2) * Real.sin t) ^ 2 / (1 + z) ^ 3| +
      |2 * (1 - 2 * ε) * (-(M / 2) * Real.cos t) / (1 + z) ^ 2| ≤ _
    linarith)


-- @node: packetSmoothCurvature_bound
/-- Both smooth arcs obey the same linear-in-M bound from roadmap (22). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM,hε,hεhi), the [stated conclusion](goal) holds. -/
lemma packetSmoothCurvature_bound {M ε : ℝ} (hM : 0 ≤ M)
    (hε : 0 ≤ ε) (hεhi : ε ≤ 1 / 2) (t : ℝ) :
    |packetSmoothCurvature M ε t| ≤ 5 * M := by
  unfold packetSmoothCurvature
  split_ifs
  · rw [abs_mul, abs_mul, abs_of_nonneg hε,
      abs_of_nonneg (by positivity : 0 ≤ M / 2)]
    have hc : |Real.cos t| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
    calc
      _ ≤ (1 / 2) * (M / 2) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hεhi (by positivity)) hc
          (abs_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith
  · exact packetUpperCurvature_bound hM hε hεhi t
  · simp only [abs_zero]
    positivity


-- @node: packetRemainder_second_deriv_bound
/-- Roadmap (22), stated directly for the original composed remainder on each smooth arc. No regularity or curvature hypothesis is assumed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM,hε,hεhi,ht), the [stated conclusion](goal) holds. -/
lemma packetRemainder_second_deriv_bound {M ε : ℝ} (hM : 0 ≤ M)
    (hε : 0 ≤ ε) (hεhi : ε ≤ 1 / 2) (t : ℝ)
    (ht : packetIntensity M t ≠ 1) :
    |deriv (deriv (fun s => packetRemainder ε (packetIntensity M s))) t| ≤ 5 * M := by
  rw [packetSmoothCurvature_eq_second_deriv hM ε t ht]
  exact packetSmoothCurvature_bound hM hε hεhi t

/-- The finite Fourier antiderivative is continuous. The [stated conclusion](goal) holds. -/
-- @node: continuous_packetAntideriv
@[fun_prop] lemma continuous_packetAntideriv (N : ℕ) :
    Continuous (packetAntideriv N) := by
  unfold packetAntideriv
  fun_prop


-- @node: packetAntideriv_periodic
/-- Every integer Fourier frequency of the antiderivative has period 2π. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetAntideriv_periodic (N : ℕ) :
    Function.Periodic (packetAntideriv N) (2 * Real.pi) := by
  intro t
  unfold packetAntideriv
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg₂ (fun x y => packetCoeffPlus N j * x + packetCoeffMinus N j * y)
    (packet_cos_periodic (4 * (N : ℤ) + j) t)
    (packet_cos_periodic (4 * (N : ℤ) - j) t)

/-- The smooth curvature density is measurable, despite the two jumps. The [stated conclusion](goal) holds. -/
-- @node: measurable_packetSmoothCurvature
@[fun_prop]
lemma measurable_packetSmoothCurvature (M ε : ℝ) :
    Measurable (packetSmoothCurvature M ε) := by
  unfold packetSmoothCurvature
  apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop)
  apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
    (by unfold packetUpperCurvature; fun_prop) measurable_const

-- @node: packetSmoothCurvature_integrable
/-- The smooth density is integrable on the circle, without additional regularity premises. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM,hε,hεhi), the [stated conclusion](goal) holds. -/
lemma packetSmoothCurvature_integrable {M ε : ℝ} (hM : 0 ≤ M)
    (hε : 0 ≤ ε) (hεhi : ε ≤ 1 / 2) :
    Integrable (packetSmoothCurvature M ε)
      (volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
  apply Integrable.of_bound (by fun_prop) (5 * M)
  filter_upwards with t
  simpa only [Real.norm_eq_abs] using packetSmoothCurvature_bound hM hε hεhi t


-- @node: packetSmoothRemainder_bound
/-- Circle translation preserves the Jackson L¹ bound, so the smooth term in roadmap (25) has absolute value at most CM/N² for every center. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetSmoothRemainder_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (M ε θ : ℝ),
      2 ≤ N → 0 ≤ M → 0 ≤ ε → ε ≤ 1 / 2 →
      |∫ t in Set.Icc (-Real.pi) Real.pi,
        packetSmoothCurvature M ε t * packetAntideriv N (t - θ) /
          (2 * Real.pi)| ≤ C * M / (N : ℝ) ^ 2 := by
  obtain ⟨c, C, hc, hcC, hpacket⟩ := jackson_packet_localization
  refine ⟨5 * C, by linarith, ?_⟩
  intro N M ε θ hN hM hε hεhi
  have hG : Integrable (fun t => |packetAntideriv N (t - θ)| / (2 * Real.pi))
      (volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    fun_prop
  have hperiod : Function.Periodic (fun t => |packetAntideriv N t| / (2 * Real.pi))
      (2 * Real.pi) := by
    intro t
    exact congrArg (fun x => |x| / (2 * Real.pi)) (packetAntideriv_periodic N t)
  have hshift := packet_periodic_integral_translate
    (fun t => |packetAntideriv N t| / (2 * Real.pi)) hperiod θ
  have hl1 := (hpacket N hN).2.2.2.2.2.2.2.2.2.2.2
  have hbound : |∫ t in Set.Icc (-Real.pi) Real.pi,
        packetSmoothCurvature M ε t * packetAntideriv N (t - θ) /
          (2 * Real.pi)| ≤
      ∫ t in Set.Icc (-Real.pi) Real.pi,
        (5 * M) * (|packetAntideriv N (t - θ)| / (2 * Real.pi)) := by
    apply (show ‖∫ t in Set.Icc (-Real.pi) Real.pi,
        packetSmoothCurvature M ε t * packetAntideriv N (t - θ) / (2 * Real.pi)‖ ≤ _ from
      norm_integral_le_of_norm_le (hG.const_mul (5 * M)) ?_)
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    calc
      _ ≤ (5 * M) * |packetAntideriv N (t - θ)| / (2 * Real.pi) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (packetSmoothCurvature_bound hM hε hεhi t)
            (abs_nonneg _)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ _ := hbound
    _ = (5 * M) * ∫ t in Set.Icc (-Real.pi) Real.pi,
        |packetAntideriv N (t - θ)| / (2 * Real.pi) := integral_const_mul _ _
    _ = (5 * M) * ∫ t in Set.Icc (-Real.pi) Real.pi,
        |packetAntideriv N t| / (2 * Real.pi) := by rw [hshift]
    _ ≤ (5 * M) * (C / (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hl1 (by positivity)
    _ = _ := by ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate
