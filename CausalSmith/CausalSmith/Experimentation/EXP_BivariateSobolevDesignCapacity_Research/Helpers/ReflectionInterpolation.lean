module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionProfileEndpoint
public import Causalean.Mathlib.Analysis.RealInterpolation.Weighted

/-! # Weighted interpolation on the ambient frequency L² space

The weighted measurable-function minimizer belongs to the ambient L² space
when the first-order weight dominates one. Thus restricting the decomposition
infimum to L² classes preserves the exact normalized interpolation energy.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
open Causalean.Mathlib.Analysis.RealInterpolation

/-- [ The unweighted measurable-function gauge is the ambient L² norm.](goal) -/
-- @node: reflection_wNorm_one_eq_enorm
lemma reflection_wNorm_one_eq_enorm {S : Type} [MeasurableSpace S]
    (μ : Measure S) (f : Lp ℂ 2 μ) :
    Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun _ => 1) μ (f : S →ₘ[μ] ℂ) = ‖f‖ₑ := by
  rw [Causalean.Mathlib.Analysis.RealInterpolation.wNorm, Lp.enorm_def]
  convert (eLpNorm_nnreal_eq_lintegral (f := fun x => f x) (μ := μ)
      (p := 2) (by norm_num)).symm using 1 <;> norm_num [one_mul, enorm_eq_nnnorm, ENNReal.rpow_two]

/-- A finite weighted gauge with weight at least one gives ambient L² membership. Under [the stated conditions](hyp:w,hw,hf), [the asserted mathematical result follows](goal). -/
-- @node: reflection_memLp_of_wNorm_lt_top
lemma reflection_memLp_of_wNorm_lt_top {S : Type} [MeasurableSpace S]
    (μ : Measure S) (w : S → ℝ≥0∞) (hw : ∀ᵐ x ∂μ, 1 ≤ w x)
    (f : S →ₘ[μ] ℂ)
    (hf : Causalean.Mathlib.Analysis.RealInterpolation.wNorm w μ f < ⊤) : MemLp f 2 μ := by
  refine ⟨f.aestronglyMeasurable, ?_⟩
  have henergy : (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤ := by
    apply lt_of_le_of_lt _ (ENNReal.pow_lt_top hf (n := 2))
    rw [wNorm_sq]
    apply lintegral_mono_ae
    filter_upwards [hw] with x hx
    exact le_mul_of_one_le_left' hx
  have he := eLpNorm_nnreal_eq_lintegral (f := fun x => f x) (μ := μ)
    (p := 2) (by norm_num)
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, enorm_eq_nnnorm, ENNReal.rpow_two] at he
  rw [he]
  simpa only [enorm_eq_nnnorm, NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] using
    ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) henergy.ne

/-- [ The weighted gauge of the zero equivalence class vanishes for any weight.](goal) Under [the stated conditions](hyp:w). -/
-- @node: reflection_wNorm_zero
lemma reflection_wNorm_zero {S : Type} [MeasurableSpace S]
    (μ : Measure S) (w : S → ℝ≥0∞) :
    Causalean.Mathlib.Analysis.RealInterpolation.wNorm w μ (0 : S →ₘ[μ] ℂ) = 0 := by
  rw [Causalean.Mathlib.Analysis.RealInterpolation.wNorm]
  have he : (∫⁻ x, w x * (‖(0 : S →ₘ[μ] ℂ) x‖₊ : ℝ≥0∞) ^ 2 ∂μ) = 0 := by
    calc
      _ = ∫⁻ x, (0 : ℝ≥0∞) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [AEEqFun.coeFn_zero (α := S) (μ := μ) (β := ℂ)] with x hx
        simp [hx]
      _ = 0 := by simp
  rw [he]
  norm_num

/-- [ Restricting weighted quadratic decompositions to ambient L² classes does
not change the K-functional. Finite minimizing costs force both summands into L².](goal) Under [the stated conditions](hyp:w,hw,hwl,ht). -/
-- @node: reflection_kFunctionalSq_Lp_eq
lemma reflection_kFunctionalSq_Lp_eq {S : Type} [MeasurableSpace S]
    (μ : Measure S) (w : S → ℝ≥0∞) (hw : Measurable w)
    (hwl : ∀ᵐ x ∂μ, 1 ≤ w x ∧ w x < ⊤)
    (t : ℝ) (ht : 0 < t) (f : Lp ℂ 2 μ) :
    kFunctionalSq (fun g : Lp ℂ 2 μ => ‖g‖ₑ)
      (fun g => Causalean.Mathlib.Analysis.RealInterpolation.wNorm w μ
        (g : S →ₘ[μ] ℂ)) t f =
    kFunctionalSq (Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun _ => 1) μ) (Causalean.Mathlib.Analysis.RealInterpolation.wNorm w μ) t
      (f : S →ₘ[μ] ℂ) := by
  have hweights : ∀ᵐ x ∂μ, 0 < (1 : ℝ≥0∞) ∧ (1 : ℝ≥0∞) < ⊤ ∧
      0 < w x ∧ w x < ⊤ := by
    filter_upwards [hwl] with x hx
    exact ⟨by norm_num, by norm_num, lt_of_lt_of_le (by norm_num) hx.1, hx.2⟩
  apply le_antisymm
  · obtain ⟨g0, g1, hsum, hcost⟩ := exists_harmonic_minimizer μ
      (fun _ => 1) w measurable_const hw hweights t ht (f : S →ₘ[μ] ℂ)
    have hbound := harmonic_energy_le_cost μ (fun _ => 1) w
      measurable_const hw hweights t ht (f : S →ₘ[μ] ℂ)
      (f : S →ₘ[μ] ℂ) 0 (by simp)
    have hzero := reflection_wNorm_zero μ w
    rw [hcost.symm, reflection_wNorm_one_eq_enorm, hzero, zero_pow (by decide),
      mul_zero, add_zero] at hbound
    have hfinite :
        Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun _ => 1) μ g0 ^ 2 +
        ENNReal.ofReal (t ^ 2) * Causalean.Mathlib.Analysis.RealInterpolation.wNorm w μ g1 ^ 2 < ⊤ :=
      lt_of_le_of_lt hbound (ENNReal.pow_lt_top
        (by rw [Lp.enorm_def]; exact (Lp.memLp f).2) (n := 2))
    have h0 : Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun _ => 1) μ g0 < ⊤ := by
      have h := lt_of_le_of_lt le_self_add hfinite
      simpa using h
    have h1 : Causalean.Mathlib.Analysis.RealInterpolation.wNorm w μ g1 < ⊤ := by
      have h := lt_of_le_of_lt le_add_self hfinite
      have ht0 : ENNReal.ofReal (t ^ 2) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos ht))
      rcases ENNReal.mul_lt_top_iff.mp h with h | h | h
      · simpa using h.2
      · exact (ht0 h).elim
      · have hz : Causalean.Mathlib.Analysis.RealInterpolation.wNorm w μ g1 = 0 := by
          simpa using h
        rw [hz]
        exact ENNReal.zero_lt_top
    let G0 : Lp ℂ 2 μ := ⟨g0, (reflection_memLp_of_wNorm_lt_top μ
      (fun _ => 1) (by simp) g0 h0).2⟩
    let G1 : Lp ℂ 2 μ := ⟨g1, (reflection_memLp_of_wNorm_lt_top μ
      w (hwl.mono fun _ hx => hx.1) g1 h1).2⟩
    have hsumLp : f = G0 + G1 := Subtype.ext hsum
    rw [kFunctionalSq_wNorm μ (fun _ => 1) w measurable_const hw hweights t ht]
    unfold kFunctionalSq
    refine (iInf_le_of_le G0 (iInf_le_of_le G1
      (iInf_le_of_le hsumLp le_rfl))).trans ?_
    dsimp only
    rw [← reflection_wNorm_one_eq_enorm μ G0]
    exact hcost.le
  · unfold kFunctionalSq
    refine le_iInf fun g0 => le_iInf fun g1 => le_iInf fun hsum => ?_
    have he : (f : S →ₘ[μ] ℂ) = (g0 : S →ₘ[μ] ℂ) + (g1 : S →ₘ[μ] ℂ) :=
      congrArg Subtype.val hsum
    refine (iInf_le_of_le (g0 : S →ₘ[μ] ℂ)
      (iInf_le_of_le (g1 : S →ₘ[μ] ℂ) (iInf_le_of_le he le_rfl))).trans ?_
    rw [reflection_wNorm_one_eq_enorm]

/-- [ The normalized K norm on L² classes is exactly the fractional weighted
energy, with no enlargement of the ambient space and no loss of constant.](goal) Under [the stated conditions](hyp:w,hw,hwl,hs). -/
-- @node: reflection_kNormSq_Lp_eq
lemma reflection_kNormSq_Lp_eq {S : Type} [MeasurableSpace S]
    (μ : Measure S) (w : S → ℝ≥0∞) (hw : Measurable w)
    (hwl : ∀ᵐ x ∂μ, 1 ≤ w x ∧ w x < ⊤)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (f : Lp ℂ 2 μ) :
    Causalean.Mathlib.Analysis.RealInterpolation.kNormSq
      (fun g : Lp ℂ 2 μ => ‖g‖ₑ)
      (fun g => Causalean.Mathlib.Analysis.RealInterpolation.wNorm w μ
        (g : S →ₘ[μ] ℂ)) s f =
      ∫⁻ x, ENNReal.rpow (w x) s * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have hweights : ∀ᵐ x ∂μ, 0 < (1 : ℝ≥0∞) ∧ (1 : ℝ≥0∞) < ⊤ ∧
      0 < w x ∧ w x < ⊤ := by
    filter_upwards [hwl] with x hx
    exact ⟨by norm_num, by norm_num, lt_of_lt_of_le (by norm_num) hx.1, hx.2⟩
  have hf : ∃ f0 f1 : S →ₘ[μ] ℂ, (f : S →ₘ[μ] ℂ) = f0 + f1 ∧
      Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun _ => 1) μ f0 < ⊤ ∧
      Causalean.Mathlib.Analysis.RealInterpolation.wNorm w μ f1 < ⊤ := by
    refine ⟨f, 0, by simp, ?_, ?_⟩
    · rw [reflection_wNorm_one_eq_enorm, Lp.enorm_def]
      exact (Lp.memLp f).2
    · rw [reflection_wNorm_zero]
      exact ENNReal.zero_lt_top
  calc
    _ = Causalean.Mathlib.Analysis.RealInterpolation.kNormSq
        (Causalean.Mathlib.Analysis.RealInterpolation.wNorm (fun _ => 1) μ)
        (Causalean.Mathlib.Analysis.RealInterpolation.wNorm w μ) s
        (f : S →ₘ[μ] ℂ) := by
      unfold Causalean.Mathlib.Analysis.RealInterpolation.kNormSq
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [reflection_kFunctionalSq_Lp_eq μ w hw hwl t ht f]
    _ = _ := by
      simpa only [ENNReal.rpow_eq_pow, ENNReal.one_rpow, one_mul] using
        weighted_l2_interpolation μ (fun _ => 1) w measurable_const hw
          hweights s hs (f : S →ₘ[μ] ℂ) hf

/-- The frequency first-order gauge agrees with its weighted L² realization. [The asserted mathematical result follows](goal). -/
-- @node: reflectionProfileFirstOrderNorm_eq_wNorm
lemma reflectionProfileFirstOrderNorm_eq_wNorm (p : ℕ)
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    reflectionProfileFirstOrderNorm p ψ =
      Causalean.Mathlib.Analysis.RealInterpolation.wNorm
        (fun ω : EuclideanSpace ℝ (Fin p) => ENNReal.ofReal (1 + ‖ω‖ ^ 2 / (p : ℝ)))
        volume (ψ : EuclideanSpace ℝ (Fin p) →ₘ[volume] ℂ) := by
  unfold reflectionProfileFirstOrderNorm Causalean.Mathlib.Analysis.RealInterpolation.wNorm
  congr 1
  apply lintegral_congr
  intro ω
  rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, enorm_eq_nnnorm, mul_comm]

/-- Source interpolation is precisely the paper's fractional angular Fourier
energy, including its local dimension normalization. Under [the stated conditions](hyp:hs), [the asserted mathematical result follows](goal). -/
-- @node: reflectionProfile_kNormSq_eq_energy
lemma reflectionProfile_kNormSq_eq_energy (p : ℕ)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1)
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    Causalean.Mathlib.Analysis.RealInterpolation.kNormSq
      (fun f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))) => ‖f‖ₑ)
      (reflectionProfileFirstOrderNorm p) s ψ =
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s) := by
  have hw : Measurable (fun ω : EuclideanSpace ℝ (Fin p) =>
      ENNReal.ofReal (1 + ‖ω‖ ^ 2 / (p : ℝ))) := by fun_prop
  have hwl : ∀ᵐ ω ∂(volume : Measure (EuclideanSpace ℝ (Fin p))),
      1 ≤ ENNReal.ofReal (1 + ‖ω‖ ^ 2 / (p : ℝ)) ∧
      ENNReal.ofReal (1 + ‖ω‖ ^ 2 / (p : ℝ)) < ⊤ := by
    filter_upwards [] with ω
    constructor
    · exact ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))
    · exact ENNReal.ofReal_lt_top
  have hn : reflectionProfileFirstOrderNorm p =
      (fun f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))) =>
        Causalean.Mathlib.Analysis.RealInterpolation.wNorm
        (fun ω : EuclideanSpace ℝ (Fin p) => ENNReal.ofReal (1 + ‖ω‖ ^ 2 / (p : ℝ)))
        volume (f : EuclideanSpace ℝ (Fin p) →ₘ[volume] ℂ)) :=
    funext (reflectionProfileFirstOrderNorm_eq_wNorm p)
  rw [hn]
  rw [reflection_kNormSq_Lp_eq volume _ hw hwl s hs ψ]
  apply lintegral_congr
  intro ω
  rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_nonneg (by positivity) hs.1.le,
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, enorm_eq_nnnorm, mul_comm]

/-- [ The genuine reflection operator's target K energy is bounded by the
exact fractional whole-space energy. Both endpoint contractions and the source
norm identification enter this estimate with constant one.](goal) Under [the stated conditions](hyp:hp,hs). -/
-- @node: reflectionProfileOperator_kNormSq_le_energy
lemma reflectionProfileOperator_kNormSq_le_energy (p : ℕ) (hp : p = 1 ∨ p = 2)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1)
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    Causalean.Mathlib.Analysis.RealInterpolation.kNormSq
      (fun f : Lp ℂ 2 (torusMeasure p) => ‖f‖ₑ)
      (reflectionTorusFirstOrderNorm p) s (reflectionProfileOperator p ψ) ≤
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s) := by
  rw [← reflectionProfile_kNormSq_eq_energy p s hs ψ]
  exact reflectionProfileOperator_kNormSq_le p hp s hs ψ

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
