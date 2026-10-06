module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperFactorial
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Order.Interval.Set.Infinite

/-! # Jackson mean containment in the clipping interval

The estimator's chosen polynomial inherits the tensor convolution oscillation
bound (12). Polynomial uniqueness on the cube recovers its coordinate degrees,
so the finite coefficient expression used by the factorial mean represents that
same convolution, rather than an unrelated approximation polynomial.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open Causalean.Mathlib.Analysis.JacksonApproximation
open Causalean.Mathlib.Analysis.Approximation.Chebyshev
open scoped BigOperators

/-- Nonnegative centers and radii give a nonnegative armwise clipping scale. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hc,hr), the [stated conclusion](goal) holds. -/
lemma clippingScale_nonneg (ε : ℝ) (c r : Fin 4 → ℝ)
    (hc : ∀ j, 0 ≤ c j) (hr : ∀ j, 0 ≤ r j) :
    0 ≤ clippingScaleFormula ε c r := by
  have ht : 0 ≤ totalMassVecFormula c := by
    simp only [totalMassVecFormula, armMassVecFormula]
    exact add_nonneg (add_nonneg (hc _) (hc _)) (add_nonneg (hc _) (hc _))
  have hd (a : Bool) : 0 ≤ anchoredDenomFormula ε c a :=
    (add_nonneg (hc _) (hc _)).trans (le_max_left _ _)
  unfold clippingScaleFormula armWeightFormula armRadiusFormula
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ =>
    mul_nonneg (add_nonneg (by norm_num) (div_nonneg ht (hd a)))
      (add_nonneg (hr _) (hr _)))

/-- The armwise modulus bounds every point in a nonnegative rectangle by its center oscillation scale, retaining the arm weights and radii together. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hc,hc0,hQ,hv), the [stated conclusion](goal) holds. -/
lemma armwiseExtension_rectangle_oscillation_le (ε : ℝ) (hε : 0 < ε)
    (c r : Fin 4 → ℝ) (hc : ∀ j, 0 ≤ c j) (hc0 : c ≠ 0)
    (hQ : ∀ v ∈ centeredRectangle c r, ∀ j, 0 ≤ v j)
    (v : Fin 4 → ℝ) (hv : v ∈ centeredRectangle c r) :
    |armwiseExtensionFormula ε v - armwiseExtensionFormula ε c| ≤ clippingScaleFormula ε c r := by
  have ht : 0 ≤ totalMassVecFormula c := by
    simp only [totalMassVecFormula, armMassVecFormula]
    exact add_nonneg (add_nonneg (hc _) (hc _)) (add_nonneg (hc _) (hc _))
  have hw (a : Bool) : 0 ≤ armWeightFormula ε c a := by
    unfold armWeightFormula
    exact add_nonneg (by norm_num) (div_nonneg ht
      ((add_nonneg (hc _) (hc _)).trans (le_max_left _ _)))
  have hdelta (a : Bool) : armDelta v c a ≤ armRadiusFormula r a := by
    simpa only [armDelta, armRadiusFormula, Fintype.sum_bool, add_comm] using
      add_le_add (hv (cellIdx a false)) (hv (cellIdx a true))
  calc
    _ ≤ 2 * (∑ a : Bool, armDelta v c a) +
        2 * (∑ a : Bool, totalMassVecFormula c / anchoredDenomFormula ε c a * armDelta v c a) :=
      armwise_modulus_extension.1 ε hε v c (hQ v hv) hc hc0
    _ = 2 * ∑ a : Bool, armWeightFormula ε c a * armDelta v c a := by
      simp only [armWeightFormula, Fintype.sum_bool]
      ring
    _ ≤ clippingScaleFormula ε c r := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hdelta a) (hw a)

/-- The actual pair selected in the estimator represents the canonical tensor convolution whenever its construction conditions hold. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hK,hr,hQ), the [stated conclusion](goal) holds. -/
lemma jacksonPolynomialPair_cos_eval (ε : ℝ) (hε : 0 < ε) (K : ℕ) (hK : 0 < K)
    (c r : Fin 4 → ℝ) (hr : ∀ j, 0 < r j)
    (hQ : ∀ v ∈ centeredRectangle c r, ∀ j, 0 ≤ v j) (x : Fin 4 → ℝ) :
    MvPolynomial.eval (cosPoint x) (jacksonPolynomialPair ε K c r).2 =
      tensorConvolution K (fun z => armwiseExtensionFormula ε (affinePoint c r z)) x := by
  unfold jacksonPolynomialPair
  simp only [dif_pos hK, dif_pos hε, dif_pos hr, dif_pos hQ]
  exact (Classical.choose_spec (Classical.choose_spec
    (affineJackson_exists_mvPolynomial_four hK c r hr (armwiseExtensionFormula ε)
      (armwise_continuousOn_rectangle ε hε c r hr hQ)))).2.1 x


-- @node: jacksonPolynomialPair_normalized_degree_le
/-- Polynomial uniqueness on the cube recovers the normalized representative's coordinate degree bound even though the affine existence interface exposes only the physical representative's degrees. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hK,hr,hQ), the [stated conclusion](goal) holds. -/
lemma jacksonPolynomialPair_normalized_degree_le (ε : ℝ) (hε : 0 < ε)
    (K : ℕ) (hK : 0 < K) (c r : Fin 4 → ℝ) (hr : ∀ j, 0 < r j)
    (hQ : ∀ v ∈ centeredRectangle c r, ∀ j, 0 ≤ v j) (j : Fin 4) :
    (jacksonPolynomialPair ε K c r).2.degreeOf j ≤ 2 * (K - 1) := by
  have haff : Continuous (affinePoint c r) := by
    unfold affinePoint
    fun_prop
  have hf : ContinuousOn (fun z => armwiseExtensionFormula ε (affinePoint c r z))
      (normalizedCube 4) :=
    (armwise_continuousOn_rectangle ε hε c r hr hQ).comp haff.continuousOn
      (fun z hz => affinePoint_mem_centeredRectangle c r z hr hz)
  obtain ⟨p, hp, hdeg, _⟩ := tensorConvolution_exists_mvPolynomial hK _ hf
  have heq : (jacksonPolynomialPair ε K c r).2 = p := by
    apply MvPolynomial.funext_set (fun _ => Set.Icc (-1 : ℝ) 1)
      (fun _ => Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1))
    intro z hz
    let x : Fin 4 → ℝ := fun i => Real.arccos (z i)
    have hcos : cosPoint x = z := by
      funext i
      exact Real.cos_arccos (hz i (Set.mem_univ i)).1 (hz i (Set.mem_univ i)).2
    rw [← hcos, jacksonPolynomialPair_cos_eval ε hε K hK c r hr hQ, hp]
  rw [heq]
  exact MvPolynomial.degreeOf_le_iff.mpr (fun m hm => hdeg m hm j)

/-- The finite centered coefficient sum used in the Poisson mean is exactly the normalized Jackson polynomial evaluation, without a truncation remainder. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hK,hr,hQ), the [stated conclusion](goal) holds. -/
lemma jacksonCoeff_sum_eq_eval (ε : ℝ) (hε : 0 < ε) (K : ℕ) (hK : 0 < K)
    (c r : Fin 4 → ℝ) (hr : ∀ j, 0 < r j)
    (hQ : ∀ v ∈ centeredRectangle c r, ∀ j, 0 ≤ v j) (z : Fin 4 → ℝ) :
    armwiseExtensionFormula ε c + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoeff ε K c r α * ∏ j, z j ^ (α j).val =
      MvPolynomial.eval z (jacksonPolynomialPair ε K c r).2 := by
  let p := (jacksonPolynomialPair ε K c r).2 - MvPolynomial.C (armwiseExtensionFormula ε c)
  have hdeg (j : Fin 4) : p.degreeOf j ≤ 2 * (K - 1) := by
    exact (MvPolynomial.degreeOf_sub_le j _ _).trans (max_le
      (jacksonPolynomialPair_normalized_degree_le ε hε K hK c r hr hQ j) (by simp))
  have he := congrArg (MvPolynomial.eval z) (tensorPolynomial_tensorCoeffs p hdeg)
  simp only [tensorPolynomial, map_sum, MvPolynomial.eval_monomial,
    tensorExponent] at he
  simp_rw [Finsupp.prod_fintype _ (fun i e => z i ^ e) (fun i => pow_zero (z i))] at he
  simp only [Finsupp.equivFunOnFinite_symm_apply_apply] at he
  change (∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
    jacksonCoeff ε K c r α * ∏ j, z j ^ (α j).val) = MvPolynomial.eval z p at he
  rw [he]
  simp only [p, map_sub, MvPolynomial.eval_C]
  ring


-- @node: tensorConvolution_abs_sub_le
/-- A normalized positive Jackson kernel preserves a uniform oscillation bound around any fixed center. Continuity supplies the integral's regularity. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hK,hf,hbound), the [stated conclusion](goal) holds. -/
lemma tensorConvolution_abs_sub_le {d K : ℕ} (hK : 0 < K)
    (f : (Fin d → ℝ) → ℝ) (hf : ContinuousOn f (normalizedCube d))
    (c B : ℝ) (hbound : ∀ z ∈ normalizedCube d, |f z - c| ≤ B)
    (x : Fin d → ℝ) : |tensorConvolution K f x - c| ≤ B := by
  have hc : Continuous (fun u : Fin d → ℝ => f (cosPoint (x - u))) := by
    apply hf.comp_continuous
    · unfold cosPoint
      fun_prop
    · exact fun u => cosPoint_mem_normalizedCube _
  have hk : Continuous (tensorJackson K d) := by
    unfold tensorJackson
    fun_prop
  have hcompact : IsCompact (periodBox d) :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  have hfi : IntegrableOn (fun u => f (cosPoint (x - u)) * tensorJackson K d u)
      (periodBox d) := (hc.mul hk).continuousOn.integrableOn_compact hcompact
  have hci : IntegrableOn (fun u => c * tensorJackson K d u) (periodBox d) :=
    (integrableOn_tensorJackson K d).const_mul c
  have hdi : IntegrableOn (fun u => (f (cosPoint (x - u)) - c) * tensorJackson K d u)
      (periodBox d) := ((hc.sub continuous_const).mul hk).continuousOn.integrableOn_compact hcompact
  have hid : tensorConvolution K f x - c =
      ∫ u in periodBox d, (f (cosPoint (x - u)) - c) * tensorJackson K d u := by
    calc
      _ = (∫ u in periodBox d, f (cosPoint (x - u)) * tensorJackson K d u) -
          ∫ u in periodBox d, c * tensorJackson K d u := by
        rw [integral_const_mul, tensorJackson_integral_eq_one hK, mul_one]
        rfl
      _ = _ := by
        rw [← integral_sub hfi hci]
        apply integral_congr_ae
        exact ae_of_all _ fun u => by ring
  rw [hid]
  calc
    _ ≤ ∫ u in periodBox d, |(f (cosPoint (x - u)) - c) * tensorJackson K d u| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ u in periodBox d, B * tensorJackson K d u := by
      apply setIntegral_mono hdi.abs ((integrableOn_tensorJackson K d).const_mul B)
      intro u
      change |(f (cosPoint (x - u)) - c) * tensorJackson K d u| ≤ B * tensorJackson K d u
      rw [abs_mul, abs_of_nonneg (tensorJackson_nonneg hK u)]
      exact mul_le_mul_of_nonneg_right
        (hbound _ (cosPoint_mem_normalizedCube _)) (tensorJackson_nonneg hK u)
    _ = B := by rw [integral_const_mul, tensorJackson_integral_eq_one hK, mul_one]

/-- Equation (12) holds for the exact finite coefficient expression appearing as the Poisson factorial mean. The oscillation scale is derived from the modulus and the positive normalized kernel rather than assumed as a containment premise. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hK,hr,hQ,hq), the [stated conclusion](goal) holds. -/
lemma jacksonCoeff_mean_oscillation_le (ε : ℝ) (hε : 0 < ε)
    (K : ℕ) (hK : 0 < K) (c r : Fin 4 → ℝ) (hr : ∀ j, 0 < r j)
    (hQ : ∀ v ∈ centeredRectangle c r, ∀ j, 0 ≤ v j)
    (q : Fin 4 → ℝ) (hq : q ∈ centeredRectangle c r) :
    |(armwiseExtensionFormula ε c + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoeff ε K c r α * ∏ j, ((q j - c j) / r j) ^ (α j).val) -
      armwiseExtensionFormula ε c| ≤ clippingScaleFormula ε c r := by
  have hlo (j : Fin 4) : 0 < c j := by
    have h := hQ (affinePoint c r (fun _ => -1))
      (affinePoint_mem_centeredRectangle c r _ hr (by intro i; constructor <;> norm_num)) j
    change 0 ≤ c j + r j * (-1) at h
    linarith [hr j]
  have hc : ∀ j, 0 ≤ c j := fun j => (hlo j).le
  have hc0 : c ≠ 0 := by
    intro h
    have hpos := hlo 0
    simp only [h, Pi.zero_apply] at hpos
    exact (lt_irrefl 0) hpos
  have haff : Continuous (affinePoint c r) := by unfold affinePoint; fun_prop
  have hf : ContinuousOn (fun z => armwiseExtensionFormula ε (affinePoint c r z))
      (normalizedCube 4) :=
    (armwise_continuousOn_rectangle ε hε c r hr hQ).comp haff.continuousOn
      (fun z hz => affinePoint_mem_centeredRectangle c r z hr hz)
  have hn := normalizedPoint_mem_normalizedCube c r q hr hq
  let x : Fin 4 → ℝ := fun j => Real.arccos (normalizedPoint c r q j)
  have hcos : cosPoint x = normalizedPoint c r q := by
    funext j
    exact Real.cos_arccos (hn j).1 (hn j).2
  rw [jacksonCoeff_sum_eq_eval ε hε K hK c r hr hQ]
  change |MvPolynomial.eval (normalizedPoint c r q) (jacksonPolynomialPair ε K c r).2 - _| ≤ _
  rw [← hcos, jacksonPolynomialPair_cos_eval ε hε K hK c r hr hQ]
  apply tensorConvolution_abs_sub_le hK _ hf
  intro z hz
  exact armwiseExtension_rectangle_oscillation_le ε hε c r hc hc0 hQ _
    (affinePoint_mem_centeredRectangle c r z hr hz)

/-- The pilot's centered rectangle is nonnegative by the truncated lower endpoint, with no extra regularity or positivity premise on the counts. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hv), the [stated conclusion](goal) holds. -/
lemma pilotCenteredRectangle_nonneg (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (Np : Fin 4 → ℕ) (v : Fin 4 → ℝ)
    (hv : v ∈ centeredRectangle (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np))
    (j : Fin 4) : 0 ≤ v j := by
  have hl := (abs_le.mp (hv j)).1
  have hn := le_max_left 0 (pilotCenterFormula m Np j - pilotHalfWidthFormula H hH m L Np j)
  dsimp [pilotMidpoint, pilotRadiusFormula, pilotLower, pilotUpperFormula] at hl
  linarith

/-- On the actual pilot rectangle, the exact factorial mean belongs to the clipping interval for every positive alphabet size, including null cells. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL,hε,hK,hd,hq), the [stated conclusion](goal) holds. -/
lemma pilotJackson_mean_mem_clipping_interval (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ)
    (ε : ℝ) (hε : 0 < ε) (K d : ℕ) (hK : 0 < K) (hd : 1 ≤ d)
    (q : Fin 4 → ℝ)
    (hq : q ∈ pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np)) :
    let b := pilotMidpoint H hH m L Np
    let r := pilotRadiusFormula H hH m L Np
    0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε b r ∧
    |(armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoeff ε K b r α * ∏ j, ((q j - b j) / r j) ^ (α j).val) -
      armwiseExtensionFormula ε b| ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε b r := by
  dsimp only
  have hr := pilotRadius_pos H hH m L hm hL Np
  have hQ := pilotCenteredRectangle_nonneg H hH m L Np
  have hs := clippingScale_nonneg ε _ _ (pilotMidpoint_nonneg H hH m L hm Np)
    (fun j => (hr j).le)
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : 1 ≤ (d : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hdreal (by norm_num)
  constructor
  · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hs
  · exact (jacksonCoeff_mean_oscillation_le ε hε K hK _ _ hr hQ q
      (pilotRectangle_center_bound H hH m L Np q hq)).trans
      (le_mul_of_one_le_left hs hpow)

/-- Localization alone suffices for the clipping second-moment transfer in (28): the mean containment and nonnegative width are supplied by the Jackson construction. The coefficient norm remains explicit for the later bound (14). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hqnonneg,hH,hHlarge,hm,hL,hWlaw,hind,hq,hε,hK,hd), the [stated conclusion](goal) holds. -/
lemma pilotClippedCellValue_square_envelope_of_localized {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (q : Fin 4 → ℝ) (hqnonneg : ∀ j, 0 ≤ q j)
    (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ)
    (hWlaw : ∀ j, ProbabilityTheory.HasLaw (W j)
      (ProbabilityTheory.poissonMeasure ⟨m * q j, mul_nonneg hm.le (hqnonneg j)⟩) μ)
    (hind : ProbabilityTheory.iIndepFun W μ)
    (hq : q ∈ pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np))
    (ε : ℝ) (hε : 0 < ε) (K d : ℕ) (hK : 0 < K) (hd : 1 ≤ d) :
    let b := pilotMidpoint H hH m L Np
    let r := pilotRadiusFormula H hH m L Np
    let p := armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoeff ε K b r α * ∏ j, ((q j - b j) / r j) ^ (α j).val
    (∫ ω, (clippedCellValueFormula ε K d m b r (fun j => W j ω) - p) ^ 2 ∂μ) ≤
      (∑ α : Fin 4 → Fin (2 * (K - 1) + 1), |jacksonCoeff ε K b r α|) ^ 2 *
        Real.exp (32 * (2 * (K - 1) : ℕ) ^ 2 / L) := by
  obtain ⟨hwidth, hmean⟩ := pilotJackson_mean_mem_clipping_interval
    H hH m L hm hL Np ε hε K d hK hd q hq
  exact pilotClippedCellValue_square_envelope μ W q hqnonneg H hH hHlarge m L
    hm hL Np hWlaw hind hq ε K d hwidth hmean

end CausalSmith.Stat.OptvalueVanishingoverlapRate
