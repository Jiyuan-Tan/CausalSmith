module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperJacksonOscillation
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperLocalizedBias
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.AffineFourBoundary

/-! # Occupied-cell Jackson bias

A reference-point modulus is integrated against the positive tensor kernel.
The weights remain attached to the true arm masses, as in roadmap (11),
and the localized pilot envelope then yields (20).
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open Causalean.Mathlib.Analysis.JacksonApproximation
open Causalean.Mathlib.Analysis.Approximation.Chebyshev
open Causalean.Mathlib.Analysis.Approximation.Chebyshev.AffineFourBoundary
open scoped BigOperators


-- @node: tensorConvolution_reference_boundary_le
/-- Only a modulus anchored at the evaluation point is needed for the boundary Jackson estimate; no uniform Lipschitz bound over pairs of points is imposed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hK,hg,hr,hL,hlip), the [stated conclusion](goal) holds. -/
lemma tensorConvolution_reference_boundary_le {d K : ℕ} (hK : 0 < K)
    (g : (Fin d → ℝ) → ℝ) (hg : ContinuousOn g (normalizedCube d))
    (r : Fin d → ℝ) (hr : ∀ i, 0 ≤ r i)
    (L : ℝ) (hL : 0 ≤ L)
    (theta : Fin d → ℝ)
    (hlip : ∀ x ∈ normalizedCube d,
      |g x - g (cosPoint theta)| ≤ L * ∑ i, r i * |x i - cosPoint theta i|) :
    |tensorConvolution K g theta - g (cosPoint theta)| ≤
      L * ∑ i : Fin d,
        (32 * r i * |Real.sin (theta i)| / (K : ℝ) +
          32 * r i / (K : ℝ) ^ 2) := by
  classical
  have hcompact : IsCompact (periodBox d) := by
    rw [show periodBox d = {u | ∀ i, u i ∈ Set.Icc (-Real.pi) Real.pi} by rfl]
    exact isCompact_pi_infinite fun _ ↦ isCompact_Icc
  have hcos : Continuous (fun u : Fin d → ℝ ↦ cosPoint (theta - u)) := by
    apply continuous_pi
    intro i
    change Continuous (fun u : Fin d → ℝ ↦ Real.cos (theta i - u i))
    fun_prop
  have hgcos : Continuous (fun u : Fin d → ℝ ↦ g (cosPoint (theta - u))) := by
    simpa [Function.comp_def] using
      hg.comp_continuous hcos (fun u ↦ cosPoint_mem_normalizedCube (theta - u))
  have hkernel : Continuous (tensorJackson K d) := by
    unfold tensorJackson
    fun_prop
  have hconvInt : IntegrableOn
      (fun u : Fin d → ℝ ↦ g (cosPoint (theta - u)) * tensorJackson K d u)
      (periodBox d) :=
    (hgcos.mul hkernel).continuousOn.integrableOn_compact hcompact
  have hconstInt : IntegrableOn
      (fun u : Fin d → ℝ ↦ g (cosPoint theta) * tensorJackson K d u)
      (periodBox d) :=
    (continuous_const.mul hkernel).continuousOn.integrableOn_compact hcompact
  have hdiffInt : IntegrableOn
      (fun u : Fin d → ℝ ↦
        (g (cosPoint (theta - u)) - g (cosPoint theta)) * tensorJackson K d u)
      (periodBox d) :=
    ((hgcos.sub continuous_const).mul hkernel).continuousOn.integrableOn_compact hcompact
  have hfirstInt (i : Fin d) : IntegrableOn
      (fun u : Fin d → ℝ ↦ |u i| * tensorJackson K d u) (periodBox d) := by
    exact ((continuous_abs.comp (continuous_apply i)).mul hkernel).continuousOn
      |>.integrableOn_compact hcompact
  have hsecondInt (i : Fin d) : IntegrableOn
      (fun u : Fin d → ℝ ↦ (u i) ^ 2 * tensorJackson K d u) (periodBox d) := by
    exact (((continuous_apply i).pow 2).mul hkernel).continuousOn
      |>.integrableOn_compact hcompact
  have htermInt (i : Fin d) : IntegrableOn
      (fun u : Fin d → ℝ ↦
        (r i * |Real.sin (theta i)| * |u i| + r i / 2 * (u i) ^ 2) *
          tensorJackson K d u) (periodBox d) := by
    have hc : Continuous (fun u : Fin d → ℝ ↦
        (r i * |Real.sin (theta i)| * |u i| + r i / 2 * (u i) ^ 2) *
          tensorJackson K d u) := by fun_prop
    exact hc.continuousOn.integrableOn_compact hcompact
  have hboundInt : IntegrableOn
      (fun u : Fin d → ℝ ↦
        L * ∑ i, (r i * |Real.sin (theta i)| * |u i| +
          r i / 2 * (u i) ^ 2) * tensorJackson K d u) (periodBox d) := by
    have hc : Continuous (fun u : Fin d → ℝ ↦
        L * ∑ i, (r i * |Real.sin (theta i)| * |u i| +
          r i / 2 * (u i) ^ 2) * tensorJackson K d u) := by
      fun_prop
    exact hc.continuousOn.integrableOn_compact hcompact
  have hdiff : tensorConvolution K g theta - g (cosPoint theta) =
      ∫ u in periodBox d,
        (g (cosPoint (theta - u)) - g (cosPoint theta)) * tensorJackson K d u := by
    unfold tensorConvolution
    calc
      (∫ u in periodBox d, g (cosPoint (theta - u)) * tensorJackson K d u) -
          g (cosPoint theta) =
          (∫ u in periodBox d, g (cosPoint (theta - u)) * tensorJackson K d u) -
            g (cosPoint theta) * (∫ u in periodBox d, tensorJackson K d u) := by
              rw [tensorJackson_integral_eq_one hK, mul_one]
      _ = (∫ u in periodBox d, g (cosPoint (theta - u)) * tensorJackson K d u) -
            ∫ u in periodBox d, g (cosPoint theta) * tensorJackson K d u := by
              rw [integral_const_mul]
      _ = ∫ u in periodBox d,
          (g (cosPoint (theta - u)) * tensorJackson K d u -
            g (cosPoint theta) * tensorJackson K d u) :=
              (integral_sub hconvInt hconstInt).symm
      _ = ∫ u in periodBox d,
          (g (cosPoint (theta - u)) - g (cosPoint theta)) * tensorJackson K d u := by
            apply integral_congr_ae
            filter_upwards
            intro u
            ring
  rw [hdiff]
  calc
    |∫ u in periodBox d,
        (g (cosPoint (theta - u)) - g (cosPoint theta)) * tensorJackson K d u| ≤
        ∫ u in periodBox d,
          |(g (cosPoint (theta - u)) - g (cosPoint theta)) * tensorJackson K d u| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ u in periodBox d,
        L * ∑ i, (r i * |Real.sin (theta i)| * |u i| +
          r i / 2 * (u i) ^ 2) * tensorJackson K d u := by
      apply setIntegral_mono hdiffInt.abs hboundInt
      intro u
      change |(g (cosPoint (theta - u)) - g (cosPoint theta)) * tensorJackson K d u| ≤
        L * ∑ i, (r i * |Real.sin (theta i)| * |u i| +
          r i / 2 * (u i) ^ 2) * tensorJackson K d u
      rw [abs_mul, abs_of_nonneg (tensorJackson_nonneg hK u)]
      calc
        |g (cosPoint (theta - u)) - g (cosPoint theta)| * tensorJackson K d u ≤
            (L * ∑ i, r i * |(cosPoint (theta - u)) i - (cosPoint theta) i|) *
              tensorJackson K d u := by
          exact mul_le_mul_of_nonneg_right
            (hlip _ (cosPoint_mem_normalizedCube _)) (tensorJackson_nonneg hK u)
        _ ≤ (L * ∑ i, (r i * |Real.sin (theta i)| * |u i| +
            r i / 2 * (u i) ^ 2)) * tensorJackson K d u := by
          apply mul_le_mul_of_nonneg_right _ (tensorJackson_nonneg hK u)
          apply mul_le_mul_of_nonneg_left _ hL
          apply Finset.sum_le_sum
          intro i _
          have hi := abs_cos_add_sub_cos_le (theta i) (-u i)
          simp only [cosPoint, Pi.sub_apply, abs_neg, neg_sq] at hi ⊢
          convert mul_le_mul_of_nonneg_left hi (hr i) using 1 <;> ring_nf
        _ = L * ∑ i, (r i * |Real.sin (theta i)| * |u i| +
            r i / 2 * (u i) ^ 2) * tensorJackson K d u := by
          rw [mul_assoc, Finset.sum_mul]
    _ = L * ∑ i : Fin d,
        (r i * |Real.sin (theta i)| *
          (∫ u in periodBox d, |u i| * tensorJackson K d u) +
        r i / 2 * (∫ u in periodBox d, (u i) ^ 2 * tensorJackson K d u)) := by
      rw [integral_const_mul]
      rw [integral_finsetSum Finset.univ (fun i _ ↦ htermInt i)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have heq (u : Fin d → ℝ) :
          (r i * |Real.sin (theta i)| * |u i| + r i / 2 * (u i) ^ 2) *
              tensorJackson K d u =
            r i * |Real.sin (theta i)| * (|u i| * tensorJackson K d u) +
              r i / 2 * ((u i) ^ 2 * tensorJackson K d u) := by ring
      simp_rw [heq]
      rw [integral_add, integral_const_mul, integral_const_mul]
      · exact (hfirstInt i).const_mul _
      · exact (hsecondInt i).const_mul _
    _ ≤ L * ∑ i : Fin d,
        (32 * r i * |Real.sin (theta i)| / (K : ℝ) +
          32 * r i / (K : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hL
      apply Finset.sum_le_sum
      intro i _
      have hfirst := (tensorJackson_first_moment_eq hK i).le.trans
        (jackson_first_moment K hK)
      have hsecond := (tensorJackson_second_moment_eq hK i).le.trans
        (jackson_second_moment K hK)
      have hcoef1 : 0 ≤ r i * |Real.sin (theta i)| :=
        mul_nonneg (hr i) (abs_nonneg _)
      have hcoef2 : 0 ≤ r i / 2 := div_nonneg (hr i) (by norm_num)
      have h1 := mul_le_mul_of_nonneg_left hfirst hcoef1
      have h2 := mul_le_mul_of_nonneg_left hsecond hcoef2
      calc
        _ ≤ r i * |Real.sin (theta i)| * (32 / (K : ℝ)) +
            r i / 2 * (64 / (K : ℝ) ^ 2) := add_le_add h1 h2
        _ = _ := by ring

/-- The estimator's finite coefficient mean inherits the boundary estimate from a physical-coordinate modulus at its true reference vector. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hK,hr,hw,hQ,hq,hmod), the [stated conclusion](goal) holds. -/
lemma jacksonCoeff_reference_boundary_le (ε : ℝ) (hε : 0 < ε)
    (K : ℕ) (hK : 0 < K) (c r q w : Fin 4 → ℝ)
    (hr : ∀ j, 0 < r j) (hw : ∀ j, 0 ≤ w j)
    (hQ : ∀ v ∈ centeredRectangle c r, ∀ j, 0 ≤ v j)
    (hq : q ∈ centeredRectangle c r)
    (hmod : ∀ v ∈ centeredRectangle c r,
      |armwiseExtensionFormula ε v - armwiseExtensionFormula ε q| ≤ ∑ j, w j * |v j - q j|) :
    |(armwiseExtensionFormula ε c + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoeff ε K c r α * ∏ j, ((q j - c j) / r j) ^ (α j).val) -
      armwiseExtensionFormula ε q| ≤
      32 * ∑ j : Fin 4, w j *
        (Real.sqrt ((q j - (c j - r j)) * ((c j + r j) - q j)) / (K : ℝ) +
          r j / (K : ℝ) ^ 2) := by
  have haff : Continuous (affinePoint c r) := by unfold affinePoint; fun_prop
  have hf : ContinuousOn (fun z => armwiseExtensionFormula ε (affinePoint c r z))
      (normalizedCube 4) :=
    (armwise_continuousOn_rectangle ε hε c r hr hQ).comp haff.continuousOn
      (fun z hz => affinePoint_mem_centeredRectangle c r z hr hz)
  have hn := normalizedPoint_mem_normalizedCube c r q hr hq
  let θ : Fin 4 → ℝ := fun j => Real.arccos (normalizedPoint c r q j)
  have hcos : cosPoint θ = normalizedPoint c r q := by
    funext j
    exact Real.cos_arccos (hn j).1 (hn j).2
  have hpoint : affinePoint c r (cosPoint θ) = q := by
    rw [hcos, affinePoint_normalizedPoint c r q hr]
  have hbound := tensorConvolution_reference_boundary_le hK _ hf
    (fun j => w j * r j) (fun j => mul_nonneg (hw j) (hr j).le)
    1 (by norm_num) θ (by
      intro z hz
      have h := hmod _ (affinePoint_mem_centeredRectangle c r z hr hz)
      rw [← hpoint] at h
      simpa only [affinePoint, abs_mul, abs_of_pos (hr _), one_mul,
        show ∀ j, c j + r j * z j - (c j + r j * cosPoint θ j) =
          r j * (z j - cosPoint θ j) by intro j; ring, mul_assoc] using h)
  rw [jacksonCoeff_sum_eq_eval ε hε K hK c r hr hQ]
  change |MvPolynomial.eval (normalizedPoint c r q) (jacksonPolynomialPair ε K c r).2 - _| ≤ _
  rw [← hcos, jacksonPolynomialPair_cos_eval ε hε K hK c r hr hQ]
  rw [hpoint, one_mul] at hbound
  apply hbound.trans_eq
  have hterm (j : Fin 4) :
      32 * (w j * r j) * |Real.sin (θ j)| / (K : ℝ) +
        32 * (w j * r j) / (K : ℝ) ^ 2 =
      32 * (w j * (Real.sqrt ((q j - (c j - r j)) * ((c j + r j) - q j)) /
        (K : ℝ) + r j / (K : ℝ) ^ 2)) := by
    have hs := radius_mul_abs_sin_arccos_eq_boundary c r q hr j
    change r j * |Real.sin (θ j)| = _ at hs
    calc
      _ = 32 * w j * (r j * |Real.sin (θ j)|) / (K : ℝ) +
          32 * (w j * r j) / (K : ℝ) ^ 2 := by ring
      _ = _ := by rw [hs]; ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]

/-- Integrating the armwise modulus at an occupied cell proves equation (11) for the exact coefficient expression, including boundary means and ties. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp,hK,hr,hQ,hq), the [stated conclusion](goal) holds. -/
lemma observed_jacksonCoeff_biasEnvelope_le {d : ℕ} (ε : ℝ) (P : DiscreteLaw d)
    (hε : 0 < ε) (hP : ObservedClass ε P) (x : Fin d) (hp : 0 < cellMass P x)
    (K : ℕ) (hK : 0 < K) (c r : Fin 4 → ℝ) (hr : ∀ j, 0 < r j)
    (hQ : ∀ v ∈ centeredRectangle c r, ∀ j, 0 ≤ v j)
    (hq : cellVector P x ∈ centeredRectangle c r) :
    |(armwiseExtensionFormula ε c + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoeff ε K c r α * ∏ j, ((cellVector P x j - c j) / r j) ^ (α j).val) -
      armwiseExtensionFormula ε (cellVector P x)| ≤
      64 * ∑ a : Bool, (1 + cellMass P x / armMass P a x) *
        ((∑ y : Bool, Real.sqrt
          ((cellVector P x (cellIdx a y) - (c (cellIdx a y) - r (cellIdx a y))) *
           ((c (cellIdx a y) + r (cellIdx a y)) - cellVector P x (cellIdx a y)))) /
            (K : ℝ) + armRadiusFormula r a / (K : ℝ) ^ 2) := by
  let w : Fin 4 → ℝ := fun j =>
    2 * (1 + cellMass P x / armMass P (decide (j.val / 2 = 1)) x)
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    have h := (observed_inverse_arm_bounds ε P hε hP x hp
      (decide (j.val / 2 = 1))).1
    dsimp [w]
    linarith
  have hmass : totalMassVecFormula (cellVector P x) = cellMass P x := by
    simp [totalMassVecFormula, armMassVecFormula, cellVector, cellMass, cellIdx]
    ring
  have hq0 : cellVector P x ≠ 0 := by
    intro hz
    rw [hz] at hmass
    simp [totalMassVecFormula, armMassVecFormula] at hmass
    linarith
  have hmod : ∀ v ∈ centeredRectangle c r,
      |armwiseExtensionFormula ε v - armwiseExtensionFormula ε (cellVector P x)| ≤
        ∑ j, w j * |v j - cellVector P x j| := by
    intro v hv
    have h := armwise_modulus_extension.1 ε hε v (cellVector P x) (hQ v hv)
      (fun _ => ENNReal.toReal_nonneg) hq0
    rw [hmass] at h
    simp_rw [anchoredDenom_cellVector_eq_armMass ε P hP x hp] at h
    convert h using 1
    simp [w, armDelta, Fin.sum_univ_succ, cellIdx]
    ring
  have h := jacksonCoeff_reference_boundary_le ε hε K hK c r (cellVector P x) w
    hr hw hQ hq hmod
  apply h.trans_eq
  simp [w, Fin.sum_univ_succ, cellIdx, armRadiusFormula]
  ring

/-- On the actual localized pilot rectangle, logarithmic degree calibration proves the occupied-cell bias bound (20) for the factorial mean itself. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp,hH,hHlarge,hm,hL,hκ,hK,hdegree,hloc), the [stated conclusion](goal) holds. -/
lemma observed_pilotJackson_mean_bias_normalized_le {d : ℕ} (ε : ℝ)
    (P : DiscreteLaw d) (hε : 0 < ε) (hP : ObservedClass ε P)
    (x : Fin d) (hp : 0 < cellMass P x)
    (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H) (m L κ : ℝ)
    (hm : 0 < m) (hL : 1 ≤ L) (hκ : 0 < κ)
    (K : ℕ) (hK : 0 < K) (hdegree : κ * L ≤ K) (Np : Fin 4 → ℕ)
    (hloc : cellVector P x ∈
      pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np)) :
    let b := pilotMidpoint H hH m L Np
    let r := pilotRadiusFormula H hH m L Np
    |(armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoeff ε K b r α * ∏ j, ((cellVector P x j - b j) / r j) ^ (α j).val) -
      armwiseExtensionFormula ε (cellVector P x)| ≤
      512 * (H * (H + 2)) * Real.sqrt 2 * (1 / κ + 1 / κ ^ 2) *
        (Real.sqrt (cellMass P x / (m * ε * L)) + 1 / (m * ε * L)) := by
  have hLp : 0 < L := by linarith
  have hr := pilotRadius_pos H hH m L hm hLp Np
  have hq : cellVector P x ∈ centeredRectangle
      (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np) := by
    intro j
    apply abs_le.mpr
    have hj := hloc j
    dsimp [pilotMidpoint, pilotRadiusFormula]
    constructor <;> linarith [hj.1, hj.2]
  have h := observed_jacksonCoeff_biasEnvelope_le ε P hε hP x hp K hK
    (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np) hr
    (pilotCenteredRectangle_nonneg H hH m L Np) hq
  have hlo (j : Fin 4) : pilotMidpoint H hH m L Np j - pilotRadiusFormula H hH m L Np j =
      pilotLower H hH m L Np j := by dsimp [pilotMidpoint, pilotRadiusFormula]; ring
  have hhi (j : Fin 4) : pilotMidpoint H hH m L Np j + pilotRadiusFormula H hH m L Np j =
      pilotUpperFormula H hH m L Np j := by dsimp [pilotMidpoint, pilotRadiusFormula]; ring
  simp_rw [hlo, hhi] at h
  have henvelope := observed_pilot_biasEnvelope_normalized_le ε P hε hP x hp
    H hH hHlarge m L K κ hm hL hκ hdegree Np hloc
  dsimp only
  apply h.trans
  convert mul_le_mul_of_nonneg_left henvelope (show (0 : ℝ) ≤ 64 by norm_num) using 1
  ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate
