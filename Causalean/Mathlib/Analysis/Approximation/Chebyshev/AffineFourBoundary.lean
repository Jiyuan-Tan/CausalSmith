module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.AffineFour

/-!
# Boundary-adaptive affine Jackson approximation in four dimensions

This module bounds the error of the canonical four-dimensional affine Jackson
polynomial by coordinatewise boundary distance. It combines the existing
positive-kernel moment estimates with a cosine displacement inequality and
affine rectangle transport.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.AffineFourBoundary

open Causalean.Mathlib.Analysis.JacksonApproximation
open MeasureTheory
open scoped BigOperators

/-- A [base phase](hyp:theta) and [phase displacement](hyp:t) give [a bound on
the cosine displacement by its sine-weighted linear part and quadratic remainder](goal).
The estimate remains valid at endpoints, where the linear term vanishes. -/
theorem abs_cos_add_sub_cos_le (theta t : ℝ) :
    |Real.cos (theta + t) - Real.cos theta| ≤
      |Real.sin theta| * |t| + t ^ 2 / 2 := by
  have hcos : |Real.cos t - 1| ≤ t ^ 2 / 2 := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one t))]
    linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  calc
    |Real.cos (theta + t) - Real.cos theta| =
        |Real.cos theta * (Real.cos t - 1) - Real.sin theta * Real.sin t| := by
          rw [Real.cos_add]
          congr 1
          ring
    _ ≤ |Real.cos theta * (Real.cos t - 1)| +
          |Real.sin theta * Real.sin t| := by
            simpa [sub_eq_add_neg] using
              (abs_add_le (Real.cos theta * (Real.cos t - 1))
                (-(Real.sin theta * Real.sin t)))
    _ = |Real.cos theta| * |Real.cos t - 1| +
          |Real.sin theta| * |Real.sin t| := by rw [abs_mul, abs_mul]
    _ ≤ |Real.sin theta| * |t| + t ^ 2 / 2 := by
      have h1 := mul_le_mul_of_nonneg_left hcos (abs_nonneg (Real.cos theta))
      have h2 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := t))
        (abs_nonneg (Real.sin theta))
      have h3 := Real.abs_cos_le_one theta
      nlinarith [sq_nonneg t]

/-- A [rectangle center](hyp:c), [positive coordinate radii](hyp:r,hr), [a point
in the ambient space](hyp:y), and [a selected coordinate](hyp:i) identify [the
physical sine factor with the square root of the two face distances' product](goal). -/
theorem radius_mul_abs_sin_arccos_eq_boundary
    (c r y : Fin 4 → ℝ) (hr : ∀ i, 0 < r i)
    (i : Fin 4) :
    r i * |Real.sin (Real.arccos (normalizedPoint c r y i))| =
      Real.sqrt ((y i - (c i - r i)) * ((c i + r i) - y i)) := by
  have hrad :
      (y i - (c i - r i)) * ((c i + r i) - y i) =
        (r i) ^ 2 * (1 - normalizedPoint c r y i ^ 2) := by
    simp only [normalizedPoint]
    field_simp [ne_of_gt (hr i)]
    ring
  rw [Real.sin_arccos, abs_of_nonneg (Real.sqrt_nonneg _), hrad,
    Real.sqrt_mul (sq_nonneg (r i)), Real.sqrt_sq (le_of_lt (hr i))]

/-- A [positive Jackson order](hyp:hK), [a function continuous on the normalized
cube](hyp:g,hg), [nonnegative coordinate weights](hyp:r,hr), and [a nonnegative
Lipschitz constant with its weighted coordinate bound](hyp:L,hL,hlip), evaluated
at [a phase point](hyp:theta), give [a tensor Jackson error bound with a
boundary-adaptive first-order term and a second-order remainder](goal). -/
theorem tensorConvolution_boundary_adaptive {d K : ℕ} (hK : 0 < K)
    (g : (Fin d → ℝ) → ℝ) (hg : ContinuousOn g (normalizedCube d))
    (r : Fin d → ℝ) (hr : ∀ i, 0 ≤ r i)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x ∈ normalizedCube d, ∀ z ∈ normalizedCube d,
      |g x - g z| ≤ L * ∑ i, r i * |x i - z i|)
    (theta : Fin d → ℝ) :
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
            (hlip _ (cosPoint_mem_normalizedCube _) _
              (cosPoint_mem_normalizedCube _)) (tensorJackson_nonneg hK u)
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

/-- A [positive Jackson order](hyp:hK), [a centered rectangle with positive
coordinate radii](hyp:c,r,hr), [a continuous physical-coordinate Lipschitz
function](hyp:f,hf,L,hL,hlip), [a polynomial pair realizing the canonical affine
tensor convolution](hyp:p,q,hpeval,hqeval), and [a point in that rectangle](hyp:y,hy)
give [a boundary-adaptive error bound for that same affine Jackson polynomial](goal). -/
theorem affineJackson_boundary_adaptive_four {K : ℕ} (hK : 0 < K)
    (c r : Fin 4 → ℝ) (hr : ∀ i, 0 < r i)
    (f : (Fin 4 → ℝ) → ℝ) (hf : ContinuousOn f (centeredRectangle c r))
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ y ∈ centeredRectangle c r, ∀ z ∈ centeredRectangle c r,
      |f y - f z| ≤ L * ∑ i, |y i - z i|)
    (p q : MvPolynomial (Fin 4) ℝ)
    (hpeval : ∀ y, MvPolynomial.eval y p =
      MvPolynomial.eval (normalizedPoint c r y) q)
    (hqeval : ∀ x, MvPolynomial.eval (cosPoint x) q =
      tensorConvolution K (fun z => f (affinePoint c r z)) x)
    (y : Fin 4 → ℝ) (hy : y ∈ centeredRectangle c r) :
    |MvPolynomial.eval y p - f y| ≤
      32 * L * ∑ i : Fin 4,
        (Real.sqrt ((y i - (c i - r i)) * ((c i + r i) - y i)) / (K : ℝ) +
          r i / (K : ℝ) ^ 2) := by
  have haff : Continuous (affinePoint c r) := by
    apply continuous_pi
    intro i
    exact continuous_const.add (continuous_const.mul (continuous_apply i))
  have hpull : ContinuousOn (fun z => f (affinePoint c r z)) (normalizedCube 4) :=
    hf.comp haff.continuousOn
      (fun z hz => affinePoint_mem_centeredRectangle c r z hr hz)
  have hlip_pull : ∀ x ∈ normalizedCube 4, ∀ z ∈ normalizedCube 4,
      |f (affinePoint c r x) - f (affinePoint c r z)| ≤
        L * ∑ i, r i * |x i - z i| := by
    intro x hx z hz
    have h := hlip (affinePoint c r x)
      (affinePoint_mem_centeredRectangle c r x hr hx) (affinePoint c r z)
      (affinePoint_mem_centeredRectangle c r z hr hz)
    have hcoord (i : Fin 4) :
        |affinePoint c r x i - affinePoint c r z i| = r i * |x i - z i| := by
      simp only [affinePoint]
      convert congrArg abs (show c i + r i * x i - (c i + r i * z i) =
        r i * (x i - z i) by ring) using 1
      rw [abs_mul, abs_of_pos (hr i)]
    simpa only [hcoord] using h
  let theta : Fin 4 → ℝ := fun i => Real.arccos (normalizedPoint c r y i)
  have hn := normalizedPoint_mem_normalizedCube c r y hr hy
  have hcos : cosPoint theta = normalizedPoint c r y := by
    funext i
    exact Real.cos_arccos (hn i).1 (hn i).2
  have happ := tensorConvolution_boundary_adaptive hK
    (fun z => f (affinePoint c r z)) hpull r
    (fun i => le_of_lt (hr i)) L hL hlip_pull theta
  calc
    |MvPolynomial.eval y p - f y| =
        |tensorConvolution K (fun z => f (affinePoint c r z)) theta -
          f (affinePoint c r (cosPoint theta))| := by
            rw [hpeval y, ← hcos, hqeval theta, hcos,
              affinePoint_normalizedPoint c r y hr]
    _ ≤ L * ∑ i : Fin 4,
        (32 * r i * |Real.sin (theta i)| / (K : ℝ) +
          32 * r i / (K : ℝ) ^ 2) := happ
    _ = 32 * L * ∑ i : Fin 4,
          (Real.sqrt ((y i - (c i - r i)) * ((c i + r i) - y i)) / (K : ℝ) +
            r i / (K : ℝ) ^ 2) := by
      have hterm (i : Fin 4) :
          32 * r i * |Real.sin (theta i)| / (K : ℝ) +
              32 * r i / (K : ℝ) ^ 2 =
            32 * (Real.sqrt ((y i - (c i - r i)) * ((c i + r i) - y i)) /
              (K : ℝ) + r i / (K : ℝ) ^ 2) := by
        rw [show 32 * r i * |Real.sin (theta i)| =
          32 * (r i * |Real.sin (theta i)|) by ring,
          radius_mul_abs_sin_arccos_eq_boundary c r y hr i]
        ring
      simp_rw [hterm]
      rw [← Finset.mul_sum]
      ring

/-- A [positive Jackson order](hyp:hK), [a centered rectangle with positive
coordinate radii](hyp:c,r,hr), and [a continuous physical-coordinate Lipschitz
function](hyp:f,hf,L,hL,hlip) give [the canonical affine tensor Jackson polynomial
with its evaluation and degree identities and a boundary-adaptive pointwise error bound](goal). -/
theorem affineJackson_boundary_exists_four {K : ℕ} (hK : 0 < K)
    (c r : Fin 4 → ℝ) (hr : ∀ i, 0 < r i)
    (f : (Fin 4 → ℝ) → ℝ) (hf : ContinuousOn f (centeredRectangle c r))
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ y ∈ centeredRectangle c r, ∀ z ∈ centeredRectangle c r,
      |f y - f z| ≤ L * ∑ i, |y i - z i|) :
    ∃ p q : MvPolynomial (Fin 4) ℝ,
      (∀ y, MvPolynomial.eval y p =
        MvPolynomial.eval (normalizedPoint c r y) q) ∧
      (∀ x, MvPolynomial.eval (cosPoint x) q =
        tensorConvolution K (fun z => f (affinePoint c r z)) x) ∧
      (∀ m ∈ p.support, ∀ i, m i ≤ 2 * (K - 1)) ∧
      p.totalDegree ≤ 8 * (K - 1) ∧
      ∀ y ∈ centeredRectangle c r,
        |MvPolynomial.eval y p - f y| ≤
          32 * L * ∑ i : Fin 4,
            (Real.sqrt ((y i - (c i - r i)) * ((c i + r i) - y i)) /
              (K : ℝ) + r i / (K : ℝ) ^ 2) := by
  obtain ⟨p, q, hpeval, hqeval, hpcoord, hptotal⟩ :=
    affineJackson_exists_mvPolynomial_four hK c r hr f hf
  refine ⟨p, q, hpeval, hqeval, hpcoord, hptotal, ?_⟩
  intro y hy
  exact affineJackson_boundary_adaptive_four hK c r hr f hf L hL hlip
    p q hpeval hqeval y hy

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.AffineFourBoundary
