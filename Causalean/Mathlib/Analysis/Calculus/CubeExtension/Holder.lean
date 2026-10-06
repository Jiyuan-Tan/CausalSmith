module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.JetBounds
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Locality

/-!
# Cardinality-independent Hölder bounds for disjoint signed sums

Real inequalities for values and ambient derivative operator norms are primary.
The coefficient depends on the normalized profile bound and the fixed support
separation factor, never the bandwidth, centers, signs, or index cardinality.
The final bridge uses CubeExtension's intrinsic coordinate jets and HolderBallOn.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeExtension
open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- [Uniform Hölder data for an exponent, radius, and function](hyp:β,R,f)
consist of [a nonnegative radius](hyp:nonneg),
[global order-two regularity](hyp:regularity), [a scalar sup bound](hyp:value),
[a scalar β-Hölder bound when β ≤ 1](hyp:value_modulus), and
[a first-derivative sup bound and (β-1)-Hölder bound when β > 1](hyp:first,first_modulus). -/
structure UniformHolderBounds (β R : ℝ) (f : E → ℝ) : Prop where
  nonneg : 0 ≤ R
  regularity : ContDiff ℝ 2 f
  value : ∀ x, |f x| ≤ R
  value_modulus : β ≤ 1 → ∀ x y, |f x - f y| ≤ R * ‖x - y‖ ^ β
  first : 1 < β → ∀ x, ‖fderiv ℝ f x‖ ≤ R
  first_modulus : 1 < β → ∀ x y,
    ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ R * ‖x - y‖ ^ (β - 1)

/-- [A scale-separated signed sum](hyp:hsep) with [jet locality](hyp:hloc),
[single-profile scaled bounds](hyp:hbound), [a nonnegative constant](hyp:hC),
and [coefficients of absolute value at most one](hyp:hσ)
has [the single-profile scalar sup bound](goal), for [positive bandwidth and factor](hyp:hh,hδ),
[any exponent](hyp:β), and [every point](hyp:x). -/
theorem signedSum_value_bound {K : ι → Set E} {β h δ C : ℝ} {f : ι → E → ℝ}
    (hsep : SupportSeparation K h δ) (hh : 0 < h) (hδ : 0 < δ)
    (hloc : JetLocality f K) (hbound : ∀ i, ScaledJetBounds β h (f i) C)
    (hC : 0 ≤ C)
    (σ : ι → ℝ) (hσ : ∀ i, |σ i| ≤ 1) (x : E) :
    |signedSum σ f x| ≤ C * h ^ β := by
  classical
  by_cases hx : ∃ i, x ∈ K i
  · obtain ⟨i, hi⟩ := hx
    rw [(signedSum_jets_eq hsep hh hδ hloc (fun i => (hbound i).regularity) σ i x hi).1,
      abs_mul]
    exact (mul_le_mul_of_nonneg_right (hσ i) (abs_nonneg _)).trans
      (by simpa using (hbound i).value x)
  · rw [(signedSum_jets_zero hloc (fun i => (hbound i).regularity) σ x
      (not_exists.mp hx)).1, abs_zero]
    exact mul_nonneg hC (Real.rpow_nonneg hh.le _)

/-- [A scale-separated signed sum](hyp:hsep) with [jet locality](hyp:hloc),
[single-profile scaled bounds](hyp:hbound), [a nonnegative constant](hyp:hC),
and [coefficients of absolute value at most one](hyp:hσ)
has [the single-profile first-jet bound](goal), for [positive bandwidth and factor](hyp:hh,hδ),
[any exponent](hyp:β), and [every point](hyp:x). -/
theorem signedSum_first_bound {K : ι → Set E} {β h δ C : ℝ} {f : ι → E → ℝ}
    (hsep : SupportSeparation K h δ) (hh : 0 < h) (hδ : 0 < δ)
    (hloc : JetLocality f K) (hbound : ∀ i, ScaledJetBounds β h (f i) C)
    (hC : 0 ≤ C)
    (σ : ι → ℝ) (hσ : ∀ i, |σ i| ≤ 1) (x : E) :
    ‖fderiv ℝ (signedSum σ f) x‖ ≤ C * h ^ (β - 1) := by
  classical
  by_cases hx : ∃ i, x ∈ K i
  · obtain ⟨i, hi⟩ := hx
    rw [(signedSum_jets_eq hsep hh hδ hloc (fun i => (hbound i).regularity) σ i x hi).2.1,
      norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hσ i) (norm_nonneg _)).trans
      (by simpa using (hbound i).first x)
  · rw [(signedSum_jets_zero hloc (fun i => (hbound i).regularity) σ x
      (not_exists.mp hx)).2.1, norm_zero]
    exact mul_nonneg hC (Real.rpow_nonneg hh.le _)

/-- [A nonnegative quantity](hyp:ha) with [a scaled sup bound](hyp:haC) is
[bounded by the separated-distance Hölder coefficient](goal) when
[distance is at least δh](hyp:hsep), [bandwidth and separation factor are positive](hyp:hh,hδ),
[the constant and distance are nonnegative](hyp:hC,hr), and
[the exponent lies in `(0,1]`](hyp:hs,hs1).

Use `Real.rpow_le_rpow` on h ≤ δ⁻¹*r and `Real.mul_rpow` to separate
the factors. Bound (δ⁻¹)^s by 1+δ⁻¹, splitting δ⁻¹ ≤ 1 versus 1 ≤ δ⁻¹;
the first case uses `Real.rpow_le_one`, the second exponent monotonicity.
The hypotheses give r>0 even at a support boundary point. -/
theorem separated_distance_holder {a C h δ r s : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hh : 0 < h) (hδ : 0 < δ) (hr : 0 ≤ r)
    (hs : 0 < s) (hs1 : s ≤ 1) (hsep : δ * h ≤ r)
    (haC : a ≤ 2 * C * h ^ s) :
    a ≤ (2 * C * (1 + δ⁻¹)) * r ^ s := by
  have hi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  have hp : δ⁻¹ ^ s ≤ 1 + δ⁻¹ := by
    by_cases hi1 : δ⁻¹ ≤ 1
    · exact (Real.rpow_le_one hi hi1 hs.le).trans (by linarith)
    · have := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hi1) hs1
      rw [Real.rpow_one] at this
      linarith
  have hhr : h ≤ δ⁻¹ * r := by
    calc
      h = δ⁻¹ * (δ * h) := by rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
      _ ≤ δ⁻¹ * r := mul_le_mul_of_nonneg_left hsep hi
  calc
    a ≤ 2 * C * h ^ s := haC
    _ ≤ 2 * C * (δ⁻¹ * r) ^ s :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hh.le hhr hs.le) (by positivity)
    _ = 2 * C * (δ⁻¹ ^ s * r ^ s) := by rw [Real.mul_rpow hi hr]
    _ ≤ 2 * C * ((1 + δ⁻¹) * r ^ s) := by
      gcongr
    _ = (2 * C * (1 + δ⁻¹)) * r ^ s := by ring

/-- With [separated supports](hyp:hsep), [jet locality](hyp:hloc),
[single-profile scaled bounds](hyp:hbound) with [a nonnegative constant](hyp:hC),
and [bounded signs](hyp:hσ),
[the signed sum has a cardinality-independent scalar β-Hölder modulus](goal)
for [β in `(0,1]`](hyp:hβ,hβ1) and [positive bandwidth and separation factor](hyp:hh,hδ).

Split the two points into: same support (use a single-profile estimate);
distinct supports (use separation and `separated_distance_holder`);
one outside every support (use the active profile's global estimate, whose
value at the other point is zero); both outside (zero). Boundary points belong
to the closed supports. No sum over index-cardinality is permitted. -/
theorem signedSum_value_holder {K : ι → Set E} {β h δ C : ℝ} {f : ι → E → ℝ}
    (hsep : SupportSeparation K h δ) (hh : 0 < h) (hδ : 0 < δ)
    (hloc : JetLocality f K) (hbound : ∀ i, ScaledJetBounds β h (f i) C)
    (hC : 0 ≤ C) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (σ : ι → ℝ) (hσ : ∀ i, |σ i| ≤ 1) (x y : E) :
    |signedSum σ f x - signedSum σ f y| ≤
      (2 * C * (1 + δ⁻¹)) * ‖x - y‖ ^ β := by
  classical
  have hreg : ∀ i, ContDiff ℝ 2 (f i) := fun i => (hbound i).regularity
  have hcoef : 2 * C ≤ 2 * C * (1 + δ⁻¹) := by
    have : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    nlinarith
  have heq (i : ι) (z : E) (hz : z ∈ K i) :
      signedSum σ f z = σ i • f i z := by
    simpa only [smul_eq_mul] using (signedSum_jets_eq hsep hh hδ hloc hreg σ i z hz).1
  have hzero (z : E) (hz : ∀ i, z ∉ K i) : signedSum σ f z = 0 :=
    (signedSum_jets_zero hloc hreg σ z hz).1
  have hsingle (i : ι) (u v : E) :
      ‖σ i • f i u - σ i • f i v‖ ≤
        (2 * C * (1 + δ⁻¹)) * ‖u - v‖ ^ β := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ ‖f i u - f i v‖ :=
        by simpa using mul_le_mul_of_nonneg_right (hσ i) (norm_nonneg (f i u - f i v))
      _ ≤ 2 * C * ‖u - v‖ ^ β := by
        simpa only [Real.norm_eq_abs] using (hbound i).value_holder hβ hβ1 hh u v
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (norm_nonneg _) _)
  simp only [← Real.norm_eq_abs]
  change ‖signedSum σ f x - signedSum σ f y‖ ≤ _
  by_cases hx : ∃ i, x ∈ K i
  · obtain ⟨i, hi⟩ := hx
    by_cases hy : ∃ j, y ∈ K j
    · obtain ⟨j, hj⟩ := hy
      by_cases hij : i = j
      · subst j
        rw [heq i x hi, heq i y hj]
        exact hsingle i x y
      · apply separated_distance_holder (norm_nonneg _) hC hh hδ (norm_nonneg _)
          hβ hβ1 (hsep.separated i j hij x hi y hj)
        calc
          _ ≤ ‖signedSum σ f x‖ + ‖signedSum σ f y‖ := norm_sub_le _ _
          _ ≤ 2 * C * h ^ β := by
            have hxbound := signedSum_value_bound hsep hh hδ hloc hbound hC σ hσ x
            have hybound := signedSum_value_bound hsep hh hδ hloc hbound hC σ hσ y
            simp only [Real.norm_eq_abs]
            linarith
    · have hyoff := not_exists.mp hy
      rw [heq i x hi, hzero y hyoff]
      have hpzero : f i y = 0 := hloc.value i y (hyoff i)
      simpa only [hpzero, smul_zero, sub_zero] using hsingle i x y
  · have hxoff := not_exists.mp hx
    by_cases hy : ∃ j, y ∈ K j
    · obtain ⟨j, hj⟩ := hy
      rw [hzero x hxoff, heq j y hj]
      have hpzero : f j x = 0 := hloc.value j x (hxoff j)
      simpa only [hpzero, smul_zero, zero_sub] using hsingle j x y
    · rw [hzero x hxoff, hzero y (not_exists.mp hy)]
      simp only [sub_self, norm_zero]
      positivity

/-- With [separated supports](hyp:hsep), [jet locality](hyp:hloc),
[single-profile scaled bounds](hyp:hbound) with [a nonnegative constant](hyp:hC),
and [bounded signs](hyp:hσ),
[the signed sum has a cardinality-independent derivative (β-1)-Hölder modulus](goal)
for [β in `(1,2]`](hyp:hβ,hβ2) and [positive bandwidth and separation factor](hyp:hh,hδ).

Repeat the same four support cases as `signedSum_value_holder`, now for
the first derivative and exponent β-1. Use the Hessian bound for same-cell
and exterior comparisons. The endpoint β=2 must remain included. -/
theorem signedSum_first_holder {K : ι → Set E} {β h δ C : ℝ} {f : ι → E → ℝ}
    (hsep : SupportSeparation K h δ) (hh : 0 < h) (hδ : 0 < δ)
    (hloc : JetLocality f K) (hbound : ∀ i, ScaledJetBounds β h (f i) C)
    (hC : 0 ≤ C) (hβ : 1 < β) (hβ2 : β ≤ 2)
    (σ : ι → ℝ) (hσ : ∀ i, |σ i| ≤ 1) (x y : E) :
    ‖fderiv ℝ (signedSum σ f) x - fderiv ℝ (signedSum σ f) y‖ ≤
      (2 * C * (1 + δ⁻¹)) * ‖x - y‖ ^ (β - 1) := by
  classical
  have hreg : ∀ i, ContDiff ℝ 2 (f i) := fun i => (hbound i).regularity
  have hcoef : 2 * C ≤ 2 * C * (1 + δ⁻¹) := by
    have : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    nlinarith
  have heq (i : ι) (z : E) (hz : z ∈ K i) :
      fderiv ℝ (signedSum σ f) z = σ i • fderiv ℝ (f i) z := by
    exact (signedSum_jets_eq hsep hh hδ hloc hreg σ i z hz).2.1
  have hzero (z : E) (hz : ∀ i, z ∉ K i) : fderiv ℝ (signedSum σ f) z = 0 :=
    (signedSum_jets_zero hloc hreg σ z hz).2.1
  have hsingle (i : ι) (u v : E) :
      ‖σ i • fderiv ℝ (f i) u - σ i • fderiv ℝ (f i) v‖ ≤
        (2 * C * (1 + δ⁻¹)) * ‖u - v‖ ^ (β - 1) := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ (f i) u - fderiv ℝ (f i) v‖ :=
        by simpa using mul_le_mul_of_nonneg_right (hσ i) (norm_nonneg _)
      _ ≤ 2 * C * ‖u - v‖ ^ (β - 1) := by exact (hbound i).first_holder hβ hβ2 hh u v
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (norm_nonneg _) _)
  change ‖fderiv ℝ (signedSum σ f) x - fderiv ℝ (signedSum σ f) y‖ ≤ _
  by_cases hx : ∃ i, x ∈ K i
  · obtain ⟨i, hi⟩ := hx
    by_cases hy : ∃ j, y ∈ K j
    · obtain ⟨j, hj⟩ := hy
      by_cases hij : i = j
      · subst j
        rw [heq i x hi, heq i y hj]
        exact hsingle i x y
      · apply separated_distance_holder (norm_nonneg _) hC hh hδ (norm_nonneg _)
          (by linarith : 0 < β - 1) (by linarith : β - 1 ≤ 1) (hsep.separated i j hij x hi y hj)
        calc
          _ ≤ ‖fderiv ℝ (signedSum σ f) x‖ + ‖fderiv ℝ (signedSum σ f) y‖ := norm_sub_le _ _
          _ ≤ 2 * C * h ^ (β - 1) := by
            have hxbound := signedSum_first_bound hsep hh hδ hloc hbound hC σ hσ x
            have hybound := signedSum_first_bound hsep hh hδ hloc hbound hC σ hσ y
            linarith
    · have hyoff := not_exists.mp hy
      rw [heq i x hi, hzero y hyoff]
      have hpzero : fderiv ℝ (f i) y = 0 := hloc.first i y (hyoff i)
      simpa only [hpzero, smul_zero, sub_zero] using hsingle i x y
  · have hxoff := not_exists.mp hx
    by_cases hy : ∃ j, y ∈ K j
    · obtain ⟨j, hj⟩ := hy
      rw [hzero x hxoff, heq j y hj]
      have hpzero : fderiv ℝ (f j) x = 0 := hloc.first j x (hxoff j)
      simpa only [hpzero, smul_zero, zero_sub] using hsingle j x y
    · rw [hzero x hxoff, hzero y (not_exists.mp hy)]
      simp only [sub_self, norm_zero]
      positivity

/-- Under [the generic separation and locality interfaces](hyp:hsep,hloc),
[single-profile scaled bounds](hyp:hbound) with [nonnegative constant](hyp:hC),
[β in `(0,2]`](hyp:hβ,hβ2), [h in `(0,1]`](hyp:hh,hh1),
[positive separation factor](hyp:hδ), and [bounded signs](hyp:hσ),
[the finite signed sum satisfies the uniform Hölder bounds of exponent β with
radius 2C(1 + 1/δ)](goal), a radius independent of the bandwidth and of the
number of summands. -/
theorem signedSum_uniform_holder {K : ι → Set E} {β h δ C : ℝ} {f : ι → E → ℝ}
    (hsep : SupportSeparation K h δ) (hh : 0 < h) (hh1 : h ≤ 1) (hδ : 0 < δ)
    (hloc : JetLocality f K) (hbound : ∀ i, ScaledJetBounds β h (f i) C)
    (hC : 0 ≤ C) (hβ : 0 < β) (hβ2 : β ≤ 2)
    (σ : ι → ℝ) (hσ : ∀ i, |σ i| ≤ 1) :
    UniformHolderBounds β (2 * C * (1 + δ⁻¹)) (signedSum σ f) := by
  have hcoef : C ≤ 2 * C * (1 + δ⁻¹) := by
    have : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    nlinarith
  refine ⟨by positivity, signedSum_contDiff σ f (fun i => (hbound i).regularity),
    ?_, ?_, ?_, ?_⟩
  · intro x
    exact (signedSum_value_bound hsep hh hδ hloc hbound hC σ hσ x).trans
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_one hh.le hh1 hβ.le) hC).trans
        (by simpa using hcoef))
  · intro hβ1 x y
    exact signedSum_value_holder hsep hh hδ hloc hbound hC hβ hβ1 σ hσ x y
  · intro hβ1 x
    exact (signedSum_first_bound hsep hh hδ hloc hbound hC σ hσ x).trans
      ((mul_le_mul_of_nonneg_left
        (Real.rpow_le_one hh.le hh1 (by linarith : 0 ≤ β - 1)) hC).trans
        (by simpa using hcoef))
  · intro hβ1 x y
    exact signedSum_first_holder hsep hh hδ hloc hbound hC hβ1 hβ2 σ hσ x y

/-- [A finite signed sum has order-two regularity on any supplied set](goal),
in particular on any supplied closed cube, when [its summands are globally
order-two regular](hyp:hf), for [any coefficients, family, and set](hyp:σ,f,S). -/
theorem signedSum_contDiffOn (σ : ι → ℝ) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (S : Set E) : ContDiffOn ℝ 2 (signedSum σ f) S := by
  exact (signedSum_contDiff σ f hf).contDiffOn

/-- For [an exponent and bandwidth](hyp:β,h), [signs](hyp:σ), and
[an unweighted profile family](hyp:p), [the amplitude-scaled signed sum](goal)
at [a point](hyp:x) is [h to the exponent times the finite signed sum](step:1). -/
noncomputable def scaledSignedSum (β h : ℝ) (σ : ι → ℝ) (p : ι → E → ℝ) (x : E) : ℝ :=
  h ^ β * signedSum σ p x

/-- [The amplitude-scaled signed sum h^β·Σ_i σ_i p_i satisfies the uniform
Hölder bounds of exponent β with radius 2C(1 + 1/δ)](goal) under [separation and
locality](hyp:hsep,hloc), [unweighted bandwidth jet bounds](hyp:hbound),
[a nonnegative profile constant](hyp:hC), [β in `(0,2]`](hyp:hβ,hβ2),
[h in `(0,1]`](hyp:hh,hh1), [positive separation factor](hyp:hδ), and [bounded signs](hyp:hσ).

The exponent-zero single-profile hypothesis expresses value ≤ C,
first jet ≤ C/h, and second jet ≤ C/h²; it is supplied by `scaledCopy_jetBounds`
with exponent zero. Distribute the amplitude over the finite sum, build scaled
bounds and jet locality for `fun i x => h^β * p i x`, and apply
`signedSum_uniform_holder`. Use `Real.rpow_add hh` for the factors; no profile
module needs to be imported here. -/
theorem scaledSignedSum_uniform_holder {K : ι → Set E} {β h δ C : ℝ} {p : ι → E → ℝ}
    (hsep : SupportSeparation K h δ) (hh : 0 < h) (hh1 : h ≤ 1) (hδ : 0 < δ)
    (hloc : JetLocality p K) (hbound : ∀ i, ScaledJetBounds 0 h (p i) C)
    (hC : 0 ≤ C) (hβ : 0 < β) (hβ2 : β ≤ 2)
    (σ : ι → ℝ) (hσ : ∀ i, |σ i| ≤ 1) :
    UniformHolderBounds β (2 * C * (1 + δ⁻¹)) (scaledSignedSum β h σ p) := by
  classical
  let q : ι → E → ℝ := fun i x => h ^ β * p i x
  have hpow : 0 ≤ h ^ β := Real.rpow_nonneg hh.le _
  have hfirst (i : ι) :
      fderiv ℝ (q i) = fun x => h ^ β • fderiv ℝ (p i) x := by
    funext x
    exact fderiv_const_mul ((hbound i).regularity.differentiable (by norm_num) x) _
  have hsecond (i : ι) (x : E) :
      fderiv ℝ (fderiv ℝ (q i)) x =
        h ^ β • fderiv ℝ (fderiv ℝ (p i)) x := by
    rw [hfirst]
    have hd : Differentiable ℝ (fderiv ℝ (p i)) :=
      ((hbound i).regularity.fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
    exact fderiv_fun_const_smul (hd x) _
  have hpower (k : ℝ) : h ^ β * (C * h ^ (0 - k)) = C * h ^ (β - k) := by
    calc
      _ = C * (h ^ β * h ^ (0 - k)) := by ring
      _ = C * h ^ (β + (0 - k)) := by rw [← Real.rpow_add hh]
      _ = _ := by congr 2; ring
  have hqbound : ∀ i, ScaledJetBounds β h (q i) C := by
    intro i
    refine ⟨hC, ?_, ?_, ?_, ?_⟩
    · simpa only [q, smul_eq_mul] using (hbound i).regularity.const_smul (h ^ β)
    · intro x
      change |h ^ β * p i x| ≤ _
      rw [abs_mul, abs_of_nonneg hpow]
      calc
        _ ≤ h ^ β * (C * h ^ (0 : ℝ)) :=
          mul_le_mul_of_nonneg_left ((hbound i).value x) hpow
        _ = C * h ^ β := by rw [Real.rpow_zero]; ring
    · intro x
      rw [hfirst, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpow]
      exact (mul_le_mul_of_nonneg_left ((hbound i).first x) hpow).trans_eq (hpower 1)
    · intro x
      rw [hsecond, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpow]
      exact (mul_le_mul_of_nonneg_left ((hbound i).second x) hpow).trans_eq (hpower 2)
  have hqloc : JetLocality q K := by
    refine ⟨?_, ?_, ?_⟩
    · intro i x hx
      change h ^ β * p i x = 0
      rw [hloc.value i x hx, mul_zero]
    · intro i x hx
      simp only [hfirst, hloc.first i x hx, smul_zero]
    · intro i x hx
      rw [hsecond, hloc.second i x hx, smul_zero]
  have heq : signedSum σ q = scaledSignedSum β h σ p := by
    funext x
    simp only [signedSum, scaledSignedSum, q, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← heq]
  exact signedSum_uniform_holder hsep hh hh1 hδ hqloc hqbound hC hβ hβ2 σ hσ

/-- [Ambient real uniform Hölder bounds of exponent β and radius R](hyp:hf)
imply [membership in the intrinsic Hölder ball of radius R on the set, of order 0
and exponent β when β ≤ 1 and of order 1 and exponent β − 1 otherwise](goal), on
[a set with unique differentiability](hyp:hS), for [β in `(0,2]`](hyp:hβ,hβ2).

The coordinate space uses its existing sup norm. For β ≤ 1 use order zero;
otherwise use order one and exponent β-1. Unique differentiability identifies
within-set jets with ambient jets even on the boundary. Use
`iteratedFDerivWithin_eq_iteratedFDeriv` and order-zero/order-one evaluation
lemmas from Mathlib's ContDiff.FTaylorSeries; coordinate directions have norm
at most one. The reference ambient bridge in ScaledProductBump assumes C∞,
so its headline cannot be applied to the present C² profiles. -/
theorem holderBallOn_of_uniformBounds {d : ℕ} {S : Set (Fin d → ℝ)}
    {β R : ℝ} {f : (Fin d → ℝ) → ℝ} (hS : UniqueDiffOn ℝ S)
    (hf : UniformHolderBounds β R f) (hβ : 0 < β) (hβ2 : β ≤ 2) :
    HolderBallOn S (if β ≤ 1 then 0 else 1)
      (if β ≤ 1 then β else β - 1) R f := by
  classical
  have hzero (v : Fin 0 → Fin d) (x : Fin d → ℝ) :
      coordJetOn S 0 f v x = f x := by
    exact iteratedFDerivWithin_zero_apply _
  have hone (v : Fin 1 → Fin d) (x : Fin d → ℝ) (hx : x ∈ S) :
      coordJetOn S 1 f v x = fderiv ℝ f x (Pi.single (v 0) (1 : ℝ)) := by
    unfold coordJetOn
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hS
      (hf.regularity.contDiffAt.of_le (by norm_num)) hx, iteratedFDeriv_one_apply]
  have heval (T : (Fin d → ℝ) →L[ℝ] ℝ) (i : Fin d) :
      |T (Pi.single i (1 : ℝ))| ≤ ‖T‖ := by
    calc
      _ = ‖T (Pi.single i (1 : ℝ))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖T‖ * ‖(Pi.single i (1 : ℝ) : Fin d → ℝ)‖ := T.le_opNorm _
      _ = ‖T‖ := by simp only [Pi.norm_single, norm_one, mul_one]
  by_cases hb : β ≤ 1
  · simp only [if_pos hb]
    refine ⟨hf.regularity.contDiffOn.of_le (by norm_num), ?_, ?_⟩
    · intro j hj v x hx
      have hj0 : j = 0 := by omega
      subst j
      rw [hzero]
      exact hf.value x
    · intro v x hx y hy
      rw [hzero, hzero]
      exact hf.value_modulus hb x y
  · simp only [if_neg hb]
    have hb1 : 1 < β := lt_of_not_ge hb
    refine ⟨hf.regularity.contDiffOn.of_le (by norm_num), ?_, ?_⟩
    · intro j hj v x hx
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
      · rw [hzero]
        exact hf.value x
      · rw [hone v x hx]
        exact (heval _ _).trans (hf.first hb1 x)
    · intro v x hx y hy
      rw [hone v x hx, hone v y hy, ← sub_apply]
      exact (heval _ _).trans (hf.first_modulus hb1 x y)

/-- [Ambient uniform Hölder bounds of exponent β and radius R](hyp:hf) for
[β in `(0,2]`](hyp:hβ,hβ2) give [membership in the same-radius intrinsic Hölder
ball on the normalized closed cube, of order 0 and exponent β when β ≤ 1 and of
order 1 and exponent β − 1 otherwise](goal). -/
theorem holderBallOn_cube_of_uniformBounds {d : ℕ} {β R : ℝ} {f : (Fin d → ℝ) → ℝ}
    (hf : UniformHolderBounds β R f) (hβ : 0 < β) (hβ2 : β ≤ 2) :
    HolderBallOn (cube d) (if β ≤ 1 then 0 else 1)
      (if β ≤ 1 then β else β - 1) R f := by
  apply holderBallOn_of_uniformBounds (hf := hf) (hβ := hβ) (hβ2 := hβ2)
  have hcube : cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
      Pi.le_def, forall_and]
  rw [hcube]
  exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num))

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
