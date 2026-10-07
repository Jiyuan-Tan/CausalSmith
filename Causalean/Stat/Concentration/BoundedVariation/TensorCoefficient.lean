module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ChebyshevOneNorm
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.EquispacedLagrange
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ParametricTensor
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorGridWeights
public import Causalean.Stat.Concentration.BoundedVariation.TensorChebyshev
public import Causalean.Stat.Concentration.BoundedVariation.Variation
public import Causalean.Stat.Concentration.BoundedVariation.WeightedIntegral

/-!
# Bounded-variation tensor coefficient paths

For a continuous family of bounded-degree tensor polynomials, each fixed monomial coefficient is
a continuous path. A uniform bounded-variation envelope for polynomial values on the normalized
cube transfers to the coefficient paths with an explicit exponential degree cost.
-/

@[expose] public section

noncomputable section

open Causalean.Mathlib.Analysis.JacksonApproximation
open Causalean.Mathlib.Analysis.Approximation.Chebyshev
open Causalean.Stat.Concentration.BoundedVariation
open MeasureTheory
open scoped BigOperators

namespace Causalean.Stat.Concentration.BoundedVariation

/-- [The coefficient path](goal) of [a time-indexed family of polynomials in
d variables](hyp:p) [whose degree in each variable is at most D](hyp:hdeg)
and [whose values at every point of the integer grid {0, …, D}^d vary
continuously in time](hyp:hgrid), at [a monomial index a](hyp:a), is the
continuous real path on the unit time interval recording the coefficient of
that monomial at each time.

The coefficient of a continuously varying bounded-degree tensor polynomial, packaged as a
continuous real path on the unit threshold interval.
-/
def tensorCoefficientPath {d D : ℕ} (p : Time → MvPolynomial (Fin d) ℝ)
    (hdeg : ∀ t i, (p t).degreeOf i ≤ D)
    (hgrid : ∀ a : Fin d → Fin (D + 1),
      Continuous (fun t => MvPolynomial.eval (fun i => (a i : ℝ)) (p t)))
    (a : Fin d → Fin (D + 1)) : Path :=
  ⟨fun t => tensorCoeffs (D := D) (p t) a,
    continuous_tensorCoeffs_of_grid p hdeg hgrid a⟩

/-- Integrating time-indexed functions against a probability measure preserves a uniform
bound on their total variation. Every time section is integrable, and the samplewise extended
variation is at most the finite real bound `B`.

For each finite time partition, bound the sum of absolute integral increments by the integral
of the sum of absolute pointwise increments. Then take the supremum over partitions.
-/
theorem eVariationOn_integral_le_of_uniform
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → Time → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hInt : ∀ t, Integrable (fun x => f x t) μ)
    (hvar : ∀ x, eVariationOn (f x) Set.univ ≤ ENNReal.ofReal B) :
    eVariationOn (fun t => ∫ x, f x t ∂μ) Set.univ ≤ ENNReal.ofReal B := by
  rw [eVariationOn]
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, _⟩ := p
  have hstep (i : ℕ) :
      Integrable (fun x => dist (f x (u (i + 1))) (f x (u i))) μ := by
    simpa [Real.dist_eq] using (hInt (u (i + 1))).sub (hInt (u i)) |>.abs
  have hpoint (x : α) :
      (∑ i ∈ Finset.range n, dist (f x (u (i + 1))) (f x (u i))) ≤ B := by
    have hv := (eVariationOn.sum_le (f := f x) (n := n) hu
      (fun _ => Set.mem_univ _)).trans (hvar x)
    have he : ENNReal.ofReal
        (∑ i ∈ Finset.range n, dist (f x (u (i + 1))) (f x (u i))) ≤
        ENNReal.ofReal B := by
      simpa [ENNReal.ofReal_sum_of_nonneg (fun i _ => dist_nonneg), edist_dist] using hv
    exact (ENNReal.ofReal_le_ofReal_iff hB).mp he
  have hsum : Integrable
      (fun x => ∑ i ∈ Finset.range n, dist (f x (u (i + 1))) (f x (u i))) μ :=
    integrable_finsetSum _ (fun i _ => hstep i)
  have hreal :
      (∑ i ∈ Finset.range n,
        dist (∫ x, f x (u (i + 1)) ∂μ) (∫ x, f x (u i) ∂μ)) ≤ B := by
    calc
      _ ≤ ∑ i ∈ Finset.range n,
          ∫ x, dist (f x (u (i + 1))) (f x (u i)) ∂μ := by
        apply Finset.sum_le_sum
        intro i _
        simpa [Real.dist_eq, integral_sub (hInt (u (i + 1))) (hInt (u i))] using
          (abs_integral_le_integral_abs
            (f := fun x => f x (u (i + 1)) - f x (u i)) (μ := μ))
      _ = ∫ x, ∑ i ∈ Finset.range n,
          dist (f x (u (i + 1))) (f x (u i)) ∂μ := by
        exact (integral_finsetSum _ (fun i _ => hstep i)).symm
      _ ≤ ∫ _ : α, B ∂μ :=
        integral_mono hsum (integrable_const B) hpoint
      _ = B := by simp
  have he : ENNReal.ofReal
      (∑ i ∈ Finset.range n,
        dist (∫ x, f x (u (i + 1)) ∂μ) (∫ x, f x (u i) ∂μ)) ≤
      ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hreal
  simpa [ENNReal.ofReal_sum_of_nonneg (fun i _ => dist_nonneg), edist_dist] using he

/-- If every value of a degree-bounded tensor-polynomial family on the normalized cube has
finite total variation in time, then every fixed monomial coefficient path has finite total
variation. The conclusion is qualitative and does not use a uniform variation envelope.

Choose a finite unisolvent tensor grid inside the cube. Its evaluation map has a fixed linear
inverse, so each coefficient is a finite linear combination of the grid evaluation paths.
-/
theorem tensorCoefficientPath_bv_of_cube {d D : ℕ}
    (p : Time → MvPolynomial (Fin d) ℝ)
    (hdeg : ∀ t i, (p t).degreeOf i ≤ D)
    (hgrid : ∀ a : Fin d → Fin (D + 1),
      Continuous (fun t => MvPolynomial.eval (fun i => (a i : ℝ)) (p t)))
    (hcont : ∀ x ∈ normalizedCube d,
      Continuous (fun t => MvPolynomial.eval x (p t)))
    (hBV : ∀ x (hx : x ∈ normalizedCube d),
      eVariationOn (⟨fun t => MvPolynomial.eval x (p t), hcont x hx⟩ : Path)
        Set.univ < ⊤) :
    ∀ a, eVariationOn (tensorCoefficientPath p hdeg hgrid a) Set.univ < ⊤ := by
  classical
  let I := Fin d → Fin (D + 1)
  let V := I → ℝ
  let x : I → Fin d → ℝ := fun b i => (b i : ℝ) / (D + 1)
  have hx (b : I) : x b ∈ normalizedCube d := by
    intro i
    change -1 ≤ (b i : ℝ) / (D + 1) ∧
      (b i : ℝ) / (D + 1) ≤ 1
    have hD : (0 : ℝ) < D + 1 := by positivity
    have hb : (b i : ℝ) ≤ D := by exact_mod_cast Nat.le_of_lt_succ (b i).isLt
    constructor
    · apply (le_div_iff₀ hD).2
      nlinarith [show (0 : ℝ) ≤ (b i : ℝ) by positivity]
    · apply (div_le_iff₀ hD).2
      nlinarith
  let E : V →ₗ[ℝ] V :=
    { toFun := fun c b => ∑ a : I, c a *
          MvPolynomial.eval (x b) (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))
      map_add' := by
        intro c c'
        funext b
        change (∑ a, (c a + c' a) * _) = (∑ a, c a * _) + ∑ a, c' a * _
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        funext b
        change (∑ a, (r * c a) * _) = r * ∑ a, c a * _
        simp [mul_assoc, Finset.mul_sum] }
  have hEval (c : V) (b : I) :
      E c b = MvPolynomial.eval (x b) (tensorPolynomial c) := by
    change (∑ a, c a * MvPolynomial.eval (x b)
      (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) = _
    simp [tensorPolynomial, MvPolynomial.eval_monomial]
    rfl
  have hdegpoly (c : V) (i : Fin d) :
      (tensorPolynomial c).degreeOf i ≤ D := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have hc : (tensorPolynomial c).coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
    simp only [tensorPolynomial, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial] at hc
    obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    split_ifs at ha with he
    · rw [← he]
      change (a i : ℕ) ≤ D
      exact Nat.le_of_lt_succ (a i).isLt
    · exact (ha rfl).elim
  have hcoeff (c : V) (a : I) :
      tensorCoeffs (tensorPolynomial c) a = c a := by
    have hExp : Function.Injective (tensorExponent (d := d) (D := D)) := by
      intro b b' h
      funext i
      apply Fin.ext
      have hi := congrArg (fun m : Fin d →₀ ℕ => m i) h
      simpa [tensorExponent] using hi
    simp only [tensorCoeffs, tensorPolynomial, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      have hne : tensorExponent b ≠ tensorExponent a := fun h => hba (hExp h)
      simp [hne]
    · intro h
      exact (h (Finset.mem_univ a)).elim
  have hinj : Function.Injective E := by
    intro c c' h
    let S : Fin d → Finset ℝ :=
      fun _ => Finset.univ.image (fun j : Fin (D + 1) => (j : ℝ) / (D + 1))
    have hcard (i : Fin d) : (S i).card = D + 1 := by
      dsimp [S]
      rw [Finset.card_image_of_injective]
      · simp
      · intro a b hab
        apply Fin.ext
        have hD : (D + 1 : ℝ) ≠ 0 := by positivity
        have : (a : ℝ) = (b : ℝ) := (div_left_inj' hD).mp hab
        exact_mod_cast this
    have hpoly : tensorPolynomial c = tensorPolynomial c' := by
      have hdegree (i : Fin d) :
          (tensorPolynomial c - tensorPolynomial c').degreeOf i < (S i).card := by
        rw [hcard i]
        exact lt_of_le_of_lt
          (MvPolynomial.degreeOf_sub_le i (tensorPolynomial c) (tensorPolynomial c'))
          (Nat.lt_succ_of_le (max_le (hdegpoly c i) (hdegpoly c' i)))
      have hzero : tensorPolynomial c - tensorPolynomial c' = 0 :=
        MvPolynomial.eq_zero_of_eval_zero_at_prod_finset
          (tensorPolynomial c - tensorPolynomial c') S hdegree (by
            intro y hy
            have hchoice : ∀ i : Fin d, ∃ b : Fin (D + 1), (b : ℝ) / (D + 1) = y i := by
              intro i
              obtain ⟨b, _, hb⟩ := Finset.mem_image.mp (hy i)
              exact ⟨b, hb⟩
            choose b hb using hchoice
            have hxy : x b = y := funext hb
            have he := congrArg (fun v : V => v b) h
            simpa [hEval, MvPolynomial.eval_sub, hxy] using sub_eq_zero.mpr he)
      exact sub_eq_zero.mp hzero
    funext b
    calc
      c b = tensorCoeffs (tensorPolynomial c) b := (hcoeff c b).symm
      _ = tensorCoeffs (tensorPolynomial c') b := by rw [hpoly]
      _ = c' b := hcoeff c' b
  let e := LinearEquiv.ofBijective E ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  let g : Time → V := fun t b => MvPolynomial.eval (x b) (p t)
  have hg (t : Time) : g t = E (tensorCoeffs (D := D) (p t)) := by
    funext b
    change MvPolynomial.eval (x b) (p t) = E (tensorCoeffs (p t)) b
    rw [hEval, tensorPolynomial_tensorCoeffs (p t) (hdeg t)]
  have hformula (a : I) (t : Time) :
      tensorCoeffs (p t) a =
        ∑ b : I, (e.symm (Pi.single b (1 : ℝ))) a * g t b := by
    have he : e.symm (g t) = tensorCoeffs (p t) := by
      rw [hg]
      exact e.symm_apply_apply _
    rw [← congrArg (fun v : V => v a) he]
    conv_lhs => rw [← LinearMap.sum_single_apply (fun _ : I => ℝ) (g t)]
    rw [map_sum]
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro b _
    have hs : Pi.single b (g t b) = (g t b) • Pi.single b (1 : ℝ) := by
      rw [← Pi.single_smul]
      simp
    rw [hs, map_smul]
    change g t b * (e.symm (Pi.single b (1 : ℝ))) a =
      (e.symm (Pi.single b (1 : ℝ))) a * g t b
    ring
  have hadd (f k : Time → ℝ) :
      eVariationOn (fun t => f t + k t) Set.univ ≤
        eVariationOn f Set.univ + eVariationOn k Set.univ := by
    apply iSup_le
    rintro ⟨n, ⟨u, hu, hus⟩⟩
    calc
      (∑ i ∈ Finset.range n,
        edist (f (u (i + 1)) + k (u (i + 1))) (f (u i) + k (u i))) ≤
          (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          (∑ i ∈ Finset.range n, edist (k (u (i + 1))) (k (u i))) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_le_sum (fun i _ => edist_add_add_le _ _ _ _)
      _ ≤ eVariationOn f Set.univ + eVariationOn k Set.univ :=
        add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)
  have hsum (s : Finset I) (f : I → Time → ℝ) :
      eVariationOn (fun t => ∑ b ∈ s, f b t) Set.univ ≤
        ∑ b ∈ s, eVariationOn (f b) Set.univ := by
    induction s using Finset.induction_on with
    | empty =>
      simpa using (eVariationOn.constant_on
        (f := fun _ : Time => (0 : ℝ)) (s := Set.univ) (by simp))
    | @insert b s hbs ih =>
      simp only [Finset.sum_insert hbs]
      exact (hadd (f b) _).trans (add_le_add_right ih _)
  have hmul (r : ℝ) (f : Time → ℝ) :
      eVariationOn (fun t => r * f t) Set.univ ≤
        (‖r‖₊ : ENNReal) * eVariationOn f Set.univ := by
    have h := (lipschitzWith_smul r).lipschitzOnWith.comp_eVariationOn_le
      (g := f) (s := Set.univ) (t := Set.univ) (by simp)
    simpa [Function.comp_def, smul_eq_mul] using h
  intro a
  have hvar :
      eVariationOn (tensorCoefficientPath p hdeg hgrid a) Set.univ ≤
        ∑ b : I, (‖(e.symm (Pi.single b (1 : ℝ))) a‖₊ : ENNReal) *
          eVariationOn (g · b) Set.univ := by
    calc
      _ = eVariationOn
          (fun t => ∑ b : I, (e.symm (Pi.single b (1 : ℝ))) a * g t b)
          Set.univ := by
            congr 1
            funext t
            exact hformula a t
      _ ≤ ∑ b : I,
          eVariationOn (fun t => (e.symm (Pi.single b (1 : ℝ))) a * g t b)
            Set.univ := by
            simpa using hsum Finset.univ
              (fun b t => (e.symm (Pi.single b (1 : ℝ))) a * g t b)
      _ ≤ _ := Finset.sum_le_sum (fun b _ => hmul _ _)
  apply lt_of_le_of_lt hvar
  apply (ENNReal.sum_lt_top).2
  intro b _
  exact ENNReal.mul_lt_top (by simp) (hBV (x b) (hx b))

/-- A finite fixed linear combination of bounded-variation paths has path size at most the
absolute-weighted sum of their path sizes. This controls both the uniform norm and every
time-partition increment sum with the same coefficients. -/
theorem pathSize_weighted_sum_le {ι : Type*} [Fintype ι]
    (c : ι → Path) (w : ι → ℝ)
    (hBV : ∀ i, eVariationOn (c i) Set.univ < ⊤) :
    pathSize (∑ i, w i • c i) ≤ ∑ i, |w i| * pathSize (c i) := by
  classical
  have hnorm : ‖∑ i, w i • c i‖ ≤ ∑ i, |w i| * ‖c i‖ := by
    calc
      ‖∑ i, w i • c i‖ ≤ ∑ i, ‖w i • c i‖ := norm_sum_le _ _
      _ = ∑ i, |w i| * ‖c i‖ := by simp [norm_smul, Real.norm_eq_abs]
  have hadd (f g : Time → ℝ) :
      eVariationOn (fun t => f t + g t) Set.univ ≤
        eVariationOn f Set.univ + eVariationOn g Set.univ := by
    apply iSup_le
    rintro ⟨n, ⟨u, hu, hus⟩⟩
    calc
      (∑ j ∈ Finset.range n,
        edist (f (u (j + 1)) + g (u (j + 1))) (f (u j) + g (u j))) ≤
          (∑ j ∈ Finset.range n, edist (f (u (j + 1))) (f (u j))) +
          (∑ j ∈ Finset.range n, edist (g (u (j + 1))) (g (u j))) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_le_sum (fun j _ => edist_add_add_le _ _ _ _)
      _ ≤ eVariationOn f Set.univ + eVariationOn g Set.univ :=
        add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)
  have hsum (s : Finset ι) (f : ι → Time → ℝ) :
      eVariationOn (fun t => ∑ i ∈ s, f i t) Set.univ ≤
        ∑ i ∈ s, eVariationOn (f i) Set.univ := by
    induction s using Finset.induction_on with
    | empty =>
      simpa using (eVariationOn.constant_on
        (f := fun _ : Time => (0 : ℝ)) (s := Set.univ) (by simp))
    | @insert i s his ih =>
      simp only [Finset.sum_insert his]
      exact (hadd (f i) _).trans (add_le_add_right ih _)
  have hmul (r : ℝ) (f : Time → ℝ) :
      eVariationOn (fun t => r * f t) Set.univ ≤
        (‖r‖₊ : ENNReal) * eVariationOn f Set.univ := by
    have h := (lipschitzWith_smul r).lipschitzOnWith.comp_eVariationOn_le
      (g := f) (s := Set.univ) (t := Set.univ) (by simp)
    simpa [Function.comp_def, smul_eq_mul] using h
  have hvar : eVariationOn (fun t => (∑ i, w i • c i) t) Set.univ ≤
      ∑ i, (‖w i‖₊ : ENNReal) * eVariationOn (c i) Set.univ := by
    calc
      _ ≤ ∑ i, eVariationOn (fun t => w i * c i t) Set.univ := by
        simpa [smul_eq_mul] using hsum Finset.univ (fun i t => w i * c i t)
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hmul (w i) (c i))
  have hfin : (∑ i, (‖w i‖₊ : ENNReal) * eVariationOn (c i) Set.univ) < ⊤ :=
    ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.mul_lt_top (by simp) (hBV i))
  have htv : pathTV (∑ i, w i • c i) ≤ ∑ i, |w i| * pathTV (c i) := by
    have h := ENNReal.toReal_mono (ne_of_lt hfin) hvar
    rw [ENNReal.toReal_sum (fun i _ => ne_of_lt
      (ENNReal.mul_lt_top (by simp) (hBV i)))] at h
    change (eVariationOn (fun t => (∑ i, w i • c i : Path) t) Set.univ).toReal ≤
      ∑ i, |w i| * pathTV (c i)
    simpa [pathTV, ENNReal.toReal_mul, Real.norm_eq_abs] using h
  dsimp [pathSize]
  simp only [Finset.sum_add_distrib, mul_add]
  linarith

/-- Every coefficient of a four-variable polynomial of coordinatewise degree `2(K-1)` is a
fixed weighted sum of its values at one finite tensor grid inside the normalized cube. The
total absolute weight over all coefficients and grid points has an exponential degree bound.

One route uses Lagrange nodes `j/(D+1)` with `D = 2(K-1)`. The coefficient one-norm of the
univariate basis polynomial at node `j` is at most
`2^D * (D+1)^D / (j! * (D-j)!)`. Summing over `j` gives
`4^D * (D+1)^D / D!`; the exponential-series bound controls the factorial ratio. Tensor the
four univariate formulas and compare their total weight with `2^(40K+19)`. This is a
quantitative finite-dimensional representation, independent of any time-indexed path. -/
theorem tensorCoeffs_four_cube_weights {K : ℕ} (hK : 0 < K) :
    ∃ (x : (Fin 4 → Fin (2 * (K - 1) + 1)) → Fin 4 → ℝ)
      (w : (Fin 4 → Fin (2 * (K - 1) + 1)) →
        (Fin 4 → Fin (2 * (K - 1) + 1)) → ℝ),
      (∀ b, x b ∈ normalizedCube 4) ∧
      (∀ (p : MvPolynomial (Fin 4) ℝ),
        (∀ i, p.degreeOf i ≤ 2 * (K - 1)) →
        ∀ a, tensorCoeffs (D := 2 * (K - 1)) p a =
          ∑ b, w a b * MvPolynomial.eval (x b) p) ∧
      (∑ a, ∑ b, |w a b|) ≤ (2 : ℝ) ^ (40 * K + 19) := by
  refine ⟨tensorGridPoint, tensorGridWeight, tensorGridPoint_mem_cube, ?_, ?_⟩
  · intro p hdeg a
    exact tensorGrid_coeff_recovery p hdeg a
  · calc
      (∑ a : Fin 4 → Fin (2 * (K - 1) + 1),
          ∑ b : Fin 4 → Fin (2 * (K - 1) + 1),
            |tensorGridWeight a b|) ≤
          ((2 : ℝ) ^ (4 * (2 * (K - 1)) + 4)) ^ 4 :=
        tensorGrid_weight_oneNorm_le 4 (2 * (K - 1))
      _ = (2 : ℝ) ^ (4 * (4 * (2 * (K - 1)) + 4)) := by
        rw [show 4 * (4 * (2 * (K - 1)) + 4) =
          (4 * (2 * (K - 1)) + 4) * 4 by omega, pow_mul]
      _ ≤ (2 : ℝ) ^ (40 * K + 19) := by
        apply pow_le_pow_right₀ (by norm_num)
        omega

/-- For four coordinates and coordinatewise degree `2(K-1)`, a uniform bound `B` on the
path sizes of all cube evaluations bounds the sum of monomial coefficient path sizes by
`2^(40K+20) B`, provided those evaluation paths have finite variation.

Apply `tensorCoeffs_four_cube_weights` to each coefficient path. The absolute values of its
fixed weights control both the supremum norm and total variation; sum over coefficients and
use the cube path-size bound. The pointwise polynomial coefficient estimate alone does not
permit swapping a supremum over cube points with the sum over time increments.
-/
theorem tensorCoefficientPath_four_size_envelope {K : ℕ} (hK : 0 < K)
    (p : Time → MvPolynomial (Fin 4) ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ t i, (p t).degreeOf i ≤ 2 * (K - 1))
    (hgrid : ∀ a : Fin 4 → Fin (2 * (K - 1) + 1),
      Continuous (fun t => MvPolynomial.eval (fun i => (a i : ℝ)) (p t)))
    (hcont : ∀ x ∈ normalizedCube 4,
      Continuous (fun t => MvPolynomial.eval x (p t)))
    (hBV : ∀ x (hx : x ∈ normalizedCube 4),
      eVariationOn (⟨fun t => MvPolynomial.eval x (p t), hcont x hx⟩ : Path)
        Set.univ < ⊤)
    (hbound : ∀ x (hx : x ∈ normalizedCube 4),
      pathSize (⟨fun t => MvPolynomial.eval x (p t), hcont x hx⟩ : Path) ≤ B) :
    (∑ a, pathSize (tensorCoefficientPath p hdeg hgrid a)) ≤
        (2 : ℝ) ^ (40 * K + 20) * B := by
  classical
  obtain ⟨x, w, hx, hrecover, hw⟩ := tensorCoeffs_four_cube_weights hK
  let c (b : Fin 4 → Fin (2 * (K - 1) + 1)) : Path :=
    ⟨fun t => MvPolynomial.eval (x b) (p t), hcont (x b) (hx b)⟩
  have hcBV (b) : eVariationOn (c b) Set.univ < ⊤ := hBV (x b) (hx b)
  have hcBound (b) : pathSize (c b) ≤ B := hbound (x b) (hx b)
  have hpath (a : Fin 4 → Fin (2 * (K - 1) + 1)) :
      tensorCoefficientPath p hdeg hgrid a = ∑ b, w a b • c b := by
    ext t
    simpa [tensorCoefficientPath, c, smul_eq_mul] using hrecover (p t) (hdeg t) a
  calc
    (∑ a, pathSize (tensorCoefficientPath p hdeg hgrid a)) =
        ∑ a, pathSize (∑ b, w a b • c b) := by simp only [hpath]
    _ ≤ ∑ a, ∑ b, |w a b| * pathSize (c b) :=
      Finset.sum_le_sum (fun a _ => pathSize_weighted_sum_le c (w a) hcBV)
    _ ≤ ∑ a, ∑ b, |w a b| * B := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (hcBound b) (abs_nonneg _)
    _ = (∑ a, ∑ b, |w a b|) * B := by simp [Finset.sum_mul]
    _ ≤ (2 : ℝ) ^ (40 * K + 19) * B :=
      mul_le_mul_of_nonneg_right hw hB
    _ ≤ (2 : ℝ) ^ (40 * K + 20) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      apply pow_le_pow_right₀ (by norm_num)
      omega

/-- A four-variable tensor polynomial family of coordinatewise degree `2(K-1)` has coefficient
paths whose summed path sizes obey a coarse exponential degree envelope, provided every cube
evaluation has bounded variation and path size at most `B`.

The proof should use the Chebyshev coefficient integral as a bounded linear map on the BV path
space; the already established scalar coefficient bound alone does not justify interchanging
variation and a supremum over cube points.

The separate bounded-variation premise is essential: `pathTV` converts extended variation to a
real number, and `ENNReal.toReal ⊤ = 0`, so a `pathSize` bound by itself does not rule out
infinite variation. Apply the Chebyshev coefficient functional to each finite partition first,
then take the supremum over partitions after integrating the pointwise increment bound.
-/
theorem tensorCoefficientPath_four_bv_envelope {K : ℕ} (hK : 0 < K)
    (p : Time → MvPolynomial (Fin 4) ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ t i, (p t).degreeOf i ≤ 2 * (K - 1))
    (hgrid : ∀ a : Fin 4 → Fin (2 * (K - 1) + 1),
      Continuous (fun t => MvPolynomial.eval (fun i => (a i : ℝ)) (p t)))
    (hcont : ∀ x ∈ normalizedCube 4,
      Continuous (fun t => MvPolynomial.eval x (p t)))
    (hBV : ∀ x (hx : x ∈ normalizedCube 4),
      eVariationOn (⟨fun t => MvPolynomial.eval x (p t), hcont x hx⟩ : Path)
        Set.univ < ⊤)
    (hbound : ∀ x (hx : x ∈ normalizedCube 4),
      pathSize (⟨fun t => MvPolynomial.eval x (p t), hcont x hx⟩ : Path) ≤ B) :
    (∀ a, eVariationOn
      (tensorCoefficientPath p hdeg hgrid a) Set.univ < ⊤) ∧
      (∑ a, pathSize (tensorCoefficientPath p hdeg hgrid a)) ≤
        (2 : ℝ) ^ (40 * K + 20) * B := by
  exact ⟨tensorCoefficientPath_bv_of_cube p hdeg hgrid hcont hBV,
    tensorCoefficientPath_four_size_envelope hK p B hB hdeg hgrid hcont hBV hbound⟩

/-- Let [a time-indexed family of four-variable polynomials](hyp:p) have [degree at most 2(K − 1) in each
variable](hyp:hdeg) and [grid evaluations continuous in time](hyp:hgrid).
If [its evaluation at every point of the normalized cube is continuous in
time](hyp:hcont), [of bounded variation](hyp:hBV), and [of path size at
most B](hyp:hbound), where [B is nonnegative](hyp:B,hB), then [the summed
path sizes of its monomial coefficient paths are at most
16 (2(K − 1) + 1)^4 (1 + √2)^(8(K − 1)) B](goal).

The summed path sizes of the monomial coefficient paths of a four-variable polynomial are
bounded by the Chebyshev conversion factor times the uniform path size of its cube evaluations.

For each tensor Chebyshev coefficient, apply the integral variation bound to the cube-valued
evaluation path, obtaining path size at most `16 B`. The recurrence for monomial coefficient
one-norms of Chebyshev polynomials bounds conversion by
`(D+1)^4 (1+sqrt 2)^(4D)` for `D=2(K-1)`. This is the quantitative form needed for the
Jackson bounded-variation coefficient envelope, rather than the coarser finite-grid bound.
-/
theorem tensorCoefficientPath_four_chebyshev_size_envelope {K : ℕ}
    (p : Time → MvPolynomial (Fin 4) ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ t i, (p t).degreeOf i ≤ 2 * (K - 1))
    (hgrid : ∀ a : Fin 4 → Fin (2 * (K - 1) + 1),
      Continuous (fun t => MvPolynomial.eval (fun i => (a i : ℝ)) (p t)))
    (hcont : ∀ x ∈ normalizedCube 4,
      Continuous (fun t => MvPolynomial.eval x (p t)))
    (hBV : ∀ x (hx : x ∈ normalizedCube 4),
      eVariationOn (⟨fun t => MvPolynomial.eval x (p t), hcont x hx⟩ : Path)
        Set.univ < ⊤)
    (hbound : ∀ x (hx : x ∈ normalizedCube 4),
      pathSize (⟨fun t => MvPolynomial.eval x (p t), hcont x hx⟩ : Path) ≤ B) :
    (∑ a, pathSize (tensorCoefficientPath p hdeg hgrid a)) ≤
      (16 : ℝ) * (↑(2 * (K - 1) + 1) : ℝ) ^ 4 *
        (1 + Real.sqrt 2) ^ (4 * (2 * (K - 1))) * B := by
  /- Apply `tensorChebyshevPath_expansion` with `D = 2 * (K - 1)` and obtain bounded
     coefficient paths `c`. At each time, take `tensorCoeffs` of that expansion;
     `tensorChebyshevBasis_coeff_factorization` and `MvPolynomial.coeff_sum` express
     the monomial coefficient path as a fixed weighted sum of the `c k` paths.
     Apply `pathSize_weighted_sum_le`, sum over monomial indices, swap finite sums,
     and use `tensorChebyshevBasis_coeff_oneNorm_le`. The remaining index count is
     `Fintype.card_fun` and `Fintype.card_fin`, giving `(D+1)^4`. -/
  classical
  let D := 2 * (K - 1)
  let I := Fin 4 → Fin (D + 1)
  obtain ⟨c, hc, hcbv, hcsz⟩ :=
    tensorChebyshevPath_expansion (D := D) p B hB hdeg hcont hBV hbound
  let w (a k : I) : ℝ := tensorCoeffs (D := D) (tensorChebyshevBasis D k) a
  have hpath (a : I) :
      tensorCoefficientPath p hdeg hgrid a = ∑ k : I, w a k • c k := by
    ext t
    have ht := congrArg (fun q => tensorCoeffs (D := D) q a) (hc t)
    simp only [tensorChebyshevPolynomial, tensorCoeffs, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_C_mul] at ht
    simpa [tensorCoefficientPath, w, tensorCoeffs, smul_eq_mul, mul_comm] using ht
  have hw (k : I) : (∑ a : I, |w a k|) ≤
      (1 + Real.sqrt 2) ^ (4 * D) :=
    tensorChebyshevBasis_coeff_oneNorm_le D k
  calc
    (∑ a : I, pathSize (tensorCoefficientPath p hdeg hgrid a)) =
        ∑ a : I, pathSize (∑ k : I, w a k • c k) := by simp only [hpath]
    _ ≤ ∑ a : I, ∑ k : I, |w a k| * pathSize (c k) :=
      Finset.sum_le_sum (fun a _ => pathSize_weighted_sum_le c (w a) hcbv)
    _ = ∑ k : I, (∑ a : I, |w a k|) * pathSize (c k) := by
      rw [Finset.sum_comm]
      simp [Finset.sum_mul]
    _ ≤ ∑ k : I, (1 + Real.sqrt 2) ^ (4 * D) * (16 * B) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul (hw k) (hcsz k) (pathSize_nonneg _) (by positivity)
    _ = (16 : ℝ) * (↑(D + 1) : ℝ) ^ 4 *
          (1 + Real.sqrt 2) ^ (4 * D) * B := by
      simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, I]
      push_cast
      ring

end Causalean.Stat.Concentration.BoundedVariation

