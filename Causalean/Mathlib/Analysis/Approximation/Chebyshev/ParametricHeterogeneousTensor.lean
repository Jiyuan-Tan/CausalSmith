module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensorExtraction
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensorInterpolation
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Parametric heterogeneous tensor Jackson polynomials

This module constructs a canonical finite polynomial from a jointly measurable, bounded cube
target and proves its convolution, coefficient, support, and finite-lift measurability APIs.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensor

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- [A coordinate-specific order map](hyp:d), [a parameter-indexed target](hyp:g), and [a parameter value](hyp:ω) determine [the canonical heterogeneous Jackson polynomial](goal).
[The polynomial](step:1) is the fixed tensor-grid interpolation polynomial built from the values, at the coordinatewise arccosines of the grid points, of the heterogeneous Jackson convolution of the target at that parameter value; it is an explicit formula, not an existentially chosen witness. -/
def polynomial (d : ι → ℕ) (g : Ω → (ι → ℝ) → ℝ) (ω : Ω) :
    MvPolynomial ι ℝ :=
  interpolate d (fun b => convolution d (g ω)
    (fun i => Real.arccos (gridPoint d b i)))

/-- For [a coordinate-specific positive order map](hyp:d,hd), [a jointly measurable
target](hyp:g,hg), [a real bound B](hyp:B) such that [the target is at most B in absolute value on
the cube for every parameter](hyp:hB), [a parameter value](hyp:ω), and [a phase vector](hyp:x),
[evaluating the canonical polynomial at the coordinatewise cosines of the phase vector gives the
heterogeneous Jackson convolution of the target at that parameter and phase](goal). -/
theorem eval_cosPoint_polynomial (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (g : Ω → (ι → ℝ) → ℝ)
    (hg : Measurable (fun z : Ω × (ι → ℝ) => g z.1 z.2))
    (B : ℝ) (hB : ∀ ω x, x ∈ cube → |g ω x| ≤ B)
    (ω : Ω) (x : ι → ℝ) :
    MvPolynomial.eval (cosPoint x) (polynomial d g ω) =
      convolution d (g ω) x := by
  classical
  have hf : Measurable (g ω) := by
    exact hg.comp (measurable_const.prodMk measurable_id)
  obtain ⟨p, hp, hbound⟩ := convolution_exists_polynomial d hd (g ω) hf B (hB ω)
  have hdegree : ∀ i, p.degreeOf i ≤ interpolationDegree d := by
    intro i
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro γ hγ
    calc
      γ i ≤ 2 * (d i - 1) := hbound γ hγ i
      _ ≤ interpolationDegree d := by
        simpa only [interpolationDegree] using
          (Finset.single_le_sum (s := Finset.univ) (f := fun j => 2 * (d j - 1))
            (fun j hj => Nat.zero_le _) (Finset.mem_univ i))
  have hgrid (b : GridIndex d) :
      cosPoint (fun i => Real.arccos (gridPoint d b i)) = gridPoint d b := by
    funext i
    have hbi : (b i : ℝ) ≤ interpolationDegree d := by
      exact_mod_cast Nat.le_of_lt_succ (b i).isLt
    have hlo : -1 ≤ gridPoint d b i := by
      dsimp [gridPoint, Causalean.Mathlib.Analysis.Approximation.Chebyshev.equispacedLagrangeNode]
      have hn : (0 : ℝ) ≤ (b i : ℝ) / (interpolationDegree d + 1) := by positivity
      linarith
    have hhi : gridPoint d b i ≤ 1 := by
      dsimp [gridPoint, Causalean.Mathlib.Analysis.Approximation.Chebyshev.equispacedLagrangeNode]
      rw [div_le_one (by positivity : (0 : ℝ) < interpolationDegree d + 1)]
      linarith
    exact Real.cos_arccos hlo hhi
  have hpoly : polynomial d g ω =
      interpolate d (fun b => MvPolynomial.eval (gridPoint d b) p) := by
    change interpolate d (fun b => convolution d (g ω)
      (fun i => Real.arccos (gridPoint d b i))) = _
    congr 1
    funext b
    calc
      convolution d (g ω) (fun i => Real.arccos (gridPoint d b i)) =
          MvPolynomial.eval (cosPoint (fun i => Real.arccos (gridPoint d b i))) p :=
        (hp _).symm
      _ = MvPolynomial.eval (gridPoint d b) p := by rw [hgrid]
  rw [hpoly, interpolate_eval d p hdegree, hp]

/-- For [a coordinate-specific positive order map](hyp:d,hd), [a jointly measurable
target](hyp:g,hg), [a real bound B](hyp:B) such that [the target is at most B in absolute value on
the cube for every parameter](hyp:hB), [a parameter value](hyp:ω), and [a point](hyp:θ) [of the
cube](hyp:hθ), [evaluating the canonical polynomial at that point gives the heterogeneous Jackson
convolution at the phase vector of coordinatewise arccosines of the point](goal). -/
theorem eval_polynomial (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (g : Ω → (ι → ℝ) → ℝ)
    (hg : Measurable (fun z : Ω × (ι → ℝ) => g z.1 z.2))
    (B : ℝ) (hB : ∀ ω x, x ∈ cube → |g ω x| ≤ B)
    (ω : Ω) (θ : ι → ℝ) (hθ : θ ∈ cube) :
    MvPolynomial.eval θ (polynomial d g ω) =
      convolution d (g ω) (fun i => Real.arccos (θ i)) := by
  have hcos : cosPoint (fun i => Real.arccos (θ i)) = θ := by
    funext i
    exact Real.cos_arccos (hθ i).1 (hθ i).2
  calc
    MvPolynomial.eval θ (polynomial d g ω) =
        MvPolynomial.eval (cosPoint (fun i => Real.arccos (θ i)))
          (polynomial d g ω) := by rw [hcos]
    _ = _ := eval_cosPoint_polynomial d hd g hg B hB ω _

/-- [A coordinate-specific order map](hyp:d), [a parameter-indexed target](hyp:g), [a parameter value](hyp:ω), and [a tensor coefficient index](hyp:a) imply that [the canonical coefficient is its explicit finite weighted convolution sum](goal). -/
theorem coeff_polynomial (d : ι → ℕ) (g : Ω → (ι → ℝ) → ℝ)
    (ω : Ω) (a : GridIndex d) :
    MvPolynomial.coeff (exponent d a) (polynomial d g ω) =
      ∑ b : GridIndex d, gridWeight d a b *
        convolution d (g ω) (fun i => Real.arccos (gridPoint d b i)) := by
  exact coeff_interpolate d _ a

/-- [A coordinate-specific order map](hyp:d), [a parameter-indexed target](hyp:g), [its joint measurability](hyp:hg), and [a monomial exponent](hyp:γ) imply that [the corresponding canonical-polynomial coefficient is measurable in the parameter](goal). -/
@[fun_prop] theorem measurable_coeff_polynomial (d : ι → ℕ)
    (g : Ω → (ι → ℝ) → ℝ)
    (hg : Measurable (fun z : Ω × (ι → ℝ) => g z.1 z.2))
    (γ : ι →₀ ℕ) :
    Measurable (fun ω => MvPolynomial.coeff γ (polynomial d g ω)) := by
  classical
  simp only [polynomial, interpolate, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  apply Finset.measurable_sum
  intro a _
  split_ifs
  · apply Finset.measurable_sum
    intro b _
    exact measurable_const.mul (measurable_convolution d g hg _)
  · exact measurable_const

/-- For [a coordinate-specific positive order map](hyp:d,hd), [a jointly measurable
target](hyp:g,hg), [a real bound B](hyp:B) such that [the target is at most B in absolute value on
the cube for every parameter](hyp:hB), [a parameter value](hyp:ω), [a monomial exponent](hyp:γ)
[appearing in the canonical polynomial](hyp:hγ), and [a selected coordinate](hyp:i), [the exponent
in that coordinate is at most twice (that coordinate's order minus one)](goal). -/
theorem support_polynomial (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (g : Ω → (ι → ℝ) → ℝ)
    (hg : Measurable (fun z : Ω × (ι → ℝ) => g z.1 z.2))
    (B : ℝ) (hB : ∀ ω x, x ∈ cube → |g ω x| ≤ B)
    (ω : Ω) (γ : ι →₀ ℕ) (hγ : γ ∈ (polynomial d g ω).support) (i : ι) :
    γ i ≤ 2 * (d i - 1) := by
  classical
  have hf : Measurable (g ω) := by
    exact hg.comp (measurable_const.prodMk measurable_id)
  obtain ⟨p, hp, hbound⟩ := convolution_exists_polynomial d hd (g ω) hf B (hB ω)
  have hdegree : ∀ j, p.degreeOf j ≤ interpolationDegree d := by
    intro j
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro δ hδ
    calc
      δ j ≤ 2 * (d j - 1) := hbound δ hδ j
      _ ≤ interpolationDegree d := by
        simpa only [interpolationDegree] using
          (Finset.single_le_sum (s := Finset.univ) (f := fun k => 2 * (d k - 1))
            (fun k hk => Nat.zero_le _) (Finset.mem_univ j))
  have hgrid (b : GridIndex d) :
      cosPoint (fun j => Real.arccos (gridPoint d b j)) = gridPoint d b := by
    funext j
    have hb : (b j : ℝ) ≤ interpolationDegree d := by
      exact_mod_cast Nat.le_of_lt_succ (b j).isLt
    have hlo : -1 ≤ gridPoint d b j := by
      dsimp [gridPoint, Causalean.Mathlib.Analysis.Approximation.Chebyshev.equispacedLagrangeNode]
      have hn : (0 : ℝ) ≤ (b j : ℝ) / (interpolationDegree d + 1) := by positivity
      linarith
    have hhi : gridPoint d b j ≤ 1 := by
      dsimp [gridPoint, Causalean.Mathlib.Analysis.Approximation.Chebyshev.equispacedLagrangeNode]
      rw [div_le_one (by positivity : (0 : ℝ) < interpolationDegree d + 1)]
      linarith
    exact Real.cos_arccos hlo hhi
  have hpoly : polynomial d g ω =
      interpolate d (fun b => MvPolynomial.eval (gridPoint d b) p) := by
    change interpolate d (fun b => convolution d (g ω)
      (fun j => Real.arccos (gridPoint d b j))) = _
    congr 1
    funext b
    calc
      convolution d (g ω) (fun j => Real.arccos (gridPoint d b j)) =
          MvPolynomial.eval (cosPoint (fun j => Real.arccos (gridPoint d b j))) p :=
        (hp _).symm
      _ = MvPolynomial.eval (gridPoint d b) p := by rw [hgrid]
  have heq : polynomial d g ω = p := by
    apply MvPolynomial.funext
    intro x
    rw [hpoly, interpolate_eval d p hdegree]
  rw [heq] at hγ
  exact hbound γ hγ i

/-- [A coordinate-specific order map](hyp:d), [a parameter-indexed target](hyp:g), [its joint measurability](hyp:hg), [a finite monomial set](hyp:S), [parameter-dependent weights](hyp:w), and [their measurability on that set](hyp:hw) imply that [the finite weighted canonical-coefficient sum is measurable](goal). -/
theorem measurable_coeff_sum (d : ι → ℕ)
    (g : Ω → (ι → ℝ) → ℝ)
    (hg : Measurable (fun z : Ω × (ι → ℝ) => g z.1 z.2))
    (S : Finset (ι →₀ ℕ)) (w : (ι →₀ ℕ) → Ω → ℝ)
    (hw : ∀ γ ∈ S, Measurable (w γ)) :
    Measurable (fun ω => ∑ γ ∈ S,
      MvPolynomial.coeff γ (polynomial d g ω) * w γ ω) := by
  classical
  apply Finset.measurable_sum
  intro γ hγ
  exact (measurable_coeff_polynomial d g hg γ).mul (hw γ hγ)

/-- [A coordinate-specific order map](hyp:d), [a parameter-indexed target](hyp:g), [its joint measurability](hyp:hg), [a parameter-dependent evaluation point](hyp:x), and [its measurability](hyp:hx) imply that [canonical-polynomial evaluation is measurable in the parameter](goal). -/
@[fun_prop] theorem measurable_eval_polynomial (d : ι → ℕ)
    (g : Ω → (ι → ℝ) → ℝ)
    (hg : Measurable (fun z : Ω × (ι → ℝ) => g z.1 z.2))
    (x : Ω → ι → ℝ) (hx : Measurable x) :
    Measurable (fun ω => MvPolynomial.eval (x ω) (polynomial d g ω)) := by
  classical
  simp only [polynomial, interpolate, MvPolynomial.eval_sum,
    MvPolynomial.eval_monomial]
  apply Finset.measurable_sum
  intro a _
  have hc : Measurable (fun ω : Ω =>
      ∑ b : GridIndex d, gridWeight d a b *
        convolution d (g ω) (fun i => Real.arccos (gridPoint d b i))) := by
    apply Finset.measurable_sum
    intro b _
    exact measurable_const.mul (measurable_convolution d g hg _)
  have hm : Measurable (fun ω : Ω =>
      (exponent d a).prod fun i n => x ω i ^ n) := by
    simpa only [MvPolynomial.eval_monomial, one_mul, Function.comp_def] using
      ((MvPolynomial.continuous_eval
        (MvPolynomial.monomial (exponent d a) (1 : ℝ))).measurable.comp hx)
  exact hc.mul hm

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensor
