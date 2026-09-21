module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Basic
public import Causalean.Mathlib.Analysis.Duality.MomentPrior.Duality
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Alternation
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Markov
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-! Finite alternation duality for the rational target `p/(p+a)`. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open scoped BigOperators

/-- A finitely supported signed measure, presented by its nodes and signed weights. -/
structure FiniteMomentDual (L : Nat) (lo hi a c : Real) where
  node : Fin (L + 2) → Real
  node_injective : Function.Injective node
  weight : Fin (L + 2) → Real
  support : ∀ i, node i ∈ Set.Icc lo hi
  totalVariation : (∑ i, |weight i|) = 1
  moments : ∀ j : Nat, j ≤ L → ∑ i, weight i * node i ^ j = 0
  gap : c ≤ ∑ i, weight i * (node i / (node i + a))

-- @node: lem:finite-alternation-duality
/-- Positive constants depending only on overlap yield a normalized finite signed
measure with vanishing moments through degree `L` and a uniform rational gap.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma finite_alternation_duality {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∃ gamma c : Real, 0 < gamma ∧ 0 < c ∧
      ∀ (L : Nat), 2 ≤ L → ∀ B : Real, 0 < B →
        let kappa := (1 - 2 * eps) / eps
        let a := gamma * B / (L : Real) ^ 2
        a / kappa ≤ B ∧ Nonempty (FiniteMomentDual L (a / kappa) B a c) := by
  let kappa := (1 - 2 * eps) / eps
  let D := kappa / ((1 + kappa) * (2 + kappa))
  let gamma := min (kappa / 4) (D * kappa / 32)
  let c := D / 8
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    apply div_pos
    · linarith
    · exact heps
  have hD : 0 < D := by
    dsimp [D]
    exact div_pos hkappa (mul_pos (by linarith) (by linarith))
  have hDlt : D < 1 := by
    dsimp [D]
    apply (div_lt_one (mul_pos (by linarith [hkappa]) (by linarith [hkappa]))).2
    nlinarith [sq_nonneg kappa]
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨gamma, c, hgamma, hc, ?_⟩
  intro L hL B hB
  dsimp only
  let a := gamma * B / (L : Real) ^ 2
  have hLreal : 0 < (L : Real) := by positivity
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hgamma_le : gamma ≤ kappa / 4 := min_le_left _ _
  have hLtwo : (2 : Real) ≤ L := by exact_mod_cast hL
  have hLsq : 4 ≤ (L : Real) ^ 2 := by
    nlinarith
  have hLsqpos : 0 < (L : Real) ^ 2 := lt_of_lt_of_le (by norm_num) hLsq
  have hleft : a / kappa ≤ B := by
    rw [div_le_iff₀ hkappa]
    dsimp [a]
    rw [div_le_iff₀ hLsqpos]
    have : gamma * B ≤ kappa * B := by gcongr <;> linarith
    nlinarith [mul_pos hkappa hB]
  refine ⟨hleft, ?_⟩
  have hapos : 0 < a / kappa := div_pos ha hkappa
  have hleft16 : a / kappa ≤ B / 16 := by
    rw [div_le_iff₀ hkappa]
    dsimp [a]
    rw [div_le_iff₀ hLsqpos]
    have hgamB : gamma * B ≤ (kappa / 4) * B := by gcongr
    nlinarith [mul_pos hkappa hB]
  have hright_strict : a / kappa < B := by linarith
  let f := Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a
  have hpole : -a ∉ Set.Icc (a / kappa) B := by
    intro h
    linarith [h.1, hapos]
  have hf : ContinuousOn f (Set.Icc (a / kappa) B) :=
    Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.continuousOn_rationalTarget hpole
  obtain ⟨A⟩ :=
    Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.exists_alternationDualCertificate
      hright_strict hf L
  let E := Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.bestUniformApproxError
    f (a / kappa) B L
  have hE : c ≤ E := by
    by_contra hnot
    have hElt : E < c := lt_of_not_ge hnot
    let p₁ := a / kappa
    let p₂ := 2 * a / kappa
    have hp₁pos : 0 < p₁ := by dsimp [p₁]; positivity
    have hp₁p₂ : p₁ < p₂ := by
      dsimp [p₁, p₂]
      calc
        a / kappa < 2 * (a / kappa) := by linarith [hapos]
        _ = 2 * a / kappa := by ring
    have hp₂B : p₂ ≤ B := by
      dsimp [p₂, a]
      have hgam : gamma ≤ kappa := hgamma_le.trans (by linarith [hkappa])
      have hmul : 2 * gamma * B ≤ 2 * kappa * B := by gcongr
      field_simp [ne_of_gt hkappa, ne_of_gt hLsqpos]
      nlinarith [mul_pos hkappa hB]
    have hp₁mem : p₁ ∈ Set.Icc (a / kappa) B := ⟨le_rfl, hp₁p₂.le.trans hp₂B⟩
    have hp₂mem : p₂ ∈ Set.Icc (a / kappa) B :=
      ⟨hp₁p₂.le, hp₂B⟩
    have hres (p : Real) (hp : p ∈ Set.Icc (a / kappa) B) :
        |f p - A.approximant.eval p| ≤ E := by
      have herr :
          Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.intervalSupNorm
            (fun x => f x - A.approximant.eval x) (a / kappa) B = E := by
        simpa [Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.uniformApproxError,
          E] using A.approximant_best
      have hu := (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.intervalSupNorm_le_iff
        (hf.sub A.approximant.continuous.continuousOn) hright_strict.le).mp
        (herr.le) p hp
      exact hu
    have hf₁ : f p₁ = 1 / (1 + kappa) := by
      dsimp [f, p₁, Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget]
      field_simp [ne_of_gt ha, ne_of_gt hkappa] <;> ring
    have hf₂ : f p₂ = 2 / (2 + kappa) := by
      dsimp [f, p₂, Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget]
      field_simp [ne_of_gt ha, ne_of_gt hkappa] <;> ring
    have hfdiff : f p₂ - f p₁ = D := by
      rw [hf₁, hf₂]
      dsimp [D]
      field_simp
      ring
    have hQdiff : D - 2 * E ≤ A.approximant.eval p₂ - A.approximant.eval p₁ := by
      have h1 := abs_le.mp (hres p₁ hp₁mem)
      have h2 := abs_le.mp (hres p₂ hp₂mem)
      linarith [hfdiff]
    obtain ⟨z, hz, hzderiv⟩ := exists_hasDerivAt_eq_slope
      (fun x => A.approximant.eval x) (fun x => A.approximant.derivative.eval x)
      hp₁p₂ A.approximant.continuous.continuousOn
      (fun x _ => A.approximant.hasDerivAt x)
    have hzmem : z ∈ Set.Icc (a / kappa) B :=
      ⟨hp₁mem.1.trans hz.1.le, hz.2.le.trans hp₂B⟩
    have hQnorm :
        Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.intervalSupNorm
          (fun x => A.approximant.eval x) (a / kappa) B ≤ 1 + E := by
      apply (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.intervalSupNorm_le_iff
        A.approximant.continuous.continuousOn hright_strict.le).2
      intro x hx
      have hr := abs_le.mp (hres x hx)
      have hfx0 : 0 ≤ f x := by
        dsimp [f, Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget]
        exact div_nonneg (hp₁pos.le.trans hx.1) (by linarith [ha, hp₁pos, hx.1])
      have hfx1 : f x ≤ 1 := by
        dsimp [f, Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget]
        apply (div_le_one (by linarith [ha, hp₁pos, hx.1])).2
        linarith [ha]
      rw [abs_le]
      constructor <;> linarith
    have hmarkov :=
      Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.markov_derivative_Icc
        A.approximant hright_strict L A.approximant_degree
    have hzupper :=
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.intervalSupNorm_le_iff
        A.approximant.derivative.continuous.continuousOn hright_strict.le).mp
        hmarkov z hzmem
    have hE0 : 0 ≤ E := by
      exact Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.bestUniformApproxError_nonneg
        hright_strict hf L
    have hEone : E < 1 := hElt.trans (by dsimp [c]; linarith [hDlt])
    have hden : 0 < B - a / kappa := sub_pos.mpr hright_strict
    have hslope :
        (D - 2 * E) / (p₂ - p₁) ≤ |A.approximant.derivative.eval z| := by
      rw [hzderiv]
      rw [abs_of_nonneg]
      · exact div_le_div_of_nonneg_right hQdiff (sub_nonneg.mpr hp₁p₂.le)
      · apply div_nonneg
        · dsimp [c] at hElt
          nlinarith
        · linarith
    have hgamma_le' : gamma ≤ D * kappa / 32 := min_le_right _ _
    have hhalfden : B / 2 ≤ B - a / kappa := by
      linarith [hleft16]
    have hupper : |A.approximant.derivative.eval z| ≤
        (2 * (L : Real) ^ 2 / (B - a / kappa)) * (1 + E) :=
      hzupper.trans (mul_le_mul_of_nonneg_left hQnorm (by positivity))
    dsimp [p₁, p₂, a] at hslope hupper hhalfden
    have hupper' : |A.approximant.derivative.eval z| ≤
        8 * (L : Real) ^ 2 / B := by
      have hfac : 0 ≤ 2 * (L : Real) ^ 2 := by positivity
      have hdiv : 2 * (L : Real) ^ 2 / (B - a / kappa) ≤
          2 * (L : Real) ^ 2 / (B / 2) :=
        div_le_div_of_nonneg_left hfac (by positivity) hhalfden
      calc
        |A.approximant.derivative.eval z|
            ≤ (2 * (L : Real) ^ 2 / (B - a / kappa)) * (1 + E) := hupper
        _ ≤ (2 * (L : Real) ^ 2 / (B / 2)) * (1 + E) :=
          mul_le_mul_of_nonneg_right hdiv (by linarith)
        _ ≤ (2 * (L : Real) ^ 2 / (B / 2)) * 2 := by
          apply mul_le_mul_of_nonneg_left (by linarith [hEone])
          positivity
        _ = 8 * (L : Real) ^ 2 / B := by
          field_simp [ne_of_gt hB]
          ring
    have hkapne : kappa ≠ 0 := ne_of_gt hkappa
    have hgamne : gamma ≠ 0 := ne_of_gt hgamma
    have hBne : B ≠ 0 := ne_of_gt hB
    have hLne : (L : Real) ^ 2 ≠ 0 := ne_of_gt hLsqpos
    field_simp [hkapne, hgamne, hBne, hLne] at hslope
    have hprod : gamma * B * |A.approximant.derivative.eval z| ≤
        8 * gamma * (L : Real) ^ 2 := by
      calc
        gamma * B * |A.approximant.derivative.eval z|
            ≤ gamma * B * (8 * (L : Real) ^ 2 / B) := by gcongr
        _ = 8 * gamma * (L : Real) ^ 2 := by field_simp [hBne]
    dsimp [c] at hElt
    nlinarith [mul_pos hLsqpos hkappa]
  let sign : Real := if 0 ≤ ∑ i, A.weights i * f (A.nodes i) then 1 else -1
  refine ⟨{
    node := A.nodes
    node_injective := A.nodes_strictMono.injective
    weight := fun i => sign * A.weights i
    support := A.nodes_mem
    totalVariation := ?_
    moments := ?_
    gap := ?_ }⟩
  · simp only [abs_mul, Finset.mul_sum]
    have hsignabs : |sign| = 1 := by
      dsimp [sign]
      split <;> simp
    simpa [hsignabs] using A.weights_normalized
  · intro j hj
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, A.moments_zero j hj, mul_zero]
  · have htarget :
        |∑ i, A.weights i * f (A.nodes i)| = E := by
      rw [A.target_eq]
      rcases A.orientation_eq with h | h <;> rw [h] <;>
        simp [E, abs_of_nonneg
          (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.bestUniformApproxError_nonneg
            hright_strict hf L)]
    change c ≤ ∑ i, sign * A.weights i * (A.nodes i / (A.nodes i + a))
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    change c ≤ sign * ∑ i, A.weights i * f (A.nodes i)
    rw [show sign * ∑ i, A.weights i * f (A.nodes i) =
        |∑ i, A.weights i * f (A.nodes i)| by
      simp only [sign]
      split_ifs with h
      · simpa [abs_of_nonneg h]
      · have : ∑ i, A.weights i * f (A.nodes i) ≤ 0 := le_of_not_ge h
        simpa [abs_of_nonpos this]]
    simpa [htarget] using hE

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
