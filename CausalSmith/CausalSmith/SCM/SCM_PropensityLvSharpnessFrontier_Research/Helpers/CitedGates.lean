import Causalean.Stat.Concentration.TailBounds.Hoeffding
import Causalean.Stat.Quantile.EmpiricalCDF

/-! # Cited concentration gates -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

/-- Hoeffding's inequality for independent, possibly heterogeneous, `[0,1]`-valued
variables. Aad W. van der Vaart and Jon A. Wellner (1996), *Weak Convergence and
Empirical Processes*, Lemma 2.2.9; DOI 10.1007/978-1-4757-2545-2. -/
-- @node: lem:hoeffding-bounded-mean
def HoeffdingBoundedMean : Sort 0 :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (Omega : Type*) (_ : MeasurableSpace Omega)
    (mu : Measure Omega) (_ : IsProbabilityMeasure mu)
    (Z : Fin m → Omega → ℝ),
    (∀ i, Measurable (Z i)) → iIndepFun Z mu →
    (∀ i, ∀ᵐ ω ∂mu, 0 ≤ Z i ω ∧ Z i ω ≤ 1) → ∀ t : ℝ, 0 < t →
    mu {ω | |∑ i, Z i ω / (m : ℝ) - ∑ i, (∫ ω, Z i ω ∂mu) / (m : ℝ)| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * (m : ℝ) * t ^ 2))

/-- The Dvoretzky--Kiefer--Wolfowitz inequality with Massart's sharp constant.
Aad W. van der Vaart and Jon A. Wellner (1996), *Weak Convergence and Empirical
Processes*, Section 2.14; DOI 10.1007/978-1-4757-2545-2. -/
-- @node: lem:dkw-massart-cdf-band
def DkwMassartCdfBand : Sort 0 :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (Omega : Type) (_ : MeasurableSpace Omega)
    (mu : Measure Omega) (_ : IsProbabilityMeasure mu)
    (X : Fin m → Omega → ℝ) (rho : Measure ℝ)
    (_ : IsProbabilityMeasure rho),
    (∀ i, Measurable (X i)) → iIndepFun X mu →
    (∀ i y, mu {ω | X i ω ≤ y} = rho (Set.Iic y)) → ∀ t : ℝ, 0 < t →
    mu {ω | sSup {r : ℝ | ∃ y : ℝ,
      r = |∑ i, (if X i ω ≤ y then (1 : ℝ) else 0) / (m : ℝ) -
        (rho (Set.Iic y)).toReal|} > t} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * (m : ℝ) * t ^ 2))

end CausalSmith.SCM.PropensityLvSharpnessFrontier
