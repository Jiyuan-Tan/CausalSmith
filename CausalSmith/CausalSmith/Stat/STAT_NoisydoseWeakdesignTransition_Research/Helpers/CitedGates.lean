module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Basic
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.Packet

/-! Five explicit cited logical gates, and the separate direct Gaussian regression benchmark.
These propositions are inputs to conditional consumers and contain no proof placeholders. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology ContDiff
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- Angular distance on the symmetric unit interval. -/
def jacobiAngularDistance (x y : ℝ) : ℝ := |Real.arccos x - Real.arccos y|
/-- Endpoint-regularized Jacobi weight at the public spectral degree. -/
def jacobiRegularizedWeight (a b : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  (1-x+(m : ℝ)^(-2 : ℝ))^(a+1/2) * (1+x+(m : ℝ)^(-2 : ℝ))^(b+1/2)
/-- A smooth cutoff on the nonnegative half-line, supported between one half and two. -/
def SmoothJacobiFilter (eta : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ eta (Ici 0) ∧ Function.support eta ⊆ Icc (1/2 : ℝ) 2

/-- Petrushev and Xu (2005), Theorem 2.4, equation (2.14), arXiv:math/0508581.
The smooth-filter specialization permits every positive decay exponent. -/
-- @node: lem:filtered-jacobi-localization
def FilteredJacobiLocalization : Sort 0 :=
  ∀ a b : ℝ, -1/2 < a → -1/2 < b → ∀ eta : ℝ → ℝ, SmoothJacobiFilter eta →
  ∀ S : ℝ, 0 < S → ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
  ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
    |filteredJacobiKernel a b eta m x y| ≤ C*m /
      (Real.sqrt (jacobiRegularizedWeight a b m x * jacobiRegularizedWeight a b m y) *
        (1+m*jacobiAngularDistance x y)^S)

/-- Kyriazis, Petrushev and Xu (2008), Theorem 2.2, equation (2.4),
https://people.math.sc.edu/pencho/Publications/kpx-06-28-06-web.pdf.
The constant depends on the fixed local angular radius and decay exponent. -/
-- @node: lem:filtered-jacobi-lipschitz
def FilteredJacobiLipschitz : Sort 0 :=
  ∀ a b : ℝ, -1/2 < a → -1/2 < b → ∀ eta : ℝ → ℝ, SmoothJacobiFilter eta →
  ∀ S cstar : ℝ, 0 < S → 0 < cstar → ∃ C : ℝ, 0 < C ∧
  ∀ m : ℕ, 1 ≤ m → ∀ x ∈ Icc (-1 : ℝ) 1, ∀ xi ∈ Icc (-1 : ℝ) 1,
  ∀ y ∈ Icc (-1 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1,
  jacobiAngularDistance x xi ≤ cstar/m → jacobiAngularDistance z xi ≤ cstar/m →
    |filteredJacobiKernel a b eta m x y - filteredJacobiKernel a b eta m xi y| ≤
      C*(m : ℝ)^2*jacobiAngularDistance x xi /
      (Real.sqrt (jacobiRegularizedWeight a b m y * jacobiRegularizedWeight a b m z) *
        (1+m*jacobiAngularDistance y z)^S)

/-- NIST Digital Library of Mathematical Functions, Table 18.3.1, Jacobi row and caption,
https://dlmf.nist.gov/18.3 (accessed 2026). Orthogonality and the positive squared norm. -/
-- @node: lem:jacobi-norm
def JacobiNormOrthogonality : Sort 0 :=
  ∀ a b : ℝ, -1/2 < a → -1/2 < b → ∀ j : ℕ,
    (∀ R : Polynomial ℝ, R.degree < (j : WithBot ℕ) →
      ∫ z in Icc (-1 : ℝ) 1, jacobiWeight a b z * stdJacobi a b j z * R.eval z = 0) ∧
    0 < jacobiSqNorm a b j ∧
    jacobiSqNorm a b j = (2 : ℝ)^(a+b+1) / (2*j+a+b+1) *
      (Real.Gamma (j+a+1) * Real.Gamma (j+b+1) /
        (Real.Gamma (j+1) * Real.Gamma (j+a+b+1)))

/-- NIST DLMF (accessed 2026), equation 5.11.12, https://dlmf.nist.gov/5.11.E12.
Positive real-axis specialization; the shifted arguments are eventually positive. -/
-- @node: lem:gamma-ratio
def GammaRatioAsymptotic : Sort 0 :=
  ∀ s t : ℝ, Tendsto (fun z : ℝ => Real.Gamma (z+s) / Real.Gamma (z+t) / z^(s-t))
    atTop (𝓝 1)

/-- Fixed power-law design in the separate direct Gaussian-response experiment. -/
def GaiffasDesign (v c xstar delta : ℝ) (nu : ProbabilityMeasure Dose) : Prop :=
  ∃ g : ℝ → ℝ, Measurable g ∧ (∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ g u) ∧
    (nu : Measure Dose).map Subtype.val = (volume.restrict (Icc (0 : ℝ) 1)).withDensity
      (fun u => ENNReal.ofReal (g u)) ∧
    ∀ u ∈ Icc (0 : ℝ) 1, |u-xstar| ≤ delta → g u = c*|u-xstar|^v

/-- Exact balance bandwidth of the separate power-law Gaussian-response regression benchmark. -/
def gaiffasBandwidth (s v c r tau : ℝ) (n : ℕ) : ℝ :=
  (tau^2*(v+1)/(2*c*r^2*n))^(1/(2*s+v+1))
/-- Definition 2's local polynomial approximation class, retaining linear polynomials at s=1. -/
def GaiffasFunctionClass (s v c r M tau xstar : ℝ) (n : ℕ) (f : Dose → ℝ) : Prop :=
  Measurable f ∧ (∀ u, |f u| ≤ M) ∧
  ∀ a : ℝ, 0 < a → a ≤ gaiffasBandwidth s v c r tau n →
    (⨅ p : {p : Polynomial ℝ // p.natDegree ≤ Nat.floor s},
      ⨆ u : {u : Dose // |(u : ℝ)-xstar| ≤ a},
        ENNReal.ofReal |f u.1 - p.1.eval ((u.1 : ℝ)-xstar)|) ≤ ENNReal.ofReal (r*a^s)

/-- Direct regression record formed from an independent design draw and Gaussian response noise. -/
def gaiffasObsLaw (tau : ℝ) (nu : ProbabilityMeasure Dose) (f : Dose → ℝ) : Measure (Dose × ℝ) :=
  ((nu : Measure Dose).prod (gaussianReal 0 ⟨tau^2, sq_nonneg tau⟩)).map
    (fun p => (p.1, f p.1+p.2))
/-- All-estimator pointwise absolute minimax risk in the separate direct regression experiment with the local polynomial approximation class. -/
def gaiffasMinimax (s v c r M tau : ℝ) (xstar : Dose) (nu : ProbabilityMeasure Dose) (n : ℕ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (T : {T : (Fin n → Dose × ℝ) → ℝ // Measurable T})
      (f : {f : Dose → ℝ // GaiffasFunctionClass s v c r M tau xstar n f}) =>
      ∫⁻ data, ENNReal.ofReal |T.1 data - f.1 xstar|
        ∂Measure.pi (fun _ : Fin n => gaiffasObsLaw tau nu f.1))

/-- Gaiffas (2005), Definition 2 and Theorem 1, equations (2.1), (2.4), (2.5),
PDF pages 3–4, https://arxiv.org/pdf/math/0410354v3.
Exact power-law specialization with absolute loss, in a separate direct regression experiment.
No causal-class inclusion or honest-length assertion is carried by this gate. -/
-- @node: lem:gaiffas-direct-benchmark
def GaiffasDirectBenchmark : Sort 0 :=
  ∀ s v c r M tau : ℝ, 0 < s → s ≤ 1 → v ∈ Icc (0 : ℝ) 2 →
  0 < c → 0 < r → 0 < M → 0 < tau →
  ∀ xstar : Dose, 0 < (xstar : ℝ) → (xstar : ℝ) < 1 →
  ∀ delta : ℝ, 0 < delta → delta ≤ min (xstar : ℝ) (1-(xstar : ℝ)) →
  ∀ nu : ProbabilityMeasure Dose, GaiffasDesign v c xstar delta nu →
  ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < C0 ∧ ∃ n0 : ℕ, ∀ n ≥ n0,
    gaiffasBandwidth s v c r tau n ≤ delta ∧
    ENNReal.ofReal (c0*(n : ℝ)^(-s/(2*s+v+1))) ≤ gaiffasMinimax s v c r M tau xstar nu n ∧
    gaiffasMinimax s v c r M tau xstar nu n ≤ ENNReal.ofReal (C0*(n : ℝ)^(-s/(2*s+v+1))) ∧
    ENNReal.ofReal (c0*r*(gaiffasBandwidth s v c r tau n)^s) ≤
      gaiffasMinimax s v c r M tau xstar nu n ∧
    gaiffasMinimax s v c r M tau xstar nu n ≤
      ENNReal.ofReal (C0*r*(gaiffasBandwidth s v c r tau n)^s)
end CausalSmith.Stat.NoisydoseWeakdesignTransition
