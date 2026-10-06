module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Basic
public import Causalean.Mathlib.Analysis.RealInterpolation
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Moments.Variance

/-! # Disclosed cited logical gates

Cited facts are recorded as Sort-0 propositions. Torus Parseval and the two exact
interpolation facts have proved witnesses; remaining cited facts are explicit consumer
inputs. Definitions fix the normalized K norm and the actual published HT benchmark.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Algebra Submodule
open scoped ENNReal BigOperators Topology ComplexConjugate
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Unit-torus coordinates represent period-two coordinates by y=2u. -/
abbrev Torus (r : ℕ) := UnitAddTorus (Fin r)
  -- @realizes Torus(period-two torus via y=2u)
/-- Normalized Haar probability on the period-two torus. -/
abbrev torusMeasure (r : ℕ) : Measure (Torus r) :=
  Measure.pi (fun _ => AddCircle.haarAddCircle)
/-- The explicit torus measure has total mass one. -/
instance torusProbability (r : ℕ) : IsProbabilityMeasure (torusMeasure r) := inferInstance
/-- Increasing finite integer frequency boxes. -/
def frequencyBox (r J : ℕ) : Finset (Fin r → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(J : ℤ)) (J : ℤ))
/-- Fourier characters in L² for the explicitly chosen normalized torus measure. -/
def torusCharacterLp {r : ℕ} (k : Fin r → ℤ) : Lp ℂ 2 (torusMeasure r) :=
  (UnitAddTorus.mFourier k).toLp 2 (torusMeasure r) ℂ

-- @node: lem:torus-parseval
/-- Complete orthonormal Fourier characters, Parseval, and L² box convergence.
Citation: Nikhil Bansal and Haotian Jiang (2024), §2.2, the Parseval display after the
Fourier-series formula; arXiv:2408.06475v1. Classical Fourier theory as recalled there.
Source checked separately; no pointwise convergence assertion is imported. -/
def TorusParseval : Sort 0 :=
  ∀ r : ℕ, 0 < r → ∀ f : Lp ℂ 2 (torusMeasure r),
    Orthonormal ℂ (torusCharacterLp (r := r)) ∧
    (⊤ : Submodule ℂ (Lp ℂ 2 (torusMeasure r))) ≤
      (Submodule.span ℂ (range (torusCharacterLp (r := r)))).topologicalClosure ∧
    HasSum (fun h : Fin r → ℤ => ‖UnitAddTorus.mFourierCoeff f h‖ ^ 2)
      (∫ t, ‖f t‖ ^ 2 ∂torusMeasure r) ∧
    Tendsto (fun J : ℕ => ‖f - ∑ h ∈ frequencyBox r J,
      UnitAddTorus.mFourierCoeff f h • torusCharacterLp h‖) atTop (𝓝 0)

private lemma frequencyBox_monotone (r : ℕ) : Monotone (frequencyBox r) := by
  intro J K hJK k hk
  simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc] at hk ⊢
  intro i
  constructor
  · exact le_trans (neg_le_neg (Int.ofNat_le.2 hJK)) (hk i).1
  · exact le_trans (hk i).2 (Int.ofNat_le.2 hJK)

private lemma mem_frequencyBox (r : ℕ) (k : Fin r → ℤ) :
    ∃ J, k ∈ frequencyBox r J := by
  let J := Finset.univ.sup fun i : Fin r => (k i).natAbs
  refine ⟨J, ?_⟩
  simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le]
  intro i
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Finset.le_sup (s := Finset.univ) (f := fun i : Fin r => (k i).natAbs)
    (Finset.mem_univ i)

private lemma frequencyBox_tendsto (r : ℕ) :
    Tendsto (frequencyBox r) atTop atTop :=
  (frequencyBox_monotone r).tendsto_atTop_finset (mem_frequencyBox r)

private lemma torusCharacter_orthonormal (r : ℕ) :
    Orthonormal ℂ (torusCharacterLp (r := r)) := by
  rw [orthonormal_iff_ite]
  intro m n
  simp only [torusCharacterLp, ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg,
    ← UnitAddTorus.mFourier_add]
  split_ifs with h
  · simpa only [h, add_neg_cancel, UnitAddTorus.mFourier_zero, probReal_univ, one_smul] using!
      integral_const (α := Torus r) (μ := torusMeasure r) (1 : ℂ)
  rw [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    MeasureTheory.integral_fintype_prod_eq_prod]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa only [eq_false_intro hi, if_false, ContinuousMap.inner_toLp, ← fourier_neg,
    ← fourier_add] using!
    (orthonormal_iff_ite.mp (@orthonormal_fourier (1 : ℝ) (by infer_instance))) (m i) (n i)

private lemma torusCharacter_dense (r : ℕ) :
    (Submodule.span ℂ (range (torusCharacterLp (r := r)))).topologicalClosure = ⊤ := by
  change (Submodule.span ℂ (range (fun x =>
    (ContinuousMap.toLp (2 : ℝ≥0∞) (torusMeasure r) ℂ)
      (UnitAddTorus.mFourier x)))).topologicalClosure = ⊤
  simpa only [map_span, ContinuousLinearMap.coe_coe, ← range_comp, Function.comp_def] using
    (ContinuousMap.toLp_denseRange ℂ (torusMeasure r) ℂ (by simp)).topologicalClosure_map_submodule
      (UnitAddTorus.span_mFourier_closure_eq_top (d := Fin r))

private def torusFourierBasis (r : ℕ) :
    HilbertBasis (Fin r → ℤ) ℂ (Lp ℂ 2 (torusMeasure r)) :=
  HilbertBasis.mk (torusCharacter_orthonormal r) (torusCharacter_dense r).ge

@[simp] private lemma coe_torusFourierBasis (r : ℕ) :
    ⇑(torusFourierBasis r) = torusCharacterLp :=
  HilbertBasis.coe_mk _ _

private lemma torusFourierBasis_repr {r : ℕ} (f : Lp ℂ 2 (torusMeasure r))
    (i : Fin r → ℤ) :
    (torusFourierBasis r).repr f i = UnitAddTorus.mFourierCoeff f i := by
  trans ∫ t, conj (torusCharacterLp i t) * f t ∂torusMeasure r
  · rw [HilbertBasis.repr_apply_apply, MeasureTheory.L2.inner_def, coe_torusFourierBasis]
    simp only [RCLike.inner_apply, mul_comm]
  · apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ)
      (torusMeasure r) (UnitAddTorus.mFourier i)] with t ht
    simp only [torusCharacterLp]
    rw [ht, ← UnitAddTorus.mFourier_neg, smul_eq_mul]

private lemma hasSum_torusFourier_series {r : ℕ} (f : Lp ℂ 2 (torusMeasure r)) :
    HasSum (fun i => UnitAddTorus.mFourierCoeff f i • torusCharacterLp i) f := by
  simpa [← coe_torusFourierBasis, torusFourierBasis_repr] using
    (torusFourierBasis r).hasSum_repr f

private lemma hasSum_sq_torusFourierCoeff {r : ℕ} (f : Lp ℂ 2 (torusMeasure r)) :
    HasSum (fun i => ‖UnitAddTorus.mFourierCoeff f i‖ ^ 2)
      (∫ t, ‖f t‖ ^ 2 ∂torusMeasure r) := by
  simp_rw [← torusFourierBasis_repr]
  have H₁ : HasSum (fun i => ‖(torusFourierBasis r).repr f i‖ ^ 2)
      (‖(torusFourierBasis r).repr f‖ ^ 2) := by
    apply_mod_cast lp.hasSum_norm ?_ ((torusFourierBasis r).repr f)
    simp
  have H₂ : ‖(torusFourierBasis r).repr f‖ ^ 2 = ‖f‖ ^ 2 := by simp
  have H₃ := congr_arg RCLike.re
    (@MeasureTheory.L2.inner_def (Torus r) ℂ ℂ _ _ _ _ _ f f)
  rw [← integral_re] at H₃
  · simp only [← norm_sq_eq_re_inner] at H₃
    rwa [H₂, H₃] at H₁
  · exact MeasureTheory.L2.integrable_inner f f

/-- The cited torus Parseval gate follows from Mathlib's Fourier basis and cofinal finite boxes. This uses [the stated conclusion](goal). -/
theorem torusParseval : TorusParseval := by
  intro r _ f
  refine ⟨torusCharacter_orthonormal r, (torusCharacter_dense r).ge,
    hasSum_sq_torusFourierCoeff f, ?_⟩
  have hsum : Tendsto
      (fun J : ℕ => ∑ h ∈ frequencyBox r J,
        UnitAddTorus.mFourierCoeff f h • torusCharacterLp h)
      atTop (𝓝 f) := by
    exact (hasSum_torusFourier_series f).comp (frequencyBox_tendsto r)
  have hsub := (tendsto_const_nhds (x := f)).sub hsum
  exact tendsto_zero_iff_norm_tendsto_zero.mp (by simpa using hsub)

/-- Normalized quadratic real-interpolation norm squared. -/
def kNormSq {V : Type*} [AddCommGroup V] (n0 n1 : V → ℝ≥0∞)
    (θ : ℝ) (v : V) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.sin (Real.pi * θ) / Real.pi) *
    ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ (-1 - 2 * θ)) *
      ⨅ (v0 : V) (v1 : V) (_ : v = v0 + v1),
        n0 v0 ^ 2 + ENNReal.ofReal (ρ ^ 2) * n1 v1 ^ 2
/-- An endpoint norm on the ambient space, infinite outside the embedded Banach space. -/
def embeddedNorm {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (i : E →L[ℝ] V) (v : V) : ℝ≥0∞ :=
  ⨅ (e : E) (_ : i e = v), ENNReal.ofReal ‖e‖

-- @node: lem:exact-interpolation-operators
/-- Exact exponent θ for common linear operators between compatible Banach pairs,
with the normalized quadratic K norm. Completeness is required at every endpoint.
Citation: S. N. Chandler-Wilde, D. P. Hewett, A. Moiola (2015), Theorem 2.2(i),
normalization (8)–(9), arXiv:1404.3599v4; that item credits McLean (2000), Theorem B.2.
Compatible pairs may be embedded in their Banach sum spaces, as in the source §2. -/
def ExactInterpolationOperators : Sort 0 :=
  ∀ (E0 E1 G0 G1 V W : Type)
    [NormedAddCommGroup E0] [NormedSpace ℝ E0] [CompleteSpace E0]
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [CompleteSpace E1]
    [NormedAddCommGroup G0] [NormedSpace ℝ G0] [CompleteSpace G0]
    [NormedAddCommGroup G1] [NormedSpace ℝ G1] [CompleteSpace G1]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (i0 : E0 →L[ℝ] V) (i1 : E1 →L[ℝ] V)
    (j0 : G0 →L[ℝ] W) (j1 : G1 →L[ℝ] W),
    Function.Injective i0 → Function.Injective i1 →
    Function.Injective j0 → Function.Injective j1 →
    ∀ (D : V →ₗ[ℝ] W) (A0 A1 : ℝ≥0∞), A0 < ⊤ → A1 < ⊤ →
    (∀ e, embeddedNorm j0 (D (i0 e)) ≤ A0 * ENNReal.ofReal ‖e‖) →
    (∀ e, embeddedNorm j1 (D (i1 e)) ≤ A1 * ENNReal.ofReal ‖e‖) →
    ∀ θ ∈ Ioo (0 : ℝ) 1, ∀ v,
      (∃ e0 e1, v = i0 e0 + i1 e1) →
      kNormSq (embeddedNorm i0) (embeddedNorm i1) θ v < ⊤ →
      kNormSq (embeddedNorm j0) (embeddedNorm j1) θ (D v) ≤
        (ENNReal.rpow A0 (1 - θ) * ENNReal.rpow A1 θ) ^ 2 *
          kNormSq (embeddedNorm i0) (embeddedNorm i1) θ v

/-- The exact operator interpolation proposition follows from the generic normalized theorem.](goal) This uses [the stated conclusion](goal). -/
-- @node: exactInterpolationOperators
theorem exactInterpolationOperators : ExactInterpolationOperators := by
  unfold ExactInterpolationOperators
  exact Causalean.Mathlib.Analysis.RealInterpolation.exact_interpolation_operators

/-- [ Weighted L² norm on measurable functions modulo null sets. -/
def wNorm {S : Type} [MeasurableSpace S] (w : S → ℝ≥0∞) (μ : Measure S)
    (f : S →ₘ[μ] ℂ) : ℝ≥0∞ :=
  ENNReal.rpow (∫⁻ x, w x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) (1 / 2)

-- @node: lem:weighted-ltwo-interpolation
/-- Weighted L² real interpolation with exactly equal normalized norms.
Infinite values encode membership equivalently as well as the equality of finite norms.
Citation: S. N. Chandler-Wilde, D. P. Hewett, A. Moiola (2015), Theorem 3.1,
arXiv:1404.3599v4, measurable positive finite weights on an arbitrary measure space.
The source includes both Lebesgue and counting measures and credits McLean B.4 for an
intermediate pointwise minimization; the theorem itself is proved by these authors. -/
def WeightedL2Interpolation : Sort 0 :=
  ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) (w0 w1 : S → ℝ≥0∞),
    Measurable w0 → Measurable w1 →
    (∀ᵐ x ∂μ, 0 < w0 x ∧ w0 x < ⊤ ∧ 0 < w1 x ∧ w1 x < ⊤) →
    ∀ θ ∈ Ioo (0 : ℝ) 1, ∀ f : S →ₘ[μ] ℂ,
    (∃ f0 f1 : S →ₘ[μ] ℂ, f = f0 + f1 ∧ wNorm w0 μ f0 < ⊤ ∧ wNorm w1 μ f1 < ⊤) →
      kNormSq (wNorm w0 μ) (wNorm w1 μ) θ f =
        ∫⁻ x, ENNReal.rpow (w0 x) (1 - θ) * ENNReal.rpow (w1 x) θ *
          (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ

/-- The weighted L² proposition follows from the generic exact norm identity.](goal) This uses [the stated conclusion](goal). -/
-- @node: weightedL2Interpolation
theorem weightedL2Interpolation : WeightedL2Interpolation := by
  intro S _ μ w0 w1 hw0 hw1 hw θ hθ f hf
  exact Causalean.Mathlib.Analysis.RealInterpolation.weighted_l2_interpolation
    μ w0 w1 hw0 hw1 hw θ hθ f hf

/-- Separability in the product topology of pointwise convergence on S → ℝ:
a countable subclass is dense, so every finite set of evaluations can be approximated
simultaneously to arbitrary positive accuracy. No norm or sequential density is required. -/
def PointwiseSeparable {S : Type} (G : Set (S → ℝ)) : Prop :=
  ∃ G0 : Set (S → ℝ), G0.Countable ∧ G0 ⊆ G ∧
    ∀ g ∈ G, ∀ xs : Finset S, ∀ ε : ℝ, 0 < ε →
      ∃ g0 ∈ G0, ∀ x ∈ xs, |g0 x - g x| < ε
/-- Expected absolute supremum, with extended nonnegative semantics. -/
def radAverage {S : Type} [MeasurableSpace S] (P : Measure S) (b : ℕ)
    (G : Set (S → ℝ)) (φ : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ u, ∫⁻ ρ, ⨆ g : G, ENNReal.ofReal |∑ h : Fin b, sgn (ρ h) * φ (g.val (u h))|
    ∂fairSigns b ∂Measure.pi (fun _ : Fin b => P)

-- @node: lem:classical-rademacher-contraction
/-- The expected absolute-supremum contraction bound with factor two.
Citation: Peter L. Bartlett and Shahar Mendelson (2002), Theorem 12(4), Definition 2,
JMLR 3, pp. 464, 469–470, https://www.jmlr.org/papers/volume3/bartlett02a/bartlett02a.pdf.
Their proof credits Ledoux–Talagrand (1991), Corollary 3.17. The integrable envelope and
separability in the product topology of pointwise convergence (countable density,
equivalently simultaneous approximation on each finite evaluation set) specify the
function-class scope. -/
def ClassicalRademacherContraction : Sort 0 :=
  ∀ (S : Type) [MeasurableSpace S] (P : Measure S), IsProbabilityMeasure P →
    ∀ (b : ℕ) (G : Set (S → ℝ)), PointwiseSeparable G →
    (∀ g ∈ G, Measurable g) →
    (∃ envelope : S → ℝ, Integrable envelope P ∧
      ∀ᵐ x ∂P, ∀ g ∈ G, |g x| ≤ envelope x) →
    ∀ φ : ℝ → ℝ, LipschitzWith 1 φ → φ 0 = 0 →
      radAverage P b G φ ≤ 2 * radAverage P b G id

/-- Probability laws of a single unit's covariate and two potential outcomes. -/
abbrev OutcomeLaw (d : ℕ) := ProbabilityMeasure (Cube d × ℝ × ℝ)
/-- Covariate marginal of a single-unit law. -/
def covMarginal {d : ℕ} (P : OutcomeLaw d) : Measure (Cube d) := P.toMeasure.fst
/-- Conditional midpoint mean, a finite real-valued version modulo covariate null sets. -/
def prognosisOf {d : ℕ} (P : OutcomeLaw d) (u : Cube d) : ℝ :=
  ∫ y, (y.2 + y.1) / 2 ∂P.toMeasure.condKernel u
/-- Conditional mean treatment effect. -/
def effectOf {d : ℕ} (P : OutcomeLaw d) (u : Cube d) : ℝ :=
  ∫ y, y.2 - y.1 ∂P.toMeasure.condKernel u
/-- The law-specific conditional-variance benchmark. -/
def VPub {d : ℕ} (P : OutcomeLaw d) : ℝ :=
  variance (effectOf P) (covMarginal P) +
    2 * (∫ u, variance Prod.snd (P.toMeasure.condKernel u) ∂covMarginal P) +
    2 * (∫ u, variance Prod.fst (P.toMeasure.condKernel u) ∂covMarginal P)
/-- Actual iid-outcome experiment with covariate-only assignment. -/
def publishedExperiment {n d : ℕ} (P : OutcomeLaw d) (π : Design n d) :
    Measure ((Fin n → Cube d × ℝ × ℝ) × Signs n) :=
  (Measure.pi (fun _ : Fin n => P.toMeasure)) ⊗ₘ
    (π.val.comap (fun xs i => (xs i).1)
      (measurable_pi_lambda _ (fun i => (measurable_pi_apply i).fst)))
/-- Actual published HT statistic on iid units and original signs. -/
def htPub {n d : ℕ} (ω : (Fin n → Cube d × ℝ × ℝ) × Signs n) : ℝ :=
  htEstimator (fun i => (ω.1 i).2) ω.2
/-- Finite second moments of both potential outcomes. -/
def FiniteOutcomeMoments {d : ℕ} (P : OutcomeLaw d) : Prop :=
  MemLp (fun ω => ω.2.1) 2 P.toMeasure ∧ MemLp (fun ω => ω.2.2) 2 P.toMeasure
/-- Covariate density with fixed strictly positive finite bounds. -/
def CovDensityBounds {d : ℕ} (P : OutcomeLaw d) (lower upper : ℝ) : Prop :=
  0 < lower ∧ lower ≤ upper ∧ ∃ f : Cube d → ℝ, Measurable f ∧
    covMarginal P = (cubeMeasure d).withDensity (fun u => ENNReal.ofReal (f u)) ∧
    (∀ᵐ u ∂cubeMeasure d, lower ≤ f u ∧ f u ≤ upper)
/-- Bounded positive covariate density. -/
def BoundedPositiveCovDensity {d : ℕ} (P : OutcomeLaw d) : Prop :=
  ∃ lower upper : ℝ, CovDensityBounds P lower upper
/-- Actual (real-valued) HT excess above the law's own benchmark. -/
def publishedExcessReal {n d : ℕ} (π : Design n d) (P : OutcomeLaw d) : ℝ :=
  (n : ℝ) * variance htPub (publishedExperiment P π) - VPub P

-- @node: lem:published-ht-excess-identity
/-- Cytrynbaum's actual HT excess-variance identity for fair outcome-independent kernels.
Citation: Max Cytrynbaum (2026), Proposition 2.3, equation (2.4), with Assumption 2.1
and Definition 2.2, arXiv:2608.18057v1. The source credits Kallus (2018) for an earlier
slightly different imbalance-variance equivalence. Conditional means are modulo null sets.
The existing cited carrier retains pointwise fairness; public a.e. fairness is bridged by
`published_excess_of_ae_fair` using a null-equivalent representative. -/
def PublishedHTExcessIdentity : Sort 0 :=
  ∀ (n d : ℕ), 2 ≤ n → 2 ≤ d → ∀ P : OutcomeLaw d,
    BoundedPositiveCovDensity P → FiniteOutcomeMoments P →
    ∀ π : Design n d, PointwiseFairKernel π.val → OutcomeIndependentKernel π.val →
      publishedExcessReal π P = (4 / (n : ℝ)) *
        ∫ ω, (∑ i, sgn (ω.2 i) * prognosisOf P ((ω.1 i).1)) ^ 2
          ∂publishedExperiment P π

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
