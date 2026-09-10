import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Monotone.Odd
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.PolicyAtoms

/-! Finite-index evaluation and external-validation sampling world. -/

open MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

-- @node: ass:iid-evaluation
def IidEvaluation (M : ImperfectReferenceModel) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (Z : Fin n → Ω → ℝ × Bool) : Prop :=
  (∀ i, Measurable (Z i)) ∧ ProbabilityTheory.iIndepFun Z μ ∧
    ∀ i, μ.map (Z i) = M.P
  -- @realizes \(Z_i\)(Fin n family with law P_SR)

-- @node: ass:external-sensitivity-sample
def ExternalSensitivitySample (M : ImperfectReferenceModel) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) {n₁ : ℕ}
    (X : Fin n₁ → Ω → Bool) : Prop :=
  (∀ i, Measurable (X i)) ∧ ProbabilityTheory.iIndepFun X μ ∧
    ∀ i, μ.map (X i) = ProbabilityTheory.bernoulliMeasure true false
      ⟨M.alpha, M.alpha_mem_Icc⟩
  -- @realizes \(X^{(1)}_\ell\)(Fin n₁ Bernoulli(α) family)

-- @node: ass:external-specificity-sample
def ExternalSpecificitySample (M : ImperfectReferenceModel) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) {n₀ : ℕ}
    (X : Fin n₀ → Ω → Bool) : Prop :=
  (∀ i, Measurable (X i)) ∧ ProbabilityTheory.iIndepFun X μ ∧
    ∀ i, μ.map (X i) = ProbabilityTheory.bernoulliMeasure true false
      ⟨M.beta, M.beta_mem_Icc⟩
  -- @realizes \(X^{(0)}_\ell\)(Fin n₀ Bernoulli(β) family)

-- @node: ass:positive-sample-sizes
def PositiveSampleSizes (n n₁ n₀ : ℕ) : Prop :=
  1 ≤ n ∧ 1 ≤ n₁ ∧ 1 ≤ n₀
  -- @realizes \(n\)(positive evaluation size) @realizes \(n_1\)(positive sensitivity size)
  -- @realizes \(n_0\)(positive specificity size)

def boolSuccesses {n : ℕ} (X : Fin n → Ω → Bool) (ω : Ω) : ℕ :=
  (Finset.univ.filter fun i => X i ω = true).card

def binomialPmf (n k : ℕ) (p : ℝ) : ℝ :=
  (Nat.choose n k : ℝ) * p ^ k * (1 - p) ^ (n - k)

/-- Equal-tailed exact-binomial test inversion based on the observed success count. -/
def exactBinomialInterval {n : ℕ} (X : Fin n → Ω → Bool)
    (η : ℝ) (ω : Ω) : Set ℝ :=
  {p | p ∈ Set.Icc (0 : ℝ) 1 ∧
    η / 2 ≤ ∑ k ∈ Finset.range (boolSuccesses X ω + 1), binomialPmf n k p ∧
    η / 2 ≤ ∑ k ∈ (Finset.range (n + 1)).filter
      (fun k => boolSuccesses X ω ≤ k), binomialPmf n k p}

-- @env: S3
structure EvaluationDesign (M : ImperfectReferenceModel) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) where
  probability : IsProbabilityMeasure μ
  n : ℕ -- @realizes \(n\)(evaluation sample size)
  n₁ : ℕ -- @realizes \(n_1\)(sensitivity-validation sample size)
  n₀ : ℕ -- @realizes \(n_0\)(specificity-validation sample size)
  Z : Fin n → Ω → ℝ × Bool -- @realizes \(Z_i\)(held-out score-reference observations)
  X₁ : Fin n₁ → Ω → Bool -- @realizes \(X^{(1)}_\ell\)(known-diseased indicators)
  X₀ : Fin n₀ → Ω → Bool -- @realizes \(X^{(0)}_\ell\)(known-nondiseased indicators)
  iidZ : IidEvaluation M μ Z
  iidX₁ : ExternalSensitivitySample M μ X₁
  iidX₀ : ExternalSpecificitySample M μ X₀
  ηs : ℝ -- @realizes \(\eta_s\)(evaluation-band error budget)
  ηs_mem : ηs ∈ Set.Ioo (0 : ℝ) 1 -- @realizes \(\eta_s\)(range (0,1))
  ηα : ℝ -- @realizes \(\eta_\alpha\)(sensitivity error budget)
  ηα_mem : ηα ∈ Set.Ioo (0 : ℝ) 1 -- @realizes \(\eta_\alpha\)(range (0,1))
  ηβ : ℝ -- @realizes \(\eta_\beta\)(specificity error budget)
  ηβ_mem : ηβ ∈ Set.Ioo (0 : ℝ) 1 -- @realizes \(\eta_\beta\)(range (0,1))

/-- The sensitivity interval is the exact-binomial inversion computed from the
known-diseased validation sample; it is not an arbitrary interval field. -/
def EvaluationDesign.Iα {M : ImperfectReferenceModel} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} (D : EvaluationDesign M μ) : Ω → Set ℝ :=
  exactBinomialInterval D.X₁ D.ηα
  -- @realizes \(I_\alpha\)(exact binomial interval from X¹ and η_α)

/-- The specificity interval is the exact-binomial inversion computed from the
known-nondiseased validation sample; it is not an arbitrary interval field. -/
def EvaluationDesign.Iβ {M : ImperfectReferenceModel} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} (D : EvaluationDesign M μ) : Ω → Set ℝ :=
  exactBinomialInterval D.X₀ D.ηβ
  -- @realizes \(I_\beta\)(exact binomial interval from X⁰ and η_β)

/-- Exact-binomial inversion is a closed subinterval of the unit interval for
a positive sample size and an error budget in `(0,1)`. -/
lemma exactBinomialInterval_closed {Ω : Type*} {n : ℕ}
    (X : Fin n → Ω → Bool) (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    (hn : 1 ≤ n) (ω : Ω) :
    ∃ l u, l ≤ u ∧ l ∈ Set.Icc (0 : ℝ) 1 ∧
      u ∈ Set.Icc (0 : ℝ) 1 ∧
      exactBinomialInterval X η ω = Set.Icc l u := by sorry

/-- Membership in the exact-binomial inversion is measurable as a function of
the finite Boolean validation sample. -/
lemma exactBinomialInterval_membership_measurable {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (X : Fin n → Ω → Bool)
    (hX : ∀ i, Measurable (X i)) (η p : ℝ) :
    MeasurableSet {ω | p ∈ exactBinomialInterval X η ω} := by
  have hcount : Measurable (boolSuccesses X) := by
    have heq : boolSuccesses X = fun ω =>
        ∑ i : Fin n, if X i ω = true then 1 else 0 := by
      funext ω
      simp [boolSuccesses]
    rw [heq]
    exact Finset.measurable_sum Finset.univ fun i _ =>
      Measurable.ite ((hX i) (MeasurableSet.singleton true))
        measurable_const measurable_const
  let A : Set ℕ := {k |
    p ∈ Set.Icc (0 : ℝ) 1 ∧
      η / 2 ≤ ∑ j ∈ Finset.range (k + 1), binomialPmf n j p ∧
      η / 2 ≤ ∑ j ∈ (Finset.range (n + 1)).filter (fun j => k ≤ j),
        binomialPmf n j p}
  change MeasurableSet (boolSuccesses X ⁻¹' A)
  exact hcount MeasurableSet.of_discrete

/-- Marginal coverage of the exact-binomial inversion, derived from the finite
i.i.d. Bernoulli sample rather than assumed as a design field. -/
lemma exactBinomialInterval_coverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → Bool) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) 1) (hn : 1 ≤ n)
    (hMeas : ∀ i, Measurable (X i))
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hLaw : ∀ i, μ.map (X i) =
      ProbabilityTheory.bernoulliMeasure true false ⟨p, hp⟩) :
    μ.real {ω | p ∈ exactBinomialInterval X η ω} ≥ 1 - η := by sorry

lemma EvaluationDesign.Iα_closed {M : ImperfectReferenceModel} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} (D : EvaluationDesign M μ)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) (ω : Ω) :
    ∃ l u, l ≤ u ∧ l ∈ Set.Icc (0 : ℝ) 1 ∧
      u ∈ Set.Icc (0 : ℝ) 1 ∧ D.Iα ω = Set.Icc l u := by
  exact exactBinomialInterval_closed D.X₁ D.ηα D.ηα_mem hSizes.2.1 ω

lemma EvaluationDesign.Iβ_closed {M : ImperfectReferenceModel} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} (D : EvaluationDesign M μ)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) (ω : Ω) :
    ∃ l u, l ≤ u ∧ l ∈ Set.Icc (0 : ℝ) 1 ∧
      u ∈ Set.Icc (0 : ℝ) 1 ∧ D.Iβ ω = Set.Icc l u := by
  exact exactBinomialInterval_closed D.X₀ D.ηβ D.ηβ_mem hSizes.2.2 ω

lemma EvaluationDesign.Iα_data_measurable {M : ImperfectReferenceModel}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (D : EvaluationDesign M μ) (p : ℝ) :
    MeasurableSet {ω | p ∈ D.Iα ω} := by
  exact exactBinomialInterval_membership_measurable D.X₁ D.iidX₁.1 D.ηα p

lemma EvaluationDesign.Iβ_data_measurable {M : ImperfectReferenceModel}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (D : EvaluationDesign M μ) (p : ℝ) :
    MeasurableSet {ω | p ∈ D.Iβ ω} := by
  exact exactBinomialInterval_membership_measurable D.X₀ D.iidX₀.1 D.ηβ p

lemma EvaluationDesign.Iα_coverage {M : ImperfectReferenceModel} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} (D : EvaluationDesign M μ)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) :
    μ.real {ω | M.alpha ∈ D.Iα ω} ≥ 1 - D.ηα := by
  let _ : IsProbabilityMeasure μ := D.probability
  exact exactBinomialInterval_coverage μ D.X₁ M.alpha M.alpha_mem_Icc
    D.ηα D.ηα_mem hSizes.2.1 D.iidX₁.1 D.iidX₁.2.1 D.iidX₁.2.2
  -- @realizes \(I_\alpha\)(exact-binomial noncoverage at most η_α)

lemma EvaluationDesign.Iβ_coverage {M : ImperfectReferenceModel} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} (D : EvaluationDesign M μ)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) :
    μ.real {ω | M.beta ∈ D.Iβ ω} ≥ 1 - D.ηβ := by
  let _ : IsProbabilityMeasure μ := D.probability
  exact exactBinomialInterval_coverage μ D.X₀ M.beta M.beta_mem_Icc
    D.ηβ D.ηβ_mem hSizes.2.2 D.iidX₀.1 D.iidX₀.2.1 D.iidX₀.2.2
  -- @realizes \(I_\beta\)(exact-binomial noncoverage at most η_β)

lemma iidEvaluation_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : ImperfectReferenceModel) {n : ℕ}
    (Z : Fin n → Ω → ℝ × Bool) (h : IidEvaluation M μ Z) (i j : Fin n) :
    ProbabilityTheory.IdentDistrib (Z i) (Z j) μ μ := by
  exact ⟨(h.1 i).aemeasurable, (h.1 j).aemeasurable,
    (h.2.2 i).trans (h.2.2 j).symm⟩

/-- Strictly increasing bounded transform used to read atom prefixes as left limits
of ordinary real distribution functions. -/
def scoreTransport (s : ℝ) : ℝ := s / (1 + |s|)

/-- For a reference stratum, observations outside the stratum are sent to `2`,
strictly above the range of `scoreTransport`. -/
def transportedEvaluation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (r : Bool) (i : Fin D.n) (ω : Ω) : ℝ :=
  if (D.Z i ω).2 = r then scoreTransport (D.Z i ω).1 else 2

/-- Left limit of a real function, used only at the finitely many cutoff
boundaries (and at a terminal point between `1` and `2`). -/
noncomputable def cdfLeftLimit (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup {z | ∃ y < x, z = F y}

lemma scoreTransport_strictMono : StrictMono scoreTransport := by
  refine strictMono_of_odd_strictMonoOn_nonneg ?_ ?_
  · intro x
    simp only [scoreTransport, abs_neg]
    ring
  · rintro x hx y hy hxy
    change 0 ≤ x at hx
    change 0 ≤ y at hy
    simp only [scoreTransport, abs_of_nonneg hx, abs_of_nonneg hy]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith

lemma scoreTransport_lt_one (s : ℝ) : scoreTransport s < 1 := by
  rw [scoreTransport, div_lt_one (by positivity)]
  nlinarith [le_abs_self s]

/-- A uniform CDF band controls every required left limit, hence every finite
cutoff-atom prefix. -/
lemma leftLimit_sub_le_uniformBand (F Fn : ℝ → ℝ) (x ε : ℝ)
    (hband : ∀ y, |Fn y - F y| ≤ ε) :
    |cdfLeftLimit Fn x - cdfLeftLimit F x| ≤ ε := by
  let A : Set ℝ := {z | ∃ y < x, z = Fn y}
  let B : Set ℝ := {z | ∃ y < x, z = F y}
  have hε : 0 ≤ ε :=
    le_trans (abs_nonneg (Fn (x - 1) - F (x - 1))) (hband (x - 1))
  have hA : A.Nonempty := ⟨Fn (x - 1), x - 1, by linarith, rfl⟩
  have hB : B.Nonempty := ⟨F (x - 1), x - 1, by linarith, rfl⟩
  have hAB : BddAbove A ↔ BddAbove B := by
    constructor
    · rintro ⟨C, hC⟩
      refine ⟨C + ε, ?_⟩
      rintro z ⟨y, hy, rfl⟩
      have hFn : Fn y ≤ C := hC ⟨y, hy, rfl⟩
      have hd := (abs_le.mp (hband y)).1
      linarith
    · rintro ⟨C, hC⟩
      refine ⟨C + ε, ?_⟩
      rintro z ⟨y, hy, rfl⟩
      have hF : F y ≤ C := hC ⟨y, hy, rfl⟩
      have hd := (abs_le.mp (hband y)).2
      linarith
  change |sSup A - sSup B| ≤ ε
  by_cases hAbdd : BddAbove A
  · have hBbdd : BddAbove B := hAB.mp hAbdd
    rw [abs_le]
    constructor
    · have hle : sSup B ≤ sSup A + ε := by
        apply csSup_le hB
        rintro z ⟨y, hy, rfl⟩
        have hFnsup : Fn y ≤ sSup A := le_csSup hAbdd ⟨y, hy, rfl⟩
        have hd := (abs_le.mp (hband y)).1
        linarith
      linarith
    · have hle : sSup A ≤ sSup B + ε := by
        apply csSup_le hA
        rintro z ⟨y, hy, rfl⟩
        have hFsup : F y ≤ sSup B := le_csSup hBbdd ⟨y, hy, rfl⟩
        have hd := (abs_le.mp (hband y)).2
        linarith
      linarith
  · have hBnot : ¬ BddAbove B := by simpa [hAB] using hAbdd
    rw [csSup_of_not_bddAbove hAbdd, csSup_of_not_bddAbove hBnot,
      sub_self, abs_zero]
    exact hε

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
