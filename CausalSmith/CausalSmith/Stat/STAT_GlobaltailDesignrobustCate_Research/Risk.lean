module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Estimators
public import Causalean.Stat.Minimax.LIntegralRisk
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Supremum loss, minimax risk, and unknown-tail selector

The loss is integrated in `ℝ≥0∞`, so an unbounded candidate estimator does not
silently receive a zero risk from an ordinary real integral.
-/
@[expose] public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped ENNReal BigOperators

/-- Supremum error over the covariate cube, retaining `∞` for an unbounded
estimator. -/
noncomputable def supLoss {d : ℕ} (f g : (Fin d → ℝ) → ℝ) : ENNReal :=
  ⨆ x : cube d, ENNReal.ofReal |f x - g x|

/-- Observed sample risk under one law. -/
noncomputable def lawRisk {d n : ℕ} (P : Law d)
    (f : (Fin n → Obs d) → (Fin d → ℝ) → ℝ)
    (target : (Fin d → ℝ) → ℝ) : ENNReal :=
  ∫⁻ sample, supLoss (f sample) target ∂P.sample n
  -- @realizes EP(expected sup-norm loss under the n-sample law)

/-- The estimator's loss must be measurable under each law in the class.
Pointwise evaluation is also measurable as required by the paper. -/
def AdmissibleEstimator (d n : ℕ) (β γ C L M : ℝ)
    (f : (Fin n → Obs d) → (Fin d → ℝ) → ℝ) : Prop :=
  (∀ x : Fin d → ℝ, Measurable (fun sample => f sample x)) ∧
  ∀ P : Law d, LawClass d β γ C L M P →
    AEMeasurable (fun sample => supLoss (f sample) P.mu1) (P.sample n)

-- @node: def:minimax-risk
/-- Expected sup-norm minimax risk over the actual law class. -/
noncomputable def minimaxRisk (d n : ℕ) (β γ C L M : ℝ) : ENNReal :=
  ⨅ (f : (Fin n → Obs d) → (Fin d → ℝ) → ℝ),
    ⨅ (_hf : AdmissibleEstimator d n β γ C L M f),
      ⨆ (P : Law d), ⨆ (_hP : LawClass d β γ C L M P),
        lawRisk P f P.mu1
  -- @realizes Risk(infimum over measurable estimators, supremum over class)

/-- Largest dyadic width no greater than the rate-balancing width. -/
noncomputable def fixedLevel (d n : ℕ) (β γ : ℝ) : ℕ :=
  Nat.ceil (Real.log ((rateWidth d n β γ)⁻¹) / Real.log 2)

/-- The selected dyadic bandwidth, rounded down from `rateWidth`. -/
noncomputable def rateBandwidth (d n : ℕ) (β γ : ℝ) : ℝ :=
  dyadicWidth (fixedLevel d n β γ) -- @realizes hstar(dyadic rounding of rateWidth)

/-- Sharp sup-norm rate at sample size `n`. -/
noncomputable def rate (d n : ℕ) (β γ : ℝ) : ℝ :=
  (n : ℝ) ^ (-β / (2 * β + effectiveDimension d γ))

/-- Minimax CATE risk restricted to laws with zero control mean. -/
def AdmissibleCATEEstimator (d n : ℕ) (β γ C L M κ : ℝ)
    (f : (Fin n → Obs d) → (Fin d → ℝ) → ℝ) : Prop :=
  (∀ x : Fin d → ℝ, Measurable (fun sample => f sample x)) ∧
  ∀ P : Law d, CATEClass d β γ C L M κ P →
    AEMeasurable (fun sample => supLoss (f sample) P.tau) (P.sample n)

/-- Minimax CATE risk restricted to laws with zero control mean. -/
noncomputable def zeroControlCATERisk (d n : ℕ)
    (β γ C L M κ : ℝ) : ENNReal :=
  ⨅ (f : (Fin n → Obs d) → (Fin d → ℝ) → ℝ),
    ⨅ (_hf : AdmissibleCATEEstimator d n β γ C L M κ f),
      ⨆ (P : Law d), ⨆ (_hP : CATEClass d β γ C L M κ P),
        ⨆ (_hzero : ∀ x ∈ cube d, P.mu0 x = 0),
          lawRisk P f P.tau

/-- Largest candidate dyadic scale index in the unknown-tail grid. -/
noncomputable def selectorMaxLevel (d n : ℕ) (β : ℝ) : ℕ :=
  Nat.floor (Real.log (n : ℝ) / Real.log 2 / (2 * β + d))

/-- Required occupancy of each norming subcell at scale `j`. -/
noncomputable def selectorThreshold (j : ℕ) (β : ℝ) : ℕ :=
  Nat.ceil ((dyadicWidth j) ^ (-(2 * β)))

/-- Occupancy-only admissibility; no response, `γ`, or `C` occurs. -/
def selectorAdmissible {d n : ℕ} (sample : Fin n → Obs d)
    (j : ℕ) (β : ℝ) : Prop :=
  ∀ Q : Fin d → Fin (2 ^ j), ∀ ℓ : MultiIndex d (polynomialOrder β),
    selectorThreshold j β ≤
      subcellCount sample true j (polynomialOrder β)
        (normingSubcells d β).radius Q ℓ

/-- Finite set of admissible grid indices. Taking its maximum selects the
smallest admissible width. -/
noncomputable def admissibleLevels {d n : ℕ} (sample : Fin n → Obs d)
    (β : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (selectorMaxLevel d n β + 1)).filter
    (fun j => selectorAdmissible sample j β)

-- @node: def:selector-handle
/-- Total unknown-tail selection handle: use the finest admissible balanced
fit, or the zero curve if the candidate set is empty. -/
noncomputable def selectorHandle {d n : ℕ} (sample : Fin n → Obs d)
    (β M : ℝ) (x : Fin d → ℝ) : ℝ :=
  if h : (admissibleLevels sample β).Nonempty then
    balancedEstimator sample ((admissibleLevels sample β).max' h) β M x
  else 0
  -- @realizes Hsel(count-admissible, tail-parameter-free selector)

end CausalSmith.Stat.GlobalTailDesignRobustCate
