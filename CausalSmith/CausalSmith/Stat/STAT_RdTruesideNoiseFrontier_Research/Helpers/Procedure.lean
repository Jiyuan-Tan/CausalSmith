module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# True-side Gaussian measurement-error endpoint frontier

Helpers/Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


-- @env: S3
variable (β σ : ℝ) (n L : ℕ) -- @realizes L(public kernel index)
/-- Chebyshev polynomial normalized by its cosine identity. Given [the displayed inputs and assumptions](hyp:L), [this definition specifies the stated object](goal). -/
def chebyshev (L : ℕ) : Polynomial ℝ := Polynomial.Chebyshev.T ℝ L -- @realizes Chebyshev(Mathlib family)
/-- The polynomial quotient fills the removable singularity at zero. Given [the displayed inputs and assumptions](hyp:L), [this definition specifies the stated object](goal). -/
def endpointF (L : ℕ) : Polynomial ℝ :=
  Polynomial.C (1/2) * Polynomial.divX (1 - (chebyshev L).comp (1 - Polynomial.C 2 * Polynomial.X))
/-- Normalized cube of the endpoint quotient. Given [the displayed inputs and assumptions](hyp:L), [this definition specifies the stated object](goal). -/
-- @node: def:endpoint-kernel
def endpointKernel (L : ℕ) : Polynomial ℝ := -- @realizes Kernel(normalized endpoint polynomial)
  Polynomial.C ((∫ t in (0 : ℝ)..1, (endpointF L).eval t ^ 3)⁻¹) * endpointF L ^ 3
/-- Degree of the positive endpoint kernel. Given [the displayed inputs and assumptions](hyp:L), [this definition specifies the stated object](goal). -/
def kernelDegree (L : ℕ) : ℕ := 3 * (L - 1) -- @realizes Degree(kernel degree)
/-- Iterated ordinary polynomial derivative. Given [the displayed inputs and assumptions](hyp:j,p), [this definition specifies the stated object](goal). -/
def polyDeriv (j : ℕ) (p : Polynomial ℝ) : Polynomial ℝ := (Polynomial.derivative^[j]) p
/-- Finite inverse heat transform, with the exact factorial coefficients. Given [the displayed inputs and assumptions](hyp:L,σ), [this definition specifies the stated object](goal). -/
-- @node: def:inverse-heat
def inverseHeat (L : ℕ) (σ : ℝ) : Polynomial ℝ := -- @realizes Inverse(finite inverse heat)
  ∑ k ∈ Finset.range (kernelDegree L / 2 + 1), -- @realizes k(nonnegative inverse-heat index)
    Polynomial.C ((-σ ^ 2 / 2) ^ k / (Nat.factorial k : ℝ)) * polyDeriv (2 * k) (endpointKernel L)
/-- Marked arm average. Given [the displayed inputs and assumptions](hyp:d,L,σ,n,s), [this definition specifies the stated object](goal). -/
def markedAvg (d : Bool) (L : ℕ) (σ : ℝ) {n : ℕ} (s : Sample n) : ℝ := -- @realizes Ahat(marked sample mean)
  (n : ℝ)⁻¹ * ∑ i, (if (s i).2.1 = d then 1 else 0) * bit (s i).2.2 *
    (inverseHeat L σ).eval (sgn d * (s i).1)
/-- Unmarked arm average. Given [the displayed inputs and assumptions](hyp:d,L,σ,n,s), [this definition specifies the stated object](goal). -/
def unmarkedAvg (d : Bool) (L : ℕ) (σ : ℝ) {n : ℕ} (s : Sample n) : ℝ := -- @realizes Bhat(unmarked sample mean)
  (n : ℝ)⁻¹ * ∑ i, (if (s i).2.1 = d then 1 else 0) *
    (inverseHeat L σ).eval (sgn d * (s i).1)
/-- Denominator floor and ordinary projection onto the interior mean range. Given [the displayed inputs and assumptions](hyp:d,L,σ,n,s), [this definition specifies the stated object](goal). -/
-- @node: def:ratio
def armRatio (d : Bool) (L : ℕ) (σ : ℝ) {n : ℕ} (s : Sample n) : ℝ := -- @realizes muhat(clipped ratio)
  max (1/4) (min (3/4) (markedAvg d L σ s / max (unmarkedAvg d L σ s) (1/8)))
/-- Marked population mean. Given [the displayed inputs and assumptions](hyp:d,L,σ,P,n), [this definition specifies the stated object](goal). -/
def markedMean (d : Bool) (L : ℕ) (σ : ℝ) (P : LatentLaw) (n : ℕ) : ℝ := -- @realizes Amean(marked population expectation)
  ∫ z, markedAvg d L σ z.1 ∂experiment P σ n
/-- Unmarked population mean. Given [the displayed inputs and assumptions](hyp:d,L,σ,P,n), [this definition specifies the stated object](goal). -/
def unmarkedMean (d : Bool) (L : ℕ) (σ : ℝ) (P : LatentLaw) (n : ℕ) : ℝ := -- @realizes Bmean(unmarked population expectation)
  ∫ z, unmarkedAvg d L σ z.1 ∂experiment P σ n
/-- Exact public bias moment. Given [the displayed inputs and assumptions](hyp:L,β), [this definition specifies the stated object](goal). -/
def kernelMoment (L : ℕ) (β : ℝ) : ℝ := -- @realizes Moment(endpoint bias moment)
  ∫ x in (0 : ℝ)..1, x ^ β * (endpointKernel L).eval x -- @realizes x(real latent integration argument)
/-- Exact finite covariance cost. Given [the displayed inputs and assumptions](hyp:L,σ), [this definition specifies the stated object](goal). -/
def kernelVariance (L : ℕ) (σ : ℝ) : ℝ := -- @realizes Variance(exact derivative sum)
  3/4 * ∑ j ∈ Finset.range (kernelDegree L + 1), -- @realizes j(nonnegative derivative index)
    σ ^ (2 * j) / (Nat.factorial j : ℝ) *
      ∫ x in (0 : ℝ)..1, ((polyDeriv j (endpointKernel L)).eval x) ^ 2
/-- The observable effect estimate includes the zero-degree fallback. Given [the displayed inputs and assumptions](hyp:L,σ,n,z), [this definition specifies the stated object](goal). -/
def thetaHat (L : ℕ) (σ : ℝ) {n : ℕ} (z : Input n) : ℝ := -- @realizes thetahat(total effect estimate)
  if L = 0 then 0 else armRatio true L σ z.1 - armRatio false L σ z.1
/-- The public bias-aware radius includes the fallback. Given [the displayed inputs and assumptions](hyp:β,n,σ,L), [this definition specifies the stated object](goal). -/
def radius (β : ℝ) (n : ℕ) (σ : ℝ) (L : ℕ) : ℝ := -- @realizes radius(public radius)
  if L = 0 then 1/2 else 12 * kernelMoment L β + 28 * Real.sqrt (40 * kernelVariance L σ / n)
/-- Public finite cap. Given [the displayed inputs and assumptions](hyp:β,n), [this definition specifies the stated object](goal). -/
def Lmax (β : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (1 / (4 * β + 2))⌉₊ -- @realizes Lmax(finite ceiling cap)
open Classical in
/-- Minimizers of the public radius over the finite candidate set. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
def minimizingDegrees (β : ℝ) (n : ℕ) (σ : ℝ) : Finset ℕ :=
  (Finset.range (Lmax β n + 1)).filter fun L =>
    ∀ J ∈ Finset.range (Lmax β n + 1), radius β n σ L ≤ radius β n σ J
/-- A finite nonempty candidate set has a radius minimizer. Given [the displayed inputs and assumptions](hyp:β,n,σ), [the stated mathematical conclusion holds](goal). -/
lemma minimizingDegrees_nonempty (β : ℝ) (n : ℕ) (σ : ℝ) :
    (minimizingDegrees β n σ).Nonempty := by
  classical
  have hne : (Finset.range (Lmax β n + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨L, hL, hmin⟩ := Finset.exists_min_image
    (Finset.range (Lmax β n + 1)) (radius β n σ) hne
  refine ⟨L, ?_⟩
  simpa only [minimizingDegrees, Finset.mem_filter] using And.intro hL hmin
/-- Smallest public minimizer, formed structurally from the finite set. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
def selectedDegree (β : ℝ) (n : ℕ) (σ : ℝ) : ℕ := -- @realizes Lstar(smallest finite minimizer)
  (minimizingDegrees β n σ).min' (minimizingDegrees_nonempty β n σ)
/-- The exactly evaluable certificate. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
def certificate (β : ℝ) (n : ℕ) (σ : ℝ) : ℝ := -- @realizes Certificate(selected public radius)
  radius β n σ (selectedDegree β n σ)
/-- Clipped lower endpoint. Given [the displayed inputs and assumptions](hyp:β,n,σ,L,z), [this definition specifies the stated object](goal). -/
def polyLo (β : ℝ) (n : ℕ) (σ : ℝ) (L : ℕ) (z : Input n) : ℝ :=
  max (-1) (thetaHat L σ z - radius β n σ L)
/-- Clipped upper endpoint. Given [the displayed inputs and assumptions](hyp:β,n,σ,L,z), [this definition specifies the stated object](goal). -/
def polyHi (β : ℝ) (n : ℕ) (σ : ℝ) (L : ℕ) (z : Input n) : ℝ :=
  min 1 (thetaHat L σ z + radius β n σ L)
/-- Given [the displayed inputs and assumptions](hyp:n,L,σ), [the stated mathematical conclusion holds](goal). -/
@[fun_prop]
lemma thetaHat_measurable (n L : ℕ) (σ : ℝ) : Measurable (@thetaHat L σ n) := by
  have hbit : Measurable bit := measurable_of_countable bit
  have hcell (d : Bool) (i : Fin n) :
      Measurable (fun z : Input n => if (z.1 i).2.1 = d then (1 : ℝ) else 0) := by
    exact (measurable_of_countable (fun y : Bool => if y = d then (1 : ℝ) else 0)).comp
      ((measurable_pi_apply i).comp measurable_fst |>.snd.fst)
  have hmark (d : Bool) : Measurable (fun z : Input n => markedAvg d L σ z.1) := by
    unfold markedAvg
    fun_prop
  have hunmark (d : Bool) : Measurable (fun z : Input n => unmarkedAvg d L σ z.1) := by
    unfold unmarkedAvg
    fun_prop
  unfold thetaHat
  by_cases hL : L = 0
  · simp only [if_pos hL]
    fun_prop
  · simp only [if_neg hL]
    unfold armRatio
    fun_prop
/-- The endpoint quotient is nonnegative, including its removable endpoint. Given [the displayed inputs and assumptions](hyp:L), [the stated mathematical conclusion holds](goal). -/
lemma endpointF_nonneg (L : ℕ) : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ (endpointF L).eval x := by
  have hpos : Ioc (0 : ℝ) 1 ⊆ {x | 0 ≤ (endpointF L).eval x} := by
    intro x hx
    have hc : (chebyshev L).eval (1 - 2*x) ≤ 1 := by
      rw [chebyshev, ← Real.cos_arccos (show -1 ≤ 1 - 2*x by linarith [hx.2])
        (show 1 - 2*x ≤ 1 by linarith [hx.1])]
      rw [Polynomial.Chebyshev.T_real_cos]
      exact Real.cos_le_one _
    have hid := congrArg (fun p : Polynomial ℝ => p.eval x)
      (Polynomial.X_mul_divX_add (1 - (chebyshev L).comp (1 - Polynomial.C 2 * Polynomial.X)))
    have hz : (1 - (chebyshev L).comp (1 - Polynomial.C 2 * Polynomial.X)).coeff 0 = 0 := by
      simp [Polynomial.coeff_zero_eq_eval_zero, chebyshev]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_comp,
      hz] at hid
    have hdiv : 0 ≤ (Polynomial.divX
        (1 - (chebyshev L).comp (1 - Polynomial.C 2 * Polynomial.X))).eval x := by
      nlinarith [hx.1]
    change 0 ≤ (endpointF L).eval x
    simpa only [endpointF, Polynomial.eval_mul, Polynomial.eval_C] using
      mul_nonneg (show (0 : ℝ) ≤ 1/2 by norm_num) hdiv
  have hclosed : IsClosed {x | 0 ≤ (endpointF L).eval x} :=
    isClosed_le continuous_const (endpointF L).continuous
  have hclosure := hclosed.closure_subset_iff.mpr hpos
  rw [closure_Ioc (show (0 : ℝ) ≠ 1 by norm_num)] at hclosure
  exact hclosure

/-- Normalizing a nonnegative cube preserves nonnegativity even at degree zero. Given [the displayed inputs and assumptions](hyp:L), [the stated mathematical conclusion holds](goal). -/
lemma endpointKernel_nonneg (L : ℕ) :
    ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ (endpointKernel L).eval x := by
  have hi : 0 ≤ ∫ t in (0 : ℝ)..1, (endpointF L).eval t ^ 3 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun t ht => pow_nonneg (endpointF_nonneg L t ht) _)
  intro x hx
  simp only [endpointKernel, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow]
  exact mul_nonneg (inv_nonneg.mpr hi) (pow_nonneg (endpointF_nonneg L x hx) _)

/-- The bias moment is nonnegative for every real smoothness exponent. Given [the displayed inputs and assumptions](hyp:L,β), [the stated mathematical conclusion holds](goal). -/
lemma kernelMoment_nonneg (L : ℕ) (β : ℝ) : 0 ≤ kernelMoment L β := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact mul_nonneg (Real.rpow_nonneg hx.1 _) (endpointKernel_nonneg L x hx)

/-- Every public radius is nonnegative, including the fallback. Given [the displayed inputs and assumptions](hyp:β,n,σ,L), [the stated mathematical conclusion holds](goal). -/
lemma radius_nonneg (β : ℝ) (n : ℕ) (σ : ℝ) (L : ℕ) : 0 ≤ radius β n σ L := by
  unfold radius
  split_ifs
  · norm_num
  · exact add_nonneg (mul_nonneg (by norm_num) (kernelMoment_nonneg L β))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

/-- Clipping the two arm ratios keeps the estimated contrast in its target range. Given [the displayed inputs and assumptions](hyp:L,σ,n,z), [the stated mathematical conclusion holds](goal). -/
lemma thetaHat_bounds (L : ℕ) (σ : ℝ) {n : ℕ} (z : Input n) :
    -(1/2 : ℝ) ≤ thetaHat L σ z ∧ thetaHat L σ z ≤ 1/2 := by
  have ha (d : Bool) : (1/4 : ℝ) ≤ armRatio d L σ z.1 ∧ armRatio d L σ z.1 ≤ 3/4 := by
    unfold armRatio
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  unfold thetaHat
  split_ifs
  · norm_num
  · constructor <;> linarith [(ha true).1, (ha true).2, (ha false).1, (ha false).2]

/-- Clipped interval endpoints are measurable and always ordered inside the target range. Given [the displayed inputs and assumptions](hyp:β,n,σ,L), [the stated mathematical conclusion holds](goal). -/
lemma polyInterval_properties (β : ℝ) (n : ℕ) (σ : ℝ) (L : ℕ) :
    Measurable (polyLo β n σ L) ∧ Measurable (polyHi β n σ L) ∧
    ∀ z, -1 ≤ polyLo β n σ L z ∧ polyLo β n σ L z ≤ polyHi β n σ L z ∧
      polyHi β n σ L z ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold polyLo
    fun_prop
  · unfold polyHi
    fun_prop
  · intro z
    have hr := radius_nonneg β n σ L
    have ht := thetaHat_bounds L σ z
    refine ⟨le_max_left _ _, ?_, min_le_left _ _⟩
    apply max_le
    · apply le_min <;> linarith [ht.1]
    · apply le_min <;> linarith [ht.2]
/-- The total connected closed interval, including the constant fallback interval. Given [the displayed inputs and assumptions](hyp:β,n,σ,L), [this definition specifies the stated object](goal). -/
def polyInterval (β : ℝ) (n : ℕ) (σ : ℝ) (L : ℕ) : IntervalProc n := -- @realizes Ipoly(clipped connected interval)
  ⟨polyLo β n σ L, polyHi β n σ L,
    (polyInterval_properties β n σ L).1, (polyInterval_properties β n σ L).2.1,
    (polyInterval_properties β n σ L).2.2⟩
/-- The selected measurable estimate. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
def attainer (β : ℝ) (n : ℕ) (σ : ℝ) : Estimator n := -- @realizes Attainer(selected measurable procedure)
  ⟨thetaHat (selectedDegree β n σ) σ, thetaHat_measurable n _ σ⟩
/-- The selected interval procedure; its honesty is proved later. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
def honestAttainer (β : ℝ) (n : ℕ) (σ : ℝ) : IntervalProc n := -- @realizes Honestattainer(selected interval)
  polyInterval β n σ (selectedDegree β n σ)
/-- Public finite selection returns the observable estimate and interval. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
-- @node: def:public-selection
def publicSelection (β : ℝ) (n : ℕ) (σ : ℝ) : Estimator n × IntervalProc n :=
  (attainer β n σ, honestAttainer β n σ)
/-- Extended worst risk of the selected procedure. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
def attainerRisk (β : ℝ) (n : ℕ) (σ : ℝ) : ℝ≥0∞ :=
  Causalean.Stat.worstCaseRiskENNReal
    (fun (T : Estimator n) (P : {P // Model β σ P}) => absRisk P.val σ n T.val)
    (attainer β n σ)
/-- Extended worst expected length of the selected interval. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
def attainerLength (β : ℝ) (n : ℕ) (σ : ℝ) : ℝ≥0∞ :=
  Causalean.Stat.worstCaseRiskENNReal
    (fun (I : IntervalProc n) (P : {P // Model β σ P}) => expectedLength P.val σ n I)
    (honestAttainer β n σ)

end CausalSmith.Stat.RdTruesideNoiseFrontier
