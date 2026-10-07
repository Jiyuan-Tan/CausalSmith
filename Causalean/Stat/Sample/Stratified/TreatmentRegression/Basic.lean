module
public import Causalean.Stat.Sample.OccupancyWeightedMean.Basic
public import Causalean.Stat.Sample.PiTransport

/-! # Categorical within-cell regression statistics

Counts, empirical treatment fractions, the residualized treatment Gram sum,
and the real-outcome regression estimator for an arbitrary finite cell type.
Empty cells contribute zero and the estimator is zero when the Gram sum is
zero. These definitions are independent of any paper or causal model.
-/

@[expose] public section

noncomputable section

namespace Causalean.Stat.Sample.Stratified.TreatmentRegression

open MeasureTheory Set
open scoped BigOperators

variable {κ Ω : Type*} [Fintype κ] [DecidableEq κ]

/-- [The cell count](goal) of [a cell k](hyp:k) in [a sample of n cell labels x](hyp:n,x) is the
number of labels equal to k. -/
def cellCount {n : ℕ} (x : Fin n → κ) (k : κ) : ℕ :=
  ∑ i, if x i = k then 1 else 0

/-- [The treated count](goal) of [a cell k](hyp:k) in [a design d of n cell-treatment pairs](hyp:n,d)
is the number of observations whose cell is k and whose treatment is true. -/
def treatedCount {n : ℕ} (d : Fin n → κ × Bool) (k : κ) : ℕ :=
  ∑ i, if (d i).1 = k ∧ (d i).2 = true then 1 else 0

/-- [The repeat count](goal) of [a sample of n cell labels x](hyp:n,x) sums, over all cells, the
cell count minus one (truncated at zero): the number of observations beyond the first in each
occupied cell. -/
def repeatCount {n : ℕ} (x : Fin n → κ) : ℕ :=
  ∑ k, (cellCount x k - 1)

/-- [The empirical treatment fraction](goal) of [a cell k](hyp:k) in
[a design d of n cell-treatment pairs](hyp:n,d) is the cell's treated count divided by its count,
with value zero at an empty cell. -/
def treatmentFraction {n : ℕ} (d : Fin n → κ × Bool) (k : κ) : ℝ :=
  if cellCount (fun i => (d i).1) k = 0 then 0 else
    (treatedCount d k : ℝ) / cellCount (fun i => (d i).1) k

/-- [The Gram contribution of a cell](goal) with [total count m](hyp:m) and
[treated count t](hyp:t) is t(m − t)/m, with value zero when the cell is empty; the difference
m − t is taken in the natural numbers (truncated at zero). -/
def cellGram (m t : ℕ) : ℝ :=
  if m = 0 then 0 else (t : ℝ) * (m - t : ℕ) / m

/-- [The Gram denominator](goal) of [a design d of n cell-treatment pairs](hyp:n,d) is the sum
over all cells of the cell Gram contributions t(m − t)/m, where m is the cell count and t the
treated count (an empty cell contributes zero). -/
def gram {n : ℕ} (d : Fin n → κ × Bool) : ℝ :=
  ∑ k, cellGram (cellCount (fun i => (d i).1) k) (treatedCount d k)

/-- [The residualized treatment weight](goal) of [observation i](hyp:i) in
[a design d of n cell-treatment pairs](hyp:n,d) is its treatment indicator minus the empirical
treatment fraction of its own cell. -/
def residualWeight {n : ℕ} (d : Fin n → κ × Bool) (i : Fin n) : ℝ :=
  (if (d i).2 then (1 : ℝ) else 0) - treatmentFraction d (d i).1

/-- [The regression numerator](goal) of [a design d of n cell-treatment pairs](hyp:n,d) with
[real outcomes y](hyp:y) is the sum over observations of the residualized treatment weight times
the outcome. -/
def numerator {n : ℕ} (d : Fin n → κ × Bool) (y : Fin n → ℝ) : ℝ :=
  ∑ i, residualWeight d i * y i

/-- [The guarded inverse Gram](goal) of [a design d of n cell-treatment pairs](hyp:n,d) is the
reciprocal of its Gram denominator when that denominator is positive, and zero otherwise. -/
def inverseGram {n : ℕ} (d : Fin n → κ × Bool) : ℝ :=
  if 0 < gram d then (gram d)⁻¹ else 0

/-- [The un-clipped within-cell regression coefficient](goal) of [real outcomes y](hyp:y) on the
treatment in [a design d of n cell-treatment pairs](hyp:n,d) is the regression numerator divided
by the Gram denominator when the latter is positive, and zero otherwise. -/
def regression {n : ℕ} (d : Fin n → κ × Bool) (y : Fin n → ℝ) : ℝ :=
  if 0 < gram d then numerator d y / gram d else 0

/-- [Interval clipping](goal) of [a real estimate t](hyp:t) at [radius R](hyp:R) is
max(−R, min(R, t)); for nonnegative R this confines t to the symmetric interval from −R to R. -/
def clip (R t : ℝ) : ℝ := max (-R) (min R t)

/-- [The clipped observed estimator](goal) reads [the cell label X](hyp:X),
[the Boolean treatment A](hyp:A) and [the real outcome Y](hyp:Y) off each draw of
[a sample z of n observations](hyp:n,z), computes the within-cell regression of the outcomes on
the treatment, and clips it at [radius R](hyp:R). -/
def clippedEstimator {n : ℕ} (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (R : ℝ) (z : Fin n → Ω) : ℝ :=
  clip R (regression (Causalean.Stat.sampleDesign X A z) (fun i => Y (z i)))

/-- [The regression residual coefficient](goal) runs the guarded within-cell regression on
[a sample z of n observations](hyp:n,z), with design given by [the cell label X](hyp:X) and
[the Boolean treatment A](hyp:A), and with outcome [the real outcome Y](hyp:Y) minus
[an arm-and-cell centre](hyp:center) evaluated at the observation's treatment and cell; it is zero
when the Gram denominator is zero. -/
def residualRegression {n : ℕ} (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (z : Fin n → Ω) : ℝ :=
  regression (Causalean.Stat.sampleDesign X A z)
    (fun i => Y (z i) - center (A (z i)) (X (z i)))

/-- For [a sample of n cell labels x](hyp:n,x), [the cell counts summed over all cells equal the
sample size n](goal). -/
lemma sum_cellCount {n : ℕ} (x : Fin n → κ) : ∑ k, cellCount x k = n := by
  classical
  unfold cellCount
  rw [Finset.sum_comm]
  simp

omit [Fintype κ] in
/-- In [a design d of n cell-treatment pairs](hyp:n,d), [the treated count of a cell k](hyp:k)
[never exceeds that cell's total count](goal). -/
lemma treatedCount_le {n : ℕ} (d : Fin n → κ × Bool) (k : κ) :
    treatedCount d k ≤ cellCount (fun i => (d i).1) k := by
  classical
  unfold treatedCount cellCount
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : (d i).1 = k <;> by_cases ha : (d i).2 = true <;> simp [hx, ha]

/-- For [any total count m and treated count t](hyp:m,t), [the cell Gram contribution is
nonnegative](goal), including the empty-cell value zero. -/
lemma cellGram_nonneg (m t : ℕ) : 0 ≤ cellGram m t := by
  unfold cellGram
  split_ifs <;> positivity

/-- For [every design d of n cell-treatment pairs](hyp:n,d), [the Gram denominator is
nonnegative](goal). -/
lemma gram_nonneg {n : ℕ} (d : Fin n → κ × Bool) : 0 ≤ gram d :=
  Finset.sum_nonneg fun _ _ => cellGram_nonneg _ _

/-- If [the Gram denominator of the design d is zero](hyp:d,h), then [both the guarded regression
of any outcomes y on d and the guarded inverse Gram of d are zero](goal). -/
lemma regression_zero {n : ℕ} (d : Fin n → κ × Bool) (y : Fin n → ℝ)
    (h : gram d = 0) : regression d y = 0 ∧ inverseGram d = 0 := by
  simp [regression, inverseGram, h]

variable [MeasurableSpace κ] [MeasurableSingletonClass κ] [MeasurableSpace Ω]

omit [Fintype κ] [DecidableEq κ] in
/-- With finitely many cells whose singletons are measurable,
[every real-valued statistic f of a design of n cell-treatment pairs](hyp:n,f)
[is measurable](goal). -/
lemma measurable_designStatistic [Finite κ] {n : ℕ} (f : (Fin n → κ × Bool) → ℝ) :
    Measurable f := measurable_of_countable f

omit [Fintype κ] in
/-- With finitely many cells, for [every sample size n](hyp:n)
[the regression numerator is jointly measurable in the design and the real outcomes](goal). -/
@[fun_prop] lemma measurable_numerator [Finite κ] {n : ℕ} :
    Measurable (fun v : (Fin n → κ × Bool) × (Fin n → ℝ) => numerator v.1 v.2) := by
  unfold numerator
  apply Finset.measurable_sum
  intro i hi
  exact ((measurable_designStatistic (fun d => residualWeight d i)).comp
    measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd)

/-- For [every sample size n](hyp:n), [the un-clipped guarded regression coefficient is jointly
measurable in the design and the real outcomes](goal). -/
@[fun_prop] lemma measurable_regression {n : ℕ} :
    Measurable (fun v : (Fin n → κ × Bool) × (Fin n → ℝ) => regression v.1 v.2) := by
  unfold regression
  have hg : Measurable (fun v : (Fin n → κ × Bool) × (Fin n → ℝ) => gram v.1) :=
    (measurable_designStatistic gram).comp measurable_fst
  exact Measurable.ite (measurableSet_lt measurable_const hg)
    (measurable_numerator.div hg) measurable_const

/-- If [the cell label X is measurable](hyp:X,hX), [the treatment A is measurable](hyp:A,hA) and
[the outcome Y is measurable](hyp:Y,hY), then for [every sample size n](hyp:n) and
[clipping radius R](hyp:R), [the clipped regression estimator is a measurable function of the
sample](goal). -/
@[fun_prop] lemma measurable_clippedEstimator {n : ℕ} (X : Ω → κ) (A : Ω → Bool)
    (Y : Ω → ℝ) (R : ℝ) (hX : Measurable X) (hA : Measurable A)
    (hY : Measurable Y) :
    Measurable (fun z : Fin n → Ω => clippedEstimator X A Y R z) := by
  change Measurable (fun z : Fin n → Ω => max (-R) (min R
    (regression (Causalean.Stat.sampleDesign X A z) (fun i => Y (z i)))))
  have hd : Measurable (Causalean.Stat.sampleDesign (n := n) X A) :=
    Causalean.Stat.measurable_sampleDesign X A hX hA
  have hy : Measurable (fun z : Fin n → Ω => fun i => Y (z i)) :=
    measurable_pi_lambda _ fun i => hY.comp (measurable_pi_apply i)
  have hg : Measurable (fun z : Fin n → Ω => gram (Causalean.Stat.sampleDesign X A z)) :=
    (measurable_designStatistic (gram (κ := κ) (n := n))).comp hd
  have hH : Measurable (fun z : Fin n → Ω =>
      numerator (Causalean.Stat.sampleDesign X A z) (fun i => Y (z i))) := by
    unfold numerator
    apply Finset.measurable_sum
    intro i hi
    exact ((measurable_designStatistic (fun d : Fin n → κ × Bool =>
      residualWeight d i)).comp hd).mul (hY.comp (measurable_pi_apply i))
  have hr : Measurable (fun z : Fin n → Ω =>
      regression (Causalean.Stat.sampleDesign X A z) (fun i => Y (z i))) := by
    unfold regression
    exact Measurable.ite (measurableSet_lt measurable_const hg) (hH.div hg) measurable_const
  exact (measurable_const (a := -R)).max ((measurable_const (a := R)).min hr)

omit [Fintype κ] [DecidableEq κ] [MeasurableSingletonClass κ] in
/-- For [n independent draws from a probability law](hyp:n,μ) carrying [measurable cell and Boolean-treatment labels](hyp:X,A,hX,hA), [the law of the observed design — the vector of the n cell-treatment pairs read off the draws — is the n-fold product of the joint law of one draw's cell and treatment](goal).

Applying the cell and treatment coordinates to each iid observation gives
the finite product of the observed cell-treatment marginal law. -/
theorem observed_design_pushforward (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (hX : Measurable X) (hA : Measurable A) :
    (Measure.pi (fun _ : Fin n => μ)).map (Causalean.Stat.sampleDesign X A) =
      Measure.pi (fun _ : Fin n => μ.map (fun ω => (X ω, A ω))) :=
  Causalean.Stat.map_pi_finCoordinatewise n μ (hX.prodMk hA)

end Causalean.Stat.Sample.Stratified.TreatmentRegression
