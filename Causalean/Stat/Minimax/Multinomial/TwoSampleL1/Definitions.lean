module
public import Causalean.Stat.Minimax.MinimaxValue
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Fixed two-sample multinomial L1 experiment

This module defines the exact fixed-size experiment for estimating the L1
distance between two finite probability vectors.  It is the neutral interface
used by reusable lower bounds for the experiment.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory
open scoped BigOperators ENNReal

/-- A finite probability vector represented by nonnegative real coordinates
whose sum is one. -/
def ProbabilitySimplex (k : ℕ) :=
  {r : Fin k → ℝ // (∀ i, 0 ≤ r i) ∧ ∑ i, r i = 1}

/-- The nonnegative extended-real coordinates of a probability vector sum to
one. -/
lemma simplexMass_sum {k : ℕ} (R : ProbabilitySimplex k) :
    ∑ i : Fin k, ENNReal.ofReal (R.1 i) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => R.2.1 i), R.2.2]
  norm_num

/-- The probability mass function represented by a finite probability
vector. -/
noncomputable def simplexPMF {k : ℕ} (R : ProbabilitySimplex k) : PMF (Fin k) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (R.1 i)) (simplexMass_sum R)

/-- The law of a fixed-size iid sample from a finite probability vector. -/
noncomputable def simplexSampleLaw {k : ℕ} (R : ProbabilitySimplex k) (n : ℕ) :
    Measure (Fin n → Fin k) :=
  Measure.pi (fun _ : Fin n => (simplexPMF R).toMeasure)

/-- A fixed-size iid sample law from a finite probability vector is a
probability measure. -/
noncomputable instance simplexSampleLaw_isProbability {k : ℕ}
    (R : ProbabilitySimplex k) (n : ℕ) :
    IsProbabilityMeasure (simplexSampleLaw R n) := by
  unfold simplexSampleLaw
  infer_instance

/-- The L1 distance between two finite probability vectors. -/
noncomputable def simplexL1 {k : ℕ} (R S : ProbabilitySimplex k) : ℝ :=
  ∑ i, |R.1 i - S.1 i|

/-- The L1 distance between two finite probability vectors lies between zero
and two. -/
lemma simplexL1_nonneg_le_two {k : ℕ} (R S : ProbabilitySimplex k) :
    0 ≤ simplexL1 R S ∧ simplexL1 R S ≤ 2 := by
  constructor
  · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · have hterm (i : Fin k) : |R.1 i - S.1 i| ≤ R.1 i + S.1 i := by
      rw [abs_le]
      constructor <;> linarith [R.2.1 i, S.2.1 i]
    calc
      simplexL1 R S ≤ ∑ i : Fin k, (R.1 i + S.1 i) :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = 2 := by rw [Finset.sum_add_distrib, R.2.2, S.2.2]; ring

/-- The L1 distance from a finite probability vector to itself is zero. -/
lemma simplexL1_self {k : ℕ} (R : ProbabilitySimplex k) :
    simplexL1 R R = 0 := by
  simp [simplexL1]

/-- The L1 distance between finite probability vectors is symmetric. -/
lemma simplexL1_symm {k : ℕ} (R S : ProbabilitySimplex k) :
    simplexL1 R S = simplexL1 S R := by
  simp only [simplexL1, abs_sub_comm]

/-- The product law of two independent fixed-size samples. -/
noncomputable def twoSampleLaw {k : ℕ} (n : ℕ)
    (RS : ProbabilitySimplex k × ProbabilitySimplex k) :
    Measure ((Fin n → Fin k) × (Fin n → Fin k)) :=
  (simplexSampleLaw RS.1 n).prod (simplexSampleLaw RS.2 n)

/-- The product law of two independent fixed-size samples is a probability
measure. -/
noncomputable instance twoSampleLaw_isProbability {k : ℕ} (n : ℕ)
    (RS : ProbabilitySimplex k × ProbabilitySimplex k) :
    IsProbabilityMeasure (twoSampleLaw n RS) := by
  unfold twoSampleLaw
  infer_instance

/-- Every measurable real-valued statistic of a pair of fixed-size samples. -/
abbrev TwoSampleEstimator (n k : ℕ) :=
  {f : ((Fin n → Fin k) × (Fin n → Fin k)) → ℝ // Measurable f}

/-- The squared risk for estimating the L1 distance in the fixed two-sample
experiment. -/
noncomputable def twoSampleL1Risk {k : ℕ} (n : ℕ)
    (est : TwoSampleEstimator n k)
    (RS : ProbabilitySimplex k × ProbabilitySimplex k) : ℝ :=
  ∫ z, (est.1 z - simplexL1 RS.1 RS.2) ^ 2 ∂twoSampleLaw n RS

/-- The minimax squared risk for estimating the L1 distance from two
fixed-size samples. -/
noncomputable def twoSampleL1MinimaxRisk (n k : ℕ) : ℝ :=
  Causalean.Stat.minimaxValueReal (twoSampleL1Risk (k := k) n)

/-- Given [an alphabet size](hyp:k), [a sample size](hyp:n), [two probability vectors](hyp:R,S), and [an ordered pair of samples](hyp:x), [the singleton mass of the paired iid law factors into its coordinate probabilities](goal). -/
lemma twoSampleLaw_singleton {k : ℕ} (n : ℕ)
    (R S : ProbabilitySimplex k)
    (x : (Fin n → Fin k) × (Fin n → Fin k)) :
    twoSampleLaw n (R, S) {x} =
      (∏ t : Fin n, (simplexPMF R) (x.1 t)) *
        (∏ t : Fin n, (simplexPMF S) (x.2 t)) := by
  have hsingle : ({x} : Set ((Fin n → Fin k) × (Fin n → Fin k))) =
      {x.1} ×ˢ {x.2} := by ext; simp [Prod.ext_iff]
  rw [twoSampleLaw, hsingle, Measure.prod_prod]
  simp only [simplexSampleLaw, Measure.pi_singleton]
  congr 1 <;> apply Finset.prod_congr rfl <;> intro t _ <;>
    exact PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1
