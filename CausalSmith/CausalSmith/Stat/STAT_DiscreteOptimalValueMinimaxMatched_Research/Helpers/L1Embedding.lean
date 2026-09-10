import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Uniform
import Causalean.Stat.Minimax.MarkovKernelTransport
import Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-! Equal-propensity embedding of the normalized two-sample L1 experiment. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open scoped BigOperators

/-- For [the specified alphabet size](hyp:d), the [probability simplex consists of nonnegative weights on the alphabet that sum to one](goal). -/
def ProbabilitySimplex (d : ℕ) :=
  {R : Fin d → ℝ // (∀ x, 0 ≤ R x) ∧ ∑ x, R x = 1}
  -- @realizes \(\Delta_d\)(nonnegative vectors summing to one)

/-- For [the specified success probability, binary value](hyp:p,y), the [Bernoulli mass assigns probability p to success and one minus p to failure](goal). -/
def bernoulliMass (p : ℝ) (y : Bool) : ℝ := if y then p else 1 - p

/-- For [the specified first probability vector, second probability vector, data point or sample](hyp:Pv,Qv,z), the [L1 embedding full-data mass is the consistency-compatible product mass formed from the two simplex weights and their normalized outcome means, and is zero off the consistency event](goal). -/
noncomputable def l1FullMass {d : ℕ} (Pv Qv : ProbabilitySimplex d)
    (z : FullObs d) : ℝ :=
  let s := Pv.1 z.1 + Qv.1 z.1
  let mu0 := Qv.1 z.1 / s
  let mu1 := Pv.1 z.1 / s
  if z.2.2.1 = (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) then
    s / 4 * bernoulliMass mu0 z.2.2.2.1 * bernoulliMass mu1 z.2.2.2.2
  else 0

/-- [the L1 embedding masses are nonnegative and sum to one](goal). -/
lemma l1FullMass_nonneg_sum {d : ℕ} (Pv Qv : ProbabilitySimplex d) :
    (∀ z, 0 ≤ l1FullMass Pv Qv z) ∧
    ∑ z : FullObs d, ENNReal.ofReal (l1FullMass Pv Qv z) = 1 := by
  classical
  have hnonneg : ∀ z, 0 ≤ l1FullMass Pv Qv z := by
    rintro ⟨x, a, y, y0, y1⟩
    have hp : 0 ≤ Pv.1 x := Pv.2.1 x
    have hq : 0 ≤ Qv.1 x := Qv.2.1 x
    by_cases hs : Pv.1 x + Qv.1 x = 0
    · have hp0 : Pv.1 x = 0 := by nlinarith
      have hq0 : Qv.1 x = 0 := by nlinarith
      simp [l1FullMass, bernoulliMass, hp0, hq0]
    · have hspos : 0 < Pv.1 x + Qv.1 x := lt_of_le_of_ne (add_nonneg hp hq) (Ne.symm hs)
      have hmu0 : 0 ≤ Qv.1 x / (Pv.1 x + Qv.1 x) := div_nonneg hq (le_of_lt hspos)
      have hmu0' : Qv.1 x / (Pv.1 x + Qv.1 x) ≤ 1 :=
        (div_le_one hspos).2 (le_add_of_nonneg_left hp)
      have hmu1 : 0 ≤ Pv.1 x / (Pv.1 x + Qv.1 x) := div_nonneg hp (le_of_lt hspos)
      have hmu1' : Pv.1 x / (Pv.1 x + Qv.1 x) ≤ 1 :=
        (div_le_one hspos).2 (le_add_of_nonneg_right hq)
      fin_cases a <;> fin_cases y <;> fin_cases y0 <;> fin_cases y1 <;>
        simp [l1FullMass, bernoulliMass] <;> positivity
  constructor
  · exact hnonneg
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun z _hz => hnonneg z)]
    have hsum : ∑ z : FullObs d, l1FullMass Pv Qv z = 1 := by
      rw [Fintype.sum_prod_type]
      calc
        ∑ x, ∑ w, l1FullMass Pv Qv (x, w) =
            ∑ x, (Pv.1 x + Qv.1 x) / 2 := by
          apply Finset.sum_congr rfl
          intro x _hx
          have hp : 0 ≤ Pv.1 x := Pv.2.1 x
          have hq : 0 ≤ Qv.1 x := Qv.2.1 x
          by_cases hs : Pv.1 x + Qv.1 x = 0
          · have hp0 : Pv.1 x = 0 := by nlinarith
            have hq0 : Qv.1 x = 0 := by nlinarith
            simp [l1FullMass, bernoulliMass, hp0, hq0]
          · simp [l1FullMass, bernoulliMass, Fintype.sum_prod_type]
            field_simp [hs]
            ring
        _ = 1 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, Pv.2.2, Qv.2.2]
          norm_num
    rw [hsum]
    norm_num

-- @node: def:l1-embedding
/-- For [the specified first probability vector, second probability vector](hyp:Pv,Qv), the [L1 embedding is the potential-outcome law induced by the embedding full-data masses](goal). -/
noncomputable def l1Embedding {d : ℕ} (Pv Qv : ProbabilitySimplex d) : PotentialLaw d :=
  ⟨PMF.ofFintype (fun z => ENNReal.ofReal (l1FullMass Pv Qv z))
    (l1FullMass_nonneg_sum Pv Qv).2⟩
  -- @realizes \(\mathbf P\)(first simplex input) @realizes \(\mathbf Q\)(second simplex input)

set_option maxHeartbeats 1000000 in
-- Expanding the finite five-coordinate PMF requires a larger simplifier budget.
/-- The explicit embedding has the four required atom identities, fair propensity,
armwise exchangeability, and consistency. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma l1Embedding_spec {d : ℕ} (Pv Qv : ProbabilitySimplex d) :
    Consistency (l1Embedding Pv Qv) ∧
    ConditionalExchangeability (l1Embedding Pv Qv) ∧
    (∀ x, jointMass (observedMarginal (l1Embedding Pv Qv)) x true true = Pv.1 x / 4) ∧
    (∀ x, jointMass (observedMarginal (l1Embedding Pv Qv)) x false false = Pv.1 x / 4) ∧
    (∀ x, jointMass (observedMarginal (l1Embedding Pv Qv)) x true false = Qv.1 x / 4) ∧
    (∀ x, jointMass (observedMarginal (l1Embedding Pv Qv)) x false true = Qv.1 x / 4) := by
  classical
  constructor
  · rintro ⟨x, a, y, y0, y1⟩ hne
    simp [l1Embedding, fullMass, l1FullMass, hne]
  · constructor
    · intro x r a ya
      fin_cases r <;> fin_cases a <;> fin_cases ya <;>
        simp [poArmAtom, poAtom, l1Embedding, fullMass, l1FullMass, bernoulliMass] <;>
        ring
    · constructor
      · intro x
        simp [jointMass, observedMarginal, l1Embedding, l1FullMass, bernoulliMass,
          PMF.ofFintype_apply, Finset.sum_filter, Fintype.sum_prod_type]
        by_cases hs : Pv.1 x + Qv.1 x = 0
        · have hp0 : Pv.1 x = 0 := by
            nlinarith [Pv.2.1 x, Qv.2.1 x]
          have hq0 : Qv.1 x = 0 := by
            nlinarith [Pv.2.1 x, Qv.2.1 x]
          simp [hp0, hq0]
        · have hp : 0 ≤ Pv.1 x := Pv.2.1 x
          have hq : 0 ≤ Qv.1 x := Qv.2.1 x
          have hspos : 0 < Pv.1 x + Qv.1 x :=
            lt_of_le_of_ne (add_nonneg hp hq) (Ne.symm hs)
          have hqdiv : Qv.1 x / (Pv.1 x + Qv.1 x) ≤ 1 :=
            (div_le_one hspos).2 (le_add_of_nonneg_left hp)
          have ht1 : 0 ≤ (Pv.1 x + Qv.1 x) / 4 *
              (Qv.1 x / (Pv.1 x + Qv.1 x)) *
              (Pv.1 x / (Pv.1 x + Qv.1 x)) := by
            positivity
          have ht2 : 0 ≤ (Pv.1 x + Qv.1 x) / 4 *
              (1 - Qv.1 x / (Pv.1 x + Qv.1 x)) *
              (Pv.1 x / (Pv.1 x + Qv.1 x)) := by
            positivity
          rw [ENNReal.toReal_add (by simp) (by simp)]
          rw [ENNReal.toReal_ofReal ht1, ENNReal.toReal_ofReal ht2]
          field_simp [hs]
          ring
      · constructor
        · intro x
          simp [jointMass, observedMarginal, l1Embedding, l1FullMass, bernoulliMass,
            PMF.ofFintype_apply, Finset.sum_filter, Fintype.sum_prod_type]
          by_cases hs : Pv.1 x + Qv.1 x = 0
          · have hp0 : Pv.1 x = 0 := by
              nlinarith [Pv.2.1 x, Qv.2.1 x]
            have hq0 : Qv.1 x = 0 := by
              nlinarith [Pv.2.1 x, Qv.2.1 x]
            simp [hp0, hq0]
          · have hp : 0 ≤ Pv.1 x := Pv.2.1 x
            have hq : 0 ≤ Qv.1 x := Qv.2.1 x
            have hspos : 0 < Pv.1 x + Qv.1 x :=
              lt_of_le_of_ne (add_nonneg hp hq) (Ne.symm hs)
            have hpdiv : Pv.1 x / (Pv.1 x + Qv.1 x) ≤ 1 :=
              (div_le_one hspos).2 (le_add_of_nonneg_right hq)
            have hqdiv : Qv.1 x / (Pv.1 x + Qv.1 x) ≤ 1 :=
              (div_le_one hspos).2 (le_add_of_nonneg_left hp)
            rw [ENNReal.toReal_add (by simp) (by simp)]
            repeat' rw [ENNReal.toReal_ofReal (by positivity)]
            field_simp [hs]
            ring
        · constructor
          · intro x
            simp [jointMass, observedMarginal, l1Embedding, l1FullMass, bernoulliMass,
              PMF.ofFintype_apply, Finset.sum_filter, Fintype.sum_prod_type]
            by_cases hs : Pv.1 x + Qv.1 x = 0
            · have hp0 : Pv.1 x = 0 := by
                nlinarith [Pv.2.1 x, Qv.2.1 x]
              have hq0 : Qv.1 x = 0 := by
                nlinarith [Pv.2.1 x, Qv.2.1 x]
              simp [hp0, hq0]
            · have hp : 0 ≤ Pv.1 x := Pv.2.1 x
              have hq : 0 ≤ Qv.1 x := Qv.2.1 x
              have hspos : 0 < Pv.1 x + Qv.1 x :=
                lt_of_le_of_ne (add_nonneg hp hq) (Ne.symm hs)
              have hpdiv : Pv.1 x / (Pv.1 x + Qv.1 x) ≤ 1 :=
                (div_le_one hspos).2 (le_add_of_nonneg_right hq)
              have hqdiv : Qv.1 x / (Pv.1 x + Qv.1 x) ≤ 1 :=
                (div_le_one hspos).2 (le_add_of_nonneg_left hp)
              rw [ENNReal.toReal_add (by simp) (by simp)]
              repeat' rw [ENNReal.toReal_ofReal (by positivity)]
              field_simp [hs]
              ring
          · intro x
            simp [jointMass, observedMarginal, l1Embedding, l1FullMass, bernoulliMass,
              PMF.ofFintype_apply, Finset.sum_filter, Fintype.sum_prod_type]
            by_cases hs : Pv.1 x + Qv.1 x = 0
            · have hp0 : Pv.1 x = 0 := by
                nlinarith [Pv.2.1 x, Qv.2.1 x]
              have hq0 : Qv.1 x = 0 := by
                nlinarith [Pv.2.1 x, Qv.2.1 x]
              simp [hp0, hq0]
            · have hp : 0 ≤ Pv.1 x := Pv.2.1 x
              have hq : 0 ≤ Qv.1 x := Qv.2.1 x
              have hspos : 0 < Pv.1 x + Qv.1 x :=
                lt_of_le_of_ne (add_nonneg hp hq) (Ne.symm hs)
              have hpdiv : Pv.1 x / (Pv.1 x + Qv.1 x) ≤ 1 :=
                (div_le_one hspos).2 (le_add_of_nonneg_right hq)
              have hqdiv : Qv.1 x / (Pv.1 x + Qv.1 x) ≤ 1 :=
                (div_le_one hspos).2 (le_add_of_nonneg_left hp)
              rw [ENNReal.toReal_add (by simp) (by simp)]
              repeat' rw [ENNReal.toReal_ofReal (by positivity)]
              field_simp [hs]
              ring

/-- For [the specified first probability vector, second probability vector](hyp:Pv,Qv), the [L1 distance is the sum of absolute differences between the two probability vectors](goal). -/
noncomputable def l1Distance {d : ℕ} (Pv Qv : ProbabilitySimplex d) : ℝ :=
  ∑ x, |Pv.1 x - Qv.1 x|

/-- [the simplex weights, viewed as extended nonnegative reals, sum to one](goal). -/
lemma simplexENNReal_sum {d : ℕ} (P : ProbabilitySimplex d) :
    ∑ x : Fin d, ENNReal.ofReal (P.1 x) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _hi => P.2.1 i), P.2.2]
  norm_num

/-- For [the specified discrete law](hyp:P), the [simplex probability mass function assigns each alphabet point its simplex weight](goal). -/
noncomputable def simplexPMF {d : ℕ} (P : ProbabilitySimplex d) : PMF (Fin d) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (P.1 x)) (simplexENNReal_sum P)

/-- A single paired draw is randomized into one of the four displayed observed atoms. -/
noncomputable def l1SingleKernel {d : ℕ} : ProbabilityTheory.Kernel (Fin d × Fin d) (Obs d) :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun z =>
    (PMF.map (fun k : Fin 4 =>
      if k = 0 then (z.1, false, false)
      else if k = 1 then (z.1, true, true)
      else if k = 2 then (z.2, false, true)
      else (z.2, true, false)) (PMF.uniformOfFintype (Fin 4))).toMeasure

/-- The explicit fixed-`n` product Markov kernel used in the reduction. -/
noncomputable def l1FixedSampleKernel (n d : ℕ) :
    ProbabilityTheory.Kernel (Fin n → (Fin d × Fin d)) (Fin n → Obs d) :=
  Causalean.Stat.finProductKernel n (l1SingleKernel (d := d))

/-- For [the specified sample size, pair of probability vectors](hyp:n,PQ), the [fixed paired-sample law is the product law of independent draws from the two categorical distributions at every sample index](goal). -/
noncomputable def fixedPairLaw {d : ℕ} (n : ℕ)
    (PQ : ProbabilitySimplex d × ProbabilitySimplex d) :
    MeasureTheory.Measure (Fin n → (Fin d × Fin d)) :=
  MeasureTheory.Measure.pi (fun _ : Fin n =>
    (simplexPMF PQ.1).toMeasure.prod (simplexPMF PQ.2).toMeasure)

/-- For [the specified sample size, alphabet size](hyp:n,d), the [fixed-sample L1 estimator is a measurable real-valued statistic of paired categorical samples](goal). -/
abbrev FixedL1Estimator (n d : ℕ) :=
  {f : (Fin n → (Fin d × Fin d)) → ℝ // Measurable f}

/-- For [the specified sample size, estimator, pair of probability vectors](hyp:n,est,PQ), the [fixed-sample L1 risk is squared-error risk for estimating the L1 distance between two categorical distributions](goal). -/
noncomputable def fixedL1Risk {d : ℕ} (n : ℕ) (est : FixedL1Estimator n d)
    (PQ : ProbabilitySimplex d × ProbabilitySimplex d) : ℝ :=
  Causalean.Stat.sqRisk (fixedPairLaw n PQ) est.1 (l1Distance PQ.1 PQ.2)

/-- For [the specified sample size, alphabet size](hyp:n,d), the [fixed-sample L1 minimax risk is the minimax squared-error risk for the paired categorical experiment](goal). -/
noncomputable def fixedL1MinimaxRisk (n d : ℕ) : ℝ :=
  Causalean.Stat.minimaxValue (fixedL1Risk (d := d) n)

/-- Two independent vectors of Poisson counts with means `2n P_x` and `2n Q_x`. -/
noncomputable def poissonPairLaw {d : ℕ} (n : ℕ)
    (PQ : ProbabilitySimplex d × ProbabilitySimplex d) :
    MeasureTheory.Measure ((Fin d → ℕ) × (Fin d → ℕ)) :=
  let P := (simplexPMF PQ.1).toMeasure
  let Q := (simplexPMF PQ.2).toMeasure
  (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.countLaw P (2 * n)).prod
    (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.countLaw Q (2 * n))

/-- For [the specified alphabet size](hyp:d), the [Poissonized L1 estimator is a measurable real-valued statistic of two categorical histograms](goal). -/
abbrev L1Estimator (d : ℕ) :=
  {f : ((Fin d → ℕ) × (Fin d → ℕ)) → ℝ // Measurable f}

/-- For [the specified sample size, estimator, pair of probability vectors](hyp:n,est,PQ), the [Poissonized L1 risk is squared-error risk for estimating L1 distance from the paired Poisson histograms](goal). -/
noncomputable def poissonL1Risk {d : ℕ} (n : ℕ) (est : L1Estimator d)
    (PQ : ProbabilitySimplex d × ProbabilitySimplex d) : ℝ :=
  Causalean.Stat.sqRisk (poissonPairLaw n PQ) est.1 (l1Distance PQ.1 PQ.2)

/-- Measurable Poisson-histogram estimators whose squared loss is integrable at
every pair of simplex laws and whose worst-case risk is finite.  This scopes
ordinary real-valued Bochner risk to the finite-risk estimators represented by
the cited minimax theorem. -/
def FiniteRiskL1Estimator (n d : ℕ) :=
  {est : L1Estimator d //
    (∀ PQ : ProbabilitySimplex d × ProbabilitySimplex d,
      MeasureTheory.Integrable (fun z => (est.1 z - l1Distance PQ.1 PQ.2) ^ 2)
        (poissonPairLaw n PQ)) ∧
    BddAbove (Set.range (poissonL1Risk n est))}

/-- The two-sample Poissonized L1 minimax risk over measurable estimators with
finite worst-case risk.  The finite-risk scope prevents both the Bochner
integral and the real supremum from taking junk values. -/
noncomputable def poissonL1FiniteRiskMinimaxRisk (n d : ℕ) : ℝ :=
  Causalean.Stat.minimaxValue
    (fun est : FiniteRiskL1Estimator n d => poissonL1Risk n est.1)

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
