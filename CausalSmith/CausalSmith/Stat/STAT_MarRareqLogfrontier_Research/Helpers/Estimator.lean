module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Probability.Distributions.Poisson.Basic

/-! The finite-work mixed-count estimator and its deterministic risk envelope. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Polynomial Set
open scoped NNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

attribute [local instance] Classical.propDecidable

-- @env: S2
variable (n d : ℕ) (q : ℝ)
/-- For [the specified inputs and assumptions](hyp:n), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def streamSize (n : ℕ) : ℝ := (n : ℝ) / 6 -- @realizes \(m\)(n/6)
/-- For [the specified inputs and assumptions](hyp:n,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def streamEffectiveSize (n : ℕ) (q : ℝ) : ℝ :=
  streamSize n * q -- @realizes \(N_0\)(mq)

/-- For [the specified inputs and assumptions](hyp:n,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def needleDegree (n : ℕ) (q : ℝ) : ℕ :=
  Nat.floor (logScale n q / 64) -- @realizes \(k\)(floor ell/64)
/-- For [the specified inputs and assumptions](hyp:n,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def needleRadius (n : ℕ) (q : ℝ) : ℝ :=
  256 * logScale n q -- @realizes \(B\)(256 ell)
/-- For [the specified inputs and assumptions](hyp:n,d,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def needleBranch (n d : ℕ) (q : ℝ) : Prop :=
  128 ≤ logScale n q ∧ Real.sqrt (effectiveSize n q) ≤ d

/-- For [the specified inputs and assumptions](hyp:n,d,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def chebNeedle (n d : ℕ) (q : ℝ) : Polynomial ℝ :=
  -- @realizes \(T_k\)(first-kind Chebyshev polynomial)
  if needleBranch n d q then
    Polynomial.C (needleRadius n q / (2 * (needleDegree n q : ℝ) ^ 2)) *
      (1 - (Polynomial.Chebyshev.T ℝ (needleDegree n q : ℤ)).comp
        (Polynomial.C 1 - Polynomial.C (2 / needleRadius n q) * Polynomial.X)).divX
  else 1
  -- @realizes \(Q_k(t)\)(Chebyshev needle; polynomial quotient)

/-- For [the specified inputs and assumptions](hyp:n,d,q,v), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def needleCoeff (n d : ℕ) (q : ℝ) (v : ℕ) : ℝ :=
  -- @realizes \(v\)(factorial degree index)
  if needleBranch n d q then (1 - chebNeedle n d q).coeff v else 0
  -- @realizes \(a_v\)(coefficient of 1-Q)

/-- For [the specified inputs and assumptions](hyp:z,v), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def fallingFactorial (z v : ℕ) : ℝ := (z.descFactorial v : ℝ)
  -- @realizes \((z)_v\)(descending factorial on count arguments)

/-- For [the specified inputs and assumptions](hyp:k,d,records,assign,pool,j,arrived,ones), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def streamCount {k d : ℕ} (records : Fin k → ObsRecord d)
    (assign : Fin k → Fin 3) (pool : Fin 3) (j : Cell d)
    (arrived ones : Bool) : ℕ :=
  ∑ i : Fin k, if assign i = pool ∧ (records i).A = j.1 ∧
      (records i).X = j.2.1 ∧ (records i).S = j.2.2 ∧
      (!arrived ∨ (records i).R = true) ∧
      (!ones ∨ (records i).RY = true) then 1 else 0

/-- For [the specified inputs and assumptions](hyp:k,d,records,assign,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def memberCount {k d : ℕ} (records : Fin k → ObsRecord d)
    (assign : Fin k → Fin 3) (j : Cell d) : ℕ :=
  streamCount records assign 0 j false false -- @realizes \(M_j\)(membership count)

/-- For [the specified inputs and assumptions](hyp:k,d,records,assign,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def pilotCount {k d : ℕ} (records : Fin k → ObsRecord d)
    (assign : Fin k → Fin 3) (j : Cell d) : ℕ :=
  streamCount records assign 1 j true false -- @realizes \(C'_j\)(pilot arrived count)

/-- For [the specified inputs and assumptions](hyp:k,d,records,assign,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def arrivedCount {k d : ℕ} (records : Fin k → ObsRecord d)
    (assign : Fin k → Fin 3) (j : Cell d) : ℕ :=
  streamCount records assign 2 j true false -- @realizes \(C_j\)(estimation arrived count)

/-- For [the specified inputs and assumptions](hyp:k,d,records,assign,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def arrivedOneCount {k d : ℕ} (records : Fin k → ObsRecord d)
    (assign : Fin k → Fin 3) (j : Cell d) : ℕ :=
  streamCount records assign 2 j true true -- @realizes \(U_j\)(estimation arrived-one count)

/-- For [the specified inputs and assumptions](hyp:k,d,n,records,assign,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def memberWeight {k d : ℕ} (n : ℕ)
    (records : Fin k → ObsRecord d) (assign : Fin k → Fin 3) (j : Cell d) : ℝ :=
  memberCount records assign j / streamSize n -- @realizes \(W_j\)(M/m)

/-- For [the specified inputs and assumptions](hyp:k,d,records,assign,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def ratioBranch {k d : ℕ} (records : Fin k → ObsRecord d)
    (assign : Fin k → Fin 3) (j : Cell d) : ℝ :=
  if 0 < arrivedCount records assign j then
    arrivedOneCount records assign j / arrivedCount records assign j else 0
  -- @realizes \(D_j\)(U/C with zero fallback)

/-- For [the specified inputs and assumptions](hyp:k,d,n,q,records,assign,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def factorialBranch {k d : ℕ} (n : ℕ) (q : ℝ)
    (records : Fin k → ObsRecord d) (assign : Fin k → Fin 3) (j : Cell d) : ℝ :=
  if needleBranch n d q then
    ∑ v ∈ Finset.Icc 1 (needleDegree n q - 1),
      needleCoeff n d q v * arrivedOneCount records assign j *
        fallingFactorial (arrivedCount records assign j - 1) (v - 1)
  else 0
  -- @realizes \(H_j\)(marked factorial branch)

/-- For [the specified inputs and assumptions](hyp:k,d,n,q,records,assign,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def selectedCellEstimate {k d : ℕ} (n : ℕ) (q : ℝ)
    (records : Fin k → ObsRecord d) (assign : Fin k → Fin 3) (j : Cell d) : ℝ :=
  if needleBranch n d q ∧ pilotCount records assign j ≤ needleRadius n q / 4 then
    factorialBranch n q records assign j else ratioBranch records assign j
  -- @realizes \(G_j\)(pilot-selected branch)

/-- For [the specified inputs and assumptions](hyp:u), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def clip (u : ℝ) : ℝ := max (-1) (min 1 u)
  -- @realizes \(\Pi_{[-1,1]}\)(Euclidean interval projection)

/-- For [the specified inputs and assumptions](hyp:k,d,n,q,records,assign), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def auxiliaryMixedValue {k d : ℕ} (n : ℕ) (q : ℝ)
    (records : Fin k → ObsRecord d) (assign : Fin k → Fin 3) : ℝ :=
  if effectiveSize n q ≤ 1 then 0 else
    clip (2 * ∑ j : Cell d,
      armSign j.1 * memberWeight n records assign j *
        selectedCellEstimate n q records assign j)

-- @node: def:mixed-count-estimator
/-- For [the specified inputs and assumptions](hyp:n,d,q,sample), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def mixedCountEstimator (n d : ℕ) (q : ℝ)
    (sample : Fin n → ObsRecord d) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    if h : k ≤ n then
      (poissonMeasure ((n : ℝ≥0) / 2)).real ({k} : Set ℕ) *
        ((∑ assign : Fin k → Fin 3,
          auxiliaryMixedValue n q (fun i => sample (Fin.castLE h i)) assign) /
          (3 : ℝ) ^ k)
    else 0
  -- @realizes \(K_0\)(Poisson records)
  -- @realizes \(\widehat\tau^{\mathrm{mix}}_{n,d,q}\)(auxiliary average)

/-- Given [the specified inputs and assumptions](hyp:n,d,q), [the stated mathematical conclusion holds](goal). -/
-- @node: mixed_count_estimator_regular
lemma mixed_count_estimator_regular (n d : ℕ) (q : ℝ) :
    Measurable (mixedCountEstimator n d q) ∧
      ∀ s, mixedCountEstimator n d q s ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · exact measurable_of_finite _
  · intro s
    have hclip (k : ℕ) (records : Fin k → ObsRecord d)
        (assign : Fin k → Fin 3) :
        -1 ≤ auxiliaryMixedValue n q records assign ∧
          auxiliaryMixedValue n q records assign ≤ 1 := by
      unfold auxiliaryMixedValue clip
      split_ifs <;> constructor <;> simp [le_max_iff, max_le_iff, min_le_iff]
    have hweight (k : ℕ) :
        0 ≤ (poissonMeasure ((n : ℝ≥0) / 2)).real ({k} : Set ℕ) :=
      measureReal_nonneg
    have hmass :
        (∑ k ∈ Finset.range (n + 1),
          (poissonMeasure ((n : ℝ≥0) / 2)).real ({k} : Set ℕ)) ≤ 1 := by
      have h := MeasureTheory.sum_measureReal_le_measureReal_univ
        (μ := poissonMeasure ((n : ℝ≥0) / 2))
        (s := Finset.range (n + 1)) (t := fun k : ℕ => ({k} : Set ℕ))
      have hm : ∀ k ∈ Finset.range (n + 1), MeasurableSet ({k} : Set ℕ) :=
        fun _ _ => MeasurableSet.singleton _
      have hd : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint
          (fun k : ℕ => ({k} : Set ℕ)) := by
        intro i hi j hj hij
        exact Set.disjoint_singleton.mpr hij
      simpa using h hm hd
    have havg (k : ℕ) (h : k ≤ n) :
        -1 ≤ (∑ assign : Fin k → Fin 3,
          auxiliaryMixedValue n q (fun i => s (Fin.castLE h i)) assign) /
          (3 : ℝ) ^ k ∧
        (∑ assign : Fin k → Fin 3,
          auxiliaryMixedValue n q (fun i => s (Fin.castLE h i)) assign) /
          (3 : ℝ) ^ k ≤ 1 := by
      have hp : (0 : ℝ) < 3 ^ k := by positivity
      have hc : (Fintype.card (Fin k → Fin 3) : ℝ) = 3 ^ k := by simp
      constructor
      · apply (le_div_iff₀ hp).2
        rw [neg_mul, one_mul, ← hc]
        simpa using Finset.sum_le_sum (s := Finset.univ)
          (fun a _ => (hclip k _ a).1)
      · apply (div_le_iff₀ hp).2
        rw [one_mul, ← hc]
        simpa using Finset.sum_le_sum (s := Finset.univ)
          (fun a _ => (hclip k _ a).2)
    have hlow :
        -(∑ k ∈ Finset.range (n + 1),
          (poissonMeasure ((n : ℝ≥0) / 2)).real ({k} : Set ℕ)) ≤
          mixedCountEstimator n d q s := by
      unfold mixedCountEstimator
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro k hk
      have h : k ≤ n := by simpa using hk
      simp only [dif_pos h]
      simpa only [mul_neg, mul_one] using
        mul_le_mul_of_nonneg_left (havg k h).1 (hweight k)
    have hupp : mixedCountEstimator n d q s ≤
        ∑ k ∈ Finset.range (n + 1),
          (poissonMeasure ((n : ℝ≥0) / 2)).real ({k} : Set ℕ) := by
      unfold mixedCountEstimator
      apply Finset.sum_le_sum
      intro k hk
      have h : k ≤ n := by simpa using hk
      simp only [dif_pos h]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (havg k h).2 (hweight k)
    exact ⟨by linarith, hupp.trans hmass⟩

/-- For [the specified inputs and assumptions](hyp:n,d,q,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def auxiliaryMixedRisk (n : ℕ) {d : ℕ} (q : ℝ) (P : FullLaw d) : ℝ :=
  ∫ sample, (∑ k ∈ Finset.range (n + 1),
    if h : k ≤ n then
      (poissonMeasure ((n : ℝ≥0) / 2)).real ({k} : Set ℕ) *
        ((∑ assign : Fin k → Fin 3,
          (auxiliaryMixedValue n q (fun i => sample (Fin.castLE h i)) assign -
            ate P) ^ 2) / (3 : ℝ) ^ k)
    else 0) +
    (1 - ∑ k ∈ Finset.range (n + 1),
      (poissonMeasure ((n : ℝ≥0) / 2)).real ({k} : Set ℕ)) * (ate P) ^ 2
      ∂(sampleLaw n P)

/-- For [the specified inputs and assumptions](hyp:n,d,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def riskEnvelope (n d : ℕ) (q : ℝ) : ℝ :=
  let N := effectiveSize n q
  let m := streamSize n
  let N₀ := streamEffectiveSize n q
  let ell := logScale n q
  let k := needleDegree n q
  let B := needleRadius n q
  let γ := Real.log 2 - 1 / 2
  if N ≤ 1 then 1
  else if ¬ needleBranch n d q then
    min 4 (((8 * d / (Real.exp 1 * N₀)) ^ 2) +
      4 * (4 / N₀ + 1 / m) + 4 * Real.exp (-(n : ℝ) * γ))
  else
    let b := 2 * (4 * d * B / (N₀ * (k : ℝ) ^ 2) + 3 * Real.exp (-16 * ell))
    let v := 8 * (4 / N₀ + 1 / m) +
      64 * d * (Real.exp (ell / 8) + 1) * (B ^ 2 / N₀ ^ 2 + B / (m * N₀)) +
        32 * Real.exp (-32 * ell) * (1 + 1 / m)
    min 4 (b ^ 2 + v + 4 * Real.exp (-(n : ℝ) * γ))
  -- @realizes \(\mathfrak U_{n,d,q}\)(three-branch risk envelope)

/-- For [the specified inputs and assumptions](hyp:n,d,q,α,sample), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def riskEnvelopeEndpoints (n d : ℕ) (q α : ℝ)
    (sample : Fin n → ObsRecord d) : ℝ × ℝ :=
  (max (-1) (mixedCountEstimator n d q sample - Real.sqrt (riskEnvelope n d q / α)),
    min 1 (mixedCountEstimator n d q sample + Real.sqrt (riskEnvelope n d q / α)))

-- @node: def:risk-envelope-interval
/-- For [the specified inputs and assumptions](hyp:n,d,q,α,sample), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def riskEnvelopeInterval (n d : ℕ) (q α : ℝ)
    -- @realizes \(\alpha\)(miscoverage level)
    (sample : Fin n → ObsRecord d) : Set ℝ :=
  Icc (riskEnvelopeEndpoints n d q α sample).1
    (riskEnvelopeEndpoints n d q α sample).2
  -- @realizes \(I^{\mathrm{mix}}_\alpha\)(clipped closed interval)

-- @node: def:complete-arrival-ht-estimator
/-- For [the specified inputs and assumptions](hyp:n,d,sample), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def completeArrivalHTEstimator (n d : ℕ)
    (sample : Fin n → ObsRecord d) : ℝ :=
  clip ((2 / (n : ℝ)) * ∑ i : Fin n,
    armSign (sample i).A *
      (if (sample i).R && (sample i).RY then (1 : ℝ) else 0))
  -- @realizes \(\widehat\tau^{\mathrm{HT}}_n\)(clipped arm contrast)

end CausalSmith.Stat.MarRareqLogfrontier
