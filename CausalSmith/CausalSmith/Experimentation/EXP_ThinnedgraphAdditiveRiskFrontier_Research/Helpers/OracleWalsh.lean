module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ScoreMean
public import Mathlib.Probability.Moments.Variance
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.SymmetricSignPolys

/-!
# Oracle variance chain
-/

@[expose] public section

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The compulsory own coordinate adjoined to the off-diagonal sources. -/
-- @node: oracleNbhd
def oracleNbhd (θ : Schedule V) (i : V) : Finset V := insert i (inNbhd θ i)

/-- The additive coefficient on an augmented source coordinate. -/
-- @node: oracleBeta
def oracleBeta (θ : Schedule V) (i j : V) : ℝ :=
  if j = i then θ.t i else θ.b i j

/-- The assignment-averaged row outcome in the centered-sign expansion. -/
-- @node: oracleMu
def oracleMu (θ : Schedule V) (i : V) : ℝ :=
  θ.a i + (∑ j ∈ oracleNbhd θ i, oracleBeta θ i j) / 2

/-- No own coordinate occurs among the off-diagonal sources.  [For the stated data and conditions](hyp:θ,i), [the stated conclusion holds](goal). -/
-- @node: oracle_self_not_mem
lemma oracle_self_not_mem (θ : Schedule V) (i : V) : i ∉ inNbhd θ i := by
  simp [inNbhd, θ.irrefl i]

/-- Summing augmented coefficients separates the own treatment coefficient.  [For the stated data and conditions](hyp:θ,i,f), [the stated conclusion holds](goal). -/
-- @node: oracleBeta_sum
lemma oracleBeta_sum (θ : Schedule V) (i : V) (f : V → ℝ) :
    (∑ j ∈ oracleNbhd θ i, oracleBeta θ i j * f j) =
      θ.t i * f i + ∑ j ∈ inNbhd θ i, θ.b i j * f j := by
  rw [oracleNbhd, Finset.sum_insert (oracle_self_not_mem θ i)]
  simp only [oracleBeta, ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := fun he => oracle_self_not_mem θ i (he ▸ hj)
  simp [hji]

/-- The augmented coefficient mass is precisely the own plus spillover mass.  [For the stated data and conditions](hyp:θ,i), [the stated conclusion holds](goal). -/
-- @node: oracleBeta_abs_sum
lemma oracleBeta_abs_sum (θ : Schedule V) (i : V) :
    (∑ j ∈ oracleNbhd θ i, |oracleBeta θ i j|) =
      |θ.t i| + ∑ j ∈ inNbhd θ i, |θ.b i j| := by
  rw [oracleNbhd, Finset.sum_insert (oracle_self_not_mem θ i)]
  simp only [oracleBeta, ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := fun he => oracle_self_not_mem θ i (he ▸ hj)
  simp [hji]

/-- The augmented row has at most d+1 coordinates.  [For the stated data and conditions](hyp:θ,d,hc,i), [the stated conclusion holds](goal). -/
-- @node: oracleNbhd_card_le
lemma oracleNbhd_card_le (θ : Schedule V) (d : ℕ) (hc : ScheduleClass θ d) (i : V) :
    (oracleNbhd θ i).card ≤ d + 1 := by
  rw [oracleNbhd, Finset.card_insert_of_notMem (oracle_self_not_mem θ i)]
  exact Nat.add_le_add_right (hc.inDegree i) 1

/-- Adjoining the diagonal increases coordinate multiplicity by at most one.  [For the stated data and conditions](hyp:θ,d,hc), [the stated conclusion holds](goal). -/
-- @node: oracleNbhd_blockDegree
lemma oracleNbhd_blockDegree (θ : Schedule V) (d : ℕ) (hc : ScheduleClass θ d) :
    Causalean.Experimentation.DesignBased.BlockDegreeLE (oracleNbhd θ) (d + 1) := by
  intro j
  have he : (Finset.univ.filter fun i => j ∈ oracleNbhd θ i) =
      insert j (Finset.univ.filter fun i => j ∈ inNbhd θ i) := by
    ext i
    simp [oracleNbhd, eq_comm]
  rw [he, Finset.card_insert_of_notMem]
  · exact Nat.add_le_add_right (hc.outDegree j) 1
  · simp [oracle_self_not_mem θ j]

/-- The centered row baseline has magnitude at most one.  [For the stated data and conditions](hyp:θ,d,hc,i), [the stated conclusion holds](goal). -/
-- @node: oracleMu_abs_le
lemma oracleMu_abs_le (θ : Schedule V) (d : ℕ) (hc : ScheduleClass θ d) (i : V) :
    |oracleMu θ i| ≤ 1 := by
  have hs := Finset.abs_sum_le_sum_abs (fun j => oracleBeta θ i j) (oracleNbhd θ i)
  have hm := hc.coeffMass i
  rw [add_assoc, ← oracleBeta_abs_sum] at hm
  calc
    |oracleMu θ i| ≤ |θ.a i| + |∑ j ∈ oracleNbhd θ i, oracleBeta θ i j| / 2 := by
      simpa [oracleMu, abs_div] using abs_add_le (θ.a i)
        ((∑ j ∈ oracleNbhd θ i, oracleBeta θ i j) / 2)
    _ ≤ 1 := by linarith [abs_nonneg (∑ j ∈ oracleNbhd θ i, oracleBeta θ i j)]

/-- Substituting treatment=(1+sign)/2 gives the actual centered row response.  [For the stated data and conditions](hyp:θ,i,z), [the stated conclusion holds](goal). -/
-- @node: potentialOutcome_oracle_centered
lemma potentialOutcome_oracle_centered (θ : Schedule V) (i : V) (z : Assign V) :
    potentialOutcome θ i z = oracleMu θ i +
      (∑ j ∈ oracleNbhd θ i, oracleBeta θ i j * signOf (z j)) / 2 := by
  have hz (j : V) : treatment (z j) = (1 + signOf (z j)) / 2 := by
    cases z j <;> norm_num [treatment, signOf]
  have ho : potentialOutcome θ i z = θ.a i +
      ∑ j ∈ oracleNbhd θ i, oracleBeta θ i j * treatment (z j) := by
    rw [oracleBeta_sum]
    change θ.a i + θ.t i * treatment (z i) +
      (∑ j ∈ inNbhd θ i, θ.b i j * treatment (z j)) = _
    ring
  rw [ho]
  simp_rw [hz, mul_div, mul_add, mul_one]
  rw [← Finset.sum_div, Finset.sum_add_distrib, oracleMu]
  ring

/-- The sum of augmented signs is the recorded supplied-graph weight.  [For the stated data and conditions](hyp:θ,i,z), [the stated conclusion holds](goal). -/
-- @node: oracleNbhd_sign_sum
lemma oracleNbhd_sign_sum (θ : Schedule V) (i : V) (z : Assign V) :
    (∑ j ∈ oracleNbhd θ i, signOf (z j)) =
      signOf (z i) + ∑ j ∈ inNbhd θ i, signOf (z j) := by
  exact Finset.sum_insert (oracle_self_not_mem θ i)

/-- The constant coefficient of the score is the all-treated contrast.  [For the stated data and conditions](hyp:θ), [the stated conclusion holds](goal). -/
-- @node: tte_oracleBeta_sum
lemma tte_oracleBeta_sum (θ : Schedule V) :
    tte θ = (Fintype.card V : ℝ)⁻¹ *
      ∑ i, ∑ j ∈ oracleNbhd θ i, oracleBeta θ i j := by
  unfold tte
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hb := oracleBeta_sum θ i (fun _ => 1)
  simp only [mul_one] at hb
  rw [hb]
  simp [potentialOutcome, treatment]
  ring

/-- Removing the diagonal sign squares leaves a genuinely quadratic, distinct-coordinate term.  [For the stated data and conditions](hyp:θ,i,z), [the stated conclusion holds](goal). -/
-- @node: oracle_row_quadratic_split
lemma oracle_row_quadratic_split (θ : Schedule V) (i : V) (z : Assign V) :
    (∑ j ∈ oracleNbhd θ i, oracleBeta θ i j * signOf (z j)) *
        (∑ k ∈ oracleNbhd θ i, signOf (z k)) =
      (∑ j ∈ oracleNbhd θ i, oracleBeta θ i j) +
        ∑ j ∈ oracleNbhd θ i, ∑ k ∈ (oracleNbhd θ i).erase j,
          oracleBeta θ i j * signOf (z j) * signOf (z k) := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ hj]
  have hs : signOf (z j) * signOf (z j) = 1 := by
    cases z j <;> norm_num [signOf]
  simp only [mul_assoc, hs, mul_one]
  ring

/-- Exact degree-at-most-two expansion of the centered supplied-graph score.
The quadratic sum uses ordered pairs so it requires no arbitrary ordering of the population.  [For the stated data and conditions](hyp:θ,z), [the stated conclusion holds](goal). -/
-- @node: oracleScore_centered_expansion
lemma oracleScore_centered_expansion (θ : Schedule V) (z : Assign V) :
    oracleScore θ z - tte θ =
      (2 / (Fintype.card V : ℝ)) *
        (∑ i, oracleMu θ i * ∑ j ∈ oracleNbhd θ i, signOf (z j)) +
      (Fintype.card V : ℝ)⁻¹ *
        ∑ i, ∑ j ∈ oracleNbhd θ i, ∑ k ∈ (oracleNbhd θ i).erase j,
          oracleBeta θ i j * signOf (z j) * signOf (z k) := by
  have hrow (i : V) :
      potentialOutcome θ i z * (∑ j ∈ oracleNbhd θ i, signOf (z j)) =
        oracleMu θ i * (∑ j ∈ oracleNbhd θ i, signOf (z j)) +
        ((∑ j ∈ oracleNbhd θ i, oracleBeta θ i j) +
          ∑ j ∈ oracleNbhd θ i, ∑ k ∈ (oracleNbhd θ i).erase j,
            oracleBeta θ i j * signOf (z j) * signOf (z k)) / 2 := by
    rw [potentialOutcome_oracle_centered, add_mul, div_mul_eq_mul_div,
      oracle_row_quadratic_split]
  rw [oracleScore, tte_oracleBeta_sum]
  simp_rw [← oracleNbhd_sign_sum, hrow]
  simp_rw [add_div]
  simp only [Finset.sum_add_distrib, ← Finset.sum_div]
  ring

/-- The collected coefficient of a source sign in the oracle score. -/
-- @node: oracleLinearCoefficient
def oracleLinearCoefficient (θ : Schedule V) (j : V) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => j ∈ oracleNbhd θ i), oracleMu θ i

/-- Collecting the linear terms by source preserves all augmented neighborhoods.  [For the stated data and conditions](hyp:θ,z), [the stated conclusion holds](goal). -/
-- @node: oracle_linear_collect
lemma oracle_linear_collect (θ : Schedule V) (z : Assign V) :
    (∑ i, oracleMu θ i * ∑ j ∈ oracleNbhd θ i, signOf (z j)) =
      ∑ j, oracleLinearCoefficient θ j * signOf (z j) := by
  have hs (i : V) : (∑ j ∈ oracleNbhd θ i, signOf (z j)) =
      ∑ j : V, if j ∈ oracleNbhd θ i then signOf (z j) else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  simp_rw [hs]
  simp only [oracleLinearCoefficient, Finset.sum_mul, Finset.mul_sum, Finset.sum_filter,
    mul_ite, ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_comm]

/-- Two centered signs are orthonormal under the actual assignment measure.  [For the stated data and conditions](hyp:j,k), [the stated conclusion holds](goal). -/
-- @node: integral_oracle_sign_pair
lemma integral_oracle_sign_pair (j k : V) :
    (∫ z, signOf (z j) * signOf (z k) ∂halfBernoulli V) =
      if j = k then 1 else 0 := by
  have he : (fun z : Assign V => signOf (z j) * signOf (z k)) =
      fun z => 2 * (treatment (z k) * signOf (z j)) - signOf (z j) := by
    funext z
    cases z j <;> cases z k <;> norm_num [signOf, treatment]
  rw [he, integral_sub (halfBernoulli_integrable _) (halfBernoulli_integrable _),
    integral_const_mul, integral_treatment_mul_signOf, integral_signOf_halfBernoulli]
  by_cases h : j = k
  · simp [h]
  · simp [h, Ne.symm h]

/-- Orthogonality gives the exact second moment of the linear sign polynomial.  [For the stated data and conditions](hyp:θ), [the stated conclusion holds](goal). -/
-- @node: oracle_linear_second_moment
lemma oracle_linear_second_moment (θ : Schedule V) :
    (∫ z, (∑ i, oracleMu θ i * ∑ j ∈ oracleNbhd θ i, signOf (z j)) ^ 2
      ∂halfBernoulli V) = ∑ j, oracleLinearCoefficient θ j ^ 2 := by
  simp_rw [oracle_linear_collect, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _)]
  have he (k : V) :
      (fun z : Assign V => (oracleLinearCoefficient θ j * signOf (z j)) *
        (oracleLinearCoefficient θ k * signOf (z k))) =
      fun z => (oracleLinearCoefficient θ j * oracleLinearCoefficient θ k) *
        (signOf (z j) * signOf (z k)) := by funext z; ring
  simp_rw [he, integral_const_mul, integral_oracle_sign_pair]
  simp [mul_ite]

/-- Cauchy-Schwarz and the out-degree bound control the linear coefficient energy.  [For the stated data and conditions](hyp:θ,d,hc), [the stated conclusion holds](goal). -/
-- @node: oracle_linear_energy_le
lemma oracle_linear_energy_le (θ : Schedule V) (d : ℕ) (hc : ScheduleClass θ d) :
    (∑ j, oracleLinearCoefficient θ j ^ 2) ≤
      (Fintype.card V : ℝ) * ((d : ℝ) + 1) ^ 2 := by
  have hmu (i : V) : oracleMu θ i ^ 2 ≤ 1 := by
    have h := oracleMu_abs_le θ d hc i
    have h' := abs_nonneg (oracleMu θ i)
    nlinarith [sq_abs (oracleMu θ i)]
  have hdegree := oracleNbhd_blockDegree θ d hc
  have hrow (j : V) : oracleLinearCoefficient θ j ^ 2 ≤
      ((d : ℝ) + 1) * ∑ i ∈ Finset.univ.filter (fun i => j ∈ oracleNbhd θ i),
        oracleMu θ i ^ 2 := by
    have hcard : ((Finset.univ.filter (fun i => j ∈ oracleNbhd θ i)).card : ℝ) ≤
        (d : ℝ) + 1 := by exact_mod_cast hdegree j
    exact (show oracleLinearCoefficient θ j ^ 2 ≤
      ((Finset.univ.filter (fun i => j ∈ oracleNbhd θ i)).card : ℝ) *
        ∑ i ∈ Finset.univ.filter (fun i => j ∈ oracleNbhd θ i), oracleMu θ i ^ 2 from
      sq_sum_le_card_mul_sum_sq).trans
        (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  calc
    (∑ j, oracleLinearCoefficient θ j ^ 2) ≤
        ∑ j, ((d : ℝ) + 1) *
          ∑ i ∈ Finset.univ.filter (fun i => j ∈ oracleNbhd θ i), oracleMu θ i ^ 2 :=
      Finset.sum_le_sum fun j _ => hrow j
    _ = ((d : ℝ) + 1) * ∑ i, (oracleNbhd θ i).card * oracleMu θ i ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp [Finset.univ_inter]
    _ ≤ ((d : ℝ) + 1) * ∑ _i : V, ((d : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      have hcard : ((oracleNbhd θ i).card : ℝ) ≤ (d : ℝ) + 1 := by
        exact_mod_cast oracleNbhd_card_le θ d hc i
      exact (mul_le_mul_of_nonneg_left (hmu i) (by positivity)).trans (by simpa using hcard)
    _ = _ := by simp; ring

/-- The complete linear contribution to the oracle variance is at most 4D²/n.  [For the stated data and conditions](hyp:θ,d,hn,hc), [the stated conclusion holds](goal). -/
-- @node: oracle_linear_scaled_second_moment_le
lemma oracle_linear_scaled_second_moment_le (θ : Schedule V) (d : ℕ)
    (hn : 4 ≤ Fintype.card V) (hc : ScheduleClass θ d) :
    (∫ z, ((2 / (Fintype.card V : ℝ)) *
      (∑ i, oracleMu θ i * ∑ j ∈ oracleNbhd θ i, signOf (z j))) ^ 2
      ∂halfBernoulli V) ≤ 4 * ((d : ℝ) + 1) ^ 2 / Fintype.card V := by
  have hn0 : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  simp_rw [mul_pow]
  rw [integral_const_mul, oracle_linear_second_moment]
  calc
    (2 / (Fintype.card V : ℝ)) ^ 2 * (∑ j, oracleLinearCoefficient θ j ^ 2) ≤
        (2 / (Fintype.card V : ℝ)) ^ 2 *
          ((Fintype.card V : ℝ) * ((d : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left (oracle_linear_energy_le θ d hc) (sq_nonneg _)
    _ = _ := by field_simp; ring

/-- A singleton sign is orthogonal to every distinct-coordinate quadratic monomial.  [For the stated data and conditions](hyp:l,j,k,hjk), [the stated conclusion holds](goal). -/
-- @node: integral_oracle_sign_triple
lemma integral_oracle_sign_triple (l j k : V) (hjk : j ≠ k) :
    (∫ z, signOf (z l) * (signOf (z j) * signOf (z k))
      ∂halfBernoulli V) = 0 := by
  have hsets : ({l} : Finset V) ≠ {j, k} := by
    intro he
    have hj : j = l := by
      have : j ∈ ({l} : Finset V) := he ▸ (by simp : j ∈ ({j, k} : Finset V))
      simpa using this
    have hk : k = l := by
      have : k ∈ ({l} : Finset V) := he ▸ (by simp : k ∈ ({j, k} : Finset V))
      simpa using this
    exact hjk (hj.trans hk.symm)
  simpa [Finset.prod_insert, hjk, hsets] using
    signProduct_orthogonality ({l} : Finset V) {j, k}

/-- The actual linear and quadratic parts of the supplied score have zero cross moment.  [For the stated data and conditions](hyp:θ), [the stated conclusion holds](goal). -/
-- @node: oracle_mixed_second_moment_zero
lemma oracle_mixed_second_moment_zero (θ : Schedule V) :
    (∫ z, (∑ i, oracleMu θ i * ∑ l ∈ oracleNbhd θ i, signOf (z l)) *
      (∑ i, ∑ j ∈ oracleNbhd θ i, ∑ k ∈ (oracleNbhd θ i).erase j,
        oracleBeta θ i j * signOf (z j) * signOf (z k))
      ∂halfBernoulli V) = 0 := by
  simp_rw [oracle_linear_collect, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _)]
  apply Finset.sum_eq_zero
  intro l _
  rw [integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _)]
  apply Finset.sum_eq_zero
  intro j hj
  rw [integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _)]
  apply Finset.sum_eq_zero
  intro k hk
  have he : (fun z : Assign V => (oracleLinearCoefficient θ l * signOf (z l)) *
      (oracleBeta θ i j * signOf (z j) * signOf (z k))) =
      fun z => (oracleLinearCoefficient θ l * oracleBeta θ i j) *
        (signOf (z l) * (signOf (z j) * signOf (z k))) := by funext z; ring
  rw [he, integral_const_mul, integral_oracle_sign_triple l j k
    (Ne.symm (Finset.mem_erase.mp hk).1), mul_zero]

/-- The ordered-pair coefficient retains the true augmented-neighborhood incidences. -/
-- @node: oracleQuadraticCoefficient
def oracleQuadraticCoefficient (θ : Schedule V) (j k : V) : ℝ :=
  ∑ i ∈ Finset.univ.filter
    (fun i => j ∈ oracleNbhd θ i ∧ k ∈ (oracleNbhd θ i).erase j), oracleBeta θ i j

/-- Diagonal coordinates have already contributed to the causal target.  [For the stated data and conditions](hyp:θ,j), [the stated conclusion holds](goal). -/
-- @node: oracleQuadraticCoefficient_diag
lemma oracleQuadraticCoefficient_diag (θ : Schedule V) (j : V) :
    oracleQuadraticCoefficient θ j j = 0 := by
  simp [oracleQuadraticCoefficient]

/-- Collecting the quadratic monomials by ordered source pair changes no graph incidence.  [For the stated data and conditions](hyp:θ,z), [the stated conclusion holds](goal). -/
-- @node: oracle_quadratic_collect
lemma oracle_quadratic_collect (θ : Schedule V) (z : Assign V) :
    (∑ i, ∑ j ∈ oracleNbhd θ i, ∑ k ∈ (oracleNbhd θ i).erase j,
      oracleBeta θ i j * signOf (z j) * signOf (z k)) =
      ∑ j, ∑ k, oracleQuadraticCoefficient θ j k * signOf (z j) * signOf (z k) := by
  have hs (s : Finset V) (f : V → ℝ) :
      (∑ j ∈ s, f j) = ∑ j : V, if j ∈ s then f j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  have hrow (i : V) :
      (∑ j ∈ oracleNbhd θ i, ∑ k ∈ (oracleNbhd θ i).erase j,
        oracleBeta θ i j * signOf (z j) * signOf (z k)) =
      ∑ j : V, ∑ k : V, if j ∈ oracleNbhd θ i ∧ k ∈ (oracleNbhd θ i).erase j
        then oracleBeta θ i j * signOf (z j) * signOf (z k) else 0 := by
    rw [hs]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ oracleNbhd θ i
    · rw [if_pos hj, hs]
      apply Finset.sum_congr rfl
      intro k _
      simp only [hj, true_and]
    · simp [hj]
  simp_rw [hrow]
  simp only [oracleQuadraticCoefficient, Finset.sum_filter, Finset.sum_mul,
    ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

/-- Equal unordered pairs are precisely the two orientations of an ordered pair.  [For the stated data and conditions](hyp:j,k,a,b), [the stated conclusion holds](goal). -/
-- @node: oracle_pair_eq_iff
lemma oracle_pair_eq_iff (j k a b : V) :
    ({j, k} : Finset V) = {a, b} ↔ (j = a ∧ k = b) ∨ (j = b ∧ k = a) := by
  rw [← Finset.coe_inj]
  simpa only [Finset.coe_pair] using
    (Set.pair_eq_pair_iff : ({j, k} : Set V) = {a, b} ↔ _)

/-- The fourth sign moment matches the two orientations, with no other surviving pairs.  [For the stated data and conditions](hyp:j,k,a,b,hjk,hab), [the stated conclusion holds](goal). -/
-- @node: integral_oracle_sign_four
lemma integral_oracle_sign_four (j k a b : V) (hjk : j ≠ k) (hab : a ≠ b) :
    (∫ z, (signOf (z j) * signOf (z k)) * (signOf (z a) * signOf (z b))
      ∂halfBernoulli V) =
      if (j = a ∧ k = b) ∨ (j = b ∧ k = a) then 1 else 0 := by
  simpa [Finset.prod_insert, hjk, hab, oracle_pair_eq_iff] using
    signProduct_orthogonality ({j, k} : Finset V) {a, b}

/-- Summing the fourth moments leaves both orientations of each non-diagonal pair.  [For the stated data and conditions](hyp:θ,j,k,hjk), [the stated conclusion holds](goal). -/
-- @node: oracle_quadratic_inner_moment
lemma oracle_quadratic_inner_moment (θ : Schedule V) (j k : V) (hjk : j ≠ k) :
    (∫ z, (signOf (z j) * signOf (z k)) *
      (∑ a, ∑ b, oracleQuadraticCoefficient θ a b * signOf (z a) * signOf (z b))
      ∂halfBernoulli V) =
      oracleQuadraticCoefficient θ j k + oracleQuadraticCoefficient θ k j := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _)]
  have hterm (a b : V) :
      (∫ z, (signOf (z j) * signOf (z k)) *
        (oracleQuadraticCoefficient θ a b * signOf (z a) * signOf (z b))
        ∂halfBernoulli V) =
      (if j = a ∧ k = b then oracleQuadraticCoefficient θ a b else 0) +
      (if j = b ∧ k = a then oracleQuadraticCoefficient θ a b else 0) := by
    by_cases hab : a = b
    · subst b
      simp only [oracleQuadraticCoefficient_diag, zero_mul, mul_zero, integral_zero]
      simp
    · have he : (fun z : Assign V => (signOf (z j) * signOf (z k)) *
          (oracleQuadraticCoefficient θ a b * signOf (z a) * signOf (z b))) =
          fun z => oracleQuadraticCoefficient θ a b *
            ((signOf (z j) * signOf (z k)) * (signOf (z a) * signOf (z b))) := by
        funext z; ring
      rw [he, integral_const_mul, integral_oracle_sign_four j k a b hjk hab]
      by_cases h1 : j = a ∧ k = b <;> by_cases h2 : j = b ∧ k = a
      · exact False.elim (hjk (h1.1.trans h2.2.symm))
      all_goals simp only [h1, h2, true_or, or_true, false_or, or_false,
        if_true, if_false, mul_one, mul_zero, add_zero, zero_add,
        hab, Ne.symm hab, and_self, false_and, and_false]
  simp_rw [integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _), hterm,
    Finset.sum_add_distrib]
  simp_rw [ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- Exact quadratic energy: ordered coefficients pair with their reverse orientation.  [For the stated data and conditions](hyp:θ), [the stated conclusion holds](goal). -/
-- @node: oracle_quadratic_second_moment
lemma oracle_quadratic_second_moment (θ : Schedule V) :
    (∫ z, (∑ i, ∑ j ∈ oracleNbhd θ i, ∑ k ∈ (oracleNbhd θ i).erase j,
      oracleBeta θ i j * signOf (z j) * signOf (z k)) ^ 2 ∂halfBernoulli V) =
      ∑ j, ∑ k, oracleQuadraticCoefficient θ j k *
        (oracleQuadraticCoefficient θ j k + oracleQuadraticCoefficient θ k j) := by
  simp_rw [oracle_quadratic_collect, pow_two, Finset.sum_mul]
  rw [integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _)]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : j = k
  · subst k
    simp [oracleQuadraticCoefficient_diag]
  · have he : (fun z : Assign V =>
        (oracleQuadraticCoefficient θ j k * signOf (z j) * signOf (z k)) *
          (∑ a, ∑ b, oracleQuadraticCoefficient θ a b * signOf (z a) * signOf (z b))) =
        fun z => oracleQuadraticCoefficient θ j k *
          ((signOf (z j) * signOf (z k)) *
            (∑ a, ∑ b, oracleQuadraticCoefficient θ a b * signOf (z a) * signOf (z b))) := by
      funext z; ring
    rw [he, integral_const_mul, oracle_quadratic_inner_moment θ j k hjk]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
