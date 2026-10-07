module
public import Causalean.Stat.CLT.FiniteDesignConditioning
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Probability.Process.Filtration

/-!
# Finite-horizon Doob information decomposition

For a square-integrable score under one probability law, this module develops the
finite-horizon decomposition into conditional-expectation increments along an arbitrary
filtration.  It supplies centering, orthogonality, information additivity, a uniform
increment-budget bound, and a density-facing Fisher-information corollary without
disintegration or stagewise Radon–Nikodym derivatives.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.DoobInformation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ) (S : Ω → ℝ)

/-- A [probability law](hyp:μ), [filtration](hyp:F), [terminal score](hyp:S), and
[stage](hyp:k) determine [the Doob score increment](goal), [given by the change in the
score's conditional expectation between the two adjacent prefix σ-algebras](step:1). -/
noncomputable def increment (μ : Measure Ω) (F : Filtration ℕ mΩ) (S : Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => μ[S | F (k + 1)] ω - μ[S | F k] ω

/-- A [probability law](hyp:μ), [filtration](hyp:F), [terminal score](hyp:S),
[square-integrability certificate](hyp:hS), and [horizon](hyp:n) determine [the constant-row
Doob martingale-difference array](goal), [given by the Doob construction in which every row
uses this same law, filtration, and score, has length equal to the horizon, and has as its entry
at each stage the change in the score's conditional expectation between the two adjacent prefix
σ-algebras](step:1). -/
noncomputable def doobArray (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ) (S : Ω → ℝ) (hS : MemLp S 2 μ) (n : ℕ) :
    MartingaleDifferenceArray (fun _ : ℕ => Ω) (fun _ => μ) :=
  doobMartingaleDifferenceArray (μ := fun _ => μ)
    (fun _ => n) (fun _ => F) (fun _ => S) (fun _ => hS)

/-- Given [a probability law](hyp:μ), [filtration](hyp:F), [square-integrable terminal
score](hyp:S,hS), [horizon](hyp:n), and [stage](hyp:k), [the score increment agrees with the
matching entry of its constant-row Doob array](goal). -/
theorem increment_eq_doobArray (hS : MemLp S 2 μ) (n k : ℕ) :
    increment μ F S k = (doobArray μ F S hS n).increment 0 k := by
  rfl

/-- Under [a probability law](hyp:μ) and [filtration](hyp:F), a [square-integrable terminal
score](hyp:S,hS) has [a square-integrable score increment at every stage](goal), including the
specified [stage](hyp:k). -/
theorem increment_memLp (hS : MemLp S 2 μ) (k : ℕ) :
    MemLp (increment μ F S k) 2 μ := by
  rw [increment_eq_doobArray (μ := μ) F S hS (k + 1) k]
  exact (doobArray μ F S hS (k + 1)).squareIntegrable 0 k
    (by simpa [doobArray, doobMartingaleDifferenceArray] using Nat.lt_succ_self k)

/-- Under [a probability law](hyp:μ) and [filtration](hyp:F), a [square-integrable terminal
score](hyp:S,hS) has [an increment measurable at the next prefix σ-algebra](goal) for the
given [stage](hyp:k). -/
theorem increment_stronglyMeasurable (hS : MemLp S 2 μ) (k : ℕ) :
    StronglyMeasurable[F (k + 1)] (increment μ F S k) := by
  rw [increment_eq_doobArray (μ := μ) F S hS (k + 1) k]
  exact (doobArray μ F S hS (k + 1)).adapted 0 k
    (by simpa [doobArray, doobMartingaleDifferenceArray] using Nat.lt_succ_self k)

/-- Under [a probability law](hyp:μ) and [filtration](hyp:F), the increment of a
[square-integrable terminal score](hyp:S,hS) has [conditional mean zero at the preceding
prefix σ-algebra](goal) for the given [stage](hyp:k). -/
theorem increment_condExp_zero (hS : MemLp S 2 μ) (k : ℕ) :
    μ[increment μ F S k | F k] =ᵐ[μ] (0 : Ω → ℝ) := by
  rw [increment_eq_doobArray (μ := μ) F S hS (k + 1) k]
  exact (doobArray μ F S hS (k + 1)).condExp_zero 0 k
    (by simpa [doobArray, doobMartingaleDifferenceArray] using Nat.lt_succ_self k)

/-- Under [a probability law](hyp:μ) and [filtration](hyp:F), the increments of a
[square-integrable terminal score](hyp:S,hS) have [a finite sum equal almost everywhere to the
difference between terminal and initial conditional expectations](goal) at the given
[horizon](hyp:n). -/
theorem increment_sum (hS : MemLp S 2 μ) (n : ℕ) :
    (fun ω => ∑ k ∈ Finset.range n, increment μ F S k ω) =ᵐ[μ]
      (fun ω => μ[S | F n] ω - μ[S | F 0] ω) := by
  have hsum : (fun ω => ∑ k ∈ Finset.range n, increment μ F S k ω) =
      (doobArray μ F S hS n).rowSum 0 := by
    funext ω
    simp only [MartingaleDifferenceArray.rowSum, Finset.sum_apply]
    change (∑ k ∈ Finset.range n, increment μ F S k ω) =
      ∑ k ∈ Finset.range n, (doobArray μ F S hS n).increment 0 k ω
    apply Finset.sum_congr rfl
    intro k _
    exact congrFun (increment_eq_doobArray (μ := μ) F S hS n k) ω
  have hrow := doobMartingaleDifferenceArray_rowSum
    (μ := fun _ => μ) (fun _ => n) (fun _ => F) (fun _ => S) (fun _ => hS) 0
  change (doobArray μ F S hS n).rowSum 0 =
    (fun ω => μ[S | F n] ω - μ[S | F 0] ω) at hrow
  exact Filter.Eventually.of_forall (fun ω => congrFun (hsum.trans hrow) ω)

/-- Under [a probability law](hyp:μ) and [filtration](hyp:F), distinct [stages](hyp:i,j)
of the Doob increments for a [square-integrable terminal score](hyp:S,hS) are [orthogonal in
the squared-integrable sense](goal), whenever [the two stages differ](hyp:hij). -/
theorem increment_orthogonal (hS : MemLp S 2 μ) {i j : ℕ} (hij : i ≠ j) :
    ∫ ω, increment μ F S i ω * increment μ F S j ω ∂μ = 0 := by
  have hforward {a b : ℕ} (hab : a < b) :
      ∫ ω, increment μ F S a ω * increment μ F S b ω ∂μ = 0 := by
    have hm : F (a + 1) ≤ F b := F.mono (Nat.succ_le_of_lt hab)
    have hmeas : StronglyMeasurable[F b] (increment μ F S a) :=
      (increment_stronglyMeasurable (μ := μ) F S hS a).mono hm
    have ha := increment_memLp (μ := μ) F S hS a
    have hb := increment_memLp (μ := μ) F S hS b
    have hprod : Integrable (increment μ F S a * increment μ F S b) μ :=
      ha.integrable_mul hb
    have hpull := condExp_mul_of_stronglyMeasurable_left hmeas hprod
      (hb.integrable (by norm_num))
    calc
      ∫ ω, increment μ F S a ω * increment μ F S b ω ∂μ =
          ∫ ω, μ[increment μ F S a * increment μ F S b | F b] ω ∂μ := by
            exact (integral_condExp (F.le b)).symm
      _ = ∫ ω, increment μ F S a ω * μ[increment μ F S b | F b] ω ∂μ :=
        integral_congr_ae hpull
      _ = 0 := by
        have hz : (fun ω => increment μ F S a ω * μ[increment μ F S b | F b] ω) =ᵐ[μ]
            (0 : Ω → ℝ) := by
          filter_upwards [increment_condExp_zero (μ := μ) F S hS b] with ω hω
          simp only [Pi.zero_apply] at hω
          simp [hω]
        rw [integral_congr_ae hz]
        simp
  rcases lt_or_gt_of_ne hij with h | h
  · exact hforward h
  · rw [show (fun ω => increment μ F S i ω * increment μ F S j ω) =
        (fun ω => increment μ F S j ω * increment μ F S i ω) from funext
        (fun ω => mul_comm _ _)]
    exact hforward h

/-- Under [a probability law](hyp:μ) and [filtration](hyp:F), if a
[square-integrable terminal score](hyp:S,hS) is [its terminal conditional expectation](hyp:hterminal)
and has [zero initial conditional expectation](hyp:hinitial), then [its Fisher-information
second moment, the expectation of the squared score, equals the sum over the stages before the
horizon of the increment second moments](goal) at the given [horizon](hyp:n).

The terminal hypothesis says the score agrees almost surely with its conditional expectation given
the σ-algebra at the horizon, and the initial hypothesis says its conditional expectation given
the σ-algebra at stage zero vanishes almost surely. -/
theorem fisher_eq_sum (hS : MemLp S 2 μ) (n : ℕ)
    (hterminal : μ[S | F n] =ᵐ[μ] S)
    (hinitial : μ[S | F 0] =ᵐ[μ] (0 : Ω → ℝ)) :
    ∫ ω, S ω ^ 2 ∂μ =
      ∑ k ∈ Finset.range n, ∫ ω, increment μ F S k ω ^ 2 ∂μ := by
  let d : ℕ → Ω → ℝ := increment μ F S
  let t : ℕ → Ω → ℝ := fun r ω => ∑ k ∈ Finset.range r, d k ω
  have hd (k : ℕ) : MemLp (d k) 2 μ := increment_memLp (μ := μ) F S hS k
  have ht (r : ℕ) : MemLp (t r) 2 μ := by
    induction r with
    | zero => simp [t]
    | succ r ihr =>
        convert ihr.add (hd r) using 1
        funext ω
        simp [t, Finset.sum_range_succ]
  have hsq (r : ℕ) :
      ∫ ω, t r ω ^ 2 ∂μ = ∑ k ∈ Finset.range r, ∫ ω, d k ω ^ 2 ∂μ := by
    induction r with
    | zero => simp [t]
    | succ r ihr =>
        have hcross : ∫ ω, t r ω * d r ω ∂μ = 0 := by
          calc
            _ = ∫ ω, ∑ k ∈ Finset.range r, d k ω * d r ω ∂μ := by
              congr 1
              funext ω
              simp [t, Finset.sum_mul]
            _ = ∑ k ∈ Finset.range r, ∫ ω, d k ω * d r ω ∂μ := by
              exact integral_finsetSum _ (by
                intro k hk
                exact (hd k).integrable_mul (hd r))
            _ = 0 := by
              apply Finset.sum_eq_zero
              intro k hk
              exact increment_orthogonal (μ := μ) F S hS
                (Nat.ne_of_lt (Finset.mem_range.mp hk))
        have hrr : Integrable (fun ω => t r ω * t r ω) μ :=
          (ht r).integrable_mul (ht r)
        have hrd : Integrable (fun ω => t r ω * d r ω) μ :=
          (ht r).integrable_mul (hd r)
        have hdr : Integrable (fun ω => d r ω * t r ω) μ :=
          (hd r).integrable_mul (ht r)
        have hdd : Integrable (fun ω => d r ω * d r ω) μ :=
          (hd r).integrable_mul (hd r)
        calc
          ∫ ω, t (r + 1) ω ^ 2 ∂μ =
              ∫ ω, (t r ω * t r ω + t r ω * d r ω) +
                (d r ω * t r ω + d r ω * d r ω) ∂μ := by
                congr 1
                funext ω
                simp only [t, Finset.sum_range_succ]
                ring
          _ = (∫ ω, t r ω * t r ω ∂μ) +
                (∫ ω, t r ω * d r ω ∂μ) +
                (∫ ω, d r ω * t r ω ∂μ) +
                (∫ ω, d r ω * d r ω ∂μ) := by
                have houter := integral_add (hrr.add hrd) (hdr.add hdd)
                have hleft := integral_add hrr hrd
                have hright := integral_add hdr hdd
                simpa only [Pi.add_apply, hleft, hright, add_assoc] using houter
          _ = ∑ k ∈ Finset.range (r + 1), ∫ ω, d k ω ^ 2 ∂μ := by
                rw [hcross]
                have hcross' : ∫ ω, d r ω * t r ω ∂μ = 0 := by
                  convert hcross using 1
                  congr 1
                  funext ω
                  ring
                rw [hcross']
                simp only [← pow_two, add_zero, Finset.sum_range_succ]
                exact congrArg (· + ∫ ω, d r ω ^ 2 ∂μ) ihr
  have hae : t n =ᵐ[μ] S := by
    filter_upwards [increment_sum (μ := μ) F S hS n, hterminal, hinitial] with
      ω hsum hterm hinit
    dsimp [t, d] at hsum ⊢
    rw [hsum, hterm, hinit]
    simp
  calc
    ∫ ω, S ω ^ 2 ∂μ = ∫ ω, t n ω ^ 2 ∂μ :=
      integral_congr_ae (by
        filter_upwards [hae] with ω hw
        rw [hw])
    _ = ∑ k ∈ Finset.range n, ∫ ω, increment μ F S k ω ^ 2 ∂μ := hsq n

/-- Under [a probability law](hyp:μ) and [filtration](hyp:F), if a
[square-integrable terminal score](hyp:S,hS) has [the terminal and initial conditional-expectation
identities](hyp:hterminal,hinitial) and [each active increment's second moment is bounded](hyp:hbound),
then [the score's Fisher information is at most the horizon times the common bound](goal) for the
given [horizon](hyp:n) and [bound](hyp:B). -/
theorem fisher_le_mul (hS : MemLp S 2 μ) (n : ℕ) (B : ℝ)
    (hterminal : μ[S | F n] =ᵐ[μ] S)
    (hinitial : μ[S | F 0] =ᵐ[μ] (0 : Ω → ℝ))
    (hbound : ∀ k < n, ∫ ω, increment μ F S k ω ^ 2 ∂μ ≤ B) :
    ∫ ω, S ω ^ 2 ∂μ ≤ (n : ℝ) * B := by
  rw [fisher_eq_sum (μ := μ) F S hS n hterminal hinitial]
  calc
    ∑ k ∈ Finset.range n, ∫ ω, increment μ F S k ω ^ 2 ∂μ ≤
        ∑ _k ∈ Finset.range n, B := by
          apply Finset.sum_le_sum
          intro k hk
          exact hbound k (Finset.mem_range.mp hk)
    _ = (n : ℝ) * B := by simp

variable {ν : Measure Ω} [IsFiniteMeasure ν]

/-- A [finite reference measure](hyp:ν), [probability law](hyp:μ), [density](hyp:q),
[density derivative](hyp:qdot), and [score](hyp:S) with [a measurable density](hyp:hq),
[the stated density representation](hyp:hμ), [almost-everywhere nonnegative density](hyp:hqnonneg),
and [almost-everywhere score identity](hyp:hscore) have [a
guarded density Fisher integral equal to the score second moment](goal).

Square integrability of the score is not assumed: when the squared score is not integrable under
the probability law, both sides are zero by the convention that the integral of a non-integrable
function is zero. -/
theorem guarded_density_fisher_eq
    (q qdot S : Ω → ℝ)
    (hq : Measurable q)
    (hμ : μ = ν.withDensity (fun ω => ENNReal.ofReal (q ω)))
    (hqnonneg : ∀ᵐ ω ∂ν, 0 ≤ q ω)
    (hscore : ∀ᵐ ω ∂ν, qdot ω = q ω * S ω) :
    (∫ ω, (if q ω = 0 then 0 else qdot ω ^ 2 / q ω) ∂ν) =
      ∫ ω, S ω ^ 2 ∂μ := by
  have hquot :
      (fun ω => if q ω = 0 then 0 else qdot ω ^ 2 / q ω) =ᵐ[ν]
        (fun ω => q ω * S ω ^ 2) := by
    filter_upwards [hscore] with ω hs
    by_cases hq0 : q ω = 0
    · simp [hq0]
    · rw [hs]
      simp only [hq0, ↓reduceIte]
      field_simp
  calc
    (∫ ω, (if q ω = 0 then 0 else qdot ω ^ 2 / q ω) ∂ν) =
        ∫ ω, q ω * S ω ^ 2 ∂ν := integral_congr_ae hquot
    _ = ∫ ω, S ω ^ 2 ∂μ := by
      rw [hμ, integral_withDensity_eq_integral_toReal_smul hq.ennreal_ofReal
        (by simp)]
      apply integral_congr_ae
      filter_upwards [hqnonneg] with ω hn
      simp [ENNReal.toReal_ofReal hn, smul_eq_mul]

/-- A [finite reference measure](hyp:ν), [probability law](hyp:μ), [filtration](hyp:F),
[horizon](hyp:n), [density](hyp:q), [density derivative](hyp:qdot), and [score](hyp:S) with
[a measurable density](hyp:hq), [the law having density q with respect to the
reference measure](hyp:hμ), [almost-everywhere nonnegative density](hyp:hqnonneg), [the score
identity that the density derivative equals the density times the score almost everywhere under
the reference measure](hyp:hscore), [square-integrable score under the law](hyp:hS), and [the
score agreeing almost surely with its conditional expectation at the horizon while its conditional
expectation at stage zero vanishes almost surely](hyp:hterminal,hinitial)
have [a guarded density Fisher integral, the reference-measure integral of the squared density
derivative divided by the density with the integrand set to zero where the density vanishes, equal
to the sum over the stages before the horizon of the second moments of the Doob score
increments](goal). -/
theorem guarded_density_fisher_eq_doob_sum
    (F : Filtration ℕ mΩ) (n : ℕ) (q qdot S : Ω → ℝ)
    (hq : Measurable q)
    (hμ : μ = ν.withDensity (fun ω => ENNReal.ofReal (q ω)))
    (hqnonneg : ∀ᵐ ω ∂ν, 0 ≤ q ω)
    (hscore : ∀ᵐ ω ∂ν, qdot ω = q ω * S ω)
    (hS : MemLp S 2 μ)
    (hterminal : μ[S | F n] =ᵐ[μ] S)
    (hinitial : μ[S | F 0] =ᵐ[μ] (0 : Ω → ℝ)) :
    (∫ ω, (if q ω = 0 then 0 else qdot ω ^ 2 / q ω) ∂ν) =
      ∑ k ∈ Finset.range n, ∫ ω, increment μ F S k ω ^ 2 ∂μ := by
  rw [guarded_density_fisher_eq q qdot S hq hμ hqnonneg hscore]
  exact fisher_eq_sum F S hS n hterminal hinitial

end Causalean.Stat.DoobInformation
