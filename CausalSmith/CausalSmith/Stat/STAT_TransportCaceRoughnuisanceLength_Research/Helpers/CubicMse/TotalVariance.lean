module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.VarianceRates
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.VarianceAggregation

/-! # Aggregation of the three exact centered correction variances

The heterogeneous Cauchy--Schwarz inequality retains the three distinct
paper constants and does not require independence between corrections.
-/

public section

open MeasureTheory
open scoped BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Conditional second moments of a finite sum are bounded by the cardinality
 times the sum of the individual bounds, even for dependent summands.  Under [the displayed assumptions and inputs](hyp:Ω,m,s,Y,B,hY,hb), [the stated conclusion holds](goal). -/
-- @node: condExp_sq_finsetSum_le_sum_bounds
lemma condExp_sq_finsetSum_le_sum_bounds
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : MeasurableSpace Ω} (s : Finset ι) (Y : ι → Ω → ℝ) (B : ι → ℝ)
    (hY : ∀ i ∈ s, MemLp (Y i) 2 μ)
    (hb : ∀ i ∈ s, ∀ᵐ x ∂μ,
      condExp m μ (fun y => (Y i y) ^ 2) x ≤ B i) :
    ∀ᵐ x ∂μ,
      condExp m μ (fun y => (∑ i ∈ s, Y i y) ^ 2) x ≤
        (s.card : ℝ) * ∑ i ∈ s, B i := by
  have hYsq : ∀ i ∈ s, Integrable (fun x => (Y i x) ^ 2) μ :=
    fun i hi => (hY i hi).integrable_sq
  let Q : Ω → ℝ := (s.card : ℝ) • (fun y => ∑ i ∈ s, (Y i y) ^ 2)
  have hsumSq : Integrable (fun y => ∑ i ∈ s, (Y i y) ^ 2) μ :=
    integrable_finsetSum s hYsq
  have hQ : Integrable Q μ := hsumSq.const_mul _
  have hsumLp : MemLp (fun y => ∑ i ∈ s, Y i y) 2 μ :=
    memLp_finsetSum s hY
  have hleft : Integrable (fun y => (∑ i ∈ s, Y i y) ^ 2) μ :=
    hsumLp.integrable_sq
  have hmono := condExp_mono hleft hQ (by
    filter_upwards [] with y
    exact sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => Y i y)) (m := m)
  have hsum := condExp_finsetSum (μ := μ) (s := s)
    (f := fun i y => (Y i y) ^ 2) hYsq m
  have hscale := condExp_smul (μ := μ) (s.card : ℝ)
    (fun y => ∑ i ∈ s, (Y i y) ^ 2) m
  have hall : ∀ᵐ x ∂μ, ∀ i ∈ s,
      condExp m μ (fun y => (Y i y) ^ 2) x ≤ B i := by
    exact (eventually_finset_ball).2 hb
  filter_upwards [hmono, hsum, hscale, hall] with x hmono hsum hscale hall
  change condExp m μ Q x = _ at hscale
  simp only [Pi.smul_apply, smul_eq_mul] at hscale
  have hsum' : condExp m μ (fun y => ∑ i ∈ s, (Y i y) ^ 2) x =
      ∑ i ∈ s, condExp m μ (fun y => (Y i y) ^ 2) x := by
    simpa only [Finset.sum_fn, Finset.sum_apply] using hsum
  rw [hscale, hsum'] at hmono
  have hsumle : (∑ i ∈ s, condExp m μ (fun y => (Y i y) ^ 2) x) ≤
      ∑ i ∈ s, B i := Finset.sum_le_sum fun i hi => hall i hi
  calc
    condExp m μ (fun y => (∑ i ∈ s, Y i y) ^ 2) x ≤
        (s.card : ℝ) * ∑ i ∈ s, condExp m μ (fun y => (Y i y) ^ 2) x := hmono
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, B i :=
      mul_le_mul_of_nonneg_left hsumle (Nat.cast_nonneg _)

/-- Roadmap (20) for the sum of the three exact conditionally centered
corrections. Square integrability is derived from the component proofs.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: centered_corrections_conditional_second_moment_sample_rate
lemma centered_corrections_conditional_second_moment_sample_rate
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    ∀ᵐ ω ∂dataLaw P n n,
      condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ : TwoSample n n =>
          ((linearTerm c_f C_f ξ A -
            condExp (trainingSigma n) (dataLaw P n n)
              (fun ζ => linearTerm c_f C_f ζ A) ξ) +
           (quadraticTerm c_f C_f ξ A -
            condExp (trainingSigma n) (dataLaw P n n)
              (fun ζ => quadraticTerm c_f C_f ζ A) ξ) +
           (cubicTerm c_f C_f ξ A -
            condExp (trainingSigma n) (dataLaw P n n)
              (fun ζ => cubicTerm c_f C_f ζ A) ξ)) ^ 2) ω ≤
        3 * (10 * (7 : ℝ) ^ 2 * (fourthDerivativeEnvelope c_f C_f) ^ 2 +
          60 * quadVarianceConstant c_f C_f +
          310 * cubicVarianceConstant c_f C_f) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  classical
  let μ := dataLaw P n n
  let m := trainingSigma n
  letI : MeasurableSpace (TwoSample n n) := Prod.instMeasurableSpace
  let F : Fin 3 → TwoSample n n → ℝ :=
    ![fun ξ => linearTerm c_f C_f ξ A,
      fun ξ => quadraticTerm c_f C_f ξ A,
      fun ξ => cubicTerm c_f C_f ξ A]
  let Y : Fin 3 → TwoSample n n → ℝ := fun i ξ => F i ξ - condExp m μ (F i) ξ
  let B : Fin 3 → ℝ :=
    ![10 * (7 : ℝ) ^ 2 * (fourthDerivativeEnvelope c_f C_f) ^ 2,
      60 * quadVarianceConstant c_f C_f,
      310 * cubicVarianceConstant c_f C_f]
  have hlp : ∀ i : Fin 3, MemLp (Y i) 2 μ := by
    intro i
    fin_cases i
    · exact (linear_conditional_variance_with_memLp c_f C_f L P n hn hP A).1
    · have hp := (quadratic_conditional_variance_with_memLp c_f C_f L P n hn hP A).1
      exact hp.sub (hp.condExp (by norm_num))
    · have hp := (cubic_conditional_variance_with_memLp c_f C_f L P n hn hP A).1
      exact hp.sub (hp.condExp (by norm_num))
  have hb : ∀ i : Fin 3, ∀ᵐ ω ∂μ,
      condExp m μ (fun ξ => (Y i ξ) ^ 2) ω ≤
        B i * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    intro i
    fin_cases i
    · exact linear_conditional_variance_sample_rate c_f C_f L P n hn hP A
    · exact quadratic_conditional_variance_sample_rate c_f C_f L P n hn hP A
    · exact cubic_conditional_variance_sample_rate c_f C_f L P n hn hP A
  have hagg := condExp_sq_finsetSum_le_sum_bounds
    (μ := μ) (m := m) Finset.univ Y (fun i => B i * (n : ℝ) ^ (-(2 / 3 : ℝ)))
    (fun i _ => hlp i) (fun i _ => hb i)
  simp only [Fin.sum_univ_three] at hagg
  filter_upwards [hagg] with ω hω
  change condExp m μ (fun ξ => (Y 0 ξ + Y 1 ξ + Y 2 ξ) ^ 2) ω ≤ _
  apply hω.trans_eq
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
  dsimp [B]
  ring

/-- Integrating the combined conditional bound gives the expected variance
constant in roadmap (20).  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: centered_corrections_expected_conditional_second_moment_sample_rate
lemma centered_corrections_expected_conditional_second_moment_sample_rate
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    (∫ ω,
      condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ : TwoSample n n =>
          ((linearTerm c_f C_f ξ A -
            condExp (trainingSigma n) (dataLaw P n n)
              (fun ζ => linearTerm c_f C_f ζ A) ξ) +
           (quadraticTerm c_f C_f ξ A -
            condExp (trainingSigma n) (dataLaw P n n)
              (fun ζ => quadraticTerm c_f C_f ζ A) ξ) +
           (cubicTerm c_f C_f ξ A -
            condExp (trainingSigma n) (dataLaw P n n)
              (fun ζ => cubicTerm c_f C_f ζ A) ξ)) ^ 2) ω ∂dataLaw P n n) ≤
        3 * (10 * (7 : ℝ) ^ 2 * (fourthDerivativeEnvelope c_f C_f) ^ 2 +
          60 * quadVarianceConstant c_f C_f +
          310 * cubicVarianceConstant c_f C_f) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  let := sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let := targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
    infer_instance
  have hb := centered_corrections_conditional_second_moment_sample_rate
    c_f C_f L P n hn hP A
  have hi := integral_mono_ae integrable_condExp
    (integrable_const (3 * (10 * (7 : ℝ) ^ 2 *
      (fourthDerivativeEnvelope c_f C_f) ^ 2 +
      60 * quadVarianceConstant c_f C_f +
      310 * cubicVarianceConstant c_f C_f) * (n : ℝ) ^ (-(2 / 3 : ℝ)))) hb
  simpa using hi

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
