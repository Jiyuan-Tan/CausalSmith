module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.CanonicalIdentification
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.TaylorRemainder

/-!
# Taylor remainders of the canonical transcript density

The finite original-record representation has integrable coordinate coefficients.
Its derivative certificate therefore supplies the exact coordinate L1 Taylor
remainder needed before moment cancellation and coordinate telescoping.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Kernel.FiniteSequence
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- Assume [measurability of f](hyp:hf), [the function hf0](hyp:hf0), and [the function hrow](hyp:hrow). [Each nonnegative fixed-record RN density is integrable because its represented transcript law is a probability measure](goal). -/
-- @node: integrable_fixedTranscript_row_density
lemma integrable_fixedTranscript_row_density (Q : LocalProtocol n (ObsRecord d))
    (f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ)
    (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w)
    (hrow : ∀ o r, (referenceLaw Q r).withDensity
      (fun z => ENNReal.ofReal (f ((o, r), z))) = fixedTranscriptLaw Q o r)
    (o : Fin n → ObsRecord d) (r : Q.Seed) :
    Integrable (fun z => f ((o, r), z)) (referenceLaw Q r) := by
  refine ⟨(hf.comp (by fun_prop)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun z => hf0 _))]
  have h := congrArg (fun mu : Measure (ProtocolTranscript Q) => mu Set.univ) (hrow o r)
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  rw [h]
  have : IsProbabilityMeasure (fixedTranscriptLaw Q o r) :=
    Causalean.Mathlib.Probability.Kernel.FiniteSequence.isProbabilityMeasure_transcriptLaw
      Q.kernels Q.markov (fun i => (o i, r))
  exact measure_lt_top _ _

/-- Assume [measurability of f](hyp:hf), [the function hf0](hyp:hf0), and [the function hrow](hyp:hrow). [The canonical density's polynomial coefficients are finite linear combinations of integrable fixed-record row densities](goal). -/
-- @node: canonicalTranscriptDensity_integrable_coordinate_polynomial
lemma canonicalTranscriptDensity_integrable_coordinate_polynomial
    (Q : LocalProtocol n (ObsRecord d))
    (f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ)
    (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w)
    (hrow : ∀ o r, (referenceLaw Q r).withDensity
      (fun z => ENNReal.ofReal (f ((o, r), z))) = fixedTranscriptLaw Q o r)
    (theta : Fin d → ℝ) (r : Q.Seed) (j : Fin d) :
    ∃ c : Fin (n + 1) → ProtocolTranscript Q → ℝ,
      (∀ q, Integrable (c q) (referenceLaw Q r)) ∧ ∀ x z,
      canonicalTranscriptDensity f (Function.update theta j x, r, z) =
        ∑ q, c q z * x^q.val := by
  classical
  choose c hc using fun o : Fin n → ObsRecord d =>
    iidAffineMass_coordinate_polynomial theta o j
  refine ⟨fun q z => ∑ o, c o q * f ((o, r), z), ?_, ?_⟩
  · intro q
    exact integrable_finsetSum _ (fun o _ =>
      (integrable_fixedTranscript_row_density Q f hf hf0 hrow o r).const_mul _)
  · intro x z
    simp only [canonicalTranscriptDensity]
    simp_rw [hc, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro o _
    ring

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [sequential local privacy of the protocol](hyp:hQ), and [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [The explicitly constructed canonical density has the same adaptive martingale derivative certificate as the existing density version. This retains the finite original-record polynomial as the source of every derivative](goal). -/
-- @node: canonical_density_certificate_rows_of_gate
lemma canonical_density_certificate_rows_of_gate (hRN : MeasurableKernelRadonNikodym)
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ) (hQ : SequentialClass Q eps)
    (hAllowed : Allowed n d eps) :
    ∃ f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ,
      Measurable f ∧ (∀ w, 0 ≤ f w) ∧
      (∀ o r, (referenceLaw Q r).withDensity
        (fun z => ENNReal.ofReal (f ((o, r), z))) = fixedTranscriptLaw Q o r) ∧
      DensityCertificate Q eps (canonicalTranscriptDensity f) := by
  have hd : 0 < d := by have := hAllowed.2.1; omega
  have heps : 0 ≤ eps := le_of_lt hAllowed.2.2.1
  obtain ⟨f, hf, hf0, hrow⟩ := fixedTranscript_row_densities_of_gate hRN Q hd
  let p := canonicalTranscriptDensity f
  have hp : Measurable p := measurable_canonicalTranscriptDensity f hf
  have hrep : ∀ theta ∈ parameterCube d, ∀ r,
      (∀ z, 0 ≤ p (theta, r, z)) ∧
      (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal (p (theta, r, z))) =
        conditionalTranscriptLaw Q theta r := by
    intro theta htheta r
    exact ⟨fun z => canonicalTranscriptDensity_nonneg f
      (fun o r z => hf0 ((o, r), z)) theta htheta r z,
      canonicalTranscriptDensity_withDensity f hf (fun o r z => hf0 ((o, r), z))
        hrow theta htheta hd r⟩
  have hpoly : ∀ theta r z j, ∃ c : Fin (n + 1) → ℝ, ∀ x,
      p (Function.update theta j x, r, z) = ∑ q, c q * x^q.val :=
    canonicalTranscriptDensity_coordinate_polynomial f
  obtain ⟨g, hg, hbound, hsum, hpriv, hgrow, href, hprod⟩ :=
    originalTranscript_stageProduct_of_gate hRN Q hd eps heps hQ
  have hcoord (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
      (r : Q.Seed) (j : Fin d) : ∀ᵐ z ∂referenceLaw Q r, ∀ x,
      p (Function.update theta j x, r, z) = ∏ i : Fin n,
        stageMixtureDensity (Function.update theta j x)
          (fun a => g i (((a, r), take (Nat.le_of_lt i.isLt) z), z i)) :=
    transcript_coordinate_ae_eq_stageProduct Q hd theta htheta r j p hp
      (fun t ht => hrep t ht r) (fun z => hpoly theta r z j) g hg
      (fun i w => le_trans (le_of_lt (Real.exp_pos _)) (hbound i w).1)
      (fun t ht => hprod t ht r)
  refine ⟨f, hf, hf0, hrow, hp, hrep, hpoly, ?_, ?_⟩
  · intro theta htheta r j k hk hkn
    have hpos (z : ProtocolTranscript Q) (i : Fin n) :
        0 < stageMixtureDensity theta
          (fun a => g i (((a, r), take (Nat.le_of_lt i.isLt) z), z i)) :=
      (originalTranscript_stageScore_bound Q hd theta htheta eps heps g
        (fun i w => (hbound i w).1) hpriv r z i j).1
    rw [canonical_densityDerivative_integral_abs_score Q p hp theta r j k
      (hrep theta htheta r).1 (hrep theta htheta r).2
      (fun z i a => g i (((a, r), take (Nat.le_of_lt i.isLt) z), z i))
      hpos (hcoord theta htheta r j)]
    have hchain := originalTranscript_eq_parameterChain Q hd theta htheta r
      g hg (fun i w => le_trans (le_of_lt (Real.exp_pos _)) (hbound i w).1)
      (fun i a eta => hgrow i a r eta) (href r) (hprod theta htheta r)
    have hfirst := originalTranscript_scoreElementary_firstMoment Q hd theta htheta r
      eps heps g hg hbound hpriv (fun i a eta => hgrow i a r eta) hchain j k
    change (∫ z, |scoreElementary (fun v => transcriptCoordinateScore Q theta r g j v z)
      n k| ∂conditionalTranscriptLaw Q theta r) ≤ _ at hfirst
    calc
      _ ≤ (k.factorial : ℝ) *
          (Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k) :=
        mul_le_mul_of_nonneg_left hfirst (by positivity)
      _ = _ := by ring
  · exact densityDerivative_eq_zero_of_coordinate_polynomial p hpoly

/-- Assume [a nonnegative privacy budget](hyp:heps), [measurability of f](hyp:hf), [the function hf0](hyp:hf0), [the function hrow](hyp:hrow), [the stated hcert condition](hyp:hcert), [the stated htheta condition](hyp:htheta), [the stated hk condition](hyp:hk), [order no larger than the sample size](hyp:hkn), [amplitude between zero and one half](hyp:ha), and [the stated hu condition](hyp:hu). [The canonical density certificate controls each coordinate Taylor remainder uniformly in the other coordinates, transcript seed, and signed amplitude](goal). -/
-- @node: canonical_density_coordinate_taylor_L1
lemma canonical_density_coordinate_taylor_L1
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ) (heps : 0 ≤ eps)
    (f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ)
    (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w)
    (hrow : ∀ o r, (referenceLaw Q r).withDensity
      (fun z => ENNReal.ofReal (f ((o, r), z))) = fixedTranscriptLaw Q o r)
    (hcert : DensityCertificate Q eps (canonicalTranscriptDensity f))
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (r : Q.Seed) (j : Fin d)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (a u : ℝ) (ha : a ∈ Set.Ioc 0 (1 / 2 : ℝ)) (hu : u ∈ Set.Icc (-a) a) :
    (∫ z, |canonicalTranscriptDensity f (Function.update theta j u, r, z) -
      ∑ q ∈ Finset.range k,
        densityDerivative (canonicalTranscriptDensity f) (Function.update theta j 0) r z j q /
          (q.factorial : ℝ) * u^q| ∂referenceLaw Q r) ≤
      |u|^k * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k := by
  classical
  obtain ⟨c, hc, heval⟩ := canonicalTranscriptDensity_integrable_coordinate_polynomial
    Q f hf hf0 hrow theta r j
  have hcube (x : ℝ) (hx : x ∈ Set.Icc (-a) a) :
      Function.update theta j x ∈ parameterCube d := by
    intro b
    by_cases hb : b = j
    · subst b
      simp only [Function.update_self]
      constructor <;> linarith [hx.1, hx.2, ha.2]
    · rw [Function.update_of_ne hb]
      exact htheta b
  have hD (x : ℝ) (z : ProtocolTranscript Q) (v : ℕ) :
      densityDerivative (canonicalTranscriptDensity f) (Function.update theta j x) r z j v =
        iteratedDeriv v (fun t : ℝ => ∑ q, c q z * t^q.val) x := by
    simp only [densityDerivative, Function.update_idem, Function.update_self]
    rw [show (fun t => canonicalTranscriptDensity f (Function.update theta j t, r, z)) =
      (fun t : ℝ => ∑ q, c q z * t^q.val) from funext (fun t => heval t z)]
  have hbeta : 0 ≤ derivativeScale d eps := by
    unfold derivativeScale
    exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr heps)) (by positivity)
  have hbound := finitePolynomial_taylor_remainder_L1 (referenceLaw Q r) (n + 1) c hc
    k hk a (Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k) u
    (le_of_lt ha.1) hu (by positivity) (fun x hx => by
      simpa only [hD, mul_assoc] using hcert.2.2.2.1
        (Function.update theta j x) (hcube x hx) r j k hk hkn)
  simpa only [densityDerivative, Function.update_idem, Function.update_self, heval, mul_assoc]
    using hbound

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [sequential local privacy of the protocol](hyp:hQ), and [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [The RN gate supplies a full density certificate together with the exact L1 Taylor remainder required by the moment-mixture argument](goal). -/
-- @node: density_coordinate_taylor_of_gate
lemma density_coordinate_taylor_of_gate (hRN : MeasurableKernelRadonNikodym)
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ) (hQ : SequentialClass Q eps)
    (hAllowed : Allowed n d eps) :
    ∃ p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ,
      DensityCertificate Q eps p ∧ ∀ theta ∈ parameterCube d, ∀ r j k,
        1 ≤ k → k ≤ n → ∀ a ∈ Set.Ioc 0 (1 / 2 : ℝ), ∀ u ∈ Set.Icc (-a) a,
        (∫ z, |p (Function.update theta j u, r, z) - ∑ q ∈ Finset.range k,
          densityDerivative p (Function.update theta j 0) r z j q /
            (q.factorial : ℝ) * u^q| ∂referenceLaw Q r) ≤
          |u|^k * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k := by
  obtain ⟨f, hf, hf0, hrow, hcert⟩ :=
    canonical_density_certificate_rows_of_gate hRN Q eps hQ hAllowed
  refine ⟨canonicalTranscriptDensity f, hcert, ?_⟩
  intro theta htheta r j k hk hkn a ha u hu
  exact canonical_density_coordinate_taylor_L1 Q eps (le_of_lt hAllowed.2.2.1)
    f hf hf0 hrow hcert theta htheta r j k hk hkn a u ha hu

end CausalSmith.Stat.LdpOptvalueUniformFrontier
