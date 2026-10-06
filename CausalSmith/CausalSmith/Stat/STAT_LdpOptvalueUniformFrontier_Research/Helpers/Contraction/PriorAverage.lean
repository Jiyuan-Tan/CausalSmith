module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.PriorCoordinate
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Averaging coordinate replacements

The canonical finite-row representation justifies Fubini for a coordinate
replacement averaged over any probability law supported on the parameter cube.
The exact single-coordinate L1 cost is preserved by this averaging.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- Assume [the stated htheta condition](hyp:htheta), [the stated ha condition](hyp:ha), and [the stated hu condition](hyp:hu). [Replacing a cube coordinate by a supported amplitude stays in the cube](goal). -/
-- @node: parameterCube_update_amplitude
lemma parameterCube_update_amplitude (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (j : Fin d) (a : ℝ)
    (ha : a ≤ (1 / 2 : ℝ)) (u : ℝ) (hu : u ∈ Set.Icc (-a) a) :
    Function.update theta j u ∈ parameterCube d := by
  intro b
  by_cases hb : b = j
  · subst b
    simp only [Function.update_self]
    constructor <;> linarith [hu.1, hu.2]
  · rw [Function.update_of_ne hb]
    exact htheta b

/-- Assume [positive dimension](hyp:hd) and [the stated htheta condition](hyp:htheta). [An iid affine input mass lies between zero and one on the cube](goal). -/
-- @node: iidAffineMass_abs_le_one
lemma iidAffineMass_abs_le_one (hd : 0 < d) (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (o : Fin n → ObsRecord d) :
    |iidAffineMass theta o| ≤ 1 := by
  rw [abs_of_nonneg (iidAffineMass_nonneg theta htheta o)]
  unfold iidAffineMass
  calc
    (∏ i, observedAffineMass theta (o i)) ≤ ∏ _i : Fin n, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _; exact observedAffineMass_nonneg theta htheta (o i)
      · intro i _
        rw [observedAffineMass_eq_real theta htheta hd]
        haveI := symmetricLaw_probability theta htheta hd
        haveI : IsProbabilityMeasure (observedLaw (symmetricLaw theta)) :=
          Measure.isProbabilityMeasure_map (by fun_prop)
        exact measureReal_le_one
    _ = 1 := by simp

/-- Assume [positive dimension](hyp:hd), [the function hpi](hyp:hpi), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [Supported coordinate-averaged affine masses are integrable over any probability law on the remaining contrasts](goal). -/
-- @node: integrable_coordinate_prior_mass
lemma integrable_coordinate_prior_mass (hd : 0 < d)
    (pi : Measure (Fin d → ℝ)) [IsProbabilityMeasure pi]
    (hpi : ∀ᵐ theta ∂pi, theta ∈ parameterCube d) (j : Fin d)
    (a : ℝ) (ha : a ≤ (1 / 2 : ℝ)) (nu : Measure ℝ)
    (hnu : AmplitudePrior a nu) (o : Fin n → ObsRecord d) :
    Integrable (fun theta => ∫ u, iidAffineMass (Function.update theta j u) o ∂nu) pi := by
  letI := hnu.1
  have hm : Measurable (fun w : (Fin d → ℝ) × ℝ =>
      iidAffineMass (Function.update w.1 j w.2) o) := by
    unfold iidAffineMass observedAffineMass
    fun_prop
  apply Integrable.of_bound hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable 1
  filter_upwards [hpi] with theta htheta
  rw [Real.norm_eq_abs]
  calc
    |∫ u, iidAffineMass (Function.update theta j u) o ∂nu| ≤
      ∫ u, |iidAffineMass (Function.update theta j u) o| ∂nu :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _u : ℝ, (1 : ℝ) ∂nu := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) (integrable_const 1)
      filter_upwards [show ∀ᵐ u ∂nu, u ∈ Set.Icc (-a) a from
        ae_iff.mpr hnu.2] with u hu
      exact iidAffineMass_abs_le_one hd _
        (parameterCube_update_amplitude theta htheta j a ha u hu) o
    _ = 1 := by simp

/-- Assume [the stated f condition](hyp:hF) and [the stated b condition](hyp:hB). [Probability averaging preserves a uniform L1 bound](goal). -/
-- @node: probability_average_L1_le
lemma probability_average_L1_le {T Z : Type*} [MeasurableSpace T] [MeasurableSpace Z]
    (pi : Measure T) [IsProbabilityMeasure pi] (mu : Measure Z) [SFinite mu]
    (F : T → Z → ℝ) (hF : Integrable (Function.uncurry F) (pi.prod mu))
    (B : ℝ) (hB : ∀ᵐ t ∂pi, (∫ z, |F t z| ∂mu) ≤ B) :
    (∫ z, |∫ t, F t z ∂pi| ∂mu) ≤ B := by
  have hleft : Integrable (fun z => |∫ t, F t z ∂pi|) mu :=
    hF.integral_prod_right.abs
  have hright : Integrable (fun z => ∫ t, |F t z| ∂pi) mu :=
    hF.abs.integral_prod_right
  calc
    _ ≤ ∫ z, ∫ t, |F t z| ∂pi ∂mu := by
      apply integral_mono hleft hright
      intro z
      exact abs_integral_le_integral_abs
    _ = ∫ t, ∫ z, |F t z| ∂mu ∂pi := (integral_integral_swap hF.abs).symm
    _ ≤ ∫ _t, B ∂pi := integral_mono_ae hF.abs.integral_prod_left (integrable_const B) hB
    _ = B := by simp

/-- Assume [a nonnegative privacy budget](hyp:heps), [positive dimension](hyp:hd), [measurability of f](hyp:hf), [the function hf0](hyp:hf0), [the function hrow](hyp:hrow), [the stated hcert condition](hyp:hcert), [the function hpi](hyp:hpi), [amplitude between zero and one half](hyp:ha), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), [the stated hk condition](hyp:hk), [order no larger than the sample size](hyp:hkn), and [the stated hmom condition](hyp:hmom). [Integrating the remaining contrasts under any cube-supported probability law preserves the exact single-coordinate matched-prior contraction cost](goal). -/
-- @node: canonical_density_averaged_coordinate_matching_L1
lemma canonical_density_averaged_coordinate_matching_L1
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ) (heps : 0 ≤ eps) (hd : 0 < d)
    (f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ)
    (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w)
    (hrow : ∀ o r, (referenceLaw Q r).withDensity
      (fun z => ENNReal.ofReal (f ((o, r), z))) = fixedTranscriptLaw Q o r)
    (hcert : DensityCertificate Q eps (canonicalTranscriptDensity f))
    (pi : Measure (Fin d → ℝ)) [IsProbabilityMeasure pi]
    (hpi : ∀ᵐ theta ∂pi, theta ∈ parameterCube d) (r : Q.Seed) (j : Fin d)
    (a : ℝ) (ha : a ∈ Set.Ioc 0 (1 / 2 : ℝ))
    (nu0 nu1 : Measure ℝ) (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hmom : MatchingMoments k nu0 nu1) :
    (∫ z, |∫ theta,
      ((∫ u, canonicalTranscriptDensity f (Function.update theta j u, r, z) ∂nu0) -
        (∫ u, canonicalTranscriptDensity f (Function.update theta j u, r, z) ∂nu1))
          ∂pi| ∂referenceLaw Q r) ≤
      2 * a^k * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k := by
  classical
  haveI : IsProbabilityMeasure (referenceLaw Q r) :=
    conditionalTranscriptLaw_probability Q (fun _ => 0)
      (by intro b; constructor <;> norm_num) hd r
  let F := fun theta z =>
    (∫ u, canonicalTranscriptDensity f (Function.update theta j u, r, z) ∂nu0) -
      (∫ u, canonicalTranscriptDensity f (Function.update theta j u, r, z) ∂nu1)
  have hexpand (nu : Measure ℝ) (hnu : AmplitudePrior a nu)
      (theta : Fin d → ℝ) (z : ProtocolTranscript Q) :
      (∫ u, canonicalTranscriptDensity f (Function.update theta j u, r, z) ∂nu) =
        ∑ o, (∫ u, iidAffineMass (Function.update theta j u) o ∂nu) * f ((o,r),z) := by
    unfold canonicalTranscriptDensity
    rw [integral_finsetSum]
    · simp_rw [integral_mul_const]
    · intro o _
      apply integrable_continuous_amplitudePrior a nu hnu
      simp only [Prod.fst, Prod.snd]
      unfold iidAffineMass observedAffineMass
      fun_prop
  have hF : Integrable (Function.uncurry F) (pi.prod (referenceLaw Q r)) := by
    have heq : Function.uncurry F = (fun w => ∑ o,
        ((∫ u, iidAffineMass (Function.update w.1 j u) o ∂nu0) -
          (∫ u, iidAffineMass (Function.update w.1 j u) o ∂nu1)) * f ((o,r),w.2)) := by
      ext w
      simp only [Function.uncurry, F, hexpand nu0 hnu0, hexpand nu1 hnu1,
        ← Finset.sum_sub_distrib, sub_mul]
    rw [heq]
    apply integrable_finsetSum
    intro o _
    exact ((integrable_coordinate_prior_mass hd pi hpi j a ha.2 nu0 hnu0 o).sub
      (integrable_coordinate_prior_mass hd pi hpi j a ha.2 nu1 hnu1 o)).mul_prod
        (integrable_fixedTranscript_row_density Q f hf hf0 hrow o r)
  apply probability_average_L1_le pi (referenceLaw Q r) F hF
  filter_upwards [hpi] with theta htheta
  exact canonical_density_coordinate_matching_L1 Q eps heps f hf hf0 hrow hcert
    theta htheta r j a ha nu0 nu1 hnu0 hnu1 k hk hkn hmom

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [sequential local privacy of the protocol](hyp:hQ), and [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [The RN gate supplies a canonical certificate whose coordinate contraction is already averaged over every supported remaining-coordinate prior](goal). -/
-- @node: density_averaged_coordinate_matching_of_gate
lemma density_averaged_coordinate_matching_of_gate (hRN : MeasurableKernelRadonNikodym)
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ) (hQ : SequentialClass Q eps)
    (hAllowed : Allowed n d eps) :
    ∃ p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ,
      DensityCertificate Q eps p ∧
      ∀ (pi : Measure (Fin d → ℝ)), IsProbabilityMeasure pi →
        (∀ᵐ theta ∂pi, theta ∈ parameterCube d) → ∀ r j,
        ∀ a ∈ Set.Ioc 0 (1 / 2 : ℝ), ∀ nu0 nu1 : Measure ℝ,
        AmplitudePrior a nu0 → AmplitudePrior a nu1 → ∀ k : ℕ,
        1 ≤ k → k ≤ n → MatchingMoments k nu0 nu1 →
        (∫ z, |∫ theta,
          ((∫ u, p (Function.update theta j u, r, z) ∂nu0) -
            (∫ u, p (Function.update theta j u, r, z) ∂nu1)) ∂pi|
              ∂referenceLaw Q r) ≤
          2 * a^k * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k := by
  obtain ⟨f, hf, hf0, hrow, hcert⟩ :=
    canonical_density_certificate_rows_of_gate hRN Q eps hQ hAllowed
  refine ⟨canonicalTranscriptDensity f, hcert, ?_⟩
  intro pi hprob hpi r j a ha nu0 nu1 hnu0 hnu1 k hk hkn hmom
  letI := hprob
  exact canonical_density_averaged_coordinate_matching_L1 Q eps (le_of_lt hAllowed.2.2.1)
    (by have := hAllowed.2.1; omega) f hf hf0 hrow hcert pi hpi r j
      a ha nu0 nu1 hnu0 hnu1 k hk hkn hmom

end CausalSmith.Stat.LdpOptvalueUniformFrontier
