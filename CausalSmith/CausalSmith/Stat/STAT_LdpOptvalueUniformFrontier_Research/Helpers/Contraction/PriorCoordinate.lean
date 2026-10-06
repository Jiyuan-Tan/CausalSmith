module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.CanonicalTaylor

/-!
# Single-coordinate matched-prior integration

Testing a finite polynomial family against the sign of its prior density
difference reduces its L1 contraction to scalar moment cancellation. All
integration exchanges are finite coefficient sums.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [the stated hc condition](hyp:hc), [nonnegative amplitude](hyp:ha), [a nonnegative bias bound](hyp:hB), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), [the stated hk condition](hyp:hk), [the stated hmom condition](hyp:hmom), and [the stated hderiv condition](hyp:hderiv). [Matched supported priors contract an integrable finite polynomial density family by twice the uniform coordinate Taylor remainder radius](goal). -/
-- @node: finitePolynomial_matchingMoments_L1
lemma finitePolynomial_matchingMoments_L1 {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (m : ℕ) (c : Fin m → Ω → ℝ)
    (hc : ∀ q, Integrable (c q) mu) (a B : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (nu0 nu1 : Measure ℝ) (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (k : ℕ) (hk : 1 ≤ k) (hmom : MatchingMoments k nu0 nu1)
    (hderiv : ∀ x ∈ Set.Icc (-a) a,
      (∫ z, |iteratedDeriv k (fun t : ℝ => ∑ q, c q z * t^q.val) x| ∂mu) ≤
        (k.factorial : ℝ) * B) :
    (∫ z, |(∫ u, ∑ q, c q z * u^q.val ∂nu0) -
      (∫ u, ∑ q, c q z * u^q.val ∂nu1)| ∂mu) ≤ 2 * a^k * B := by
  let F := fun x : ℝ => fun z : Ω => ∑ q, c q z * x^q.val
  have hprior (nu : Measure ℝ) (hnu : AmplitudePrior a nu) (z : Ω) :
      (∫ u, F u z ∂nu) = ∑ q, c q z * (∫ u, u^q.val ∂nu) := by
    rw [integral_finsetSum _ (fun q _ =>
      integrable_continuous_amplitudePrior a nu hnu _ (by fun_prop))]
    simp_rw [integral_const_mul]
  let R := fun z : Ω => (∫ u, F u z ∂nu0) - ∫ u, F u z ∂nu1
  have hR : Integrable R mu := by
    dsimp [R]
    simp_rw [hprior nu0 hnu0, hprior nu1 hnu1]
    exact (integrable_finsetSum _ (fun q _ => (hc q).mul_const _)).sub
      (integrable_finsetSum _ (fun q _ => (hc q).mul_const _))
  let g := fun z : Ω => R z / |R z|
  have hg : AEStronglyMeasurable g mu :=
    hR.aestronglyMeasurable.div₀ hR.abs.aestronglyMeasurable
  have hgb (z : Ω) : |g z| ≤ 1 := by
    dsimp [g]
    rw [abs_div, abs_abs]
    by_cases hz : R z = 0
    · simp [hz]
    · rw [div_self (abs_ne_zero.mpr hz)]
  have hgR (z : Ω) : g z * R z = |R z| := by
    dsimp [g]
    by_cases hz : R z = 0
    · simp [hz]
    · field_simp [abs_ne_zero.mpr hz]
      nlinarith [sq_abs (R z)]
  have hgc (q : Fin m) : Integrable (fun z => g z * c q z) mu :=
    (hc q).bdd_mul hg (Filter.Eventually.of_forall (fun z => by simpa using hgb z))
  let f := fun x : ℝ => ∫ z, g z * F x z ∂mu
  have hfpoly (x : ℝ) : f x = ∑ q, (∫ z, g z * c q z ∂mu) * x^q.val := by
    dsimp [f, F]
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [integral_finsetSum _ (fun q _ => (hgc q).mul_const _)]
    simp_rw [integral_mul_const]
  have hf : ContDiff ℝ k f := by
    rw [show f = _ from funext hfpoly]
    fun_prop
  have hD (v : ℕ) (x : ℝ) : Integrable (fun z => iteratedDeriv v (fun t => F t z) x) mu :=
    integrable_finitePolynomial_iteratedDeriv mu m c hc v x
  have hfD (v : ℕ) (x : ℝ) : iteratedDeriv v f x =
      ∫ z, g z * iteratedDeriv v (fun t => F t z) x ∂mu := by
    have heq : f = (fun t : ℝ => ∫ z, ∑ q, (g z * c q z) * t^q.val ∂mu) := by
      ext t
      simp [f, F, Finset.mul_sum, mul_assoc]
    rw [heq, finitePolynomial_iteratedDeriv_integral mu m _ hgc]
    apply integral_congr_ae
    filter_upwards [] with z
    have heqz : (fun t : ℝ => ∑ q, (g z * c q z) * t^q.val) =
        (fun t : ℝ => g z * F t z) := by
      ext t
      simp [F, Finset.mul_sum, mul_assoc]
    rw [heqz, iteratedDeriv_const_mul_field]
  have hfd (x : ℝ) (hx : x ∈ Set.Icc (-a) a) :
      |iteratedDeriv k f x| ≤ (k.factorial : ℝ) * B := by
    rw [hfD]
    calc
      _ ≤ ∫ z, |g z * iteratedDeriv k (fun t => F t z) x| ∂mu :=
        abs_integral_le_integral_abs
      _ ≤ ∫ z, |iteratedDeriv k (fun t => F t z) x| ∂mu := by
        apply integral_mono_ae ((hD k x).bdd_mul hg
          (Filter.Eventually.of_forall (fun z => by simpa using hgb z))).abs (hD k x).abs
        filter_upwards [] with z
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (hgb z)
      _ ≤ _ := hderiv x hx
  have hswap (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
      (∫ u, f u ∂nu) = ∫ z, g z * (∫ u, F u z ∂nu) ∂mu := by
    simp_rw [hfpoly, hprior nu hnu]
    rw [integral_finsetSum _ (fun q _ =>
      integrable_continuous_amplitudePrior a nu hnu _ (by fun_prop))]
    simp_rw [integral_const_mul, Finset.mul_sum, ← mul_assoc]
    rw [integral_finsetSum _ (fun q _ => (hgc q).mul_const _)]
    simp_rw [integral_mul_const]
  have hscalar := matchingMoments_smooth_integral_sub_le a B ha hB
    nu0 nu1 hnu0 hnu1 k hk hmom f hf hfd
  have heq : (∫ u, f u ∂nu0) - (∫ u, f u ∂nu1) = ∫ z, |R z| ∂mu := by
    rw [hswap nu0 hnu0, hswap nu1 hnu1, ← integral_sub]
    · simp_rw [← mul_sub]
      change (∫ z, g z * R z ∂mu) = _
      simp_rw [hgR]
    · simp_rw [hprior nu0 hnu0, Finset.mul_sum, ← mul_assoc]
      exact integrable_finsetSum _ (fun q _ => (hgc q).mul_const _)
    · simp_rw [hprior nu1 hnu1, Finset.mul_sum, ← mul_assoc]
      exact integrable_finsetSum _ (fun q _ => (hgc q).mul_const _)
  rw [heq, abs_of_nonneg (integral_nonneg (fun z => abs_nonneg (R z)))] at hscalar
  exact hscalar

variable {n d : ℕ}

/-- Assume [a nonnegative privacy budget](hyp:heps), [measurability of f](hyp:hf), [the function hf0](hyp:hf0), [the function hrow](hyp:hrow), [the stated hcert condition](hyp:hcert), [the stated htheta condition](hyp:htheta), [amplitude between zero and one half](hyp:ha), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), [the stated hk condition](hyp:hk), [order no larger than the sample size](hyp:hkn), and [the stated hmom condition](hyp:hmom). [A single coordinate replacement between moment-matched priors has the exact L1 cost, uniformly over the other contrasts and every public seed](goal). -/
-- @node: canonical_density_coordinate_matching_L1
lemma canonical_density_coordinate_matching_L1
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ) (heps : 0 ≤ eps)
    (f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ)
    (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w)
    (hrow : ∀ o r, (referenceLaw Q r).withDensity
      (fun z => ENNReal.ofReal (f ((o, r), z))) = fixedTranscriptLaw Q o r)
    (hcert : DensityCertificate Q eps (canonicalTranscriptDensity f))
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (r : Q.Seed) (j : Fin d)
    (a : ℝ) (ha : a ∈ Set.Ioc 0 (1 / 2 : ℝ))
    (nu0 nu1 : Measure ℝ) (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hmom : MatchingMoments k nu0 nu1) :
    (∫ z, |(∫ u, canonicalTranscriptDensity f (Function.update theta j u, r, z) ∂nu0) -
      (∫ u, canonicalTranscriptDensity f (Function.update theta j u, r, z) ∂nu1)|
        ∂referenceLaw Q r) ≤
      2 * a^k * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k := by
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
  have hD (x : ℝ) (z : ProtocolTranscript Q) :
      densityDerivative (canonicalTranscriptDensity f) (Function.update theta j x) r z j k =
        iteratedDeriv k (fun t : ℝ => ∑ q, c q z * t^q.val) x := by
    simp only [densityDerivative, Function.update_idem, Function.update_self]
    rw [show (fun t => canonicalTranscriptDensity f (Function.update theta j t, r, z)) =
      (fun t : ℝ => ∑ q, c q z * t^q.val) from funext (fun t => heval t z)]
  have hbeta : 0 ≤ derivativeScale d eps := by
    unfold derivativeScale
    exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr heps)) (by positivity)
  have hbound := finitePolynomial_matchingMoments_L1 (referenceLaw Q r) (n + 1) c hc
    a (Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k) (le_of_lt ha.1)
    (by positivity) nu0 nu1 hnu0 hnu1 k hk hmom (fun x hx => by
      simpa only [hD, mul_assoc] using hcert.2.2.2.1
        (Function.update theta j x) (hcube x hx) r j k hk hkn)
  simpa only [heval, mul_assoc] using hbound

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [sequential local privacy of the protocol](hyp:hQ), and [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [The RN construction provides one canonical density certificate and all single-coordinate matched-prior L1 bounds needed for product-prior telescoping](goal). -/
-- @node: density_coordinate_matching_of_gate
lemma density_coordinate_matching_of_gate (hRN : MeasurableKernelRadonNikodym)
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ) (hQ : SequentialClass Q eps)
    (hAllowed : Allowed n d eps) :
    ∃ p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ,
      DensityCertificate Q eps p ∧ ∀ theta ∈ parameterCube d, ∀ r j,
        ∀ a ∈ Set.Ioc 0 (1 / 2 : ℝ), ∀ nu0 nu1 : Measure ℝ,
        AmplitudePrior a nu0 → AmplitudePrior a nu1 → ∀ k : ℕ,
        1 ≤ k → k ≤ n → MatchingMoments k nu0 nu1 →
        (∫ z, |(∫ u, p (Function.update theta j u, r, z) ∂nu0) -
          (∫ u, p (Function.update theta j u, r, z) ∂nu1)| ∂referenceLaw Q r) ≤
          2 * a^k * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k := by
  obtain ⟨f, hf, hf0, hrow, hcert⟩ :=
    canonical_density_certificate_rows_of_gate hRN Q eps hQ hAllowed
  refine ⟨canonicalTranscriptDensity f, hcert, ?_⟩
  intro theta htheta r j a ha nu0 nu1 hnu0 hnu1 k hk hkn hmom
  exact canonical_density_coordinate_matching_L1 Q eps (le_of_lt hAllowed.2.2.1)
    f hf hf0 hrow hcert theta htheta r j a ha nu0 nu1 hnu0 hnu1 k hk hkn hmom

end CausalSmith.Stat.LdpOptvalueUniformFrontier
