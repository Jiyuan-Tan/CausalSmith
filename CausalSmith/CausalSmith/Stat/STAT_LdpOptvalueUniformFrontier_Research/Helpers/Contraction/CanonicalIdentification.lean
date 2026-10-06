module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.Derivative
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.HistoryScore
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.StageIdentification
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Simultaneous coordinate identification of transcript densities

Countably many density identities identify the entire coordinate polynomial outside
one reference-null set. Thus the canonical finite-sum version and repaired stage
product have the same derivatives, including at boundary parameters.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Kernel.FiniteSequence
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- Assume [the stated hx condition](hyp:hx) and [the stated heq condition](hyp:heq). [Equality at an injective sequence identifies measurable families of real polynomials outside one null set, simultaneously at every real argument](goal). -/
-- @node: polynomial_family_ae_eq_of_sequence
lemma polynomial_family_ae_eq_of_sequence {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (P T : Ω → Polynomial ℝ) (x : ℕ → ℝ)
    (hx : Function.Injective x)
    (heq : ∀ m, (fun w => (P w).eval (x m)) =ᵐ[mu]
      (fun w => (T w).eval (x m))) :
    ∀ᵐ w ∂mu, ∀ y, (P w).eval y = (T w).eval y := by
  filter_upwards [ae_all_iff.mpr heq] with w hw
  have hPT : P w = T w := Polynomial.eq_of_infinite_eval_eq _ _
    ((Set.infinite_range_of_injective hx).mono (by
      rintro y ⟨m, rfl⟩
      exact hw m))
  intro y
  rw [hPT]

/-- [A coordinate section of a finite affine stage product is an actual real polynomial, also outside the parameter cube. [](](goal). -/
-- @node: stageProduct_coordinate_polynomial_eval
lemma stageProduct_coordinate_polynomial_eval (theta : Fin d → ℝ)
    (f : Fin n → PairedSymbol d → ℝ) (j : Fin d) :
    ∃ P : Polynomial ℝ, ∀ x,
      (∏ i, stageMixtureDensity (Function.update theta j x) (f i)) = P.eval x := by
  refine ⟨∏ i, (Polynomial.C (stageMixtureDensity (Function.update theta j 0) (f i)) +
    Polynomial.C (stageCoordinateSlope (f i) j) * Polynomial.X), ?_⟩
  intro x
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X]
  apply Finset.prod_congr rfl
  intro i hi
  rw [stageMixtureDensity_update theta, stageMixtureDensity_update theta]
  ring

/-- Assume [positive dimension](hyp:hd), [the stated htheta condition](hyp:htheta), [measurability of p](hyp:hp), [the protocol transcript](hyp:hpRep), [the protocol transcript](hyp:hpoly), [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), and [the stated hprod rep condition](hyp:hprodRep). [Simultaneous coordinate equality of the canonical density and the repaired stage product follows from their density representations. The exceptional set is independent of the coordinate argument, so derivatives may be compared there](goal). -/
-- @node: transcript_coordinate_ae_eq_stageProduct
lemma transcript_coordinate_ae_eq_stageProduct
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (r : Q.Seed) (j : Fin d)
    (p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ)
    (hp : Measurable p)
    (hpRep : ∀ t ∈ parameterCube d,
      (∀ z, 0 ≤ p (t, r, z)) ∧
      (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal (p (t, r, z))) =
        conditionalTranscriptLaw Q t r)
    (hpoly : ∀ z, ∃ c : Fin (n + 1) → ℝ, ∀ x,
      p (Function.update theta j x, r, z) = ∑ q, c q * x ^ q.val)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i w, 0 ≤ f i w)
    (hprodRep : ∀ t ∈ parameterCube d,
      (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal
        (∏ i, stageMixtureDensity t
          (fun a => f i (((a, r), take (Nat.le_of_lt i.isLt) z), z i)))) =
        conditionalTranscriptLaw Q t r) :
    ∀ᵐ z ∂referenceLaw Q r, ∀ x,
      p (Function.update theta j x, r, z) =
        ∏ i, stageMixtureDensity (Function.update theta j x)
          (fun a => f i (((a, r), take (Nat.le_of_lt i.isLt) z), z i)) := by
  classical
  haveI : IsProbabilityMeasure (referenceLaw Q r) :=
    conditionalTranscriptLaw_probability Q _ (by intro a; constructor <;> norm_num) hd r
  choose c hc using hpoly
  let P : ProtocolTranscript Q → Polynomial ℝ := fun z =>
    ∑ q : Fin (n + 1), Polynomial.C (c z q) * Polynomial.X ^ q.val
  have hP (z : ProtocolTranscript Q) (x : ℝ) :
      p (Function.update theta j x, r, z) = (P z).eval x := by
    rw [hc]
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  choose T hT using fun z : ProtocolTranscript Q =>
    stageProduct_coordinate_polynomial_eval theta
      (fun i a => f i (((a, r), take (Nat.le_of_lt i.isLt) z), z i)) j
  let x : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 2)
  have hx : Function.Injective x := by
    intro a b hab
    have h : (a : ℝ) + 2 = (b : ℝ) + 2 := by
      apply inv_injective
      simpa [x, one_div] using hab
    exact_mod_cast (show (a : ℝ) = (b : ℝ) by linarith)
  have hcube (m : ℕ) : Function.update theta j (x m) ∈ parameterCube d := by
    intro a
    by_cases ha : a = j
    · subst a
      rw [Function.update_self]
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      dsimp [x]
      constructor
      · have : 0 ≤ 1 / ((m : ℝ) + 2) := by positivity
        linarith
      · apply (div_le_iff₀ (by positivity)).mpr
        linarith
    · rw [Function.update_of_ne ha]
      exact htheta a
  have heq (m : ℕ) : (fun z => (P z).eval (x m)) =ᵐ[referenceLaw Q r]
      (fun z => (T z).eval (x m)) := by
    let t := Function.update theta j (x m)
    have ht : t ∈ parameterCube d := hcube m
    have hM := (measurable_originalTranscript_stageProduct Q f hf).comp
      (show Measurable (fun z : ProtocolTranscript Q => (t, r, z)) by fun_prop)
    have hmu := (hpRep t ht).2.trans (hprodRep t ht).symm
    have hae := (withDensity_eq_iff_of_sigmaFinite
      ((hp.comp (show Measurable (fun z : ProtocolTranscript Q => (t, r, z))
        by fun_prop)).ennreal_ofReal.aemeasurable)
      hM.ennreal_ofReal.aemeasurable).mp hmu
    filter_upwards [hae] with z hz
    have h0 : 0 ≤ ∏ i : Fin n, stageMixtureDensity t
        (fun a => f i (((a, r), take (Nat.le_of_lt i.isLt) z), z i)) := by
      apply Finset.prod_nonneg
      intro i hi
      apply Finset.sum_nonneg
      intro a ha
      exact mul_nonneg (stageInputWeight_nonneg t ht a) (hf0 i _)
    have hreal := (ENNReal.ofReal_eq_ofReal_iff ((hpRep t ht).1 z) h0).mp hz
    rw [← hP, ← hT]
    exact hreal
  filter_upwards [polynomial_family_ae_eq_of_sequence (referenceLaw Q r) P T x hx heq]
    with z hz
  intro y
  rw [hP, hT, hz]

/-- Assume [the protocol transcript](hyp:heq). [All orders of coordinate differentiation preserve the simultaneous canonical-to-product identity. No differentiation of a parameter-dependent null set is used](goal). -/
-- @node: densityDerivative_ae_eq_of_coordinate_identity
lemma densityDerivative_ae_eq_of_coordinate_identity
    (Q : LocalProtocol n (ObsRecord d))
    (p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ)
    (g : ℝ → ProtocolTranscript Q → ℝ)
    (theta : Fin d → ℝ) (r : Q.Seed) (j : Fin d)
    (heq : ∀ᵐ z ∂referenceLaw Q r, ∀ x,
      p (Function.update theta j x, r, z) = g x z) :
    ∀ᵐ z ∂referenceLaw Q r, ∀ k,
      densityDerivative p theta r z j k = iteratedDeriv k (fun x => g x z) (theta j) := by
  filter_upwards [heq] with z hz
  intro k
  unfold densityDerivative
  rw [show (fun x => p (Function.update theta j x, r, z)) = (fun x => g x z)
    from funext hz]

/-- Assume [the stated hpos condition](hyp:hpos). [The elementary score formula for a finite stage family uses zero scores past the transcript horizon](goal). -/
-- @node: finite_stageProduct_coordinateDerivative_score
lemma finite_stageProduct_coordinateDerivative_score
    (theta : Fin d → ℝ) (f : Fin n → PairedSymbol d → ℝ) (j : Fin d)
    (hpos : ∀ i, 0 < stageMixtureDensity theta (f i)) (k : ℕ) :
    iteratedDeriv k (fun x => ∏ i : Fin n,
      stageMixtureDensity (Function.update theta j x) (f i)) (theta j) =
      (k.factorial : ℝ) * (∏ i : Fin n, stageMixtureDensity theta (f i)) *
        scoreElementary (fun i => if hi : i < n then
          stageCoordinateSlope (f ⟨i, hi⟩) j / stageMixtureDensity theta (f ⟨i, hi⟩)
          else 0) n k := by
  classical
  let rows : ℕ → PairedSymbol d → ℝ := fun i => if hi : i < n then f ⟨i, hi⟩ else 0
  have hprod (t : Fin d → ℝ) : (∏ i : Fin n, stageMixtureDensity t (f i)) =
      ∏ i ∈ Finset.range n, stageMixtureDensity t (rows i) := by
    rw [Finset.prod_fin_eq_prod_range]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [rows, hi]
  have hxi : (fun i => stageCoordinateSlope (rows i) j /
      stageMixtureDensity theta (rows i)) =
      (fun i => if hi : i < n then stageCoordinateSlope (f ⟨i, hi⟩) j /
        stageMixtureDensity theta (f ⟨i, hi⟩) else 0) := by
    funext i
    by_cases hi : i < n
    · simp [rows, hi]
    · simp [rows, hi, stageCoordinateSlope]
  simp_rw [hprod]
  rw [stageProduct_coordinateDerivative_score theta rows j n k
    (by intro i hi; simpa [rows, hi] using hpos ⟨i, hi⟩), hxi]

/-- Assume [the stated hpos condition](hyp:hpos) and [the stated heq condition](hyp:heq). [The canonical density has the exact factorial-times-density-times-elementary score identity almost everywhere, simultaneously in the derivative order](goal). -/
-- @node: canonical_densityDerivative_ae_score
lemma canonical_densityDerivative_ae_score
    (Q : LocalProtocol n (ObsRecord d))
    (p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ)
    (theta : Fin d → ℝ) (r : Q.Seed) (j : Fin d)
    (f : ProtocolTranscript Q → Fin n → PairedSymbol d → ℝ)
    (hpos : ∀ z i, 0 < stageMixtureDensity theta (f z i))
    (heq : ∀ᵐ z ∂referenceLaw Q r, ∀ x,
      p (Function.update theta j x, r, z) =
        ∏ i : Fin n, stageMixtureDensity (Function.update theta j x) (f z i)) :
    ∀ᵐ z ∂referenceLaw Q r, ∀ k,
      densityDerivative p theta r z j k = (k.factorial : ℝ) * p (theta, r, z) *
        scoreElementary (fun i => if hi : i < n then
          stageCoordinateSlope (f z ⟨i, hi⟩) j /
            stageMixtureDensity theta (f z ⟨i, hi⟩) else 0) n k := by
  have hderiv := densityDerivative_ae_eq_of_coordinate_identity Q p _ theta r j heq
  filter_upwards [heq, hderiv] with z hz hdz
  intro k
  rw [hdz k, finite_stageProduct_coordinateDerivative_score theta (f z) j (hpos z)]
  have hpz := hz (theta j)
  simp only [Function.update_eq_self] at hpz
  rw [← hpz]

/-- Assume [measurability of p](hyp:hp), [the stated hp0 condition](hyp:hp0), [the stated hrep condition](hyp:hrep), [the stated hpos condition](hyp:hpos), and [the stated heq condition](hyp:heq). [The canonical derivative L1 integral is exactly the score first moment under the original parameter-specific transcript law. This identifies the measure needed for the adaptive martingale bound](goal). -/
-- @node: canonical_densityDerivative_integral_abs_score
lemma canonical_densityDerivative_integral_abs_score
    (Q : LocalProtocol n (ObsRecord d))
    (p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ) (hp : Measurable p)
    (theta : Fin d → ℝ) (r : Q.Seed) (j : Fin d) (k : ℕ)
    (hp0 : ∀ z, 0 ≤ p (theta, r, z))
    (hrep : (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal (p (theta, r, z))) =
      conditionalTranscriptLaw Q theta r)
    (f : ProtocolTranscript Q → Fin n → PairedSymbol d → ℝ)
    (hpos : ∀ z i, 0 < stageMixtureDensity theta (f z i))
    (heq : ∀ᵐ z ∂referenceLaw Q r, ∀ x,
      p (Function.update theta j x, r, z) =
        ∏ i : Fin n, stageMixtureDensity (Function.update theta j x) (f z i)) :
    (∫ z, |densityDerivative p theta r z j k| ∂referenceLaw Q r) =
      (k.factorial : ℝ) * (∫ z,
        |scoreElementary (fun i => if hi : i < n then
          stageCoordinateSlope (f z ⟨i, hi⟩) j /
            stageMixtureDensity theta (f z ⟨i, hi⟩) else 0) n k|
        ∂conditionalTranscriptLaw Q theta r) := by
  let E := fun z => scoreElementary (fun i => if hi : i < n then
    stageCoordinateSlope (f z ⟨i, hi⟩) j / stageMixtureDensity theta (f z ⟨i, hi⟩)
    else 0) n k
  have hscore := canonical_densityDerivative_ae_score Q p theta r j f hpos heq
  calc
    _ = ∫ z, |(k.factorial : ℝ) * p (theta, r, z) * E z| ∂referenceLaw Q r := by
      apply integral_congr_ae
      filter_upwards [hscore] with z hz
      rw [hz k]
    _ = (k.factorial : ℝ) * (∫ z, |E z| ∂conditionalTranscriptLaw Q theta r) := by
      rw [integral_abs_density_score (referenceLaw Q r) (fun z => p (theta, r, z))
        E _ (hp.comp (by fun_prop)) hp0 (k.factorial : ℝ) (by positivity)
        (fun _ => rfl), hrep]

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [positive dimension](hyp:hd), [a nonnegative privacy budget](hyp:heps), and [sequential local privacy of the protocol](hyp:hQ). [The RN gate gives canonical finite-sum densities and repaired rows whose coordinate sections agree simultaneously outside one reference-null set. This certifies the identification needed before applying the martingale score bound](goal). -/
-- @node: canonical_stageProduct_coordinate_identification_of_gate
lemma canonical_stageProduct_coordinate_identification_of_gate
    (hRN : MeasurableKernelRadonNikodym)
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (eps : ℝ) (heps : 0 ≤ eps) (hQ : SequentialClass Q eps) :
    ∃ p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ,
      ∃ f : (i : Fin n) →
        ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ,
      Measurable p ∧ (∀ i, Measurable (f i)) ∧
      (∀ i w, Real.exp (-eps) ≤ f i w ∧ f i w ≤ Real.exp eps) ∧
      (∀ i a b r eta z,
        f i (((a, r), eta), z) ≤ Real.exp eps * f i (((b, r), eta), z)) ∧
      (∀ i a r eta, (stageReferenceKernel Q i (r, eta)).withDensity
        (fun z => ENNReal.ofReal (f i (((a, r), eta), z))) =
          averagedKernel Q i ((a, r), eta)) ∧
      (∀ r, stageReferenceTranscriptLaw Q r = referenceLaw Q r) ∧
      (∀ theta ∈ parameterCube d, ∀ r,
        (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal
          (∏ i : Fin n, stageMixtureDensity theta
            (fun a => f i (((a, r), take (Nat.le_of_lt i.isLt) z), z i)))) =
          conditionalTranscriptLaw Q theta r) ∧
      (∀ theta ∈ parameterCube d, ∀ r,
        (∀ z, 0 ≤ p (theta, r, z)) ∧
        (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal (p (theta, r, z))) =
          conditionalTranscriptLaw Q theta r) ∧
      (∀ theta r z j, ∃ c : Fin (n + 1) → ℝ, ∀ x,
        p (Function.update theta j x, r, z) = ∑ q, c q * x ^ q.val) ∧
      ∀ theta ∈ parameterCube d, ∀ r j,
        ∀ᵐ z ∂referenceLaw Q r, ∀ x,
          p (Function.update theta j x, r, z) = ∏ i : Fin n,
            stageMixtureDensity (Function.update theta j x)
              (fun a => f i (((a, r), take (Nat.le_of_lt i.isLt) z), z i)) := by
  obtain ⟨p, hp, hrep, hpoly⟩ := canonical_density_polynomial_of_gate hRN Q hd
  obtain ⟨f, hf, hbound, hsum, hpriv, hrow, href, hprod⟩ :=
    originalTranscript_stageProduct_of_gate hRN Q hd eps heps hQ
  refine ⟨p, f, hp, hf, hbound, hpriv, hrow, href, hprod, hrep, hpoly, ?_⟩
  intro theta htheta r j
  exact transcript_coordinate_ae_eq_stageProduct Q hd theta htheta r j p hp
    (fun t ht => hrep t ht r) (fun z => hpoly theta r z j) f hf
    (fun i w => le_trans (le_of_lt (Real.exp_pos _)) (hbound i w).1)
    (fun t ht => hprod t ht r)

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN_of_gate), [sequential local privacy of the protocol](hyp:hQ), [sample size at least two](hyp:hn), [dimension at least two](hyp:hd), and [a privacy budget in the interval from zero to one](hyp:heps). [Full polynomial-density derivative certificate with the RN gate threaded](goal). -/
-- @node: density_derivative_of_gate
lemma density_derivative_of_gate (hRN_of_gate : MeasurableKernelRadonNikodym)
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ) (hQ : SequentialClass Q eps)
    (hn : 2 ≤ n) (hd : 2 ≤ d) (heps : eps ∈ Set.Ioc 0 1) :
    ∃ p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ,
      DensityCertificate Q eps p := by
  obtain ⟨p, f, hp, hf, hbound, hpriv, hrow, href, hprod, hrep, hpoly, hcoord⟩ :=
    canonical_stageProduct_coordinate_identification_of_gate hRN_of_gate Q
      (by omega) eps (le_of_lt heps.1) hQ
  refine ⟨p, hp, hrep, hpoly, ?_, ?_⟩
  · intro theta htheta r j k hk hkn
    have hpos (z : ProtocolTranscript Q) (i : Fin n) :
        0 < stageMixtureDensity theta
          (fun a => f i (((a, r), take (Nat.le_of_lt i.isLt) z), z i)) :=
      (originalTranscript_stageScore_bound Q (by omega) theta htheta eps
        (le_of_lt heps.1) f (fun i w => (hbound i w).1) hpriv r z i j).1
    rw [canonical_densityDerivative_integral_abs_score Q p hp theta r j k
      (hrep theta htheta r).1 (hrep theta htheta r).2
      (fun z i a => f i (((a, r), take (Nat.le_of_lt i.isLt) z), z i))
      hpos (hcoord theta htheta r j)]
    have hchain := originalTranscript_eq_parameterChain Q (by omega) theta htheta r
      f hf (fun i w => le_trans (le_of_lt (Real.exp_pos _)) (hbound i w).1)
      (fun i a eta => hrow i a r eta) (href r) (hprod theta htheta r)
    have hfirst := originalTranscript_scoreElementary_firstMoment Q (by omega)
      theta htheta r eps (le_of_lt heps.1) f hf hbound hpriv
      (fun i a eta => hrow i a r eta) hchain j k
    change (∫ z, |scoreElementary (fun v => transcriptCoordinateScore Q theta r f j v z)
      n k| ∂conditionalTranscriptLaw Q theta r) ≤ _ at hfirst
    calc
      _ ≤ (k.factorial : ℝ) *
          (Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k) :=
        mul_le_mul_of_nonneg_left hfirst (by positivity)
      _ = _ := by ring
  · exact densityDerivative_eq_zero_of_coordinate_polynomial p hpoly


end CausalSmith.Stat.LdpOptvalueUniformFrontier
