module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.Density
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Canonical finite-sum transcript densities

This module constructs transcript densities from fixed-record row densities and the explicit
affine masses of iid observed-record vectors.  The resulting density represents the conditional
transcript law and is polynomial of degree at most the sample size in each parameter coordinate.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

variable {n d : ℕ} {Q : LocalProtocol n (ObsRecord d)}

/-- Fix [the function theta](hyp:theta) and [the observed participant record](hyp:o). [The explicit affine mass of one observed record under the symmetric experiment](goal). -/
-- @node: observedAffineMass
def observedAffineMass (theta : Fin d → ℝ) (o : ObsRecord d) : ℝ :=
  (1 + obsSign o * theta o.1) / (4 * d)

/-- Fix [the function theta](hyp:theta) and [the function o](hyp:o). [The explicit iid mass of a complete observed-record vector](goal). -/
-- @node: iidAffineMass
def iidAffineMass (theta : Fin d → ℝ) (o : Fin n → ObsRecord d) : ℝ :=
  ∏ i, observedAffineMass theta (o i)

/-- Fix [the function f](hyp:f) and [the function w](hyp:w). [The finite sum of fixed-record transcript-row densities weighted by iid affine masses](goal). -/
-- @node: canonicalTranscriptDensity
def canonicalTranscriptDensity
    (f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ)
    (w : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q) : ℝ :=
  ∑ o, iidAffineMass w.1 o * f ((o, w.2.1), w.2.2)

/-- Assume [the stated htheta condition](hyp:htheta). [An observed-record affine mass is nonnegative throughout the parameter cube. [](](goal). -/
-- @node: observedAffineMass_nonneg
lemma observedAffineMass_nonneg (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (o : ObsRecord d) : 0 ≤ observedAffineMass theta o := by
  rcases o with ⟨j, a, y⟩
  have hj := htheta j
  cases a <;> cases y <;> simp only [observedAffineMass, obsSign, signVal,
    Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] <;>
    apply div_nonneg <;> linarith [hj.1, hj.2]

/-- Assume [the stated htheta condition](hyp:htheta). [The product mass of an iid observed-record vector is nonnegative on the cube. [](](goal). -/
-- @node: iidAffineMass_nonneg
lemma iidAffineMass_nonneg (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (o : Fin n → ObsRecord d) : 0 ≤ iidAffineMass theta o := by
  exact Finset.prod_nonneg fun i _ => observedAffineMass_nonneg theta htheta (o i)

/-- [A finite sum of jointly measurable row densities with affine weights is measurable](goal) when [the row-density family is measurable](hyp:hf). -/
-- @node: measurable_canonicalTranscriptDensity
@[fun_prop] lemma measurable_canonicalTranscriptDensity
    (f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ)
    (hf : Measurable f) : Measurable (canonicalTranscriptDensity f) := by
  apply Finset.measurable_sum
  intro o ho
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro i hi
    unfold observedAffineMass
    fun_prop
  · exact hf.comp (by fun_prop)

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [The explicit affine mass equals the observed symmetric-law singleton probability](goal). -/
-- @node: observedAffineMass_eq_real
lemma observedAffineMass_eq_real (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (hd : 0 < d) (o : ObsRecord d) :
    observedAffineMass theta o = (observedLaw (symmetricLaw theta)).real {o} := by
  have h := symmetricLaw_observed_recover_real theta htheta (signedObserve o) o.2.1
  rw [recoverObs_signedObserve] at h
  rw [h]
  unfold pairedLaw
  rw [atomLaw_real_event]
  · rcases o with ⟨j, a, y⟩
    cases a <;> cases y <;>
      simp [observedAffineMass, signedObserve, signVal, obsSign] <;> ring
  · intro v
    have hv := htheta v.1
    apply div_nonneg _ (by positivity)
    cases v.2 <;> simp only [signVal, Bool.false_eq_true, ↓reduceIte] <;>
      linarith [hv.1, hv.2]

/-- Assume [positive dimension](hyp:hd). [Every fixed-record transcript row is dominated by the zero-contrast transcript law](goal). -/
-- @node: fixedTranscriptLaw_absolutelyContinuous_reference
lemma fixedTranscriptLaw_absolutelyContinuous_reference
    (Q : LocalProtocol n (ObsRecord d)) (o : Fin n → ObsRecord d) (r : Q.Seed)
    (hd : 0 < d) : fixedTranscriptLaw Q o r ≪ referenceLaw Q r := by
  have hcube : (fun _ : Fin d => (0 : ℝ)) ∈ parameterCube d := by
    intro j; constructor <;> norm_num
  haveI := symmetricLaw_probability (fun _ : Fin d => 0) hcube hd
  haveI : IsProbabilityMeasure (observedLaw (symmetricLaw (fun _ : Fin d => 0))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let nu : Measure (Fin n → ObsRecord d) :=
    Measure.pi (fun _ : Fin n => observedLaw (symmetricLaw (fun _ : Fin d => 0)))
  have hpos : ∀ x : Fin n → ObsRecord d, nu {x} ≠ 0 := by
    intro x
    dsimp [nu]
    rw [Measure.pi_singleton]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => observed_symmetric_zero_atom hd (x i)
  have hac := finite_bind_absolutelyContinuous (Measure.dirac o) nu
    (fun x => fixedTranscriptLaw Q x r) (by fun_prop) hpos
  rw [Measure.dirac_bind (by fun_prop)] at hac
  simpa [referenceLaw, conditionalTranscriptLaw, nu] using hac

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN) and [the stated absolute-continuity property](hyp:hac). [The kernel RN gate admits a jointly measurable everywhere-nonnegative real density version](goal). -/
-- @node: nonnegative_real_kernel_density_of_gate
lemma nonnegative_real_kernel_density_of_gate (hRN : MeasurableKernelRadonNikodym)
    {H Z : Type} [MeasurableSpace H] [MeasurableSpace Z] [StandardBorelSpace Z]
    (K L : Kernel H Z) [IsMarkovKernel K] [IsMarkovKernel L]
    (hac : ∀ h, K h ≪ L h) :
    ∃ f : H × Z → ℝ, Measurable f ∧ (∀ w, 0 ≤ f w) ∧ ∀ h,
      (L h).withDensity (fun z => ENNReal.ofReal (f (h,z))) = K h := by
  obtain ⟨g, hg, hrep⟩ := hRN K L hac
  refine ⟨fun w => (g w).toReal, hg.ennreal_toReal, fun w => ENNReal.toReal_nonneg, ?_⟩
  intro h
  have hfin : (∫⁻ z, g (h,z) ∂L h) < ∞ := by
    have hu := hrep h Set.univ MeasurableSet.univ
    rw [setLIntegral_univ] at hu
    rw [← hu]
    exact measure_lt_top _ _
  have hae : ∀ᵐ z ∂L h, g (h,z) ≠ ∞ :=
    (ae_lt_top (show Measurable (fun z => g (h,z)) by fun_prop) hfin.ne).mono
      (fun z hz => hz.ne)
  ext E hE
  rw [withDensity_apply _ hE, hrep h E hE]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hae] with z hz
  exact ENNReal.ofReal_toReal hz

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN_of_gate) and [positive dimension](hyp:hd). [The RN gate supplies nonnegative densities for all fixed-record transcript rows at once](goal). -/
-- @node: fixedTranscript_row_densities_of_gate
lemma fixedTranscript_row_densities_of_gate
    (hRN_of_gate : MeasurableKernelRadonNikodym)
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d) :
    ∃ f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ,
      Measurable f ∧ (∀ w, 0 ≤ f w) ∧ ∀ o r,
        (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal (f ((o, r), z))) =
          fixedTranscriptLaw Q o r := by
  let K : Kernel ((Fin n → ObsRecord d) × Q.Seed) (ProtocolTranscript Q) :=
    ⟨fun w => fixedTranscriptLaw Q w.1 w.2, by fun_prop⟩
  let L : Kernel ((Fin n → ObsRecord d) × Q.Seed) (ProtocolTranscript Q) :=
    ⟨fun w => referenceLaw Q w.2, by
      have hm := (measurable_conditionalTranscriptLaw_clipped Q hd).comp
        (show Measurable (fun w : (Fin n → ObsRecord d) × Q.Seed =>
          ((fun _ : Fin d => (0 : ℝ)), w.2)) by fun_prop)
      have hzero : densityCubeClamp (fun _ : Fin d => (0 : ℝ)) = fun _ => 0 :=
        densityCubeClamp_eq _ (by intro j; constructor <;> norm_num)
      simpa only [Function.comp_def, hzero, referenceLaw] using hm⟩
  haveI : IsMarkovKernel K := ⟨fun w =>
    Causalean.Mathlib.Probability.Kernel.FiniteSequence.isProbabilityMeasure_transcriptLaw
      Q.kernels Q.markov (fun i => (w.1 i, w.2))⟩
  haveI : IsMarkovKernel L := ⟨fun w =>
    conditionalTranscriptLaw_probability Q _
      (by intro j; constructor <;> norm_num) hd w.2⟩
  haveI : StandardBorelSpace (ProtocolTranscript Q) := by
    unfold ProtocolTranscript Causalean.Mathlib.Probability.Kernel.FiniteSequence.Transcript
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.History
    infer_instance
  simpa [K, L] using nonnegative_real_kernel_density_of_gate hRN_of_gate K L
    (fun w => fixedTranscriptLaw_absolutelyContinuous_reference Q w.1 w.2 hd)

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [The extended-real iid affine mass is the product-law singleton mass on the cube](goal). -/
-- @node: iidAffineMass_ofReal
lemma iidAffineMass_ofReal (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (hd : 0 < d) (o : Fin n → ObsRecord d) :
    ENNReal.ofReal (iidAffineMass theta o) =
      Measure.pi (fun _ : Fin n => observedLaw (symmetricLaw theta)) {o} := by
  haveI := symmetricLaw_probability theta htheta hd
  haveI : IsProbabilityMeasure (observedLaw (symmetricLaw theta)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [Measure.pi_singleton, iidAffineMass,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => observedAffineMass_nonneg theta htheta (o i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [observedAffineMass_eq_real theta htheta hd]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [The conditional transcript law is the finite affine mixture of fixed-record rows](goal). -/
-- @node: conditionalTranscriptLaw_eq_sum_rows
lemma conditionalTranscriptLaw_eq_sum_rows (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (hd : 0 < d) (r : Q.Seed) :
    conditionalTranscriptLaw Q theta r =
      ∑ o : Fin n → ObsRecord d,
        ENNReal.ofReal (iidAffineMass theta o) • fixedTranscriptLaw Q o r := by
  haveI := symmetricLaw_probability theta htheta hd
  haveI : IsProbabilityMeasure (observedLaw (symmetricLaw theta)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  ext E hE
  rw [conditionalTranscriptLaw, Measure.bind_apply hE
    (show Measurable (fun o => fixedTranscriptLaw Q o r) by fun_prop).aemeasurable,
    lintegral_fintype]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro o ho
  rw [iidAffineMass_ofReal theta htheta hd]
  exact mul_comm _ _

/-- Assume [the function hf](hyp:hf) and [the stated htheta condition](hyp:htheta). [Nonnegative fixed-row densities give a nonnegative canonical transcript density](goal). -/
-- @node: canonicalTranscriptDensity_nonneg
lemma canonicalTranscriptDensity_nonneg
    (f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ)
    (hf : ∀ o r z, 0 ≤ f ((o, r), z))
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (r : Q.Seed) (z : ProtocolTranscript Q) :
    0 ≤ canonicalTranscriptDensity f (theta, r, z) := by
  apply Finset.sum_nonneg
  intro o ho
  exact mul_nonneg (iidAffineMass_nonneg theta htheta o) (hf o r z)

/-- Assume [measurability of f](hyp:hf), [the function hf0](hyp:hf0), [the function hrep](hyp:hrep), [the stated htheta condition](hyp:htheta), and [positive dimension](hyp:hd). [The canonical finite-sum density represents the conditional transcript law](goal). -/
-- @node: canonicalTranscriptDensity_withDensity
lemma canonicalTranscriptDensity_withDensity
    (f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ)
    (hf : Measurable f) (hf0 : ∀ o r z, 0 ≤ f ((o, r), z))
    (hrep : ∀ o r,
      (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal (f ((o, r), z))) =
        fixedTranscriptLaw Q o r)
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (hd : 0 < d) (r : Q.Seed) :
    (referenceLaw Q r).withDensity
        (fun z => ENNReal.ofReal (canonicalTranscriptDensity f (theta, r, z))) =
      conditionalTranscriptLaw Q theta r := by
  rw [conditionalTranscriptLaw_eq_sum_rows Q theta htheta hd r]
  ext E hE
  rw [withDensity_apply _ hE]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  have hpoint (z : ProtocolTranscript Q) :
      ENNReal.ofReal (canonicalTranscriptDensity f (theta, r, z)) =
        ∑ o, ENNReal.ofReal (iidAffineMass theta o) *
          ENNReal.ofReal (f ((o, r), z)) := by
    rw [canonicalTranscriptDensity,
      ENNReal.ofReal_sum_of_nonneg (fun o _ => mul_nonneg
        (iidAffineMass_nonneg theta htheta o) (hf0 o r z))]
    apply Finset.sum_congr rfl
    intro o ho
    rw [ENNReal.ofReal_mul (iidAffineMass_nonneg theta htheta o)]
  simp_rw [hpoint]
  rw [lintegral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro o ho
    have hfr : Measurable (fun z : ProtocolTranscript Q => f ((o, r), z)) :=
      hf.comp (show Measurable (fun z : ProtocolTranscript Q => ((o, r), z)) by fun_prop)
    rw [lintegral_const_mul _ hfr.ennreal_ofReal]
    have hh := congrArg (fun mu : Measure (ProtocolTranscript Q) => mu E) (hrep o r)
    rw [withDensity_apply _ hE] at hh
    exact congrArg (fun x => ENNReal.ofReal (iidAffineMass theta o) * x) hh
  · intro o ho
    have hfr : Measurable (fun z : ProtocolTranscript Q => f ((o, r), z)) :=
      hf.comp (show Measurable (fun z : ProtocolTranscript Q => ((o, r), z)) by fun_prop)
    exact measurable_const.mul hfr.ennreal_ofReal

/-- [Updating one coordinate writes each observed-record mass as an affine function. [](](goal). -/
-- @node: observedAffineMass_update
lemma observedAffineMass_update (theta : Fin d → ℝ) (o : ObsRecord d) (j : Fin d) (x : ℝ) :
    observedAffineMass (Function.update theta j x) o =
      observedAffineMass (Function.update theta j 0) o +
        (if o.1 = j then obsSign o / (4 * d) else 0) * x := by
  by_cases h : o.1 = j
  · subst j
    simp [observedAffineMass]
    ring
  · simp [observedAffineMass, h]

/-- [Every iid observed-vector mass has degree at most the sample size in one coordinate. [](](goal). -/
-- @node: iidAffineMass_coordinate_polynomial
lemma iidAffineMass_coordinate_polynomial (theta : Fin d → ℝ)
    (o : Fin n → ObsRecord d) (j : Fin d) :
    ∃ coeff : Fin (n + 1) → ℝ, ∀ x : ℝ,
      iidAffineMass (Function.update theta j x) o = ∑ k, coeff k * x ^ k.val := by
  let factors : Fin n → Polynomial ℝ := fun i =>
    Polynomial.C (observedAffineMass (Function.update theta j 0) (o i)) +
      Polynomial.C (if (o i).1 = j then obsSign (o i) / (4 * d) else 0) * Polynomial.X
  let P : Polynomial ℝ := ∏ i, factors i
  have hdeg : P.natDegree < n + 1 := by
    apply Nat.lt_succ_of_le
    calc
      P.natDegree ≤ ∑ i : Fin n, (factors i).natDegree :=
        Polynomial.natDegree_prod_le Finset.univ factors
      _ ≤ ∑ _i : Fin n, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Polynomial.natDegree_add_le _ _).trans
          (max_le (by simp) ((Polynomial.natDegree_mul_le (p := Polynomial.C
            (if (o i).1 = j then obsSign (o i) / (4 * d) else 0))
            (q := Polynomial.X)).trans (by simp)))
      _ = n := by simp
  refine ⟨fun k => P.coeff k, ?_⟩
  intro x
  have hsum : (∑ k : Fin (n + 1), P.coeff k.val * x ^ k.val) = P.eval x := by
    rw [Fin.sum_univ_eq_sum_range (fun i => P.coeff i * x ^ i) (n + 1)]
    exact (Polynomial.eval_eq_sum_range' hdeg x).symm
  rw [hsum]
  simp only [P, factors, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X]
  apply Finset.prod_congr rfl
  intro i hi
  rw [observedAffineMass_update]

/-- [A canonical finite-sum transcript density has degree at most the sample size coordinatewise. [](](goal). -/
-- @node: canonicalTranscriptDensity_coordinate_polynomial
lemma canonicalTranscriptDensity_coordinate_polynomial
    (f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ)
    (theta : Fin d → ℝ) (r : Q.Seed) (z : ProtocolTranscript Q) (j : Fin d) :
    ∃ coeff : Fin (n + 1) → ℝ, ∀ x : ℝ,
      canonicalTranscriptDensity f (Function.update theta j x, r, z) =
        ∑ k, coeff k * x ^ k.val := by
  choose c hc using fun o : Fin n → ObsRecord d =>
    iidAffineMass_coordinate_polynomial theta o j
  refine ⟨fun k => ∑ o, c o k * f ((o, r), z), ?_⟩
  intro x
  simp only [canonicalTranscriptDensity]
  simp_rw [hc]
  calc
    (∑ o, (∑ k, c o k * x ^ k.val) * f ((o, r), z)) =
        ∑ o, ∑ k, c o k * x ^ k.val * f ((o, r), z) := by
          apply Finset.sum_congr rfl
          intro o ho
          rw [Finset.sum_mul]
    _ =
        ∑ o, ∑ k, (c o k * f ((o, r), z)) * x ^ k.val := by
          apply Finset.sum_congr rfl
          intro o ho
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = ∑ k, ∑ o, (c o k * f ((o, r), z)) * x ^ k.val := by
          rw [Finset.sum_comm]
    _ = ∑ k, (∑ o, c o k * f ((o, r), z)) * x ^ k.val := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_mul]

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN_of_gate) and [positive dimension](hyp:hd). [The RN gate yields a canonical measurable, nonnegative, coordinate-polynomial density version](goal). -/
-- @node: canonical_density_polynomial_of_gate
lemma canonical_density_polynomial_of_gate
    (hRN_of_gate : MeasurableKernelRadonNikodym)
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d) :
    ∃ p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ,
      Measurable p ∧
      (∀ theta ∈ parameterCube d, ∀ r,
        (∀ z, 0 ≤ p (theta, r, z)) ∧
        (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal (p (theta, r, z))) =
          conditionalTranscriptLaw Q theta r) ∧
      (∀ theta r z j, ∃ coeff : Fin (n + 1) → ℝ,
        ∀ x : ℝ, p (Function.update theta j x, r, z) = ∑ k, coeff k * x ^ k.val) := by
  obtain ⟨f, hf, hf0, hrep⟩ := fixedTranscript_row_densities_of_gate hRN_of_gate Q hd
  refine ⟨canonicalTranscriptDensity f, measurable_canonicalTranscriptDensity f hf, ?_, ?_⟩
  · intro theta htheta r
    exact ⟨fun z => canonicalTranscriptDensity_nonneg f
      (fun o r z => hf0 ((o, r), z)) theta htheta r z,
      canonicalTranscriptDensity_withDensity f hf (fun o r z => hf0 ((o, r), z))
        hrep theta htheta hd r⟩
  · exact canonicalTranscriptDensity_coordinate_polynomial f

end CausalSmith.Stat.LdpOptvalueUniformFrontier
