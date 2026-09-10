import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers.InterventionAlgebra
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Shared kernel and matching certificate

The certificate shares one basis extension, inverse, matching, and alternating-reachability forest
across all admissible sources. The exact-real cost and dense-output lower-bound claims are explicit.
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open Set
open scoped BigOperators

abbrev KernelColumnIndex (p n : ℕ) (hpn : p ≤ n) (x : Fin p) :=
  {k : Fin n // k = Fin.castLE hpn x ∨ p ≤ k.1}

def kernelBlock {p n : ℕ} {C : MixingMatrix p n} {x : Fin p}
    (D : CertificateData C x) : Matrix (Fin n) (KernelColumnIndex p n D.dim_le x) ℝ :=
  fun i k => D.inverseBasis i k.1

def IsKernelBasis {p n : ℕ} (C : MixingMatrix p n) (x : Fin p)
    (D : CertificateData C x) : Prop :=
  ∀ z : Fin n → ℝ,
    (∀ i : {i : Fin p // i ≠ x}, ∑ j, C i.1 j * z j = 0) ↔
    ∃ coeff : KernelColumnIndex p n D.dim_le x → ℝ,
      z = fun j => ∑ k, kernelBlock D j k * coeff k

def KernelRowNonzero {p n : ℕ} {C : MixingMatrix p n} {x : Fin p}
    (D : CertificateData C x) (j : Fin n) : Prop :=
  ∃ k, kernelBlock D j k ≠ 0

/-- Shared-kernel/matching certificate, including conditional cubic exact-real enumeration,
rationality preservation, and worst-case output optimality certified by dense rational
Vandermonde instances. The cost claim begins from exact `C`, not from `P_X`. -/
-- @node: lem:shared-kernel-matching-certificate
lemma shared_kernel_matching_certificate {p n : ℕ} (C : MixingMatrix p n)
    (hdim : ValidPopulationDimensions p n) (hC : FullRowRank C) (x : Fin p) :
    ∃ D : CertificateData C x,
      IsKernelBasis C x D ∧
      (∀ j, j ∈ admissibleSources C x ↔ C x j ≠ 0 ∧ KernelRowNonzero D j) ∧
      (∀ j (hj : j ∈ admissibleSources C x),
        CompletionFiber C D.dim_le x (D.completion ⟨j, hj⟩).1
          (D.completion ⟨j, hj⟩).2 ∧
        assignedSource (D.completion ⟨j, hj⟩).2 (D.valid ⟨j, hj⟩).monomial
          (Fin.castLE D.dim_le x) = j) ∧
      (IsRationalMatrix C → ∀ j (hj : j ∈ admissibleSources C x),
        IsRationalMatrix (D.completion ⟨j, hj⟩).1 ∧
          IsRationalMatrix (D.completion ⟨j, hj⟩).2) ∧
      (∀ j : AdmissibleSourceIndex C x,
        (D.completion j).1 = (D.trace j).Q ∧ (D.completion j).2 = (D.trace j).H) ∧
      CubicExactCertificateEnumeration C hdim hC x D ∧
      WorstCaseDenseOutputOptimal := by
  -- BLOCKER: needs-substrate(uniform exact-arithmetic compiler for the shared
  -- Gaussian-elimination/matching construction, with a cubic execution proof)
  sorry

/-- Package the inputs on which an irreducible certificate run may depend. -/
-- @node: IrreducibleCertificateRunInput
structure IrreducibleCertificateRunInput where
  p : ℕ
  n : ℕ
  C : MixingMatrix p n
  hC : FullRowRank C
  hC0 : NonzeroColumns C
  hCdir : DistinctDirections C
  x : Fin p

/-- The dependent result type of a packaged irreducible certificate run. -/
-- @node: IrreducibleCertificateRunInput.Result
def IrreducibleCertificateRunInput.Result (input : IrreducibleCertificateRunInput) :=
  CertificateData input.C input.x

/-- An execution producing every certificate output also produces any requested pair of its
dense witnesses, with exactly the same registers and shared-run linkage. -/
-- @node: computesWitnessPair_of_computesCertificate
lemma computesWitnessPair_of_computesCertificate {p n : ℕ}
    (program : ExactArithmeticProgram p n) (C : MixingMatrix p n)
    (hdim : ValidPopulationDimensions p n) (hC : FullRowRank C) (x : Fin p)
    (D : CertificateData C x) (hcomp : program.ComputesCertificate C hC x D)
    (j k : Fin n) (hj : j ∈ admissibleSources C x) (hk : k ∈ admissibleSources C x) :
    program.ComputesWitnessPair C hdim hC x D j k hj hk := by
  rcases hcomp with ⟨registers, hexec, _hadmissible, _hscalar, _hvector, hwitness⟩
  refine ⟨registers, hexec, ?_, (hwitness j hj).2.1, (hwitness k hk).2.1,
    (hwitness j hj).2.2, (hwitness k hk).2.2⟩
  intro row col
  exact ⟨(hwitness j hj).1 row col |>.1, (hwitness j hj).1 row col |>.2,
    (hwitness k hk).1 row col |>.1, (hwitness k hk).1 row col |>.2⟩

/-- A shared cubic all-witness enumeration yields cubic production of any requested witness pair
after its shared basis extension and inverse.  The pair algorithm owns the same certificate run,
including at the particular input supplied by the caller. -/
-- @node: cubicWitnessPairAfterSharedInverse_of_irreducibleEnumeration
lemma cubicWitnessPairAfterSharedInverse_of_irreducibleEnumeration {p n : ℕ}
    (C : MixingMatrix p n) (hdim : ValidPopulationDimensions p n) (hC : FullRowRank C)
    (hC0 : NonzeroColumns C) (hCdir : DistinctDirections C) (x : Fin p)
    (D : CertificateData C x)
    (hcubic : CubicExactIrreducibleCertificateEnumeration C hdim hC hC0 hCdir x D)
    (j k : Fin n) (hj : j ∈ admissibleSources C x) (hk : k ∈ admissibleSources C x) :
    CubicWitnessPairAfterSharedInverse C hdim hC hC0 hCdir x D j k hj hk := by
  classical
  rcases hcubic with ⟨certificateAlgorithm, hcubic, _huses, hcurrent⟩
  rcases hcubic with ⟨c, n0, hc, hbound⟩
  let target : IrreducibleCertificateRunInput := ⟨p, n, C, hC, hC0, hCdir, x⟩
  let fallback : (input : IrreducibleCertificateRunInput) → input.Result := fun input =>
    if hex : ∃ E : CertificateData input.C input.x,
        certificateAlgorithm.ComputesCertificate input.C input.hC input.x E
      then Classical.choose hex
      else Classical.choice (certificateData_nonempty input.C input.hC input.x)
  let selected : (input : IrreducibleCertificateRunInput) → input.Result :=
    Function.update fallback target D
  let pairAlgorithm : UniformExactPairAlgorithm :=
    { program := fun p n x _j _k => certificateAlgorithm.program p n x
      run := fun {p n} C hC hC0 hCdir x => selected ⟨p, n, C, hC, hC0, hCdir, x⟩ }
  have hpairCubic : IsUniformlyCubicPairAfterSharedInverse pairAlgorithm := by
    refine ⟨c + 4, n0, by omega, ?_⟩
    intro p' n' C' hdim' hC' hC0' hCdir' x' j' k' hj' hk' hn'
    let input : IrreducibleCertificateRunInput :=
      ⟨p', n', C', hC', hC0', hCdir', x'⟩
    obtain ⟨E, _husesE, hcompE, hcostE⟩ :=
      hbound C' hdim' hC' hC0' hCdir' x' hn'
    have hex : ∃ E : CertificateData C' x',
        certificateAlgorithm.ComputesCertificate C' hC' x' E := ⟨E, hcompE⟩
    have hselected : certificateAlgorithm.ComputesCertificate C' hC' x' (selected input) := by
      let Good : {input : IrreducibleCertificateRunInput} → input.Result → Prop :=
        fun {input} E =>
          certificateAlgorithm.ComputesCertificate input.C input.hC input.x E
      change Good (Function.update fallback target D input)
      apply (Function.pred_update (@Good) fallback target D input).2
      by_cases hit : input = target
      · left
        refine ⟨hit, ?_⟩
        simpa [Good, target] using hcurrent
      · have hfallback : certificateAlgorithm.ComputesCertificate C' hC' x'
            (fallback input) := by
          dsimp only [fallback]
          split
          · exact Classical.choose_spec ‹∃ E, _›
          · contradiction
        right
        exact ⟨hit, hfallback⟩
    refine ⟨computesWitnessPair_of_computesCertificate
      (certificateAlgorithm.program p' n' x') C' hdim' hC' x' (selected input)
      hselected j' k' hj' hk', ?_⟩
    change (certificateAlgorithm.program p' n' x').code.length + 4 * n' * n' ≤
      (c + 4) * n' ^ 3
    have hcode : (certificateAlgorithm.program p' n' x').code.length ≤
        certificateAlgorithm.cost C' x' := by
      simp [UniformExactCertificateAlgorithm.cost, ExactArithmeticProgram.cost]
    have hp' : 2 ≤ p' := hdim'.1
    have hpn' : p' ≤ n' := hdim'.2
    have hnpos : 1 ≤ n' := le_trans (by omega : 1 ≤ p') hpn'
    have hsq : n' * n' ≤ n' ^ 3 := by
      calc
        n' * n' ≤ n' * n' * n' := by
          simpa using Nat.mul_le_mul_left (n' * n') hnpos
        _ = n' ^ 3 := by ring
    calc
      (certificateAlgorithm.program p' n' x').code.length + 4 * n' * n' ≤
          c * n' ^ 3 + 4 * n' * n' := Nat.add_le_add_right (hcode.trans hcostE) _
      _ ≤ (c + 4) * n' ^ 3 := by nlinarith
  refine ⟨pairAlgorithm, hpairCubic, ?_, ?_⟩
  · change D = selected target
    exact (Function.update_self target D fallback).symm
  · exact computesWitnessPair_of_computesCertificate
      (certificateAlgorithm.program p n x) C hdim hC x D hcurrent j k hj hk

-- @node: lem:shear-matching-sufficiency
lemma certifiedCompletion_mem_fiber {p n : ℕ} (C : MixingMatrix p n)
    (x : Fin p) (hdim : ValidPopulationDimensions p n) (hC : FullRowRank C) :
    ∃ D : CertificateData C x, ∀ (j : Fin n) (hj : j ∈ admissibleSources C x),
      let hpn := D.dim_le
      (D.trace ⟨j, hj⟩).Q = (certifiedCompletion C x D j hj).1 ∧
      (D.trace ⟨j, hj⟩).H = (certifiedCompletion C x D j hj).2 ∧
      CompletionFiber C hpn x (certifiedCompletion C x D j hj).1
          (certifiedCompletion C x D j hj).2 ∧
        (∃ hmono : MonomialSourceAssignment (certifiedCompletion C x D j hj).2,
          assignedSource (certifiedCompletion C x D j hj).2 hmono
            (Fin.castLE hpn x) = j) ∧
        (IsRationalMatrix C →
          IsRationalMatrix (certifiedCompletion C x D j hj).1 ∧
            IsRationalMatrix (certifiedCompletion C x D j hj).2) := by
  obtain ⟨D, _hKernel, _hAdmissible, hCompletion, hRational,
      hTrace, _hCubic, _hOptimal⟩ :=
    shared_kernel_matching_certificate C hdim hC x
  refine ⟨D, ?_⟩
  intro j hj
  have hcompletion := hCompletion j hj
  have hvalid := hcompletion.1
  have hassigned := hcompletion.2
  have hrat := hRational
  have htrace := hTrace ⟨j, hj⟩
  dsimp only [certifiedCompletion]
  refine ⟨htrace.1.symm, htrace.2.symm, hvalid, ?_, ?_⟩
  · exact ⟨hvalid.monomial, hassigned⟩
  · intro hCrat
    exact hrat hCrat j hj

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier
