import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Basic
import Causalean.Mathlib.Combinatorics.JohnsonKneser.Harmonics
import Causalean.Mathlib.Combinatorics.JohnsonKneser.Kneser
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic

/-!
# Johnson components and Kneser covariance

This file gives the paper's data-only projection family, normalized disjointness
operator, spectral multipliers, covariance functionals, and two cited logical gates.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

open Causalean.Mathlib.Combinatorics.JohnsonKneser

-- @env: S2
variable (n M : ℕ)

/-- The canonical degree-`k` Johnson harmonic space: the degree-at-most-`k`
space orthogonal to all lower-degree inclusion monomials. -/
def johnsonHarmonicSpace (n M : ℕ) (hM : M ≤ n) (k : Fin (M + 1)) :
    Set (Omega n M → ℝ) :=
  {f | WithLp.toLp 2 f ∈ johnsonHarmonic n M k.1}
  -- @realizes \mathcal H_{n,k}(canonical inclusion-degree harmonic space)

/-- Genuine orthogonal Johnson projections onto the canonical harmonic degree
spaces, including the centered orthogonal decomposition asserted in the paper. -/
structure JohnsonProjections (n M : ℕ) where
  slice_nonempty : M ≤ n
  proj : Fin (M + 1) → (Omega n M → ℝ) → (Omega n M → ℝ)
    -- @realizes \Pi_{n,k}(orthogonal projection onto canonical degree k)
  map_add : ∀ k f g, proj k (fun A => f A + g A) = fun A => proj k f A + proj k g A
  map_smul : ∀ k (c : ℝ) f, proj k (fun A => c * f A) = fun A => c * proj k f A
  range_eq : ∀ k, Set.range (proj k) = johnsonHarmonicSpace n M slice_nonempty k
  fixes_range : ∀ k f, f ∈ johnsonHarmonicSpace n M slice_nonempty k → proj k f = f
  residual_orthogonal : ∀ k f g, g ∈ johnsonHarmonicSpace n M slice_nonempty k →
    sliceInner n M slice_nonempty (fun A => f A - proj k f A) g = 0

/-- The canonical Johnson projection family supplied by the reusable
Johnson--Kneser substrate. -/
noncomputable def canonicalJohnsonProjections (n M : ℕ) (hM : M ≤ n) :
    JohnsonProjections n M := by
  let p : Fin (M + 1) → (Omega n M → ℝ) → (Omega n M → ℝ) :=
    fun k f A => harmonicProjection n M k (WithLp.toLp 2 f) A
  refine {
    slice_nonempty := hM
    proj := p
    map_add := ?_
    map_smul := ?_
    range_eq := ?_
    fixes_range := ?_
    residual_orthogonal := ?_ }
  · intro k f g
    funext A
    dsimp [p]
    exact congrArg (fun q => q A) (harmonicProjection_add k
      (WithLp.toLp 2 f) (WithLp.toLp 2 g))
  · intro k c f
    funext A
    dsimp [p]
    exact congrArg (fun q => q A)
      (harmonicProjection_smul k c (WithLp.toLp 2 f))
  · intro k
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      exact harmonicProjection_mem k (WithLp.toLp 2 g)
    · intro hf
      refine ⟨f, ?_⟩
      funext A
      dsimp [p]
      exact congrArg (fun q => q A) ((harmonicProjection_eq_self_iff k
        (WithLp.toLp 2 f)).2 hf)
  · intro k f hf
    funext A
    dsimp [p]
    exact congrArg (fun q => q A) ((harmonicProjection_eq_self_iff k
      (WithLp.toLp 2 f)).2 hf)
  · intro k f g hg
    rw [sliceInner, slice]
    simp only [completeRandomization, FiniteDesign.E, one_div]
    rw [← Finset.mul_sum]
    exact sliceInner_residual_eq_zero hM k
      (WithLp.toLp 2 f) (WithLp.toLp 2 g) hg

/-- The degree-indexed component family of a slice function. -/
-- @node: def:johnson-decomposition
def johnsonComponents (J : JohnsonProjections n M) (f : Omega n M → ℝ) :
    Fin (M + 1) → (Omega n M → ℝ) := fun k => J.proj k f

/-- The unnormalized Kneser adjacency sum. -/
noncomputable def kneserAdjacency (f : Omega n M → ℝ) (A : Omega n M) : ℝ :=
  ∑ C ∈ (Finset.univ.filter fun C : Omega n M => Disjoint C.1 A.1), f C

/-- [When two groups fit in the population](hyp:h2M), [every Kneser neighborhood has the stated cardinality](goal). -/
lemma kneserDegree (h2M : 2 * M ≤ n) (A : Omega n M) :
    ((Finset.univ.filter fun C : Omega n M => Disjoint C.1 A.1).card) =
      (n - M).choose M := by
  rw [← Fintype.card_coe]
  let e : {C : Omega n M // Disjoint C.1 A.1} ≃
      ↥(Finset.powersetCard M A.1ᶜ) := {
    toFun := fun C => ⟨C.1.1, by
      rw [Finset.mem_powersetCard]
      exact ⟨by
        rw [Finset.subset_iff]
        intro x hx
        simp only [Finset.mem_compl]
        exact Finset.disjoint_left.mp C.2 hx, C.1.2⟩⟩
    invFun := fun C => ⟨⟨C.1, (Finset.mem_powersetCard.mp C.2).2⟩, by
      rw [Finset.disjoint_left]
      intro x hx
      exact (by
        have := (Finset.mem_powersetCard.mp C.2).1 hx
        simpa using this)⟩
    left_inv := by intro C; cases C; rfl
    right_inv := by intro C; cases C; rfl }
  let e0 : ↥(Finset.univ.filter fun C : Omega n M => Disjoint C.1 A.1) ≃
      {C : Omega n M // Disjoint C.1 A.1} := {
    toFun := fun C => ⟨C.1, (Finset.mem_filter.mp C.2).2⟩
    invFun := fun C => ⟨C.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.2⟩⟩
    left_inv := by intro C; cases C; rfl
    right_inv := by intro C; cases C; rfl }
  calc
    Fintype.card ↥(Finset.univ.filter fun C : Omega n M => Disjoint C.1 A.1) =
        Fintype.card {C : Omega n M // Disjoint C.1 A.1} := Fintype.card_congr e0
    _ = Fintype.card ↥(Finset.powersetCard M A.1ᶜ) := Fintype.card_congr e
    _ = (n - M).choose M := by
      rw [Fintype.card_coe, Finset.card_powersetCard,
        Finset.card_compl, Fintype.card_fin, A.2]

/-- The normalized Kneser disjointness operator. -/
noncomputable def kneserOp (f : Omega n M → ℝ) (A : Omega n M) : ℝ :=
  kneserAdjacency n M f A / ((n - M).choose M : ℝ)
  -- @realizes \mathsf K_n(normalized disjointness average)

/-- The normalized degree-`k` Kneser eigenvalue. -/
noncomputable def kneserEigenvalue (k : Fin (M + 1)) : ℝ :=
  (-1 : ℝ) ^ k.1 * (M.descFactorial k.1 : ℝ) /
    ((n - M).descFactorial k.1 : ℝ)
  -- @realizes \lambda_{n,k}(falling-factorial eigenvalue)

/-- Ordered-disjoint covariance of two arm tables. -/
-- @node: def:kneser-covariance
noncomputable def crossCov (hM : M ≤ n) (Y : PotentialOutcome n M)
    (a b : Arm) : ℝ :=
  sliceInner n M hM (armTableCentered n M hM Y a)
    (kneserOp n M (armTableCentered n M hM Y b))
  -- @realizes C_{ab,n}(ordered-disjoint covariance)

/-- Ordered-disjoint covariance of the arm contrast. -/
noncomputable def crossCovContrast (hM : M ≤ n) (Y : PotentialOutcome n M) : ℝ :=
  crossCov n M hM Y true true + crossCov n M hM Y false false -
    2 * crossCov n M hM Y true false
  -- @realizes C_{\tau\tau,n}(C11 plus C00 minus twice C10)

/-- Ordered pairs of disjoint slice elements. -/
abbrev OrderedDisjointPair (n M : ℕ) :=
  {P : Omega n M × Omega n M // Disjoint P.1.1 P.2.1}

/-- A uniform design on any inhabited finite type. -/
noncomputable def uniformFiniteDesign (α : Type*) [Fintype α] [Nonempty α] : FiniteDesign α := by
  classical
  exact {
    p := fun _ => 1 / (Fintype.card α : ℝ)
    p_nonneg := fun _ => one_div_nonneg.mpr (Nat.cast_nonneg _)
    p_sum := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hc : (Fintype.card α : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      field_simp [hc] }

/-- If [twice the group size does not exceed the population](hyp:h2M), then [the ordered-disjoint-pair type is nonempty](goal). -/
lemma orderedDisjointPair_nonempty (h2M : 2 * M ≤ n) :
    Nonempty (OrderedDisjointPair n M) := by
  classical
  have hMn : M ≤ n := by omega
  obtain ⟨A, -, hAcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
      (n := M) (by simpa using hMn)
  have hMcomp : M ≤ Aᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, hAcard]
    omega
  obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hMcomp
  exact ⟨⟨(⟨A, hAcard⟩, ⟨C, hCcard⟩), by
    rw [Finset.disjoint_left]
    intro x hxA hxC
    have hxcomp := hCsub hxC
    simpa [hxA] using hxcomp⟩⟩

/-- The uniform ordered-disjoint-pair design. -/
noncomputable def orderedDisjointPairDesign (h2M : 2 * M ≤ n) :
    FiniteDesign (OrderedDisjointPair n M) := by
  letI : Nonempty (OrderedDisjointPair n M) := orderedDisjointPair_nonempty n M h2M
  exact uniformFiniteDesign (OrderedDisjointPair n M)

/-- Ordered disjoint pairs are a dependent pair of a slice element and a
disjoint second slice element. -/
-- @node: orderedPairSigmaEquiv
def orderedPairSigmaEquiv (n M : ℕ) : OrderedDisjointPair n M ≃
    Σ A : Omega n M, {C : Omega n M // Disjoint C.1 A.1} where
  toFun P := ⟨P.1.1, ⟨P.1.2, P.2.symm⟩⟩
  invFun P := ⟨(P.1, P.2.1), P.2.2.symm⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

/-- [When two groups fit in the population](hyp:h2M), [the fiber of groups disjoint from a fixed group has the Kneser degree](goal). -/
-- @node: orderedDisjointFiber_card
lemma orderedDisjointFiber_card (h2M : 2 * M ≤ n) (A : Omega n M) :
    Fintype.card {C : Omega n M // Disjoint C.1 A.1} = (n - M).choose M := by
  let e : {C : Omega n M // Disjoint C.1 A.1} ≃
      ↥(Finset.univ.filter fun C : Omega n M => Disjoint C.1 A.1) := {
    toFun := fun C => ⟨C.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.2⟩⟩
    invFun := fun C => ⟨C.1, (Finset.mem_filter.mp C.2).2⟩
    left_inv := by intro C; cases C; rfl
    right_inv := by intro C; cases C; rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]
  exact kneserDegree n M h2M A

/-- [When two groups fit in the population](hyp:h2M), [the ordered-disjoint-pair space has slice cardinality times Kneser degree](goal). -/
-- @node: orderedDisjointPair_card
lemma orderedDisjointPair_card (h2M : 2 * M ≤ n) :
    Fintype.card (OrderedDisjointPair n M) = n.choose M * (n - M).choose M := by
  rw [Fintype.card_congr (orderedPairSigmaEquiv n M), Fintype.card_sigma]
  simp_rw [orderedDisjointFiber_card n M h2M]
  simp [Fintype.card_finset_len]

/-- For two slice functions, [a sum over ordered disjoint pairs is the corresponding iterated slice-and-neighborhood sum](goal). -/
-- @node: orderedDisjointPair_sum
lemma orderedDisjointPair_sum (f g : Omega n M → ℝ) :
    (∑ P : OrderedDisjointPair n M, f P.1.1 * g P.1.2) =
      ∑ A : Omega n M,
        ∑ C ∈ (Finset.univ.filter fun C : Omega n M => Disjoint C.1 A.1),
          f A * g C := by
  calc
    (∑ P : OrderedDisjointPair n M, f P.1.1 * g P.1.2) =
        ∑ Q : Σ A : Omega n M, {C : Omega n M // Disjoint C.1 A.1},
          f Q.1 * g Q.2.1 := by
            exact Fintype.sum_equiv (orderedPairSigmaEquiv n M) _ _ (fun _ => rfl)
    _ = ∑ A : Omega n M, ∑ C : {C : Omega n M // Disjoint C.1 A.1},
          f A * g C.1 := by
            apply Fintype.sum_sigma
    _ = ∑ A : Omega n M,
          ∑ C ∈ (Finset.univ.filter fun C : Omega n M => Disjoint C.1 A.1),
            f A * g C := by
      apply Finset.sum_congr rfl
      intro A _
      let e : {C : Omega n M // Disjoint C.1 A.1} ≃
          ↥(Finset.univ.filter fun C : Omega n M => Disjoint C.1 A.1) := {
        toFun := fun C => ⟨C.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.2⟩⟩
        invFun := fun C => ⟨C.1, (Finset.mem_filter.mp C.2).2⟩
        left_inv := by intro C; cases C; rfl
        right_inv := by intro C; cases C; rfl }
      calc
        (∑ C : {C : Omega n M // Disjoint C.1 A.1}, f A * g C.1) =
            ∑ C : ↥(Finset.univ.filter fun C : Omega n M => Disjoint C.1 A.1),
              f A * g C.1 := by
                exact Fintype.sum_equiv e _ _ (fun _ => rfl)
        _ = ∑ C ∈ (Finset.univ.filter fun C : Omega n M => Disjoint C.1 A.1),
              f A * g C := by
          change (∑ C ∈ (Finset.univ.filter fun C : Omega n M =>
            Disjoint C.1 A.1).attach, f A * g C.1) = _
          exact Finset.sum_attach _ (fun C => f A * g C)

/-- [When two groups fit in the population](hyp:h2M), [ordered-pair expectation agrees with the Kneser inner-product formula](goal). -/
-- @node: orderedDisjointPair_E_eq
lemma orderedDisjointPair_E_eq (h2M : 2 * M ≤ n) (f g : Omega n M → ℝ) :
    (orderedDisjointPairDesign n M h2M).E (fun P => f P.1.1 * g P.1.2) =
      sliceInner n M (by omega) f (kneserOp n M g) := by
  classical
  have hnchoose : n.choose M ≠ 0 := Nat.choose_ne_zero (by omega)
  have hdegchoose : (n - M).choose M ≠ 0 := Nat.choose_ne_zero (by omega)
  simp only [orderedDisjointPairDesign, uniformFiniteDesign, FiniteDesign.E,
    sliceInner, slice, completeRandomization, kneserOp, kneserAdjacency]
  rw [← Finset.mul_sum]
  rw [orderedDisjointPair_sum n M f g, orderedDisjointPair_card n M h2M]
  simp only [Fintype.card_finset_len, Fintype.card_fin]
  have hcollapse :
      (∑ A : Omega n M,
        ∑ C ∈ (Finset.univ.filter fun C : Omega n M => Disjoint C.1 A.1),
          f A * g C) =
      ∑ A : Omega n M, f A *
        ∑ C ∈ (Finset.univ.filter fun C : Omega n M => Disjoint C.1 A.1), g C := by
    apply Finset.sum_congr rfl
    intro A _
    rw [Finset.mul_sum]
  rw [hcollapse]
  push_cast
  rw [← Finset.mul_sum]
  simp_rw [div_eq_mul_inv, mul_assoc]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  field_simp

/-- [When two groups fit in the population](hyp:h2M), [the quotient of unnormalized Kneser eigenvalue magnitudes is the ratio of the corresponding falling factorials](goal). -/
-- @node: kneserChooseRatio_eq_descFactorialRatio
lemma kneserChooseRatio_eq_descFactorialRatio (h2M : 2 * M ≤ n)
    (k : Fin (M + 1)) :
    (((n - M - k.1).choose (M - k.1) : ℕ) : ℝ) /
        (((n - M).choose M : ℕ) : ℝ) =
      (M.descFactorial k.1 : ℝ) / ((n - M).descFactorial k.1 : ℝ) := by
  have hkM : k.1 ≤ M := by omega
  have hMn : M ≤ n - M := by omega
  have hkden : 0 < (n - M).descFactorial k.1 :=
    Nat.descFactorial_pos.mpr (by omega)
  have hchoose : 0 < (n - M).choose M := Nat.choose_pos hMn
  have hsplit := Nat.descFactorial_mul_descFactorial (n := n - M) hkM
  have hfac := Nat.factorial_mul_descFactorial (n := M) hkM
  have hnum := Nat.descFactorial_eq_factorial_mul_choose (n - M - k.1) (M - k.1)
  have htotal := Nat.descFactorial_eq_factorial_mul_choose (n - M) M
  have hcrossNat :
      (n - M - k.1).choose (M - k.1) * (n - M).descFactorial k.1 =
        M.descFactorial k.1 * (n - M).choose M := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos (M - k.1))
    calc
      (M - k.1).factorial *
          ((n - M - k.1).choose (M - k.1) * (n - M).descFactorial k.1) =
          (n - M - k.1).descFactorial (M - k.1) *
            (n - M).descFactorial k.1 := by rw [hnum]; ac_rfl
      _ = (n - M).descFactorial M := hsplit
      _ = M.factorial * (n - M).choose M := htotal
      _ = ((M - k.1).factorial * M.descFactorial k.1) *
            (n - M).choose M := by rw [hfac]
      _ = (M - k.1).factorial *
            (M.descFactorial k.1 * (n - M).choose M) := by ac_rfl
  field_simp
  exact_mod_cast hcrossNat.trans (by ac_rfl)

/-- Yuval Filmus (2016), *An Orthogonal Basis for Functions over a Slice of the
Boolean Hypercube*, Theorem 4.1 and Lemma 4.3, arXiv:1406.0142v2, pp. 10 and 12.
The cited result supplies the orthogonal direct-sum decomposition of functions on
the uniform slice and the Bose--Mesner eigenspace identification. -/
def JohnsonOrthogonalDecomposition (n M : ℕ) (J : JohnsonProjections n M) : Sort 0 :=
  ∀ h2M : 2 * M ≤ n,
    (∀ f A,
      (∑ k ∈ (Finset.univ.filter fun k : Fin (M + 1) => 0 < k.1), J.proj k f A) =
        f A - (slice n M (by omega)).E f) ∧
    (∀ k l f g, k ≠ l →
      sliceInner n M (by omega) (J.proj k f) (J.proj l g) = 0)

/-- Andries E. Brouwer, Sebastian M. Cioaba, Ferdinand Ihringer, and Matt
McGinnis (2018), *The Smallest Eigenvalues of Hamming Graphs, Johnson Graphs and
Other Distance-Regular Graphs with Classical Parameters*, Proposition 3.1,
arXiv:1709.09011, p. 10.  It gives the unnormalized Kneser adjacency eigenvalue
`(-1)^k * choose (n-M-k) (M-k)`. -/
def KneserAdjacencySpectrum (n M : ℕ) : Sort 0 :=
  ∀ h2M : 2 * M ≤ n, ∀ (k : Fin (M + 1)) (f : Omega n M → ℝ),
    f ∈ johnsonHarmonicSpace n M (by omega) k →
    kneserAdjacency n M f =
      fun A => ((-1 : ℝ) ^ k.1 * ((n - M - k.1).choose (M - k.1) : ℝ)) *
        f A

/-- [For a feasible slice size](hyp:hM), [the canonical projection family has the Johnson orthogonal decomposition required here](goal). -/
-- @node: lem:classical-johnson-decomposition
lemma canonicalJohnsonOrthogonalDecomposition (n M : ℕ) (hM : M ≤ n) :
    JohnsonOrthogonalDecomposition n M (canonicalJohnsonProjections n M hM) := by
  intro h2M
  constructor
  · intro f A
    have h := sum_positive_harmonicProjection_eq_center (by omega)
      (WithLp.toLp 2 f)
    let A' : Causalean.Mathlib.Combinatorics.JohnsonKneser.Omega n M :=
      ⟨A.1, A.2⟩
    have hA := congrFun (congrArg WithLp.ofLp h) A'
    simp only [WithLp.ofLp_sum] at hA
    rw [Finset.sum_apply A'
      (Finset.univ.filter (fun i : Fin (M + 1) => 0 < i.1))] at hA
    simp [center, constFn] at hA
    have hE : (slice n M (by omega)).E f = mean (WithLp.toLp 2 f) := by
      rw [slice]
      simp only [completeRandomization, FiniteDesign.E, one_div, mean]
      rw [completeRandomization_card, Fintype.card_fin,
        Causalean.Mathlib.Combinatorics.JohnsonKneser.card_omega (by omega),
        ← Finset.mul_sum]
      rfl
    rw [hE]
    simpa [canonicalJohnsonProjections, center, constFn, Finset.sum_apply, A',
      Pi.sub_apply] using hA
  · intro k l f g hkl
    rw [sliceInner, slice]
    simp only [completeRandomization, FiniteDesign.E, one_div]
    rw [← Finset.mul_sum]
    exact johnsonHarmonic_pairwise_orthogonal (by omega) hkl
      (harmonicProjection_mem k (WithLp.toLp 2 f))
      (harmonicProjection_mem l (WithLp.toLp 2 g))

/-- [The canonical Kneser adjacency operator has the stated harmonic spectrum](goal). -/
-- @node: lem:classical-kneser-spectrum
lemma canonicalKneserAdjacencySpectrum (n M : ℕ) :
    KneserAdjacencySpectrum n M := by
  intro h2M k f hf
  have h := Causalean.Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency_eigen
    h2M k (WithLp.toLp 2 f) hf
  funext A
  have hA := congrFun (congrArg WithLp.ofLp h) A
  simp only [WithLp.ofLp_smul] at hA
  change (∑ x, if Disjoint A.1 x.1 then f x else 0) =
    ((-1 : ℝ) ^ k.1 * ((n - M - k.1).choose (M - k.1) : ℝ)) * f A at hA
  simpa [kneserAdjacency,
    Causalean.Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency,
    Finset.sum_filter, disjoint_comm,
    mul_ite, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul] using hA

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
