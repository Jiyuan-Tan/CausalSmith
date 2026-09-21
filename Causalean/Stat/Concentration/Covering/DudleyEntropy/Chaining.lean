module
public import Causalean.Stat.Concentration.Rademacher.Rademacher
public import Causalean.Stat.Concentration.Covering.EmpiricalPseudoMetric
public import Causalean.Stat.Concentration.TailBounds.Massart
public import Causalean.Stat.Concentration.Covering.CoveringNumber
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Group.CompleteLattice
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Finite Dudley chains

This file constructs dyadic cover approximations and chain increments in the
empirical pseudometric. It establishes boundedness of the main and increment
suprema and splits the signed Rademacher average into the pieces estimated by
the later parts of the Dudley argument.
-/

@[expose] public section

-- Adapted from auto-res/lean-rademacher FoML/DudleyEntropy.lean and FoML/Main.lean
-- (commit 72d28921dc960f47691640fb973303a1be9d13ca, MIT License (c) 2025 AutoRes).



namespace Causalean.Stat.Concentration

universe v u
open scoped BigOperators
open ProbabilityTheory

section Empirical
variable {Z : Type v}
variable {n m : ℕ} {ι : Type u} [Nonempty ι]
variable {F : ι → Z → ℝ}
variable {S : Fin m → Z}

/-- A nonnegative term in a finite sum is bounded by the full sum of
nonnegative terms. -/
theorem term_le_total_sum_of_nonneg {α : Type u} [Fintype α]
    {M : Type*} [AddCommMonoid M] [Preorder M] [IsOrderedAddMonoid M]
    (j : α) (f : α → M) (h0 : ∀ j, 0 ≤ f j) :
  f j ≤ ∑ i : α, f i := by
  classical
  have hj : j ∈ (Finset.univ : Finset α) := by simp
  have hsum :
      (Finset.univ.erase j).sum (fun i : α => f i) + f j =
        ∑ i : α, f i := by
    exact Finset.sum_erase_add _ _ hj
  have h_nonneg :
      0 ≤ (Finset.univ.erase j).sum (fun i : α => f i) := by
    refine Finset.sum_nonneg ?_
    intro i hi
    exact h0 i
  have h_le :
      f j ≤ (Finset.univ.erase j).sum (fun i : α => f i) + f j := by
    simpa [add_comm] using add_le_add_left h_nonneg (f j)
  exact h_le.trans_eq hsum


variable {c : ℝ}
  -- Dyadic radius sequence, associated cover, and cover cardinality.
/-- The dyadic radius at a chaining level is the initial radius divided by two repeatedly at each
successive level. These radii set the resolution of the finite covers in the Dudley entropy
argument. -/
noncomputable abbrev ej (c : ℝ) : ℕ → ℝ := fun j ↦ c/(2^j : ℝ)

/-- When [the initial radius is positive](hyp:c_pos), [every dyadic chaining radius is
positive](goal). -/
lemma ej_pos (c_pos : 0 < c) : ∀ j, (ej c j > 0) := by
  intro j
  dsimp [ej]
  simp only [gt_iff_lt, Nat.ofNat_pos, pow_pos, div_pos_iff_of_pos_right]
  exact c_pos

/-- At each positive dyadic radius, this selects a finite cover of the empirical function class.
The selected cover supplies the approximation candidates at that level of the chaining
construction. -/
noncomputable abbrev cj (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (j : ℕ)
  := coveringFinset h (ej_pos c_pos j)
  -- Factor out commonly used expressions
/-- For [a sample size](hyp:m), the [inverse sign-vector count](goal) is the reciprocal of the
number of possible Rademacher sign vectors of that length. It normalizes the averages over signs
in the chaining argument. -/
noncomputable abbrev signs_card_inv (m : ℕ) : ℝ := (Fintype.card (Signs m) : ℝ)⁻¹

/-- When [the initial radius is positive](hyp:c_pos), [every dyadic chaining radius is
nonnegative](goal). -/
lemma ej_nonneg (c_pos : 0 < c) : ∀ j, (0 ≤ ej c j) :=
  fun j ↦ le_of_lt (ej_pos c_pos j)
/-- [The empirical function space of a nonempty indexed class is nonempty](goal). -/
lemma e_nonempty :
    (Set.univ : Set (EmpiricalFunctionSpace F S)).Nonempty := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  exact ⟨⟨i⟩, by simp⟩

omit [Nonempty ι] in
/-- For [a positive initial radius](hyp:c_pos) and [a totally bounded empirical function
space](hyp:h), [every indexed function has a representative in each finite dyadic cover within
that cover's radius](goal). -/
lemma exists_cover_approximation (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
  (fh : ι) (j : ℕ) :
  ∃ f_j : EmpiricalFunctionSpace F S,
    f_j ∈ cj c_pos h j ∧ empiricalDist S (F fh) f_j ≤ ej c j := by
  have : ⟨fh⟩ ∈ ⋃ y ∈ coveringFinset h (ej_pos c_pos j), Metric.ball y (ej c j)
    := coveringFinset_cover h (ej_pos c_pos j) (Set.mem_univ fh)
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp this
  obtain ⟨hy', hy''⟩ := Set.mem_iUnion.mp hy
  use ⟨y.index⟩
  constructor
  · exact hy'
  · exact le_of_lt hy''

/-- Each function in the empirical class is assigned one representative from the finite cover at
every dyadic resolution. The assigned representative is within that resolution's radius and is
used to form the chaining approximation. -/
noncomputable def coverApprox (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) :
    ι → ℕ → EmpiricalFunctionSpace F S :=
    fun fh j => Classical.choose (exists_cover_approximation c_pos h fh j)

omit [Nonempty ι] in
/-- For [a positive initial radius](hyp:c_pos) and [a totally bounded empirical function
space](hyp:h), [the chosen approximation belongs to its finite dyadic cover](goal). -/
lemma coverApprox_mem_cover (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (fh : ι) (j : ℕ) : coverApprox c_pos h fh j ∈ cj c_pos h j := by
  classical
  exact (Classical.choose_spec (exists_cover_approximation c_pos h fh j)).1

omit [Nonempty ι] in
/-- For [a positive initial radius](hyp:c_pos) and [a totally bounded empirical function
space](hyp:h), [the empirical distance from a function to its chosen cover representative is at
most the dyadic radius](goal). -/
lemma empiricalDist_coverApprox_le_radius (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (fh : ι) (j : ℕ) : empiricalDist S (F fh) (coverApprox c_pos h fh j) ≤ ej c j := by
  classical
  exact (Classical.choose_spec (exists_cover_approximation c_pos h fh j)).2

/-- The chaining approximation is zero at the coarsest level and otherwise uses the selected
finite-cover representative at the corresponding dyadic resolution. It provides the successive
approximations whose increments control empirical Rademacher complexity. -/
noncomputable def chainApprox (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) :
    ι → ℕ → Z → ℝ :=
    fun fh j => if j = 0 then 0 else (coverApprox c_pos h fh j : Z → ℝ)

omit [Nonempty ι] in
/-- For [a positive initial radius](hyp:c_pos) and [a totally bounded empirical function
space](hyp:h), [the level-zero chain approximation is zero and every other level is the chosen
cover approximation](goal). -/
lemma chainApprox_def (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) :
    ∀ fh j,
      chainApprox c_pos h fh j =
        if j = 0 then 0 else (coverApprox c_pos h fh j : Z → ℝ) := by
    intro fh j
    dsimp [chainApprox]

omit [Nonempty ι] in
/-- For [a positive initial radius](hyp:c_pos) and [a totally bounded empirical function
space](hyp:h), [the chain approximation at every positive level equals the chosen cover
approximation at that level](goal). -/
lemma chainApprox_succ (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (fh : ι) (j : ℕ) :
    chainApprox c_pos h fh (j + 1) =
      (coverApprox c_pos h fh (j + 1) : Z → ℝ) := by
  simp [chainApprox]

omit [Nonempty ι] in
private lemma chain_decomposition (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
  (fh : ι) (n : ℕ) :
      F fh = F fh - chainApprox c_pos h fh n +
        ∑ j : Fin n,
          (chainApprox c_pos h fh ((j : ℕ) + 1) -
            chainApprox c_pos h fh ((j : ℕ))) := by
  induction n with
  | zero => simp [chainApprox]
  | succ n hn =>
    nth_rewrite 1 [hn]
    rw [Fin.sum_univ_castSucc]
    simp
    ring_nf

omit [Nonempty ι] in
/-- If every function has empirical norm at most a given bound on a positive-size
sample, then its absolute value at each sampled observation is at most the
sample-size square root times that bound. -/
lemma pointwise_bound_from_empirical_norm
    (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (i : Fin m) (hm_pos : 0 < m) :
    ∀ (f : ι), |F f (S i)| ≤ √↑m * c := by
  intro f
  dsimp [empiricalNorm] at cs
  have fcs := cs f
  -- from a finite-sample ℓ₂ bound to a pointwise bound via the coordinate projection inequality
  have hm_pos : 0 < (m : ℝ) := by norm_cast
  have hm_sqrt_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm_pos
  have hproj := empiricalDist_proj (S := S) (f := F f) (i := i)
  have hcancel : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt hm_sqrt_pos
  have h1 : |F f (S i)| ≤ √↑m * empiricalNorm S (F f) := by
    have hproj' := mul_le_mul_of_nonneg_left hproj (le_of_lt hm_sqrt_pos)
    -- simplify the left side using positivity of √m
    have hleft : √↑m * (|F f (S i)| / √↑m) = |F f (S i)| := by
      field_simp [hcancel]
    simpa [hleft] using hproj'
  calc
    |F f (S i)| ≤ √↑m * empiricalNorm S (F f) := h1
    _ ≤ √↑m * c := by
      apply mul_le_mul_of_nonneg_left fcs
      exact le_of_lt hm_sqrt_pos

private lemma chainApprox_pointwise_bound (c_pos : 0 < c) (m_pos : 0 < m)
    (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (i_1 : ℕ)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) :
    ∀ (i_2 : Fin m) (a : ι), |chainApprox c_pos h a i_1 (S i_2)| ≤ √↑m * c := by
  dsimp [chainApprox]
  by_cases h0 : i_1 = 0
  · rw [h0]
    simp only [↓reduceIte, Pi.zero_apply, abs_zero, forall_const]
    intro i_2
    have : 0 ≤ √↑m := by simp
    exact (mul_nonneg_iff_of_pos_right c_pos).mpr this
  · simp only [if_neg h0]
    intro i_2 a
    exact pointwise_bound_from_empirical_norm cs i_2 m_pos
      (coverApprox c_pos h a i_1).index

private lemma chainApprox_increment_bound (c_pos : 0 < c) (m_pos : 0 < m)
    (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (i_1 : ℕ)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) :
    ∀ (i_2 : Fin m) (a : ι),
      |chainApprox c_pos h a (i_1 + 1) (S i_2) -
        chainApprox c_pos h a (i_1) (S i_2)| ≤ 2 * (√↑m * c) := by
  intro i_2 a
  calc
  _ ≤ |chainApprox c_pos h a (i_1 + 1) (S i_2)| + |chainApprox c_pos h a i_1 (S i_2)| := by
    exact abs_sub (chainApprox c_pos h a (i_1 + 1) (S i_2)) (chainApprox c_pos h a i_1 (S i_2))
  _ ≤ √↑m * c + √↑m * c := by
    exact add_le_add
      (chainApprox_pointwise_bound c_pos m_pos cs (i_1 + 1) h i_2 a)
      (chainApprox_pointwise_bound c_pos m_pos cs i_1 h i_2 a)
  _ = _ := by ring

/-- The main remainder term in the Dudley chain has a finite upper bound. -/
theorem splitBound.bddAbove_main_term {c_pos : 0 < c}
    (cs : ∀ (f : ι), empiricalNorm S (F f) ≤ c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
  (m_pos : ¬m = 0)
  (i : Signs m) :
  BddAbove
    (Set.range fun fh ↦
      ∑ i_1,
        ↑↑(i i_1) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1))) := by
  rw [bddAbove_def]
  classical
  refine ⟨m * (2 * (Real.sqrt (m : ℝ) * c)), ?_⟩
  intro y hy
  rcases hy with ⟨fh, rfl⟩
  have hmpos : 0 < m := Nat.pos_of_ne_zero m_pos
  calc
    (∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1)))
        ≤ ∑ i_1, |(i i_1 : ℝ) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1))| := by
          refine Finset.sum_le_sum ?_
          intro _ _
          exact le_abs_self _
    _ = ∑ i_1, |F fh (S i_1) - chainApprox c_pos h fh n (S i_1)| := by
          apply Finset.sum_congr rfl
          intro _ _
          simp [abs_mul]
    _ ≤ ∑ i_1, (|F fh (S i_1)| + |chainApprox c_pos h fh n (S i_1)|) := by
          refine Finset.sum_le_sum ?_
          intro i_1 _
          have htri : |F fh (S i_1) - chainApprox c_pos h fh n (S i_1)|
              ≤ |F fh (S i_1)| + |chainApprox c_pos h fh n (S i_1)| := by
            exact abs_sub (F fh (S i_1)) (chainApprox c_pos h fh n (S i_1))
          exact htri
    _ ≤ ∑ i_1, (Real.sqrt (m : ℝ) * c + Real.sqrt (m : ℝ) * c) := by
          refine Finset.sum_le_sum ?_
          intro i_1 _
          have hF : |F fh (S i_1)| ≤ Real.sqrt (m : ℝ) * c :=
            pointwise_bound_from_empirical_norm cs i_1 hmpos fh
          have hG : |chainApprox c_pos h fh n (S i_1)| ≤ Real.sqrt (m : ℝ) * c :=
            chainApprox_pointwise_bound c_pos hmpos cs n h i_1 fh
          have :
              |F fh (S i_1)| + |chainApprox c_pos h fh n (S i_1)| ≤
                Real.sqrt (m : ℝ) * c + Real.sqrt (m : ℝ) * c := by
            nlinarith
          exact this
    _ = m * (2 * (Real.sqrt (m : ℝ) * c)) := by
      simp
      grind

/-- The sum of chaining increment terms has a finite upper bound. -/
theorem splitBound.bddAbove_increment_term {c_pos : 0 < c}
    (cs : ∀ (f : ι), empiricalNorm S (F f) ≤ c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
  (m_pos : ¬m = 0)
  (i : Signs m) :
  BddAbove
    (Set.range fun fh ↦
      ∑ x_1 : Fin n, ∑ i_1,
        ↑↑(i i_1) *
          (chainApprox c_pos h fh (↑x_1 + 1) (S i_1) -
            chainApprox c_pos h fh (↑x_1) (S i_1))) := by
  rw [bddAbove_def]
  classical
  refine ⟨(n : ℝ) * m * (2 * (Real.sqrt (m : ℝ) * c)), ?_⟩
  intro y hy
  rcases hy with ⟨fh, rfl⟩
  have hmpos : 0 < m := Nat.pos_of_ne_zero m_pos
  calc
    (∑ x_1 : Fin n, ∑ i_1,
      (i i_1 : ℝ) *
        (chainApprox c_pos h fh (↑x_1 + 1) (S i_1) -
          chainApprox c_pos h fh (↑x_1) (S i_1)))
        ≤ ∑ x_1 : Fin n, ∑ i_1,
          |(i i_1 : ℝ) *
            (chainApprox c_pos h fh (↑x_1 + 1) (S i_1) -
              chainApprox c_pos h fh (↑x_1) (S i_1))| := by
          refine Finset.sum_le_sum ?_
          intro _ _
          refine Finset.sum_le_sum ?_
          intro _ _
          exact le_abs_self _
        _ = ∑ x_1 : Fin n, ∑ i_1,
            |chainApprox c_pos h fh (↑x_1 + 1) (S i_1) -
              chainApprox c_pos h fh (↑x_1) (S i_1)| := by
          apply Finset.sum_congr rfl
          intro _ _
          apply Finset.sum_congr rfl
          intro i_1 _
          obtain ⟨v, hv⟩ := i i_1
          simp at hv
          cases hv with
          | inl hv => simp [hv]; rw [<- abs_neg]; apply congrArg; linarith
          | inr hv => simp [hv]
        _ ≤ ∑ x_1 : Fin n, ∑ i_1, 2 * (Real.sqrt (m : ℝ) * c) := by
              refine Finset.sum_le_sum ?_
              intro x_1 _
              refine Finset.sum_le_sum ?_
              intro i_1 _
              have hdiff :
                  |chainApprox c_pos h fh (↑x_1 + 1) (S i_1) -
                    chainApprox c_pos h fh (↑x_1) (S i_1)| ≤
                    2 * (Real.sqrt (m : ℝ) * c) :=
                chainApprox_increment_bound c_pos hmpos cs (↑x_1) h i_1 fh
              nlinarith
        _ = (n : ℝ) * m * (2 * (Real.sqrt (m : ℝ) * c)) := by
              simp [Finset.sum_const, Finset.card_univ, mul_assoc, mul_left_comm, mul_comm]

  -- Split the target into the main term and the increment term.
/-- For [a function class evaluated on a finite sample](hyp:Z,m,ι,F,S), [a positive radius
and evidence of its positivity](hyp:c,c_pos), [a uniform empirical-radius bound](hyp:cs), [total
boundedness of the empirical class](hyp:h), and [a terminal chaining level](hyp:n), [the
empirical Rademacher complexity is bounded by the sum of the terminal approximation term and
all successive chaining increments](goal). -/
lemma split_main_and_increment_terms {c_pos : 0 < c}
    (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) :
  empiricalRademacherComplexity_without_abs m F S ≤
    ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) * ((F fh (S i)) - chainApprox c_pos h fh n (S i)))) +
    ∑ j : Fin n, ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) *
      (chainApprox c_pos h fh (j + 1) (S i) - chainApprox c_pos h fh j (S i)))) := by
  by_cases m_pos : m = 0
  · simp [m_pos]
    subst m_pos
    dsimp [empiricalRademacherComplexity_without_abs]
    simp
  · calc
    _ = signs_card_inv m * ((m : ℝ)⁻¹ * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i)))) := by
      dsimp [empiricalRademacherComplexity_without_abs, signs_card_inv]
      apply congrArg
      rw [Finset.mul_sum]
      apply congrArg
      ext σ
      let H : ι → ℝ := fun i => ∑ k : Fin m, (σ k : ℝ) * F i (S k)
      change ⨆ i, (↑m)⁻¹ * H i = (↑m)⁻¹ * ⨆ i, H i
      refine Eq.symm (Real.mul_iSup_of_nonneg (by simp) H)
    _ = (m : ℝ)⁻¹ * (signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i)))) := by
      ring
    _ = (m : ℝ)⁻¹ * (signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * (((F fh) (S i) - chainApprox c_pos h fh n (S i)) +
        (∑ j : Fin n,
          (chainApprox c_pos h fh ((j : ℕ) + 1) (S i) -
            chainApprox c_pos h fh ((j : ℕ)) (S i)))))) := by
      repeat apply congrArg
      ext σ
      repeat apply congrArg
      ext fh
      apply congrArg
      ext i
      apply congrArg
      symm
      have h := congrArg (fun (h : Z → ℝ) => h (S i)) (chain_decomposition c_pos h fh n)
      simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply] at h
      symm
      exact h
    _ ≤ (m : ℝ)⁻¹ * ((signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i) - chainApprox c_pos h fh n (S i)))) +
      signs_card_inv m * ∑ j : Fin n, (∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) *
        (chainApprox c_pos h fh (j + 1) (S i) -
          chainApprox c_pos h fh j (S i))))) := by
      rw [<- left_distrib]
      rw [Finset.sum_comm]
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left
        · have w :
              (∑ σ : Signs m, ⨆ fh, ∑ i,
                  (σ i : ℝ) * (F fh (S i) - chainApprox c_pos h fh n (S i))) +
                ∑ y : Signs m, ∑ x : Fin n, ⨆ fh, ∑ i,
                  (y i : ℝ) *
                    (chainApprox c_pos h fh (↑x + 1) (S i) -
                      chainApprox c_pos h fh (↑x) (S i))
              = ∑ σ : Signs m,
                  ((⨆ fh, ∑ i,
                      (σ i : ℝ) *
                        (F fh (S i) - chainApprox c_pos h fh n (S i))) +
                    (∑ x : Fin n, ⨆ fh, ∑ i,
                      (σ i : ℝ) *
                        (chainApprox c_pos h fh (↑x + 1) (S i) -
                          chainApprox c_pos h fh (↑x) (S i)))) := by
            let chainApprox_increment_bound (σ : Signs m) :=
              ⨆ fh, ∑ i, (σ i : ℝ) *
                (F fh (S i) - chainApprox c_pos h fh n (S i))
            let chainApprox_pointwise_bound (y : Signs m) :=
              ∑ x : Fin n, ⨆ fh, ∑ i, (y i : ℝ) *
                (chainApprox c_pos h fh (↑x + 1) (S i) -
                  chainApprox c_pos h fh (↑x) (S i))
            have w' :
                ∑ σ : Signs m, chainApprox_increment_bound σ +
                  ∑ y : Signs m, chainApprox_pointwise_bound y =
                    ∑ σ : Signs m,
                      (chainApprox_increment_bound σ + chainApprox_pointwise_bound σ) :=
              Eq.symm Finset.sum_add_distrib
            dsimp [chainApprox_increment_bound, chainApprox_pointwise_bound] at w'
            exact w'
          rw [w]
          apply Finset.sum_le_sum
          intro i hi
          have q :
              ⨆ fh, ∑ i_1, (i i_1 : ℝ) *
                (F fh (S i_1) - chainApprox c_pos h fh n (S i_1) +
                  ∑ j : Fin n,
                    (chainApprox c_pos h fh ((j : ℕ) + 1) (S i_1) -
                      chainApprox c_pos h fh ((j : ℕ)) (S i_1))) ≤
            (⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1))) +
              ⨆ fh, ∑ x : Fin n, ∑ i_1, (i i_1 : ℝ) *
                (chainApprox c_pos h fh (↑x + 1) (S i_1) -
                  chainApprox c_pos h fh (↑x) (S i_1)) := by
            apply ciSup_le
            intro x
            -- split the inner sum into a constant part and the telescoping part
            have hx_split :
                (∑ i_1, (i i_1 : ℝ) * (F x (S i_1) - chainApprox c_pos h x n (S i_1) +
                  ∑ j : Fin n,
                    (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) -
                      chainApprox c_pos h x ((j : ℕ)) (S i_1))))
                = (∑ i_1, (i i_1 : ℝ) * (F x (S i_1) - chainApprox c_pos h x n (S i_1))) +
                  (∑ i_1, (i i_1 : ℝ) *
                    (∑ j : Fin n,
                      (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) -
                        chainApprox c_pos h x ((j : ℕ)) (S i_1)))) := by
              -- distribute the product over the inner addition and split the outer sum
              simp [mul_add, Finset.sum_add_distrib]
            -- bound each part by the respective suprema
            have hx1 : (∑ i_1, (i i_1 : ℝ) * (F x (S i_1) - chainApprox c_pos h x n (S i_1))) ≤
                ⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1)) := by
                  apply le_ciSup_of_le
                  · exact splitBound.bddAbove_main_term cs h n m_pos i
                  · exact Preorder.le_refl
                      (∑ i_1, ↑↑(i i_1) *
                        (F x (S i_1) - chainApprox c_pos h x n (S i_1)))
            calc
              (∑ i_1, (i i_1 : ℝ) *
                (F x (S i_1) - chainApprox c_pos h x n (S i_1) +
                  ∑ j : Fin n,
                    (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) -
                      chainApprox c_pos h x ((j : ℕ)) (S i_1))))
                  = _ := hx_split
              _ ≤ (⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1))) +
                  (∑ i_1, (i i_1 : ℝ) *
                    (∑ j : Fin n,
                      (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) -
                        chainApprox c_pos h x ((j : ℕ)) (S i_1)))) := by
                nlinarith
              _ ≤ (⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1))) +
                  (⨆ fh, ∑ x : Fin n, ∑ i_1, (i i_1 : ℝ) *
                    (chainApprox c_pos h fh (↑x + 1) (S i_1) -
                      chainApprox c_pos h fh (↑x) (S i_1))) := by
                -- rewrite the second sum as a double sum and take fh = x in the supremum
                have hx2_swap :
                    (∑ i_1, (i i_1 : ℝ) *
                      (∑ j : Fin n,
                        (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) -
                          chainApprox c_pos h x ((j : ℕ)) (S i_1))))
                    = ∑ j : Fin n, ∑ i_1, (i i_1 : ℝ) *
                        (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) -
                          chainApprox c_pos h x ((j : ℕ)) (S i_1)) := by
                  -- expand the outer product into an inner sum and then swap the summations
                  have h_expand :
                      (∑ i_1, (i i_1 : ℝ) *
                        (∑ j : Fin n,
                          (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) -
                            chainApprox c_pos h x ((j : ℕ)) (S i_1))))
                      = ∑ i_1, ∑ j : Fin n, (i i_1 : ℝ) *
                          (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) -
                            chainApprox c_pos h x ((j : ℕ)) (S i_1)) := by
                    apply Finset.sum_congr rfl
                    intro i1 hi1
                    -- move the scalar inside the inner sum
                    rw [Finset.mul_sum]
                  rw [h_expand]
                  rw [Finset.sum_comm]
                have hx2 :
                    (∑ j : Fin n, ∑ i_1, (i i_1 : ℝ) *
                      (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) -
                        chainApprox c_pos h x ((j : ℕ)) (S i_1))) ≤
                    ⨆ fh, ∑ x_1 : Fin n, ∑ i_1, (i i_1 : ℝ) *
                      (chainApprox c_pos h fh (↑x_1 + 1) (S i_1) -
                        chainApprox c_pos h fh (↑x_1) (S i_1)) := by
                  apply le_ciSup_of_le
                  · exact splitBound.bddAbove_increment_term cs h n m_pos i
                  · apply Preorder.le_refl
                -- combine both bounds
                rw [hx2_swap]
                apply add_le_add_right
                exact hx2
          apply le_trans q
          rw [add_le_add_iff_left]
          apply ciSup_le
          intro x'
          apply Finset.sum_le_sum
          intro i_1 hi_1
          apply le_ciSup_of_le
          · rw [bddAbove_def]
            use m * (2 * (√↑m * c))
            simp
            intro a
            calc
            _ ≤ ∑ i_2,
                |(i i_2 : ℝ) *
                  (chainApprox c_pos h a (↑i_1 + 1) (S i_2) -
                    chainApprox c_pos h a (↑i_1) (S i_2))| :=
              Finset.sum_le_sum (fun i_2 hi_2 ↦
                le_abs_self ((i i_2 : ℝ) *
                  (chainApprox c_pos h a (↑i_1 + 1) (S i_2) -
                    chainApprox c_pos h a (↑i_1) (S i_2))))
            _ ≤ ∑ i_2 : Fin m, 2 * (√↑m * c) := by
              apply Finset.sum_le_sum
              intro i_2 hi_2
              rw [abs_mul]
              simp
              apply chainApprox_increment_bound
              · apply Nat.pos_of_ne_zero m_pos
              · exact cs
            _ = _ := by simp
          · change
              ∑ i_1_1, (i i_1_1 : ℝ) *
                (chainApprox c_pos h x' (↑i_1 + 1) (S i_1_1) -
                  chainApprox c_pos h x' (↑i_1) (S i_1_1)) ≤
              ∑ i_2, (i i_2 : ℝ) *
                (chainApprox c_pos h x' (↑i_1 + 1) (S i_2) -
                  chainApprox c_pos h x' (↑i_1) (S i_2))
            simp
        · dsimp [signs_card_inv]
          simp
      · simp
    _ = (m : ℝ)⁻¹ * ((signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i) - chainApprox c_pos h fh n (S i)))) +
      ∑ j : Fin n, ( signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) *
        (chainApprox c_pos h fh (j + 1) (S i) -
          chainApprox c_pos h fh j (S i))))) := by
      simp
      left
      simp [Finset.mul_sum]
    _ = ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i) - chainApprox c_pos h fh n (S i)))) +
      (m : ℝ)⁻¹ * ∑ j : Fin n, ( signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) *
        (chainApprox c_pos h fh (j + 1) (S i) -
          chainApprox c_pos h fh j (S i)))) := by
      rw [mul_add]
      rw [mul_assoc]
    _ = _ := by
      simp only [add_right_inj]
      simp [Finset.mul_sum, mul_assoc]



end Empirical
end Causalean.Stat.Concentration
