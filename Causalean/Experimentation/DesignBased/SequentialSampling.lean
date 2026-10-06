/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.FinitePopulationMoments
public import Causalean.Stat.CLT.FiniteDesignConditioning
public import Mathlib.GroupTheory.Perm.Fin

/-! # Sequential simple random sampling without replacement

This module represents sequential sampling without replacement by a uniformly random permutation.
It defines the prefix filtration, the next draw and its finite conditional moments, and the Doob
martingale-difference array of a centered simple-random-sample mean.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Experimentation.DesignBased

open FinitePopulationMoments
open Causalean.Stat
open Causalean.Stat.FiniteRaoBlackwell

/-- Given [a population size](hyp:N), the [ordered sampling space](goal) is the set of
permutations of the `N` population indices. -/
abbrev PermutationSampleSpace (N : ℕ) : Type := Equiv.Perm (Fin N)

/-- For [a population size](hyp:N), the [ordered sampling space carries the discrete
σ-algebra](goal). -/
instance (N : ℕ) : MeasurableSpace (PermutationSampleSpace N) := ⊤

/-- For [a population size](hyp:N), [singletons in the ordered sampling space are
measurable](goal) under its discrete σ-algebra. -/
instance (N : ℕ) : MeasurableSingletonClass (PermutationSampleSpace N) := ⟨fun _ => trivial⟩

/-- For [a population size](hyp:N), the [space of partially revealed permutation
prefixes carries the discrete σ-algebra](goal). -/
instance (N : ℕ) : MeasurableSpace (Fin N → Option (Fin N)) := ⊤

/-- For [a population size](hyp:N), [singletons of partially revealed permutation prefixes are
measurable](goal) under the discrete σ-algebra. -/
instance (N : ℕ) : MeasurableSingletonClass (Fin N → Option (Fin N)) := ⟨fun _ => trivial⟩

/-- Given [a population size](hyp:N), the [uniform permutation design](goal) gives every ordering
of the population the same probability. -/
noncomputable def uniformPermutationDesign (N : ℕ) : FiniteDesign (PermutationSampleSpace N) := by
  classical
  exact {
    p := fun _ => 1 / (Fintype.card (PermutationSampleSpace N) : ℝ)
    p_nonneg := fun _ => one_div_nonneg.mpr (Nat.cast_nonneg _)
    p_sum := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : Fintype.card (PermutationSampleSpace N) ≠ 0 := Fintype.card_ne_zero
      have hcardR : (Fintype.card (PermutationSampleSpace N) : ℝ) ≠ 0 := by
        exact_mod_cast hcard
      field_simp [hcardR] }

/-- Given [a prefix length](hyp:k) and [an ordering](hyp:π), the [revealed prefix](goal) records
the draw at positions below `k` and records no value at later positions. -/
def permutationPrefix {N : ℕ} (k : ℕ) (π : PermutationSampleSpace N) :
    Fin N → Option (Fin N) :=
  fun i => if i.val < k then some (π i) else none

/-- Given [a truncation length](hyp:k) and [a possibly revealed coordinate vector](hyp:x), the
[truncated prefix](goal) retains positions below `k` and hides all later positions. -/
def truncatePermutationPrefix {N : ℕ} (k : ℕ) (x : Fin N → Option (Fin N)) :
    Fin N → Option (Fin N) :=
  fun i => if i.val < k then x i else none

/-- For [a population size](hyp:N), the [successive-draw filtration](goal) is generated at time
`k` by the first `k` values of the random ordering. -/
noncomputable def permutationRevealFiltration (N : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (PermutationSampleSpace N)) where
  seq k := MeasurableSpace.comap (permutationPrefix k)
    inferInstance
  mono' := by
    intro k l hkl
    apply MeasurableSpace.comap_le_comap_of_eq_comp (truncatePermutationPrefix k)
      (measurable_of_finite _)
    funext π i
    change (if i.val < k then some (π i) else none) =
      if i.val < k then (if i.val < l then some (π i) else none) else none
    by_cases hik : i.val < k
    · have hil : i.val < l := lt_of_lt_of_le hik hkl
      simp [hik, hil]
    · simp [hik]
  le' := fun _ => le_top

/-- Given [a population outcome vector](hyp:y), [a draw position](hyp:k) that [is inside the
population](hyp:hk), and [an ordering](hyp:π), the [outcome of that draw](goal) is the outcome at
the index occupying position `k`. -/
def permutationDraw {N : ℕ} (y : Fin N → ℝ) (k : ℕ) (hk : k < N)
    (π : PermutationSampleSpace N) : ℝ := y (π ⟨k, hk⟩)

/-- Given [a finite population and an ordering](hyp:N,π), [a valid natural-number position](hyp:k,hk),
and [any position in the ordering](hyp:j), the [position-swapped ordering](goal) exchanges those two
draw positions. -/
def permutationSwapPosition {N : ℕ} (π : PermutationSampleSpace N)
    (k : ℕ) (hk : k < N) (j : Fin N) : PermutationSampleSpace N :=
  π * Equiv.swap ⟨k, hk⟩ j

/-- Given [an ordering](hyp:π), [a valid current position](hyp:k,hk), and [an unrevealed
position](hyp:j,hj), [swapping the current position with that position preserves the prefix
revealed before the current draw](goal). -/
theorem permutationPrefix_swapPosition {N : ℕ} (π : PermutationSampleSpace N)
    (k : ℕ) (hk : k < N) (j : Fin N) (hj : k ≤ j.val) :
    permutationPrefix k (permutationSwapPosition π k hk j) = permutationPrefix k π := by
  funext i
  by_cases hi : i.val < k
  · have hik : i ≠ ⟨k, hk⟩ := by
      intro h
      simp [h] at hi
    have hij : i ≠ j := by
      intro h
      subst j
      omega
    simp [permutationPrefix, permutationSwapPosition, hi, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hik hij]
  · simp [permutationPrefix, hi]

/-- Given [population outcomes](hyp:y), [a valid current position](hyp:k,hk), [an
ordering](hyp:π), and [another position](hyp:j), [the draw after swapping positions `k` and
`j` is the outcome originally occupying position `j`](goal). -/
theorem permutationDraw_swapPosition {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k < N) (π : PermutationSampleSpace N) (j : Fin N) :
    permutationDraw y k hk (permutationSwapPosition π k hk j) = y (π j) := by
  simp [permutationDraw, permutationSwapPosition, Equiv.Perm.mul_apply]

/-- Given [population outcomes](hyp:y), [a valid current position](hyp:k,hk), [an
ordering whose prefix fixes the conditioning fiber](hyp:π), and [an unrevealed
position](hyp:j,hj), [the fiber sum of the current draw equals the fiber sum of the outcome at
that unrevealed position](goal). -/
theorem sum_prefixFiber_permutationDraw_eq_position {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k < N) (π : PermutationSampleSpace N) (j : Fin N)
    (hj : k ≤ j.val) :
    (∑ σ : PermutationSampleSpace N,
        if permutationPrefix k σ = permutationPrefix k π
        then permutationDraw y k hk σ else 0) =
      ∑ σ : PermutationSampleSpace N,
        if permutationPrefix k σ = permutationPrefix k π then y (σ j) else 0 := by
  classical
  let e : Equiv.Perm (PermutationSampleSpace N) :=
    Equiv.mulRight (Equiv.swap ⟨k, hk⟩ j)
  let g : PermutationSampleSpace N → ℝ := fun σ =>
    if permutationPrefix k σ = permutationPrefix k π
    then permutationDraw y k hk σ else 0
  have hsum := Equiv.sum_comp e g
  have he : ∀ σ, e σ = permutationSwapPosition σ k hk j := fun _ => rfl
  simpa only [g, he, permutationPrefix_swapPosition _ k hk j hj,
    permutationDraw_swapPosition] using hsum.symm

/-- Given [a population outcome vector](hyp:y), [a revealed-prefix length](hyp:k), [its
feasibility](hyp:hk), and [an ordering](hyp:π), the [sum of outcomes in the revealed
positions](goal) adds the first `k` ordered outcomes. -/
noncomputable def permutationRevealedSum {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k ≤ N) (π : PermutationSampleSpace N) : ℝ :=
  ∑ i : Fin k, y (π (Fin.castLE hk i))

/-- Given [a population outcome vector](hyp:y), [a revealed-prefix length](hyp:k), [its
feasibility](hyp:hk), and [an ordering](hyp:π), the [sum of outcomes remaining after the
prefix](goal) is the population total minus the revealed sum. -/
noncomputable def permutationRemainingSum {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k ≤ N) (π : PermutationSampleSpace N) : ℝ :=
  (∑ i : Fin N, y (π i)) - permutationRevealedSum y k hk π

/-- Given [a feasible prefix length](hyp:k,hk) and [an offset among the remaining
positions](hyp:j), the [corresponding position in the original ordering](goal) has index `k+j`. -/
def permutationRemainingPosition {N : ℕ} (k : ℕ) (hk : k ≤ N)
    (j : Fin (N - k)) : Fin N :=
  ⟨k + j.val, by omega⟩

/-- For [population outcomes](hyp:y), [a feasible prefix length](hyp:k,hk), and [an
ordering](hyp:π), [the sum over the remaining positions equals the population total minus the
revealed-position sum](goal). -/
theorem sum_remainingPositions_eq_permutationRemainingSum {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k ≤ N) (π : PermutationSampleSpace N) :
    (∑ j : Fin (N - k), y (π (permutationRemainingPosition k hk j))) =
      permutationRemainingSum y k hk π := by
  let e : Fin k ⊕ Fin (N - k) ≃ Fin N :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hk))
  have hsplit := Equiv.sum_comp e (fun i : Fin N => y (π i))
  change _ = (∑ i : Fin N, y (π i)) - ∑ i : Fin k, y (π (Fin.castLE hk i))
  rw [← hsplit]
  rw [Fintype.sum_sum_type]
  have hleft : (∑ i : Fin k, y (π (e (Sum.inl i)))) =
      ∑ i : Fin k, y (π (Fin.castLE hk i)) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 2
  have hright : (∑ j : Fin (N - k), y (π (e (Sum.inr j)))) =
      ∑ j : Fin (N - k), y (π (permutationRemainingPosition k hk j)) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 2
  rw [hleft, hright]
  ring

/-- Given [population outcomes](hyp:y), [a feasible prefix length](hyp:k,hk), and [two
orderings with the same revealed prefix](hyp:σ,π,hprefix), [their remaining outcome sums
are equal](goal). -/
theorem permutationRemainingSum_eq_of_prefix_eq {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k ≤ N) (σ π : PermutationSampleSpace N)
    (hprefix : permutationPrefix k σ = permutationPrefix k π) :
    permutationRemainingSum y k hk σ = permutationRemainingSum y k hk π := by
  have hfullσ : (∑ i : Fin N, y (σ i)) = ∑ i : Fin N, y i := Equiv.sum_comp σ y
  have hfullπ : (∑ i : Fin N, y (π i)) = ∑ i : Fin N, y i := Equiv.sum_comp π y
  have hreveal : permutationRevealedSum y k hk σ = permutationRevealedSum y k hk π := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : (Fin.castLE hk i).val < k := i.isLt
    have hcoord := congrFun hprefix (Fin.castLE hk i)
    simp only [permutationPrefix, hi, if_true, Option.some.injEq] at hcoord
    rw [hcoord]
  simp only [permutationRemainingSum, hfullσ, hfullπ, hreveal]

/-- Given [population outcomes](hyp:y), [a valid current position](hyp:k,hk), and [an
ordering fixing the conditioning fiber](hyp:π), [the number of remaining positions times the
fiber sum of the next draw equals the fiber count times the fixed remaining outcome sum](goal). -/
theorem remainingCount_mul_sum_prefixFiber_permutationDraw {N : ℕ}
    (y : Fin N → ℝ) (k : ℕ) (hk : k < N) (π : PermutationSampleSpace N) :
    ((N - k : ℕ) : ℝ) *
        (∑ σ : PermutationSampleSpace N,
          if permutationPrefix k σ = permutationPrefix k π
          then permutationDraw y k hk σ else 0) =
      (∑ σ : PermutationSampleSpace N,
          if permutationPrefix k σ = permutationPrefix k π then (1 : ℝ) else 0) *
        permutationRemainingSum y k hk.le π := by
  classical
  let drawFiberSum : ℝ :=
    ∑ σ : PermutationSampleSpace N,
      if permutationPrefix k σ = permutationPrefix k π
      then permutationDraw y k hk σ else 0
  calc
    ((N - k : ℕ) : ℝ) * drawFiberSum =
        ∑ j : Fin (N - k), drawFiberSum := by simp
    _ = ∑ j : Fin (N - k), ∑ σ : PermutationSampleSpace N,
          if permutationPrefix k σ = permutationPrefix k π
          then y (σ (permutationRemainingPosition k hk.le j)) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_prefixFiber_permutationDraw_eq_position y k hk π
        (permutationRemainingPosition k hk.le j) (by
          simp [permutationRemainingPosition])
    _ = ∑ σ : PermutationSampleSpace N, ∑ j : Fin (N - k),
          if permutationPrefix k σ = permutationPrefix k π
          then y (σ (permutationRemainingPosition k hk.le j)) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ σ : PermutationSampleSpace N,
          if permutationPrefix k σ = permutationPrefix k π
          then permutationRemainingSum y k hk.le π else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hprefix : permutationPrefix k σ = permutationPrefix k π
      · simp only [hprefix, if_true]
        rw [sum_remainingPositions_eq_permutationRemainingSum]
        exact permutationRemainingSum_eq_of_prefix_eq y k hk.le σ π hprefix
      · simp [hprefix]
    _ = (∑ σ : PermutationSampleSpace N,
          if permutationPrefix k σ = permutationPrefix k π then (1 : ℝ) else 0) *
        permutationRemainingSum y k hk.le π := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hprefix : permutationPrefix k σ = permutationPrefix k π <;>
        simp [hprefix]

/-- For [a population outcome vector](hyp:y) and [a valid draw position](hyp:k,hk), [the draw is
measurable immediately after that position is revealed](goal). -/
@[fun_prop]
theorem permutationDraw_stronglyMeasurable {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k < N) :
    StronglyMeasurable[(permutationRevealFiltration N) (k + 1)]
      (permutationDraw y k hk) := by
  apply Measurable.stronglyMeasurable
  apply (measurable_of_finite y).comp
  have hcoord : Measurable[(permutationRevealFiltration N) (k + 1)]
      (fun π : PermutationSampleSpace N => π ⟨k, hk⟩) := by
    let read : (Fin N → Option (Fin N)) → Fin N :=
      fun x => (x ⟨k, hk⟩).getD ⟨k, hk⟩
    have hread : Measurable read := measurable_of_finite _
    have heq : (fun π : PermutationSampleSpace N => π ⟨k, hk⟩) =
        read ∘ permutationPrefix (k + 1) := by
      funext π
      simp [read, permutationPrefix]
    rw [heq]
    exact hread.comp (comap_measurable _)
  exact hcoord

/-- Given [a population outcome vector](hyp:y), [a valid draw position](hyp:k,hk), and [an
ordering](hyp:π), the [finite conditional mean of the next draw given the preceding prefix](goal)
is the uniform-design fiber average over orderings with the same first `k` draws. -/
noncomputable def permutationNextMean {N : ℕ} (y : Fin N → ℝ) (k : ℕ) (hk : k < N)
    (π : PermutationSampleSpace N) : ℝ :=
  finiteConditionalMean (uniformPermutationDesign N) (permutationPrefix k)
    (permutationDraw y k hk) (permutationPrefix k π)

/-- For [population outcomes](hyp:y) and [a valid next-draw position](hyp:k,hk), [the
prefix-conditional next-draw mean is measurable before that draw](goal). -/
@[fun_prop]
theorem permutationNextMean_stronglyMeasurable {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k < N) :
    StronglyMeasurable[(permutationRevealFiltration N) k]
      (permutationNextMean y k hk) := by
  apply Measurable.stronglyMeasurable
  exact (measurable_of_finite
    (finiteConditionalMean (uniformPermutationDesign N) (permutationPrefix k)
      (permutationDraw y k hk))).comp (comap_measurable _)

/-- Given [population outcomes](hyp:y), [a valid next-draw position](hyp:k,hk), and [an
ordering](hyp:π), [the conditional mean of the next draw is the arithmetic mean of the
outcomes remaining after the revealed prefix](goal). -/
theorem permutationNextMean_eq_remainingMean {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k < N) (π : PermutationSampleSpace N) :
    permutationNextMean y k hk π =
      permutationRemainingSum y k hk.le π / ((N - k : ℕ) : ℝ) := by
  classical
  let D := uniformPermutationDesign N
  let c : ℝ := 1 / (Fintype.card (PermutationSampleSpace N) : ℝ)
  let b := permutationPrefix k π
  have hcard : (Fintype.card (PermutationSampleSpace N) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (PermutationSampleSpace N) ≠ 0)
  have hc : c ≠ 0 := one_div_ne_zero hcard
  have hp : D.p π ≠ 0 := by
    change c ≠ 0
    exact hc
  have hmass : fiberMass D (permutationPrefix k) b ≠ 0 := by
    intro hzero
    exact hp (p_eq_zero_of_mem_fiberMass_eq_zero D (permutationPrefix k) b
      hzero π rfl)
  have hnum : fiberNumerator D (permutationPrefix k)
      (fun σ (_ : Unit) => permutationDraw y k hk σ) b () =
      c * (∑ σ : PermutationSampleSpace N,
        if permutationPrefix k σ = b then permutationDraw y k hk σ else 0) := by
    unfold fiberNumerator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hσ : permutationPrefix k σ = b <;>
      simp [D, c, uniformPermutationDesign, hσ]
  have hmass' : fiberMass D (permutationPrefix k) b =
      c * (∑ σ : PermutationSampleSpace N,
        if permutationPrefix k σ = b then (1 : ℝ) else 0) := by
    unfold fiberMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hσ : permutationPrefix k σ = b <;>
      simp [D, c, uniformPermutationDesign, hσ]
  have hcount : ((N - k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hk).ne'
  have hraw := remainingCount_mul_sum_prefixFiber_permutationDraw y k hk π
  have hweighted : ((N - k : ℕ) : ℝ) *
      fiberNumerator D (permutationPrefix k)
        (fun σ (_ : Unit) => permutationDraw y k hk σ) b () =
      fiberMass D (permutationPrefix k) b * permutationRemainingSum y k hk.le π := by
    rw [hnum, hmass']
    dsimp only [b]
    calc
      ((N - k : ℕ) : ℝ) * (c *
          ∑ σ : PermutationSampleSpace N,
            if permutationPrefix k σ = permutationPrefix k π
            then permutationDraw y k hk σ else 0) =
          c * (((N - k : ℕ) : ℝ) *
            ∑ σ : PermutationSampleSpace N,
              if permutationPrefix k σ = permutationPrefix k π
              then permutationDraw y k hk σ else 0) := by ring
      _ = c * ((∑ σ : PermutationSampleSpace N,
              if permutationPrefix k σ = permutationPrefix k π then (1 : ℝ) else 0) *
            permutationRemainingSum y k hk.le π) := by rw [hraw]
      _ = (c * ∑ σ : PermutationSampleSpace N,
              if permutationPrefix k σ = permutationPrefix k π then (1 : ℝ) else 0) *
            permutationRemainingSum y k hk.le π := by ring
  unfold permutationNextMean finiteConditionalMean conditionalMeanAlongMap
  simp only [D, b, hmass, if_false]
  apply (div_eq_div_iff hmass hcount).2
  calc
    fiberNumerator D (permutationPrefix k)
          (fun σ (_ : Unit) => permutationDraw y k hk σ) b () *
        ((N - k : ℕ) : ℝ) =
        ((N - k : ℕ) : ℝ) * fiberNumerator D (permutationPrefix k)
          (fun σ (_ : Unit) => permutationDraw y k hk σ) b () := mul_comm _ _
    _ = fiberMass D (permutationPrefix k) b *
        permutationRemainingSum y k hk.le π := hweighted
    _ = permutationRemainingSum y k hk.le π *
        fiberMass D (permutationPrefix k) b := mul_comm _ _

/-- For [a population outcome vector](hyp:y) and [a valid draw position](hyp:k,hk), [the explicit
prefix-fiber mean of the next draw equals its measure-theoretic conditional expectation](goal)
given the preceding draws. -/
theorem permutationNextMean_ae_eq_condExp {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k < N) :
    permutationNextMean y k hk =ᵐ[(uniformPermutationDesign N).toMeasure]
      ((uniformPermutationDesign N).toMeasure)[
        permutationDraw y k hk | (permutationRevealFiltration N) k] := by
  change (fun π => finiteConditionalMean (uniformPermutationDesign N) (permutationPrefix k)
      (permutationDraw y k hk) (permutationPrefix k π)) =ᵐ[(uniformPermutationDesign N).toMeasure]
    ((uniformPermutationDesign N).toMeasure)[permutationDraw y k hk |
      MeasurableSpace.comap (permutationPrefix k) inferInstance]
  exact finiteConditionalMean_comp_ae_eq_condExp (uniformPermutationDesign N)
    (permutationPrefix k) (permutationDraw y k hk)

/-- For [population outcomes](hyp:y) and [a valid next-draw position](hyp:k,hk), [the
next draw centered by its prefix-conditional mean has conditional expectation zero](goal). -/
theorem permutationCenteredDraw_condExp_zero {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k < N) :
    ((uniformPermutationDesign N).toMeasure)[
      fun π => permutationDraw y k hk π - permutationNextMean y k hk π |
        (permutationRevealFiltration N) k] =ᵐ[(uniformPermutationDesign N).toMeasure] 0 := by
  let μ := (uniformPermutationDesign N).toMeasure
  let m := (permutationRevealFiltration N) k
  have hsub := condExp_sub (Integrable.of_finite : Integrable (permutationDraw y k hk) μ)
    (Integrable.of_finite : Integrable (permutationNextMean y k hk) μ) m
  have hdraw := permutationNextMean_ae_eq_condExp y k hk
  have hmean : μ[permutationNextMean y k hk | m] = permutationNextMean y k hk :=
    condExp_of_stronglyMeasurable ((permutationRevealFiltration N).le k)
      (permutationNextMean_stronglyMeasurable y k hk) Integrable.of_finite
  change μ[permutationDraw y k hk - permutationNextMean y k hk | m] =ᵐ[μ] 0
  filter_upwards [hsub, hdraw] with π hsubπ hdrawπ
  change permutationNextMean y k hk π = μ[permutationDraw y k hk | m] π at hdrawπ
  rw [hsubπ]
  change μ[permutationDraw y k hk | m] π -
    μ[permutationNextMean y k hk | m] π = 0
  rw [hmean, ← hdrawπ]
  simp

/-- Given [a population outcome vector](hyp:y), [a valid draw position](hyp:k,hk), and [an
ordering](hyp:π), the [conditional centered second moment of the next draw](goal) is the
prefix-fiber average of its squared deviation from the conditional first moment. -/
noncomputable def permutationNextVariance {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k < N) (π : PermutationSampleSpace N) : ℝ :=
  finiteConditionalMean (uniformPermutationDesign N) (permutationPrefix k)
    (fun π' => (permutationDraw y k hk π' - permutationNextMean y k hk π') ^ 2)
    (permutationPrefix k π)

/-- Given [population outcomes](hyp:y), [a valid next-draw position](hyp:k,hk), and [an
ordering](hyp:π), [the conditional centered second moment of the next draw is the average
squared deviation of the remaining outcomes from their remaining mean](goal). -/
theorem permutationNextVariance_eq_remainingVariance {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k < N) (π : PermutationSampleSpace N) :
    permutationNextVariance y k hk π =
      (∑ j : Fin (N - k),
        (y (π (permutationRemainingPosition k hk.le j)) -
          permutationNextMean y k hk π) ^ 2) / ((N - k : ℕ) : ℝ) := by
  classical
  let m := permutationNextMean y k hk π
  let z : Fin N → ℝ := fun i => (y i - m) ^ 2
  have hfiber : finiteConditionalMean (uniformPermutationDesign N) (permutationPrefix k)
      (fun σ => (permutationDraw y k hk σ - permutationNextMean y k hk σ) ^ 2)
      (permutationPrefix k π) =
      finiteConditionalMean (uniformPermutationDesign N) (permutationPrefix k)
        (permutationDraw z k hk) (permutationPrefix k π) := by
    unfold finiteConditionalMean conditionalMeanAlongMap
    split_ifs with hmass
    · rfl
    · congr 1
      unfold fiberNumerator
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hprefix : permutationPrefix k σ = permutationPrefix k π
      · have hremain := permutationRemainingSum_eq_of_prefix_eq y k hk.le σ π hprefix
        have hmean : permutationNextMean y k hk σ = m := by
          dsimp only [m]
          rw [permutationNextMean_eq_remainingMean,
            permutationNextMean_eq_remainingMean, hremain]
        simp [hprefix, permutationDraw, z, hmean, m]
      · simp [hprefix]
  unfold permutationNextVariance
  rw [hfiber]
  change permutationNextMean z k hk π = _
  rw [permutationNextMean_eq_remainingMean,
    ← sum_remainingPositions_eq_permutationRemainingSum]

/-- For [population outcomes](hyp:y) and [a valid next-draw position](hyp:k,hk), [the
explicit remaining-population variance equals the conditional expectation of the squared
centered next draw](goal). -/
theorem permutationNextVariance_ae_eq_condExp {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k < N) :
    permutationNextVariance y k hk =ᵐ[(uniformPermutationDesign N).toMeasure]
      ((uniformPermutationDesign N).toMeasure)[
        (fun π => (permutationDraw y k hk π - permutationNextMean y k hk π) ^ 2) |
          (permutationRevealFiltration N) k] := by
  change (fun π => finiteConditionalMean (uniformPermutationDesign N) (permutationPrefix k)
      (fun σ => (permutationDraw y k hk σ - permutationNextMean y k hk σ) ^ 2)
      (permutationPrefix k π)) =ᵐ[(uniformPermutationDesign N).toMeasure]
    ((uniformPermutationDesign N).toMeasure)[
      (fun π => (permutationDraw y k hk π - permutationNextMean y k hk π) ^ 2) |
        MeasurableSpace.comap (permutationPrefix k) inferInstance]
  exact finiteConditionalMean_comp_ae_eq_condExp (uniformPermutationDesign N)
    (permutationPrefix k)
    (fun π => (permutationDraw y k hk π - permutationNextMean y k hk π) ^ 2)

/-- Given [a feasible sample size](hyp:K,hK), [population outcomes](hyp:y), and [an
ordering](hyp:π), the [mean of the first `K` draws](goal) is the ordered representation of the
simple-random-sample mean. -/
noncomputable def permutationSampleMean {N : ℕ} (K : ℕ) (hK : K ≤ N)
    (y : Fin N → ℝ) (π : PermutationSampleSpace N) : ℝ :=
  (∑ j : Fin K, y (π (Fin.castLE hK j))) / (K : ℝ)

/-- Given [sequences of population and sample sizes](hyp:N,K,hK) and [finite-population
outcomes](hyp:y), the [SRS Doob martingale-difference array](goal) reveals the permutation one draw
at a time and has the centered first-`K` sample mean as its terminal statistic. -/
noncomputable def srsPermutationDoobArray
    (N K : ℕ → ℕ) (hK : ∀ n, K n ≤ N n)
    (y : ∀ n, Fin (N n) → ℝ) :
    MartingaleDifferenceArray
      (fun n => PermutationSampleSpace (N n))
      (fun n => (uniformPermutationDesign (N n)).toMeasure) :=
  doobMartingaleDifferenceArray K (fun n => permutationRevealFiltration (N n))
    (fun n π => permutationSampleMean (K n) (hK n) (y n) π - popMean (y n))
    (fun n => (uniformPermutationDesign (N n)).memLp_toMeasure
      (fun π => permutationSampleMean (K n) (hK n) (y n) π - popMean (y n)) 2)

end Causalean.Experimentation.DesignBased
