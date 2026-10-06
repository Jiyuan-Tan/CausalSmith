module

public import Causalean.Mathlib.Probability.Kernel.FiniteSequence.Law

/-!
# Exact cylinder probabilities for finite sequential kernels

This module evaluates atoms of dependent finite transcript laws as products of their stagewise
conditional singleton probabilities.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Mathlib.Probability.Kernel.FiniteSequence

variable {n : ℕ} {X : Type*} {Z : Fin n → Type*}
  [MeasurableSpace X] [∀ i, MeasurableSpace (Z i)]
  [∀ i, MeasurableSingletonClass (Z i)]

/-- Given [a sequential kernel family](hyp:Q), [the condition that every stage kernel is
Markov](hyp:hQ), [a fixed input vector](hyp:x), [a preceding-prefix length](hyp:k), [a successor
bound](hyp:hk), [a preceding history](hyp:u), and [a next output](hyp:z), [the atom of the
extended history is the preceding atom mass times the conditional next-output mass](goal). -/
theorem prefixLaw_succ_singleton (Q : KernelFamily X Z)
    (hQ : ∀ i, IsMarkovKernel (Q i)) (x : Fin n → X)
    (k : ℕ) (hk : k + 1 ≤ n)
    (u : History Z k (Nat.le_of_succ_le hk)) (z : Z (nextIndex hk)) :
    prefixLaw Q x (k + 1) hk {snoc hk u z} =
      prefixLaw Q x k (Nat.le_of_succ_le hk) {u} *
        (Q (nextIndex hk)) (x (nextIndex hk), u) {z} := by
  let μ := prefixLaw Q x k (Nat.le_of_succ_le hk)
  let K := (Q (nextIndex hk)).comap
    (fun v => (x (nextIndex hk), v)) (by fun_prop)
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_prefixLaw Q hQ x k _
  haveI : IsMarkovKernel (Q (nextIndex hk)) := hQ _
  haveI : IsMarkovKernel K := Kernel.IsMarkovKernel.comap _ (by fun_prop)
  have hms (v : History Z (k + 1) hk) : MeasurableSet ({v} : Set (History Z (k + 1) hk)) := by
    change MeasurableSet ({v} : Set ((i : Fin (k + 1)) → Z (Fin.castLE hk i)))
    have h := MeasurableSet.univ_pi (fun i => measurableSet_singleton (v i))
    exact (Set.univ_pi_singleton v) ▸ h
  have hmu (v : History Z k (Nat.le_of_succ_le hk)) :
      MeasurableSet ({v} : Set (History Z k (Nat.le_of_succ_le hk))) := by
    change MeasurableSet ({v} : Set ((i : Fin k) → Z (Fin.castLE (Nat.le_of_succ_le hk) i)))
    have h := MeasurableSet.univ_pi (fun i => measurableSet_singleton (v i))
    exact (Set.univ_pi_singleton v) ▸ h
  letI : MeasurableSingletonClass (History Z k (Nat.le_of_succ_le hk)) := ⟨hmu⟩
  have hs : (fun p : History Z k (Nat.le_of_succ_le hk) × Z (nextIndex hk) =>
      snoc hk p.1 p.2) ⁻¹' {snoc hk u z} = {u} ×ˢ {z} := by
    ext p
    change (snoc hk p.1 p.2 = snoc hk u z) ↔ (p.1 = u ∧ p.2 = z)
    exact Fin.snoc_inj
  rw [prefixLaw_succ, Measure.map_apply (measurable_snoc hk) (hms _), hs]
  rw [Measure.compProd_apply_prod (hmu u) (measurableSet_singleton z)]
  rw [lintegral_singleton]
  simp only [Kernel.comap_apply]
  exact mul_comm _ _

/-- Given [a sequential kernel family](hyp:Q), [the condition that every stage kernel is
Markov](hyp:hQ), [a fixed input vector](hyp:x), and [a complete transcript](hyp:t), [the
transcript atom probability is the finite product of its stagewise conditional singleton
probabilities](goal). -/
theorem transcriptLaw_singleton (Q : KernelFamily X Z)
    (hQ : ∀ i, IsMarkovKernel (Q i)) (x : Fin n → X)
    (t : Transcript Z) :
    transcriptLaw Q x {t} =
      ∏ i : Fin n,
        (Q i) (x i, take (Nat.le_of_lt i.isLt) t) {t i} := by
  have h (k : ℕ) (hk : k ≤ n) :
      prefixLaw Q x k hk {take hk t} =
        ∏ i : Fin k,
          (Q (Fin.castLE hk i))
            (x (Fin.castLE hk i),
              take (Nat.le_of_lt (Fin.castLE hk i).isLt) t)
            {t (Fin.castLE hk i)} := by
    induction k with
    | zero =>
        have he : ({take hk t} : Set (History Z 0 hk)) = Set.univ := by
          ext v
          have hv : v = take hk t := by funext i; exact i.elim0
          simp [hv]
        change (Measure.dirac (fun j : Fin 0 => j.elim0))
          ({take hk t} : Set ((j : Fin 0) → Z (Fin.castLE hk j))) = _
        have hm := congrArg
          (fun s : Set (History Z 0 hk) =>
            (Measure.dirac (fun j : Fin 0 => j.elim0)) s) he
        change (Measure.dirac (fun j : Fin 0 => j.elim0))
          ({take hk t} : Set ((j : Fin 0) → Z (Fin.castLE hk j))) = 1
        haveI : IsProbabilityMeasure (prefixLaw Q x 0 hk) :=
          isProbabilityMeasure_prefixLaw Q hQ x 0 hk
        exact hm.trans (by change (prefixLaw Q x 0 hk) Set.univ = 1; exact measure_univ)
    | succ j ih =>
        let hj : j ≤ n := Nat.le_of_succ_le hk
        have ht : take hk t = snoc hk (take hj t) (t (nextIndex hk)) := by
          funext i
          refine Fin.lastCases ?_ (fun a => ?_) i
          · simp [take, snoc, nextIndex, Fin.snoc, Fin.castLE]
          · simp [take, snoc, nextIndex, Fin.snoc, Fin.castLE]
        rw [ht, prefixLaw_succ_singleton Q hQ x j hk]
        rw [ih hj, Fin.prod_univ_castSucc]
        rfl
  have ht : take le_rfl t = t := by funext i; rfl
  simpa only [transcriptLaw, ht, Fin.castLE_refl] using h n le_rfl

/-- Given [a zero-horizon output family](hyp:Z), [a sequential kernel family](hyp:Q), [the
condition that every stage kernel is Markov](hyp:hQ), [a zero-horizon input vector](hyp:x), and
[the sole empty transcript](hyp:t),
[that transcript has probability one](goal). -/
theorem transcriptLaw_zero (Z : Fin 0 → Type*) [∀ i, MeasurableSpace (Z i)]
    [∀ i, MeasurableSingletonClass (Z i)] (Q : KernelFamily X Z)
    (hQ : ∀ i, IsMarkovKernel (Q i)) (x : Fin 0 → X)
    (t : Transcript Z) : transcriptLaw Q x {t} = 1 := by
  simpa using transcriptLaw_singleton Q hQ x t

end Causalean.Mathlib.Probability.Kernel.FiniteSequence
