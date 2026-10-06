module

public import Causalean.Mathlib.Probability.Kernel.FiniteSequence.Basic

/-!
# Construction of finite sequential laws

This module recursively constructs laws of dependent finite output histories from kernels that
may depend on the current input and all preceding private outputs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Mathlib.Probability.Kernel.FiniteSequence

variable {n : ℕ} {X : Type*} {Z : Fin n → Type*}
  [MeasurableSpace X] [∀ i, MeasurableSpace (Z i)]

/-- Given [an input space](hyp:X) and [an output family](hyp:Z), [a sequential kernel family](goal)
is [given by one kernel at each stage from the current input and preceding private history to the
current output](step:1). -/
abbrev KernelFamily (X : Type*) [MeasurableSpace X] (Z : Fin n → Type*)
    [∀ i, MeasurableSpace (Z i)] :=
  (i : Fin n) → Kernel (X × History Z i.val (Nat.le_of_lt i.isLt)) (Z i)

/-- Given [a successor bound](hyp:hk), [appending a next output to a preceding dependent
history is measurable](goal). -/
theorem measurable_snoc {k : ℕ} (hk : k + 1 ≤ n) :
    Measurable (fun p : History Z k (Nat.le_of_succ_le hk) × Z (nextIndex hk) =>
      snoc hk p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have h : nextIndex hk = Fin.castLE hk (Fin.last k) := rfl
    have hm := (measurable_eq_mp Z h).comp
      (measurable_snd : Measurable (fun p : History Z k (Nat.le_of_succ_le hk) ×
        Z (nextIndex hk) => p.2))
    convert hm using 1
    funext p
    simp [snoc, Fin.snoc]
    rfl
  · have h : Fin.castLE (Nat.le_of_succ_le hk) i =
        Fin.castLE hk i.castSucc := rfl
    have hm := (measurable_eq_mp Z h).comp
      ((measurable_pi_apply i).comp
        (measurable_fst : Measurable (fun p : History Z k (Nat.le_of_succ_le hk) ×
          Z (nextIndex hk) => p.1)))
    convert hm using 1
    funext p
    simp [snoc, Fin.snoc]
    rfl

/-- Given [a successor bound](hyp:hk), [splitting a nonempty dependent history into its
preceding history and final output is measurable](goal). -/
theorem measurable_init_last {k : ℕ} (hk : k + 1 ≤ n) :
    Measurable (fun u : History Z (k + 1) hk => (init hk u, last hk u)) := by
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply i.castSucc
  · exact measurable_pi_apply (Fin.last k)

/-- Given [a sequential kernel family](hyp:Q), [a fixed input vector](hyp:x), [a prefix
length](hyp:k), and [evidence that the prefix lies within the horizon](hyp:hk), [the law of the
first outputs](goal) is [given by iterated composition from the unique empty history](step:1). -/
noncomputable def prefixLaw (Q : KernelFamily X Z) (x : Fin n → X) (k : ℕ)
    (hk : k ≤ n) : Measure (History Z k hk) :=
  Nat.rec (motive := fun j => (hj : j ≤ n) → Measure (History Z j hj))
    (fun _ => Measure.dirac (fun j : Fin 0 => j.elim0))
    (fun j prev hj =>
      let hprev : j ≤ n := Nat.le_of_succ_le hj
      let idx : Fin n := nextIndex hj
      let K : Kernel (History Z j hprev) (Z idx) :=
        (Q idx).comap (fun u => (x idx, u)) (by fun_prop)
      (prev hprev ⊗ₘ K).map (fun p => snoc hj p.1 p.2))
    k hk

/-- Given [a sequential kernel family](hyp:Q), [the condition that every stage kernel is
Markov](hyp:hQ), [a fixed input vector](hyp:x), [a prefix length](hyp:k), and [evidence that the
prefix lies within the horizon](hyp:hk), [the prefix law has total mass one](goal). -/
theorem isProbabilityMeasure_prefixLaw (Q : KernelFamily X Z)
    (hQ : ∀ i, IsMarkovKernel (Q i)) (x : Fin n → X) (k : ℕ) (hk : k ≤ n) :
    IsProbabilityMeasure (prefixLaw Q x k hk) := by
  induction k with
  | zero =>
      change IsProbabilityMeasure (Measure.dirac (fun j : Fin 0 => j.elim0))
      exact ⟨by simp⟩
  | succ j ih =>
      let hprev : j ≤ n := Nat.le_of_succ_le hk
      let idx : Fin n := nextIndex hk
      let K : Kernel (History Z j hprev) (Z idx) :=
        (Q idx).comap (fun u => (x idx, u)) (by fun_prop)
      haveI : IsProbabilityMeasure (prefixLaw Q x j hprev) := ih hprev
      haveI : IsMarkovKernel (Q idx) := hQ idx
      haveI : IsMarkovKernel K := Kernel.IsMarkovKernel.comap _ (by fun_prop)
      haveI : IsProbabilityMeasure (prefixLaw Q x j hprev ⊗ₘ K) :=
        ⟨by simp⟩
      change IsProbabilityMeasure
        ((prefixLaw Q x j hprev ⊗ₘ K).map (fun p => snoc hk p.1 p.2))
      exact Measure.isProbabilityMeasure_map (measurable_snoc hk).aemeasurable

end Causalean.Mathlib.Probability.Kernel.FiniteSequence
