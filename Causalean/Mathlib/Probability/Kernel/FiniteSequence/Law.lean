module

public import Causalean.Mathlib.Probability.Kernel.FiniteSequence.Construction
public import Causalean.Mathlib.Probability.Kernel.FiniteSequence.Restriction

/-!
# Prefix and next-step identities for finite sequential laws

This module identifies every finite prefix marginal and every prefix-plus-next-output law of the
recursively constructed transcript measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Mathlib.Probability.Kernel.FiniteSequence

variable {n : ℕ} {X : Type*} {Z : Fin n → Type*}
  [MeasurableSpace X] [∀ i, MeasurableSpace (Z i)]

/-- Given [a sequential kernel family](hyp:Q), [a fixed input vector](hyp:x), [a prefix
length](hyp:k), and [a successor bound](hyp:hk), [the next prefix law is the composition-product
of the preceding prefix and current kernel, pushed forward by appending](goal). -/
theorem prefixLaw_succ (Q : KernelFamily X Z) (x : Fin n → X) (k : ℕ)
    (hk : k + 1 ≤ n) :
    prefixLaw Q x (k + 1) hk =
      ((prefixLaw Q x k (Nat.le_of_succ_le hk)) ⊗ₘ
        (Q (nextIndex hk)).comap
          (fun u => (x (nextIndex hk), u)) (by fun_prop)).map
        (fun p => snoc hk p.1 p.2) := by
  rfl

/-- Given [a sequential kernel family](hyp:Q), [a fixed input vector](hyp:x), [a prefix
length](hyp:k), and [a successor bound](hyp:hk), [splitting the next prefix into its preceding
history and final output yields the composition-product law](goal). -/
theorem prefixLaw_succ_map_init_last (Q : KernelFamily X Z) (x : Fin n → X)
    (k : ℕ) (hk : k + 1 ≤ n) :
    (prefixLaw Q x (k + 1) hk).map (fun u => (init hk u, last hk u)) =
      (prefixLaw Q x k (Nat.le_of_succ_le hk)) ⊗ₘ
        (Q (nextIndex hk)).comap (fun u => (x (nextIndex hk), u)) (by fun_prop) := by
  rw [prefixLaw_succ, Measure.map_map (measurable_init_last hk) (measurable_snoc hk)]
  have h : (fun u : History Z (k + 1) hk => (init hk u, last hk u)) ∘
      (fun p : History Z k (Nat.le_of_succ_le hk) × Z (nextIndex hk) =>
        snoc hk p.1 p.2) = id := by
    funext p
    cases p with
    | mk a b =>
      change (init hk (snoc hk a b), last hk (snoc hk a b)) = (a, b)
      apply Prod.ext
      · funext i
        exact congrFun (Fin.init_snoc (α := fun j : Fin (k + 1) => Z (Fin.castLE hk j))
          (p := a) (x := b)) i
      · exact Fin.snoc_last (α := fun j : Fin (k + 1) => Z (Fin.castLE hk j))
          (p := a) (x := b)
  rw [h, Measure.map_id]

/-- Given [a sequential kernel family](hyp:Q), [the condition that every stage kernel is
Markov](hyp:hQ), [a fixed input vector](hyp:x), [a prefix length](hyp:k), and [a successor
bound](hyp:hk), [forgetting the final output recovers the preceding prefix law](goal). -/
theorem prefixLaw_succ_map_init (Q : KernelFamily X Z)
    (hQ : ∀ i, IsMarkovKernel (Q i)) (x : Fin n → X)
    (k : ℕ) (hk : k + 1 ≤ n) :
    (prefixLaw Q x (k + 1) hk).map (init hk) =
      prefixLaw Q x k (Nat.le_of_succ_le hk) := by
  let μ := prefixLaw Q x k (Nat.le_of_succ_le hk)
  let K := (Q (nextIndex hk)).comap
    (fun u => (x (nextIndex hk), u)) (by fun_prop)
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_prefixLaw Q hQ x k _
  haveI : IsMarkovKernel (Q (nextIndex hk)) := hQ _
  haveI : IsMarkovKernel K := Kernel.IsMarkovKernel.comap _ (by fun_prop)
  have h := congrArg (fun ν : Measure (History Z k (Nat.le_of_succ_le hk) ×
      Z (nextIndex hk)) => ν.map Prod.fst)
    (prefixLaw_succ_map_init_last Q x k hk)
  rw [Measure.map_map measurable_fst (measurable_init_last hk)] at h
  have hfst : (μ ⊗ₘ K).fst = μ := by
    exact @Measure.fst_compProd _ _ _ _ μ (inferInstance) K (‹IsMarkovKernel K›)
  simpa only [Function.comp_def, μ, K, Measure.fst, Prod.fst] using h.trans hfst

/-- Given [a sequential kernel family](hyp:Q) and [a fixed input vector](hyp:x), [the complete
dependent transcript law](goal) is [given by the final prefix law](step:1). -/
noncomputable abbrev transcriptLaw (Q : KernelFamily X Z) (x : Fin n → X) :
    Measure (Transcript Z) := prefixLaw Q x n le_rfl

/-- Given [a sequential kernel family](hyp:Q), [the condition that every stage kernel is
Markov](hyp:hQ), [a fixed input vector](hyp:x), [a target prefix bound](hyp:hk), [a source prefix
bound](hyp:hl), and [an ordering of their lengths](hyp:hkl), [restricting the longer prefix law
recovers the shorter prefix law](goal). -/
theorem prefixLaw_map_restrictHistory (Q : KernelFamily X Z)
    (hQ : ∀ i, IsMarkovKernel (Q i)) (x : Fin n → X)
    {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n) (hkl : k ≤ l) :
    (prefixLaw Q x l hl).map (restrictHistory hk hl hkl) = prefixLaw Q x k hk := by
  induction l generalizing k with
  | zero =>
    have h : k = 0 := Nat.eq_zero_of_le_zero hkl
    subst k
    have hp : hk = hl := Subsingleton.elim _ _
    subst hk
    have hfun : restrictHistory (Z := Z) hl hl hkl =
        (id : History Z 0 hl → History Z 0 hl) := by
      funext u
      exact restrictHistory_self hl u
    rw [hfun, Measure.map_id]
  | succ l ih =>
    rcases Nat.eq_or_lt_of_le hkl with heq | hlt
    · subst k
      have hp : hk = hl := Subsingleton.elim _ _
      subst hk
      have hfun : restrictHistory (Z := Z) hl hl hkl =
          (id : History Z (l + 1) hl → History Z (l + 1) hl) := by
        funext u
        exact restrictHistory_self hl u
      rw [hfun, Measure.map_id]
    · have hkl' : k ≤ l := Nat.lt_succ_iff.mp hlt
      have hs : l + 1 ≤ n := hl
      have hinit := prefixLaw_succ_map_init Q hQ x l hs
      have hcomp : (restrictHistory (Z := Z) hk hl hkl) =
          (restrictHistory (Z := Z) hk (Nat.le_of_succ_le hs) hkl') ∘ init hs := by
        funext u
        exact restrictHistory_succ hk hs hkl' u
      rw [hcomp]
      have hmeas : Measurable (init hs : History Z (l + 1) hs →
          History Z l (Nat.le_of_succ_le hs)) := by
        apply measurable_pi_iff.mpr
        intro i
        exact measurable_pi_apply i.castSucc
      rw [← Measure.map_map (measurable_restrictHistory hk (Nat.le_of_succ_le hs) hkl')
        hmeas]
      rw [hinit]
      exact ih hk (Nat.le_of_succ_le hs) hkl'

/-- Given [a sequential kernel family](hyp:Q), [the condition that every stage kernel is
Markov](hyp:hQ), [a fixed input vector](hyp:x), [a prefix length](hyp:k), and [evidence that the
prefix lies within the horizon](hyp:hk), [the complete transcript law has the recursively
constructed prefix law as its prefix marginal](goal). -/
theorem transcriptLaw_map_prefix (Q : KernelFamily X Z)
    (hQ : ∀ i, IsMarkovKernel (Q i)) (x : Fin n → X)
    (k : ℕ) (hk : k ≤ n) :
    (transcriptLaw Q x).map (take hk) = prefixLaw Q x k hk := by
  have htake : (take hk : Transcript Z → History Z k hk) =
      restrictHistory hk le_rfl hk := by
    funext u
    exact (restrictHistory_transcript hk u).symm
  rw [htake]
  exact prefixLaw_map_restrictHistory Q hQ x hk le_rfl hk

/-- Given [a sequential kernel family](hyp:Q), [the condition that every stage kernel is
Markov](hyp:hQ), [a fixed input vector](hyp:x), [a prefix length](hyp:k), and [a successor
bound](hyp:hk), [under the complete transcript law, the joint law of the prefix of that length
and the next output is the composition-product of the prefix law with the next-stage kernel
evaluated at the next input coordinate](goal). -/
theorem transcriptLaw_map_take_next (Q : KernelFamily X Z)
    (hQ : ∀ i, IsMarkovKernel (Q i)) (x : Fin n → X)
    (k : ℕ) (hk : k + 1 ≤ n) :
    (transcriptLaw Q x).map
        (fun t => (take (Nat.le_of_succ_le hk) t, t (nextIndex hk))) =
      (prefixLaw Q x k (Nat.le_of_succ_le hk)) ⊗ₘ
        (Q (nextIndex hk)).comap (fun u => (x (nextIndex hk), u)) (by fun_prop) := by
  have hmeas : Measurable (take hk : Transcript Z → History Z (k + 1) hk) := by
    have hfun : (take hk : Transcript Z → History Z (k + 1) hk) =
        restrictHistory hk le_rfl hk := by
      funext u
      exact (restrictHistory_transcript hk u).symm
    rw [hfun]
    exact measurable_restrictHistory hk le_rfl hk
  have hfun : (fun t : Transcript Z =>
      (take (Nat.le_of_succ_le hk) t, t (nextIndex hk))) =
      (fun u : History Z (k + 1) hk => (init hk u, last hk u)) ∘ take hk := by
    funext t
    apply Prod.ext
    · funext i
      rfl
    · rfl
  rw [hfun, ← Measure.map_map (measurable_init_last hk) hmeas,
    transcriptLaw_map_prefix Q hQ x (k + 1) hk,
    prefixLaw_succ_map_init_last Q x k hk]

/-- Given [a sequential kernel family](hyp:Q), [the condition that every stage kernel is
Markov](hyp:hQ), and [a fixed input vector](hyp:x), [the complete transcript law has total mass
one](goal). -/
theorem isProbabilityMeasure_transcriptLaw (Q : KernelFamily X Z)
    (hQ : ∀ i, IsMarkovKernel (Q i)) (x : Fin n → X) :
    IsProbabilityMeasure (transcriptLaw Q x) := by
  exact isProbabilityMeasure_prefixLaw Q hQ x n le_rfl

end Causalean.Mathlib.Probability.Kernel.FiniteSequence
