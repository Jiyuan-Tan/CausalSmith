module
public import Causalean.Stat.EmpiricalProcess.Countable.ChainBasic
public import Causalean.Stat.EmpiricalProcess.Countable.FiniteSigns
public import Causalean.Stat.EmpiricalProcess.Countable.TraceOrdering

/-!
# Signed weighted nested chains

An arbitrary nested set family has only finitely many distinct traces on a
finite sample. A permutation places all those traces among prefixes. Signs
are invariant under that permutation, and restricting coefficients to a
containing union yields the squared-energy estimate with constant 256/27.
The indexing family may be infinite; no trace-complexity assumption is needed.
-/

public section

noncomputable section
open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- If [a family of sets](hyp:B) is [nested, any two members being
comparable by inclusion](hyp:hchain), and [every member lies in a
containing set U](hyp:U,hU), then for [any sample](hyp:x) and [real sample
weights](hyp:w), [the sign-average fourth power of the chain supremum is at
most 256/27 times the square of the chain energy in U](goal).

The bound is independent of the number of observations and of chain
members.
-/
theorem nested_chain_fourth_le_energy {Ω ι : Type*} (B : ι → Set Ω)
    (hchain : ∀ i k, B i ⊆ B k ∨ B k ⊆ B i) (U : Set Ω)
    (hU : ∀ i, B i ⊆ U) {n : ℕ} (x : Fin n → Ω) (w : Fin n → ℝ) :
    signAverage (fun σ => chainSignSup B x w σ ^ 4) ≤
      (256 / 27 : ℝ) * chainEnergy U x w ^ 2 := by
  -- Use nested_trace_prefix and replace w by its restriction to U.
  -- Each chain sum is a prefix sum of the restricted permuted coefficients.
  -- Reindex all Boolean signs by p and apply signedPrefixMax_fourth_le_energy.
  -- The empty chain has real supremum zero and satisfies the same bound.
  classical
  obtain ⟨p, hp⟩ := nested_trace_prefix B hchain x
  let a : Fin n → ℝ := fun j => if x (p j) ∈ U then w (p j) else 0
  have henergy : (∑ j, a j ^ 2) = chainEnergy U x w := by
    calc
      _ = ∑ j, if x (p j) ∈ U then w (p j) ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [a]
        split_ifs <;> simp
      _ = _ := Equiv.sum_comp p (fun j => if x j ∈ U then w j ^ 2 else 0)
  have hprefix_nonneg (τ : Fin n → Bool) : 0 ≤ signedPrefixMax a τ := by
    exact le_trans (abs_nonneg (signedPrefix a τ 0))
      (le_ciSup (Set.finite_range (fun k => |signedPrefix a τ k|)).bddAbove
        (0 : Fin (n + 1)))
  have htrace (σ : Fin n → Bool) (i : ι) :
      |∑ j, if x j ∈ B i then (if σ j then (1 : ℝ) else -1) * w j else 0| ≤
        signedPrefixMax a (fun j => σ (p j)) := by
    obtain ⟨k, hk⟩ := hp i
    have heq : (∑ j, if x j ∈ B i then
        (if σ j then (1 : ℝ) else -1) * w j else 0) =
        signedPrefix a (fun j => σ (p j)) k := by
      rw [← Equiv.sum_comp p (fun j => if x j ∈ B i then
        (if σ j then (1 : ℝ) else -1) * w j else 0)]
      unfold signedPrefix
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : x (p j) ∈ B i
      · simp [hj, (hk j).mp hj, a, hU i hj]
      · simp [hj, mt (hk j).mpr hj]
    rw [heq]
    exact le_ciSup
      (Set.finite_range (fun k => |signedPrefix a (fun j => σ (p j)) k|)).bddAbove k
  have hbounded (σ : Fin n → Bool) : BddAbove (Set.range (fun i =>
      |∑ j, if x j ∈ B i then (if σ j then (1 : ℝ) else -1) * w j else 0|)) := by
    refine ⟨signedPrefixMax a (fun j => σ (p j)), ?_⟩
    rintro y ⟨i, rfl⟩
    exact htrace σ i
  have hle (σ : Fin n → Bool) :
      chainSignSup B x w σ ≤ signedPrefixMax a (fun j => σ (p j)) := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · let := hι
      simpa only [chainSignSup, Real.iSup_of_isEmpty] using
        hprefix_nonneg (fun j => σ (p j))
    · let := hι
      exact ciSup_le (htrace σ)
  have hnonneg (σ : Fin n → Bool) : 0 ≤ chainSignSup B x w σ := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · let := hι
      simp only [chainSignSup, Real.iSup_of_isEmpty, le_refl]
    · let := hι
      obtain ⟨i⟩ := hι
      exact le_trans (abs_nonneg _) (le_ciSup (hbounded σ) i)
  have havg : signAverage (fun σ => chainSignSup B x w σ ^ 4) ≤
      signAverage (fun σ => signedPrefixMax a (fun j => σ (p j)) ^ 4) := by
    exact signAverage_mono _ _ (fun σ =>
      pow_le_pow_left₀ (hnonneg σ) (hle σ) 4)
  have hreindex : signAverage (fun σ =>
      signedPrefixMax a (fun j => σ (p j)) ^ 4) =
      signAverage (fun σ => signedPrefixMax a σ ^ 4) := by
    unfold signAverage
    congr 1
    exact (p.symm.arrowCongr (Equiv.refl Bool)).sum_comp
      (fun σ => signedPrefixMax a σ ^ 4)
  calc
    _ ≤ signAverage (fun σ => signedPrefixMax a (fun j => σ (p j)) ^ 4) := havg
    _ = signAverage (fun σ => signedPrefixMax a σ ^ 4) := hreindex
    _ ≤ (256 / 27 : ℝ) * (∑ j, a j ^ 2) ^ 2 := signedPrefixMax_fourth_le_energy a
    _ = _ := by rw [henergy]

end Causalean.Stat.EmpiricalProcess.Countable
