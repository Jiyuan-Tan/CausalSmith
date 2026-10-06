module
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.Sequences

/-!
# Countable one-sided skeletons inside arbitrary real subsets

A deterministic eligibility set need not be open or have a continuous loss.
Choose a countable dense subset of that set and adjoin its points isolated on
the required side. Those boundary representatives are countable by Mathlib's
countable_setOfPred_isolated_left_within/right_within. Approximation stays
inside eligibility, even at a closed localization boundary.
-/

@[expose] public section

open Filter Set Topology
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- [A sequence of cutoffs](hyp:s) [one-sidedly approximates](goal) [a
cutoff t](hyp:t) from [the side selected by a Boolean flag](hyp:upper) when
[every term lies at or above t if the flag is true, or at or below t if it
is false](step:1), and [the sequence converges to t](step:2).

Equality is allowed throughout.
-/
def OneSidedApproximates (upper : Bool) (s : ℕ → ℝ) (t : ℝ) : Prop :=
  (∀ k, if upper then t ≤ s k else s k ≤ t) ∧ Tendsto s atTop (nhds t)

/-- [The one-sided boundary](goal) of [a set T of eligible
cutoffs](hyp:T), on [the side selected by a Boolean flag](hyp:upper), is
[the set of points of T that are isolated from the points of T strictly
above them (flag true) or strictly below them (flag false)](step:1).

Such cutoffs cannot be approximated from that side and must be included as
representatives.
-/
def oneSidedBoundary (upper : Bool) (T : Set ℝ) : Set ℝ :=
  {t ∈ T | nhdsWithin t (T ∩ (if upper then Ioi t else Iio t)) = ⊥}

/-- [The one-sided boundary of any set of reals, on either side, is
countable](goal). -/
theorem oneSidedBoundary_countable (upper : Bool) (T : Set ℝ) :
    (oneSidedBoundary upper T).Countable := by
  cases upper
  · exact countable_setOfPred_isolated_left_within
  · exact countable_setOfPred_isolated_right_within

/-- [Every set T of reals has a countable subset that contains its
one-sided boundary and approximates every point of T, from the selected
side, by a sequence lying entirely in that subset](goal). -/
theorem exists_countable_oneSided_skeleton (upper : Bool) (T : Set ℝ) :
    ∃ D : Set ℝ, D.Countable ∧ D ⊆ T ∧ oneSidedBoundary upper T ⊆ D ∧
      ∀ t ∈ T, ∃ s : ℕ → ℝ, (∀ k, s k ∈ D) ∧ OneSidedApproximates upper s t := by
  classical
  obtain ⟨C, hCT, hC, hTC⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace T).exists_countable_dense_subset
  refine ⟨C ∪ oneSidedBoundary upper T,
    hC.union (oneSidedBoundary_countable upper T), ?_, subset_union_right, ?_⟩
  · rintro x (hx | hx)
    · exact hCT hx
    · exact hx.1
  · intro t ht
    by_cases hb : t ∈ oneSidedBoundary upper T
    · refine ⟨fun _ => t, fun _ => Or.inr hb, ?_, tendsto_const_nhds⟩
      intro k
      cases upper <;> exact le_rfl
    · let U : Set ℝ := if upper then Ioi t else Iio t
      have hU : IsOpen U := by
        cases upper <;> simp [U, isOpen_Iio, isOpen_Ioi]
      have hn : nhdsWithin t (T ∩ U) ≠ ⊥ := by
        intro h
        exact hb ⟨ht, h⟩
      have hcl : t ∈ closure (T ∩ U) :=
        mem_closure_iff_nhdsWithin_neBot.mpr ⟨hn⟩
      have hsub : T ∩ U ⊆ closure (C ∩ U) := by
        intro x hx
        exact hU.closure_inter ⟨hTC hx.1, hx.2⟩
      have hd : t ∈ closure (C ∩ U) :=
        (closure_minimal hsub isClosed_closure) hcl
      obtain ⟨s, hs, hst⟩ := mem_closure_iff_seq_limit.mp hd
      refine ⟨s, fun k => Or.inl (hs k).1, ?_, hst⟩
      intro k
      have hk := (hs k).2
      cases upper <;> exact le_of_lt hk


end Causalean.Stat.EmpiricalProcess.Countable
