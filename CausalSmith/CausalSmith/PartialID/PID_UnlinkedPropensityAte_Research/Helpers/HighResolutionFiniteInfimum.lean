module
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Finite assembly of independent reproduction-center infima. -/

@[expose] public section

open Set
open scoped BigOperators

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ι,Z,C,cost,i), [this definition](goal) introduces the corresponding object. -/
def independentCenterValues {ι Z : Type*}
    (C : ι → Set Z) (cost : ι → Z → ℝ) (i : ι) : Set ℝ :=
  {v | ∃ z ∈ C i, v = cost i z}

/-- For [the specified mathematical inputs](hyp:ι,Z,C,cost), [this definition](goal) introduces the corresponding object. -/
def independentCenterTotalValues {ι Z : Type*} [Fintype ι]
    (C : ι → Set Z) (cost : ι → Z → ℝ) : Set ℝ :=
  {v | ∃ z : ι → Z, (∀ i, z i ∈ C i) ∧ v = ∑ i, cost i (z i)}

/-- Given [the stated mathematical inputs and assumptions](hyp:ι,Z,C,cost,hne,hbelow), this result [establishes the stated mathematical conclusion](goal). -/
lemma sInf_independentCenterTotalValues_eq_sum_of_nonempty_bddBelow
    {ι Z : Type*} [Fintype ι]
    (C : ι → Set Z) (cost : ι → Z → ℝ)
    (hne : ∀ i, (independentCenterValues C cost i).Nonempty)
    (hbelow : ∀ i, BddBelow (independentCenterValues C cost i)) :
    sInf (independentCenterTotalValues C cost) =
      ∑ i, sInf (independentCenterValues C cost i) := by
  classical
  choose lower hlower using hbelow
  have hne' := hne
  choose initial hinitial using hne
  choose z hzC hzcost using fun i => hinitial i
  have htotalBelow : BddBelow (independentCenterTotalValues C cost) := by
    refine ⟨∑ i, lower i, ?_⟩
    rintro v ⟨w, hwC, rfl⟩
    apply Finset.sum_le_sum
    intro i hi
    exact hlower i ⟨w i, hwC i, rfl⟩
  have htotalNonempty :
      (independentCenterTotalValues C cost).Nonempty :=
    ⟨∑ i, cost i (z i), z, hzC, rfl⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro δ hδ
    let η : ℝ := δ / ((Fintype.card ι : ℝ) + 1)
    have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
    have hη : 0 < η := div_pos hδ hden
    have hbudget : (Fintype.card ι : ℝ) * η < δ := by
      dsimp [η]
      rw [show (Fintype.card ι : ℝ) *
          (δ / ((Fintype.card ι : ℝ) + 1)) =
          ((Fintype.card ι : ℝ) * δ) /
            ((Fintype.card ι : ℝ) + 1) by ring]
      rw [div_lt_iff₀ hden]
      have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
      nlinarith
    have happrox (i : ι) : ∃ v ∈ independentCenterValues C cost i,
        v < sInf (independentCenterValues C cost i) + η :=
      Real.lt_sInf_add_pos (hne' i) hη
    choose v hv hvalt using happrox
    choose w hwC hvw using fun i => hv i
    have hmember : (∑ i, cost i (w i)) ∈
        independentCenterTotalValues C cost :=
      ⟨w, hwC, rfl⟩
    have hinf : sInf (independentCenterTotalValues C cost) ≤
        ∑ i, cost i (w i) := csInf_le htotalBelow hmember
    have hsum : (∑ i, cost i (w i)) ≤
        ∑ i, (sInf (independentCenterValues C cost i) + η) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← hvw i]
      exact (hvalt i).le
    calc
      sInf (independentCenterTotalValues C cost) ≤
          ∑ i, cost i (w i) := hinf
      _ ≤ ∑ i, (sInf (independentCenterValues C cost i) + η) := hsum
      _ = (∑ i, sInf (independentCenterValues C cost i)) +
          (Fintype.card ι : ℝ) * η := by
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ (∑ i, sInf (independentCenterValues C cost i)) + δ := by
        linarith
  · apply le_csInf htotalNonempty
    rintro v ⟨w, hwC, rfl⟩
    apply Finset.sum_le_sum
    intro i hi
    exact csInf_le ⟨lower i, hlower i⟩ ⟨w i, hwC i, rfl⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ι,a,b,hab,cost,hbelow), this result [establishes the stated mathematical conclusion](goal). -/
lemma sInf_independentCenterTotalValues_Icc_eq_sum_of_bddBelow
    {ι : Type*} [Fintype ι] (a b : ℝ) (hab : a ≤ b)
    (cost : ι → ℝ → ℝ)
    (hbelow : ∀ i, BddBelow
      (independentCenterValues (fun _ : ι => Set.Icc a b) cost i)) :
    sInf (independentCenterTotalValues (fun _ : ι => Set.Icc a b) cost) =
      ∑ i, sInf
        (independentCenterValues (fun _ : ι => Set.Icc a b) cost i) := by
  apply sInf_independentCenterTotalValues_eq_sum_of_nonempty_bddBelow
  · intro i
    exact ⟨cost i a, a, ⟨le_rfl, hab⟩, rfl⟩
  · exact hbelow

end
end CausalSmith.PartialID.UnlinkedPropensityAte
