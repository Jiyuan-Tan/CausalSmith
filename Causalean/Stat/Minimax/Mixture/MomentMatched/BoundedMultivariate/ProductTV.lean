module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product

/-!
# Total variation of heterogeneous finite products

Coordinatewise total variation bounds add across a finite independent
product. This version allows each coordinate to have a different law.
-/

public section

open MeasureTheory

namespace Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/- The Causalean product comparison currently covers the iid case. Adapt
  its coupling proof: take an overlap coupling for each pair, product the
  couplings, and bound the event of any coordinate mismatch by the sum of
  coordinate mismatch probabilities. The archived implementation is not a
  permitted import, but its proof can guide this reusable theorem. -/

/-- Two [finite families of coordinatewise probability laws](hyp:μ,ν) have [product total variation no larger than the sum of their coordinatewise total variations](goal). -/
theorem tvDist_pi_le_sum_heterogeneous
    {X : Type*} [MeasurableSpace X] [MeasurableEq X] [Countable X]
    {d : ℕ} (μ ν : Fin d → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] :
    Causalean.Stat.tvDist (Measure.pi μ) (Measure.pi ν) ≤
      ∑ i, Causalean.Stat.tvDist (μ i) (ν i) := by
  induction d with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
      simp [Causalean.Stat.tvDist]
  | succ n ih =>
      let e : ((i : Fin (n + 1)) → X) ≃ᵐ X × ((j : Fin n) → X) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let μ' : Fin n → Measure X := fun j => μ (Fin.succAbove 0 j)
      let ν' : Fin n → Measure X := fun j => ν (Fin.succAbove 0 j)
      let ρ := Measure.pi μ
      let σ := Measure.pi ν
      have hmap_eq :
          Causalean.Stat.tvDist (ρ.map e) (σ.map e) =
            Causalean.Stat.tvDist ρ σ := by
        letI : IsProbabilityMeasure (ρ.map e) :=
          Measure.isProbabilityMeasure_map e.measurable.aemeasurable
        letI : IsProbabilityMeasure (σ.map e) :=
          Measure.isProbabilityMeasure_map e.measurable.aemeasurable
        apply le_antisymm
        · unfold Causalean.Stat.tvDist
          refine ciSup_le fun A => ?_
          rw [Measure.real, Measure.real, Measure.map_apply e.measurable A.2,
            Measure.map_apply e.measurable A.2]
          exact Causalean.Stat.abs_measureReal_sub_le_tvDist
            (A.2.preimage e.measurable)
        · unfold Causalean.Stat.tvDist
          refine ciSup_le fun A => ?_
          have hB : MeasurableSet (e.symm ⁻¹' A.1) :=
            A.2.preimage e.symm.measurable
          have hle := Causalean.Stat.abs_measureReal_sub_le_tvDist
            (μ := ρ.map e) (ν := σ.map e) hB
          rw [Measure.real, Measure.real, Measure.map_apply e.measurable hB,
            Measure.map_apply e.measurable hB] at hle
          have hpre : e ⁻¹' (e.symm ⁻¹' A.1) = A.1 := by
            ext x
            simp
          rw [hpre] at hle
          exact hle
      have hμ : Measure.map e (Measure.pi μ) = (μ 0).prod (Measure.pi μ') := by
        simpa [e, μ'] using (measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))).map_eq
      have hν : Measure.map e (Measure.pi ν) = (ν 0).prod (Measure.pi ν') := by
        simpa [e, ν'] using (measurePreserving_piFinSuccAbove ν (0 : Fin (n + 1))).map_eq
      calc
        Causalean.Stat.tvDist (Measure.pi μ) (Measure.pi ν) =
            Causalean.Stat.tvDist (Measure.map e (Measure.pi μ))
              (Measure.map e (Measure.pi ν)) := by
                simpa [ρ, σ] using hmap_eq.symm
        _ = Causalean.Stat.tvDist ((μ 0).prod (Measure.pi μ'))
              ((ν 0).prod (Measure.pi ν')) := by rw [hμ, hν]
        _ ≤ Causalean.Stat.tvDist (μ 0) (ν 0) +
              Causalean.Stat.tvDist (Measure.pi μ') (Measure.pi ν') :=
            Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_prod_le_add _ _ _ _
        _ ≤ Causalean.Stat.tvDist (μ 0) (ν 0) +
              ∑ j, Causalean.Stat.tvDist (μ' j) (ν' j) :=
            add_le_add_right (ih μ' ν') _
        _ = ∑ i, Causalean.Stat.tvDist (μ i) (ν i) := by
            simp [Fin.sum_univ_succ, μ', ν']

end Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
