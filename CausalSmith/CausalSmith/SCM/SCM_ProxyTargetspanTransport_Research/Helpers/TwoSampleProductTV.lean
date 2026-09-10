import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmProductTV

/-! A reusable additive total-variation bound for products of two probability measures. -/

open MeasureTheory ProbabilityTheory

namespace CausalSmith.SCM.ProxyTargetspanTransport

/-- [the total-variation distance between two product probability measures is at most the sum of the marginal total-variation distances](goal). -/
theorem tvDist_prod_le_add
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableEq A] [MeasurableEq B] [MeasurableEq (A × B)]
    (mu nu : Measure A) (rho sigma : Measure B)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsProbabilityMeasure rho] [IsProbabilityMeasure sigma] :
    Causalean.Stat.tvDist (mu.prod rho) (nu.prod sigma) ≤
      Causalean.Stat.tvDist mu nu + Causalean.Stat.tvDist rho sigma := by
  let gammaA := Causalean.Stat.maximalCoupling mu nu
  let gammaB := Causalean.Stat.maximalCoupling rho sigma
  let Gamma := gammaA.prod gammaB
  let left : (A × A) × (B × B) → A × B := fun z => (z.1.1, z.2.1)
  let right : (A × A) × (B × B) → A × B := fun z => (z.1.2, z.2.2)
  have hleft : Gamma.map left = mu.prod rho := by
    change (gammaA.prod gammaB).map left = _
    rw [show left = Prod.map Prod.fst Prod.fst by rfl,
      ← Measure.map_prod_map gammaA gammaB measurable_fst measurable_fst,
      Causalean.Stat.maximalCoupling_map_fst,
      Causalean.Stat.maximalCoupling_map_fst]
  have hright : Gamma.map right = nu.prod sigma := by
    change (gammaA.prod gammaB).map right = _
    rw [show right = Prod.map Prod.snd Prod.snd by rfl,
      ← Measure.map_prod_map gammaA gammaB measurable_snd measurable_snd,
      Causalean.Stat.maximalCoupling_map_snd,
      Causalean.Stat.maximalCoupling_map_snd]
  have hcouple :=
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.tvDist_le_coupling_ne
      (mu.prod rho) (nu.prod sigma) Gamma left right (by fun_prop) (by fun_prop)
        hleft hright
  let EA : Set ((A × A) × (B × B)) := {z | z.1.1 ≠ z.1.2}
  let EB : Set ((A × A) × (B × B)) := {z | z.2.1 ≠ z.2.2}
  have hEA : MeasurableSet EA :=
    (measurableSet_eq_fun (measurable_fst.comp measurable_fst)
      (measurable_snd.comp measurable_fst)).compl
  have hEB : MeasurableSet EB :=
    (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd)).compl
  have hsub : {z | left z ≠ right z} ⊆ EA ∪ EB := by
    intro z hz
    by_contra hmem
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, EA, EB, not_not] at hmem
    apply hz
    exact Prod.ext hmem.1 hmem.2
  have hmass : Gamma.real {z | left z ≠ right z} ≤
      Gamma.real EA + Gamma.real EB := by
    exact (measureReal_mono hsub (measure_ne_top Gamma _)).trans
      (measureReal_union_le EA EB)
  let D_A : Set (A × A) := {z | z.1 ≠ z.2}
  let D_B : Set (B × B) := {z | z.1 ≠ z.2}
  have hD_A : MeasurableSet D_A :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hD_B : MeasurableSet D_B :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hmA : Gamma.real EA = gammaA.real {z | z.1 ≠ z.2} := by
    calc
      Gamma.real EA = Gamma.real (Prod.fst ⁻¹' D_A) := by rfl
      _ = (Gamma.map Prod.fst).real D_A :=
        (map_measureReal_apply measurable_fst hD_A).symm
      _ = gammaA.real {z | z.1 ≠ z.2} := by simp [Gamma, D_A]
  have hmB : Gamma.real EB = gammaB.real {z | z.1 ≠ z.2} := by
    calc
      Gamma.real EB = Gamma.real (Prod.snd ⁻¹' D_B) := by rfl
      _ = (Gamma.map Prod.snd).real D_B :=
        (map_measureReal_apply measurable_snd hD_B).symm
      _ = gammaB.real {z | z.1 ≠ z.2} := by simp [Gamma, D_B]
  calc
    Causalean.Stat.tvDist (mu.prod rho) (nu.prod sigma)
        ≤ Gamma.real {z | left z ≠ right z} := hcouple
    _ ≤ Gamma.real EA + Gamma.real EB := hmass
    _ = gammaA.real {z | z.1 ≠ z.2} + gammaB.real {z | z.1 ≠ z.2} := by
      rw [hmA, hmB]
    _ ≤ Causalean.Stat.tvDist mu nu + Causalean.Stat.tvDist rho sigma :=
      add_le_add
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.maximalCoupling_ne_mass_le mu nu)
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.maximalCoupling_ne_mass_le rho sigma)

end CausalSmith.SCM.ProxyTargetspanTransport
