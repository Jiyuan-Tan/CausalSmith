module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.FactorialCertificate
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.AggregateBias
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.AggregateMSE
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.AggregateVariance
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.BetweenBranch
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.CanonicalRate
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.CountTransfer
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.FalseLightRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.MixtureVariance
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.RateAbsorption
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.InverseCountArmRisk
public import Causalean.Stat.Concentration.Poisson.Threshold

/-!
Uniform arm MSE bound for the independent three-pool hybrid statistic.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

-- @node: lem:uniform-hybrid-arm-risk
/--
[The three-pool Poisson hybrid arm statistic has the universal rare-overlap mean squared error
bound](goal).
-/
lemma uniform_hybrid_arm_risk :
    ∃ C : Real, 0 < C ∧ ∀ (n m d : Nat) (eps : Real) (P : DiscreteLaw d)
      (a : Bool) (u tp t : Real),
      1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 → Real.exp 4096 ≤ (n : Real) * eps →
      ModelClass d eps P → (n : Real) / 32 ≤ u → ((n : Real) + m) / 64 ≤ tp →
      ((n : Real) + m) / 64 ≤ t → 1 / 3 ≤ t / tp → t / tp ≤ 3 →
      let L := Nat.floor (Real.log ((n : Real) * eps) / 1024)
      let B : Real := 2 ^ 20 * L / min tp t
      let k0 := Nat.floor (tp * B / 4)
      ∀ (Om : Type) [MeasurableSpace Om] (mu : Measure Om) [IsProbabilityMeasure mu]
        (Z J K : Bool → Fin d → Om → Nat),
        (∀ b j, Measurable (Z b j) ∧ Measurable (J b j) ∧ Measurable (K b j)) →
        (∀ b j, mu.map (Z b j) = poissonMeasure (Real.toNNReal (u * markedMass P j b))) →
        (∀ b j, mu.map (J b j) = poissonMeasure (Real.toNNReal (tp * armMass P j b))) →
        (∀ b j, mu.map (K b j) = poissonMeasure (Real.toNNReal (t * armMass P j b))) →
        ProbabilityTheory.iIndepFun (fun i : Fin 3 × Bool × Fin d =>
          if i.1 = 0 then Z i.2.1 i.2.2 else if i.1 = 1 then J i.2.1 i.2.2 else K i.2.1 i.2.2) mu →
        (∫ om, ((∑ j : Fin d, hybridCellValue L B k0 u t
          (Z a j om) (J a j om) (K a j om) (K (!a) j om)) -
            ∑ j : Fin d, cellMass P j * outcomeMean P a j) ^ 2 ∂mu) ≤
          C * (1 / ((n : Real) * eps) + ((d : Real) / (((n : Real) + m) * eps * L)) ^ 2) :=
  by
    classical
    obtain ⟨C, hC, hcanonical⟩ := hybrid_canonical_arm_rate
    refine ⟨C, hC, ?_⟩
    intro n m d eps P a u tp t hn hd heps heps4 hS hP hu htp ht hratio _
    dsimp only
    intro Om _ mu _ Z J K hmeas hZ hJ hK hind
    let X : Fin 4 × Fin d → Om → Nat := fun i =>
      if i.1 = 0 then J a i.2 else if i.1 = 1 then Z a i.2
      else if i.1 = 2 then K a i.2 else K (!a) i.2
    have hX (i) : Measurable (X i) := by
      dsimp [X]
      split_ifs <;> first
      | exact (hmeas a i.2).1
      | exact (hmeas a i.2).2.1
      | exact (hmeas a i.2).2.2
      | exact (hmeas (!a) i.2).2.2
    let idx : Fin 4 × Fin d → Fin 3 × Bool × Fin d := fun i =>
      if i.1 = 0 then (1,a,i.2) else if i.1 = 1 then (0,a,i.2)
      else if i.1 = 2 then (2,a,i.2) else (2,!a,i.2)
    have hinj : Function.Injective idx := by
      rintro ⟨i,j⟩ ⟨i',j'⟩ h
      fin_cases i <;> fin_cases i' <;> simp [idx] at h ⊢ <;>
        exact h
    have hi : iIndepFun X mu := by
      have hh := hind.precomp hinj
      have hfun : (fun i : Fin 4 × Fin d =>
          if (idx i).1 = 0 then Z (idx i).2.1 (idx i).2.2
          else if (idx i).1 = 1 then J (idx i).2.1 (idx i).2.2
          else K (idx i).2.1 (idx i).2.2) = X := by
        funext ⟨i,j⟩
        fin_cases i <;> simp [idx, X]
      rw [hfun] at hh
      exact hh
    have hlaw := hybrid_four_count_product_law mu X hX hi
    simp only [X, Fin.reduceEq, if_true, if_false] at hlaw
    simp_rw [hJ, hZ, hK] at hlaw
    have hsum (j : Fin d) : armMass P j a + armMass P j (!a) = cellMass P j := by
      cases a <;> simp [cellMass, armMass, add_comm]
    have hq (j : Fin d) : armMass P j a * outcomeMean P a j = markedMass P j a := by
      by_cases hz : armMass P j a = 0
      · have hbound : markedMass P j a ≤ armMass P j a := by
          simp only [markedMass, armMass, Fintype.sum_bool]
          linarith [jointMass_nonneg P j a false]
        have hzero : markedMass P j a = 0 :=
          le_antisymm (hz ▸ hbound) (jointMass_nonneg P j a true)
        simp [hz, hzero]
      · dsimp only [outcomeMean]; field_simp
    have hc := hcanonical ((n : Real) * eps) ((n : Real) + m) eps u tp t hS heps
      (by linarith) (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (Nat.cast_nonneg m)) heps.le)
      (by nlinarith) htp ht hratio d
      (fun j => armMass P j a) (fun j => armMass P j (!a)) (outcomeMean P a)
      (by omega)
      (fun j => ⟨armMass_nonneg P j a, armMass_nonneg P j (!a),
        outcomeMean_mem_Icc P a j, by rw [hsum]; exact armMass_ge_overlap_cellMass P eps hP j a⟩)
      (by simpa only [hsum, sum_cellMass] using (le_refl (1 : Real)))
    dsimp only at hc
    simp_rw [hsum, hq] at hc
    let F : (Fin d → Nat × (Nat × Nat × Nat)) → Real := fun z =>
      ((∑ j, hybridCellValue (Nat.floor (Real.log ((n : Real) * eps) / 1024))
        (2 ^ 20 * Nat.floor (Real.log ((n : Real) * eps) / 1024) / min tp t)
        (Nat.floor (tp * (2 ^ 20 * Nat.floor (Real.log ((n : Real) * eps) / 1024) /
          min tp t) / 4)) u t (z j).2.1 (z j).1 (z j).2.2.1 (z j).2.2.2) -
        ∑ j, cellMass P j * outcomeMean P a j) ^ 2
    have hmap : Measurable (fun om j => (J a j om, Z a j om, K a j om, K (!a) j om)) := by
      apply measurable_pi_lambda
      intro j
      exact (hmeas a j).2.1.prodMk ((hmeas a j).1.prodMk
        ((hmeas a j).2.2.prodMk (hmeas (!a) j).2.2))
    have hF : Measurable F := measurable_of_countable F
    have heq := integral_map (μ := mu) hmap.aemeasurable hF.aestronglyMeasurable
    rw [hlaw] at heq
    change (∫ om, F (fun j => (J a j om, Z a j om, K a j om, K (!a) j om)) ∂mu) ≤ _
    rw [← heq]
    exact hc

end CausalSmith.Stat.AnnotationRarearmFrontier
