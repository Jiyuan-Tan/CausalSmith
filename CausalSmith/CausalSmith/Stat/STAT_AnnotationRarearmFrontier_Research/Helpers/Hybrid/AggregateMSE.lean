module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.BaselinePoissonRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.AggregateVariance

/-!
Mean squared error assembly for independent canonical hybrid cells, retaining every
variance and squared-bias term from roadmap equations (12)--(14).
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- [Under the stated inputs and conditions](hyp:d,L,k0,B,u,tp,t,s,v,mu), Independence across canonical cells turns the MSE of their sum into the sum
of the cell variances plus the squared sum of their biases.  This gives [the stated result](goal).-/
-- @node: hybrid_canonical_mse_decomposition
lemma hybrid_canonical_mse_decomposition {d : Nat} (L k0 : Nat)
    (B u tp t : Real) (s v mu : Fin d → Real) :
    let nu := fun j => (poissonMeasure (Real.toNNReal (tp * s j))).prod
      (cellPoissonLaw u t (s j * mu j) (s j) (v j))
    let V := fun z : Nat × (Nat × Nat × Nat) =>
      hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2
    (∫ z : Fin d → Nat × (Nat × Nat × Nat),
      ((∑ j, V (z j)) - ∑ j, (s j + v j) * mu j) ^ 2 ∂Measure.pi nu) =
      (∑ j, variance V (nu j)) +
        (∑ j, ((∫ z, V z ∂nu j) - (s j + v j) * mu j)) ^ 2 := by
  dsimp only
  let nu := fun j => (poissonMeasure (Real.toNNReal (tp * s j))).prod
    (cellPoissonLaw u t (s j * mu j) (s j) (v j))
  let V := fun z : Nat × (Nat × Nat × Nat) =>
    hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2
  let (j : Fin d) : IsProbabilityMeasure (nu j) := by
    dsimp [nu, cellPoissonLaw]
    infer_instance
  have hcell (j : Fin d) : MemLp V 2 (nu j) :=
    hybrid_pilot_cell_memLp L k0 B u tp t (s j * mu j) (s j) (v j)
  have heval (j : Fin d) : MemLp (fun z => V (z j)) 2 (Measure.pi nu) :=
    (hcell j).comp_measurePreserving (measurePreserving_eval nu j)
  have hsum : MemLp (fun z => ∑ j, V (z j)) 2 (Measure.pi nu) := by
    apply memLp_finsetSum
    intro j _
    exact heval j
  rw [baseline_mse_eq_variance_add_bias hsum]
  have hvar : variance (fun z => ∑ j, V (z j)) (Measure.pi nu) =
      ∑ j, variance V (nu j) := by
    have hfun : (fun z : Fin d → Nat × (Nat × Nat × Nat) => ∑ j, V (z j)) =
        ∑ j, (fun z => V (z j)) := by funext z; simp
    rw [hfun]
    exact variance_sum_pi hcell
  have hmean : (∫ z, ∑ j, V (z j) ∂Measure.pi nu) =
      ∑ j, ∫ z, V z ∂nu j := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      exact integral_comp_eval (hcell j).aestronglyMeasurable
    · intro j _
      exact (heval j).integrable (by norm_num)
  change variance (fun z => ∑ j, V (z j)) (Measure.pi nu) +
    ((∫ z, ∑ j, V (z j) ∂Measure.pi nu) - ∑ j, (s j + v j) * mu j) ^ 2 = _
  rw [hvar, hmean, ← Finset.sum_sub_distrib]

/-- Under the stated inputs and conditions, The proved light/heavy variance assembly and squared total bias bound give
the canonical arm MSE envelope, without dropping either incorrect pilot branch.
The inverse-count sum remains explicit for its separate overlap bound.  This gives [the stated result](goal). -/
-- @node: hybrid_canonical_mse_envelope
lemma hybrid_canonical_mse_envelope :
    ∃ CP CH : Real, 0 < CP ∧ 0 < CH ∧ ∀ (S u tp t eps : Real),
      Real.exp 4096 ≤ S → 0 < u → 0 < tp → 0 < t → 0 < eps → eps ≤ 1 →
      1 / 3 ≤ t / tp → ∀ (d : Nat) (s v mu : Fin d → Real),
      (∀ j, 0 ≤ s j ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1 ∧
        eps * (s j + v j) ≤ s j) →
      (∑ j, (s j + v j)) ≤ 1 →
      let L := Nat.floor (Real.log S / 1024)
      let B : Real := (2 : Real) ^ 20 * L / min tp t
      let k0 := Nat.floor (tp * B / 4)
      let light := Finset.univ.filter (fun j => s j ≤ B)
      let M := light.sum (fun j => s j + v j)
      let nu := fun j => cellPoissonLaw u t (s j * mu j) (s j) (v j)
      (∫ z : Fin d → Nat × (Nat × Nat × Nat),
        ((∑ j, hybridCellValue L B k0 u t (z j).2.1 (z j).1
          (z j).2.2.1 (z j).2.2.2) - ∑ j, (s j + v j) * mu j) ^ 2 ∂
        Measure.pi (fun j => (poissonMeasure (Real.toNNReal (tp * s j))).prod (nu j))) ≤
      (∑ j, variance (inverseCellBranch u) (nu j)) +
        CP * ((2 : Real) ^ 24) ^ L * (M / (u * eps) + M / t + light.card * B ^ 2 / eps ^ 2) +
        2 * light.card * (B / (eps * (L : Real) ^ 2)) ^ 2 +
        1 / (Real.exp 1 * t * eps) +
        CH * (S ^ 20)⁻¹ * (1 / (u * eps) + 1 + 1 / t) +
        2 * (d : Real) ^ 2 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) +
        18 * (S ^ 20)⁻¹ := by
  obtain ⟨CP, CH, hCP, hCH, hvariance⟩ := hybrid_canonical_variance_sum
  refine ⟨CP, CH, hCP, hCH, ?_⟩
  intro S u tp t eps hS hu htp ht heps heps1 hratio d s v mu hcell hmass
  dsimp only
  let L := Nat.floor (Real.log S / 1024)
  let B : Real := (2 : Real) ^ 20 * L / min tp t
  have hL4 : 4 ≤ L := (hybrid_degree_calibration S hS).1
  have hLp : 0 < (L : Real) := by exact_mod_cast (show 0 < L by omega)
  have hB : 0 < B := by dsimp [B]; positivity
  have hpilot := hybrid_bandwidth_pilot_scale L tp t htp ht
  have hfactorial := hybrid_bandwidth_pilot_scale L t tp ht htp
  rw [min_comm t tp] at hfactorial
  have hD : (L : Real) ≤ t * B := by
    change (2 : Real) ^ 20 * L ≤ t * B at hfactorial
    have hpower : (1 : Real) ≤ 2 ^ 20 := by norm_num
    nlinarith only [hfactorial, hpower, hLp]
  have hv := hvariance S B u tp t eps hS hB hu htp ht heps heps1 hD hpilot
    Finset.univ s v mu (fun j _ => hcell j) hmass
  have hb := hybrid_selected_squared_bias_sum S u tp t eps hS hu htp ht heps hratio
    Finset.univ s v mu (fun j _ => hcell j) hmass
  rw [hybrid_canonical_mse_decomposition]
  have hh := add_le_add hv hb
  simpa only [Finset.card_univ, Fintype.card_fin, add_assoc] using hh

end CausalSmith.Stat.AnnotationRarearmFrontier
