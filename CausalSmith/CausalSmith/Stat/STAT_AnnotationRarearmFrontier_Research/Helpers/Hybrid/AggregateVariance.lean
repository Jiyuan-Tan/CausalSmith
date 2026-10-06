module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.BetweenBranch
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.FalseLightRisk

/-!
Light-cell assembly of the pilot-mixture variance in roadmap equation (13).
All three mixture terms are retained, including at null cells.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- Under the stated inputs and conditions, Summing equation (13) over light cells retains the inverse-count variance,
the polynomial mass envelope, and both parts of the branch separation.  This gives [the stated result](goal). -/
-- @node: light_hybrid_variance_sum
lemma light_hybrid_variance_sum :
    ∃ C : Real, 0 < C ∧ ∀ (L k0 : Nat) (B u tp t eps : Real),
      4 ≤ L → 0 < B → 0 < u → 0 < t → 0 < eps → eps ≤ 1 →
      (L : Real) ≤ t * B → ∀ {alpha : Type} (J : Finset alpha)
      (s v mu : alpha → Real),
      (∀ j ∈ J, 0 ≤ s j ∧ s j ≤ B ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1 ∧
        eps * (s j + v j) ≤ s j) →
      (J.sum (fun j => s j + v j)) ≤ 1 →
      let nu := fun j => cellPoissonLaw u t (s j * mu j) (s j) (v j)
      (∑ j ∈ J, variance (fun z : Nat × (Nat × Nat × Nat) =>
        hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2)
        ((poissonMeasure (Real.toNNReal (tp * s j))).prod (nu j))) ≤
      (∑ j ∈ J, variance (inverseCellBranch u) (nu j)) +
        C * ((2 : Real) ^ 24) ^ L *
          ((J.sum (fun j => s j + v j)) / (u * eps) +
            (J.sum (fun j => s j + v j)) / t + J.card * B ^ 2 / eps ^ 2) +
        2 * J.card * (B / (eps * (L : Real) ^ 2)) ^ 2 +
          1 / (Real.exp 1 * t * eps) := by
  obtain ⟨C, hC, hpol⟩ := light_polynomial_variance_sum
  refine ⟨C, hC, ?_⟩
  intro L k0 B u tp t eps hL hB hu ht heps heps1 hD alpha J s v mu hcell hmass
  dsimp only
  let nu := fun j => cellPoissonLaw u t (s j * mu j) (s j) (v j)
  let pi := fun j => (poissonMeasure (Real.toNNReal (tp * s j))).real (Set.Iic k0)
  have hq (j) (hj : j ∈ J) :
      0 ≤ s j * mu j ∧ s j * mu j ≤ s j ∧ s j ≤ B ∧ 0 ≤ v j ∧
        eps * (s j + v j) ≤ s j := by
    obtain ⟨hs, hsB, hv, hmu, hov⟩ := hcell j hj
    exact ⟨mul_nonneg hs hmu.1, mul_le_of_le_one_right hs hmu.2, hsB, hv, hov⟩
  have hp := hpol L B u t eps hL hB hu ht heps heps1 hD
    J (fun j => s j * mu j) s v hq
  have hb := hybrid_light_between_branch_sum J s v mu pi L B u t eps
    (by omega) hB hu ht heps hcell hmass
  calc
    _ ≤ ∑ j ∈ J, (variance (inverseCellBranch u) (nu j) +
        variance (polynomialCellBranch L B u t) (nu j) +
        pi j * (1 - pi j) *
          ((∫ z, polynomialCellBranch L B u t z ∂nu j) -
            ∫ z, inverseCellBranch u z ∂nu j) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [hybrid_pilot_cell_variance]
      have hheavy : (1 - pi j) * variance (inverseCellBranch u) (nu j) ≤
          variance (inverseCellBranch u) (nu j) :=
        mul_le_of_le_one_left (variance_nonneg _ _) (by
          have hh : 0 ≤ pi j := measureReal_nonneg
          linarith)
      have hpoly : pi j * variance (polynomialCellBranch L B u t) (nu j) ≤
          variance (polynomialCellBranch L B u t) (nu j) :=
        mul_le_of_le_one_left (variance_nonneg _ _) (show pi j ≤ 1 from measureReal_le_one)
      have hh := add_le_add_right (add_le_add hpoly hheavy)
        (pi j * (1 - pi j) *
          ((∫ z, polynomialCellBranch L B u t z ∂nu j) -
            ∫ z, inverseCellBranch u z ∂nu j) ^ 2)
      simpa only [nu, pi, add_comm] using hh
    _ = (∑ j ∈ J, variance (inverseCellBranch u) (nu j)) +
        (∑ j ∈ J, variance (polynomialCellBranch L B u t) (nu j)) +
        (∑ j ∈ J, pi j * (1 - pi j) *
          ((∫ z, polynomialCellBranch L B u t z ∂nu j) -
            ∫ z, inverseCellBranch u z ∂nu j) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := by
      have hh := add_le_add (add_le_add_left hp
        (∑ j ∈ J, variance (inverseCellBranch u) (nu j))) hb
      simpa only [nu, add_assoc, add_comm, add_left_comm] using hh

/-- Under the stated inputs and conditions, Adding the light and heavy cell bounds retains every term of equation (13).
The only global mass requirement is total mass at most one.  This gives [the stated result](goal). -/
-- @node: hybrid_canonical_variance_sum
lemma hybrid_canonical_variance_sum :
    ∃ CP CH : Real, 0 < CP ∧ 0 < CH ∧ ∀ (S B u tp t eps : Real),
      Real.exp 4096 ≤ S → 0 < B → 0 < u → 0 < tp → 0 < t → 0 < eps → eps ≤ 1 →
      (Nat.floor (Real.log S / 1024) : Real) ≤ t * B →
      (2 : Real) ^ 20 * Nat.floor (Real.log S / 1024) ≤ tp * B →
      ∀ {alpha : Type} (J : Finset alpha) (s v mu : alpha → Real),
      (∀ j ∈ J, 0 ≤ s j ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1 ∧
        eps * (s j + v j) ≤ s j) →
      (J.sum (fun j => s j + v j)) ≤ 1 →
      let L := Nat.floor (Real.log S / 1024)
      let k0 := Nat.floor (tp * B / 4)
      let light := J.filter (fun j => s j ≤ B)
      let M := light.sum (fun j => s j + v j)
      let nu := fun j => cellPoissonLaw u t (s j * mu j) (s j) (v j)
      (∑ j ∈ J, variance (fun z : Nat × (Nat × Nat × Nat) =>
        hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2)
        ((poissonMeasure (Real.toNNReal (tp * s j))).prod (nu j))) ≤
      (∑ j ∈ J, variance (inverseCellBranch u) (nu j)) +
        CP * ((2 : Real) ^ 24) ^ L * (M / (u * eps) + M / t + light.card * B ^ 2 / eps ^ 2) +
        2 * light.card * (B / (eps * (L : Real) ^ 2)) ^ 2 +
        1 / (Real.exp 1 * t * eps) +
        CH * (S ^ 20)⁻¹ * (1 / (u * eps) + 1 + 1 / t) := by
  obtain ⟨CP, hCP, hlight⟩ := light_hybrid_variance_sum
  obtain ⟨CH, hCH, hheavy⟩ := heavy_hybrid_variance_sum
  refine ⟨CP, CH, hCP, hCH, ?_⟩
  intro S B u tp t eps hS hB hu htp ht heps heps1 hD hscale alpha J s v mu hcell hmass
  dsimp only
  let L := Nat.floor (Real.log S / 1024)
  let k0 := Nat.floor (tp * B / 4)
  let light := J.filter (fun j => s j ≤ B)
  let heavy := J.filter (fun j => ¬s j ≤ B)
  let nu := fun j => cellPoissonLaw u t (s j * mu j) (s j) (v j)
  let V := fun j => variance (fun z : Nat × (Nat × Nat × Nat) =>
    hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2)
    ((poissonMeasure (Real.toNNReal (tp * s j))).prod (nu j))
  have hmass_sub (K : Finset alpha) (hK : K ⊆ J) :
      (K.sum (fun j => s j + v j)) ≤ 1 := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hK ?_) hmass
    intro j hj _
    exact add_nonneg (hcell j hj).1 (hcell j hj).2.1
  have hlcell (j) (hj : j ∈ light) :
      0 ≤ s j ∧ s j ≤ B ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1 ∧ eps * (s j + v j) ≤ s j := by
    obtain ⟨hjJ, hsB⟩ := Finset.mem_filter.mp hj
    obtain ⟨hs, hv, hm, hov⟩ := hcell j hjJ
    exact ⟨hs, hsB, hv, hm, hov⟩
  have hhcell (j) (hj : j ∈ heavy) :
      B < s j ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1 ∧ eps * (s j + v j) ≤ s j := by
    obtain ⟨hjJ, hsB⟩ := Finset.mem_filter.mp hj
    obtain ⟨hs, hv, hm, hov⟩ := hcell j hjJ
    exact ⟨lt_of_not_ge hsB, hv, hm, hov⟩
  have hl := hlight L k0 B u tp t eps (hybrid_degree_calibration S hS).1
    hB hu ht heps heps1 hD light s v mu hlcell
    (hmass_sub light (Finset.filter_subset _ _))
  have hh := hheavy S B u tp t eps hS hB hu htp ht heps heps1 hD hscale
    heavy s v mu hhcell (hmass_sub heavy (Finset.filter_subset _ _))
  have hsplit (f : alpha → Real) : light.sum f + heavy.sum f = J.sum f :=
    Finset.sum_filter_add_sum_filter_not J (fun j => s j ≤ B) f
  have hadd := add_le_add hl hh
  change light.sum V + heavy.sum V ≤ _ at hadd
  rw [hsplit V] at hadd
  have hinverse := hsplit (fun j => variance (inverseCellBranch u) (nu j))
  dsimp only [nu] at hinverse
  dsimp only [V, nu] at hadd
  linarith only [hadd, hinverse]

/-- [Under the stated inputs and conditions](hyp:hS,hu,htp,ht,heps,hratio,alpha,J,S,u,tp,t,eps,s,v,mu), Squaring equation (12) gives the approximation term and a pilot remainder
of the same order retained in equation (14), including null cells.  This gives [the stated result](goal).-/
-- @node: hybrid_selected_squared_bias_sum
lemma hybrid_selected_squared_bias_sum (S u tp t eps : Real)
    (hS : Real.exp 4096 ≤ S) (hu : 0 < u) (htp : 0 < tp) (ht : 0 < t)
    (heps : 0 < eps) (hratio : 1 / 3 ≤ t / tp)
    {alpha : Type} (J : Finset alpha) (s v mu : alpha → Real) :
    let L := Nat.floor (Real.log S / 1024)
    let B : Real := (2 : Real) ^ 20 * L / min tp t
    let k0 := Nat.floor (tp * B / 4)
    (∀ j ∈ J, 0 ≤ s j ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1 ∧
      eps * (s j + v j) ≤ s j) →
    (J.sum (fun j => s j + v j)) ≤ 1 →
    (∑ j ∈ J, ((∫ z : Nat × (Nat × Nat × Nat),
      hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2 ∂
      (poissonMeasure (Real.toNNReal (tp * s j))).prod
        (cellPoissonLaw u t (s j * mu j) (s j) (v j))) - (s j + v j) * mu j)) ^ 2 ≤
      2 * (J.card : Real) ^ 2 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) +
        18 * (S ^ 20)⁻¹ := by
  dsimp only
  intro hcell hmass
  let L := Nat.floor (Real.log S / 1024)
  let B : Real := (2 : Real) ^ 20 * L / min tp t
  let b : Real := J.card * (B / (eps * (L : Real) ^ 2))
  let r : Real := (S ^ 20)⁻¹
  have hb := hybrid_selected_bias_sum S u tp t eps hS hu htp ht heps hratio
    J s v mu hcell hmass
  have hS1 : 1 ≤ S := (Real.one_le_exp (by norm_num : (0 : Real) ≤ 4096)).trans hS
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hS1)
  have hr2 : r ^ 2 ≤ r := by nlinarith only [hr0, hr1]
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hsq
  change _ ≤ (b + 3 * r) ^ 2 at hsq
  calc
    _ ≤ (b + 3 * r) ^ 2 := hsq
    _ ≤ 2 * b ^ 2 + 18 * r ^ 2 := by
      nlinarith only [sq_nonneg (b - 3 * r)]
    _ ≤ 2 * b ^ 2 + 18 * r := by linarith only [hr2]
    _ = _ := by dsimp [b, r]; ring

end CausalSmith.Stat.AnnotationRarearmFrontier
