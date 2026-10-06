module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.AggregateMSE
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.RateAbsorption

/-!
Overlap bounds for canonical inverse-count variances and the completed canonical
hybrid arm rate. The transfer to an arbitrary independent count family is separate.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- [Under the stated inputs and conditions](hyp:hu,ht,hq,hqs,hv,heps,hov,u,t,q,s,v,eps), The canonical product counts satisfy the inverse-count cell variance envelope,
including zero success intensity and null cells.  This gives [the stated result](goal).-/
-- @node: hybrid_canonical_inverse_variance
lemma hybrid_canonical_inverse_variance (u t q s v eps : Real)
    (hu : 0 < u) (ht : 0 < t) (hq : 0 ≤ q) (hqs : q ≤ s) (hv : 0 ≤ v)
    (heps : 0 < eps) (hov : eps * (s + v) ≤ s) :
    variance (inverseCellBranch u) (cellPoissonLaw u t q s v) ≤
      (2 + 4 * (2 ^ 16 : Real)) * (s + v) * (1 / (u * eps) + 1 / (t * eps)) := by
  let nu := (poissonMeasure (Real.toNNReal (t * s))).prod
    (poissonMeasure (Real.toNNReal (t * v)))
  let W : Nat × Nat → Real := fun z => 1 + (z.2 : Real) / ((z.1 : Real) + 1)
  let : IsProbabilityMeasure (cellPoissonLaw u t q s v) := by
    dsimp [cellPoissonLaw]; infer_instance
  have hs : 0 ≤ s := hq.trans hqs
  obtain ⟨hw, hws, hwv⟩ := inverse_count_weight_moments nu Prod.fst Prod.snd
    (Real.toNNReal (t * s)) (Real.toNNReal (t * v)) (by fun_prop) (by fun_prop)
    (by simp [nu]) (by simp [nu])
    ((indepFun_prod (μ := poissonMeasure (Real.toNNReal (t * s)))
      (ν := poissonMeasure (Real.toNNReal (t * v))) measurable_id measurable_id).symm)
  have hz := Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two
    (Real.toNNReal (u * q))
  have hzm := Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment
    (Real.toNNReal (u * q))
  have hzs := Causalean.Mathlib.Probability.Poisson.PairSecondMoment.poisson_count_second_moment
    (Real.toNNReal (u * q))
  simp only [Real.coe_toNNReal _ (mul_nonneg hu.le hq)] at hzm hzs
  have hm : (∫ z, inverseCellBranch u z ∂cellPoissonLaw u t q s v) =
      q * (∫ z, W z ∂nu) := by
    change (∫ z : Nat × (Nat × Nat), (z.1 : Real) / u * W z.2 ∂
      (poissonMeasure (Real.toNNReal (u * q))).prod nu) = _
    rw [integral_prod_mul (fun k : Nat => (k : Real) / u) W, integral_div, hzm, mul_div_cancel_left₀ q hu.ne']
  have hsq : (∫ z, inverseCellBranch u z ^ 2 ∂cellPoissonLaw u t q s v) =
      (q / u + q ^ 2) * (∫ z, W z ^ 2 ∂nu) := by
    change (∫ z : Nat × (Nat × Nat), ((z.1 : Real) / u * W z.2) ^ 2 ∂
      (poissonMeasure (Real.toNNReal (u * q))).prod nu) = _
    simp only [mul_pow, div_pow]
    rw [integral_prod_mul (fun k : Nat => (k : Real) ^ 2 / u ^ 2)
      (fun z : Nat × Nat => W z ^ 2), integral_div, hzs]
    congr 1
    field_simp
    ring
  have hid : variance (inverseCellBranch u) (cellPoissonLaw u t q s v) =
      q / u * (∫ z, W z ^ 2 ∂nu) + q ^ 2 * variance W nu := by
    rw [variance_eq_sub (hybrid_cell_branches_memLp 0 1 u t q s v).2]
    simp only [Pi.pow_apply]
    rw [hm, hsq, variance_eq_sub hw]
    simp only [Pi.pow_apply]
    ring
  have henv := inverse_count_cell_variance_envelope s v q u t eps (2 ^ 16)
    hs hv hq hqs hu ht heps (by positivity) hov
  rw [hid]
  apply le_trans _ henv
  have h1 := mul_le_mul_of_nonneg_left hws (show 0 ≤ q / u by positivity)
  have h2 := mul_le_mul_of_nonneg_left hwv (sq_nonneg q)
  simp only [Real.coe_toNNReal _ (mul_nonneg ht.le hs),
    Real.coe_toNNReal _ (mul_nonneg ht.le hv)] at h1 h2
  simpa only [W, mul_assoc] using add_le_add h1 h2

/-- [Under the stated inputs and conditions](hyp:d,hu,ht,heps,hcell,hmass,u,t,eps,s,v,mu), Summing canonical inverse-count variances uses total mass at most one and
therefore has no cell-count factor.  This gives [the stated result](goal).-/
-- @node: hybrid_canonical_inverse_variance_sum
lemma hybrid_canonical_inverse_variance_sum {d : Nat} (u t eps : Real)
    (s v mu : Fin d → Real) (hu : 0 < u) (ht : 0 < t) (heps : 0 < eps)
    (hcell : ∀ j, 0 ≤ s j ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1 ∧ eps * (s j + v j) ≤ s j)
    (hmass : (∑ j : Fin d, (s j + v j)) ≤ 1) :
    (∑ j, variance (inverseCellBranch u) (cellPoissonLaw u t (s j * mu j) (s j) (v j))) ≤
      (2 + 4 * (2 ^ 16 : Real)) * (1 / (u * eps) + 1 / (t * eps)) := by
  calc
    _ ≤ ∑ j, (2 + 4 * (2 ^ 16 : Real)) * (s j + v j) *
        (1 / (u * eps) + 1 / (t * eps)) := by
      apply Finset.sum_le_sum
      intro j _
      obtain ⟨hs, hv, hm, hov⟩ := hcell j
      exact hybrid_canonical_inverse_variance u t (s j * mu j) (s j) (v j) eps hu ht
        (mul_nonneg hs hm.1) (mul_le_of_le_one_right hs hm.2) hv heps hov
    _ = (2 + 4 * (2 ^ 16 : Real)) * (∑ j : Fin d, (s j + v j)) *
        (1 / (u * eps) + 1 / (t * eps)) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hmass
        (show 0 ≤ (2 + 4 * (2 ^ 16 : Real)) * (1 / (u * eps) + 1 / (t * eps)) by positivity)
      convert hh using 1 <;> first | rfl | ring

/-- Under the stated inputs and conditions, The canonical independent three-pool statistic has the full universal arm
rate, assembled from its actual MSE envelope and inverse-count variance bound.
Null cells and boundary outcome means are included.  This gives [the stated result](goal). -/
-- @node: hybrid_canonical_arm_rate
lemma hybrid_canonical_arm_rate :
    ∃ C : Real, 0 < C ∧ ∀ (S N eps u tp t : Real),
      Real.exp 4096 ≤ S → 0 < eps → eps ≤ 1 → S ≤ N * eps →
      S / 32 ≤ u * eps → N / 64 ≤ tp → N / 64 ≤ t → 1 / 3 ≤ t / tp →
      ∀ (d : Nat) (s v mu : Fin d → Real), 1 ≤ d →
      (∀ j, 0 ≤ s j ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1 ∧ eps * (s j + v j) ≤ s j) →
      (∑ j : Fin d, (s j + v j)) ≤ 1 →
      let L := Nat.floor (Real.log S / 1024)
      let B : Real := (2 : Real) ^ 20 * L / min tp t
      let k0 := Nat.floor (tp * B / 4)
      (∫ z : Fin d → Nat × (Nat × Nat × Nat),
        ((∑ j, hybridCellValue L B k0 u t (z j).2.1 (z j).1
          (z j).2.2.1 (z j).2.2.2) - ∑ j, (s j + v j) * mu j) ^ 2 ∂
        Measure.pi (fun j => (poissonMeasure (Real.toNNReal (tp * s j))).prod
          (cellPoissonLaw u t (s j * mu j) (s j) (v j)))) ≤
        C * (1 / S + ((d : Real) / (N * eps * L)) ^ 2) := by
  obtain ⟨CP, CH, hCP, hCH, hmse⟩ := hybrid_canonical_mse_envelope
  obtain ⟨C, hC, hrate⟩ := hybrid_canonical_envelope_rate
    (2 + 4 * (2 ^ 16 : Real)) CP CH (by positivity) hCP hCH
  refine ⟨C, hC, ?_⟩
  intro S N eps u tp t hS heps heps1 hNS hu htp ht hratio d s v mu hd hcell hmass
  dsimp only
  let L := Nat.floor (Real.log S / 1024)
  let B : Real := (2 : Real) ^ 20 * L / min tp t
  let light := Finset.univ.filter (fun j => s j ≤ B)
  let M := light.sum (fun j => s j + v j)
  have hSp : 0 < S := (Real.exp_pos _).trans_le hS
  have hN : 0 < N := by nlinarith
  have huP : 0 < u := by nlinarith
  have htP : 0 < t := (show 0 < N / 64 by positivity).trans_le ht
  have htpP : 0 < tp := (show 0 < N / 64 by positivity).trans_le htp
  have hLp : 0 < (L : Real) := by
    exact_mod_cast (show 0 < L from by have := (hybrid_degree_calibration S hS).1; omega)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm : 0 ≤ M := Finset.sum_nonneg (fun j _ => add_nonneg (hcell j).1 (hcell j).2.1)
  have hmassLight : M ≤ 1 := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_) hmass
    intro j _ _
    exact add_nonneg (hcell j).1 (hcell j).2.1
  have hmassB : M ≤ (d : Real) * B / eps := by
    have hh := (light_cell_mass_bound light s v B eps heps
      (fun j hj => ⟨(hcell j).2.2.2, (Finset.mem_filter.mp hj).2⟩) hmassLight).trans
      (min_le_right _ _)
    apply hh.trans
    apply div_le_div_of_nonneg_right _ heps.le
    apply mul_le_mul_of_nonneg_right _ hB
    exact_mod_cast (show light.card ≤ d from
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp))
  have hc : (light.card : Real) ≤ d := by
    exact_mod_cast (show light.card ≤ d from
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp))
  have hi := hybrid_canonical_inverse_variance_sum u t eps s v mu huP htP heps hcell hmass
  have henv := hmse S u tp t eps hS huP htpP htP heps heps1 hratio d s v mu hcell hmass
  have hr := hrate S N d eps u tp t M light.card
    (∑ j, variance (inverseCellBranch u) (cellPoissonLaw u t (s j * mu j) (s j) (v j)))
    hS (by exact_mod_cast hd) heps heps1 hNS hu htp ht hm hmassB (by positivity) hc hi
  exact henv.trans hr

end CausalSmith.Stat.AnnotationRarearmFrontier
