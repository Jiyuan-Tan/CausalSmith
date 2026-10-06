module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.TargetLaws

/-! # Pairwise sign overlap identities -/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- Given [the supplied inputs](hyp:K,hK,ell), [the stated result about bump sq affine interval holds](goal). -/

lemma bump_sq_affine_interval (K : ℕ) (hK : 0 < K) (ell : Fin K) :
    (∫ x in ((ell.val : ℝ) / K)..(((ell.val : ℝ) + 1) / K),
      bump ((K : ℝ) * x - ell.val) ^ 2) = 1 / (2 * (K : ℝ)) := by
  have h := intervalIntegral.mul_integral_comp_mul_sub
    (f := fun t : ℝ => bump t ^ 2) (K : ℝ) (ell.val : ℝ)
    (a := (ell.val : ℝ) / K) (b := ((ell.val : ℝ) + 1) / K)
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  have hlo : (K : ℝ) * ((ell.val : ℝ) / K) - ell.val = 0 := by
    field_simp
    ring
  have hhi : (K : ℝ) * (((ell.val : ℝ) + 1) / K) - ell.val = 1 := by
    field_simp
    ring
  rw [hlo, hhi, bump_sq_integral] at h
  apply (mul_left_cancel₀ hK0)
  rw [h]
  field_simp
/-- Given [the supplied inputs](hyp:K,hK,ell), [the stated result about bump sq cell integral holds](goal). -/

lemma bump_sq_cell_integral (K : ℕ) (hK : 0 < K) (ell : Fin K) :
    (∫ x in cell K ell, bump ((K : ℝ) * x - ell.val) ^ 2) =
      1 / (2 * (K : ℝ)) := by
  have hinter := bump_sq_affine_interval K hK ell
  have hle : (ell.val : ℝ) / K ≤ ((ell.val : ℝ) + 1) / K := by
    apply div_le_div_of_nonneg_right (by linarith) (by positivity : (0 : ℝ) ≤ K)
  unfold cell
  split_ifs with hlast
  · have hend : ((ell.val : ℝ) + 1) / K = 1 := by
      have hlast' : (ell.val : ℝ) + 1 = K := by exact_mod_cast hlast
      rw [hlast']
      simp [Nat.ne_of_gt hK]
    calc
      (∫ x in Icc ((ell.val : ℝ) / K) 1,
          bump ((K : ℝ) * x - ell.val) ^ 2) =
          ∫ x in Ioc ((ell.val : ℝ) / K) 1,
            bump ((K : ℝ) * x - ell.val) ^ 2 := integral_Icc_eq_integral_Ioc
      _ = ∫ x in ((ell.val : ℝ) / K)..1,
            bump ((K : ℝ) * x - ell.val) ^ 2 := by
          rw [intervalIntegral.integral_of_le]
          simpa [hend] using hle
      _ = ∫ x in ((ell.val : ℝ) / K)..(((ell.val : ℝ) + 1) / K),
            bump ((K : ℝ) * x - ell.val) ^ 2 := by rw [hend]
      _ = 1 / (2 * (K : ℝ)) := hinter
  · calc
      (∫ x in Ico ((ell.val : ℝ) / K) (((ell.val : ℝ) + 1) / K),
          bump ((K : ℝ) * x - ell.val) ^ 2) =
          ∫ x in Ioc ((ell.val : ℝ) / K) (((ell.val : ℝ) + 1) / K),
            bump ((K : ℝ) * x - ell.val) ^ 2 := integral_Ico_eq_integral_Ioc
      _ = ∫ x in ((ell.val : ℝ) / K)..(((ell.val : ℝ) + 1) / K),
            bump ((K : ℝ) * x - ell.val) ^ 2 := by
          rw [intervalIntegral.integral_of_le hle]
      _ = 1 / (2 * (K : ℝ)) := hinter
/-- [The tiled term object](goal) is defined from [the supplied inputs](hyp:cStar,n,s,ell,x). -/

noncomputable def tiledTerm (cStar : ℝ) (n : ℕ)
    (s : Fin (lowerCells n) → Bool) (ell : Fin (lowerCells n)) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ cell (lowerCells n) ell then
      lowerHeight cStar n * sign (s ell) *
        bump ((lowerCells n : ℝ) * x - ell.val)
    else 0
/-- Given [the supplied inputs](hyp:cStar,n,s), [the stated result about tiled perturbation eq sum tiled term holds](goal). -/

lemma tiledPerturbation_eq_sum_tiledTerm (cStar : ℝ) (n : ℕ)
    (s : Fin (lowerCells n) → Bool) :
    tiledPerturbation cStar n s = fun x => ∑ ell, tiledTerm cStar n s ell x := by
  funext x
  rfl
/-- Given [the supplied inputs](hyp:cStar,n,s,t,i,j,hK,hij,x), [the stated result about tiled term mul eq zero of ne holds](goal). -/

lemma tiledTerm_mul_eq_zero_of_ne (cStar : ℝ) (n : ℕ)
    (s t : Fin (lowerCells n) → Bool) (i j : Fin (lowerCells n))
    (hK : 0 < lowerCells n) (hij : i ≠ j) (x : ℝ) :
    tiledTerm cStar n s i x * tiledTerm cStar n t j x = 0 := by
  classical
  unfold tiledTerm
  by_cases hi : x ∈ cell (lowerCells n) i
  · have hj : x ∉ cell (lowerCells n) j := by
      intro hxj
      exact hij (cell_mem_unique _ hK i j x hi hxj)
    simp [hi, hj]
  · simp [hi]
/-- Given [the supplied inputs](hyp:cStar,n,s,t,i,j), [the stated result about tiled term product integrable holds](goal). -/

lemma tiledTerm_product_integrable (cStar : ℝ) (n : ℕ)
    (s t : Fin (lowerCells n) → Bool) (i j : Fin (lowerCells n)) :
    Integrable (fun x => tiledTerm cStar n s i x * tiledTerm cStar n t j x)
      (volume.restrict covariateSpace) := by
  letI : IsFiniteMeasure (volume.restrict covariateSpace) := by
    change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1))
    infer_instance
  have hcell (ell : Fin (lowerCells n)) : MeasurableSet (cell (lowerCells n) ell) := by
    unfold cell
    split_ifs <;> measurability
  have hm (r : Fin (lowerCells n) → Bool) (ell : Fin (lowerCells n)) :
      Measurable (tiledTerm cStar n r ell) := by
    unfold tiledTerm
    apply Measurable.ite (hcell ell)
    · unfold bump
      fun_prop
    · exact measurable_const
  have hb (r : Fin (lowerCells n) → Bool) (ell : Fin (lowerCells n)) (x : ℝ) :
      |tiledTerm cStar n r ell x| ≤ |lowerHeight cStar n| := by
    unfold tiledTerm
    split_ifs
    · rw [abs_mul, abs_mul]
      have hs : |sign (r ell)| = 1 := by cases r ell <;> simp [sign]
      have hu : |bump ((lowerCells n : ℝ) * x - ell.val)| ≤ 1 := by
        simpa [bump] using Real.abs_sin_le_one
          (2 * Real.pi * ((lowerCells n : ℝ) * x - ell.val))
      rw [hs, mul_one]
      exact mul_le_of_le_one_right (abs_nonneg _) hu
    · simp
  apply Integrable.of_bound ((hm s i).mul (hm t j)).aestronglyMeasurable
    (|lowerHeight cStar n| ^ 2)
  filter_upwards [] with x
  change |tiledTerm cStar n s i x * tiledTerm cStar n t j x| ≤ _
  rw [abs_mul]
  nlinarith [hb s i x, hb t j x, abs_nonneg (tiledTerm cStar n s i x),
    abs_nonneg (tiledTerm cStar n t j x), sq_nonneg (|lowerHeight cStar n|)]
/-- Given [the supplied inputs](hyp:cStar,n,s,t,hK,i,j), [the stated result about tiled term pair integral holds](goal). -/

lemma tiledTerm_pair_integral (cStar : ℝ) (n : ℕ)
    (s t : Fin (lowerCells n) → Bool) (hK : 0 < lowerCells n)
    (i j : Fin (lowerCells n)) :
    (∫ x in covariateSpace,
      tiledTerm cStar n s i x * tiledTerm cStar n t j x) =
      if i = j then
        lowerHeight cStar n ^ 2 * sign (s i) * sign (t i) /
          (2 * (lowerCells n : ℝ))
      else 0 := by
  classical
  split_ifs with hij
  · subst j
    have hcell : MeasurableSet (cell (lowerCells n) i) := by
      unfold cell
      split_ifs <;> measurability
    have hfun : (fun x => tiledTerm cStar n s i x * tiledTerm cStar n t i x) =
        (cell (lowerCells n) i).indicator (fun x =>
          lowerHeight cStar n ^ 2 * sign (s i) * sign (t i) *
            bump ((lowerCells n : ℝ) * x - i.val) ^ 2) := by
      funext x
      unfold tiledTerm
      by_cases hx : x ∈ cell (lowerCells n) i <;> simp [hx, Set.indicator] <;> ring
    rw [hfun, integral_indicator hcell]
    rw [Measure.restrict_restrict_of_subset (cell_subset_covariateSpace _ hK i)]
    rw [integral_const_mul, bump_sq_cell_integral _ hK]
    ring
  · have hzero : (fun x => tiledTerm cStar n s i x * tiledTerm cStar n t j x) = 0 := by
      funext x
      exact tiledTerm_mul_eq_zero_of_ne cStar n s t i j hK hij x
    rw [hzero]
    simp
/-- Given [the supplied inputs](hyp:cStar,n,s,t,hn), [the stated result about tiled perturbation pair integral holds](goal). -/

lemma tiledPerturbation_pair_integral (cStar : ℝ) (n : ℕ)
    (s t : Fin (lowerCells n) → Bool) (hn : 0 < n) :
    (∫ x in covariateSpace,
      tiledPerturbation cStar n s x * tiledPerturbation cStar n t x) =
      lowerHeight cStar n ^ 2 / (2 * (lowerCells n : ℝ)) *
        Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign s t := by
  classical
  have hK : 0 < lowerCells n := by
    unfold lowerCells
    exact Nat.ceil_pos.mpr (by positivity)
  rw [tiledPerturbation_eq_sum_tiledTerm,
    tiledPerturbation_eq_sum_tiledTerm]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      tiledTerm_product_integrable cStar n s t i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ =>
    tiledTerm_product_integrable cStar n s t _ j)]
  simp_rw [tiledTerm_pair_integral cStar n s t hK]
  have hdiag (i : Fin (lowerCells n)) :
      (∑ j : Fin (lowerCells n), if i = j then
          lowerHeight cStar n ^ 2 * sign (s i) * sign (t i) /
            (2 * (lowerCells n : ℝ)) else 0) =
        lowerHeight cStar n ^ 2 * sign (s i) * sign (t i) /
          (2 * (lowerCells n : ℝ)) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  simp_rw [hdiag]
  unfold Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [sign]
  ring
/-- Given [the supplied inputs](hyp:cStar,n,s,t,hn), [the stated result about target likelihood pair integrable holds](goal). -/

lemma targetLikelihood_pair_integrable (cStar : ℝ) (n : ℕ)
    (s t : Fin (lowerCells n) → Bool) (hn : 0 < n) :
    Integrable (fun x =>
      (1 + tiledPerturbation cStar n s x) *
        (1 + tiledPerturbation cStar n t x))
      (volume.restrict covariateSpace) := by
  letI : IsFiniteMeasure (volume.restrict covariateSpace) := by
    change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1))
    infer_instance
  have hm (r : Fin (lowerCells n) → Bool) : Measurable
      (fun x => 1 + tiledPerturbation cStar n r x) :=
    measurable_const.add (tiledPerturbation_measurable cStar n r)
  have hb (r : Fin (lowerCells n) → Bool) (x : ℝ) :
      |1 + tiledPerturbation cStar n r x| ≤
        1 + |lowerHeight cStar n| := by
    calc
      |1 + tiledPerturbation cStar n r x| ≤
          1 + |tiledPerturbation cStar n r x| := by
            simpa using abs_add_le (1 : ℝ)
              (tiledPerturbation cStar n r x)
      _ ≤ 1 + |lowerHeight cStar n| :=
        by
          simpa using add_le_add_right
            (tiledPerturbation_abs_le_abs_lowerHeight cStar n r x) 1
  apply Integrable.of_bound ((hm s).mul (hm t)).aestronglyMeasurable
    ((1 + |lowerHeight cStar n|) ^ 2)
  filter_upwards [] with x
  change |(1 + tiledPerturbation cStar n s x) *
    (1 + tiledPerturbation cStar n t x)| ≤ _
  rw [abs_mul]
  nlinarith [hb s x, hb t x,
    abs_nonneg (1 + tiledPerturbation cStar n s x),
    abs_nonneg (1 + tiledPerturbation cStar n t x),
    sq_nonneg (1 + |lowerHeight cStar n|)]
/-- Given [the supplied inputs](hyp:cStar,n,s,t), [the stated result about tiled perturbation product integrable holds](goal). -/

lemma tiledPerturbation_product_integrable (cStar : ℝ) (n : ℕ)
    (s t : Fin (lowerCells n) → Bool) :
    Integrable (fun x => tiledPerturbation cStar n s x *
      tiledPerturbation cStar n t x) (volume.restrict covariateSpace) := by
  rw [tiledPerturbation_eq_sum_tiledTerm,
    tiledPerturbation_eq_sum_tiledTerm]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      tiledTerm_product_integrable cStar n s t i j))
/-- Given [the supplied inputs](hyp:cStar,n,s,t,hn), [the stated result about target likelihood pair integral holds](goal). -/

lemma targetLikelihood_pair_integral (cStar : ℝ) (n : ℕ)
    (s t : Fin (lowerCells n) → Bool) (hn : 0 < n) :
    (∫ x in covariateSpace,
      (1 + tiledPerturbation cStar n s x) *
        (1 + tiledPerturbation cStar n t x)) =
      1 + (lowerHeight cStar n ^ 2 / 2) *
        Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign s t /
          (lowerCells n : ℝ) := by
  letI : IsFiniteMeasure (volume.restrict covariateSpace) := by
    change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1))
    infer_instance
  have hs := tiledPerturbation_integrable_and_integral_zero cStar n s hn
  have ht := tiledPerturbation_integrable_and_integral_zero cStar n t hn
  have hp := tiledPerturbation_pair_integral cStar n s t hn
  rw [show (fun x =>
      (1 + tiledPerturbation cStar n s x) *
        (1 + tiledPerturbation cStar n t x)) =
      fun x => 1 + tiledPerturbation cStar n s x +
        tiledPerturbation cStar n t x +
          tiledPerturbation cStar n s x * tiledPerturbation cStar n t x by
      funext x; ring]
  change (∫ x in covariateSpace,
    ((1 + tiledPerturbation cStar n s x) +
      tiledPerturbation cStar n t x) +
      tiledPerturbation cStar n s x * tiledPerturbation cStar n t x) = _
  calc
    _ = (∫ x in covariateSpace,
          (1 + tiledPerturbation cStar n s x) +
            tiledPerturbation cStar n t x) +
        ∫ x in covariateSpace,
          tiledPerturbation cStar n s x *
            tiledPerturbation cStar n t x := by
        exact integral_add (((integrable_const 1).add hs.1).add ht.1)
          (tiledPerturbation_product_integrable cStar n s t)
    _ = ((∫ x in covariateSpace,
            1 + tiledPerturbation cStar n s x) +
          ∫ x in covariateSpace, tiledPerturbation cStar n t x) +
        ∫ x in covariateSpace,
          tiledPerturbation cStar n s x *
            tiledPerturbation cStar n t x := by
        congr 1
        exact integral_add ((integrable_const 1).add hs.1) ht.1
    _ = (((∫ _x in covariateSpace, (1 : ℝ)) +
            ∫ x in covariateSpace, tiledPerturbation cStar n s x) +
          ∫ x in covariateSpace, tiledPerturbation cStar n t x) +
        ∫ x in covariateSpace,
          tiledPerturbation cStar n s x *
            tiledPerturbation cStar n t x := by
        congr 2
        exact integral_add (integrable_const 1) hs.1
    _ = _ := by
      rw [hs.2, ht.2, hp]
      simp [covariateSpace]
      ring

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
