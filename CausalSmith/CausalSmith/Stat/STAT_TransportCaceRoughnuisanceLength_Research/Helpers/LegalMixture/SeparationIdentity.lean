module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.ConditionalMargins

/-! # Exact nonlinear tiled-bump integrals for the lower separation -/

public section

open Set MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- A nonlinear function vanishing at zero acts cellwise on the disjoint tiled bump.  Under [the displayed assumptions and inputs](hyp:cStar,n,sgn,hK,f,hf,x), [the stated conclusion holds](goal). -/
-- @node: tiledPerturbation_comp_eq_sum
lemma tiledPerturbation_comp_eq_sum (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (hK : 0 < lowerCells n)
    (f : ℝ → ℝ) (hf : f 0 = 0) (x : ℝ) :
    f (tiledPerturbation cStar n sgn x) =
      ∑ i : Fin (lowerCells n), if x ∈ cell (lowerCells n) i then
        f (lowerHeight cStar n * sign (sgn i) *
          bump ((lowerCells n : ℝ) * x - i.val)) else 0 := by
  classical
  by_cases hex : ∃ i : Fin (lowerCells n), x ∈ cell (lowerCells n) i
  · obtain ⟨i, hi⟩ := hex
    have hnot (j : Fin (lowerCells n)) (hji : j ≠ i) :
        x ∉ cell (lowerCells n) j := by
      intro hj
      exact hji (cell_mem_unique _ hK j i x hj hi)
    unfold tiledPerturbation
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      simp [hnot j hji]
    · simp
    · intro j _ hji
      simp [hnot j hji]
    · simp
  · have hnot (i : Fin (lowerCells n)) : x ∉ cell (lowerCells n) i :=
      fun hi => hex ⟨i, hi⟩
    simp [tiledPerturbation, hnot, hf]

/-- Integration of an integrable transform reduces to the finite cell sum.  Under [the displayed assumptions and inputs](hyp:cStar,n,sgn,hK,f,hf,hf0), [the stated conclusion holds](goal). -/
-- @node: integral_tiledPerturbation_comp
lemma integral_tiledPerturbation_comp (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (hK : 0 < lowerCells n)
    (f : ℝ → ℝ)
    (hf : ∀ i : Fin (lowerCells n), IntegrableOn (fun x : ℝ =>
      f (lowerHeight cStar n * sign (sgn i) *
        bump ((lowerCells n : ℝ) * x - i.val))) covariateSpace)
    (hf0 : f 0 = 0) :
    (∫ x in covariateSpace, f (tiledPerturbation cStar n sgn x)) =
      ∑ i : Fin (lowerCells n), ∫ x in cell (lowerCells n) i,
        f (lowerHeight cStar n * sign (sgn i) *
          bump ((lowerCells n : ℝ) * x - i.val)) := by
  classical
  have hm (i : Fin (lowerCells n)) : MeasurableSet (cell (lowerCells n) i) := by
    unfold cell
    split_ifs <;> measurability
  have hi (i : Fin (lowerCells n)) : Integrable
      (fun x : ℝ => if x ∈ cell (lowerCells n) i then
        f (lowerHeight cStar n * sign (sgn i) *
          bump ((lowerCells n : ℝ) * x - i.val)) else 0)
      (volume.restrict covariateSpace) := by
    exact (hf i).indicator (hm i)
  simp_rw [tiledPerturbation_comp_eq_sum cStar n sgn hK f hf0]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  change (∫ x in covariateSpace, (cell (lowerCells n) i).indicator (fun y : ℝ =>
    f (lowerHeight cStar n * sign (sgn i) *
      bump ((lowerCells n : ℝ) * y - i.val))) x) = _
  rw [integral_indicator (hm i),
    Measure.restrict_restrict_of_subset (cell_subset_covariateSpace _ hK i)]

/-- The affine substitution on a tile has Jacobian equal to the reciprocal cell count.  Under [the displayed assumptions and inputs](hyp:K,hK,i,f), [the stated conclusion holds](goal). -/
-- @node: integral_comp_affine_cell
lemma integral_comp_affine_cell (K : ℕ) (hK : 0 < K) (i : Fin K)
    (f : ℝ → ℝ) :
    (∫ x in cell K i, f ((K : ℝ) * x - i.val)) =
      (K : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1, f t := by
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have hle : (i.val : ℝ) / K ≤ ((i.val : ℝ) + 1) / K := by
    apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h := intervalIntegral.mul_integral_comp_mul_sub (f := f) (K : ℝ) (i.val : ℝ)
    (a := (i.val : ℝ) / K) (b := ((i.val : ℝ) + 1) / K)
  have hlo : (K : ℝ) * ((i.val : ℝ) / K) - i.val = 0 := by field_simp; ring
  have hhi : (K : ℝ) * (((i.val : ℝ) + 1) / K) - i.val = 1 := by
    field_simp
    ring
  rw [hlo, hhi] at h
  have heq : (∫ x in ((i.val : ℝ) / K)..(((i.val : ℝ) + 1) / K),
      f ((K : ℝ) * x - i.val)) = (K : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1, f t := by
    apply (mul_left_cancel₀ hK0)
    rw [h]
    field_simp
  unfold cell
  split_ifs with hlast
  · have hend : ((i.val : ℝ) + 1) / K = 1 := by
      have : (i.val : ℝ) + 1 = K := by exact_mod_cast hlast
      rw [this]
      simp [hK0]
    conv_lhs => rw [← hend, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle]
    exact heq
  · rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    exact heq

/-- The rational bump powers integrate exactly tile by tile, including their sign factors.  Under [the displayed assumptions and inputs](hyp:cStar,n,sgn,hK,hh,p,hp), [the stated conclusion holds](goal). -/
-- @node: integral_tiledPerturbation_rational_power
lemma integral_tiledPerturbation_rational_power (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (hK : 0 < lowerCells n)
    (hh : lowerHeight cStar n ^ 2 ≤ 1 / 8) (p : ℕ) (hp : 0 < p) :
    (∫ x in covariateSpace, tiledPerturbation cStar n sgn x ^ p /
      (1 / 4 - tiledPerturbation cStar n sgn x ^ 2)) =
      ∑ i : Fin (lowerCells n),
        (lowerHeight cStar n ^ p * sign (sgn i) ^ p) *
          ((lowerCells n : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1,
            bump t ^ p / (1 / 4 - lowerHeight cStar n ^ 2 * bump t ^ 2)) := by
  let h := lowerHeight cStar n
  have hs (b : Bool) : sign b ^ 2 = 1 := by cases b <;> norm_num [sign]
  have hb (t : ℝ) : bump t ^ 2 ≤ 1 := by
    have ht : |bump t| ≤ 1 := by
      simpa [bump] using Real.abs_sin_le_one (2 * Real.pi * t)
    nlinarith [sq_abs (bump t), abs_nonneg (bump t)]
  have hd (t : ℝ) : 0 < 1 / 4 - h ^ 2 * bump t ^ 2 := by
    have := mul_le_mul_of_nonneg_left (hb t) (sq_nonneg h)
    change h ^ 2 ≤ 1 / 8 at hh
    nlinarith
  have hcont : Continuous (fun t : ℝ =>
      bump t ^ p / (1 / 4 - h ^ 2 * bump t ^ 2)) := by
    have hc : Continuous bump := by unfold bump; fun_prop
    exact (hc.pow p).div (continuous_const.sub (continuous_const.mul (hc.pow 2)))
      (fun t => ne_of_gt (hd t))
  have heq (i : Fin (lowerCells n)) (t : ℝ) :
      (h * sign (sgn i) * bump t) ^ p /
        (1 / 4 - (h * sign (sgn i) * bump t) ^ 2) =
      (h ^ p * sign (sgn i) ^ p) *
        (bump t ^ p / (1 / 4 - h ^ 2 * bump t ^ 2)) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, hs, mul_one]
    ring
  have hi (i : Fin (lowerCells n)) : IntegrableOn (fun x : ℝ =>
      (h * sign (sgn i) * bump ((lowerCells n : ℝ) * x - i.val)) ^ p /
        (1 / 4 - (h * sign (sgn i) *
          bump ((lowerCells n : ℝ) * x - i.val)) ^ 2)) covariateSpace := by
    simp_rw [heq]
    have hc : Continuous (fun x : ℝ =>
        (h ^ p * sign (sgn i) ^ p) *
          (bump ((lowerCells n : ℝ) * x - i.val) ^ p /
            (1 / 4 - h ^ 2 * bump ((lowerCells n : ℝ) * x - i.val) ^ 2))) := by
      exact continuous_const.mul (hcont.comp (by fun_prop))
    exact hc.continuousOn.integrableOn_Icc
  rw [integral_tiledPerturbation_comp cStar n sgn hK
    (fun u : ℝ => u ^ p / (1 / 4 - u ^ 2)) hi (by simp [Nat.ne_of_gt hp])]
  dsimp [h] at heq
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [heq]
  rw [integral_const_mul, integral_comp_affine_cell _ hK i
    (fun t : ℝ => bump t ^ p / (1 / 4 - lowerHeight cStar n ^ 2 * bump t ^ 2))]

/-- The odd rational correction has zero integral on every tile.  Under [the displayed assumptions and inputs](hyp:cStar,n,sgn,hK,hh), [the stated conclusion holds](goal). -/
-- @node: tiledPerturbation_odd_ratio_integral_zero
lemma tiledPerturbation_odd_ratio_integral_zero (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (hK : 0 < lowerCells n)
    (hh : lowerHeight cStar n ^ 2 ≤ 1 / 8) :
    (∫ x in covariateSpace, tiledPerturbation cStar n sgn x ^ 3 /
      (1 / 4 - tiledPerturbation cStar n sgn x ^ 2)) = 0 := by
  rw [integral_tiledPerturbation_rational_power cStar n sgn hK hh 3 (by norm_num)]
  rw [bump_odd_ratio_integral_zero]
  simp

/-- The even rational term equals the paper's separation, independently of the signs.  Under [the displayed assumptions and inputs](hyp:cStar,n,sgn,hK,hh), [the stated conclusion holds](goal). -/
-- @node: tiledPerturbation_even_ratio_integral_eq_separation
lemma tiledPerturbation_even_ratio_integral_eq_separation (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (hK : 0 < lowerCells n)
    (hh : lowerHeight cStar n ^ 2 ≤ 1 / 8) :
    (∫ x in covariateSpace, tiledPerturbation cStar n sgn x ^ 2 /
      (1 / 4 - tiledPerturbation cStar n sgn x ^ 2)) = separation cStar n := by
  rw [integral_tiledPerturbation_rational_power cStar n sgn hK hh 2 (by norm_num)]
  have hs (i : Fin (lowerCells n)) : sign (sgn i) ^ 2 = 1 := by
    cases sgn i <;> norm_num [sign]
  simp_rw [hs, mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold separation
  have hK0 : (lowerCells n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  field_simp
  congr 2
  funext t
  ring

/-- The rational powers used in the separation calculation are integrable.  Under [the displayed assumptions and inputs](hyp:cStar,n,sgn,hh,p), [the stated conclusion holds](goal). -/
-- @node: tiledPerturbation_rational_power_integrable
lemma tiledPerturbation_rational_power_integrable (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool)
    (hh : lowerHeight cStar n ^ 2 ≤ 1 / 8) (p : ℕ) :
    IntegrableOn (fun x => tiledPerturbation cStar n sgn x ^ p /
      (1 / 4 - tiledPerturbation cStar n sgn x ^ 2)) covariateSpace := by
  have hu (x : ℝ) := tiledPerturbation_abs_le_abs_lowerHeight cStar n sgn x
  have hd (x : ℝ) : 1 / 8 ≤ 1 / 4 - tiledPerturbation cStar n sgn x ^ 2 := by
    have hs := pow_le_pow_left₀ (abs_nonneg _) (hu x) 2
    simp only [sq_abs] at hs
    linarith
  have hm : Measurable (fun x => tiledPerturbation cStar n sgn x ^ p /
      (1 / 4 - tiledPerturbation cStar n sgn x ^ 2)) := by
    have h := tiledPerturbation_measurable cStar n sgn
    fun_prop
  haveI : IsFiniteMeasure (volume.restrict covariateSpace) := by
    change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1))
    infer_instance
  apply Integrable.of_bound hm.aestronglyMeasurable (8 * |lowerHeight cStar n| ^ p)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_pos (by linarith [hd x] : 0 < 1 / 4 - tiledPerturbation cStar n sgn x ^ 2),
    div_le_iff₀ (by linarith [hd x])]
  have hp := pow_le_pow_left₀ (abs_nonneg _) (hu x) p
  nlinarith [mul_le_mul_of_nonneg_left (hd x)
    (pow_nonneg (abs_nonneg (lowerHeight cStar n)) p)]

/-- The exact transported outcome is minus tau times the separation; the tilted
cubic correction cancels rather than contributing a bias term.  Under [the displayed assumptions and inputs](hyp:a,n,cStar,sgn,hK,ha,hh), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_transportedOutcome_eq_separation
lemma legalIVComponent_transportedOutcome_eq_separation (a : ℝ) (n : ℕ)
    (cStar τ : ℝ) (sgn : Fin (lowerCells n) → Bool)
    (hK : 0 < lowerCells n) (ha : actualStrength a n ≠ 0)
    (hh : lowerHeight cStar n ^ 2 ≤ 1 / 8) :
    transportedForm (legalIVComponent a n cStar τ sgn) true =
      -(τ * separation cStar n) := by
  have hc (x : ℝ) := (legalIVComponent_arm_contrasts a n cStar τ sgn x ha).2
  simp_rw [transportedForm, hc]
  change (∫ x in covariateSpace, (1 + tiledPerturbation cStar n sgn x) *
    (-(tiledPerturbation cStar n sgn x * coupledPerturbation cStar τ n sgn x) /
      (1 / 4 - tiledPerturbation cStar n sgn x ^ 2))) = _
  have heq (x : ℝ) :
      (1 + tiledPerturbation cStar n sgn x) *
        (-(tiledPerturbation cStar n sgn x * coupledPerturbation cStar τ n sgn x) /
          (1 / 4 - tiledPerturbation cStar n sgn x ^ 2)) =
      -τ * (tiledPerturbation cStar n sgn x ^ 2 /
        (1 / 4 - tiledPerturbation cStar n sgn x ^ 2) +
        tiledPerturbation cStar n sgn x ^ 3 /
          (1 / 4 - tiledPerturbation cStar n sgn x ^ 2)) := by
    unfold coupledPerturbation
    ring
  simp_rw [heq]
  rw [integral_const_mul, integral_add
    (tiledPerturbation_rational_power_integrable cStar n sgn hh 2)
    (tiledPerturbation_rational_power_integrable cStar n sgn hh 3),
    tiledPerturbation_even_ratio_integral_eq_separation cStar n sgn hK hh,
    tiledPerturbation_odd_ratio_integral_zero cStar n sgn hK hh]
  ring


/-- The target integral uses exactly the tilted covariate density in the construction. Under [the displayed assumptions and inputs](hyp:a,n,cStar,sgn,hb,hAdm,hn,g,hτ), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_target_integral_eq_density_integral
lemma legalIVComponent_target_integral_eq_density_integral (a : ℝ) (n : ℕ)
    (cStar τ : ℝ) (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1)
    (hn : 0 < n) (g : ℝ → ℝ) :
    (∫ x, g x ∂targetXLaw (legalIVComponent a n cStar τ sgn)) =
      ∫ x in covariateSpace, (1 + tiledPerturbation cStar n sgn x) * g x := by
  have hmap := legalTargetLaw_eq_density a n cStar τ sgn hb hAdm hτ hn
  change targetXLaw (legalIVComponent a n cStar τ sgn) = _ at hmap
  have hm : Measurable (fun x : ℝ =>
      ENNReal.ofReal (1 + tiledPerturbation cStar n sgn x)) := by
    have hu := tiledPerturbation_measurable cStar n sgn
    fun_prop
  rw [hmap, integral_withDensity_eq_integral_toReal_smul hm
    (by filter_upwards [] with x; simp)]
  apply integral_congr_ae
  filter_upwards [] with x
  have hu := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
  have hnonneg : 0 ≤ 1 + tiledPerturbation cStar n sgn x := by
    linarith [hAdm.2.1, neg_abs_le (tiledPerturbation cStar n sgn x)]
  simp [ENNReal.toReal_ofReal hnonneg]

/-- The target conditional margins identify CACE with the exact transported outcome
 divided by the construction's constant complier share. Under [the displayed assumptions and inputs](hyp:a,n,cStar,sgn,hb,hAdm,hn,hD,hY,hτ), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_targetCACE_eq_transportedOutcome
lemma legalIVComponent_targetCACE_eq_transportedOutcome (a : ℝ) (n : ℕ)
    (cStar τ : ℝ) (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1)
    (hn : 0 < n)
    (hD : ConditionalMean (legalIVComponent a n cStar τ sgn) false complier
      (fun _ => actualStrength a n))
    (hY : ConditionalMean (legalIVComponent a n cStar τ sgn) false
      (fun o => (outcome1 o - outcome0 o) * complier o)
      (fun x => -(tiledPerturbation cStar n sgn x *
        coupledPerturbation cStar τ n sgn x) /
        (1 / 4 - tiledPerturbation cStar n sgn x ^ 2))) :
    targetCACE (legalIVComponent a n cStar τ sgn) =
      transportedForm (legalIVComponent a n cStar τ sgn) true / actualStrength a n := by
  let P := legalIVComponent a n cStar τ sgn
  have hshare : targetComplierShare P = actualStrength a n := by
    rw [← integral_complier_eq_targetComplierShare P]
    have h := hD.2 Set.univ MeasurableSet.univ
    simp only [Set.mem_univ, Set.setOf_true, Measure.restrict_univ] at h
    rw [h, ← show targetXLaw P = (populationLaw P false).map covariate from rfl]
    rw [legalIVComponent_target_integral_eq_density_integral a n cStar τ sgn
      hb hAdm hτ hn]
    have hu := tiledPerturbation_integrable_and_integral_zero cStar n sgn hn
    haveI : IsFiniteMeasure (volume.restrict covariateSpace) := by
      change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1))
      infer_instance
    simp_rw [add_mul]
    rw [integral_add (integrable_const _) (hu.1.mul_const _)]
    simp [integral_mul_const, covariateSpace]
    left
    simpa only [covariateSpace] using hu.2
  have hout : (∫ o, (outcome1 o - outcome0 o) * complier o
      ∂populationLaw P false) = transportedForm P true := by
    have h := hY.2 Set.univ MeasurableSet.univ
    simp only [Set.mem_univ, Set.setOf_true, Measure.restrict_univ] at h
    rw [h, ← show targetXLaw P = (populationLaw P false).map covariate from rfl]
    rw [legalIVComponent_target_integral_eq_density_integral a n cStar τ sgn
      hb hAdm hτ hn]
    unfold transportedForm
    have hc (x : ℝ) := (legalIVComponent_arm_contrasts a n cStar τ sgn x
      (ne_of_gt hb.1)).2
    change (∫ x in covariateSpace, (1 + tiledPerturbation cStar n sgn x) * _) =
      ∫ x in covariateSpace, (1 + tiledPerturbation cStar n sgn x) *
        armContrast (legalIVComponent a n cStar τ sgn) true x
    simp_rw [hc]
  change (∫ o, (outcome1 o - outcome0 o) * complier o
    ∂populationLaw P false) / targetComplierShare P = _
  rw [hshare, hout]

-- @node: legal_mixture_margins
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn,hn,ha,hc,hτ), [the stated result about legal mixture margins holds](goal). -/
lemma legal_mixture_margins (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hn : threshold ≤ n) (ha : 0 < a ∧ a ≤ 1 / 4)
    (hc : 0 < cStar ∧ cStar ≤ 1 / 100)
    (hτ : τ ∈ Icc (-1 : ℝ) 1) :
    (∀ s : Bool,
      ConditionalMean (legalIVComponent a n cStar τ sgn) s complier
        (fun _ => actualStrength a n) ∧
      ConditionalMean (legalIVComponent a n cStar τ sgn) s
        (fun o => (outcome1 o - outcome0 o) * complier o)
        (fun x =>
          -(tiledPerturbation cStar n sgn x *
            coupledPerturbation cStar τ n sgn x) /
            (1 / 4 - tiledPerturbation cStar n sgn x ^ 2))) ∧
    firstStage (legalIVComponent a n cStar τ sgn) = actualStrength a n ∧
    targetCACE (legalIVComponent a n cStar τ sgn) =
      -(τ * separation cStar n) / actualStrength a n ∧
    firstStage (mixtureCenter a n) = actualStrength a n ∧
    targetCACE (mixtureCenter a n) = 0 := by
  have hstrength : actualStrength a n ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le ha.1 (le_max_left _ _))
  have hmeans : ∀ s : Bool,
      ConditionalMean (legalIVComponent a n cStar τ sgn) s complier
        (fun _ => actualStrength a n) ∧
      ConditionalMean (legalIVComponent a n cStar τ sgn) s
        (fun o => (outcome1 o - outcome0 o) * complier o)
        (fun x => -(tiledPerturbation cStar n sgn x *
          coupledPerturbation cStar τ n sgn x) /
          (1 / 4 - tiledPerturbation cStar n sgn x ^ 2)) := by
    intro s
    exact legalIVComponent_conditional_complier_margins a n cStar τ sgn
      (actualStrength_bounds a n hn ha)
      (lower_admissible_of_small_amplitude n a cStar hn ha hc) hτ
      (by have : 256 ≤ n := hn; omega) s
  refine ⟨hmeans, ?_, ?_, mixtureCenter_firstStage a n hstrength, ?_⟩
  · have h (x : ℝ) :=
      (legalIVComponent_arm_contrasts a n cStar τ sgn x hstrength).1
    simp_rw [firstStage, transportedForm, h]
    change (∫ x in covariateSpace,
      (1 + tiledPerturbation cStar n sgn x) * actualStrength a n) =
        actualStrength a n
    have hu := tiledPerturbation_integrable_and_integral_zero cStar n sgn (by
      have : 256 ≤ n := hn
      omega)
    haveI : IsFiniteMeasure (volume.restrict covariateSpace) := by
      change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1))
      infer_instance
    simp_rw [add_mul]
    rw [integral_add (integrable_const _) (hu.1.mul_const _)]
    simp [integral_mul_const, covariateSpace]
    left
    simpa only [covariateSpace] using hu.2
  · have hb := actualStrength_bounds a n hn ha
    have hAdm := lower_admissible_of_small_amplitude n a cStar hn ha hc
    have hn0 : 0 < n := by have : 256 ≤ n := hn; omega
    have hK : 0 < lowerCells n := by
      unfold lowerCells
      exact Nat.ceil_pos.mpr (by positivity)
    have hh : lowerHeight cStar n ^ 2 ≤ 1 / 8 := by
      have hheight0 : 0 ≤ lowerHeight cStar n := by
        unfold lowerHeight
        exact mul_nonneg hc.1.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      nlinarith [hAdm.2.1]
    rw [legalIVComponent_targetCACE_eq_transportedOutcome a n cStar τ sgn
      hb hAdm hτ hn0 (hmeans false).1 (hmeans false).2,
      legalIVComponent_transportedOutcome_eq_separation a n cStar τ sgn
        hK hstrength hh]
  · exact mixtureCenter_targetCACE_zero a n (actualStrength_bounds a n hn ha)


end CausalSmith.Stat.TransportCaceRoughnuisanceLength
