module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.ConsistencyFrontier
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerRateSplice
public import Causalean.Stat.Minimax.ChiSquaredFinite

/-! # The finite-alphabet boundary-propensity lower experiment

The last step of the lower-bound roadmap uses a common Bernoulli mean shift.
Uniform covariate labels carry no information about that shift, so this
submodel has the same information as the single occupied cell experiment.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators ENNReal


-- @node: constantDenseObservedLaw_value
/-- The constant dense parameter has exactly the scalar shifted target. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi), the [stated conclusion](goal) holds. -/
lemma constantDenseObservedLaw_value {d : ℕ} (hd : 0 < d) (ε a : ℝ)
    (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2) :
    observedValue (denseObservedLaw hd ε a hε hεhi ha hahi
      (fun _ => 1) (by intro _; norm_num)) = 1 / 2 + a := by
  rw [denseObservedLaw_value]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp [densePriorTarget, densePositivePart, hdR]


-- @node: constantDenseObservedLaw_absolutelyContinuous
/-- The central law has positive mass at every atom, so every shifted law is absolutely continuous with respect to it. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi), the [stated conclusion](goal) holds. -/
lemma constantDenseObservedLaw_absolutelyContinuous {d : ℕ} (hd : 0 < d)
    (ε a : ℝ) (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2) :
    (denseObservedLaw hd ε a hε hεhi ha hahi (fun _ => 1)
      (by intro _; norm_num)).pmf.toMeasure ≪
    (denseObservedLaw hd ε 0 hε hεhi (by norm_num) (by norm_num)
      (fun _ => 1) (by intro _; norm_num)).pmf.toMeasure := by
  classical
  let Q := denseObservedLaw hd ε 0 hε hεhi (by norm_num) (by norm_num)
    (fun _ => 1) (by intro _; norm_num)
  have hpos (o : Obs d) : 0 < Q.pmf.toMeasure.real {o} := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    change 0 < (Q.pmf.toMeasure {o}).toReal
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    change 0 < jointMass Q o.1 o.2.1 o.2.2
    rw [denseObservedLaw_jointMass]
    have he : 0 < 1 - ε := by linarith
    cases o.2.1 <;> simp [denseObservedMass] <;> positivity
  intro s hs
  have hempty : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro o ho
    have hz : Q.pmf.toMeasure {o} = 0 :=
      measure_mono_null (Set.singleton_subset_iff.mpr ho) hs
    have hp := hpos o
    simp [Measure.real_def, hz] at hp
  rw [hempty, measure_empty]


-- @node: discreteLaw_real_singleton
/-- Real singleton masses agree with the observed atom coordinates. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma discreteLaw_real_singleton {d : ℕ} (P : DiscreteLaw d) (o : Obs d) :
    P.pmf.toMeasure.real {o} = jointMass P o.1 o.2.1 o.2.2 := by
  rw [Measure.real_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rfl


-- @node: constantDenseObservedLaw_chiSqDiv
/-- The exact one-observation information is four times the overlap floor and the squared mean shift, independently of the covariate alphabet. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi), the [stated conclusion](goal) holds. -/
lemma constantDenseObservedLaw_chiSqDiv {d : ℕ} (hd : 0 < d)
    (ε a : ℝ) (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2) :
    Causalean.Stat.chiSqDiv
      (denseObservedLaw hd ε a hε hεhi ha hahi (fun _ => 1)
        (by intro _; norm_num)).pmf.toMeasure
      (denseObservedLaw hd ε 0 hε hεhi (by norm_num) (by norm_num)
        (fun _ => 1) (by intro _; norm_num)).pmf.toMeasure = 4 * ε * a ^ 2 := by
  classical
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hεne : ε ≠ 0 := hε.ne'
  have hone : 1 - ε ≠ 0 := by linarith
  have h := Causalean.Stat.finite_one_add_chiSqDiv _ _
    (constantDenseObservedLaw_absolutelyContinuous hd ε a hε hεhi ha hahi)
  have hsum :
      (∑ o : Obs d,
        ((denseObservedLaw hd ε a hε hεhi ha hahi (fun _ => 1)
          (by intro _; norm_num)).pmf.toMeasure.real {o}) ^ 2 /
        (denseObservedLaw hd ε 0 hε hεhi (by norm_num) (by norm_num)
          (fun _ => 1) (by intro _; norm_num)).pmf.toMeasure.real {o}) =
        1 + 4 * ε * a ^ 2 := by
    simp_rw [discreteLaw_real_singleton]
    simp_rw [denseObservedLaw_jointMass]
    rw [Fintype.sum_prod_type]
    have hcell (x : Fin d) :
        (∑ b : Bool × Bool,
          (denseObservedMass ε a (fun _ : Fin d => 1) (x, b)) ^ 2 /
          denseObservedMass ε 0 (fun _ : Fin d => 1) (x, b)) =
          (1 + 4 * ε * a ^ 2) / d := by
      simp [Fintype.sum_prod_type, denseObservedMass]
      field_simp
      <;> ring
    simp_rw [hcell]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  linarith


-- @node: constantDense_twoPoint_sqRisk_lower
/-- Tensorization and a small information budget give a fixed-sample squared-risk testing floor for the legal constant boundary submodel. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi,hinfo), the [stated conclusion](goal) holds. -/
lemma constantDense_twoPoint_sqRisk_lower {n d : ℕ} (hd : 0 < d)
    (ε a : ℝ) (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2)
    (hinfo : (n : ℝ) * ε * a ^ 2 ≤ 1 / 16) (est : Estimator n d) :
    a ^ 2 / 16 ≤ max
      (Causalean.Stat.sqRisk
        (productLaw (denseObservedLaw hd ε a hε hεhi ha hahi
          (fun _ => 1) (by intro _; norm_num)) n) est.1 (1 / 2 + a))
      (Causalean.Stat.sqRisk
        (productLaw (denseObservedLaw hd ε 0 hε hεhi (by norm_num) (by norm_num)
          (fun _ => 1) (by intro _; norm_num)) n) est.1 (1 / 2)) := by
  let P := denseObservedLaw hd ε a hε hεhi ha hahi
    (fun _ => 1) (by intro _; norm_num)
  let Q := denseObservedLaw hd ε 0 hε hεhi (by norm_num) (by norm_num)
    (fun _ => 1) (by intro _; norm_num)
  letI : IsProbabilityMeasure (productLaw P n) := by unfold productLaw; infer_instance
  letI : IsProbabilityMeasure (productLaw Q n) := by unfold productLaw; infer_instance
  have hac : P.pmf.toMeasure ≪ Q.pmf.toMeasure :=
    constantDenseObservedLaw_absolutelyContinuous hd ε a hε hεhi ha hahi
  have hacn : productLaw P n ≪ productLaw Q n :=
    Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous _ _ hac n
  have hchi : Causalean.Stat.chiSqDiv (productLaw P n) (productLaw Q n) ≤ 1 := by
    have ht := Causalean.Stat.one_add_chiSqDiv_pi_iid _ _ hac n
    have hsingle : Causalean.Stat.chiSqDiv P.pmf.toMeasure Q.pmf.toMeasure =
        4 * ε * a ^ 2 := constantDenseObservedLaw_chiSqDiv hd ε a hε hεhi ha hahi
    rw [hsingle] at ht
    have hp : (1 + 4 * ε * a ^ 2) ^ n ≤ Real.exp ((n : ℝ) * (4 * ε * a ^ 2)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity)
        (by simpa only [add_comm] using Real.add_one_le_exp (4 * ε * a ^ 2)) n
    have he : Real.exp ((n : ℝ) * (4 * ε * a ^ 2)) ≤ 4 / 3 := by
      calc
        _ ≤ Real.exp (1 / 4) := Real.exp_le_exp.mpr (by nlinarith)
        _ ≤ 4 / 3 := by
          have h := Real.exp_bound_div_one_sub_of_interval
            (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
          norm_num at h ⊢
          exact h
    change 1 + Causalean.Stat.chiSqDiv (productLaw P n) (productLaw Q n) = _ at ht
    linarith
  have htest := Causalean.Stat.two_point_lower_bound_of_chiSqDiv_le
    (P₀ := productLaw P n) (P₁ := productLaw Q n)
    (θ₀ := 1 / 2 + a) (θ₁ := 1 / 2) (s := a / 2) est.2
    (by rw [show (1 / 2 + a) - (1 / 2 : ℝ) = a by ring, abs_of_nonneg ha]; linarith)
    hacn Integrable.of_finite hchi
  norm_num only [Real.sqrt_one] at htest
  have htest' : (1 / 4 : ℝ) ≤ max
      ((productLaw P n).real {o | a / 2 ≤ |est.1 o - (1 / 2 + a)|})
      ((productLaw Q n).real {o | a / 2 ≤ |est.1 o - 1 / 2|}) := by
    convert htest using 1 <;> norm_num
  have hmark (μ : Measure (Fin n → Obs d)) [IsProbabilityMeasure μ] (θ : ℝ) :
      (a / 2) ^ 2 * μ.real {o | a / 2 ≤ |est.1 o - θ|} ≤
        Causalean.Stat.sqRisk μ est.1 θ := by
    have hset : {o | a / 2 ≤ |est.1 o - θ|} =
        {o | (a / 2) ^ 2 ≤ (est.1 o - θ) ^ 2} := by
      ext o
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;>
        nlinarith [sq_abs (est.1 o - θ), abs_nonneg (est.1 o - θ)]
    rw [hset]
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun o => sq_nonneg (est.1 o - θ))
      Integrable.of_finite _
  have hm := max_le_max (hmark (productLaw P n) (1 / 2 + a))
    (hmark (productLaw Q n) (1 / 2))
  rw [← mul_max_of_nonneg _ _ (sq_nonneg (a / 2))] at hm
  have h := mul_le_mul_of_nonneg_left htest' (sq_nonneg (a / 2))
  have heq : (a / 2) ^ 2 * (1 / 4) = a ^ 2 / 16 := by ring
  rw [heq] at h
  exact h.trans hm


-- @node: finiteAlphabet_parametric_minimaxRisk_lower
/-- The boundary-propensity two-point experiment yields the parametric fallback uniformly over every finite alphabet, with no alphabet cutoff. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hε,hεhi), the [stated conclusion](goal) holds. -/
lemma finiteAlphabet_parametric_minimaxRisk_lower {n d : ℕ} (hn : 1 ≤ n)
    (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) :
    (1 / 1024 : ℝ) * min 1 (1 / ((n : ℝ) * ε)) ≤ minimaxRisk n d ε := by
  have hdpos : 0 < d := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let r := min 1 (1 / ((n : ℝ) * ε))
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  let a := Real.sqrt (r / 64)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hasq : a ^ 2 = r / 64 := Real.sq_sqrt (by positivity)
  have hahi : a ≤ 1 / 2 := by
    have hcap : r ≤ 1 := min_le_left _ _
    nlinarith
  have hinfo : (n : ℝ) * ε * a ^ 2 ≤ 1 / 16 := by
    rw [hasq]
    have h := mul_le_mul_of_nonneg_left (min_le_right 1 (1 / ((n : ℝ) * ε)))
      (show 0 ≤ (n : ℝ) * ε by positivity)
    have heq : (n : ℝ) * ε * (1 / ((n : ℝ) * ε)) = 1 := by field_simp
    rw [heq] at h
    dsimp [r]
    nlinarith
  let P : ModelLaw d ε :=
    ⟨denseObservedLaw hdpos ε a hε hεhi ha hahi (fun _ => 1) (by intro _; norm_num),
      (denseObservedLaw_parameters hdpos ε a hε hεhi ha hahi
        (fun _ => 1) (by intro _; norm_num)).1⟩
  let Q : ModelLaw d ε :=
    ⟨denseObservedLaw hdpos ε 0 hε hεhi (by norm_num) (by norm_num)
      (fun _ => 1) (by intro _; norm_num),
      (denseObservedLaw_parameters hdpos ε 0 hε hεhi (by norm_num) (by norm_num)
        (fun _ => 1) (by intro _; norm_num)).1⟩
  letI : Nonempty (Estimator n d) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  apply Causalean.Stat.le_minimaxValue_of_two_point P Q observedRisk_bddAbove
  intro est
  have h := constantDense_twoPoint_sqRisk_lower hdpos ε a hε hεhi ha hahi hinfo est
  have hP : observedValue P.1 = 1 / 2 + a :=
    constantDenseObservedLaw_value hdpos ε a hε hεhi ha hahi
  have hQ : observedValue Q.1 = 1 / 2 := by
    simpa using constantDenseObservedLaw_value hdpos ε 0 hε hεhi
      (by norm_num) (by norm_num)
  change (1 / 1024 : ℝ) * r ≤ max
    (Causalean.Stat.sqRisk (productLaw P.1 n) est.1 (observedValue P.1))
    (Causalean.Stat.sqRisk (productLaw Q.1 n) est.1 (observedValue Q.1))
  rw [hP, hQ]
  have heq : a ^ 2 / 16 = (1 / 1024 : ℝ) * r := by rw [hasq]; ring
  rwa [heq] at h


-- @node: allAlphabet_minimaxRisk_lower
/-- The parametric fallback covers the finite exceptional set below the large-alphabet cutoff. Together the two experiments give the paper rate for every legal sample size, alphabet and overlap floor. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma allAlphabet_minimaxRisk_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (n d : ℕ) (ε : ℝ),
      1 ≤ n → 2 ≤ d → 0 < ε → ε ≤ 1 / 2 →
      c * rateScale n d ε ≤ minimaxRisk n d ε := by
  obtain ⟨c, D, hc, hD, hlarge⟩ := largeAlphabet_minimaxRisk_lower
  have hDR : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  let cstar := min c (1 / (1024 * (D : ℝ)))
  refine ⟨cstar, lt_min hc (by positivity), ?_⟩
  intro n d ε hn hd hε hεhi
  have hr : 0 ≤ rateScale n d ε := rateScale_nonneg (by omega) hε.le
  by_cases hcut : D ≤ d
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hr).trans
      (hlarge n d ε hn hcut hε hεhi)
  · have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hdpos : (0 : ℝ) < d := by linarith
    have hdD : (d : ℝ) ≤ D := by exact_mod_cast (by omega : d ≤ D)
    have hL : 1 ≤ logAlphabet d := by
      rw [logAlphabet, Real.log_mul (Real.exp_pos _).ne' hdpos.ne', Real.log_exp]
      have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
      linarith
    have hscale : rateScale n d ε ≤
        (D : ℝ) * min 1 (1 / ((n : ℝ) * ε)) := by
      rw [mul_min_of_nonneg _ _ hDR.le]
      apply le_min
      · have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
        exact (min_le_left _ _).trans (by simpa using hD1)
      · calc
          _ ≤ (d : ℝ) / ((n : ℝ) * ε * logAlphabet d) := min_le_right _ _
          _ ≤ (D : ℝ) / ((n : ℝ) * ε) := by
            apply (div_le_div_iff₀ (by positivity) (by positivity)).2
            have h := mul_le_mul_of_nonneg_left hL hDR.le
            have hbound : (d : ℝ) ≤ D * logAlphabet d := hdD.trans (by simpa using h)
            have hm := mul_le_mul_of_nonneg_right hbound
              (show 0 ≤ (n : ℝ) * ε by positivity)
            nlinarith only [hm]
          _ = (D : ℝ) * (1 / ((n : ℝ) * ε)) := by ring
    calc
      cstar * rateScale n d ε ≤ (1 / (1024 * (D : ℝ))) * rateScale n d ε :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hr
      _ ≤ (1 / (1024 * (D : ℝ))) *
          ((D : ℝ) * min 1 (1 / ((n : ℝ) * ε))) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = (1 / 1024 : ℝ) * min 1 (1 / ((n : ℝ) * ε)) := by field_simp
      _ ≤ minimaxRisk n d ε := finiteAlphabet_parametric_minimaxRisk_lower hn hd hε hεhi

end CausalSmith.Stat.OptvalueVanishingoverlapRate
