module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogCellIdentification
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogQuantileIntegrals

/-! Concrete sharp endpoint identities for the three-score score-log laws. -/

@[expose] public section

namespace CausalSmith.PartialID.UnlinkedPropensityAte

open MeasureTheory ProbabilityTheory Set

noncomputable section

private lemma scoreLogReleasedCellLaw_control_mass {J : ℕ}
    (r : LabelSpace J) (q t c : ℝ)
    (hc0 : 0 ≤ c) (hs0 : 0 ≤ t / q) (hs1 : t / q ≤ 1) :
    (scoreLogReleasedCellLaw r q t c).real
        {z | z.1 = r ∧ z.2.1 = false} = c := by
  letI := trialOutcomeLaw_isProbabilityMeasure (t / q) hs0 hs1
  unfold scoreLogReleasedCellLaw
  rw [Measure.real_def, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, Measure.map_apply (by fun_prop)]
  · simp [hc0, trialZeroOutcome]
  · exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)

private lemma scoreLogReleasedCellLaw_control_mass_all {J : ℕ}
    (r r' : LabelSpace J) (q t c : ℝ)
    (hc0 : 0 ≤ c) (hs0 : 0 ≤ t / q) (hs1 : t / q ≤ 1) :
    (scoreLogReleasedCellLaw r q t c).real
        {z | z.1 = r' ∧ z.2.1 = false} = if r' = r then c else 0 := by
  classical
  by_cases hr : r' = r
  · subst r'
    rw [if_pos rfl, scoreLogReleasedCellLaw_control_mass r q t c hc0 hs0 hs1]
  · rw [if_neg hr]
    letI := trialOutcomeLaw_isProbabilityMeasure (t / q) hs0 hs1
    unfold scoreLogReleasedCellLaw
    rw [Measure.real_def, Measure.add_apply, Measure.smul_apply,
      Measure.smul_apply, Measure.map_apply (by fun_prop)]
    · simp [Ne.symm hr, trialZeroOutcome]
    · exact (measurableSet_eq_fun measurable_fst measurable_const).inter
        (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)

private lemma scoreLogReleasedCellLaw_armCellOutcomeLaw_false {J : ℕ}
    (r : LabelSpace J) (q t c : ℝ)
    (hq0 : 0 ≤ q) (hc : 0 < c) (hs0 : 0 ≤ t / q) (hs1 : t / q ≤ 1)
    (hsum : q + c = 1) :
    let Prel := scoreLogReleasedCellLaw r q t c
    let hPrel : IsProbabilityMeasure Prel :=
      scoreLogReleasedCellLaw_isProbabilityMeasure r q t c hq0 hc.le hs0 hs1 hsum
    armCellOutcomeLaw Prel hPrel false r
        (by simpa [Prel, scoreLogReleasedCellLaw_control_mass r q t c hc.le hs0 hs1]
          using hc) =
      Measure.dirac 0 := by
  dsimp only
  letI : IsProbabilityMeasure (trialOutcomeLaw (t / q)) :=
    trialOutcomeLaw_isProbabilityMeasure (t / q) hs0 hs1
  letI : IsProbabilityMeasure (scoreLogReleasedCellLaw r q t c) :=
    scoreLogReleasedCellLaw_isProbabilityMeasure r q t c hq0 hc.le hs0 hs1 hsum
  apply Measure.ext fun B hB => ?_
  rw [armCellOutcomeLaw_apply]
  unfold scoreLogReleasedCellLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (by fun_prop)]
  · rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.map_apply (by fun_prop)]
    · simp only [Measure.dirac_apply, smul_eq_mul]
      simp [trialZeroOutcome]
      have hcE : ENNReal.ofReal c ≠ 0 := by positivity
      have hcT : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
      rw [← mul_assoc, ENNReal.inv_mul_cancel hcE hcT, one_mul]
      simp [Set.indicator]
      by_cases h0 : (0 : ℝ) ∈ B <;> simp [h0]
    · exact (measurableSet_eq_fun measurable_fst measurable_const).inter
        ((measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).inter
          ((by fun_prop : Measurable fun z : Observation J => (z.2.2 : ℝ)) hB))
  · exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
  · exact hB

private lemma quantile_dirac_zero_product
    (W : Measure ℝ) (φ : ℝ → ℝ) :
    (∫ u in (0 : ℝ)..1,
      Causalean.Stat.quantile (Measure.dirac 0) u *
        Causalean.Stat.quantile W (φ u)) = 0 := by
  calc
    _ = ∫ _u : ℝ in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro u hu
      change Causalean.Stat.quantile (Measure.dirac 0) u *
        Causalean.Stat.quantile W (φ u) = 0
      rw [quantile_dirac_interior 0 u hu.1 hu.2]
      simp
    _ = 0 := by simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,r,q,t,c,hrel,hq0,hc,hs0,hs1,hsum), this result [establishes the stated mathematical conclusion](goal). -/
lemma muLower_muUpper_false_eq_zero_of_scoreLogReleasedCellLaw
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J))
    (hMass : CompatibleCellMasses H g Prel)
    (r : LabelSpace J) (q t c : ℝ)
    (hrel : Prel = scoreLogReleasedCellLaw r q t c)
    (hq0 : 0 ≤ q) (hc : 0 < c) (hs0 : 0 ≤ t / q) (hs1 : t / q ≤ 1)
    (hsum : q + c = 1) :
    muLower H g Prel hMass false = 0 ∧ muUpper H g Prel hMass false = 0 := by
  have hmass (r' : LabelSpace J) :
      armCellMass H g false r' = if r' = r then c else 0 := by
    rw [← hMass.2.2.2 false r', hrel]
    exact scoreLogReleasedCellLaw_control_mass_all r r' q t c hc.le hs0 hs1
  have hout :
      armCellOutcomeLaw Prel hMass.2.1 false r
          (by rw [hMass.2.2.2 false r, hmass r, if_pos rfl]; exact hc) =
        Measure.dirac 0 := by
    unfold armCellOutcomeLaw
    rw [hrel]
    have hout' := scoreLogReleasedCellLaw_armCellOutcomeLaw_false
      r q t c hq0 hc hs0 hs1 hsum
    unfold armCellOutcomeLaw at hout'
    exact hout'
  constructor
  · unfold muLower
    rw [Finset.sum_eq_single r]
    · split_ifs with hpos
      · rw [hmass r, if_pos rfl, hout,
          quantile_dirac_zero_product _ (fun u => 1 - u), mul_zero]
      · exfalso
        apply hpos
        rw [hmass r, if_pos rfl]
        exact hc
    · intro r' _ hr'
      split_ifs with hpos
      · rw [hmass r', if_neg hr'] at hpos
        exact (lt_irrefl 0 hpos).elim
      · rfl
    · simp
  · unfold muUpper
    rw [Finset.sum_eq_single r]
    · split_ifs with hpos
      · rw [hmass r, if_pos rfl, hout,
          quantile_dirac_zero_product _ (fun u => u), mul_zero]
      · exfalso
        apply hpos
        rw [hmass r, if_pos rfl]
        exact hc
    · intro r' _ hr'
      split_ifs with hpos
      · rw [hmass r', if_neg hr'] at hpos
        exact (lt_irrefl 0 hpos).elim
      · rfl
    · simp

private lemma scoreLogTripleBaseline_armCellMass_true_all
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (r r' : LabelSpace J)
    (x y z : ScoreSpace ε)
    (hx : g x = r) (hy : g y = r) (hz : g z = r) :
    armCellMass (scoreLogTripleBaseline x y z) g true r' =
      if r' = r then ((x : ℝ) + y + z) / 3 else 0 := by
  classical
  by_cases hr : r' = r
  · subst r'
    rw [scoreLogTripleBaseline_armCellMass_true g r x y z hx hy hz, if_pos rfl]
  · rw [if_neg hr]
    unfold armCellMass scoreLogTripleBaseline
    rw [Measure.restrict_add, Measure.restrict_add,
      Measure.restrict_smul, Measure.restrict_smul, Measure.restrict_smul,
      restrict_dirac, restrict_dirac, restrict_dirac]
    simp [cell, hx, hy, hz, Ne.symm hr]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,r,x,y,z,hxy,hyz,hx,hy,hz,t,ht₁,ht₂,hMass), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTripleBaseline_muUpper_true
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (r : LabelSpace J) (x y z : ScoreSpace ε)
    (hxy : x < y) (hyz : y < z)
    (hx : g x = r) (hy : g y = r) (hz : g z = r)
    (t : ℝ)
    (ht₁ : (x : ℝ) * (1 / 3) < t)
    (ht₂ : t < min ((x : ℝ) * (1 / 3) + (y : ℝ) * (1 / 3))
      ((z : ℝ) * (1 / 3)))
    (hMass : CompatibleCellMasses (scoreLogTripleBaseline x y z) g
      (releasedLaw (scoreLogTripleBaselineFullLaw g x y z
        (t / (((x : ℝ) + y + z) / 3))))) :
    muUpper (scoreLogTripleBaseline x y z) g
        (releasedLaw (scoreLogTripleBaselineFullLaw g x y z
          (t / (((x : ℝ) + y + z) / 3)))) hMass true =
      threeScoreUpperEndpoint (x : ℝ) y (1 / 3) t := by
  let q : ℝ := ((x : ℝ) + y + z) / 3
  have hx0 : 0 < (x : ℝ) := lt_of_lt_of_le hOverlap.1 x.property.1
  have hy0 : 0 < (y : ℝ) := lt_trans hx0 hxy
  have hz0 : 0 < (z : ℝ) := lt_trans hy0 hyz
  have hq : 0 < q := by dsimp [q]; linarith
  have ht0 : 0 < t := lt_trans (mul_pos hx0 (by norm_num)) ht₁
  have htq : t < q := by
    have hleft := lt_of_lt_of_le ht₂ (min_le_left _ _)
    dsimp [q]
    nlinarith [mul_pos hz0 (by norm_num : (0 : ℝ) < 1 / 3)]
  have hs0 : 0 ≤ t / q := (div_pos ht0 hq).le
  have hs1 : t / q ≤ 1 := (div_lt_one hq).2 htq |>.le
  have hrel := scoreLogTripleBaseline_releasedLaw_cell
    g hOverlap r x y z hx hy hz t hs0 hs1
  have hout :
      armCellOutcomeLaw
          (releasedLaw (scoreLogTripleBaselineFullLaw g x y z (t / q)))
          hMass.2.1 true r
          (by
            rw [hMass.2.2.2 true r,
              scoreLogTripleBaseline_armCellMass_true g r x y z hx hy hz]
            exact hq) =
        threeScoreOutcomeLaw q t := by
    unfold armCellOutcomeLaw
    rw [hrel]
    have hout' := scoreLogReleasedCellLaw_armCellOutcomeLaw r q t (1 - q)
      hq (sub_nonneg.mpr (by
        dsimp [q]
        have hx1 : (x : ℝ) ≤ 1 := by linarith [x.property.2, hOverlap.1]
        have hy1 : (y : ℝ) ≤ 1 := by linarith [y.property.2, hOverlap.1]
        have hz1 : (z : ℝ) ≤ 1 := by linarith [z.property.2, hOverlap.1]
        linarith)) hs0 hs1 (by ring)
    unfold armCellOutcomeLaw at hout'
    exact hout'
  unfold muUpper
  rw [Finset.sum_eq_single r]
  · split_ifs with hpos
    · rw [scoreLogTripleBaseline_armCellMass_true g r x y z hx hy hz]
      rw [hout]
      rw [scoreLogTripleBaseline_armCellWeightLaw_true g hMass.2.2.1 r
        x y z hx hy hz hq]
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
      have hupper := threeScore_quantileProduct_upper
        (x : ℝ) y z (1 / 3) (1 / 3) (1 / 3) t hx0 hxy hyz
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht₁ ht₂
      have hqeq :
          (x : ℝ) * (1 / 3) + (y : ℝ) * (1 / 3) + (z : ℝ) * (1 / 3) = q := by
        dsimp [q]
        ring
      rw [hqeq] at hupper
      exact hupper
    · exfalso
      apply hpos
      rw [scoreLogTripleBaseline_armCellMass_true g r x y z hx hy hz]
      exact hq
  · intro r' _ hr'
    split_ifs with hpos
    · have hzero := scoreLogTripleBaseline_armCellMass_true_all
        g r r' x y z hx hy hz
      rw [if_neg hr'] at hzero
      rw [hzero] at hpos
      exact (lt_irrefl 0 hpos).elim
    · rfl
  · simp

private lemma scoreLogTriplePerturbed_armCellMass_true_all
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (r r' : LabelSpace J)
    (x y z : ScoreSpace ε) (hxy : x < y) (hyz : y < z)
    (hx : g x = r) (hy : g y = r) (hz : g z = r)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u * ((z : ℝ) - x) ≤ 1 / 3) :
    armCellMass (scoreLogTriplePerturbed x y z u) g true r' =
      if r' = r then ((x : ℝ) + y + z) / 3 else 0 := by
  classical
  by_cases hr : r' = r
  · subst r'
    rw [scoreLogTriplePerturbed_armCellMass_true g r x y z hxy hyz
      hx hy hz u hu0 hu, if_pos rfl]
  · rw [if_neg hr]
    unfold armCellMass scoreLogTriplePerturbed
    rw [Measure.restrict_add, Measure.restrict_add,
      Measure.restrict_smul, Measure.restrict_smul, Measure.restrict_smul,
      restrict_dirac, restrict_dirac, restrict_dirac]
    simp [cell, hx, hy, hz, Ne.symm hr]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,r,x,y,z,hxy,hyz,hx,hy,hz,t,u,hu0,hu,ht₁,ht₂,hMass), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTriplePerturbed_muUpper_true
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (r : LabelSpace J) (x y z : ScoreSpace ε)
    (hxy : x < y) (hyz : y < z)
    (hx : g x = r) (hy : g y = r) (hz : g z = r)
    (t u : ℝ) (hu0 : 0 ≤ u) (hu : u * ((z : ℝ) - x) ≤ 1 / 3)
    (ht₁ : (x : ℝ) * (1 / 3 + u * ((z : ℝ) - y)) < t)
    (ht₂ : t < min
      ((x : ℝ) * (1 / 3 + u * ((z : ℝ) - y)) +
        (y : ℝ) * (1 / 3 - u * ((z : ℝ) - x)))
      ((z : ℝ) * (1 / 3 + u * ((y : ℝ) - x))))
    (hMass : CompatibleCellMasses (scoreLogTriplePerturbed x y z u) g
      (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z
        (t / (((x : ℝ) + y + z) / 3)) u))) :
    muUpper (scoreLogTriplePerturbed x y z u) g
        (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z
          (t / (((x : ℝ) + y + z) / 3)) u)) hMass true =
      threeScoreUpperEndpoint (x : ℝ) y
        (1 / 3 + u * ((z : ℝ) - y)) t := by
  let wx : ℝ := 1 / 3 + u * ((z : ℝ) - y)
  let wy : ℝ := 1 / 3 - u * ((z : ℝ) - x)
  let wz : ℝ := 1 / 3 + u * ((y : ℝ) - x)
  let q : ℝ := ((x : ℝ) + y + z) / 3
  have hw := scoreLogTriple_weights_nonneg x y z hxy hyz u hu0 hu
  have hsum := (scoreLogTriple_weight_identities x y z hxy hyz u).1
  have hmoment := (scoreLogTriple_weight_identities x y z hxy hyz u).2
  have hx0 : 0 < (x : ℝ) := lt_of_lt_of_le hOverlap.1 x.property.1
  have hy0 : 0 < (y : ℝ) := lt_trans hx0 hxy
  have hz0 : 0 < (z : ℝ) := lt_trans hy0 hyz
  have hq : 0 < q := by dsimp [q]; linarith
  have ht0 : 0 < t := by
    have : 0 ≤ (x : ℝ) * wx := mul_nonneg hx0.le (by simpa [wx] using hw.1)
    exact lt_of_le_of_lt this (by simpa [wx] using ht₁)
  have htq : t < q := by
    have hleft := lt_of_lt_of_le ht₂ (min_le_left _ _)
    have hwz : 0 ≤ wz := by simpa [wz] using hw.2.2
    have hmom : (x : ℝ) * wx + (y : ℝ) * wy + (z : ℝ) * wz = q := by
      dsimp [wx, wy, wz, q]
      calc
        _ = (x : ℝ) / 3 + (y : ℝ) / 3 + (z : ℝ) / 3 := hmoment
        _ = ((x : ℝ) + y + z) / 3 := by ring
    have hleft' : t < (x : ℝ) * wx + (y : ℝ) * wy := by
      simpa [wx, wy] using hleft
    nlinarith [mul_nonneg hz0.le hwz]
  have hs0 : 0 ≤ t / q := (div_pos ht0 hq).le
  have hs1 : t / q ≤ 1 := (div_lt_one hq).2 htq |>.le
  have hrel := scoreLogTriplePerturbed_releasedLaw_cell
    g hOverlap r x y z hxy hyz hx hy hz t u hs0 hs1 hu0 hu
  have hout :
      armCellOutcomeLaw
          (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z (t / q) u))
          hMass.2.1 true r
          (by
            rw [hMass.2.2.2 true r,
              scoreLogTriplePerturbed_armCellMass_true g r x y z hxy hyz
                hx hy hz u hu0 hu]
            exact hq) =
        threeScoreOutcomeLaw q t := by
    unfold armCellOutcomeLaw
    rw [hrel]
    have hout' := scoreLogReleasedCellLaw_armCellOutcomeLaw r q t (1 - q)
      hq (sub_nonneg.mpr (by
        dsimp [q]
        have hx1 : (x : ℝ) ≤ 1 := by linarith [x.property.2, hOverlap.1]
        have hy1 : (y : ℝ) ≤ 1 := by linarith [y.property.2, hOverlap.1]
        have hz1 : (z : ℝ) ≤ 1 := by linarith [z.property.2, hOverlap.1]
        linarith)) hs0 hs1 (by ring)
    unfold armCellOutcomeLaw at hout'
    exact hout'
  unfold muUpper
  rw [Finset.sum_eq_single r]
  · split_ifs with hpos
    · rw [scoreLogTriplePerturbed_armCellMass_true g r x y z hxy hyz
        hx hy hz u hu0 hu]
      rw [hout]
      rw [scoreLogTriplePerturbed_armCellWeightLaw_true g hMass.2.2.1 r
        x y z hxy hyz hx hy hz u hu0 hu hq]
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
      have hupper := threeScore_quantileProduct_upper
        (x : ℝ) y z wx wy wz t hx0 hxy hyz
        (by simpa [wx] using hw.1) (by simpa [wy] using hw.2.1)
        (by simpa [wz] using hw.2.2) (by simpa [wx, wy, wz] using hsum)
        (by simpa [wx] using ht₁) (by simpa [wx, wy, wz] using ht₂)
      have hqeq : (x : ℝ) * wx + (y : ℝ) * wy + (z : ℝ) * wz = q := by
        dsimp [wx, wy, wz, q]
        calc
          _ = (x : ℝ) / 3 + (y : ℝ) / 3 + (z : ℝ) / 3 := hmoment
          _ = ((x : ℝ) + y + z) / 3 := by ring
      rw [hqeq] at hupper
      exact hupper
    · exfalso
      apply hpos
      rw [scoreLogTriplePerturbed_armCellMass_true g r x y z hxy hyz
        hx hy hz u hu0 hu]
      exact hq
  · intro r' _ hr'
    split_ifs with hpos
    · have hzero := scoreLogTriplePerturbed_armCellMass_true_all
        g r r' x y z hxy hyz hx hy hz u hu0 hu
      rw [if_neg hr'] at hzero
      rw [hzero] at hpos
      exact (lt_irrefl 0 hpos).elim
    · rfl
  · simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,r,x,y,z,hxy,hyz,hx,hy,hz,t,ht₁,ht₂,hMass), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTripleBaseline_muLower_true
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (r : LabelSpace J) (x y z : ScoreSpace ε)
    (hxy : x < y) (hyz : y < z)
    (hx : g x = r) (hy : g y = r) (hz : g z = r)
    (t : ℝ)
    (ht₁ : (x : ℝ) * (1 / 3) < t)
    (ht₂ : t < min ((x : ℝ) * (1 / 3) + (y : ℝ) * (1 / 3))
      ((z : ℝ) * (1 / 3)))
    (hMass : CompatibleCellMasses (scoreLogTripleBaseline x y z) g
      (releasedLaw (scoreLogTripleBaselineFullLaw g x y z
        (t / (((x : ℝ) + y + z) / 3))))) :
    muLower (scoreLogTripleBaseline x y z) g
        (releasedLaw (scoreLogTripleBaselineFullLaw g x y z
          (t / (((x : ℝ) + y + z) / 3)))) hMass true =
      threeScoreLowerEndpoint (z : ℝ) t := by
  let q : ℝ := ((x : ℝ) + y + z) / 3
  have hx0 : 0 < (x : ℝ) := lt_of_lt_of_le hOverlap.1 x.property.1
  have hy0 : 0 < (y : ℝ) := lt_trans hx0 hxy
  have hz0 : 0 < (z : ℝ) := lt_trans hy0 hyz
  have hq : 0 < q := by dsimp [q]; linarith
  have ht0 : 0 < t := lt_trans (mul_pos hx0 (by norm_num)) ht₁
  have htq : t < q := by
    have hleft := lt_of_lt_of_le ht₂ (min_le_left _ _)
    dsimp [q]
    nlinarith [mul_pos hz0 (by norm_num : (0 : ℝ) < 1 / 3)]
  have hs0 : 0 ≤ t / q := (div_pos ht0 hq).le
  have hs1 : t / q ≤ 1 := (div_lt_one hq).2 htq |>.le
  have hrel := scoreLogTripleBaseline_releasedLaw_cell
    g hOverlap r x y z hx hy hz t hs0 hs1
  have hout :
      armCellOutcomeLaw
          (releasedLaw (scoreLogTripleBaselineFullLaw g x y z (t / q)))
          hMass.2.1 true r
          (by
            rw [hMass.2.2.2 true r,
              scoreLogTripleBaseline_armCellMass_true g r x y z hx hy hz]
            exact hq) =
        threeScoreOutcomeLaw q t := by
    unfold armCellOutcomeLaw
    rw [hrel]
    have hout' := scoreLogReleasedCellLaw_armCellOutcomeLaw r q t (1 - q)
      hq (sub_nonneg.mpr (by
        dsimp [q]
        have hx1 : (x : ℝ) ≤ 1 := by linarith [x.property.2, hOverlap.1]
        have hy1 : (y : ℝ) ≤ 1 := by linarith [y.property.2, hOverlap.1]
        have hz1 : (z : ℝ) ≤ 1 := by linarith [z.property.2, hOverlap.1]
        linarith)) hs0 hs1 (by ring)
    unfold armCellOutcomeLaw at hout'
    exact hout'
  unfold muLower
  rw [Finset.sum_eq_single r]
  · split_ifs with hpos
    · rw [scoreLogTripleBaseline_armCellMass_true g r x y z hx hy hz]
      rw [hout]
      rw [scoreLogTripleBaseline_armCellWeightLaw_true g hMass.2.2.1 r
        x y z hx hy hz hq]
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
      have hlower := threeScore_quantileProduct_lower
        (x : ℝ) y z (1 / 3) (1 / 3) (1 / 3) t hx0 hxy hyz
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht₁ ht₂
      have hqeq :
          (x : ℝ) * (1 / 3) + (y : ℝ) * (1 / 3) + (z : ℝ) * (1 / 3) = q := by
        dsimp [q]
        ring
      rw [hqeq] at hlower
      exact hlower
    · exfalso
      apply hpos
      rw [scoreLogTripleBaseline_armCellMass_true g r x y z hx hy hz]
      exact hq
  · intro r' _ hr'
    split_ifs with hpos
    · have hzero := scoreLogTripleBaseline_armCellMass_true_all
        g r r' x y z hx hy hz
      rw [if_neg hr'] at hzero
      rw [hzero] at hpos
      exact (lt_irrefl 0 hpos).elim
    · rfl
  · simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,r,x,y,z,hxy,hyz,hx,hy,hz,t,u,hu0,hu,ht₁,ht₂,hMass), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTriplePerturbed_muLower_true
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (r : LabelSpace J) (x y z : ScoreSpace ε)
    (hxy : x < y) (hyz : y < z)
    (hx : g x = r) (hy : g y = r) (hz : g z = r)
    (t u : ℝ) (hu0 : 0 ≤ u) (hu : u * ((z : ℝ) - x) ≤ 1 / 3)
    (ht₁ : (x : ℝ) * (1 / 3 + u * ((z : ℝ) - y)) < t)
    (ht₂ : t < min
      ((x : ℝ) * (1 / 3 + u * ((z : ℝ) - y)) +
        (y : ℝ) * (1 / 3 - u * ((z : ℝ) - x)))
      ((z : ℝ) * (1 / 3 + u * ((y : ℝ) - x))))
    (hMass : CompatibleCellMasses (scoreLogTriplePerturbed x y z u) g
      (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z
        (t / (((x : ℝ) + y + z) / 3)) u))) :
    muLower (scoreLogTriplePerturbed x y z u) g
        (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z
          (t / (((x : ℝ) + y + z) / 3)) u)) hMass true =
      threeScoreLowerEndpoint (z : ℝ) t := by
  let wx : ℝ := 1 / 3 + u * ((z : ℝ) - y)
  let wy : ℝ := 1 / 3 - u * ((z : ℝ) - x)
  let wz : ℝ := 1 / 3 + u * ((y : ℝ) - x)
  let q : ℝ := ((x : ℝ) + y + z) / 3
  have hw := scoreLogTriple_weights_nonneg x y z hxy hyz u hu0 hu
  have hsum := (scoreLogTriple_weight_identities x y z hxy hyz u).1
  have hmoment := (scoreLogTriple_weight_identities x y z hxy hyz u).2
  have hx0 : 0 < (x : ℝ) := lt_of_lt_of_le hOverlap.1 x.property.1
  have hy0 : 0 < (y : ℝ) := lt_trans hx0 hxy
  have hz0 : 0 < (z : ℝ) := lt_trans hy0 hyz
  have hq : 0 < q := by dsimp [q]; linarith
  have ht0 : 0 < t := by
    have : 0 ≤ (x : ℝ) * wx := mul_nonneg hx0.le (by simpa [wx] using hw.1)
    exact lt_of_le_of_lt this (by simpa [wx] using ht₁)
  have htq : t < q := by
    have hleft := lt_of_lt_of_le ht₂ (min_le_left _ _)
    have hwz : 0 ≤ wz := by simpa [wz] using hw.2.2
    have hmom : (x : ℝ) * wx + (y : ℝ) * wy + (z : ℝ) * wz = q := by
      dsimp [wx, wy, wz, q]
      calc
        _ = (x : ℝ) / 3 + (y : ℝ) / 3 + (z : ℝ) / 3 := hmoment
        _ = ((x : ℝ) + y + z) / 3 := by ring
    have hleft' : t < (x : ℝ) * wx + (y : ℝ) * wy := by
      simpa [wx, wy] using hleft
    nlinarith [mul_nonneg hz0.le hwz]
  have hs0 : 0 ≤ t / q := (div_pos ht0 hq).le
  have hs1 : t / q ≤ 1 := (div_lt_one hq).2 htq |>.le
  have hrel := scoreLogTriplePerturbed_releasedLaw_cell
    g hOverlap r x y z hxy hyz hx hy hz t u hs0 hs1 hu0 hu
  have hout :
      armCellOutcomeLaw
          (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z (t / q) u))
          hMass.2.1 true r
          (by
            rw [hMass.2.2.2 true r,
              scoreLogTriplePerturbed_armCellMass_true g r x y z hxy hyz
                hx hy hz u hu0 hu]
            exact hq) =
        threeScoreOutcomeLaw q t := by
    unfold armCellOutcomeLaw
    rw [hrel]
    have hout' := scoreLogReleasedCellLaw_armCellOutcomeLaw r q t (1 - q)
      hq (sub_nonneg.mpr (by
        dsimp [q]
        have hx1 : (x : ℝ) ≤ 1 := by linarith [x.property.2, hOverlap.1]
        have hy1 : (y : ℝ) ≤ 1 := by linarith [y.property.2, hOverlap.1]
        have hz1 : (z : ℝ) ≤ 1 := by linarith [z.property.2, hOverlap.1]
        linarith)) hs0 hs1 (by ring)
    unfold armCellOutcomeLaw at hout'
    exact hout'
  unfold muLower
  rw [Finset.sum_eq_single r]
  · split_ifs with hpos
    · rw [scoreLogTriplePerturbed_armCellMass_true g r x y z hxy hyz
        hx hy hz u hu0 hu]
      rw [hout]
      rw [scoreLogTriplePerturbed_armCellWeightLaw_true g hMass.2.2.1 r
        x y z hxy hyz hx hy hz u hu0 hu hq]
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
      have hlower := threeScore_quantileProduct_lower
        (x : ℝ) y z wx wy wz t hx0 hxy hyz
        (by simpa [wx] using hw.1) (by simpa [wy] using hw.2.1)
        (by simpa [wz] using hw.2.2) (by simpa [wx, wy, wz] using hsum)
        (by simpa [wx] using ht₁) (by simpa [wx, wy, wz] using ht₂)
      have hqeq : (x : ℝ) * wx + (y : ℝ) * wy + (z : ℝ) * wz = q := by
        dsimp [wx, wy, wz, q]
        calc
          _ = (x : ℝ) / 3 + (y : ℝ) / 3 + (z : ℝ) / 3 := hmoment
          _ = ((x : ℝ) + y + z) / 3 := by ring
      rw [hqeq] at hlower
      exact hlower
    · exfalso
      apply hpos
      rw [scoreLogTriplePerturbed_armCellMass_true g r x y z hxy hyz
        hx hy hz u hu0 hu]
      exact hq
  · intro r' _ hr'
    split_ifs with hpos
    · have hzero := scoreLogTriplePerturbed_armCellMass_true_all
        g r r' x y z hxy hyz hx hy hz u hu0 hu
      rw [if_neg hr'] at hzero
      rw [hzero] at hpos
      exact (lt_irrefl 0 hpos).elim
    · rfl
  · simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,r,x,y,z,hxy,hyz,hx,hy,hz,t,u,hu0,hu,hb₁,hb₂,hp₁,hp₂,hMass₀,hMass₁), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTriple_sharpATELength_perturbation
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (r : LabelSpace J) (x y z : ScoreSpace ε)
    (hxy : x < y) (hyz : y < z)
    (hx : g x = r) (hy : g y = r) (hz : g z = r)
    (t u : ℝ) (hu0 : 0 ≤ u) (hu : u * ((z : ℝ) - x) ≤ 1 / 3)
    (hb₁ : (x : ℝ) * (1 / 3) < t)
    (hb₂ : t < min ((x : ℝ) * (1 / 3) + (y : ℝ) * (1 / 3))
      ((z : ℝ) * (1 / 3)))
    (hp₁ : (x : ℝ) * (1 / 3 + u * ((z : ℝ) - y)) < t)
    (hp₂ : t < min
      ((x : ℝ) * (1 / 3 + u * ((z : ℝ) - y)) +
        (y : ℝ) * (1 / 3 - u * ((z : ℝ) - x)))
      ((z : ℝ) * (1 / 3 + u * ((y : ℝ) - x))))
    (hMass₀ : CompatibleCellMasses (scoreLogTripleBaseline x y z) g
      (releasedLaw (scoreLogTripleBaselineFullLaw g x y z
        (t / (((x : ℝ) + y + z) / 3)))))
    (hMass₁ : CompatibleCellMasses (scoreLogTriplePerturbed x y z u) g
      (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z
        (t / (((x : ℝ) + y + z) / 3)) u))) :
    sharpATELength (scoreLogTriplePerturbed x y z u) g
        (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z
          (t / (((x : ℝ) + y + z) / 3)) u)) hMass₁ -
      sharpATELength (scoreLogTripleBaseline x y z) g
        (releasedLaw (scoreLogTripleBaselineFullLaw g x y z
          (t / (((x : ℝ) + y + z) / 3)))) hMass₀ =
      u * ((z : ℝ) - y) * (1 - (x : ℝ) / y) := by
  let q : ℝ := ((x : ℝ) + y + z) / 3
  have hx0 : 0 < (x : ℝ) := lt_of_lt_of_le hOverlap.1 x.property.1
  have hy0 : 0 < (y : ℝ) := lt_trans hx0 hxy
  have hz0 : 0 < (z : ℝ) := lt_trans hy0 hyz
  have hq : 0 < q := by dsimp [q]; linarith
  have ht0 : 0 < t := lt_trans (mul_pos hx0 (by norm_num)) hb₁
  have htq : t < q := by
    have hleft := lt_of_lt_of_le hb₂ (min_le_left _ _)
    dsimp [q]
    nlinarith [mul_pos hz0 (by norm_num : (0 : ℝ) < 1 / 3)]
  have hs0 : 0 ≤ t / q := (div_pos ht0 hq).le
  have hs1 : t / q ≤ 1 := (div_lt_one hq).2 htq |>.le
  have hq1 : q < 1 := by
    have hx1 : (x : ℝ) < 1 := lt_of_le_of_lt x.property.2 (by linarith [hOverlap.1])
    have hy1 : (y : ℝ) < 1 := lt_of_le_of_lt y.property.2 (by linarith [hOverlap.1])
    have hz1 : (z : ℝ) < 1 := lt_of_le_of_lt z.property.2 (by linarith [hOverlap.1])
    dsimp [q]
    linarith
  have hrel₀ := scoreLogTripleBaseline_releasedLaw_cell
    g hOverlap r x y z hx hy hz t hs0 hs1
  have hrel₁ := scoreLogTriplePerturbed_releasedLaw_cell
    g hOverlap r x y z hxy hyz hx hy hz t u hs0 hs1 hu0 hu
  have hc₀ := muLower_muUpper_false_eq_zero_of_scoreLogReleasedCellLaw
    (scoreLogTripleBaseline x y z) g
    (releasedLaw (scoreLogTripleBaselineFullLaw g x y z (t / q))) hMass₀
    r q t (1 - q) hrel₀ hq.le (sub_pos.mpr hq1) hs0 hs1 (by ring)
  have hc₁ := muLower_muUpper_false_eq_zero_of_scoreLogReleasedCellLaw
    (scoreLogTriplePerturbed x y z u) g
    (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z (t / q) u)) hMass₁
    r q t (1 - q) hrel₁ hq.le (sub_pos.mpr hq1) hs0 hs1 (by ring)
  unfold sharpATELength
  rw [scoreLogTriplePerturbed_muUpper_true g hOverlap r x y z hxy hyz
      hx hy hz t u hu0 hu hp₁ hp₂ hMass₁,
    scoreLogTriplePerturbed_muLower_true g hOverlap r x y z hxy hyz
      hx hy hz t u hu0 hu hp₁ hp₂ hMass₁,
    scoreLogTripleBaseline_muUpper_true g hOverlap r x y z hxy hyz
      hx hy hz t hb₁ hb₂ hMass₀,
    scoreLogTripleBaseline_muLower_true g hOverlap r x y z hxy hyz
      hx hy hz t hb₁ hb₂ hMass₀,
    hc₁.1, hc₁.2, hc₀.1, hc₀.2]
  have hshift := threeScoreUpperEndpoint_perturbation
    (x : ℝ) y z t u hx0 hxy
  linarith

end
end CausalSmith.PartialID.UnlinkedPropensityAte
