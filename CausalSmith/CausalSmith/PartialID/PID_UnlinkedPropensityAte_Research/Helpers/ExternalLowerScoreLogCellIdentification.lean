module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogArmCell
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogFullLaw

/-! Identification of the active released cell in the score-log full laws. -/

public section

namespace CausalSmith.PartialID.UnlinkedPropensityAte

open MeasureTheory Set

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,r,x,y,z,hx,hy,hz,t,hs0,hs1), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTripleBaseline_releasedLaw_cell
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (r : LabelSpace J) (x y z : ScoreSpace ε)
    (hx : g x = r) (hy : g y = r) (hz : g z = r)
    (t : ℝ)
    (hs0 : 0 ≤ t / (((x : ℝ) + y + z) / 3))
    (hs1 : t / (((x : ℝ) + y + z) / 3) ≤ 1) :
    let q := ((x : ℝ) + y + z) / 3
    releasedLaw
        (scoreLogTripleBaselineFullLaw g x y z (t / q)) =
      scoreLogReleasedCellLaw r q t (1 - q) := by
  dsimp only
  let q : ℝ := ((x : ℝ) + y + z) / 3
  have ex0 : 0 ≤ (x : ℝ) := le_trans hOverlap.1.le x.property.1
  have ey0 : 0 ≤ (y : ℝ) := le_trans hOverlap.1.le y.property.1
  have ez0 : 0 ≤ (z : ℝ) := le_trans hOverlap.1.le z.property.1
  have ex1 : (x : ℝ) ≤ 1 := by linarith [x.property.2, hOverlap.1]
  have ey1 : (y : ℝ) ≤ 1 := by linarith [y.property.2, hOverlap.1]
  have ez1 : (z : ℝ) ≤ 1 := by linarith [z.property.2, hOverlap.1]
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  let T : Measure (Observation J) :=
    (trialOutcomeLaw (t / q)).map (fun v => (r, true, v))
  let F : Measure (Observation J) := Measure.dirac (r, false, trialZeroOutcome)
  have htCoeff :
      ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (x : ℝ) +
          ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (y : ℝ) +
          ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (z : ℝ) =
        ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3),
      ← ENNReal.ofReal_add (mul_nonneg (by norm_num) ex0)
        (mul_nonneg (by norm_num) ey0),
      ← ENNReal.ofReal_add
        (add_nonneg (mul_nonneg (by norm_num) ex0)
          (mul_nonneg (by norm_num) ey0))
        (mul_nonneg (by norm_num) ez0)]
    congr 1
    dsimp [q]
    ring
  have hcCoeff :
      ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (1 - (x : ℝ)) +
          ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (1 - (y : ℝ)) +
          ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (1 - (z : ℝ)) =
        ENNReal.ofReal (1 - q) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3),
      ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (sub_nonneg.mpr ex1))
        (mul_nonneg (by norm_num) (sub_nonneg.mpr ey1)),
      ← ENNReal.ofReal_add
        (add_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr ex1))
          (mul_nonneg (by norm_num) (sub_nonneg.mpr ey1)))
        (mul_nonneg (by norm_num) (sub_nonneg.mpr ez1))]
    congr 1
    dsimp [q]
    ring
  rw [scoreLogTripleBaselineFullLaw_releasedLaw,
    scoreLogAtomFullLaw_releasedLaw g x (t / q) hs0 hs1,
    scoreLogAtomFullLaw_releasedLaw g y (t / q) hs0 hs1,
    scoreLogAtomFullLaw_releasedLaw g z (t / q) hs0 hs1,
    hx, hy, hz]
  unfold scoreLogReleasedCellLaw
  have htCoeff' :
      ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (x : ℝ) +
          ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (y : ℝ) +
          ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (z : ℝ) =
        ENNReal.ofReal (((x : ℝ) + y + z) / 3) := by
    simpa [q] using htCoeff
  have hcCoeff' :
      ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (1 - (x : ℝ)) +
          ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (1 - (y : ℝ)) +
          ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (1 - (z : ℝ)) =
        ENNReal.ofReal (1 - (((x : ℝ) + y + z) / 3)) := by
    simpa [q] using hcCoeff
  rw [← htCoeff', ← hcCoeff']
  module

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,r,x,y,z,hxy,hyz,hx,hy,hz,t,u,hs0,hs1,hu0,hu), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTriplePerturbed_releasedLaw_cell
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (r : LabelSpace J) (x y z : ScoreSpace ε)
    (hxy : x < y) (hyz : y < z)
    (hx : g x = r) (hy : g y = r) (hz : g z = r)
    (t u : ℝ)
    (hs0 : 0 ≤ t / (((x : ℝ) + y + z) / 3))
    (hs1 : t / (((x : ℝ) + y + z) / 3) ≤ 1)
    (hu0 : 0 ≤ u) (hu : u * ((z : ℝ) - x) ≤ 1 / 3) :
    let q := ((x : ℝ) + y + z) / 3
    releasedLaw
        (scoreLogTriplePerturbedFullLaw g x y z (t / q) u) =
      scoreLogReleasedCellLaw r q t (1 - q) := by
  dsimp only
  rw [← scoreLogTriple_releasedLaw_eq g hOverlap r x y z hxy hyz
    hx hy hz (t / (((x : ℝ) + y + z) / 3)) hs0 hs1 u hu0 hu]
  exact scoreLogTripleBaseline_releasedLaw_cell
    g hOverlap r x y z hx hy hz t hs0 hs1

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,r,x,y,z,hx,hy,hz), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTripleBaseline_armCellMass_true
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (r : LabelSpace J)
    (x y z : ScoreSpace ε)
    (hx : g x = r) (hy : g y = r) (hz : g z = r) :
    armCellMass (scoreLogTripleBaseline x y z) g true r =
      ((x : ℝ) + y + z) / 3 := by
  classical
  unfold armCellMass scoreLogTripleBaseline
  rw [Measure.restrict_add, Measure.restrict_add,
    Measure.restrict_smul, Measure.restrict_smul, Measure.restrict_smul,
    restrict_dirac, restrict_dirac, restrict_dirac]
  simp only [cell, hx, hy, hz, Set.mem_ofPred_eq, if_pos]
  rw [integral_add_measure, integral_add_measure,
    integral_smul_measure, integral_smul_measure, integral_smul_measure]
  simp [armProb]
  ring
  all_goals
    first
    | exact Integrable.add_measure
        (Integrable.smul_measure (integrable_dirac (by simp [armProb])) (by simp))
        (Integrable.smul_measure (integrable_dirac (by simp [armProb])) (by simp))
    | exact Integrable.smul_measure (integrable_dirac (by simp [armProb])) (by simp)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hg,r,x,y,z,hx,hy,hz,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTripleBaseline_armCellWeightLaw_true
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hg : Measurable g)
    (r : LabelSpace J) (x y z : ScoreSpace ε)
    (hx : g x = r) (hy : g y = r) (hz : g z = r)
    (hq : 0 < ((x : ℝ) + y + z) / 3) :
    let hm : 0 < armCellMass (scoreLogTripleBaseline x y z) g true r := by
      rw [scoreLogTripleBaseline_armCellMass_true g r x y z hx hy hz]
      exact hq
    armCellWeightLaw (scoreLogTripleBaseline x y z)
        (scoreLogTripleBaseline_isProbabilityMeasure x y z)
        g hg true r hm =
      threeScoreInverseLaw (x : ℝ) y z (1 / 3) (1 / 3) (1 / 3) := by
  classical
  dsimp only
  unfold armCellWeightLaw armCellScoreLaw
  rw [scoreLogTripleBaseline_armCellMass_true g r x y z hx hy hz]
  unfold scoreLogTripleBaseline
  rw [
    withDensity_add_measure, withDensity_add_measure,
    withDensity_smul_measure, withDensity_smul_measure,
    withDensity_smul_measure, dirac_withDensity, dirac_withDensity,
    dirac_withDensity]
  simp only [Measure.restrict_add, Measure.restrict_smul, restrict_dirac,
    cell, hx, hy, hz, Set.mem_ofPred_eq, if_pos, armProb]
  repeat' rw [smul_smul]
  have hmap : Measurable (fun e : ScoreSpace ε => ((e : ℝ))⁻¹) := by
    simpa [armProb] using (measurable_inverseArmProb (ε := ε) true)
  rw [Measure.map_smul,
    Measure.map_add _ _ hmap,
    Measure.map_add _ _ hmap,
    Measure.map_smul, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' hmap, Measure.map_dirac' hmap,
    Measure.map_dirac' hmap]
  unfold threeScoreInverseLaw
  have hden :
      (x : ℝ) * (1 / 3) + (y : ℝ) * (1 / 3) + (z : ℝ) * (1 / 3) =
        ((x : ℝ) + y + z) / 3 := by ring
  have hcoeff (v : ℝ) :
      (ENNReal.ofReal (((x : ℝ) + y + z) / 3))⁻¹ *
          (ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal v) =
        ENNReal.ofReal
          (v * (1 / 3) /
            ((x : ℝ) * (1 / 3) + (y : ℝ) * (1 / 3) + (z : ℝ) * (1 / 3))) := by
    rw [hden, ENNReal.ofReal_div_of_pos hq]
    have hn :
        ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal v =
          ENNReal.ofReal (v * (1 / 3)) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
      congr 1
      ring
    rw [hn]
    simp only [div_eq_mul_inv, mul_comm]
  rw [smul_add, smul_add]
  repeat' rw [smul_smul]
  rw [hcoeff (x : ℝ), hcoeff (y : ℝ), hcoeff (z : ℝ)]
  simp only [one_div]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,r,x,y,z,hxy,hyz,hx,hy,hz,u,hu0,hu), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTriplePerturbed_armCellMass_true
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (r : LabelSpace J)
    (x y z : ScoreSpace ε) (hxy : x < y) (hyz : y < z)
    (hx : g x = r) (hy : g y = r) (hz : g z = r)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u * ((z : ℝ) - x) ≤ 1 / 3) :
    armCellMass (scoreLogTriplePerturbed x y z u) g true r =
      ((x : ℝ) + y + z) / 3 := by
  classical
  have hw := scoreLogTriple_weights_nonneg x y z hxy hyz u hu0 hu
  unfold armCellMass scoreLogTriplePerturbed
  rw [Measure.restrict_add, Measure.restrict_add,
    Measure.restrict_smul, Measure.restrict_smul, Measure.restrict_smul,
    restrict_dirac, restrict_dirac, restrict_dirac]
  simp only [cell, hx, hy, hz, Set.mem_ofPred_eq, if_pos]
  rw [integral_add_measure, integral_add_measure,
    integral_smul_measure, integral_smul_measure, integral_smul_measure]
  rw [ENNReal.toReal_ofReal hw.1, ENNReal.toReal_ofReal hw.2.1,
    ENNReal.toReal_ofReal hw.2.2]
  simp [armProb]
  have hm := (scoreLogTriple_weight_identities x y z hxy hyz u).2
  linarith
  all_goals
    first
    | exact Integrable.add_measure
        (Integrable.smul_measure (integrable_dirac (by simp [armProb])) (by simp))
        (Integrable.smul_measure (integrable_dirac (by simp [armProb])) (by simp))
    | exact Integrable.smul_measure (integrable_dirac (by simp [armProb])) (by simp)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hg,r,x,y,z,hxy,hyz,hx,hy,hz,u,hu0,hu,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTriplePerturbed_armCellWeightLaw_true
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hg : Measurable g)
    (r : LabelSpace J) (x y z : ScoreSpace ε)
    (hxy : x < y) (hyz : y < z)
    (hx : g x = r) (hy : g y = r) (hz : g z = r)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u * ((z : ℝ) - x) ≤ 1 / 3)
    (hq : 0 < ((x : ℝ) + y + z) / 3) :
    let wx := 1 / 3 + u * ((z : ℝ) - y)
    let wy := 1 / 3 - u * ((z : ℝ) - x)
    let wz := 1 / 3 + u * ((y : ℝ) - x)
    let hm : 0 < armCellMass (scoreLogTriplePerturbed x y z u) g true r := by
      rw [scoreLogTriplePerturbed_armCellMass_true g r x y z hxy hyz hx hy hz u hu0 hu]
      exact hq
    armCellWeightLaw (scoreLogTriplePerturbed x y z u)
        (scoreLogTriplePerturbed_isProbabilityMeasure x y z hxy hyz u hu0 hu)
        g hg true r hm =
      threeScoreInverseLaw (x : ℝ) y z wx wy wz := by
  classical
  dsimp only
  have hw := scoreLogTriple_weights_nonneg x y z hxy hyz u hu0 hu
  unfold armCellWeightLaw armCellScoreLaw
  rw [scoreLogTriplePerturbed_armCellMass_true g r x y z hxy hyz hx hy hz u hu0 hu]
  unfold scoreLogTriplePerturbed
  rw [withDensity_add_measure, withDensity_add_measure,
    withDensity_smul_measure, withDensity_smul_measure,
    withDensity_smul_measure, dirac_withDensity, dirac_withDensity,
    dirac_withDensity]
  simp only [Measure.restrict_add, Measure.restrict_smul, restrict_dirac,
    cell, hx, hy, hz, Set.mem_ofPred_eq, if_pos, armProb]
  repeat' rw [smul_smul]
  have hmap : Measurable (fun e : ScoreSpace ε => ((e : ℝ))⁻¹) := by
    simpa [armProb] using (measurable_inverseArmProb (ε := ε) true)
  rw [Measure.map_smul, Measure.map_add _ _ hmap,
    Measure.map_add _ _ hmap, Measure.map_smul, Measure.map_smul,
    Measure.map_smul, Measure.map_dirac' hmap, Measure.map_dirac' hmap,
    Measure.map_dirac' hmap]
  unfold threeScoreInverseLaw
  have hden :
      (x : ℝ) * (1 / 3 + u * ((z : ℝ) - y)) +
          (y : ℝ) * (1 / 3 - u * ((z : ℝ) - x)) +
          (z : ℝ) * (1 / 3 + u * ((y : ℝ) - x)) =
        ((x : ℝ) + y + z) / 3 := by
    calc
      _ = (x : ℝ) / 3 + (y : ℝ) / 3 + (z : ℝ) / 3 :=
        (scoreLogTriple_weight_identities x y z hxy hyz u).2
      _ = ((x : ℝ) + y + z) / 3 := by ring
  have hcoeff (v w : ℝ) (hw0 : 0 ≤ w) :
      (ENNReal.ofReal (((x : ℝ) + y + z) / 3))⁻¹ *
          (ENNReal.ofReal w * ENNReal.ofReal v) =
        ENNReal.ofReal
          (v * w /
            ((x : ℝ) * (1 / 3 + u * ((z : ℝ) - y)) +
              (y : ℝ) * (1 / 3 - u * ((z : ℝ) - x)) +
              (z : ℝ) * (1 / 3 + u * ((y : ℝ) - x)))) := by
    rw [hden, ENNReal.ofReal_div_of_pos hq]
    have hn : ENNReal.ofReal w * ENNReal.ofReal v =
        ENNReal.ofReal (v * w) := by
      rw [← ENNReal.ofReal_mul hw0]
      congr 1
      ring
    rw [hn]
    simp only [div_eq_mul_inv, mul_comm]
  rw [smul_add, smul_add]
  repeat' rw [smul_smul]
  rw [hcoeff (x : ℝ) _ hw.1, hcoeff (y : ℝ) _ hw.2.1,
    hcoeff (z : ℝ) _ hw.2.2]
  simp only [one_div]

end
end CausalSmith.PartialID.UnlinkedPropensityAte
