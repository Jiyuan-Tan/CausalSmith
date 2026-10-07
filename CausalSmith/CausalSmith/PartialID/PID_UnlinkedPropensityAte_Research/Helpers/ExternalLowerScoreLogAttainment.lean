module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawEndpointFullRow
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogSharpATE

/-! Paper-specific endpoint-law instantiations for the score-log pair. -/

public section

open MeasureTheory
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointFullLaw_externalScoreLaw
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    ExternalScoreLaw g
      (endpointFullLaw H g Prel hMass hOverlap upper0 upper1) H where
  probabilityP := endpointFullLaw_isProbabilityMeasure
    H g Prel hMass hOverlap upper0 upper1
  probabilityH := hMass.1
  overlap := hOverlap
  measurableRelease := hMass.2.2.1
  scoreMarginal := endpointFullLaw_scoreMarginal
    H g Prel hMass hOverlap upper0 upper1
  randomizedAssignment := endpointFullLaw_randomizedAssignment
    H g Prel hMass hOverlap upper0 upper1
  consistency := endpointFullLaw_consistency
    H g Prel hMass hOverlap upper0 upper1
  deterministicRelease := endpointFullLaw_deterministicRelease
    H g Prel hMass hOverlap upper0 upper1

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointFullLaw_mem_externalLaws
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    (endpointFullLaw H g Prel hMass hOverlap upper0 upper1, H) ∈
      ExternalLaws g :=
  ⟨endpointFullLaw_isProbabilityMeasure H g Prel hMass hOverlap upper0 upper1,
    hMass.1,
    endpointFullLaw_externalScoreLaw H g Prel hMass hOverlap upper0 upper1⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,upper0,upper1), this result [establishes the stated mathematical conclusion](goal). -/
lemma endpointFullLaw_ate
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (upper0 upper1 : Bool) :
    ate (endpointFullLaw H g Prel hMass hOverlap upper0 upper1) =
      (if upper1 then muUpper H g Prel hMass true
       else muLower H g Prel hMass true) -
      (if upper0 then muUpper H g Prel hMass false
       else muLower H g Prel hMass false) := by
  letI : IsProbabilityMeasure
      (endpointFullLaw H g Prel hMass hOverlap upper0 upper1) :=
    endpointFullLaw_isProbabilityMeasure H g Prel hMass hOverlap upper0 upper1
  rw [ate_eq_potentialOutcomeMeans_sub]
  rw [show (∫ ω, ((outcome1 ω : OutcomeSpace) : ℝ)
        ∂endpointFullLaw H g Prel hMass hOverlap upper0 upper1) =
      (if upper1 then muUpper H g Prel hMass true
       else muLower H g Prel hMass true) by
        simpa using endpointFullLaw_armMean H g Prel hMass hOverlap
          upper0 upper1 true]
  rw [show (∫ ω, ((outcome0 ω : OutcomeSpace) : ℝ)
        ∂endpointFullLaw H g Prel hMass hOverlap upper0 upper1) =
      (if upper0 then muUpper H g Prel hMass false
       else muLower H g Prel hMass false) by
        simpa using endpointFullLaw_armMean H g Prel hMass hOverlap
          upper0 upper1 false]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,r,x,y,z,hxy,hyz,hx,hy,hz,t,ht₁,ht₂,hMass), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTripleBaseline_lowerEndpoint_ate
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
    ate (endpointFullLaw (scoreLogTripleBaseline x y z) g
        (releasedLaw (scoreLogTripleBaselineFullLaw g x y z
          (t / (((x : ℝ) + y + z) / 3)))) hMass hOverlap true false) =
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
  have hq1 : q < 1 := by
    have hx1 : (x : ℝ) < 1 :=
      lt_of_le_of_lt x.property.2 (by linarith [hOverlap.1])
    have hy1 : (y : ℝ) < 1 :=
      lt_of_le_of_lt y.property.2 (by linarith [hOverlap.1])
    have hz1 : (z : ℝ) < 1 :=
      lt_of_le_of_lt z.property.2 (by linarith [hOverlap.1])
    dsimp [q]
    linarith
  have hrel := scoreLogTripleBaseline_releasedLaw_cell
    g hOverlap r x y z hx hy hz t hs0 hs1
  have hc := muLower_muUpper_false_eq_zero_of_scoreLogReleasedCellLaw
    (scoreLogTripleBaseline x y z) g
    (releasedLaw (scoreLogTripleBaselineFullLaw g x y z (t / q))) hMass
    r q t (1 - q) hrel hq.le (sub_pos.mpr hq1) hs0 hs1 (by ring)
  rw [endpointFullLaw_ate]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [scoreLogTripleBaseline_muLower_true g hOverlap r x y z hxy hyz
      hx hy hz t ht₁ ht₂ hMass,
    hc.2, sub_zero]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,r,x,y,z,hxy,hyz,hx,hy,hz,t,u,hu0,hu,ht₁,ht₂,hMass), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTriplePerturbed_upperEndpoint_ate
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
    ate (endpointFullLaw (scoreLogTriplePerturbed x y z u) g
        (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z
          (t / (((x : ℝ) + y + z) / 3)) u)) hMass hOverlap false true) =
      threeScoreUpperEndpoint (x : ℝ) y
        (1 / 3 + u * ((z : ℝ) - y)) t := by
  let q : ℝ := ((x : ℝ) + y + z) / 3
  have hx0 : 0 < (x : ℝ) := lt_of_lt_of_le hOverlap.1 x.property.1
  have hy0 : 0 < (y : ℝ) := lt_trans hx0 hxy
  have hz0 : 0 < (z : ℝ) := lt_trans hy0 hyz
  have hq : 0 < q := by dsimp [q]; linarith
  have hw := scoreLogTriple_weights_nonneg x y z hxy hyz u hu0 hu
  have hsum := (scoreLogTriple_weight_identities x y z hxy hyz u).1
  have hmoment := (scoreLogTriple_weight_identities x y z hxy hyz u).2
  let wx : ℝ := 1 / 3 + u * ((z : ℝ) - y)
  let wy : ℝ := 1 / 3 - u * ((z : ℝ) - x)
  let wz : ℝ := 1 / 3 + u * ((y : ℝ) - x)
  have ht0 : 0 < t := by
    have hxwx : 0 ≤ (x : ℝ) * wx :=
      mul_nonneg hx0.le (by simpa [wx] using hw.1)
    exact lt_of_le_of_lt hxwx (by simpa [wx] using ht₁)
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
  have hq1 : q < 1 := by
    have hx1 : (x : ℝ) < 1 :=
      lt_of_le_of_lt x.property.2 (by linarith [hOverlap.1])
    have hy1 : (y : ℝ) < 1 :=
      lt_of_le_of_lt y.property.2 (by linarith [hOverlap.1])
    have hz1 : (z : ℝ) < 1 :=
      lt_of_le_of_lt z.property.2 (by linarith [hOverlap.1])
    dsimp [q]
    linarith
  have hrel := scoreLogTriplePerturbed_releasedLaw_cell
    g hOverlap r x y z hxy hyz hx hy hz t u hs0 hs1 hu0 hu
  have hc := muLower_muUpper_false_eq_zero_of_scoreLogReleasedCellLaw
    (scoreLogTriplePerturbed x y z u) g
    (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z (t / q) u)) hMass
    r q t (1 - q) hrel hq.le (sub_pos.mpr hq1) hs0 hs1 (by ring)
  rw [endpointFullLaw_ate]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [scoreLogTriplePerturbed_muUpper_true g hOverlap r x y z hxy hyz
      hx hy hz t u hu0 hu ht₁ ht₂ hMass,
    hc.1, sub_zero]

end
end CausalSmith.PartialID.UnlinkedPropensityAte
