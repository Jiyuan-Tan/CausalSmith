module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogCertificate

/-! Final specialization of the calibrated score-log lower certificate. -/

@[expose] public section

open MeasureTheory Set Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,r,x,y,z,hxy,hyz,hx,hy,hz,t,ht₁,ht₂,hMass), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTripleBaseline_sharpLength
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
    sharpATELength (scoreLogTripleBaseline x y z) g
        (releasedLaw (scoreLogTripleBaselineFullLaw g x y z
          (t / (((x : ℝ) + y + z) / 3)))) hMass =
      threeScoreUpperEndpoint (x : ℝ) y (1 / 3) t -
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
    have hx1 : (x : ℝ) < 1 := lt_of_le_of_lt x.property.2 (by linarith [hOverlap.1])
    have hy1 : (y : ℝ) < 1 := lt_of_le_of_lt y.property.2 (by linarith [hOverlap.1])
    have hz1 : (z : ℝ) < 1 := lt_of_le_of_lt z.property.2 (by linarith [hOverlap.1])
    dsimp [q]
    linarith
  have hrel := scoreLogTripleBaseline_releasedLaw_cell
    g hOverlap r x y z hx hy hz t hs0 hs1
  have hc := muLower_muUpper_false_eq_zero_of_scoreLogReleasedCellLaw
    (scoreLogTripleBaseline x y z) g
    (releasedLaw (scoreLogTripleBaselineFullLaw g x y z (t / q))) hMass
    r q t (1 - q) hrel hq.le (sub_pos.mpr hq1) hs0 hs1 (by ring)
  unfold sharpATELength
  rw [scoreLogTripleBaseline_muUpper_true g hOverlap r x y z hxy hyz
      hx hy hz t ht₁ ht₂ hMass,
    scoreLogTripleBaseline_muLower_true g hOverlap r x y z hxy hyz
      hx hy hz t ht₁ ht₂ hMass,
    hc.1, hc.2]
  ring

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,r,x,y,z,hxy,hyz,hx,hy,hz,t,u,hu0,hu,ht₁,ht₂,hMass), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTriplePerturbed_sharpLength
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
    sharpATELength (scoreLogTriplePerturbed x y z u) g
        (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z
          (t / (((x : ℝ) + y + z) / 3)) u)) hMass =
      threeScoreUpperEndpoint (x : ℝ) y
          (1 / 3 + u * ((z : ℝ) - y)) t -
        threeScoreLowerEndpoint (z : ℝ) t := by
  let q : ℝ := ((x : ℝ) + y + z) / 3
  let wx : ℝ := 1 / 3 + u * ((z : ℝ) - y)
  let wy : ℝ := 1 / 3 - u * ((z : ℝ) - x)
  let wz : ℝ := 1 / 3 + u * ((y : ℝ) - x)
  have hw := scoreLogTriple_weights_nonneg x y z hxy hyz u hu0 hu
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
    have hleft' : t < (x : ℝ) * wx + (y : ℝ) * wy := by simpa [wx, wy] using hleft
    nlinarith [mul_nonneg hz0.le hwz]
  have hs0 : 0 ≤ t / q := (div_pos ht0 hq).le
  have hs1 : t / q ≤ 1 := (div_lt_one hq).2 htq |>.le
  have hq1 : q < 1 := by
    have hx1 : (x : ℝ) < 1 := lt_of_le_of_lt x.property.2 (by linarith [hOverlap.1])
    have hy1 : (y : ℝ) < 1 := lt_of_le_of_lt y.property.2 (by linarith [hOverlap.1])
    have hz1 : (z : ℝ) < 1 := lt_of_le_of_lt z.property.2 (by linarith [hOverlap.1])
    dsimp [q]
    linarith
  have hrel := scoreLogTriplePerturbed_releasedLaw_cell
    g hOverlap r x y z hxy hyz hx hy hz t u hs0 hs1 hu0 hu
  have hc := muLower_muUpper_false_eq_zero_of_scoreLogReleasedCellLaw
    (scoreLogTriplePerturbed x y z u) g
    (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z (t / q) u)) hMass
    r q t (1 - q) hrel hq.le (sub_pos.mpr hq1) hs0 hs1 (by ring)
  unfold sharpATELength
  rw [scoreLogTriplePerturbed_muUpper_true g hOverlap r x y z hxy hyz
      hx hy hz t u hu0 hu ht₁ ht₂ hMass,
    scoreLogTriplePerturbed_muLower_true g hOverlap r x y z hxy hyz
      hx hy hz t u hu0 hu ht₁ ht₂ hMass,
    hc.1, hc.2]
  ring

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,r,x,y,z,hxy,hyz,hx,hy,hz,t,u,hu0,hu,hb₁,hb₂,hp₁,hp₂,hMass₀,hMass₁), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTriple_endpoint_ate_separation
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
    ate (endpointFullLaw (scoreLogTriplePerturbed x y z u) g
          (releasedLaw (scoreLogTriplePerturbedFullLaw g x y z
            (t / (((x : ℝ) + y + z) / 3)) u)) hMass₁ hOverlap false true) -
        ate (endpointFullLaw (scoreLogTripleBaseline x y z) g
          (releasedLaw (scoreLogTripleBaselineFullLaw g x y z
            (t / (((x : ℝ) + y + z) / 3)))) hMass₀ hOverlap true false) =
      sharpATELength (scoreLogTripleBaseline x y z) g
          (releasedLaw (scoreLogTripleBaselineFullLaw g x y z
            (t / (((x : ℝ) + y + z) / 3)))) hMass₀ +
        u * ((z : ℝ) - y) * (1 - (x : ℝ) / y) := by
  have hA₀ := scoreLogTripleBaseline_lowerEndpoint_ate
    g hOverlap r x y z hxy hyz hx hy hz t hb₁ hb₂ hMass₀
  have hA₁ := scoreLogTriplePerturbed_upperEndpoint_ate
    g hOverlap r x y z hxy hyz hx hy hz t u hu0 hu hp₁ hp₂ hMass₁
  have hW₁ := scoreLogTriplePerturbed_sharpLength
    g hOverlap r x y z hxy hyz hx hy hz t u hu0 hu hp₁ hp₂ hMass₁
  have hshift := scoreLogTriple_sharpATELength_perturbation
    g hOverlap r x y z hxy hyz hx hy hz t u hu0 hu hb₁ hb₂ hp₁ hp₂
      hMass₀ hMass₁
  rw [hA₁, hA₀, ← hW₁]
  linarith

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,Qj,hTrial,hLog,hInd,P0,P0',P1,P1',H0,H1,hPH0,hPH0',hPH1,hPH1',hrel0,hrel1), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalExperiment_tv_eq_of_releasedLaw
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj) (hLog : ExternalLogIID g Qj)
    (hInd : ExternalLogIndependent g Qj)
    (P0 P0' P1 P1' : Measure (FullRow ε J))
    (H0 H1 : Measure (ScoreSpace ε))
    (hPH0 : (P0, H0) ∈ ExternalLaws g)
    (hPH0' : (P0', H0) ∈ ExternalLaws g)
    (hPH1 : (P1, H1) ∈ ExternalLaws g)
    (hPH1' : (P1', H1) ∈ ExternalLaws g)
    (hrel0 : releasedLaw P0' = releasedLaw P0)
    (hrel1 : releasedLaw P1' = releasedLaw P1) :
    Causalean.Stat.tvDist (Qj P0' H0) (Qj P1' H1) =
      Causalean.Stat.tvDist (Qj P0 H0) (Qj P1 H1) := by
  have hQ (P : Measure (FullRow ε J)) (H : Measure (ScoreSpace ε))
      (hPH : (P, H) ∈ ExternalLaws g) :
      Qj P H = (Measure.pi (fun _ : Fin n => releasedLaw P)).prod
        (Measure.pi (fun _ : Fin m => H)) := by
    rw [hInd (P, H) hPH, hTrial (P, H) hPH, hLog (P, H) hPH]
  rw [hQ P0' H0 hPH0', hQ P1' H1 hPH1', hQ P0 H0 hPH0,
    hQ P1 H1 hPH1, hrel0, hrel1]

/-- For [the specified mathematical inputs](hyp:ε,α,x,y,z), [this definition](goal) introduces the corresponding object. -/
def threeScoreFixedLogCertificate {ε : ℝ}
    (α : ℝ) (x y z : ScoreSpace ε) : ℝ :=
  (1 - 2 * α) * Real.sqrt (Real.log (1 + (1 - 2 * α) ^ 2)) /
      (2 * Real.sqrt 3) *
    ((((z : ℝ) - y) * (1 - (x : ℝ) / y)) /
      Real.sqrt (threeScoreGapSq x y z))

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,hg,r,x,y,z,hxy,hyz,hx,hy,hz,α,hα,Qj,hTrial,hLog,hInd), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogFixedTriple_eventually_externalExcessRisk_lower
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (hg : Measurable g) (r : LabelSpace J) (x y z : ScoreSpace ε)
    (hxy : x < y) (hyz : y < z)
    (hx : g x = r) (hy : g y = r) (hz : g z = r)
    (α : ℝ) (hα : 0 < α ∧ α < 1 / 2)
    (Qj : ∀ n m,
      Measure (FullRow ε J) → Measure (ScoreSpace ε) →
        Measure (ExternalSample ε J n m))
    (hTrial : ∀ n m, JointTrialIID g (Qj n m))
    (hLog : ∀ n m, ExternalLogIID g (Qj n m))
    (hInd : ∀ n m, ExternalLogIndependent g (Qj n m)) :
    ∀ᶠ m : ℕ in atTop, ∀ n : ℕ, 0 < n →
      threeScoreFixedLogCertificate α x y z *
          (Real.sqrt (m : ℝ))⁻¹ ≤
        externalExcessRisk g (Qj n m) α := by
  let t := threeScoreThreshold x y z
  let q : ℝ := ((x : ℝ) + y + z) / 3
  have hx0 : 0 < (x : ℝ) := lt_of_lt_of_le hOverlap.1 x.property.1
  have hb := threeScoreThreshold_baseline x y z hx0 hxy hyz
  dsimp only at hb
  have hs0 : 0 ≤ t / q := by simpa [t, q] using hb.2.2.1.le
  have hs1 : t / q ≤ 1 := by simpa [t, q] using hb.2.2.2.le
  have htv := scoreLogCalibrated_jointExperiment_eventually_tv_bound
    g hOverlap hg r x y z hxy hyz hx hy hz t α hα hs0 hs1
      Qj hTrial hLog hInd
  filter_upwards [threeScoreCalibratedU_eventually_thresholds
      α hα x y z hx0 hxy hyz, htv, eventually_gt_atTop (0 : ℕ)]
    with m hth htv_m hm
  intro n hn
  dsimp only at hth
  let u := threeScoreCalibratedU α x y z m
  let Pbase := scoreLogTripleBaselineFullLaw g x y z (t / q)
  let Hbase := scoreLogTripleBaseline x y z
  let Ppert := scoreLogTriplePerturbedFullLaw g x y z (t / q) u
  let Hpert := scoreLogTriplePerturbed x y z u
  have hpair := scoreLogTriple_externalPair g hOverlap hg r x y z hxy hyz
    hx hy hz (t / q) hs0 hs1 u hth.2.2.2.1 hth.2.2.2.2.1
  have hPHbase : (Pbase, Hbase) ∈ ExternalLaws g := by
    simpa [Pbase, Hbase, q] using hpair.1
  have hPHpert : (Ppert, Hpert) ∈ ExternalLaws g := by
    simpa [Ppert, Hpert, q] using hpair.2.1
  let hMass0 := externalLawCellMasses g (Pbase, Hbase) hPHbase
  let hMass1 := externalLawCellMasses g (Ppert, Hpert) hPHpert
  let E0 := endpointFullLaw Hbase g (releasedLaw Pbase) hMass0 hOverlap true false
  let E1 := endpointFullLaw Hpert g (releasedLaw Ppert) hMass1 hOverlap false true
  have hE0 : (E0, Hbase) ∈ ExternalLaws g := by
    exact endpointFullLaw_mem_externalLaws Hbase g (releasedLaw Pbase)
      hMass0 hOverlap true false
  have hE1 : (E1, Hpert) ∈ ExternalLaws g := by
    exact endpointFullLaw_mem_externalLaws Hpert g (releasedLaw Ppert)
      hMass1 hOverlap false true
  have hrel0 : releasedLaw E0 = releasedLaw Pbase := by
    exact endpointFullLaw_releasedLaw Hbase g (releasedLaw Pbase)
      hMass0 hOverlap true false
  have hrel1 : releasedLaw E1 = releasedLaw Ppert := by
    exact endpointFullLaw_releasedLaw Hpert g (releasedLaw Ppert)
      hMass1 hOverlap false true
  have htvEndpoint : Causalean.Stat.tvDist
      (Qj n m E0 Hbase) (Qj n m E1 Hpert) ≤ (1 - 2 * α) / 2 := by
    rw [externalExperiment_tv_eq_of_releasedLaw g (Qj n m)
      (hTrial n m) (hLog n m) (hInd n m)
      Pbase E0 Ppert E1 Hbase Hpert hPHbase hE0 hPHpert hE1 hrel0 hrel1]
    simpa [Pbase, Hbase, Ppert, Hpert, u, t, q] using htv_m n
  have hW0 := scoreLogTripleBaseline_sharpLength
    g hOverlap r x y z hxy hyz hx hy hz t hb.1 hb.2.1 hMass0
  have hsep := scoreLogTriple_endpoint_ate_separation
    g hOverlap r x y z hxy hyz hx hy hz t u hth.2.2.2.1
      hth.2.2.2.2.1 hb.1 hb.2.1 hth.2.2.2.2.2.1 hth.2.2.2.2.2.2
      hMass0 hMass1
  let Delta : ℝ := u * ((z : ℝ) - y) * (1 - (x : ℝ) / y)
  have hu0 : 0 < u := threeScoreCalibratedU_pos α hα x y z hxy hyz m
    hm
  have hy0 : 0 < (y : ℝ) := lt_trans hx0 hxy
  have hDelta : 0 < Delta := by
    dsimp [Delta]
    exact mul_pos (mul_pos hu0 (sub_pos.mpr hyz))
      (sub_pos.mpr ((div_lt_one hy0).2 hxy))
  have hW0nonneg : 0 ≤ sharpATELength Hbase g (releasedLaw Pbase) hMass0 :=
    sharpATELength_nonneg_of_overlap Hbase g (releasedLaw Pbase)
      hMass0 hOverlap
  have htheta : ate E0 ≤ ate E1 := by
    have : ate E1 - ate E0 =
        sharpATELength Hbase g (releasedLaw Pbase) hMass0 + Delta := by
      simpa [E0, E1, Pbase, Hbase, Ppert, Hpert, hMass0, hMass1,
        t, q, u, Delta] using hsep
    linarith
  have hSharpEq :
      sharpATELength Hbase g (releasedLaw E0)
          (externalLawCellMasses g (E0, Hbase) hE0) =
        sharpATELength Hbase g (releasedLaw Pbase) hMass0 := by
    simpa only [hrel0]
  have hrisk := externalExcessRisk_lower_of_twoPoint g α hα (Qj n m)
    (hTrial n m) (hLog n m) (hInd n m) E0 E1 Hbase Hpert hE0 hE1
    (sharpATELength Hbase g (releasedLaw Pbase) hMass0) Delta
    hSharpEq htheta (by
      simpa [E0, E1, Pbase, Hbase, Ppert, Hpert, hMass0, hMass1,
        t, q, u, Delta] using hsep) hDelta htvEndpoint
  have hcoef : threeScoreFixedLogCertificate α x y z *
      (Real.sqrt (m : ℝ))⁻¹ = Delta * ((1 - 2 * α) / 2) := by
    dsimp [threeScoreFixedLogCertificate, Delta, u, threeScoreCalibratedU]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hcoef]
  exact hrisk

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,hg,α,hα,Qj,hTrial,hLog,hInd,C,hUpper), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLog_logCertificate_liminf
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (hg : Measurable g) (α : ℝ) (hα : 0 < α ∧ α < 1 / 2)
    (Qj : ∀ n m,
      Measure (FullRow ε J) → Measure (ScoreSpace ε) →
        Measure (ExternalSample ε J n m))
    (hTrial : ∀ n m, JointTrialIID g (Qj n m))
    (hLog : ∀ n m, ExternalLogIID g (Qj n m))
    (hInd : ∀ n m, ExternalLogIndependent g (Qj n m))
    (C : ℝ)
    (hUpper : ∀ n m : ℕ, 0 < n → 0 < m →
      externalNormalizer n m * externalExcessRisk g (Qj n m) α ≤ C) :
    logCertificate g α ≤
      liminf (fun m : ℕ => sInf {v : ℝ | ∃ n : ℕ, 0 < n ∧
        v = Real.sqrt (m : ℝ) * externalExcessRisk g (Qj n m) α}) atTop := by
  let K : ℝ := (1 - 2 * α) *
    Real.sqrt (Real.log (1 + (1 - 2 * α) ^ 2)) / (2 * Real.sqrt 3)
  have hβ : 0 < 1 - 2 * α := by linarith [hα.2]
  have hlog : 0 < Real.log (1 + (1 - 2 * α) ^ 2) :=
    Real.log_pos (by nlinarith [sq_pos_of_pos hβ])
  have hK : 0 < K := by dsimp [K]; positivity
  apply le_of_forall_lt
  intro c hc
  have hcK : c / K < fiberTripleSeparation g := by
    apply (div_lt_iff₀ hK).2
    simpa [logCertificate, K, mul_comm] using hc
  let T : Set ℝ := {v | ∃ (r : LabelSpace J)
      (e₁ e₂ e₃ : ScoreSpace ε),
    e₁ < e₂ ∧ e₂ < e₃ ∧ g e₁ = r ∧ g e₂ = r ∧ g e₃ = r ∧
    v = (((e₃ : ℝ) - e₂) * (1 - (e₁ : ℝ) / e₂)) /
      Real.sqrt (((e₃ : ℝ) - e₂) ^ 2 +
        ((e₃ : ℝ) - e₁) ^ 2 + ((e₂ : ℝ) - e₁) ^ 2)}
  have hTne : T.Nonempty := by
    obtain ⟨r, x, y, z, hxy, hyz, hx, hy, hz⟩ :=
      fiberTriple_exists g hOverlap
    exact ⟨_, r, x, y, z, hxy, hyz, hx, hy, hz, rfl⟩
  have hcSup : c / K < sSup T := by
    simpa [fiberTripleSeparation, T] using hcK
  obtain ⟨v, hvT, hcv⟩ := exists_lt_of_lt_csSup hTne hcSup
  rcases hvT with ⟨r, x, y, z, hxy, hyz, hx, hy, hz, rfl⟩
  have hfixed := scoreLogFixedTriple_eventually_externalExcessRisk_lower
    g hOverlap hg r x y z hxy hyz hx hy hz α hα Qj hTrial hLog hInd
  have hlim := externalExcessRisk_log_liminf_of_eventual_uniform
    g Qj α (threeScoreFixedLogCertificate α x y z) C hfixed hUpper
  have hcoeff : K *
      ((((z : ℝ) - y) * (1 - (x : ℝ) / y)) /
        Real.sqrt (((z : ℝ) - y) ^ 2 + ((z : ℝ) - x) ^ 2 +
          ((y : ℝ) - x) ^ 2)) =
      threeScoreFixedLogCertificate α x y z := by
    simp only [threeScoreFixedLogCertificate, threeScoreGapSq, K]
  have hcFixed : c < threeScoreFixedLogCertificate α x y z := by
    have := (div_lt_iff₀ hK).1 hcv
    rw [mul_comm, hcoeff] at this
    exact this
  exact hcFixed.trans_le hlim

end
end CausalSmith.PartialID.UnlinkedPropensityAte
