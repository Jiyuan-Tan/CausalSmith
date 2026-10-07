module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogFullLaw
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogCalibration
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogSharpATE

/-! Testing control for the actual trial-plus-score-log experiments. -/

public section

open MeasureTheory Set Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,hg,r,x,y,z,hxy,hyz,hx,hy,hz,t,α,hα,hs0,hs1,Qj,hTrial,hLog,hInd), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogCalibrated_jointExperiment_eventually_tv_bound
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (hg : Measurable g) (r : LabelSpace J) (x y z : ScoreSpace ε)
    (hxy : x < y) (hyz : y < z)
    (hx : g x = r) (hy : g y = r) (hz : g z = r)
    (t α : ℝ) (hα : 0 < α ∧ α < 1 / 2)
    (hs0 : 0 ≤ t / (((x : ℝ) + y + z) / 3))
    (hs1 : t / (((x : ℝ) + y + z) / 3) ≤ 1)
    (Qj : ∀ n m,
      Measure (FullRow ε J) → Measure (ScoreSpace ε) →
        Measure (ExternalSample ε J n m))
    (hTrial : ∀ n m, JointTrialIID g (Qj n m))
    (hLog : ∀ n m, ExternalLogIID g (Qj n m))
    (hInd : ∀ n m, ExternalLogIndependent g (Qj n m)) :
    ∀ᶠ m : ℕ in atTop, ∀ n : ℕ,
      let u := threeScoreCalibratedU α x y z m
      let P₀ := scoreLogTripleBaselineFullLaw g x y z
        (t / (((x : ℝ) + y + z) / 3))
      let H₀ := scoreLogTripleBaseline x y z
      let P₁ := scoreLogTriplePerturbedFullLaw g x y z
        (t / (((x : ℝ) + y + z) / 3)) u
      let H₁ := scoreLogTriplePerturbed x y z u
      Causalean.Stat.tvDist (Qj n m P₀ H₀) (Qj n m P₁ H₁) ≤
        (1 - 2 * α) / 2 := by
  filter_upwards [threeScoreCalibratedU_eventually_weights_pos α x y z,
    eventually_gt_atTop (0 : ℕ)] with m hw hm
  intro n
  dsimp only
  let u := threeScoreCalibratedU α x y z m
  let P₀ := scoreLogTripleBaselineFullLaw g x y z
    (t / (((x : ℝ) + y + z) / 3))
  let H₀ := scoreLogTripleBaseline x y z
  let P₁ := scoreLogTriplePerturbedFullLaw g x y z
    (t / (((x : ℝ) + y + z) / 3)) u
  let H₁ := scoreLogTriplePerturbed x y z u
  have hu0 : 0 ≤ u :=
    (threeScoreCalibratedU_pos α hα x y z hxy hyz m hm).le
  have hu : u * ((z : ℝ) - x) ≤ 1 / 3 := by
    dsimp [u] at hw ⊢
    linarith [hw.2.1]
  have hpair := scoreLogTriple_externalPair g hOverlap hg r x y z hxy hyz
    hx hy hz (t / (((x : ℝ) + y + z) / 3)) hs0 hs1 u hu0 hu
  have hPH₀ : (P₀, H₀) ∈ ExternalLaws g := by
    simpa [P₀, H₀] using hpair.1
  have hPH₁ : (P₁, H₁) ∈ ExternalLaws g := by
    simpa [P₁, H₁] using hpair.2.1
  have hrel : releasedLaw P₀ = releasedLaw P₁ := by
    simpa [P₀, P₁] using hpair.2.2
  have hQ (P : Measure (FullRow ε J)) (H : Measure (ScoreSpace ε))
      (hPH : (P, H) ∈ ExternalLaws g) :
      Qj n m P H =
        (Measure.pi (fun _ : Fin n => releasedLaw P)).prod
          (Measure.pi (fun _ : Fin m => H)) := by
    rw [hInd n m (P, H) hPH, hTrial n m (P, H) hPH,
      hLog n m (P, H) hPH]
  rw [hQ P₀ H₀ hPH₀, hQ P₁ H₁ hPH₁]
  let ρ : Measure (Fin n → Observation J) :=
    Measure.pi (fun _ : Fin n => releasedLaw P₀)
  have hPrel : IsProbabilityMeasure (releasedLaw P₀) := by
    exact @Measure.isProbabilityMeasure_map _ _ _ _ P₀ hPH₀.2.2.probabilityP _
      (by unfold releasedRecord label arm observed; fun_prop :
        Measurable (releasedRecord (ε := ε) (J := J))).aemeasurable
  letI : IsProbabilityMeasure (releasedLaw P₀) := hPrel
  letI : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have htv := threeScoreCalibratedU_commonTrial_tv_bound ρ α hα x y z
    hxy hyz m hm hw.1 hw.2.1 hw.2.2
  rw [← hrel]
  rw [Causalean.Stat.tvDist_symm]
  simpa [ρ, H₀, H₁, u, scoreLogTripleBaseline,
    scoreLogTriplePerturbed, threeScoreBaseLaw, threeScorePerturbedLaw] using htv

end
end CausalSmith.PartialID.UnlinkedPropensityAte
