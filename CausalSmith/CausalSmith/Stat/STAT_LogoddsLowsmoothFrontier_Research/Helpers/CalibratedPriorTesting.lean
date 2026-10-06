module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FinitePriorHellinger

/-! # Testing bounds from the calibrated mixed and fair supports

The mixed null prior belongs to every radius slice. The random fair prior with
input effect r/2 also belongs to the slice. Their original-record Hellinger
budgets imply length lower bounds through the finite-prior reduction.
-/
public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The null mixed support and the homogeneous alternative yield a lower
bound proportional to the actual mixed amplitude product. [the documented result](goal) Under [the stated assumptions](hyp:hD,hr,hk,hI,hH). -/
-- @node: mixed_prior_length_lower
lemma mixed_prior_length_lower (α β r : ℝ) (n k : ℕ)
    (hD : ExponentDomain α β) (hr : 0 ≤ r) (hk : 1 ≤ k)
    (I : Procedure n) (hI : HonestProcedure n α β I)
    (hH : originalRecordHellinger n
      (mixedMixture false n k (calibEps*(k : ℝ)^(-α)) (calibEps*(k : ℝ)^(-β)))
      (mixedMixture true n k (calibEps*(k : ℝ)^(-α)) (calibEps*(k : ℝ)^(-β))) ≤ 1/100) :
    (7/10 : ℝ)*(32*(calibEps*(k : ℝ)^(-α))*(calibEps*(k : ℝ)^(-β))) ≤
      worstLength n α β r I := by
  let η := calibEps*(k : ℝ)^(-α)
  let ζ := calibEps*(k : ℝ)^(-β)
  have hSupport := calib_constants_spec.2.2.1 α β hD k hk
  dsimp only at hSupport
  have hModels := hSupport.1
  have hP₀ (σ : Fin (k+1) → Bool) : RadiusModel α β r (mixedLaw false k σ η ζ) := by
    refine { (hModels σ).1 with radius := ?_ }
    change |effect (mixedLaw false k σ η ζ)| ≤ r
    rw [(hModels σ).2.2.1, abs_zero]
    exact hr
  have h := finitePrior_hellinger_length_lower n k k α β r 0 (32*η*ζ)
    (fun σ => mixedLaw false k σ η ζ) (fun σ => mixedLaw true k σ η ζ)
    I hI hP₀ (fun σ => (hModels σ).2.1)
    (fun σ => (hModels σ).2.2.1) (fun σ => (hModels σ).2.2.2)
    (fun σ => totalCellLaw_uniform _) (fun σ => totalCellLaw_uniform _) hH
  have hη : 0 ≤ η := mul_nonneg calib_constants_spec.1.le (by positivity)
  have hζ : 0 ≤ ζ := mul_nonneg calib_constants_spec.1.le (by positivity)
  simpa only [sub_zero, abs_of_nonneg (by positivity : 0 ≤ 32*η*ζ)] using h

/-- [The random fair prior is the evaluation prior, even though its effect
exceeds the comparator's effect. The comparator is a constant finite prior. [the documented result](goal) Under [the stated assumptions](hyp:hD,hr,hk,hI,hH). -/
-- @node: fair_prior_length_lower
lemma fair_prior_length_lower (α β r : ℝ) (n k : ℕ)
    (hD : ExponentDomain α β) (hr : r ∈ Set.Icc (0 : ℝ) (1/2)) (hk : 1 ≤ k)
    (I : Procedure n) (hI : HonestProcedure n α β I)
    (hH : originalRecordHellinger n
      (fairMixture n k (r/2) (calibEps*(k : ℝ)^(-β)))
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw
        (fairComparator k (r/2) (calibEps*(k : ℝ)^(-β))).measure n) ≤ 1/100) :
    (7/10 : ℝ)*(3*(r/2)*(calibEps*(k : ℝ)^(-β))^2) ≤ worstLength n α β r I := by
  let t := r/2
  let δ := calibEps*(k : ℝ)^(-β)
  have ht : t ∈ Set.Icc (0 : ℝ) (1/4) := ⟨by dsimp [t]; linarith [hr.1],
    by dsimp [t]; linarith [hr.2]⟩
  have hδ : |δ| ≤ 1/100 :=
    (calibrated_amplitude_abs_le calibEps β calib_constants_spec.1.le hD.1.le k hk).trans
      calib_regularity_spec.1
  have hSupport := (calib_constants_spec.2.2.1 α β hD k hk).2.2 t ht
  have hP₀ (σ : Fin (k+1) → Bool) : RadiusModel α β r (fairLaw k σ t δ) := by
    refine { (hSupport.1 σ).1 with radius := ?_ }
    change |effect (fairLaw k σ t δ)| ≤ r
    rw [(hSupport.1 σ).2, abs_of_nonneg ht.1]
    dsimp [t]
    linarith [hr.1]
  have hH' : originalRecordHellinger n
      (finiteSignMixture n k (fun σ => fairLaw k σ t δ))
      (finiteSignMixture n k (fun _ => fairComparator k t δ)) ≤ 1/100 := by
    rw [finiteSignMixture_const]
    exact hH
  have h := finitePrior_hellinger_length_lower n k k α β r t (comparatorEffect t δ)
    (fun σ => fairLaw k σ t δ) (fun _ => fairComparator k t δ)
    I hI hP₀ (fun _ => hSupport.2.1)
    (fun σ => (hSupport.1 σ).2) (fun _ => hSupport.2.2.1)
    (fun σ => totalCellLaw_uniform _) (fun _ => totalCellLaw_uniform _) hH'
  rw [abs_of_nonpos (sub_nonpos.mpr (comparatorEffect_range_bounds t δ ht hδ).2),
    neg_sub] at h
  exact (mul_le_mul_of_nonneg_left (comparatorEffect_gap_bounds t δ ht hδ).1
    (by norm_num : (0 : ℝ) ≤ 7/10)).trans h

end CausalSmith.Stat.LogoddsLowsmoothFrontier
