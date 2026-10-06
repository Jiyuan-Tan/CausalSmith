module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.BandCovarianceTrace
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CellAverageContraction
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ConditionalKernelMoments
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CovarianceAssembly
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CovariateKernelMoments
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.FullChainCovariance
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ObservedKernelMoments
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ObservedSecondMoments
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.OperatorCovariance
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ResidualSecondMoment
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RoleOverlap
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RoleVarianceTransport
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.SecondOrderCovariance
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ThirdOrderMoments
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ThirdRoleProjections

/-!
Uniform multiband quadratic-form covariance control without a band-count or sparse-rank loss.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- The numerical covariance certificate used by the explicit tuned procedure. -/
lemma multiband_covariance_public_constant :
    let C : ℝ := 2 ^ 24
    ∀ P : ObsLaw, Model P → ∀ m, 1 ≤ m → ∀ mx my L T J q kt,
      Dyadic mx → Dyadic my → Dyadic L → J = 2 ^ T * L → Dyadic q → q ≤ m →
      (∀ t, t ≤ T → Dyadic (kt t)) → ∀ train : Fin m → Omega,
      ∀ ν : Measure (SampleSpace (13 * m)), SamplingLaw P (13 * m) ν →
      (∀ b a (f : Hj J), -- @realizes f(arbitrary histogram test vector)
        variance (fun eval => inner ℝ (Utwo train mx my L T J kt eval b a) f) (evalLaw P m) ≤
          C * ((m : ℝ)⁻¹ * ‖f‖ ^ 2 + (m : ℝ) ^ (-2 : ℤ) * 
            ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L J t f‖ ^ 2)) ∧
      (∀ b a (f : Hj J),
        variance (fun eval => inner ℝ (Uthree train mx my J q eval b a) f) (evalLaw P m) ≤
          C * (m : ℝ)⁻¹ * ‖f‖ ^ 2) ∧
      (∀ f : Hj J, covarianceForm (contrastCovariance P train mx my L T J q kt) f ≤
        C * ((m : ℝ)⁻¹ * ‖f‖ ^ 2 + (m : ℝ) ^ (-2 : ℤ) * 
          ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L J t f‖ ^ 2)) ∧
      covarianceOpNorm (contrastCovariance P train mx my L T J q kt) ≤ WAllow C m T kt ∧
      covarianceSquareTrace (contrastCovariance P train mx my L T J q kt) ≤ VAllow C m J L T kt :=
    by
  dsimp only
  intro P hModel m hm mx my L T J q kt hmx hmy hL hJ hq hqm hkt train ν hSampling
  subst J
  have hktpos : ∀ t, t ≤ T → 0 < kt t := by
    intro t ht
    obtain ⟨l,hl⟩ := hkt t ht
    rw [hl]
    positivity
  refine ⟨?_, ?_⟩
  · intro b a f
    have h := variance_inner_Utwo_le P hModel hm train mx my L T hL kt hktpos b a f
    apply h.trans
    apply mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ^ 16 ≤ 2 ^ 24)
    exact add_nonneg (by positivity) (mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun t _ => by positivity)))
  · refine ⟨?_, ?_⟩
    · intro b a f
      have hLpos : 0 < L := by obtain ⟨l, rfl⟩ := hL; positivity
      have hqpos : 0 < q := by obtain ⟨l, rfl⟩ := hq; positivity
      have h := variance_inner_Uthree_le P hModel hm train mx my (2 ^ T * L) q
        (by positivity) hqpos hqm b a f
      apply h.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ^ 20 ≤ 2 ^ 24)
          (by positivity : (0 : ℝ) ≤ (m : ℝ)⁻¹)) (sq_nonneg _)
    · suffices hrest :
          (∀ f : Hj (2 ^ T * L),
            covarianceForm (contrastCovariance P train mx my L T (2 ^ T * L) q kt) f ≤
              (2 : ℝ) ^ 24 * ((m : ℝ)⁻¹ * ‖f‖ ^ 2 + (m : ℝ) ^ (-2 : ℤ) *
                ∑ t ∈ Finset.range (T + 1),
                  (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2)) ∧
          covarianceSquareTrace (contrastCovariance P train mx my L T (2 ^ T * L) q kt) ≤
            VAllow (2 ^ 24) m (2 ^ T * L) L T kt by
        exact ⟨hrest.1,
          covarianceOpNorm_le_WAllow_of_multiband (2 ^ 24) (by positivity) m L T hm hL kt
            _ (contrastCovariance_form_nonneg P train mx my L T (2 ^ T * L) q kt) hrest.1,
          hrest.2⟩
      refine ⟨?_, ?_⟩
      · intro f
        have hqpos : 0 < q := by obtain ⟨l, rfl⟩ := hq; positivity
        exact contrastCovariance_form_le_multiband P hModel hm train mx my L T q
          hL hqpos hqm kt hktpos f
      · have hqpos : 0 < q := by obtain ⟨l, rfl⟩ := hq; positivity
        exact covarianceSquareTrace_le_VAllow_of_multiband (2 ^ 24) m L T hm hL kt _
          (contrastCovariance_posSemidef P train mx my L T (2 ^ T * L) q kt)
          (fun f => contrastCovariance_form_le_multiband P hModel hm train mx my L T q
            hL hqpos hqm kt hktpos f)

-- @node: thm:multiband-covariance
/-- Every trained realization has the stated second- and third-order covariance bounds;
the complete corrected contrast has the same multiband envelope, operator and trace bounds. -/
theorem multiband_covariance :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(universal positive covariance constant)
    ∀ P : ObsLaw, Model P → ∀ m, 1 ≤ m → ∀ mx my L T J q kt,
      Dyadic mx → Dyadic my → Dyadic L → J = 2 ^ T * L → Dyadic q → q ≤ m →
      (∀ t, t ≤ T → Dyadic (kt t)) → ∀ train : Fin m → Omega,
      ∀ ν : Measure (SampleSpace (13 * m)), SamplingLaw P (13 * m) ν →
      (∀ b a (f : Hj J), -- @realizes f(arbitrary histogram test vector)
        variance (fun eval => inner ℝ (Utwo train mx my L T J kt eval b a) f) (evalLaw P m) ≤
          C * ((m : ℝ)⁻¹ * ‖f‖ ^ 2 + (m : ℝ) ^ (-2 : ℤ) * 
            ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L J t f‖ ^ 2)) ∧
      (∀ b a (f : Hj J),
        variance (fun eval => inner ℝ (Uthree train mx my J q eval b a) f) (evalLaw P m) ≤
          C * (m : ℝ)⁻¹ * ‖f‖ ^ 2) ∧
      (∀ f : Hj J, covarianceForm (contrastCovariance P train mx my L T J q kt) f ≤
        C * ((m : ℝ)⁻¹ * ‖f‖ ^ 2 + (m : ℝ) ^ (-2 : ℤ) * 
          ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L J t f‖ ^ 2)) ∧
      covarianceOpNorm (contrastCovariance P train mx my L T J q kt) ≤ WAllow C m T kt ∧
      covarianceSquareTrace (contrastCovariance P train mx my L T J q kt) ≤
        VAllow C m J L T kt := by
  exact ⟨2 ^ 24, by positivity, multiband_covariance_public_constant⟩

end CausalSmith.Stat.DensityEffectRoughNull
