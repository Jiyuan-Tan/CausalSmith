module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialVanTrees

/-! # Remaining measurable fields for the sequential van Trees adapter -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Causalean.Stat.Minimax.ObservationDependentVanTrees

/-- The centered quartic prior used on the scalar local interval `[-R,R]`. [The sequential VTPrior](goal) is determined by [the displayed parameters](hyp:R). -/
noncomputable def sequentialVTPrior (R : ℝ) : ℝ → ℝ :=
  smoothPrior 0 (R / 2)

/-- The declared derivative of the centered local prior. [The sequential VTPrior Deriv](goal) is determined by [the displayed parameters](hyp:R). -/
noncomputable def sequentialVTPriorDeriv (R : ℝ) : ℝ → ℝ :=
  smoothPriorDeriv 0 (R / 2)

/-- All paper-independent smooth-prior fields needed by van Trees on `[-R,R]`. For the displayed inputs and conditions, this structure records the stated data. [The Sequential VTPrior Facts](goal) is determined by [the displayed parameters](hyp:R). -/
structure SequentialVTPriorFacts (R : ℝ) : Prop where
  contDiff : ContDiff ℝ 1 (sequentialVTPrior R)
  support : Function.support (sequentialVTPrior R) ⊆ Set.Icc (-R) R
  hasDeriv : ∀ a, HasDerivAt (sequentialVTPrior R)
    (sequentialVTPriorDeriv R a) a
  nonneg : ∀ a, 0 ≤ sequentialVTPrior R a
  normalized : ∫ a, sequentialVTPrior R a
    ∂parameterMeasure (-R) R = 1
  scoreSqMeasurable : AEStronglyMeasurable
    (fun a ↦ sequentialVTPrior R a *
      (priorScore (sequentialVTPrior R) (sequentialVTPriorDeriv R) a) ^ 2)
    (parameterMeasure (-R) R)
  scoreSqIntegrable : Integrable
    (fun a ↦ sequentialVTPrior R a *
      (priorScore (sequentialVTPrior R) (sequentialVTPriorDeriv R) a) ^ 2)
    (parameterMeasure (-R) R)
  information : priorInformation (-R) R
    (sequentialVTPrior R) (sequentialVTPriorDeriv R) = 40 / R ^ 2
/-- Under [the supplied quantities and conditions](hyp:hR), [the sequential vt prior facts assertion](goal) holds. -/
lemma sequentialVTPrior_facts {R : ℝ} (hR : 0 < R) :
    SequentialVTPriorFacts R := by
  have ha : 0 < R / 2 := by linarith
  have hleft : -R ≤ (0 : ℝ) - R / 2 := by linarith
  have hright : (0 : ℝ) + R / 2 ≤ R := by linarith
  refine ⟨smoothPrior_contDiff ha, ?_, hasDerivAt_smoothPrior ha,
    smoothPrior_nonneg ha, integral_smoothPrior_parameterMeasure ha hleft hright,
    smoothPrior_scoreSq_aestronglyMeasurable ha,
    smoothPrior_scoreSq_integrable ha, ?_⟩
  · exact support_smoothPrior_subset_Icc ha (by linarith) (by linarith)
  · unfold sequentialVTPrior sequentialVTPriorDeriv
    rw [priorInformation_smoothPrior ha hleft hright]
    field_simp [hR.ne']
    ring

/-- For the supplied quantities and conditions, the vt target is the mathematical object specified below. [The vt Target](goal) is determined by [the displayed parameters](hyp:θ,v,a,_x). -/
def vtTarget {X : Type*} (θ v : TrialParameter) (a : ℝ) (_x : X) : ℝ :=
  contrast θ + a * contrast v

/-- For [the supplied quantities and conditions](hyp:v,_a,_x), the [vt target deriv](goal) is the mathematical object specified below. -/
def vtTargetDeriv {X : Type*} (v : TrialParameter) (_a : ℝ) (_x : X) : ℝ :=
  contrast v

/-- Under [the supplied quantities and conditions](hyp:v), [the vt target eq parameter path assertion](goal) holds. For [the displayed quantities and conditions](hyp:a,x), these specify the stated inputs. -/
lemma vtTarget_eq_parameterPath {X : Type*} (θ v : TrialParameter)
    (a : ℝ) (x : X) :
    vtTarget θ v a x = contrast (parameterPath θ v a) := by
  simp [vtTarget, contrast, parameterPath]
  ring

/-- Under [the supplied quantities and conditions](hyp:v,a,x), [the has deriv at vt target assertion](goal) holds. -/
lemma hasDerivAt_vtTarget {X : Type*} (θ v : TrialParameter) (a : ℝ) (x : X) :
    HasDerivAt (fun b ↦ vtTarget θ v b x) (vtTargetDeriv v a x) a := by
  unfold vtTarget vtTargetDeriv
  simpa only [id_eq, one_mul] using
    ((hasDerivAt_id a).mul_const (contrast v)).const_add (contrast θ)

/-- Under [the supplied quantities and conditions](hyp:v), [the vt target absolutely continuous assertion](goal) holds. For [the displayed quantities and conditions](hyp:x,ell,upper), these specify the stated inputs. -/
lemma vtTarget_absolutelyContinuous {X : Type*} (θ v : TrialParameter)
    (x : X) (ell upper : ℝ) :
    AbsolutelyContinuousOnInterval (fun a ↦ vtTarget θ v a x) ell upper := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  unfold vtTarget
  exact (by fun_prop : ContDiff ℝ 1 (fun a ↦ contrast θ + a * contrast v)).contDiffOn

/-- [the measurable vt density joint assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,ell,upper), these specify the stated inputs. -/
lemma measurable_vtDensity_joint {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (ell upper : ℝ) :
    Measurable (fun az : ℝ × Transcript (Z n) ↦
      vtDensity P θ v p n ell upper az.1 az.2) := by
  unfold vtDensity transcriptMixtureRealDensity
  apply Measurable.ite
  · exact measurableSet_Icc.preimage measurable_fst
  · apply Finset.measurable_fun_sum
    intro x hx
    have hc : Continuous (fun a ↦
        inputPathProbability (parameterPath θ v a) p x) := by
      rw [continuous_iff_continuousAt]
      intro a
      exact (hasDerivAt_inputPathProbability_parameterPath θ v p a x).continuousAt
    exact (hc.measurable.comp measurable_fst).mul
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal.comp measurable_snd)
  · exact measurable_const

-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
/-- [the continuous transcript mixture real derivative path assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,z), these specify the stated inputs. -/
lemma continuous_transcriptMixtureRealDerivative_path {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (z : Transcript (Z n)) :
    Continuous (fun a ↦ transcriptMixtureRealDerivative P
      (parameterPath θ v a) v p n z) := by
  have hcd := (transcriptDensityPath_contDiff P θ v p n z).continuous_deriv (by norm_num)
  have heq : deriv (fun a ↦
      transcriptMixtureRealDensity P (parameterPath θ v a) p n z) =
      fun a ↦ transcriptMixtureRealDerivative P (parameterPath θ v a) v p n z := by
    funext a
    exact (hasDerivAt_transcriptMixtureRealDensity_parameterPath
      P θ v p a n z).deriv
  rwa [heq] at hcd

/-- [the measurable vt density deriv joint assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,ell,upper), these specify the stated inputs. -/
lemma measurable_vtDensityDeriv_joint {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (ell upper : ℝ) :
    Measurable (fun az : ℝ × Transcript (Z n) ↦
      vtDensityDeriv P θ v p n ell upper az.1 az.2) := by
  unfold vtDensityDeriv transcriptMixtureRealDerivative
  apply Measurable.ite
  · exact measurableSet_Icc.preimage measurable_fst
  · apply Finset.measurable_fun_sum
    intro x hx
    have hc : Continuous (fun a ↦
        inputPathDirectionalDerivative (parameterPath θ v a) v p x) := by
      unfold inputPathDirectionalDerivative
      apply continuous_finsetSum
      intro i hi
      apply Continuous.mul continuous_const
      apply continuous_finsetProd
      intro j hj
      rw [continuous_iff_continuousAt]
      intro a
      exact (hasDerivAt_piTheta_parameterPath θ v p a (x j)).continuousAt
    exact (hc.measurable.comp measurable_fst).mul
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal.comp measurable_snd)
  · exact measurable_const

/-- A weighted cross term is integrable whenever both weighted square terms are
integrable.  This is the Cauchy–Schwarz step used for the van Trees error-score
field. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:f,s,q,mu,hf,hs,hq,hq_nonneg,hf_sq,hs_sq), these specify the stated inputs. -/
lemma integrable_mul_mul_of_integrable_sq_mul {A : Type*} [MeasurableSpace A]
    (f s q : A → ℝ) (mu : Measure A)
    (hf : Measurable f) (hs : Measurable s) (hq : Measurable q)
    (hq_nonneg : ∀ x, 0 ≤ q x)
    (hf_sq : Integrable (fun x ↦ f x ^ 2 * q x) mu)
    (hs_sq : Integrable (fun x ↦ s x ^ 2 * q x) mu) :
    Integrable (fun x ↦ f x * s x * q x) mu := by
  let qroot : A → ℝ := fun x ↦ Real.sqrt (q x)
  have hqroot : Measurable qroot :=
    Real.continuous_sqrt.measurable.comp hq
  have hfroot_sq : Integrable (fun x ↦ (f x * qroot x) ^ 2) mu := by
    convert hf_sq using 1
    funext x
    dsimp [qroot]
    rw [mul_pow, Real.sq_sqrt (hq_nonneg x)]
  have hsroot_sq : Integrable (fun x ↦ (s x * qroot x) ^ 2) mu := by
    convert hs_sq using 1
    funext x
    dsimp [qroot]
    rw [mul_pow, Real.sq_sqrt (hq_nonneg x)]
  have hfroot : MemLp (fun x ↦ f x * qroot x) 2 mu :=
    (memLp_two_iff_integrable_sq
      (hf.mul hqroot).aestronglyMeasurable).2 hfroot_sq
  have hsroot : MemLp (fun x ↦ s x * qroot x) 2 mu :=
    (memLp_two_iff_integrable_sq
      (hs.mul hqroot).aestronglyMeasurable).2 hsroot_sq
  have hcross := hfroot.integrable_mul hsroot
  convert hcross using 1
  funext x
  dsimp [qroot]
  have hroot : Real.sqrt (q x) * Real.sqrt (q x) = q x :=
    Real.mul_self_sqrt (hq_nonneg x)
  calc
    f x * s x * q x = f x * s x *
        (Real.sqrt (q x) * Real.sqrt (q x)) := by rw [hroot]
    _ = f x * Real.sqrt (q x) * (s x * Real.sqrt (q x)) := by ring

/-- A nonnegative measurable risk is either integrable or has infinite
Lebesgue integral.  This supplies the harmless infinite-risk branch before
applying the finite-risk van Trees argument. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:F,mu,hF,hF_nonneg), these specify the stated inputs. -/
lemma integrable_or_lintegral_ofReal_eq_top {A : Type*} [MeasurableSpace A]
    (F : A → ℝ) (mu : Measure A) (hF : Measurable F)
    (hF_nonneg : ∀ x, 0 ≤ F x) :
    Integrable F mu ∨ ∫⁻ x, ENNReal.ofReal (F x) ∂mu = ∞ := by
  by_cases h : Integrable F mu
  · exact Or.inl h
  · right
    have hnotfinite : ¬ HasFiniteIntegral F mu := by
      intro hfinite
      exact h ⟨hF.aestronglyMeasurable, hfinite⟩
    have hnotlt : ¬ (∫⁻ x, ENNReal.ofReal ‖F x‖ ∂mu) < ∞ := by
      exact fun hlt ↦ hnotfinite ((hasFiniteIntegral_iff_norm (μ := mu) F).2 hlt)
    have htop : (∫⁻ x, ENNReal.ofReal ‖F x‖ ∂mu) = ∞ :=
      top_unique (not_lt.mp hnotlt)
    convert htop using 1
    apply lintegral_congr
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hF_nonneg x)]

/-- The product-measurability fields required by the observation-dependent van
Trees theorem. For [the displayed quantities and conditions](hyp:w,dw,p,dp,g,dg,T), [the stated result](goal) follows. -/
structure VanTreesProductMeasurable {X : Type*} [MeasurableSpace X]
    (w dw : ℝ → ℝ) (p dp g dg : ℝ → X → ℝ) (T : X → ℝ) : Prop where
  balance : Measurable (derivativeBalanceField w dw p dp g dg T)
  errorScore : Measurable (errorScoreField w dw p dp g T)
  sensitivity : Measurable (sensitivityField w p dg)
  errorSq : Measurable (errorSqField w p g T)
  scoreSq : Measurable (scoreSqField w dw p dp)
  priorJointSq : Measurable (fun z : ℝ × X ↦
    w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2)
  fisherSq : Measurable (fun z : ℝ × X ↦
    w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2)
  cross : Measurable (fun z : ℝ × X ↦
    w z.1 * p z.1 z.2 *
      (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2))

/-- Joint measurability of the primitive density, derivative, target, and
estimator functions supplies every product-measurability side condition in van
Trees. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:w,dw,p,dp,g,dg,T,hw,hdw,hp,hdp,hg,hdg,hT), these specify the stated inputs. -/
lemma vanTreesProductMeasurable_of_joint {X : Type*} [MeasurableSpace X]
    (w dw : ℝ → ℝ) (p dp g dg : ℝ → X → ℝ) (T : X → ℝ)
    (hw : Measurable w) (hdw : Measurable dw)
    (hp : Measurable (fun z : ℝ × X ↦ p z.1 z.2))
    (hdp : Measurable (fun z : ℝ × X ↦ dp z.1 z.2))
    (hg : Measurable (fun z : ℝ × X ↦ g z.1 z.2))
    (hdg : Measurable (fun z : ℝ × X ↦ dg z.1 z.2))
    (hT : Measurable T) :
    VanTreesProductMeasurable w dw p dp g dg T := by
  have hwj : Measurable (fun z : ℝ × X ↦ w z.1) := hw.comp measurable_fst
  have hdwj : Measurable (fun z : ℝ × X ↦ dw z.1) := hdw.comp measurable_fst
  have hTj : Measurable (fun z : ℝ × X ↦ T z.2) := hT.comp measurable_snd
  have hjoint : Measurable (jointDensity w p) := by
    exact hwj.mul hp
  have hprior : Measurable (fun z : ℝ × X ↦ priorScore w dw z.1) := by
    unfold priorScore
    exact Measurable.ite (measurableSet_lt measurable_const hwj)
      (hdwj.div hwj) measurable_const
  have hlike : Measurable (fun z : ℝ × X ↦ likelihoodScore p dp z.1 z.2) := by
    unfold likelihoodScore
    exact Measurable.ite (measurableSet_lt measurable_const hp)
      (hdp.div hp) measurable_const
  have hscore : Measurable (jointScore w dw p dp) := by
    unfold jointScore
    exact Measurable.ite (measurableSet_lt measurable_const hjoint)
      ((hdwj.mul hp |>.add (hwj.mul hdp)).div hjoint) measurable_const
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold derivativeBalanceField
    fun_prop
  · unfold errorScoreField
    exact (hTj.sub hg).mul hscore |>.mul hjoint
  · unfold sensitivityField
    exact hdg.mul hjoint
  · unfold errorSqField
    exact ((hTj.sub hg).pow_const 2).mul hjoint
  · unfold scoreSqField
    exact (hscore.pow_const 2).mul hjoint
  · exact (hwj.mul hp).mul (hprior.pow_const 2)
  · exact (hwj.mul hp).mul (hlike.pow_const 2)
  · exact (hwj.mul hp).mul (hprior.mul hlike)

/-- The sequential mixture likelihood, affine contrast target, and smooth prior
satisfy all van Trees product-measurability conditions for every measurable
transcript estimator. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,v,p,R,n,hR,T,hT), these specify the stated inputs. -/
lemma sequentialVanTreesProductMeasurable {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p R : ℝ) (n : ℕ)
    (hR : 0 < R)
    (T : Transcript (Z n) → ℝ) (hT : Measurable T) :
    VanTreesProductMeasurable
      (sequentialVTPrior R) (sequentialVTPriorDeriv R)
      (vtDensity P θ v p n (-R) R) (vtDensityDeriv P θ v p n (-R) R)
      (vtTarget θ v) (vtTargetDeriv v) T := by
  apply vanTreesProductMeasurable_of_joint
  · exact (smoothPrior_contDiff (a := R / 2) (c := 0) (by linarith)).continuous.measurable
  · unfold sequentialVTPriorDeriv smoothPriorDeriv
    apply Measurable.ite
    · exact measurableSet_lt
        (continuous_abs.comp (continuous_id.sub continuous_const)).measurable
        measurable_const
    · fun_prop
    · exact measurable_const
  · exact measurable_vtDensity_joint P θ v p n (-R) R
  · exact measurable_vtDensityDeriv_joint P θ v p n (-R) R
  · unfold vtTarget
    fun_prop
  · unfold vtTargetDeriv
    exact measurable_const
  · exact hT

/-- Finite weighted squared error and finite joint-score information imply
integrability of the signed error-score field. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:w,dw,p,dp,g,T,mu,hw,hp,hg,hT,hscore,hw_nonneg,hp_nonneg,herrorSq,hscoreSq), these specify the stated inputs. -/
lemma integrable_errorScoreField_of_squares {X : Type*} [MeasurableSpace X]
    (w dw : ℝ → ℝ) (p dp g : ℝ → X → ℝ) (T : X → ℝ)
    (mu : Measure (ℝ × X))
    (hw : Measurable w)
    (hp : Measurable (fun z : ℝ × X ↦ p z.1 z.2))
    (hg : Measurable (fun z : ℝ × X ↦ g z.1 z.2))
    (hT : Measurable T)
    (hscore : Measurable (jointScore w dw p dp))
    (hw_nonneg : ∀ a, 0 ≤ w a) (hp_nonneg : ∀ a x, 0 ≤ p a x)
    (herrorSq : Integrable (errorSqField w p g T) mu)
    (hscoreSq : Integrable (scoreSqField w dw p dp) mu) :
    Integrable (errorScoreField w dw p dp g T) mu := by
  have h := integrable_mul_mul_of_integrable_sq_mul
    (fun z : ℝ × X ↦ T z.2 - g z.1 z.2)
    (jointScore w dw p dp) (jointDensity w p) mu
    ((hT.comp measurable_snd).sub hg) hscore
    ((hw.comp measurable_fst).mul hp)
    (fun z ↦ mul_nonneg (hw_nonneg z.1) (hp_nonneg z.1 z.2))
    herrorSq hscoreSq
  change Integrable (fun z : ℝ × X ↦
    (T z.2 - g z.1 z.2) * jointScore w dw p dp z * jointDensity w p z) mu
  exact h

/-- The centered smooth prior vanishes at both endpoints of the wider local
parameter interval. For [the displayed inputs and conditions](hyp:hR), [the stated result](goal) follows. -/
lemma sequentialVTPrior_endpoints {R : ℝ} (hR : 0 < R) :
    sequentialVTPrior R R = 0 ∧ sequentialVTPrior R (-R) = 0 := by
  unfold sequentialVTPrior
  have h := smoothPrior_ambient_endpoints
    (ell := -R) (u := R) (c := 0) (a := R / 2)
    (by linarith) (by linarith) (by linarith)
  exact ⟨h.2, h.1⟩

end CausalSmith.Stat.LdpAteEfficiencySurface
