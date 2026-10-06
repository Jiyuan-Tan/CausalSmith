module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Covariance
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.MarkedDomination

/-!
# Population bridges for the finite certificate

This file isolates the product-law reduction used by the single-observation
calculations.  In particular, reflecting the Gaussian error for either arm
does not change its law or its independence from the latent schedule.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- The part of a latent observation independent of the measurement error. Given [the displayed inputs and assumptions](hyp:ω), [this definition specifies the stated object](goal). -/
@[no_expose]
def latentSchedule (ω : Latent) : ℝ × Bool × Bool :=
  (score ω, ω.2.1, ω.2.2.1)

/-- Given the displayed inputs, [the stated mathematical conclusion holds](goal). -/
lemma latentSchedule_measurable : Measurable latentSchedule := by
  unfold latentSchedule score
  fun_prop

/-- The [first coordinate of the latent schedule](goal) is the latent score. Given [the latent observation](hyp:ω), this records the defining projection identity. -/
@[simp] lemma latentSchedule_fst (ω : Latent) : (latentSchedule ω).1 = score ω := by
  rfl

/-- Pull an observed integral back to the latent law. Given [the displayed inputs and assumptions](hyp:Q,σ,H,hH), [the stated mathematical conclusion holds](goal). -/
lemma integral_Pobs_eq_integral_obs_comp (Q : LatentLaw) (σ : ℝ)
    (H : Obs → ℝ) (hH : AEStronglyMeasurable H (Pobs Q σ)) :
    (∫ o, H o ∂Pobs Q σ) = ∫ ω, H (obs σ ω) ∂Q.P := by
  exact integral_map (obs_measurable σ).aemeasurable hH

/-- On the independent schedule/Gaussian product, the inverse-heat evaluation
at the reflected compactly-supported score is square integrable. Given [the displayed inputs and assumptions](hyp:hherm,Q,d,J,σ), [the stated mathematical conclusion holds](goal). -/
lemma inverseHeat_schedule_gaussian_memLp_two (hherm : ClassicalHermiteFacts)
    (Q : LatentLaw) (d : Bool) (J : ℕ) (σ : ℝ) :
    MemLp (fun sz : (ℝ × Bool × Bool) × ℝ =>
      (inverseHeat J σ).eval (sgn d * sz.1.1 + σ * sz.2)) 2
      ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) := by
  letI : IsProbabilityMeasure Q.P := Q.prob
  letI : IsProbabilityMeasure (Q.P.map latentSchedule) :=
    Measure.isProbabilityMeasure_map latentSchedule_measurable.aemeasurable
  have hsupp : ∀ᵐ s ∂Q.P.map latentSchedule, s.1 ∈ Icc (-1 : ℝ) 1 := by
    rw [ae_map_iff latentSchedule_measurable.aemeasurable
      (measurableSet_Icc.preimage measurable_fst)]
    simpa [latentSchedule] using Q.supp
  have hmode (j : ℕ) : MemLp (fun sz : (ℝ × Bool × Bool) × ℝ =>
      (σ ^ j * (polyDeriv j (endpointKernel J)).eval (sgn d * sz.1.1) /
        (Nat.factorial j : ℝ)) *
        (Polynomial.aeval sz.2 (Polynomial.hermite j) : ℝ)) 2
      ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) := by
    let c : (ℝ × Bool × Bool) → ℝ := fun s =>
      σ ^ j * (polyDeriv j (endpointKernel J)).eval (sgn d * s.1) /
        (Nat.factorial j : ℝ)
    have hcmeas : Measurable c := by
      dsimp [c]
      fun_prop
    have hccont : ContinuousOn (fun x : ℝ =>
        σ ^ j * (polyDeriv j (endpointKernel J)).eval (sgn d * x) /
          (Nat.factorial j : ℝ)) (Icc (-1 : ℝ) 1) := by
      fun_prop
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hccont
    have hcTop : MemLp c ⊤ (Q.P.map latentSchedule) := by
      apply memLp_top_of_bound hcmeas.aestronglyMeasurable C
      filter_upwards [hsupp] with s hs
      exact hC s.1 hs
    have hcProd : MemLp (fun sz : (ℝ × Bool × Bool) × ℝ => c sz.1) ⊤
        ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) :=
      hcTop.comp_measurePreserving measurePreserving_fst
    have hhProd : MemLp (fun sz : (ℝ × Bool × Bool) × ℝ =>
        (Polynomial.aeval sz.2 (Polynomial.hermite j) : ℝ)) 2
        ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) :=
      (hermite_memLp_two hherm j).comp_measurePreserving measurePreserving_snd
    change MemLp ((fun sz : (ℝ × Bool × Bool) × ℝ => c sz.1) *
      fun sz => (Polynomial.aeval sz.2 (Polynomial.hermite j) : ℝ)) 2 _
    exact hhProd.mul hcProd
  have hsum : MemLp (fun sz : (ℝ × Bool × Bool) × ℝ =>
      ∑ j ∈ Finset.range (kernelDegree J + 1),
        (σ ^ j * (polyDeriv j (endpointKernel J)).eval (sgn d * sz.1.1) /
          (Nat.factorial j : ℝ)) *
          (Polynomial.aeval sz.2 (Polynomial.hermite j) : ℝ)) 2
      ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) :=
    memLp_finsetSum _ (fun j _ => hmode j)
  have hexp (sz : (ℝ × Bool × Bool) × ℝ) :
      (inverseHeat J σ).eval (sgn d * sz.1.1 + σ * sz.2) =
        ∑ j ∈ Finset.range (kernelDegree J + 1),
          (σ ^ j * (polyDeriv j (endpointKernel J)).eval (sgn d * sz.1.1) /
            (Nat.factorial j : ℝ)) *
            (Polynomial.aeval sz.2 (Polynomial.hermite j) : ℝ) := by
    rw [inverseHeat_eq_finiteInverseHeat]
    exact finiteInverseHeat_hermite_expansion (endpointKernel J) (kernelDegree J)
      (endpointKernel_natDegree_le J) (sgn d * sz.1.1) σ sz.2
  simpa only [hexp] using hsum

/-- Given [the displayed inputs and assumptions](hyp:d), [the stated mathematical conclusion holds](goal). -/
lemma signedError_measurable (d : Bool) :
    Measurable (fun ω : Latent => sgn d * errorCoord ω) := by
  unfold errorCoord
  fun_prop

/-- Reflecting the proxy splits into the reflected score and the reflected
error with the original nonnegative noise scale. Given [the displayed inputs and assumptions](hyp:d,σ,ω), [the stated mathematical conclusion holds](goal). -/
lemma sgn_mul_proxy (d : Bool) (σ : ℝ) (ω : Latent) :
    sgn d * proxy σ ω =
      sgn d * score ω + σ * (sgn d * errorCoord ω) := by
  unfold proxy
  ring

/-- On an observation assigned to arm `d`, the observed binary mark is exactly
the corresponding latent potential. Given [the displayed inputs and assumptions](hyp:d,ω), [the stated mathematical conclusion holds](goal). -/
lemma arm_indicator_outcome_eq_pot (d : Bool) (ω : Latent) :
    (if side ω = d then (1 : ℝ) else 0) * bit (outcome ω) =
      (if side ω = d then (1 : ℝ) else 0) * pot d ω := by
  by_cases hs : side ω = d
  · cases d <;> simp_all [outcome, pot]
  · simp [hs]

/-- Given [the displayed inputs and assumptions](hyp:d), [the stated mathematical conclusion holds](goal). -/
lemma pot_measurable (d : Bool) : Measurable (pot d) := by
  have hb : Measurable bit := measurable_of_countable bit
  cases d
  · change Measurable (fun ω : Latent => bit ω.2.1)
    exact hb.comp measurable_snd.fst
  · change Measurable (fun ω : Latent => bit ω.2.2.1)
    exact hb.comp measurable_snd.snd.fst

/-- Given [the displayed inputs and assumptions](hyp:d,ω), [the stated mathematical conclusion holds](goal). -/
lemma pot_nonneg (d : Bool) (ω : Latent) : 0 ≤ pot d ω := by
  cases d
  · cases h : ω.2.1 <;> simp [pot, bit, h]
  · cases h : ω.2.2.1 <;> simp [pot, bit, h]

/-- The conditional-mean density is globally measurable even though the
version itself is only controlled on the score support. Given [the displayed inputs and assumptions](hyp:β,σ,Q,hQ,d), [the stated mathematical conclusion holds](goal). -/
lemma mu_mul_f_measurable (β σ : ℝ) (Q : LatentLaw) (hQ : Model β σ Q)
    (d : Bool) : Measurable (fun x => Q.mu d x * Q.f x) := by
  have hc : ContinuousOn (fun x => Q.mu d x * Q.f x) (Icc (-1 : ℝ) 1) :=
    (Q.mu_cont d).mul Q.f_cont
  have heq : (fun x => Q.mu d x * Q.f x) =
      (Icc (-1 : ℝ) 1).piecewise (fun x => Q.mu d x * Q.f x) 0 := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · simp [hx]
    · simp [hx, Q.f_zero x hx]
  rw [heq]
  exact hc.measurable_piecewise continuous_const.continuousOn measurableSet_Icc

/-- Given [the displayed inputs and assumptions](hyp:Q), [the stated mathematical conclusion holds](goal). -/
lemma density_measurable (Q : LatentLaw) : Measurable Q.f := by
  have heq : Q.f = (Icc (-1 : ℝ) 1).piecewise Q.f 0 := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · simp [hx]
    · simp [hx, Q.f_zero x hx]
  rw [heq]
  exact Q.f_cont.measurable_piecewise continuous_const.continuousOn measurableSet_Icc

/-- Given [the displayed inputs and assumptions](hyp:β,σ,Q,hQ,d,x), [the stated mathematical conclusion holds](goal). -/
lemma mu_mul_f_nonneg (β σ : ℝ) (Q : LatentLaw) (hQ : Model β σ Q)
    (d : Bool) (x : ℝ) : 0 ≤ Q.mu d x * Q.f x := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · exact mul_nonneg (le_trans (by norm_num) (hQ.means d x hx).1) (Q.f_nonneg x)
  · rw [Q.f_zero x hx, mul_zero]

/-- Given [the displayed inputs and assumptions](hyp:β,σ,Q,hQ,d), [the stated mathematical conclusion holds](goal). -/
lemma mu_mul_f_integrable (β σ : ℝ) (Q : LatentLaw) (hQ : Model β σ Q)
    (d : Bool) : Integrable (fun x => Q.mu d x * Q.f x) := by
  have hc : ContinuousOn (fun x => Q.mu d x * Q.f x) (Icc (-1 : ℝ) 1) :=
    (Q.mu_cont d).mul Q.f_cont
  have heq : (fun x => Q.mu d x * Q.f x) =
      (Icc (-1 : ℝ) 1).indicator (fun x => Q.mu d x * Q.f x) := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · simp [hx]
    · simp [hx, Q.f_zero x hx]
  rw [heq]
  exact (integrable_indicator_iff measurableSet_Icc).2 hc.integrableOn_Icc

/-- The finite measure obtained by weighting the latent law by a binary
potential outcome. Given [the displayed inputs and assumptions](hyp:Q,d), [this definition specifies the stated object](goal). -/
@[no_expose]
def potentialWeightedLaw (Q : LatentLaw) (d : Bool) : Measure Latent :=
  Q.P.withDensity (fun ω => ENNReal.ofReal (pot d ω))

/-- The score pushforward of the potential-weighted latent law has density
`mu d * f`.  This promotes the eventwise `mu_version` axiom to a measure
identity that can be integrated against arbitrary measurable weights. Given [the displayed inputs and assumptions](hyp:β,σ,Q,hQ,d), [the stated mathematical conclusion holds](goal). -/
lemma potentialWeightedLaw_map_score (β σ : ℝ) (Q : LatentLaw)
    (hQ : Model β σ Q) (d : Bool) :
    (potentialWeightedLaw Q d).map score =
      volume.withDensity (fun x => ENNReal.ofReal (Q.mu d x * Q.f x)) := by
  letI : IsProbabilityMeasure Q.P := Q.prob
  apply Measure.ext
  intro B hB
  have hs : Measurable score := by
    unfold score
    fun_prop
  rw [Measure.map_apply hs hB]
  unfold potentialWeightedLaw
  rw [withDensity_apply _ (hs hB)]
  rw [withDensity_apply _ hB]
  have hpint : Integrable (pot d) Q.P := by
    apply Integrable.of_bound (pot_measurable d).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω => by
      cases d
      · cases h : ω.2.1 <;> simp [pot, bit, h]
      · cases h : ω.2.2.1 <;> simp [pot, bit, h]
  have hgint := mu_mul_f_integrable β σ Q hQ d
  rw [← ofReal_integral_eq_lintegral_ofReal hpint.integrableOn
      (Filter.Eventually.of_forall fun ω => pot_nonneg d ω),
    ← ofReal_integral_eq_lintegral_ofReal hgint.integrableOn
      (Filter.Eventually.of_forall fun x => mu_mul_f_nonneg β σ Q hQ d x)]
  congr 1
  have hv := Q.mu_version d B hB
  change (∫ ω in score ⁻¹' B, pot d ω ∂Q.P) =
    ∫ x in B ∩ Icc (-1 : ℝ) 1, Q.mu d x * Q.f x at hv
  rw [hv]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hB inter_subset_left
  intro x hx
  have hout : x ∉ Icc (-1 : ℝ) 1 := by
    intro hin
    exact hx.2 ⟨hx.1, hin⟩
  rw [Q.f_zero x hout, mul_zero]

/-- The eventwise conditional-mean identity integrates against every
measurable real score weight.  Integrability is handled by the Bochner
integral convention and can be strengthened separately when needed. Given [the displayed inputs and assumptions](hyp:β,σ,Q,hQ,d,w,hw), [the stated mathematical conclusion holds](goal). -/
lemma integral_scoreWeight_mul_pot (β σ : ℝ) (Q : LatentLaw)
    (hQ : Model β σ Q) (d : Bool) (w : ℝ → ℝ) (hw : Measurable w) :
    (∫ ω, w (score ω) * pot d ω ∂Q.P) =
      ∫ x, w x * (Q.mu d x * Q.f x) := by
  have hs : Measurable score := by
    unfold score
    fun_prop
  have hpmeas : Measurable (fun ω => ENNReal.ofReal (pot d ω)) :=
    (pot_measurable d).ennreal_ofReal
  have hgmeas : Measurable (fun x => ENNReal.ofReal (Q.mu d x * Q.f x)) :=
    (mu_mul_f_measurable β σ Q hQ d).ennreal_ofReal
  calc
    (∫ ω, w (score ω) * pot d ω ∂Q.P) =
        ∫ ω, w (score ω) ∂potentialWeightedLaw Q d := by
          unfold potentialWeightedLaw
          rw [integral_withDensity_eq_integral_toReal_smul hpmeas
            (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) ]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by
            change w (score ω) * pot d ω =
              (ENNReal.ofReal (pot d ω)).toReal * w (score ω)
            rw [ENNReal.toReal_ofReal (pot_nonneg d ω)]
            ring
    _ = ∫ x, w x ∂(potentialWeightedLaw Q d).map score := by
          exact (integral_map hs.aemeasurable hw.aestronglyMeasurable).symm
    _ = ∫ x, w x ∂volume.withDensity
        (fun x => ENNReal.ofReal (Q.mu d x * Q.f x)) := by
          rw [potentialWeightedLaw_map_score β σ Q hQ d]
    _ = ∫ x, w x * (Q.mu d x * Q.f x) := by
          rw [integral_withDensity_eq_integral_toReal_smul hgmeas
            (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            change (ENNReal.ofReal (Q.mu d x * Q.f x)).toReal * w x =
              w x * (Q.mu d x * Q.f x)
            rw [ENNReal.toReal_ofReal (mu_mul_f_nonneg β σ Q hQ d x)]
            ring

/-- The ordinary score-density identity also integrates against every
measurable real weight. Given [the displayed inputs and assumptions](hyp:Q,w,hw), [the stated mathematical conclusion holds](goal). -/
lemma integral_scoreWeight (Q : LatentLaw) (w : ℝ → ℝ) (hw : Measurable w) :
    (∫ ω, w (score ω) ∂Q.P) = ∫ x, w x * Q.f x := by
  have hs : Measurable score := by
    unfold score
    fun_prop
  calc
    (∫ ω, w (score ω) ∂Q.P) = ∫ x, w x ∂Q.P.map score := by
      exact (integral_map hs.aemeasurable hw.aestronglyMeasurable).symm
    _ = ∫ x, w x ∂volume.withDensity (fun x => ENNReal.ofReal (Q.f x)) := by
      rw [Q.density]
    _ = ∫ x, w x * Q.f x := by
      rw [integral_withDensity_eq_integral_toReal_smul
        (density_measurable Q).ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change (ENNReal.ofReal (Q.f x)).toReal * w x = w x * Q.f x
        rw [ENNReal.toReal_ofReal (Q.f_nonneg x)]
        ring

/-- A score law with a Lebesgue density has no atom at the cutoff. Given [the displayed inputs and assumptions](hyp:Q), [the stated mathematical conclusion holds](goal). -/
lemma score_eq_zero_null (Q : LatentLaw) : Q.P {ω | score ω = 0} = 0 := by
  have hs : Measurable score := by
    unfold score
    fun_prop
  have hsingle : (volume : Measure ℝ) ({0} : Set ℝ) = 0 := measure_singleton 0
  have hac := withDensity_absolutelyContinuous volume
    (fun x => ENNReal.ofReal (Q.f x))
  calc
    Q.P {ω | score ω = 0} = Q.P (score ⁻¹' ({0} : Set ℝ)) := by rfl
    _ = (Q.P.map score) ({0} : Set ℝ) :=
      (Measure.map_apply hs (s := ({0} : Set ℝ))
        (measurableSet_singleton (0 : ℝ))).symm
    _ = (volume.withDensity (fun x => ENNReal.ofReal (Q.f x))) {0} := by rw [Q.density]
    _ = 0 := hac hsingle

/-- Apart from the null cutoff atom, true-side assignment is exactly membership
of the reflected score in `[0,1]`. Given [the displayed inputs and assumptions](hyp:Q,d), [the stated mathematical conclusion holds](goal). -/
lemma arm_indicator_ae_eq_reflected_Icc (Q : LatentLaw) (d : Bool) :
    (fun ω => if side ω = d then (1 : ℝ) else 0) =ᵐ[Q.P]
      fun ω => if sgn d * score ω ∈ Icc (0 : ℝ) 1 then 1 else 0 := by
  have hzero : ∀ᵐ ω ∂Q.P, ω ∉ {ω | score ω = 0} :=
    (measure_eq_zero_iff_ae_notMem).1 (score_eq_zero_null Q)
  filter_upwards [Q.supp, hzero] with ω hsupp hne
  have hs0 : score ω ≠ 0 := by simpa only [Set.mem_setOf_eq, not_false_eq_true] using hne
  unfold side sgn
  cases d
  · change (if decide (0 ≤ score ω) = false then (1 : ℝ) else 0) =
      if (if false = true then 1 else -1) * score ω ∈ Icc (0 : ℝ) 1 then 1 else 0
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    have hcases : score ω < 0 ∨ 0 < score ω := lt_or_gt_of_ne hs0
    rcases hcases with hneg | hpos
    · have hnside : ¬0 ≤ score ω := by linarith
      have href0 : 0 ≤ -score ω := by linarith
      have href1 : -score ω ≤ 1 := by linarith [hsupp.1]
      simp [hnside, href0, href1]
    · have hside : 0 ≤ score ω := hpos.le
      have hnref : ¬0 ≤ -score ω := by linarith
      simp [hside, hnref]
  · change (if decide (0 ≤ score ω) = true then (1 : ℝ) else 0) =
      if (if true = true then 1 else -1) * score ω ∈ Icc (0 : ℝ) 1 then 1 else 0
    simp only [↓reduceIte, one_mul]
    by_cases h : 0 ≤ score ω
    · simp [h, hsupp.2]
    · simp [h]

/-- The inverse-heat evaluation of one observed proxy is square integrable. Given [the displayed inputs and assumptions](hyp:hherm,β,σ,Q,hQ,d,J), [the stated mathematical conclusion holds](goal). -/
lemma inverseHeat_proxy_memLp_two (hherm : ClassicalHermiteFacts)
    (β σ : ℝ) (Q : LatentLaw) (hQ : Model β σ Q) (d : Bool) (J : ℕ) :
    MemLp (fun o : Obs => (inverseHeat J σ).eval (sgn d * o.1)) 2
      (Pobs Q σ) := by
  letI : IsProbabilityMeasure Q.P := Q.prob
  letI : IsProbabilityMeasure (Q.P.map latentSchedule) :=
    Measure.isProbabilityMeasure_map latentSchedule_measurable.aemeasurable
  have hm : Measurable (fun ω : Latent =>
      (latentSchedule ω, sgn d * errorCoord ω)) :=
    latentSchedule_measurable.prodMk (signedError_measurable d)
  have hmp : MeasurePreserving
      (fun ω : Latent => (latentSchedule ω, sgn d * errorCoord ω)) Q.P
      ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) := by
    refine ⟨hm, ?_⟩
    have hi : IndepFun latentSchedule
        (fun ω : Latent => sgn d * errorCoord ω) Q.P := by
      unfold latentSchedule
      simpa only [Function.comp_def] using
        (hQ.independent.comp
          (by fun_prop : Measurable (fun x : ℝ => sgn d * x))
          (by fun_prop : Measurable (fun x : ℝ × Bool × Bool => x))).symm
    rw [hi.map_prod_eq_prod_map_map latentSchedule_measurable.aemeasurable
      (signedError_measurable d).aemeasurable]
    have he : Measurable errorCoord := by
      unfold errorCoord
      fun_prop
    cases d with
    | false =>
        rw [show (fun ω : Latent => sgn false * errorCoord ω) =
            (fun x : ℝ => -x) ∘ errorCoord by funext ω; simp [sgn] ]
        rw [← Measure.map_map (by fun_prop : Measurable (fun x : ℝ => -x)) he,
          show Q.P.map errorCoord = gaussianReal 0 1 from hQ.gaussian,
          gaussianReal_map_neg]
        norm_num
    | true =>
        rw [show Q.P.map (fun ω => sgn true * errorCoord ω) =
          gaussianReal 0 1 by simpa [sgn, GaussianError] using hQ.gaussian]
  have hlatent := (inverseHeat_schedule_gaussian_memLp_two hherm Q d J σ).comp_measurePreserving hmp
  have hobs : AEStronglyMeasurable
      (fun o : Obs => (inverseHeat J σ).eval (sgn d * o.1)) (Pobs Q σ) := by
    fun_prop
  apply (memLp_map_measure_iff hobs (obs_measurable σ).aemeasurable).2
  change MemLp (fun ω : Latent =>
    (inverseHeat J σ).eval (sgn d * proxy σ ω)) 2 Q.P
  convert hlatent using 1
  funext ω
  exact congrArg (inverseHeat J σ).eval (sgn_mul_proxy d σ ω)

/-- Both arm-weighted observed summands inherit square integrability from the
unweighted inverse-heat proxy. Given [the displayed inputs and assumptions](hyp:hherm,β,σ,Q,hQ,d,J), [the stated mathematical conclusion holds](goal). -/
lemma observed_arm_summands_memLp_two (hherm : ClassicalHermiteFacts)
    (β σ : ℝ) (Q : LatentLaw) (hQ : Model β σ Q) (d : Bool) (J : ℕ) :
    MemLp (fun o : Obs => (if o.2.1 = d then 1 else 0) * bit o.2.2 *
      (inverseHeat J σ).eval (sgn d * o.1)) 2 (Pobs Q σ) ∧
    MemLp (fun o : Obs => (if o.2.1 = d then 1 else 0) *
      (inverseHeat J σ).eval (sgn d * o.1)) 2 (Pobs Q σ) := by
  have hbase := inverseHeat_proxy_memLp_two hherm β σ Q hQ d J
  have hiMeas : Measurable (fun o : Obs => if o.2.1 = d then (1 : ℝ) else 0) := by
    exact measurable_const.ite
      ((measurableSet_singleton d).preimage measurable_snd.fst) measurable_const
  have hbMeas : Measurable (fun o : Obs => bit o.2.2) := by
    exact (measurable_of_countable bit).comp measurable_snd.snd
  have hiTop : MemLp (fun o : Obs => if o.2.1 = d then (1 : ℝ) else 0) ⊤
      (Pobs Q σ) := by
    apply memLp_top_of_bound hiMeas.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun o => by split_ifs <;> norm_num
  have hibTop : MemLp (fun o : Obs =>
      (if o.2.1 = d then (1 : ℝ) else 0) * bit o.2.2) ⊤ (Pobs Q σ) := by
    apply memLp_top_of_bound (hiMeas.mul hbMeas).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun o => by
      cases h : o.2.2 <;> simp [bit, h] <;> split_ifs <;> norm_num
  constructor
  · change MemLp ((fun o : Obs =>
      (if o.2.1 = d then (1 : ℝ) else 0) * bit o.2.2) *
        fun o => (inverseHeat J σ).eval (sgn d * o.1)) 2 (Pobs Q σ)
    exact hbase.mul hibTop
  · change MemLp ((fun o : Obs => if o.2.1 = d then (1 : ℝ) else 0) *
        fun o => (inverseHeat J σ).eval (sgn d * o.1)) 2 (Pobs Q σ)
    exact hbase.mul hiTop

/-- Reflection into either treatment arm preserves the standard Gaussian
error marginal. Given [the displayed inputs and assumptions](hyp:Q,hQ,d), [the stated mathematical conclusion holds](goal). -/
lemma signedError_map_eq_gaussian (Q : LatentLaw) (hQ : GaussianError Q)
    (d : Bool) :
    Q.P.map (fun ω => sgn d * errorCoord ω) = gaussianReal 0 1 := by
  have he : Measurable errorCoord := by
    unfold errorCoord
    fun_prop
  cases d with
  | false =>
      rw [show (fun ω : Latent => sgn false * errorCoord ω) =
          (fun x : ℝ => -x) ∘ errorCoord by funext ω; simp [sgn] ]
      rw [← Measure.map_map (by fun_prop : Measurable (fun x : ℝ => -x)) he,
        show Q.P.map errorCoord = gaussianReal 0 1 from hQ,
        gaussianReal_map_neg]
      norm_num
  | true =>
      simpa [sgn, GaussianError] using hQ

/-- The same factorization with the schedule first, convenient for applying
the Gaussian covariance identities as inner integrals. Given [the displayed inputs and assumptions](hyp:β,σ,Q,hQ,d), [the stated mathematical conclusion holds](goal). -/
lemma latentSchedule_signedError_jointLaw (β σ : ℝ) (Q : LatentLaw)
    (hQ : Model β σ Q) (d : Bool) :
    Q.P.map (fun ω => (latentSchedule ω, sgn d * errorCoord ω)) =
      (Q.P.map latentSchedule).prod (gaussianReal 0 1) := by
  letI : IsProbabilityMeasure Q.P := Q.prob
  have hi : IndepFun latentSchedule
      (fun ω : Latent => sgn d * errorCoord ω) Q.P := by
    exact (by
      unfold latentSchedule
      simpa only [Function.comp_def] using
        (hQ.independent.comp
          (by fun_prop : Measurable (fun x : ℝ => sgn d * x))
          (by fun_prop : Measurable (fun x : ℝ × Bool × Bool => x))).symm)
  rw [hi.map_prod_eq_prod_map_map latentSchedule_measurable.aemeasurable
    (signedError_measurable d).aemeasurable]
  rw [signedError_map_eq_gaussian Q hQ.gaussian d]

/-- Schedule-first Fubini reduction, matching the shape of
`exact_covariance`. Given [the displayed inputs and assumptions](hyp:β,σ,Q,hQ,d,H,hH), [the stated mathematical conclusion holds](goal). -/
lemma integral_latentSchedule_signedError (β σ : ℝ) (Q : LatentLaw)
    (hQ : Model β σ Q) (d : Bool) (H : (ℝ × Bool × Bool) × ℝ → ℝ)
    (hH : Integrable H ((Q.P.map latentSchedule).prod (gaussianReal 0 1))) :
    (∫ ω, H (latentSchedule ω, sgn d * errorCoord ω) ∂Q.P) =
      ∫ s, ∫ z, H (s, z) ∂gaussianReal 0 1 ∂Q.P.map latentSchedule := by
  letI : IsProbabilityMeasure Q.P := Q.prob
  have hm : Measurable (fun ω : Latent =>
      (latentSchedule ω, sgn d * errorCoord ω)) :=
    latentSchedule_measurable.prodMk (signedError_measurable d)
  have hj := latentSchedule_signedError_jointLaw β σ Q hQ d
  have hHmap : Integrable H
      (Q.P.map (fun ω => (latentSchedule ω, sgn d * errorCoord ω))) := by
    rw [hj]
    exact hH
  rw [← integral_map hm.aemeasurable hHmap.aestronglyMeasurable]
  rw [hj]
  exact integral_prod H hH

/-- Reflection sends either arm's compact score half to the common endpoint
interval, with the cutoff discrepancy already absorbed by Lebesgue nullity. Given [the displayed inputs and assumptions](hyp:d,g), [the stated mathematical conclusion holds](goal). -/
lemma reflected_Icc_integral (d : Bool) (g : ℝ → ℝ) :
    (∫ x, (if sgn d * x ∈ Icc (0 : ℝ) 1 then 1 else 0) * g (sgn d * x)) =
      ∫ x in (0 : ℝ)..1, g x := by
  have hset : (∫ x in Icc (0 : ℝ) 1, g x) = ∫ x in (0 : ℝ)..1, g x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  cases d
  · have href := integral_neg_eq_self
        (fun x : ℝ => (if x ∈ Icc (0 : ℝ) 1 then 1 else 0) * g x) volume
    rw [show (fun x : ℝ =>
        (if sgn false * x ∈ Icc (0 : ℝ) 1 then 1 else 0) * g (sgn false * x)) =
      (fun x : ℝ => (if x ∈ Icc (0 : ℝ) 1 then 1 else 0) * g x) ∘
        fun x => -x by funext x; simp [sgn]]
    change (∫ x : ℝ, (if -x ∈ Icc (0 : ℝ) 1 then 1 else 0) * g (-x)) = _
    rw [href]
    rw [show (fun x : ℝ => (if x ∈ Icc (0 : ℝ) 1 then 1 else 0) * g x) =
      (Icc (0 : ℝ) 1).indicator g by funext x; by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [hx]]
    rw [integral_indicator measurableSet_Icc, hset]
  · simp only [sgn, ↓reduceIte, one_mul]
    rw [show (fun x : ℝ => (if x ∈ Icc (0 : ℝ) 1 then 1 else 0) * g x) =
      (Icc (0 : ℝ) 1).indicator g by funext x; by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [hx]]
    rw [integral_indicator measurableSet_Icc, hset]

/-- Exact FC.1 population identity for the unmarked arm summand. Given [the displayed inputs and assumptions](hyp:legendre,hermite,β,σ,Q,hQ,hσ,J,hJ,d), [the stated mathematical conclusion holds](goal). -/
lemma unmarked_observed_integral_eq_endpoint (legendre : ClassicalLegendreFacts)
    (hermite : ClassicalHermiteFacts) (β σ : ℝ) (Q : LatentLaw)
    (hQ : Model β σ Q) (hσ : σ ∈ Icc (0 : ℝ) 1) (J : ℕ) (hJ : 1 ≤ J)
    (d : Bool) :
    (∫ o : Obs, (if o.2.1 = d then 1 else 0) *
      (inverseHeat J σ).eval (sgn d * o.1) ∂Pobs Q σ) =
      ∫ x in (0 : ℝ)..1, (endpointKernel J).eval x * Q.f (sgn d * x) := by
  obtain ⟨C, hC, hall⟩ := exact_covariance
  have hcov := (hall J hJ σ hσ).1
  let I : (ℝ × Bool × Bool) → ℝ := fun s =>
    if decide (0 ≤ s.1) = d then 1 else 0
  let H : (ℝ × Bool × Bool) × ℝ → ℝ := fun sz =>
    I sz.1 * (inverseHeat J σ).eval (sgn d * sz.1.1 + σ * sz.2)
  letI : IsProbabilityMeasure Q.P := Q.prob
  letI : IsProbabilityMeasure (Q.P.map latentSchedule) :=
    Measure.isProbabilityMeasure_map latentSchedule_measurable.aemeasurable
  have hImeas : Measurable I := by
    dsimp [I]
    have hs : Measurable (fun s : ℝ × Bool × Bool => decide (0 ≤ s.1)) := by
      have hset : MeasurableSet {s : ℝ × Bool × Bool | 0 ≤ s.1} :=
        measurableSet_le measurable_const measurable_fst
      have heq : (fun s : ℝ × Bool × Bool => decide (0 ≤ s.1)) =
          fun s => if 0 ≤ s.1 then true else false := by
        funext s
        by_cases h : 0 ≤ s.1 <;> simp [h]
      rw [heq]
      exact measurable_const.ite hset measurable_const
    exact measurable_const.ite
      ((measurableSet_singleton d).preimage hs) measurable_const
  have hITop : MemLp (fun sz : (ℝ × Bool × Bool) × ℝ => I sz.1) ⊤
      ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) := by
    apply memLp_top_of_bound (hImeas.comp measurable_fst).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun sz => by dsimp [I]; split_ifs <;> norm_num
  have hHLp : MemLp H 2 ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) := by
    have hb := inverseHeat_schedule_gaussian_memLp_two hermite Q d J σ
    change MemLp ((fun sz : (ℝ × Bool × Bool) × ℝ => I sz.1) *
      fun sz => (inverseHeat J σ).eval (sgn d * sz.1.1 + σ * sz.2)) 2 _
    exact hb.mul hITop
  have hHintegrable : Integrable H
      ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) :=
    hHLp.integrable (by norm_num)
  have hpull : (∫ o : Obs, (if o.2.1 = d then 1 else 0) *
      (inverseHeat J σ).eval (sgn d * o.1) ∂Pobs Q σ) =
      ∫ ω, H (latentSchedule ω, sgn d * errorCoord ω) ∂Q.P := by
    rw [integral_Pobs_eq_integral_obs_comp]
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        dsimp [H, I, obs, latentSchedule]
        rw [sgn_mul_proxy]
        rfl
    · have hiobs : Measurable (fun o : Obs => if o.2.1 = d then (1 : ℝ) else 0) :=
        measurable_const.ite
          ((measurableSet_singleton d).preimage measurable_snd.fst) measurable_const
      have hpoly : Measurable (fun o : Obs =>
          (inverseHeat J σ).eval (sgn d * o.1)) := by fun_prop
      exact (hiobs.mul hpoly).aestronglyMeasurable
  rw [hpull, integral_latentSchedule_signedError β σ Q hQ d H hHintegrable]
  have hinner (s : ℝ × Bool × Bool) :
      (∫ z, H (s, z) ∂gaussianReal 0 1) = I s * (endpointKernel J).eval (sgn d * s.1) := by
    dsimp [H]
    rw [integral_const_mul, (hcov (sgn d * s.1)).1]
  simp_rw [hinner]
  rw [integral_map latentSchedule_measurable.aemeasurable (by fun_prop)]
  have harmint : (∫ ω, I (latentSchedule ω) *
      (endpointKernel J).eval (sgn d * (latentSchedule ω).1) ∂Q.P) =
      ∫ ω, (if sgn d * score ω ∈ Icc (0 : ℝ) 1 then 1 else 0) *
        (endpointKernel J).eval (sgn d * score ω) ∂Q.P := by
    apply integral_congr_ae
    filter_upwards [arm_indicator_ae_eq_reflected_Icc Q d] with ω harm
    dsimp [I, latentSchedule]
    rw [show (if decide (0 ≤ score ω) = d then (1 : ℝ) else 0) =
      if sgn d * score ω ∈ Icc (0 : ℝ) 1 then 1 else 0 by
        change (if side ω = d then (1 : ℝ) else 0) = _
        exact harm]
  rw [harmint]
  have hwmeas : Measurable (fun x =>
      (if sgn d * x ∈ Icc (0 : ℝ) 1 then 1 else 0) *
        (endpointKernel J).eval (sgn d * x)) := by
    have hs : MeasurableSet {x : ℝ | sgn d * x ∈ Icc (0 : ℝ) 1} :=
      measurableSet_Icc.preimage (by fun_prop)
    exact (measurable_const.ite hs measurable_const).mul (by fun_prop)
  rw [integral_scoreWeight Q (fun x =>
    (if sgn d * x ∈ Icc (0 : ℝ) 1 then 1 else 0) *
      (endpointKernel J).eval (sgn d * x)) hwmeas]
  rw [show (fun x =>
      ((if sgn d * x ∈ Icc (0 : ℝ) 1 then 1 else 0) *
        (endpointKernel J).eval (sgn d * x)) * Q.f x) =
      fun x => (if sgn d * x ∈ Icc (0 : ℝ) 1 then 1 else 0) *
        ((endpointKernel J).eval (sgn d * x) * Q.f x) by funext x; ring]
  cases d
  · simpa [sgn, mul_assoc] using reflected_Icc_integral false
      (fun x => (endpointKernel J).eval x * Q.f (sgn false * x))
  · simpa [sgn, mul_assoc] using reflected_Icc_integral true
      (fun x => (endpointKernel J).eval x * Q.f (sgn true * x))

/-- Exact FC.1 population identity for the marked arm summand. Given [the displayed inputs and assumptions](hyp:legendre,hermite,β,σ,Q,hQ,hσ,J,hJ,d), [the stated mathematical conclusion holds](goal). -/
lemma marked_observed_integral_eq_endpoint (legendre : ClassicalLegendreFacts)
    (hermite : ClassicalHermiteFacts) (β σ : ℝ) (Q : LatentLaw)
    (hQ : Model β σ Q) (hσ : σ ∈ Icc (0 : ℝ) 1) (J : ℕ) (hJ : 1 ≤ J)
    (d : Bool) :
    (∫ o : Obs, (if o.2.1 = d then 1 else 0) * bit o.2.2 *
      (inverseHeat J σ).eval (sgn d * o.1) ∂Pobs Q σ) =
      ∫ x in (0 : ℝ)..1,
        (endpointKernel J).eval x * Q.f (sgn d * x) * Q.mu d (sgn d * x) := by
  obtain ⟨C, hC, hall⟩ := exact_covariance
  have hcov := (hall J hJ σ hσ).1
  let I : (ℝ × Bool × Bool) → ℝ := fun s => if decide (0 ≤ s.1) = d then 1 else 0
  let M : (ℝ × Bool × Bool) → ℝ := fun s => bit (if d then s.2.2 else s.2.1)
  let H : (ℝ × Bool × Bool) × ℝ → ℝ := fun sz => I sz.1 * M sz.1 *
    (inverseHeat J σ).eval (sgn d * sz.1.1 + σ * sz.2)
  letI : IsProbabilityMeasure Q.P := Q.prob
  letI : IsProbabilityMeasure (Q.P.map latentSchedule) :=
    Measure.isProbabilityMeasure_map latentSchedule_measurable.aemeasurable
  have hImeas : Measurable I := by
    dsimp [I]
    have hs : Measurable (fun s : ℝ × Bool × Bool => decide (0 ≤ s.1)) := by
      have hset : MeasurableSet {s : ℝ × Bool × Bool | 0 ≤ s.1} :=
        measurableSet_le measurable_const measurable_fst
      have heq : (fun s : ℝ × Bool × Bool => decide (0 ≤ s.1)) =
          fun s => if 0 ≤ s.1 then true else false := by
        funext s; by_cases h : 0 ≤ s.1 <;> simp [h]
      rw [heq]
      exact measurable_const.ite hset measurable_const
    exact measurable_const.ite ((measurableSet_singleton d).preimage hs) measurable_const
  have hMmeas : Measurable M := by
    dsimp [M]
    exact (measurable_of_countable bit).comp
      (measurable_snd.snd.ite (by simp) measurable_snd.fst)
  have hIMTop : MemLp (fun sz : (ℝ × Bool × Bool) × ℝ => I sz.1 * M sz.1) ⊤
      ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) := by
    apply memLp_top_of_bound
      (((hImeas.mul hMmeas).comp measurable_fst).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall fun sz => by
      dsimp [I, M]; cases d <;> cases h : sz.1.2.1 <;> cases k : sz.1.2.2 <;>
        simp [bit, h, k] <;> split_ifs <;> norm_num
  have hHLp : MemLp H 2 ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) := by
    have hb := inverseHeat_schedule_gaussian_memLp_two hermite Q d J σ
    change MemLp ((fun sz : (ℝ × Bool × Bool) × ℝ => I sz.1 * M sz.1) *
      fun sz => (inverseHeat J σ).eval (sgn d * sz.1.1 + σ * sz.2)) 2 _
    exact hb.mul hIMTop
  have hHint : Integrable H ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) :=
    hHLp.integrable (by norm_num)
  have hpull : (∫ o : Obs, (if o.2.1 = d then 1 else 0) * bit o.2.2 *
      (inverseHeat J σ).eval (sgn d * o.1) ∂Pobs Q σ) =
      ∫ ω, H (latentSchedule ω, sgn d * errorCoord ω) ∂Q.P := by
    rw [integral_Pobs_eq_integral_obs_comp]
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        dsimp [H, I, M, obs, latentSchedule]
        rw [sgn_mul_proxy]
        calc
          (if side ω = d then 1 else 0) * bit (outcome ω) *
              (inverseHeat J σ).eval
                (sgn d * score ω + σ * (sgn d * errorCoord ω)) =
            ((if side ω = d then 1 else 0) * bit (outcome ω)) *
              (inverseHeat J σ).eval
                (sgn d * score ω + σ * (sgn d * errorCoord ω)) := by ring
          _ = ((if side ω = d then 1 else 0) * pot d ω) *
              (inverseHeat J σ).eval
                (sgn d * score ω + σ * (sgn d * errorCoord ω)) := by
                rw [arm_indicator_outcome_eq_pot]
          _ = _ := by rfl
    · have hiobs : Measurable (fun o : Obs => if o.2.1 = d then (1 : ℝ) else 0) :=
        measurable_const.ite ((measurableSet_singleton d).preimage measurable_snd.fst)
          measurable_const
      exact ((hiobs.mul ((measurable_of_countable bit).comp measurable_snd.snd)).mul
        (by fun_prop)).aestronglyMeasurable
  rw [hpull, integral_latentSchedule_signedError β σ Q hQ d H hHint]
  have hinner (s : ℝ × Bool × Bool) : (∫ z, H (s,z) ∂gaussianReal 0 1) =
      I s * M s * (endpointKernel J).eval (sgn d * s.1) := by
    dsimp [H]
    change (∫ z, (I s * M s) *
      (inverseHeat J σ).eval (sgn d * s.1 + σ * z) ∂gaussianReal 0 1) = _
    rw [integral_const_mul, (hcov (sgn d * s.1)).1]
  simp_rw [hinner]
  rw [integral_map latentSchedule_measurable.aemeasurable (by fun_prop)]
  have harmint : (∫ ω, I (latentSchedule ω) * M (latentSchedule ω) *
      (endpointKernel J).eval (sgn d * (latentSchedule ω).1) ∂Q.P) =
      ∫ ω, ((if sgn d * score ω ∈ Icc (0 : ℝ) 1 then 1 else 0) *
        (endpointKernel J).eval (sgn d * score ω)) * pot d ω ∂Q.P := by
    apply integral_congr_ae
    filter_upwards [arm_indicator_ae_eq_reflected_Icc Q d] with ω harm
    dsimp [I, M, latentSchedule]
    rw [show (if decide (0 ≤ score ω) = d then (1 : ℝ) else 0) =
      if sgn d * score ω ∈ Icc (0 : ℝ) 1 then 1 else 0 by
        change (if side ω = d then (1 : ℝ) else 0) = _; exact harm]
    unfold pot
    ring
  rw [harmint]
  have hwmeas : Measurable (fun x =>
      (if sgn d * x ∈ Icc (0 : ℝ) 1 then 1 else 0) *
        (endpointKernel J).eval (sgn d * x)) := by
    exact (measurable_const.ite
      (measurableSet_Icc.preimage (by fun_prop)) measurable_const).mul (by fun_prop)
  rw [integral_scoreWeight_mul_pot β σ Q hQ d _ hwmeas]
  rw [show (fun x => ((if sgn d * x ∈ Icc (0 : ℝ) 1 then 1 else 0) *
      (endpointKernel J).eval (sgn d * x)) * (Q.mu d x * Q.f x)) =
      fun x => (if sgn d * x ∈ Icc (0 : ℝ) 1 then 1 else 0) *
        ((endpointKernel J).eval (sgn d * x) * (Q.f x * Q.mu d x)) by
          funext x; ring]
  cases d
  · simpa [sgn, mul_assoc, mul_comm, mul_left_comm] using
      reflected_Icc_integral false (fun x =>
        (endpointKernel J).eval x *
          (Q.f (sgn false * x) * Q.mu false (sgn false * x)))
  · simpa [sgn, mul_assoc, mul_comm, mul_left_comm] using
      reflected_Icc_integral true (fun x =>
        (endpointKernel J).eval x *
          (Q.f (sgn true * x) * Q.mu true (sgn true * x)))

end CausalSmith.Stat.RdTruesideNoiseFrontier
