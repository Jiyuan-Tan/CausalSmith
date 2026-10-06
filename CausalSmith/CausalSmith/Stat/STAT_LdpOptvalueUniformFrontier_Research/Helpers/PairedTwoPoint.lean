module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.Lower
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.PairedTV

/-! # Paired two-point converse

Direct squared-risk and honest-length reductions on the paired model, including
all dimensions below a fixed universal cutoff.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [sequential local privacy of the protocol](hyp:hK), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), and [amplitude between zero and one half](hyp:ha). [Constant paired parameters inherit the arbitrary-channel contraction through signed preprocessing of the original records](goal). -/
-- @node: paired_constant_contrast_tv_bound
lemma paired_constant_contrast_tv_bound (hRN : MeasurableKernelRadonNikodym)
    (K : LocalProtocol n (PairedSymbol d)) (eps a : ℝ)
    (hK : SequentialClass K eps) (hAllowed : Allowed n d eps)
    (ha : a ∈ Set.Ioc 0 (1/2 : ℝ)) :
    Causalean.Stat.tvDist (canonicalSeedTranscriptLaw K (pairedLaw (fun _ => 0)))
      (canonicalSeedTranscriptLaw K (pairedLaw (fun _ => a))) ≤ a*Real.sqrt n*eps := by
  have h0 : (fun _ : Fin d => (0 : ℝ)) ∈ parameterCube d := by
    intro j; constructor <;> norm_num
  have h1 : (fun _ : Fin d => a) ∈ parameterCube d := by
    intro j; exact ⟨by linarith [ha.1], ha.2⟩
  have h := constant_contrast_tv_bound hRN (canonicalScheme n d)
    canonicalScheme_iidPeople canonicalScheme_independentRandomness (pulledProtocol K)
    eps a ((signed_protocol_classes eps).2 K |>.1 hK) hAllowed ha
  simp only [seedTranscriptLaw, canonicalSeedTranscriptLaw,
    pulledProtocol_decisionLaw _ canonicalScheme_iidPeople
      canonicalScheme_independentRandomness hAllowed.2.1 K _ h0,
    pulledProtocol_decisionLaw _ canonicalScheme_iidPeople
      canonicalScheme_independentRandomness hAllowed.2.1 K _ h1] at h
  dsimp [pulledProtocol, canonicalSeedTranscriptLaw] at h ⊢
  exact h

/-- Assume [amplitude between zero and one half](hyp:ha), [dimension at least two](hyp:hd), and [the stated total-variation bound](hyp:hTV). [The two point-prior reduction is applied on the symmetric submodel, so the interval premise asks for honesty only on paired laws](goal). -/
-- @node: paired_constant_contrast_decision_lower
lemma paired_constant_contrast_decision_lower
    (K : LocalProtocol n (PairedSymbol d)) (a : ℝ)
    (ha : a ∈ Set.Ioc 0 (1/2 : ℝ)) (hd : 2 ≤ d)
    (hTV : Causalean.Stat.tvDist
      (canonicalSeedTranscriptLaw K (pairedLaw (fun _ => 0)))
      (canonicalSeedTranscriptLaw K (pairedLaw (fun _ => a))) ≤ 1/8) :
    (∀ T : Estimator K, ENNReal.ofReal (63*a^2/4096) ≤
      ⨆ p : {p : Measure (PairedSymbol d) // p ∈ pairedFamily d},
        squaredRisk (canonicalDecisionLaw K p.1) T (tvFromUniform p.1)) ∧
    (∀ J : IntervalDecision K 0 1,
      (∀ p ∈ pairedFamily d, (0.90 : ℝ) ≤ coverage (canonicalDecisionLaw K p) J
        (tvFromUniform p)) →
      ENNReal.ofReal (81*a/320) ≤
        ⨆ p : {p : Measure (PairedSymbol d) // p ∈ pairedFamily d},
          expectedLength (canonicalDecisionLaw K p.1) J) := by
  let Q := pulledProtocol K
  let M := symmetricLaw '' parameterCube d
  let laws := completedDecisionLaw Q
  let target := fun P : Measure (FullRecord d) => value P - 1/2
  have h0 : (fun _ : Fin d => (0 : ℝ)) ∈ parameterCube d := by
    intro j; constructor <;> norm_num
  have h1 : (fun _ : Fin d => a) ∈ parameterCube d := by
    intro j; exact ⟨by linarith [ha.1], ha.2⟩
  have hEq (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) :
      laws (symmetricLaw theta) = canonicalDecisionLaw K (pairedLaw theta) := by
    haveI := symmetricLaw_probability theta htheta (by omega)
    rw [show laws (symmetricLaw theta) = decisionLaw (canonicalScheme n d) Q
      (symmetricLaw theta) from completedDecisionLaw_eq_canonical Q _]
    exact pulledProtocol_decisionLaw _ canonicalScheme_iidPeople
      canonicalScheme_independentRandomness hd K theta htheta
  have hTarget (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) :
      target (symmetricLaw theta) = tvFromUniform (pairedLaw theta) := by
    dsimp [target]
    rw [symmetricLaw_value theta htheta (by omega),
      tvFromUniform_pairedLaw theta htheta (by omega)]
    ring
  have hProduct : ∀ P ∈ M, laws P =
      (((laws P).map (fun w => (w.1,w.2.1))).prod uniform01).map
        (fun w : (ProtocolTranscript Q × Q.Seed) × ℝ => (w.1.1,w.1.2,w.2)) := by
    rintro P ⟨theta, htheta, rfl⟩
    haveI := symmetricLaw_probability theta htheta (by omega)
    dsimp [laws]
    rw [completedDecisionLaw_eq_canonical]
    exact sampling_decisionLaw_randomizer _ canonicalScheme_iidPeople
      canonicalScheme_independentRandomness Q _
      (symmetricLaw_causalModel theta htheta (by omega))
  have hProb : ∀ P ∈ M, IsProbabilityMeasure (laws P) := by
    rintro P ⟨theta, htheta, rfl⟩
    haveI := symmetricLaw_probability theta htheta (by omega)
    dsimp [laws]
    rw [completedDecisionLaw_eq_canonical]
    exact sampling_decisionLaw_probability _ canonicalScheme_iidPeople
      canonicalScheme_independentRandomness Q _
      (symmetricLaw_causalModel theta htheta (by omega))
  have hv0 : target (symmetricLaw (fun _ : Fin d => (0 : ℝ))) = 0 := by
    rw [hTarget _ h0, tvFromUniform_pairedLaw _ h0 (by omega), signedNorm_constant _ (by omega)]
    norm_num
  have hv1 : target (symmetricLaw (fun _ : Fin d => a)) = a/2 := by
    rw [hTarget _ h1, tvFromUniform_pairedLaw _ h1 (by omega),
      signedNorm_constant _ (by omega), abs_of_pos ha.1]
  have hmem0 : symmetricLaw (fun _ : Fin d => (0 : ℝ)) ∈ M := ⟨_, h0, rfl⟩
  have hmem1 : symmetricLaw (fun _ : Fin d => a) ∈ M := ⟨_, h1, rfl⟩
  have hbind (P : Measure (FullRecord d)) : (Measure.dirac P).bind laws = laws P := by
    rw [Measure.bind_congr_right (ae_eq_dirac laws)]
    change (Measure.dirac P).bind (fun _ => laws P) = _
    simp
  have hescape0 : (Measure.dirac (symmetricLaw (fun _ : Fin d => (0 : ℝ)))).real
      {P | (a/2-0)/8 < |target P-0|} ≤ 0 := by
    have hnot : symmetricLaw (fun _ : Fin d => (0 : ℝ)) ∉
        {P | (a/2-0)/8 < |target P-0|} := by
      simp only [Set.mem_ofPred_eq, hv0, sub_self, abs_zero]; linarith [ha.1]
    simp only [Measure.real, Measure.dirac_apply, Set.indicator_of_notMem hnot,
      ENNReal.toReal_zero, le_refl]
  have hescape1 : (Measure.dirac (symmetricLaw (fun _ : Fin d => a))).real
      {P | (a/2-0)/8 < |target P-a/2|} ≤ 0 := by
    have hnot : symmetricLaw (fun _ : Fin d => a) ∉
        {P | (a/2-0)/8 < |target P-a/2|} := by
      simp only [Set.mem_ofPred_eq, hv1, sub_self, abs_zero]; linarith [ha.1]
    simp only [Measure.real, Measure.dirac_apply, Set.indicator_of_notMem hnot,
      ENNReal.toReal_zero, le_refl]
  have htv : Causalean.Stat.tvDist
      (((Measure.dirac (symmetricLaw (fun _ : Fin d => (0 : ℝ)))).bind laws).map
        (fun w => (w.2.1,w.1)))
      (((Measure.dirac (symmetricLaw (fun _ : Fin d => a))).bind laws).map
        (fun w => (w.2.1,w.1))) ≤ 1/8 := by
    rw [hbind, hbind, hEq _ h0, hEq _ h1]
    dsimp [Q, pulledProtocol] at *
    exact hTV
  have hsep := separated_value_mixtures_generic Q M target laws hProduct hProb
    (Measure.dirac (symmetricLaw (fun _ : Fin d => (0 : ℝ))))
    (Measure.dirac (symmetricLaw (fun _ : Fin d => a)))
    (by simp [hmem0]) (by simp [hmem1])
    (by dsimp [target]; fun_prop) (measurable_completedDecisionLaw Q)
    0 (a/2) 0 (1/8) (by linarith [ha.1]) hescape0 hescape1 htv 0 1
  have hr : 9*(a/2-0)^2/128 * max 0 (1-(1/8 : ℝ)-2*0) = 63*a^2/4096 := by
    norm_num; ring
  have hl : 3*(a/2-0)/4 * max 0 ((0.80 : ℝ)-2*0-1/8) = 81*a/320 := by
    norm_num; ring
  rw [hr, hl] at hsep
  constructor
  · intro T
    refine (hsep.1 T).trans ?_
    apply iSup_le
    rintro ⟨P, theta, htheta, rfl⟩
    rw [hEq _ htheta, hTarget _ htheta]
    exact le_iSup_of_le ⟨pairedLaw theta, theta, htheta, rfl⟩ le_rfl
  · intro J hCov
    let JQ : IntervalDecision Q 0 1 :=
      ⟨J.lo, J.hi, J.measurable_lo, J.measurable_hi, J.ordered, J.range_lo, J.range_hi⟩
    have hCovM : ∀ P ∈ M, (0.90 : ℝ) ≤ coverage (laws P) JQ (target P) := by
      rintro P ⟨theta, htheta, rfl⟩
      rw [hEq _ htheta, hTarget _ htheta]
      exact hCov _ ⟨theta, htheta, rfl⟩
    refine (hsep.2 JQ hCovM).trans ?_
    apply iSup_le
    rintro ⟨P, theta, htheta, rfl⟩
    rw [hEq _ htheta]
    exact le_iSup_of_le ⟨pairedLaw theta, theta, htheta, rfl⟩ le_rfl

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), and [sequential local privacy of the protocol](hyp:hK). [The paired two-point experiment gives both per-decision inverse-information bounds for every sequential channel and independent public seed](goal). -/
-- @node: paired_dimension_free_two_point_decisions
lemma paired_dimension_free_two_point_decisions (hRN : MeasurableKernelRadonNikodym)
    (n d : ℕ) (eps : ℝ) (hAllowed : Allowed n d eps)
    (K : LocalProtocol n (PairedSymbol d)) (hK : SequentialClass K eps) :
    (∀ T : Estimator K, ENNReal.ofReal ((1/8192 : ℝ)*min 1 (1/(n*eps^2))) ≤
      ⨆ p : {p : Measure (PairedSymbol d) // p ∈ pairedFamily d},
        squaredRisk (canonicalDecisionLaw K p.1) T (tvFromUniform p.1)) ∧
    (∀ J : IntervalDecision K 0 1,
      (∀ p ∈ pairedFamily d, (0.90 : ℝ) ≤ coverage (canonicalDecisionLaw K p) J
        (tvFromUniform p)) →
      ENNReal.ofReal ((1/8192 : ℝ)*min 1 (1/(Real.sqrt n*eps))) ≤
        ⨆ p : {p : Measure (PairedSymbol d) // p ∈ pairedFamily d},
          expectedLength (canonicalDecisionLaw K p.1) J) := by
  let a := min 1 (1/(Real.sqrt n*eps))/8
  obtain ⟨ha, hsmall, hr, hl⟩ := two_point_amplitude_calibration n eps
    (by have := hAllowed.1; omega) hAllowed.2.2.1
  have hTV := (paired_constant_contrast_tv_bound hRN K eps a hK hAllowed ha).trans hsmall
  have hsep := paired_constant_contrast_decision_lower K a ha hAllowed.2.1 hTV
  exact ⟨fun T => (ENNReal.ofReal_le_ofReal hr).trans (hsep.1 T),
    fun J hCov => (ENNReal.ofReal_le_ofReal hl).trans (hsep.2 J hCov)⟩

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [polynomial degree at least two](hyp:hD), [dimension no larger than the polynomial degree](hyp:hdD), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), and [sequential local privacy of the protocol](hyp:hK). [Below a fixed dimension cutoff the two-point bounds control the full paired frontier, with the same universal cutoff factor for risk and honest length](goal). -/
-- @node: paired_bounded_dimension_frontier_lower
lemma paired_bounded_dimension_frontier_lower (hRN : MeasurableKernelRadonNikodym)
    (D n d : ℕ) (eps : ℝ) (hD : 2 ≤ D) (hdD : d ≤ D) (hAllowed : Allowed n d eps)
    (K : LocalProtocol n (PairedSymbol d)) (hK : SequentialClass K eps) :
    (∀ T : Estimator K, ENNReal.ofReal ((1/(32768*(D : ℝ)^2))*rateR .SI n d eps) ≤
      ⨆ p : {p : Measure (PairedSymbol d) // p ∈ pairedFamily d},
        squaredRisk (canonicalDecisionLaw K p.1) T (tvFromUniform p.1)) ∧
    (∀ J : IntervalDecision K 0 1,
      (∀ p ∈ pairedFamily d, (0.90 : ℝ) ≤ coverage (canonicalDecisionLaw K p) J
        (tvFromUniform p)) →
      ENNReal.ofReal ((1/(32768*(D : ℝ)^2))*rateH .SI n d eps) ≤
        ⨆ p : {p : Measure (PairedSymbol d) // p ∈ pairedFamily d},
          expectedLength (canonicalDecisionLaw K p.1) J) := by
  obtain ⟨hr, hh⟩ := bounded_dimension_frontier_comparisons D n d eps hD hdD hAllowed
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hscale : (1/(32768*(D : ℝ)^2))*(4*(D : ℝ)^2) = 1/8192 := by
    field_simp
    <;> ring
  have hscaledR := mul_le_mul_of_nonneg_left hr
    (by positivity : (0 : ℝ) ≤ 1/(32768*(D : ℝ)^2))
  have hscaledH := mul_le_mul_of_nonneg_left hh
    (by positivity : (0 : ℝ) ≤ 1/(32768*(D : ℝ)^2))
  rw [← mul_assoc, hscale] at hscaledR hscaledH
  have hdec := paired_dimension_free_two_point_decisions hRN n d eps hAllowed K hK
  exact ⟨fun T => (ENNReal.ofReal_le_ofReal hscaledR).trans (hdec.1 T),
    fun J hCov => (ENNReal.ofReal_le_ofReal hscaledH).trans (hdec.2 J hCov)⟩

end CausalSmith.Stat.LdpOptvalueUniformFrontier
