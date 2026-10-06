module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Main

/-! Product-measure variance bounds used by the common-marginal construction. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators
/-- [the stated conditions](hyp:hg) establishes [the stated conclusion](goal). -/

lemma integral_sum_iid {k : Nat} {nu : Measure Real} [IsProbabilityMeasure nu]
    {g : Real → Real} (hg : Integrable g nu) :
    ∫ w : Fin k → Real, ∑ i, g (w i) ∂Measure.pi (fun _ : Fin k => nu) =
      k * ∫ p, g p ∂nu := by
  rw [integral_finsetSum]
  · simp_rw [integral_comp_eval (μ := fun _ : Fin k => nu)
      (f := g) hg.aestronglyMeasurable, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · intro i _
    exact integrable_comp_eval hg
/-- [the stated conditions](hyp:ha,hkappa,hsupport) establishes [the stated conclusion](goal). -/

lemma zeroInflated_polar_firstMoment
    {iota : Type*} [Fintype iota] {L : Nat}
    (C : Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate
      iota L) (a kappa B : Real) (ha : 0 < a) (hkappa : 0 < kappa)
    (hsupport : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / kappa) B) :
    ∫ p, p * C.polarSign p ∂C.zeroInflatedPrior a =
      a * ∑ i, C.weight i * (C.node i / (C.node i + a)) := by
  classical
  have hpolar_node (i : iota) : C.polarSign (C.node i) = Real.sign (C.weight i) := by
    unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.polarSign
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [C.node_injective.ne hji.symm]
    · simp
  have hpolar_mem (p : Real) : C.polarSign p ∈ Set.Icc (-1 : Real) 1 := by
    by_cases hp : ∃ i, p = C.node i
    · obtain ⟨i, rfl⟩ := hp
      rw [hpolar_node]
      rcases lt_trichotomy (C.weight i) 0 with hi | hi | hi
      · simp [Real.sign_of_neg hi]
      · simp [hi]
      · simp [Real.sign_of_pos hi]
    · unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.polarSign
      have hne : ∀ i, p ≠ C.node i := fun i hi => hp ⟨i, hi⟩
      simp [hne]
  have hf : Integrable (fun p => p * C.polarSign p) (C.zeroInflatedPrior a) := by
    let _ := C.zeroInflatedPrior_isProbabilityMeasure a kappa B ha hkappa hsupport
    apply Integrable.of_bound
      (measurable_id.mul C.measurable_polarSign).aestronglyMeasurable |B|
    filter_upwards [C.zeroInflatedPrior_support a kappa B ha hkappa hsupport] with p hp
    rcases hp with rfl | hp
    · simp
    · change |p * C.polarSign p| ≤ |B|
      rw [abs_mul]
      have hp0 : 0 ≤ p := (div_nonneg ha.le hkappa.le).trans hp.1
      rw [abs_of_nonneg hp0]
      calc
        p * |C.polarSign p| ≤ p * 1 := by
          gcongr
          exact (abs_le).2 (hpolar_mem p)
        _ ≤ |B| := by simpa using hp.2.trans (le_abs_self B)
  let tilt : Real → ENNReal := fun p => ENNReal.ofReal (a / (p + a))
  have hleft : Integrable (fun p => p * C.polarSign p)
      (C.signedMeasure.variation.withDensity tilt) := by
    exact hf.mono_measure (by
      unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.zeroInflatedPrior
      exact Measure.le_add_right le_rfl)
  have hright : Integrable (fun p => p * C.polarSign p)
      (ENNReal.ofReal
          (1 - ∫ p, a / (p + a) ∂C.signedMeasure.variation) • Measure.dirac 0) := by
    exact hf.mono_measure (by
      unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.zeroInflatedPrior
      exact Measure.le_add_left le_rfl)
  rw [Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.zeroInflatedPrior,
    integral_add_measure hleft hright,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    integral_smul_measure, integral_dirac]
  simp only [smul_eq_mul, zero_mul, mul_zero, add_zero]
  have htilt : ∀ᵐ p ∂C.signedMeasure.variation,
      (tilt p).toReal = a / (p + a) := by
    filter_upwards [hsupport] with p hp
    rw [ENNReal.toReal_ofReal]
    exact div_nonneg ha.le (add_nonneg
      ((div_nonneg ha.le hkappa.le).trans hp.1) ha.le)
  rw [integral_congr_ae (htilt.mono fun p hp => by rw [hp])]
  rw [show (fun p : Real => a / (p + a) * (p * C.polarSign p)) =
      fun p => a * ((p / (p + a)) * C.polarSign p) by
    funext p
    ring]
  rw [integral_const_mul]
  rw [C.variation_eq_absoluteMeasure]
  unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.absoluteMeasure
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  apply congrArg (fun z : Real => a * z)
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (abs_nonneg _), hpolar_node]
  change |C.weight i| *
      ((C.node i / (C.node i + a)) * Real.sign (C.weight i)) =
      C.weight i * (C.node i / (C.node i + a))
  have habs : |C.weight i| * Real.sign (C.weight i) = C.weight i := by
    rcases lt_trichotomy (C.weight i) 0 with hi | hi | hi
    · simp [abs_of_neg hi, Real.sign_of_neg hi]
    · simp [hi]
    · simp [abs_of_pos hi, Real.sign_of_pos hi]
  calc
    |C.weight i| *
        ((C.node i / (C.node i + a)) * Real.sign (C.weight i)) =
        (|C.weight i| * Real.sign (C.weight i)) *
          (C.node i / (C.node i + a)) := by ring
    _ = C.weight i * (C.node i / (C.node i + a)) := by rw [habs]
/-- [the stated conditions](hyp:hg,hsupport,hB,hmean) establishes [the stated conclusion](goal). -/

lemma variance_sum_iid_le {k : Nat} {nu : Measure Real} [IsProbabilityMeasure nu]
    {g : Real → Real} {B a : Real} (hg : Measurable g)
    (hsupport : ∀ᵐ p ∂nu, 0 ≤ g p ∧ g p ≤ p ∧ p ≤ B)
    (hB : 0 ≤ B) (hmean : ∫ p, p ∂nu ≤ a) :
    variance (fun w : Fin k → Real => ∑ i, g (w i))
        (Measure.pi fun _ : Fin k => nu) ≤ k * B * a := by
  have hgIcc : ∀ᵐ p ∂nu, g p ∈ Set.Icc (0 : Real) B := by
    filter_upwards [hsupport] with p hp
    exact ⟨hp.1, hp.2.1.trans hp.2.2⟩
  have hgMem : MemLp g 2 nu :=
    memLp_of_bounded hgIcc hg.aestronglyMeasurable 2
  have hgMean_nonneg : 0 ≤ ∫ p, g p ∂nu := integral_nonneg_of_ae <|
    hsupport.mono fun _ hp => hp.1
  have hpInt : Integrable id nu := by
    apply Integrable.of_bound measurable_id.aestronglyMeasurable (max |B| 0)
    filter_upwards [hsupport] with p hp
    change |p| ≤ max |B| 0
    rw [abs_of_nonneg (hp.1.trans hp.2.1), abs_of_nonneg hB, max_eq_left hB]
    exact hp.2.2
  have hgInt : Integrable g nu := hgMem.integrable (by norm_num)
  have hgMean_le : ∫ p, g p ∂nu ≤ a := by
    exact (integral_mono_ae hgInt hpInt
      (hsupport.mono fun _ hp => hp.2.1)).trans hmean
  have hvar : variance g nu ≤ B * a := by
    calc
      variance g nu ≤ (B - ∫ p, g p ∂nu) * (∫ p, g p ∂nu) := by
        simpa using variance_le_sub_mul_sub hgIcc hg.aemeasurable
      _ ≤ B * a := by
        nlinarith [sq_nonneg (∫ p, g p ∂nu),
          mul_nonneg hB (sub_nonneg.mpr hgMean_le)]
  rw [show (fun w : Fin k → Real => ∑ i, g (w i)) =
      ∑ i, fun w : Fin k → Real => g (w i) by funext w; simp,
    variance_sum_pi (fun _ => hgMem)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    (k : Real) * variance g nu ≤ (k : Real) * (B * a) :=
      mul_le_mul_of_nonneg_left hvar (Nat.cast_nonneg k)
    _ = (k : Real) * B * a := by ring
/-- [the stated conditions](hyp:hsupport,hB,hmean) establishes [the stated conclusion](goal). -/

lemma variance_const_add_sum_iid_le {k : Nat} {nu : Measure Real}
    [IsProbabilityMeasure nu] {c B a : Real}
    (hsupport : ∀ᵐ p ∂nu, p ∈ Set.Icc (0 : Real) B)
    (hB : 0 ≤ B) (hmean : ∫ p, p ∂nu ≤ a) :
    variance (fun w : Fin k → Real => c + ∑ i, w i)
        (Measure.pi fun _ : Fin k => nu) ≤ k * B * a := by
  have hsum_meas : AEStronglyMeasurable
      (fun w : Fin k → Real => ∑ i, w i)
      (Measure.pi fun _ : Fin k => nu) := by fun_prop
  rw [variance_const_add hsum_meas c]
  apply variance_sum_iid_le measurable_id
  · filter_upwards [hsupport] with p hp
    exact ⟨hp.1, le_rfl, hp.2⟩
  · exact hB
  · exact hmean

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
