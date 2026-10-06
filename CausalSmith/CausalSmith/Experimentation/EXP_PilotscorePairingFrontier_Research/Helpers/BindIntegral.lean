module
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Signed integration through measure bind -/

public section

open MeasureTheory
open scoped ENNReal

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

/-- Fubini's identity for an integrable real function under a measurable measure kernel. -/
lemma integral_bind_real {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (κ : α → Measure β) (f : β → ℝ)
    (hκ : AEMeasurable κ μ) (hf : Integrable f (μ.bind κ)) :
    (∫ x, f x ∂μ.bind κ) = ∫ a, ∫ x, f x ∂κ a ∂μ := by
  let p : α → ℝ≥0∞ := fun a => ∫⁻ x, ENNReal.ofReal (f x) ∂κ a
  let n : α → ℝ≥0∞ := fun a => ∫⁻ x, ENNReal.ofReal (-f x) ∂κ a
  have hfpos : AEMeasurable (fun x => ENNReal.ofReal (f x)) (μ.bind κ) :=
    hf.aemeasurable.ennreal_ofReal
  have hfneg : AEMeasurable (fun x => ENNReal.ofReal (-f x)) (μ.bind κ) :=
    hf.neg.aemeasurable.ennreal_ofReal
  have hpmeas : AEMeasurable p μ := by
    unfold p
    have hj : AEMeasurable
        (fun ν : Measure β => ∫⁻ x, ENNReal.ofReal (f x) ∂ν) (μ.map κ) := by
      apply Measure.aemeasurable_lintegral
      simpa [Measure.bind] using hfpos
    exact hj.comp_aemeasurable hκ
  have hnmeas : AEMeasurable n μ := by
    unfold n
    have hj : AEMeasurable
        (fun ν : Measure β => ∫⁻ x, ENNReal.ofReal (-f x) ∂ν) (μ.map κ) := by
      apply Measure.aemeasurable_lintegral
      simpa [Measure.bind] using hfneg
    exact hj.comp_aemeasurable hκ
  have hpfinite : (∫⁻ a, p a ∂μ) ≠ ∞ := by
    rw [← Measure.lintegral_bind hκ hfpos]
    exact ne_top_of_le_ne_top hf.2.ne (lintegral_ofReal_le_lintegral_enorm f)
  have hnfinite : (∫⁻ a, n a ∂μ) ≠ ∞ := by
    rw [← Measure.lintegral_bind hκ hfneg]
    exact ne_top_of_le_ne_top hf.neg.2.ne (lintegral_ofReal_le_lintegral_enorm (-f))
  have hpint : Integrable (fun a => (p a).toReal) μ := by
    exact integrable_toReal_of_lintegral_ne_top hpmeas hpfinite
  have hnint : Integrable (fun a => (n a).toReal) μ := by
    exact integrable_toReal_of_lintegral_ne_top hnmeas hnfinite
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  rw [Measure.lintegral_bind hκ hfpos, Measure.lintegral_bind hκ hfneg]
  rw [← integral_toReal hpmeas (ae_lt_top' hpmeas hpfinite),
    ← integral_toReal hnmeas (ae_lt_top' hnmeas hnfinite)]
  rw [← integral_sub hpint hnint]
  apply integral_congr_ae
  have hsec : ∀ᵐ a ∂μ, Integrable f (κ a) := by
    let r : α → ℝ≥0∞ := fun a => ∫⁻ x, ‖f x‖ₑ ∂κ a
    have hnormmeas : AEMeasurable (fun x => ‖f x‖ₑ) (μ.bind κ) :=
      hf.aemeasurable.enorm
    have hrmeas : AEMeasurable r μ := by
      unfold r
      have hj : AEMeasurable
          (fun ν : Measure β => ∫⁻ x, ‖f x‖ₑ ∂ν) (μ.map κ) := by
        apply Measure.aemeasurable_lintegral
        simpa [Measure.bind] using hnormmeas
      exact hj.comp_aemeasurable hκ
    have hrfinite : (∫⁻ a, r a ∂μ) ≠ ∞ := by
      rw [← Measure.lintegral_bind hκ hnormmeas]
      exact hf.2.ne
    filter_upwards [hκ.ae_of_bind hf.aemeasurable,
      ae_lt_top' hrmeas hrfinite] with a hfa hra
    exact ⟨hfa.aestronglyMeasurable, hra⟩
  filter_upwards [hsec] with a ha
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part ha).symm

end CausalSmith.Experimentation.PilotscorePairingFrontier
