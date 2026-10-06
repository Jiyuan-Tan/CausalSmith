module
public import Causalean.Stat.Minimax.Fano

/-!
# Information-radius interfaces for Fano's method

This module makes the mutual-information form of Fano directly usable from
reference-law and pairwise Kullback--Leibler bounds.  Its main result is the
general compensation identity: average divergence to a reference law equals
mutual information plus the divergence of the uniform mixture to that
reference law.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory
open scoped BigOperators ENNReal

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
  [Fintype ι] [Nonempty ι]
  (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]

/-- Given [a finite experiment](hyp:P), [a reference probability law](hyp:Q), and
[finite KL divergence from every experiment law to the reference](hyp:hfin), [each
component log-likelihood ratio to the reference decomposes almost everywhere into its
ratio to the uniform mixture plus the mixture's ratio to the reference](goal). -/
lemma llr_eq_llr_uniformMixture_add (Q : Measure Ω) [IsProbabilityMeasure Q]
    (hfin : ∀ j, _root_.InformationTheory.klDiv (P j) Q ≠ ⊤) (i : ι) :
    llr (P i) Q =ᵐ[P i]
      llr (P i) (uniformMixture P) + llr (uniformMixture P) Q := by
  letI : IsProbabilityMeasure (uniformMixture P) := uniformMixture_isProbabilityMeasure P
  have hPiQ := (_root_.InformationTheory.klDiv_ne_top_iff.mp (hfin i)).1
  have hPiBar := absolutelyContinuous_uniformMixture P i
  have hBarQ : uniformMixture P ≪ Q := by
    apply Measure.AbsolutelyContinuous.mk
    intro A _hA hQA
    rw [uniformMixture, mixture_apply
      (fun _ : ι => (Fintype.card ι : ENNReal)⁻¹) P A]
    apply Finset.sum_eq_zero
    intro j _hj
    rw [(_root_.InformationTheory.klDiv_ne_top_iff.mp (hfin j)).1 hQA, mul_zero]
  have hchainQ := Measure.rnDeriv_mul_rnDeriv
    (μ := P i) (ν := uniformMixture P) (κ := Q) hPiBar
  have hchain := hPiQ.ae_le hchainQ
  filter_upwards [hchain, Measure.rnDeriv_pos hPiQ,
      hPiQ.ae_le (Measure.rnDeriv_ne_top (P i) Q),
      Measure.rnDeriv_pos hPiBar,
      hPiBar.ae_le (Measure.rnDeriv_ne_top (P i) (uniformMixture P)),
      hPiBar.ae_le (Measure.rnDeriv_pos hBarQ),
      hPiQ.ae_le (Measure.rnDeriv_ne_top (uniformMixture P) Q)]
    with x hprod hPiQpos hPiQtop hPiBarpos hPiBartop hBarQpos hBarQtop
  simp only [Pi.mul_apply, Pi.add_apply] at hprod ⊢
  rw [llr_def, llr_def, llr_def, ← Real.log_mul
      (ENNReal.toReal_pos hPiBarpos.ne' hPiBartop).ne'
      (ENNReal.toReal_pos hBarQpos.ne' hBarQtop).ne']
  apply congrArg Real.log
  rw [← ENNReal.toReal_mul, hprod]

/-- **KL compensation identity.** Given [a finite experiment](hyp:P), [a reference
probability law](hyp:Q), and [finite KL divergence from every experiment law to the
reference](hyp:hfin), [the average KL divergence to the reference minus the uniform-prior
mutual information equals the KL divergence from the uniform mixture to the reference](goal).

Equivalently, `N⁻¹ ∑ᵢ KL(Pᵢ ‖ Q) = I(V;X) + KL(Pbar ‖ Q)`.  The observation space is
arbitrary; finiteness is only the standard regularity needed for this real-valued identity. -/
theorem uniform_kl_compensation_identity (Q : Measure Ω) [IsProbabilityMeasure Q]
    (hfin : ∀ i, _root_.InformationTheory.klDiv (P i) Q ≠ ⊤) :
    (Fintype.card ι : ℝ)⁻¹ *
          ∑ i, (_root_.InformationTheory.klDiv (P i) Q).toReal -
        uniformMutualInformation P =
      (_root_.InformationTheory.klDiv (uniformMixture P) Q).toReal := by
  letI : IsProbabilityMeasure (uniformMixture P) := uniformMixture_isProbabilityMeasure P
  have hPiQac : ∀ i, P i ≪ Q := fun i =>
    (_root_.InformationTheory.klDiv_ne_top_iff.mp (hfin i)).1
  have hPiQint : ∀ i, Integrable (llr (P i) Q) (P i) := fun i =>
    (_root_.InformationTheory.klDiv_ne_top_iff.mp (hfin i)).2
  have hPiBarint : ∀ i, Integrable (llr (P i) (uniformMixture P)) (P i) := fun i =>
    (_root_.InformationTheory.klDiv_ne_top_iff.mp
      (klDiv_uniformMixture_ne_top P i)).2
  have hBarQac : uniformMixture P ≪ Q := by
    apply Measure.AbsolutelyContinuous.mk
    intro A _hA hQA
    rw [uniformMixture, mixture_apply
      (fun _ : ι => (Fintype.card ι : ENNReal)⁻¹) P A]
    apply Finset.sum_eq_zero
    intro j _hj
    rw [hPiQac j hQA, mul_zero]
  have hchain : ∀ i, llr (P i) Q =ᵐ[P i]
      llr (P i) (uniformMixture P) + llr (uniformMixture P) Q :=
    llr_eq_llr_uniformMixture_add P Q hfin
  have hBarQint_i : ∀ i, Integrable (llr (uniformMixture P) Q) (P i) := by
    intro i
    apply ((hPiQint i).sub (hPiBarint i)).congr
    filter_upwards [hchain i] with x hx
    simp only [Pi.add_apply] at hx
    change llr (P i) Q x - llr (P i) (uniformMixture P) x =
      llr (uniformMixture P) Q x
    linarith
  have hBarQint : Integrable (llr (uniformMixture P) Q) (uniformMixture P) := by
    rw [uniformMixture, mixture]
    apply integrable_finsetSum_measure.2
    intro i _hi
    exact (hBarQint_i i).smul_measure (by simp)
  have hkl_i : ∀ i,
      (_root_.InformationTheory.klDiv (P i) Q).toReal =
        (_root_.InformationTheory.klDiv (P i) (uniformMixture P)).toReal +
          ∫ x, llr (uniformMixture P) Q x ∂P i := by
    intro i
    rw [_root_.InformationTheory.toReal_klDiv_of_measure_eq (hPiQac i) (by simp),
      _root_.InformationTheory.toReal_klDiv_of_measure_eq
        (absolutelyContinuous_uniformMixture P i) (by simp)]
    calc
      ∫ x, llr (P i) Q x ∂P i =
          ∫ x, (llr (P i) (uniformMixture P) + llr (uniformMixture P) Q) x ∂P i :=
        integral_congr_ae (hchain i)
      _ = ∫ x, llr (P i) (uniformMixture P) x ∂P i +
          ∫ x, llr (uniformMixture P) Q x ∂P i :=
        integral_add (hPiBarint i) (hBarQint_i i)
  have hmixIntegral :
      ∫ x, llr (uniformMixture P) Q x ∂uniformMixture P =
        (Fintype.card ι : ℝ)⁻¹ *
          ∑ i, ∫ x, llr (uniformMixture P) Q x ∂P i := by
    rw [uniformMixture, mixture, integral_finsetSum_measure]
    · simp_rw [integral_smul_measure]
      rw [Finset.mul_sum]
      simp [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    · intro i _hi
      exact (hBarQint_i i).smul_measure (by simp)
  rw [_root_.InformationTheory.toReal_klDiv_of_measure_eq hBarQac (by simp)]
  simp_rw [hkl_i]
  rw [Finset.sum_add_distrib, uniformMutualInformation, mul_add, hmixIntegral]
  ring

/-- Given [a finite experiment](hyp:P), [a reference probability law](hyp:Q), and
[finite KL divergence from every experiment law to the reference](hyp:hfin), [uniform-prior
mutual information is at most the average KL divergence to that reference](goal). -/
theorem uniformMutualInformation_le_average_kl (Q : Measure Ω) [IsProbabilityMeasure Q]
    (hfin : ∀ i, _root_.InformationTheory.klDiv (P i) Q ≠ ⊤) :
    uniformMutualInformation P ≤
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ i, (_root_.InformationTheory.klDiv (P i) Q).toReal := by
  have hid := uniform_kl_compensation_identity P Q hfin
  have hnonneg : 0 ≤
      (_root_.InformationTheory.klDiv (uniformMixture P) Q).toReal :=
    ENNReal.toReal_nonneg
  linarith

/-- Given [a nonempty finite family of probability laws](hyp:P), the [maximum pairwise
KL divergence](goal) is the largest real-valued divergence between two members. -/
noncomputable def maxPairwiseKL : ℝ :=
  (Finset.univ : Finset (ι × ι)).sup' Finset.univ_nonempty fun ij =>
    (_root_.InformationTheory.klDiv (P ij.1) (P ij.2)).toReal

/-- Given [a finite experiment](hyp:P) whose [pairwise KL divergences are finite](hyp:hfin),
[uniform-prior mutual information is at most the maximum pairwise KL divergence](goal). -/
theorem uniformMutualInformation_le_maxPairwiseKL
    (hfin : ∀ i j, _root_.InformationTheory.klDiv (P i) (P j) ≠ ⊤) :
    uniformMutualInformation P ≤ maxPairwiseKL P := by
  classical
  let j₀ : ι := Classical.choice inferInstance
  have href := uniformMutualInformation_le_average_kl P (P j₀) (fun i => hfin i j₀)
  have hterm : ∀ i,
      (_root_.InformationTheory.klDiv (P i) (P j₀)).toReal ≤ maxPairwiseKL P := by
    intro i
    change (_root_.InformationTheory.klDiv (P i) (P j₀)).toReal ≤
      (Finset.univ : Finset (ι × ι)).sup' _
        (fun ij => (_root_.InformationTheory.klDiv (P ij.1) (P ij.2)).toReal)
    exact Finset.le_sup' (s := (Finset.univ : Finset (ι × ι)))
      (fun ij : ι × ι => (_root_.InformationTheory.klDiv (P ij.1) (P ij.2)).toReal)
      (Finset.mem_univ (i, j₀))
  calc
    uniformMutualInformation P ≤
        (Fintype.card ι : ℝ)⁻¹ *
          ∑ i, (_root_.InformationTheory.klDiv (P i) (P j₀)).toReal := href
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, maxPairwiseKL P := by
      gcongr
      exact hterm i
    _ = maxPairwiseKL P := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [show (Fintype.card ι : ℝ) ≠ 0 by positivity]

end Causalean.Stat
