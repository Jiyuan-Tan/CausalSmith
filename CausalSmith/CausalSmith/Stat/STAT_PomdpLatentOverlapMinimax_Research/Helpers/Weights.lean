import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.Kernels
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

set_option linter.style.longLine false

/-! # Partial-history weight algebra and one-step integral peeling -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- Policy overlap bounds every totalized observable ratio. [the hb condition](hyp:hb); and [the he condition](hyp:he); and [the h condition](hyp:h); and [the h L condition](hyp:hL). [the stated conclusion](goal). -/
lemma ratio_mem {nX : Nat} {b e : Policy nX} {L : ℝ}
    (hb : PolicyVector b) (he : PolicyVector e)
    (h : ∀ x a, e x a ≤ L * b x a) (hL : 0 ≤ L)
    (x : Fin nX) (a : Bool) : ratio b e x a ∈ Set.Icc 0 L := by
  rw [ratio]
  split_ifs with hba
  · exact ⟨le_rfl, hL⟩
  · have hb_nonneg : 0 ≤ b x a := (hb x).1 a
    have hb_pos : 0 < b x a := lt_of_le_of_ne hb_nonneg (Ne.symm hba)
    exact ⟨div_nonneg ((he x).1 a) hb_nonneg, (div_le_iff₀ hb_pos).2 (h x a)⟩
  -- @realizes \(\rho_t\)(range [0,L] from both probability policies and domination)

/-- One behavior-action factor is replaced by its target-policy ratio inside an integral. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the hf condition](hyp:hf). [the stated conclusion](goal). -/
lemma integral_ratio_step {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    {L : ℝ} (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 0 ≤ L) (t : Fin T)
    (f : StateHistoryView T nX nH t × Bool → ℝ)
    (hf : Integrable f (M.law.map (histActionPair t))) :
    ∫ z, ratio M.b M.e (currentObsState t z.1) z.2 * f z
        ∂(M.law.map (histActionPair t)) =
      ∫ h, ∑ a : Bool, M.e (currentObsState t h) a * f (h, a)
        ∂(M.law.map (histStateView t)) := by
  letI : IsMarkovKernel (behaviourKernel M) := by
    constructor
    intro x
    constructor
    change (∑ a : Bool, ENNReal.ofReal (M.b x a) • Measure.dirac a) Set.univ = 1
    simp
    rw [← ENNReal.ofReal_add ((hign.1 x).1 true) ((hign.1 x).1 false)]
    rw [show M.b x true + M.b x false = 1 by simpa using (hign.1 x).2]
    norm_num
  rw [hign.2 t] at hf ⊢
  have hratio_meas : Measurable (fun z : StateHistoryView T nX nH t × Bool ↦
      ratio M.b M.e (currentObsState t z.1) z.2) := by
    exact (measurable_of_countable fun xa : Fin nX × Bool ↦ ratio M.b M.e xa.1 xa.2).comp
      ((measurable_currentObsState t).comp measurable_fst |>.prodMk measurable_snd)
  have hg : Integrable (fun z : StateHistoryView T nX nH t × Bool ↦
      ratio M.b M.e (currentObsState t z.1) z.2 * f z)
      ((M.law.map (histStateView t)).compProd
        (Kernel.comap (behaviourKernel M) (currentObsState t) (measurable_currentObsState t))) := by
    apply hf.bdd_mul hratio_meas.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (ratio_mem hign.1 hoverlap.1 hoverlap.2 hL _ _).1]
    exact (ratio_mem hign.1 hoverlap.1 hoverlap.2 hL _ _).2
  rw [Measure.integral_compProd hg]
  apply integral_congr_ae
  filter_upwards with h
  change (∫ b, ratio M.b M.e (currentObsState t h) b * f (h, b) ∂
      ∑ a : Bool, ENNReal.ofReal (M.b (currentObsState t h) a) • Measure.dirac a) = _
  rw [integral_finsetSum_measure (fun a _ ↦
    (integrable_dirac (f := fun b : Bool ↦
      ratio M.b M.e (currentObsState t h) b * f (h, b))
        enorm_lt_top).smul_measure
        ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal ((hign.1 _).1 a), ratio]
  split_ifs with hba
  · have hea : M.e (currentObsState t h) a = 0 :=
      le_antisymm (by simpa [hba] using hoverlap.2 (currentObsState t h) a)
        ((hoverlap.1 _).1 a)
    simp [hba, hea]
  · simp only [smul_eq_mul]
    field_simp

/-- One reward-transition block is peeled using the POMDP factorization. [the h K condition](hyp:hK); and [the hf condition](hyp:hf). [the stated conclusion](goal). -/
lemma integral_kernel_step {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hK : PomdpKernelLaw M) (t : Fin T)
    (f : ActionHistoryView T nX nH t × Step nX nH → ℝ)
    (hf : Integrable f (M.law.map (histNextPair t))) :
    ∫ z, f z ∂(M.law.map (histNextPair t)) =
      ∫ h, ∫ y, f (h, y) ∂(M.K h.1.2 h.2) ∂(M.law.map (histView t)) := by
  letI : IsMarkovKernel (kernelOfK M) :=
    ⟨fun sa ↦ hK.1 sa.1 sa.2⟩
  rw [hK.2 t] at hf ⊢
  rw [Measure.integral_compProd hf]
  rfl

end CausalSmith.Stat.PomdpLatentOverlapMinimax
