module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Bridge.Protocol
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.FiniteDensity
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Stagewise reference densities

Uniform finite averages dominate each input row. Applying the measurable kernel
Radon–Nikodym gate to these stage references gives jointly measurable nonnegative
real densities, at every history and seed, for the ancillary-averaged protocol.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Fix [the Markov kernel K](hyp:K). [Uniform averaging of finitely many probability kernels at a common parameter](goal). -/
-- @node: uniformRowAverage
def uniformRowAverage {I H Z : Type} [Fintype I] [MeasurableSpace H]
    [MeasurableSpace Z] (K : I → Kernel H Z) : Kernel H Z :=
  ⟨fun h => (Fintype.card I : ℝ≥0∞)⁻¹ • ∑ a, K a h, by
    apply Measure.measurable_of_measurable_coe
    intro E hE
    simp only [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
    exact measurable_const.mul (Finset.measurable_sum _ (fun a _ => (K a).measurable_coe hE))⟩

/-- Assume [the Markov kernel hK](hyp:hK). [A uniform average of a nonempty finite family of Markov kernels is Markov](goal). -/
-- @node: uniformRowAverage_markov
lemma uniformRowAverage_markov {I H Z : Type} [Fintype I] [Nonempty I]
    [MeasurableSpace H] [MeasurableSpace Z] (K : I → Kernel H Z)
    (hK : ∀ a, IsMarkovKernel (K a)) : IsMarkovKernel (uniformRowAverage K) := by
  constructor
  intro h
  constructor
  have hmass (a : I) : K a h Set.univ = 1 := by
    let := hK a
    exact measure_univ
  change ((Fintype.card I : ℝ≥0∞)⁻¹ • ∑ a, K a h) Set.univ = 1
  simp only [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply, hmass,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)

/-- [Every row is dominated by the uniform finite average, with no privacy premise](goal). -/
-- @node: row_absolutelyContinuous_uniformRowAverage
lemma row_absolutelyContinuous_uniformRowAverage {I H Z : Type} [Fintype I]
    [Nonempty I] [MeasurableSpace H] [MeasurableSpace Z]
    (K : I → Kernel H Z) (a : I) (h : H) : K a h ≪ uniformRowAverage K h := by
  intro E hE
  change ((Fintype.card I : ℝ≥0∞)⁻¹ • ∑ b, K b h) E = 0 at hE
  simp only [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply] at hE
  have hsum : ∑ b, K b h E = 0 :=
    (mul_eq_zero.mp hE).resolve_left (by simp)
  exact (Finset.sum_eq_zero_iff.mp hsum) a (Finset.mem_univ a)

/-- Assume [the Markov kernel hK](hyp:hK), [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), and [the stated hrep condition](hyp:hrep). [Finite row densities have average one almost everywhere under their reference](goal). -/
-- @node: uniformRowAverage_density_sum_ae
lemma uniformRowAverage_density_sum_ae {I H Z : Type} [Fintype I] [Nonempty I]
    [MeasurableSpace H] [MeasurableSpace Z] (K : I → Kernel H Z)
    (hK : ∀ a, IsMarkovKernel (K a)) (h : H) (f : I → Z → ℝ)
    (hf : ∀ a, Measurable (f a)) (hf0 : ∀ a z, 0 ≤ f a z)
    (hrep : ∀ a, (uniformRowAverage K h).withDensity
      (fun z => ENNReal.ofReal (f a z)) = K a h) :
    ∀ᵐ z ∂uniformRowAverage K h, ∑ a, f a z = (Fintype.card I : ℝ) := by
  let := uniformRowAverage_markov K hK
  let c : ℝ≥0∞ := (Fintype.card I : ℝ≥0∞)⁻¹
  have hc : c ≠ 0 := by simp [c]
  have hdens : (uniformRowAverage K h).withDensity
      (fun z => c * ∑ a, ENNReal.ofReal (f a z)) = uniformRowAverage K h := by
    ext E hE
    rw [withDensity_apply _ hE]
    rw [lintegral_const_mul _ (Finset.measurable_sum _
      (fun a _ => (hf a).ennreal_ofReal)), lintegral_finsetSum]
    · change c * (∑ a, ∫⁻ z in E, ENNReal.ofReal (f a z) ∂uniformRowAverage K h) =
        ((Fintype.card I : ℝ≥0∞)⁻¹ • ∑ a, K a h) E
      simp only [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [← withDensity_apply _ hE, hrep a]
    · intro a _
      exact (hf a).ennreal_ofReal
  have heq := (withDensity_eq_iff_of_sigmaFinite
    (measurable_const.mul (Finset.measurable_sum _
      (fun a _ => (hf a).ennreal_ofReal))).aemeasurable
    measurable_const.aemeasurable).mp (hdens.trans withDensity_one.symm)
  filter_upwards [heq] with z hz
  change c * (∑ a, ENNReal.ofReal (f a z)) = 1 at hz
  have hsum : ∑ a, ENNReal.ofReal (f a z) = (Fintype.card I : ℝ≥0∞) := by
    have hh := congrArg (fun x : ℝ≥0∞ => (Fintype.card I : ℝ≥0∞) * x) hz
    simpa only [c, ← mul_assoc, ENNReal.mul_inv_cancel (a := (Fintype.card I : ℝ≥0∞))
      (by exact_mod_cast Fintype.card_ne_zero) (by simp), one_mul, mul_one] using hh
  have hh := congrArg ENNReal.toReal hsum
  simpa only [ENNReal.toReal_sum (fun a _ => ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (hf0 _ _), ENNReal.toReal_natCast] using hh

/-- Assume [measurability of f](hyp:hf), [measurability of g](hyp:hg), [the stated hg0 condition](hyp:hg0), [the stated hc condition](hyp:hc), and [the set hpriv](hyp:hpriv). [An all-event privacy inequality transfers to any measurable density versions](goal). -/
-- @node: row_density_privacy_ae
lemma row_density_privacy_ae {Z : Type} [MeasurableSpace Z]
    (mu : Measure Z) [IsFiniteMeasure mu] (f g : Z → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (c : ℝ) (hc : 0 ≤ c)
    (hpriv : ∀ E, MeasurableSet E →
      mu.withDensity (fun z => ENNReal.ofReal (f z)) E ≤
        ENNReal.ofReal c * mu.withDensity (fun z => ENNReal.ofReal (g z)) E) :
    ∀ᵐ z ∂mu, f z ≤ c * g z := by
  have hh : (fun z => ENNReal.ofReal (f z)) ≤ᵐ[mu]
      (fun z => ENNReal.ofReal (c * g z)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hf.ennreal_ofReal
    intro E hE _
    simp only [ENNReal.ofReal_mul hc]
    rw [lintegral_const_mul _ hg.ennreal_ofReal]
    simpa only [withDensity_apply _ hE] using hpriv E hE
  filter_upwards [hh] with z hz
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc (hg0 z))).mp hz

/-- Assume [the stated privacy condition for the protocol](hyp:hK), [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), [the stated hrep condition](hyp:hrep), [a privacy factor at least one](hyp:hc), and [the stated hpriv condition](hyp:hpriv). [A common measurable null-set repair makes normalization and privacy pointwise, without changing any represented row at any parameter](goal). -/
-- @node: repair_uniform_row_densities
lemma repair_uniform_row_densities {I H Z : Type} [Fintype I] [Nonempty I]
    [MeasurableSpace H] [MeasurableSpace Z] (K : I → Kernel H Z)
    (hK : ∀ a, IsMarkovKernel (K a)) (f : I → H × Z → ℝ)
    (hf : ∀ a, Measurable (f a)) (hf0 : ∀ a w, 0 ≤ f a w)
    (hrep : ∀ a h, (uniformRowAverage K h).withDensity
      (fun z => ENNReal.ofReal (f a (h, z))) = K a h)
    (c : ℝ) (hc : 1 ≤ c)
    (hpriv : ∀ a b h E, MeasurableSet E → K a h E ≤ ENNReal.ofReal c * K b h E) :
    ∃ g : I → H × Z → ℝ, (∀ a, Measurable (g a)) ∧
      (∀ a w, 0 ≤ g a w) ∧
      (∀ w, ∑ a, g a w = (Fintype.card I : ℝ)) ∧
      (∀ a b w, g a w ≤ c * g b w) ∧
      ∀ a h, (uniformRowAverage K h).withDensity
        (fun z => ENNReal.ofReal (g a (h, z))) = K a h := by
  classical
  let good : Set (H × Z) := {w | (∑ a, f a w) = (Fintype.card I : ℝ) ∧
    ∀ a b, f a w ≤ c * f b w}
  have hgood : MeasurableSet good := by
    have hp : MeasurableSet {w : H × Z | ∀ a b, f a w ≤ c * f b w} := by
      simpa only [Set.ofPred_forall, Pi.mul_apply] using (MeasurableSet.iInter fun a =>
        MeasurableSet.iInter fun b => measurableSet_le (hf a)
          ((measurable_const : Measurable (fun _ : H × Z => c)).mul (hf b)))
    exact (measurableSet_eq_fun (Finset.measurable_sum _ (fun a _ => hf a))
      measurable_const).inter hp
  have hae (h : H) : ∀ᵐ z ∂uniformRowAverage K h, (h, z) ∈ good := by
    let := uniformRowAverage_markov K hK
    have hsum := uniformRowAverage_density_sum_ae K hK h
      (fun a z => f a (h, z)) (fun a => (hf a).comp (by fun_prop))
      (fun a z => hf0 a (h, z)) (fun a => hrep a h)
    have hp : ∀ a b, ∀ᵐ z ∂uniformRowAverage K h, f a (h, z) ≤ c * f b (h, z) := by
      intro a b
      apply row_density_privacy_ae _ _ _ ((hf a).comp (by fun_prop))
        ((hf b).comp (by fun_prop)) (fun z => hf0 b (h, z)) c (by linarith)
      intro E hE
      simp only [Function.comp_def]
      rw [hrep a h, hrep b h]
      exact hpriv a b h E hE
    have hpall : ∀ᵐ z ∂uniformRowAverage K h, ∀ a b, f a (h, z) ≤ c * f b (h, z) :=
      ae_all_iff.mpr (fun a => ae_all_iff.mpr (hp a))
    filter_upwards [hsum, hpall] with z hz hpz
    exact ⟨hz, hpz⟩
  let g : I → H × Z → ℝ := fun a w => if w ∈ good then f a w else 1
  refine ⟨g, fun a => (hf a).piecewise hgood measurable_const, ?_, ?_, ?_, ?_⟩
  · intro a w
    dsimp [g]
    split_ifs
    · exact hf0 a w
    · norm_num
  · intro w
    by_cases hw : w ∈ good
    · simpa only [g, if_pos hw] using hw.1
    · simp [g, hw]
  · intro a b w
    by_cases hw : w ∈ good
    · simpa only [g, if_pos hw] using hw.2 a b
    · simpa only [g, if_neg hw, mul_one] using hc
  · intro a h
    have heq : (fun z => ENNReal.ofReal (g a (h, z))) =ᵐ[uniformRowAverage K h]
        (fun z => ENNReal.ofReal (f a (h, z))) := by
      filter_upwards [hae h] with z hz
      simp only [g, if_pos hz]
    exact withDensity_congr_ae heq |>.trans (hrep a h)

/-- Fix [the local protocol Q](hyp:Q) and [the participant index](hyp:i). [Stage reference rows are the uniform average of all paired-input rows, with the ancillary assignment already integrated out](goal). -/
-- @node: stageReferenceKernel
def stageReferenceKernel {n d : ℕ} (Q : LocalProtocol n (ObsRecord d)) (i : Fin n) :
    Kernel (Q.Seed × ProtocolHistory Q i) (Q.Message i) :=
  uniformRowAverage (fun a : PairedSymbol d =>
    (averagedKernel Q i).comap (fun h => ((a, h.1), h.2)) (by fun_prop))

/-- Assume [positive dimension](hyp:hd). [Each stage reference is a probability kernel, including at null histories](goal). -/
-- @node: stageReferenceKernel_markov
lemma stageReferenceKernel_markov {n d : ℕ} (Q : LocalProtocol n (ObsRecord d))
    (i : Fin n) (hd : 0 < d) : IsMarkovKernel (stageReferenceKernel Q i) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let := averagedKernel_markov Q i
  apply uniformRowAverage_markov
  intro a
  infer_instance

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN) and [positive dimension](hyp:hd). [The measurable RN gate gives nonnegative stage densities jointly in input, seed, history and message. The reference is the uniform input average, rather than a whole-transcript RN witness](goal). -/
-- @node: stage_density_of_gate
lemma stage_density_of_gate (hRN : MeasurableKernelRadonNikodym)
    {n d : ℕ} (Q : LocalProtocol n (ObsRecord d)) (i : Fin n) (hd : 0 < d) :
    ∃ f : ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ,
      Measurable f ∧ (∀ w, 0 ≤ f w) ∧ ∀ a r eta,
        (stageReferenceKernel Q i (r, eta)).withDensity
          (fun z => ENNReal.ofReal (f (((a, r), eta), z))) =
            averagedKernel Q i ((a, r), eta) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let := averagedKernel_markov Q i
  let := stageReferenceKernel_markov Q i hd
  let L := (stageReferenceKernel Q i).comap
    (fun w : (PairedSymbol d × Q.Seed) × ProtocolHistory Q i => (w.1.2, w.2))
    (by fun_prop)
  have hac : ∀ w, averagedKernel Q i w ≪ L w := by
    intro w
    exact row_absolutelyContinuous_uniformRowAverage
      (fun a : PairedSymbol d => (averagedKernel Q i).comap
        (fun h : Q.Seed × ProtocolHistory Q i => ((a, h.1), h.2)) (by fun_prop))
      w.1.1 (w.1.2, w.2)
  obtain ⟨f, hf, hrep⟩ := real_kernel_density_of_gate hRN (averagedKernel Q i) L hac
  refine ⟨fun w => max (f w) 0, hf.max measurable_const, fun w => le_max_right _ _, ?_⟩
  intro a r eta
  simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_zero, L, Kernel.comap_apply]
    using hrep ((a, r), eta)

/-- Assume [the stated hc condition](hyp:hc), [the stated hsum condition](hyp:hsum), and [the stated hpriv condition](hyp:hpriv). [Uniform normalization and pairwise privacy bound each row away from zero and above by the privacy factor](goal). -/
-- @node: normalized_private_row_bounds
lemma normalized_private_row_bounds {I : Type} [Fintype I] [Nonempty I]
    (f : I → ℝ) (c : ℝ) (hc : 0 < c)
    (hsum : ∑ a, f a = (Fintype.card I : ℝ))
    (hpriv : ∀ a b, f a ≤ c * f b) (a : I) : c⁻¹ ≤ f a ∧ f a ≤ c := by
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hpriv b a)
  have hhi := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hpriv a b)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum] at hlo
  rw [← Finset.mul_sum, hsum] at hhi
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hhi
  constructor
  · rw [← one_div, div_le_iff₀ hc]
    nlinarith
  · nlinarith

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [positive dimension](hyp:hd), [a nonnegative privacy budget](hyp:heps), and [sequential local privacy of the protocol](hyp:hQ). [Repaired stage densities jointly represent every private paired-input row and satisfy exact uniform normalization and privacy at every message, history and seed](goal). -/
-- @node: stage_density_repaired_of_gate
lemma stage_density_repaired_of_gate (hRN : MeasurableKernelRadonNikodym)
    {n d : ℕ} (Q : LocalProtocol n (ObsRecord d)) (i : Fin n) (hd : 0 < d)
    (eps : ℝ) (heps : 0 ≤ eps) (hQ : SequentialClass Q eps) :
    ∃ f : ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ,
      Measurable f ∧ (∀ w, 0 ≤ f w) ∧
      (∀ r eta z, (∑ a : PairedSymbol d, f (((a, r), eta), z)) = (2*d : ℝ)) ∧
      (∀ a b r eta z, f (((a, r), eta), z) ≤ Real.exp eps * f (((b, r), eta), z)) ∧
      (∀ w, Real.exp (-eps) ≤ f w ∧ f w ≤ Real.exp eps) ∧
      ∀ a r eta, (stageReferenceKernel Q i (r, eta)).withDensity
        (fun z => ENNReal.ofReal (f (((a, r), eta), z))) = averagedKernel Q i ((a, r), eta) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let := averagedKernel_markov Q i
  let K : PairedSymbol d → Kernel (Q.Seed × ProtocolHistory Q i) (Q.Message i) :=
    fun a => (averagedKernel Q i).comap (fun h => ((a, h.1), h.2)) (by fun_prop)
  obtain ⟨f, hf, hf0, hrep⟩ := stage_density_of_gate hRN Q i hd
  obtain ⟨g, hg, hg0, hsum, hpriv, hgrep⟩ := repair_uniform_row_densities K
    (fun _ => by dsimp [K]; infer_instance)
    (fun a w => f (((a, w.1.1), w.1.2), w.2))
    (fun a => hf.comp (by fun_prop)) (fun a w => hf0 _)
    (fun a h => hrep a h.1 h.2) (Real.exp eps) (Real.one_le_exp_iff.mpr heps)
    (fun a b h E hE => averagedProtocol_privacy Q eps hQ.privacy i a b h.2 h.1 E hE)
  have hjoint : Measurable (fun w : PairedSymbol d ×
      ((Q.Seed × ProtocolHistory Q i) × Q.Message i) => g w.1 w.2) := by
    apply measurable_from_prod_countable_right
    exact hg
  refine ⟨fun w => g w.1.1.1 ((w.1.1.2, w.1.2), w.2),
    hjoint.comp (show Measurable (fun w : ((PairedSymbol d × Q.Seed) ×
      ProtocolHistory Q i) × Q.Message i =>
        (w.1.1.1, ((w.1.1.2, w.1.2), w.2))) by fun_prop), ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    exact hg0 _ _
  · intro r eta z
    simpa only [PairedSymbol, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hsum ((r, eta), z)
  · intro a b r eta z
    exact hpriv a b ((r, eta), z)
  · intro w
    simpa only [Real.exp_neg] using normalized_private_row_bounds
      (fun a => g a ((w.1.1.2, w.1.2), w.2)) (Real.exp eps) (Real.exp_pos eps)
      (hsum _) (fun a b => hpriv a b _) w.1.1.1
  · intro a r eta
    exact hgrep a (r, eta)

end CausalSmith.Stat.LdpOptvalueUniformFrontier
