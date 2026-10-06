module
public import Causalean.Mathlib.InformationTheory.Fano
public import Causalean.Mathlib.InformationTheory.FiniteKL
public import Causalean.Mathlib.InformationTheory.FiniteMutualInformation
public import Causalean.Mathlib.InformationTheory.ProductKLLeCam
public import Causalean.Stat.Minimax.KLTail
public import Causalean.Stat.Minimax.LeCam
public import Causalean.Stat.Minimax.Mixture

/-!
# Fano lower bounds for general measurable experiments

This file connects finite-alphabet entropy Fano to general measurable statistical
experiments. The main bounds use the uniform-prior mutual information
`card(ι)⁻¹ ∑ᵢ KL(Pᵢ ‖ P̄)`, where `P̄` is the uniform mixture, and therefore retain
the logarithmic packing-size gain used in minimax lower bounds.

The earlier total-variation union bound remains available under the explicit
`tv_multiple_testing_*` names; it is not an entropy Fano inequality.

References: Tsybakov (2009), Theorem 2.5 and Corollary 2.6; Yu (1997), Lemma 3;
Wainwright (2019), Proposition 15.12.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {Θ : Type*} [PseudoMetricSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]

/-- For [a sample space](hyp:Ω), [a pseudo-metric parameter space](hyp:Θ), [an
estimator from the sample space to the parameter space](hyp:est), [a parameter value](hyp:θ), and
[a real radius](hyp:s), the [acceptance region](goal) is the set
of sample points at which the estimator lies at distance strictly less than that radius from the
parameter value. -/
def acceptanceRegion (est : Ω → Θ) (θ : Θ) (s : ℝ) : Set Ω :=
  {ω | dist (est ω) θ < s}

/-- A measurable estimator has a measurable acceptance region around any target. -/
theorem measurableSet_acceptanceRegion {est : Ω → Θ} (hest : Measurable est)
    (θ : Θ) (s : ℝ) : MeasurableSet (acceptanceRegion est θ s) := by
  have h : acceptanceRegion est θ s = {ω | s ≤ dist (est ω) θ}ᶜ := by
    ext ω; simp [acceptanceRegion, not_le]
  rw [h]
  exact (measurableSet_error hest θ s).compl

omit [MeasurableSpace Θ] [OpensMeasurableSpace Θ] in
/-- The acceptance region is the complement of the error region. -/
theorem acceptanceRegion_compl (est : Ω → Θ) (θ : Θ) (s : ℝ) :
    (acceptanceRegion est θ s)ᶜ = {ω | s ≤ dist (est ω) θ} := by
  ext ω; simp [acceptanceRegion, not_lt]

omit [MeasurableSpace Θ] [OpensMeasurableSpace Θ] in
/-- **Disjointness of acceptance regions.** If two target values are `2s`-separated,
their acceptance regions are disjoint: a point within `s` of both would force the
targets within `2s` of each other. -/
theorem acceptanceRegion_disjoint {est : Ω → Θ} {θ₀ θ₁ : Θ} {s : ℝ}
    (hsep : 2 * s ≤ dist θ₀ θ₁) :
    Disjoint (acceptanceRegion est θ₀ s) (acceptanceRegion est θ₁ s) := by
  rw [Set.disjoint_left]
  intro ω h0 h1
  have h0' : dist (est ω) θ₀ < s := h0
  have h1' : dist (est ω) θ₁ < s := h1
  have htri : dist θ₀ θ₁ ≤ dist (est ω) θ₀ + dist (est ω) θ₁ := by
    simpa [dist_comm] using dist_triangle θ₀ (est ω) θ₁
  linarith

variable {ι : Type*}

omit [MeasurableSpace Θ] [OpensMeasurableSpace Θ] in
/-- **Pairwise disjointness** of the acceptance regions of a `2s`-separated family. -/
theorem acceptanceRegion_pairwiseDisjoint {est : Ω → Θ} {θ : ι → Θ} {s : ℝ}
    (hsep : ∀ i k, i ≠ k → 2 * s ≤ dist (θ i) (θ k)) :
    Pairwise (Function.onFun Disjoint (fun i => acceptanceRegion est (θ i) s)) :=
  fun i k hik => acceptanceRegion_disjoint (hsep i k hik)

variable [Fintype ι] (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]

/-- For [a nonempty finite family of experiment laws](hyp:P), the [uniform mixture
law](goal) assigns weight `1 / card ι` to every member of the family. -/
noncomputable def uniformMixture [Nonempty ι] : Measure Ω :=
  mixture (fun _ : ι => (Fintype.card ι : ℝ≥0∞)⁻¹) P

/-- The constant weights used by a nonempty finite uniform mixture sum to one. -/
private theorem uniformWeight_sum [Nonempty ι] :
    ∑ _i : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply ENNReal.mul_inv_cancel <;> simp [Fintype.card_ne_zero]

/-- The [uniform mixture of probability laws](hyp:P) [is itself a probability law](goal). -/
theorem uniformMixture_isProbabilityMeasure [Nonempty ι] :
    IsProbabilityMeasure (uniformMixture P) := by
  exact mixture_isProbabilityMeasure _ uniformWeight_sum P

omit [∀ i, IsProbabilityMeasure (P i)] in
/-- Every [member `P i` of a nonempty finite experiment](hyp:P) [is absolutely
continuous with respect to the uniform mixture](goal). -/
lemma absolutelyContinuous_uniformMixture [Nonempty ι] (i : ι) :
    P i ≪ uniformMixture P := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hzero
  have hsumzero :
      ∑ j, (Fintype.card ι : ℝ≥0∞)⁻¹ * P j A = 0 := by
    simpa [uniformMixture, mixture_apply] using hzero
  have htermle :
      (Fintype.card ι : ℝ≥0∞)⁻¹ * P i A ≤
        ∑ j, (Fintype.card ι : ℝ≥0∞)⁻¹ * P j A :=
    Finset.single_le_sum
      (f := fun j => (Fintype.card ι : ℝ≥0∞)⁻¹ * P j A)
      (fun _j _ => zero_le) (Finset.mem_univ i)
  have htermzero : (Fintype.card ι : ℝ≥0∞)⁻¹ * P i A = 0 := by
    apply le_antisymm
    · exact hsumzero ▸ htermle
    · exact zero_le
  exact (mul_eq_zero.mp htermzero).resolve_left (by simp)

/-- For [a nonempty finite family of experiment laws](hyp:P), the [uniform-prior
mutual information](goal) is the average Kullback--Leibler divergence from each
law to their uniform mixture.

This is `I(V;X)` when `V` is uniform on the hypothesis index and `X | V=i` has
law `P i`. -/
noncomputable def uniformMutualInformation [Nonempty ι] : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ∑ i, (_root_.InformationTheory.klDiv (P i) (uniformMixture P)).toReal

omit [∀ i, IsProbabilityMeasure (P i)] in
/-- For [a nonempty finite family of measures](hyp:P) and [an index](hyp:i), [the indexed
measure is bounded by the cardinality times the uniform mixture](goal). -/
lemma uniformComponent_le_card_smul_mixture [Nonempty ι] (i : ι) :
    P i ≤ (Fintype.card ι : NNReal) • uniformMixture P := by
  apply Measure.le_iff.2
  intro A _hA
  change P i A ≤ (Fintype.card ι : ENNReal) * uniformMixture P A
  rw [uniformMixture, mixture_apply
    (fun _ : ι => (Fintype.card ι : ENNReal)⁻¹) P A]
  have hterm :
      (Fintype.card ι : ENNReal)⁻¹ * P i A ≤
        ∑ j, (Fintype.card ι : ENNReal)⁻¹ * P j A :=
    Finset.single_le_sum
      (f := fun j => (Fintype.card ι : ENNReal)⁻¹ * P j A)
      (fun _j _ => zero_le) (Finset.mem_univ i)
  calc
    P i A = (Fintype.card ι : ENNReal) *
        ((Fintype.card ι : ENNReal)⁻¹ * P i A) := by
      rw [← mul_assoc,
        ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (by simp), one_mul]
    _ ≤ (Fintype.card ι : ENNReal) *
        ∑ j, (Fintype.card ι : ENNReal)⁻¹ * P j A := by gcongr

/-- For [a nonempty finite family of measures](hyp:P) and [an index](hyp:i), [the
Radon--Nikodym density of that component with respect to the uniform mixture is at most the
family cardinality almost everywhere](goal). -/
lemma rnDeriv_uniformMixture_toReal_le_card [Nonempty ι] (i : ι) :
    (fun x => ((P i).rnDeriv (uniformMixture P) x).toReal) ≤ᵐ[uniformMixture P]
      fun _ => (Fintype.card ι : ℝ) := by
  letI : IsProbabilityMeasure (uniformMixture P) := uniformMixture_isProbabilityMeasure P
  let N : NNReal := Fintype.card ι
  have hN : N ≠ 0 := by simp [N, Fintype.card_ne_zero]
  have hle : P i ≤ N • uniformMixture P := by
    simpa [N] using uniformComponent_le_card_smul_mixture P i
  have hs := Measure.rnDeriv_le_one_of_le hle
  have hscaledAc : uniformMixture P ≪ N • uniformMixture P :=
    Measure.absolutelyContinuous_smul (by exact_mod_cast hN)
  have hs' := hscaledAc.ae_le hs
  have heq := Measure.rnDeriv_smul_right (P i) (uniformMixture P) hN
  filter_upwards [hs', heq] with x hx heqx
  simp only [Pi.one_apply] at hx
  rw [heqx] at hx
  simp only [Pi.smul_apply, ENNReal.smul_def] at hx
  have hmul : (P i).rnDeriv (uniformMixture P) x ≤ (N : ENNReal) := by
    calc
      (P i).rnDeriv (uniformMixture P) x =
          (N : ENNReal) * ((N : ENNReal)⁻¹ *
            (P i).rnDeriv (uniformMixture P) x) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast hN) (by simp), one_mul]
      _ ≤ (N : ENNReal) * 1 := by
        gcongr
        simpa [ENNReal.coe_inv, hN] using hx
      _ = N := mul_one _
  simpa [N] using (ENNReal.toReal_le_coe_of_le_coe hmul)

/-- For [a nonempty finite family of probability laws](hyp:P) and [an index](hyp:i),
[the KL divergence from that component to the uniform mixture is finite](goal). -/
theorem klDiv_uniformMixture_ne_top [Nonempty ι] (i : ι) :
    _root_.InformationTheory.klDiv (P i) (uniformMixture P) ≠ ⊤ := by
  letI : IsProbabilityMeasure (uniformMixture P) := uniformMixture_isProbabilityMeasure P
  have hac := absolutelyContinuous_uniformMixture P i
  have hN1 : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card ι)
  have hlogN : 0 ≤ Real.log (Fintype.card ι) := Real.log_nonneg hN1
  let C : ℝ := (Fintype.card ι : ℝ) * Real.log (Fintype.card ι) + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmulInt : Integrable
      (fun x => ((P i).rnDeriv (uniformMixture P) x).toReal *
        Real.log ((P i).rnDeriv (uniformMixture P) x).toReal)
      (uniformMixture P) := by
    apply (integrable_const C).mono'
    · fun_prop
    · filter_upwards [rnDeriv_uniformMixture_toReal_le_card P i] with x hx
      let r := ((P i).rnDeriv (uniformMixture P) x).toReal
      have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
      change |r * Real.log r| ≤ C
      by_cases hr1 : r ≤ 1
      · rw [abs_of_nonpos (Real.mul_log_nonpos hr0 hr1)]
        have hneg := Real.negMulLog_le_one_sub_self hr0
        dsimp [Real.negMulLog] at hneg
        dsimp [C]
        nlinarith
      · have h1r : 1 ≤ r := le_of_not_ge hr1
        rw [abs_of_nonneg (Real.mul_log_nonneg h1r)]
        have hlog : Real.log r ≤ Real.log (Fintype.card ι) :=
          Real.log_le_log (by positivity) hx
        dsimp [C]
        nlinarith
  have hllr : Integrable (llr (P i) (uniformMixture P)) (P i) :=
    (integrable_rnDeriv_mul_log_iff hac).mp hmulInt
  exact _root_.InformationTheory.klDiv_ne_top hac hllr

/-- For [a nonempty finite family of probability laws](hyp:P) and [an index](hyp:i),
[the KL divergence from that component to the uniform mixture is at most the logarithm of
the family cardinality](goal). -/
theorem klDiv_uniformMixture_toReal_le_log_card [Nonempty ι] (i : ι) :
    (_root_.InformationTheory.klDiv (P i) (uniformMixture P)).toReal ≤
      Real.log (Fintype.card ι) := by
  letI : IsProbabilityMeasure (uniformMixture P) := uniformMixture_isProbabilityMeasure P
  have hfin := klDiv_uniformMixture_ne_top P i
  have hac := (_root_.InformationTheory.klDiv_ne_top_iff.mp hfin).1
  have hllr := (_root_.InformationTheory.klDiv_ne_top_iff.mp hfin).2
  have hllrBound : llr (P i) (uniformMixture P) ≤ᵐ[P i]
      fun _ => Real.log (Fintype.card ι) := by
    filter_upwards [hac.ae_le (rnDeriv_uniformMixture_toReal_le_card P i),
      Measure.rnDeriv_pos hac,
      hac.ae_le (Measure.rnDeriv_ne_top (P i) (uniformMixture P))] with x hx hpos htop
    exact Real.log_le_log (ENNReal.toReal_pos hpos.ne' htop) hx
  rw [_root_.InformationTheory.toReal_klDiv_of_measure_eq hac (by simp)]
  simpa using integral_mono_ae hllr (integrable_const _) hllrBound

omit [Fintype ι] in
/-- For a [sample size](hyp:n) and [two laws in the experiment](hyp:j,k), if
[the first law is absolutely continuous with respect to the second](hyp:hac) and
[their one-observation log-likelihood ratio is integrable](hyp:hint), then [the
KL divergence between the corresponding i.i.d. product laws equals `n` times
the one-observation KL divergence](goal). -/
theorem iid_experiment_kl_eq_nat_mul (n : ℕ) (j k : ι)
    (hac : P j ≪ P k)
    (hint : Integrable (llr (P j) (P k)) (P j)) :
    (_root_.InformationTheory.klDiv
        (Measure.pi (fun _ : Fin n => P j))
        (Measure.pi (fun _ : Fin n => P k))).toReal =
      (n : ℝ) * (_root_.InformationTheory.klDiv (P j) (P k)).toReal :=
  Causalean.Mathlib.InformationTheory.productKL_tensorization_of_finite
    n (P j) (P k) hac hint

/-- A reference hypothesis assigns total mass `≤ 1` across the disjoint acceptance
regions, since their union has measure `≤ 1`. -/
theorem sum_refReal_acceptance_le {est : Ω → Θ} (hest : Measurable est) {θ : ι → Θ}
    {s : ℝ} (hsep : ∀ i k, i ≠ k → 2 * s ≤ dist (θ i) (θ k)) (i₀ : ι) :
    ∑ i, (P i₀).real (acceptanceRegion est (θ i) s) ≤ 1 := by
  have hmeas : ∀ i, MeasurableSet (acceptanceRegion est (θ i) s) := fun i =>
    measurableSet_acceptanceRegion hest (θ i) s
  have hdisj : Pairwise
      (Function.onFun Disjoint (fun i => acceptanceRegion est (θ i) s)) :=
    acceptanceRegion_pairwiseDisjoint (est := est) (θ := θ) (s := s) hsep
  have hunion : (P i₀) (⋃ i, acceptanceRegion est (θ i) s)
      = ∑ i, (P i₀) (acceptanceRegion est (θ i) s) := by
    rw [measure_iUnion hdisj hmeas, tsum_fintype]
  have hle : (P i₀) (⋃ i, acceptanceRegion est (θ i) s) ≤ 1 := by
    calc (P i₀) (⋃ i, acceptanceRegion est (θ i) s)
        ≤ (P i₀) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hfin : ∀ i, (P i₀) (acceptanceRegion est (θ i) s) ≠ ⊤ := fun i =>
    measure_ne_top _ _
  have hsumeq : ∑ i, (P i₀).real (acceptanceRegion est (θ i) s)
      = ((P i₀) (⋃ i, acceptanceRegion est (θ i) s)).toReal := by
    rw [hunion, ENNReal.toReal_sum (fun i _ => hfin i)]; rfl
  rw [hsumeq]
  calc ((P i₀) (⋃ i, acceptanceRegion est (θ i) s)).toReal
      ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hle
    _ = 1 := ENNReal.toReal_one

/-- **Heart of Fano.** The total probability of correct recovery, summed over the
family, is at most `1 + ∑ᵢ tvDist (P i₀) (P i)`: comparing each `Pᵢ(A i)` to the
reference `P i₀(A i)` costs one `tvDist`, and the reference masses sum to `≤ 1`. -/
theorem sum_correct_le {est : Ω → Θ} (hest : Measurable est) {θ : ι → Θ} {s : ℝ}
    (hsep : ∀ i k, i ≠ k → 2 * s ≤ dist (θ i) (θ k)) (i₀ : ι) :
    ∑ i, (P i).real (acceptanceRegion est (θ i) s)
      ≤ 1 + ∑ i, tvDist (P i₀) (P i) := by
  have hterm : ∀ i, (P i).real (acceptanceRegion est (θ i) s)
      ≤ (P i₀).real (acceptanceRegion est (θ i) s) + tvDist (P i₀) (P i) := by
    intro i
    have hmeas : MeasurableSet (acceptanceRegion est (θ i) s) :=
      measurableSet_acceptanceRegion hest (θ i) s
    have h := measureReal_sub_le_tvDist (μ := P i₀) (ν := P i) hmeas
    linarith
  calc ∑ i, (P i).real (acceptanceRegion est (θ i) s)
      ≤ ∑ i, ((P i₀).real (acceptanceRegion est (θ i) s) + tvDist (P i₀) (P i)) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i, (P i₀).real (acceptanceRegion est (θ i) s))
          + ∑ i, tvDist (P i₀) (P i) := by rw [Finset.sum_add_distrib]
    _ ≤ 1 + ∑ i, tvDist (P i₀) (P i) := by
        have := sum_refReal_acceptance_le P hest hsep i₀
        linarith

/-- **Total-variation multiple-testing average bound.** For [a measurable
estimator `est`](hyp:hest) and a family of parameter values that are [pairwise
`2s`-separated](hyp:hsep), [the average probability of error over the
`N = card ι` hypotheses is at least
`1 − (1 + ∑ᵢ tvDist (P i₀) (P i)) / N`](goal). -/
theorem tv_multiple_testing_average_lower {est : Ω → Θ} (hest : Measurable est)
    {θ : ι → Θ} {s : ℝ}
    (hsep : ∀ i k, i ≠ k → 2 * s ≤ dist (θ i) (θ k)) (i₀ : ι) :
    1 - (1 + ∑ i, tvDist (P i₀) (P i)) / (Fintype.card ι)
      ≤ (∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)}) / (Fintype.card ι) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN, Nat.cast_pos]
    exact Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have herr : ∀ i, (P i).real {ω | s ≤ dist (est ω) (θ i)}
      = 1 - (P i).real (acceptanceRegion est (θ i) s) := by
    intro i
    rw [← acceptanceRegion_compl est (θ i) s,
      measureReal_compl (measurableSet_acceptanceRegion hest (θ i) s)]
    simp [probReal_univ]
  have hsumerr : ∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)}
      = N - ∑ i, (P i).real (acceptanceRegion est (θ i) s) := by
    simp_rw [herr]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hN]
  have hcorrect := sum_correct_le P hest hsep i₀
  rw [hsumerr, le_div_iff₀ hNpos, sub_mul, div_mul_cancel₀ _ hNne, one_mul]
  linarith [hcorrect]

/-- **Total-variation multiple-testing bound (uniform `β`).** For [a measurable estimator
`est`](hyp:hest) and a family of parameter values that are [pairwise
`2s`-separated](hyp:hsep), if [every hypothesis's law is within total variation `β` of the
reference `P i₀`](hyp:hβ), then [some hypothesis has error probability at least
`1 − 1/N − β`](goal).  This is the directly usable minimax statement:
choosing the number of hypotheses `N` large and the divergence `β` small forces
error. -/
theorem tv_multiple_testing_lower {est : Ω → Θ} (hest : Measurable est)
    {θ : ι → Θ} {s : ℝ}
    (hsep : ∀ i k, i ≠ k → 2 * s ≤ dist (θ i) (θ k)) (i₀ : ι) {β : ℝ}
    (hβ : ∀ i, tvDist (P i₀) (P i) ≤ β) :
    ∃ i, 1 - 1 / (Fintype.card ι) - β
      ≤ (P i).real {ω | s ≤ dist (est ω) (θ i)} := by
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN, Nat.cast_pos]; exact Fintype.card_pos_iff.mpr ⟨i₀⟩
  have havg := tv_multiple_testing_average_lower P hest hsep i₀
  rw [← hN] at havg
  have hsumtv : ∑ i, tvDist (P i₀) (P i) ≤ N * β := by
    calc ∑ i, tvDist (P i₀) (P i) ≤ ∑ _i : ι, β := Finset.sum_le_sum (fun i _ => hβ i)
      _ = N * β := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
  have hstep : (1 + ∑ i, tvDist (P i₀) (P i)) / N ≤ 1 / N + β := by
    rw [add_div]
    have hle : (∑ i, tvDist (P i₀) (P i)) / N ≤ β := by
      rw [div_le_iff₀ hNpos]; linarith [hsumtv]
    linarith
  have hbound : 1 - 1 / N - β
      ≤ (∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)}) / N := by
    refine le_trans ?_ havg
    linarith [hstep]
  by_contra hcon
  push Not at hcon
  have hstrict : ∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)} < N * (1 - 1 / N - β) := by
    calc ∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)}
        < ∑ _i : ι, (1 - 1 / N - β) :=
          Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨i₀⟩)
            (fun i _ => hcon i)
      _ = N * (1 - 1 / N - β) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
  rw [le_div_iff₀ hNpos] at hbound
  nlinarith [hbound, hstrict]

private theorem fano_decoder_average_error
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι]
    (hcard : 2 ≤ Fintype.card ι) (decode : Ω → ι) (hdecode : Measurable decode) :
    1 - (uniformMutualInformation P + Real.log 2) /
        Real.log (Fintype.card ι) ≤
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, (P i).real {ω | decode ω ≠ i} := by
  classical
  let N : ℝ := Fintype.card ι
  let u : ℝ := N⁻¹
  let Pbar : Measure Ω := uniformMixture P
  let R : ι → Measure ι := fun i => Measure.map decode (P i)
  let Rbar : Measure ι := Measure.map decode Pbar
  let r : ι → ι → ℝ := fun i y => (R i).real {y}
  let p : ι × ι → ℝ := fun z => u * r z.1 z.2
  let hPbar : IsProbabilityMeasure Pbar := uniformMixture_isProbabilityMeasure P
  let hR : ∀ i, IsProbabilityMeasure (R i) := fun _i =>
    Measure.isProbabilityMeasure_map hdecode.aemeasurable
  let hRbar : IsProbabilityMeasure Rbar :=
    Measure.isProbabilityMeasure_map hdecode.aemeasurable
  have hfin : ∀ i,
      _root_.InformationTheory.klDiv (P i) (uniformMixture P) ≠ ⊤ :=
    klDiv_uniformMixture_ne_top P
  have hr0 : ∀ i y, 0 ≤ r i y := fun _i _y => measureReal_nonneg
  have hrsum : ∀ i, ∑ y, r i y = 1 := by
    intro i
    simpa [r, probReal_univ] using
      (sum_measureReal_singleton (μ := R i) (Finset.univ : Finset ι))
  have hp0 : ∀ z, 0 ≤ p z := fun z => mul_nonneg (by positivity) (hr0 z.1 z.2)
  have hpsum : ∑ z, p z = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [p, ← Finset.mul_sum, hrsum]
    simp [u, N, Fintype.card_ne_zero]
  have hRbarMass : ∀ y, Rbar.real {y} = u * ∑ i, r i y := by
    intro y
    rw [show Rbar.real {y} = Pbar.real (decode ⁻¹' {y}) by
      simp [Rbar, Measure.real, Measure.map_apply hdecode (measurableSet_singleton y)]]
    simp only [Pbar, uniformMixture, mixture_apply, Measure.real]
    rw [ENNReal.toReal_sum]
    · simp only [ENNReal.toReal_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [ENNReal.toReal_inv]
      simp only [ENNReal.toReal_natCast, r, R, Measure.real]
      rw [Measure.map_apply hdecode (measurableSet_singleton y)]
    · intro i _hi
      exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  have hRac : ∀ i, R i ≪ Rbar := fun i =>
    (absolutelyContinuous_uniformMixture P i).map hdecode
  have hfiniteR : ∀ i, _root_.InformationTheory.klDiv (R i) Rbar ≠ ⊤ := by
    intro i
    exact ne_top_of_le_ne_top (hfin i)
      (_root_.InformationTheory.klDiv_map_le (P i) Pbar hdecode)
  have hinfoEq :
      Real.log N - Causalean.Mathlib.InformationTheory.condEntropy p =
        u * ∑ i, (_root_.InformationTheory.klDiv (R i) Rbar).toReal := by
    rw [show Real.log N = Real.log (Fintype.card ι) by rfl,
      show u = (Fintype.card ι : ℝ)⁻¹ by rfl,
      Causalean.Mathlib.InformationTheory.uniform_condEntropy_kl_identity r hr0 hrsum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Causalean.Mathlib.InformationTheory.klDiv_toReal_eq_sum_measureReal
      (R i) Rbar (hRac i)]
    simp only [r]
    congr 1
    funext y
    rw [hRbarMass]
  have hinfoLe :
      u * ∑ i, (_root_.InformationTheory.klDiv (R i) Rbar).toReal ≤
        uniformMutualInformation P := by
    simp only [uniformMutualInformation, u, N]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _hi
    exact (ENNReal.toReal_le_toReal (hfiniteR i) (hfin i)).2
      (_root_.InformationTheory.klDiv_map_le (P i) (uniformMixture P) hdecode)
  have hfano := Causalean.Mathlib.InformationTheory.fano_error_lower_bound
    hp0 hpsum hcard (fun y : ι => y)
  have hlogpos : 0 < Real.log N := by
    apply Real.log_pos
    dsimp [N]
    exact_mod_cast (show 1 < Fintype.card ι by omega)
  have herrorInfo :
      1 - (u * ∑ i, (_root_.InformationTheory.klDiv (R i) Rbar).toReal +
          Real.log 2) / Real.log N ≤
        Causalean.Mathlib.InformationTheory.errorProb p (fun y : ι => y) := by
    change (Causalean.Mathlib.InformationTheory.condEntropy p - Real.log 2) /
      Real.log N ≤ _ at hfano
    rw [← hinfoEq]
    convert hfano using 1
    field_simp [hlogpos.ne']
    ring
  have herrorEq :
      Causalean.Mathlib.InformationTheory.errorProb p (fun y : ι => y) =
        u * ∑ i, (P i).real {ω | decode ω ≠ i} := by
    rw [Causalean.Mathlib.InformationTheory.errorProb_def, Fintype.sum_prod_type]
    simp only [p]
    calc
      (∑ i, ∑ y, if i = y then 0 else u * r i y) =
          ∑ i, u * ∑ y, (if i = y then 0 else r i y) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _hy
            by_cases hiy : i = y <;> simp [hiy]
      _ = u * ∑ i, (P i).real {ω | decode ω ≠ i} := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        congr 1
        have hinner : (∑ y, if i = y then 0 else r i y) = 1 - r i i := by
          calc
            (∑ y, if i = y then 0 else r i y) =
                ∑ y, (r i y - if y = i then r i y else 0) := by
                  apply Finset.sum_congr rfl
                  intro y _hy
                  by_cases hy : y = i
                  · simp [hy]
                  · simp [hy, Ne.symm hy]
            _ = (∑ y, r i y) - ∑ y, (if y = i then r i y else 0) := by
                  rw [Finset.sum_sub_distrib]
            _ = 1 - r i i := by
                  rw [hrsum]
                  simp
        rw [hinner]
        have hset : {ω | decode ω ≠ i} = (decode ⁻¹' {i})ᶜ := by
          ext ω
          simp
        rw [hset, measureReal_compl (hdecode (measurableSet_singleton i)), probReal_univ]
        congr 1
        simp only [r, R, Measure.real]
        rw [Measure.map_apply hdecode (measurableSet_singleton i)]
  rw [herrorEq] at herrorInfo
  refine le_trans ?_ herrorInfo
  dsimp [N, u]
  gcongr

/-- **Fano's average-error lower bound.** For [a measurable estimator](hyp:hest),
a finite experiment, and parameter values that are [pairwise separated by at least
`2s`](hyp:hsep), assuming [the hypothesis count is at least two](hyp:hcard),
[the average probability of estimation error at radius `s` is at least
`1 - (I(V;X) + log 2) / log(card ι)`](goal).

Here `I(V;X)` is `uniformMutualInformation P`, the average KL divergence to the
uniform mixture. This is the mutual-information average-error step underlying the
Fano minimax methods of Yu (1997), Lemma 3, and Wainwright (2019), Proposition 15.12;
those published results add divergence assumptions and pass to worst-case or minimax risk. -/
theorem fano_average_error [Nonempty ι]
    {est : Ω → Θ} (hest : Measurable est) {θ : ι → Θ} {s : ℝ}
    (hsep : ∀ i k, i ≠ k → 2 * s ≤ dist (θ i) (θ k))
    (hcard : 2 ≤ Fintype.card ι) :
    1 - (uniformMutualInformation P + Real.log 2) /
        Real.log (Fintype.card ι) ≤
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)} := by
  letI : MeasurableSpace ι := ⊤
  have hmeas : ∀ i, MeasurableSet (acceptanceRegion est (θ i) s) := fun i =>
    measurableSet_acceptanceRegion hest (θ i) s
  obtain ⟨decode, hdecode, hagree⟩ := exists_measurable_piecewise
    (fun i => acceptanceRegion est (θ i) s) hmeas
    (fun i _ω => i) (fun _i => measurable_const) (by
      intro i k hik ω hω
      exact (Set.disjoint_left.mp
        (acceptanceRegion_disjoint (est := est) (hsep i k hik)) hω.1 hω.2).elim)
  have hdecoder := fano_decoder_average_error P hcard decode hdecode
  refine le_trans hdecoder ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _hi
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  by_contra hgood
  have hacc : ω ∈ acceptanceRegion est (θ i) s := by
    simpa [acceptanceRegion, not_le] using hgood
  exact hω (hagree i hacc)

/-- **Fano's worst-hypothesis lower bound.** Under [measurability of the estimator](hyp:hest),
[pairwise `2s` separation](hyp:hsep), and [at least two hypotheses](hyp:hcard),
[some experiment law assigns error
probability at least `1 - (I(V;X) + log 2) / log(card ι)`](goal).

This is the directly usable minimax corollary of `fano_average_error`. -/
theorem fano_exists_error [Nonempty ι]
    {est : Ω → Θ} (hest : Measurable est) {θ : ι → Θ} {s : ℝ}
    (hsep : ∀ i k, i ≠ k → 2 * s ≤ dist (θ i) (θ k))
    (hcard : 2 ≤ Fintype.card ι) :
    ∃ i, 1 - (uniformMutualInformation P + Real.log 2) /
        Real.log (Fintype.card ι) ≤
      (P i).real {ω | s ≤ dist (est ω) (θ i)} := by
  let B := 1 - (uniformMutualInformation P + Real.log 2) /
    Real.log (Fintype.card ι)
  have havg := fano_average_error P hest hsep hcard
  by_contra hcon
  push Not at hcon
  have hcardpos : 0 < (Fintype.card ι : ℝ) := by positivity
  have hstrict :
      ∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)} <
        (Fintype.card ι : ℝ) * B := by
    calc
      ∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)} < ∑ _i : ι, B :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          (fun i _hi => hcon i)
      _ = (Fintype.card ι : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  dsimp [B] at hstrict ⊢
  have hmul := mul_le_mul_of_nonneg_left havg hcardpos.le
  have hcardne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcardpos
  have hcancel :
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ *
        ∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)}) =
      ∑ i, (P i).real {ω | s ≤ dist (est ω) (θ i)} := by
    field_simp [hcardne]
  rw [hcancel] at hmul
  exact (not_lt_of_ge hmul) hstrict

end Causalean.Stat
