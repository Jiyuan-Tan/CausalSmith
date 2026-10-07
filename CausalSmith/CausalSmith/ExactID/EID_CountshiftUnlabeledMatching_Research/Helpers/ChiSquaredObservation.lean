module

public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.Mixture.Iid
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-! Conditional Jensen contracts the chi-squared divergence when an experiment
is reduced to a measurable observation, and supplies the integrability required
by the subsequent total-variation bound. -/

public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- A measurable observation preserves domination and square-integrability of
the likelihood deviation, and cannot increase its chi-squared divergence. -/
-- @node: chiSq_observation_contraction
lemma chiSq_observation_contraction {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (g : α → β) (hg : Measurable g) (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2) ν) :
    μ.map g ≪ ν.map g ∧
      Integrable (fun y => (((μ.map g).rnDeriv (ν.map g) y).toReal - 1) ^ 2)
        (ν.map g) ∧
      Causalean.Stat.chiSqDiv (μ.map g) (ν.map g) ≤ Causalean.Stat.chiSqDiv μ ν := by
  have hcv : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => (x - 1) ^ 2) := by
    have hs := (even_two.convexOn_pow (𝕜 := ℝ)).translate_right (-1 : ℝ)
    have hu : ConvexOn ℝ Set.univ (fun x : ℝ => (x - 1) ^ 2) := by
      simpa [Function.comp_def, sub_eq_add_neg, add_comm] using hs
    exact hu.subset (Set.subset_univ _) (convex_Ici _)
  have hf : StronglyMeasurable (fun x : ℝ => (x - 1) ^ 2) := by fun_prop
  have hc : ContinuousWithinAt (fun x : ℝ => (x - 1) ^ 2) (Set.Ici 0) 0 := by
    fun_prop
  have hout := hcv.integrable_comp_rnDeriv_map hac hg hf hc hint
  refine ⟨hac.map hg, hout, ?_⟩
  unfold Causalean.Stat.chiSqDiv
  rw [integral_map hg.aemeasurable hout.aestronglyMeasurable]
  calc
    (∫ x, (((μ.map g).rnDeriv (ν.map g) (g x)).toReal - 1) ^ 2 ∂ν) ≤
        ∫ x, (ν[fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2 |
          ‹MeasurableSpace β›.comap g]) x ∂ν :=
      integral_mono_ae (hout.comp_measurable hg) integrable_condExp
        (hcv.comp_rnDeriv_map_le hac hg hf hc hint)
    _ = _ := integral_condExp hg.comap_le

/-- Retaining the latent coordinate and sampling from the same probability kernel
preserves chi-squared divergence exactly, including square-integrability. -/
-- @node: chiSq_common_kernel_joint
lemma chiSq_common_kernel_joint {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2) ν) :
    (μ ⊗ₘ κ) ≪ (ν ⊗ₘ κ) ∧
      Integrable (fun y => (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) y).toReal - 1) ^ 2)
        (ν ⊗ₘ κ) ∧
      Causalean.Stat.chiSqDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = Causalean.Stat.chiSqDiv μ ν := by
  have hrn := rnDeriv_measure_compProd_left μ ν κ
  have heq : (fun y => (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) y).toReal - 1) ^ 2) =ᵐ[ν ⊗ₘ κ]
      fun y : α × β => ((μ.rnDeriv ν y.1).toReal - 1) ^ 2 :=
    hrn.mono (fun _ h => by simp only [h])
  have hm : Measurable (fun y : α × β => ((μ.rnDeriv ν y.1).toReal - 1) ^ 2) :=
    (((Measure.measurable_rnDeriv μ ν).comp measurable_fst).ennreal_toReal.sub
      measurable_const).pow_const 2
  have hi : Integrable (fun y : α × β => ((μ.rnDeriv ν y.1).toReal - 1) ^ 2)
      (ν ⊗ₘ κ) := by
    apply (Measure.integrable_compProd_iff hm.aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall (fun x => by
        simpa only using
          (integrable_const (((μ.rnDeriv ν x).toReal - 1) ^ 2) : Integrable _ (κ x)))
    · simpa using hint.norm
  refine ⟨hac.compProd_left κ, hi.congr heq.symm, ?_⟩
  unfold Causalean.Stat.chiSqDiv
  rw [integral_congr_ae heq, Measure.integral_compProd hi]
  simp

/-- A common probability kernel followed by any measurable observation contracts
chi-squared divergence; no separate integrability premise is needed at the output. -/
-- @node: chiSq_common_kernel_observation
lemma chiSq_common_kernel_observation {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ]
    (g : α × β → γ) (hg : Measurable g) (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2) ν) :
    (μ ⊗ₘ κ).map g ≪ (ν ⊗ₘ κ).map g ∧
      Integrable (fun y => ((((μ ⊗ₘ κ).map g).rnDeriv
        ((ν ⊗ₘ κ).map g) y).toReal - 1) ^ 2) ((ν ⊗ₘ κ).map g) ∧
      Causalean.Stat.chiSqDiv ((μ ⊗ₘ κ).map g) ((ν ⊗ₘ κ).map g) ≤
        Causalean.Stat.chiSqDiv μ ν := by
  obtain ⟨hjoint, hijoint, heq⟩ := chiSq_common_kernel_joint μ ν κ hac hint
  obtain ⟨hout, hiout, hle⟩ :=
    chiSq_observation_contraction (μ ⊗ₘ κ) (ν ⊗ₘ κ) g hg hjoint hijoint
  exact ⟨hout, hiout, hle.trans_eq heq⟩

/-- Integrable pairwise likelihood products guarantee integrability of the
uniform mixture's squared likelihood deviation. -/
-- @node: uniformMixture_likelihood_deviation_integrable
lemma uniformMixture_likelihood_deviation_integrable {α S : Type*}
    [MeasurableSpace α] [Fintype S] [Nonempty S]
    (Q : S → Measure α) (P : Measure α)
    [IsProbabilityMeasure P] [∀ s, IsProbabilityMeasure (Q s)]
    (hac : ∀ s, Q s ≪ P)
    (hpair : ∀ s t, Integrable
      (fun x => ((Q s).rnDeriv P x).toReal * ((Q t).rnDeriv P x).toReal) P) :
    Integrable (fun x =>
      (((Causalean.Stat.Minimax.Mixture.uniformMixture Q).rnDeriv P x).toReal - 1) ^ 2) P := by
  classical
  have := Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability Q
  let d (s : S) (x : α) : ℝ := ((Q s).rnDeriv P x).toReal
  let r (x : α) : ℝ :=
    ((Causalean.Stat.Minimax.Mixture.uniformMixture Q).rnDeriv P x).toReal
  have hsum : Integrable (fun x => ∑ s : S, ∑ t : S, d s x * d t x) P := by
    apply integrable_finsetSum Finset.univ
    intro s _
    apply integrable_finsetSum Finset.univ
    intro t _
    exact hpair s t
  have hsq : Integrable (fun x => r x ^ 2) P := by
    apply (hsum.div_const ((Fintype.card S : ℝ) ^ 2)).congr
    filter_upwards [Causalean.Stat.Minimax.Mixture.uniformMixture_rnDeriv Q P]
      with x hx
    change r x = (∑ s : S, d s x) / (Fintype.card S : ℝ) at hx
    rw [hx, div_pow]
    simp only [pow_two, Finset.sum_mul_sum]
  have hr : Integrable r P := Measure.integrable_toReal_rnDeriv
  have hpoly := (hsq.sub (hr.const_mul 2)).add (integrable_const 1)
  have heq : (fun x => (r x - 1) ^ 2) =
      (fun x => r x ^ 2 - 2 * r x + 1) := by
    funext x
    ring
  change Integrable (fun x => (r x - 1) ^ 2) P
  rw [heq]
  exact hpoly

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
