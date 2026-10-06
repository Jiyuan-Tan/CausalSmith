module
public import Causalean.Stat.Nonparametric.HistogramRegression.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.IdentDistribIndep

/-!
# Transferring histogram loss along an iid sample law

The integrated squared histogram loss is a measurable function of the training
tuple. Independent observations with a common law therefore have exactly the
same expected integrated loss as canonical product samples. This layer does
not require bounded responses or a conditional mean, and is independent of
the statistical risk inequality in `Risk`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

variable {Ω A κ : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Finite κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- [Measurable partition inputs, responses, and target](hyp:hlabel,hX,hY,hg)
give [measurable integrated squared histogram loss as a function of the
training tuple](goal) under a probability observation law. -/
theorem measurable_integrated_sq_loss {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (g : A → ℝ) (a : ℝ)
    (hlabel : Measurable label) (hX : Measurable X) (hY : Measurable Y)
    (hg : Measurable g) :
    Measurable (fun z : Fin m → Ω =>
      ∫ ω, (histogram label X Y a z (X ω) - g (X ω)) ^ 2 ∂μ) := by
  -- Compose measurable_histogram with (z,ω) ↦ (z,X ω), subtract g∘X,
  -- and square. For real-valued functions, joint measurability supplies
  -- StronglyMeasurable; StronglyMeasurable.integral_prod_right then gives
  -- the claim. Bochner totalization allows nonintegrable sections, so no
  -- boundedness or integrability premise is needed for this measurability.
  have hpred : Measurable (fun q : (Fin m → Ω) × Ω =>
      histogram label X Y a q.1 (X q.2)) :=
    (measurable_histogram label X Y a hlabel hX hY).comp
      (measurable_fst.prodMk (hX.comp measurable_snd))
  have hloss : Measurable (fun q : (Fin m → Ω) × Ω =>
      (histogram label X Y a q.1 (X q.2) - g (X q.2)) ^ 2) :=
    (hpred.sub (hg.comp (hX.comp measurable_snd))).pow_const 2
  exact hloss.stronglyMeasurable.integral_prod_right.measurable

/-- [Measurable iid observation maps with a common law](hyp:hZ,hind,hident)
and [measurable partition inputs, responses, and target](hyp:hlabel,hX,hY,hg)
give [equality of expected integrated squared histogram loss on the original
sample space and the canonical product sample space](goal). -/
theorem integral_histogram_loss_eq_risk_iid {m : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (Z : Fin m → S → Ω) (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (g : A → ℝ) (a : ℝ)
    (hZ : ∀ r, Measurable (Z r)) (hind : iIndepFun Z ν)
    (hident : ∀ r, IdentDistrib (Z r) id ν μ)
    (hlabel : Measurable label) (hX : Measurable X) (hY : Measurable Y)
    (hg : Measurable g) :
    (∫ s, (∫ ω, (histogram label X Y a (fun r => Z r s) (X ω) - g (X ω)) ^ 2 ∂μ) ∂ν) =
      risk μ (Measure.pi (fun _ : Fin m => μ)) label X Y a g := by
  -- Apply iIndepFun_iff_map_fun_eq_pi_map to the measurable tuple map,
  -- rewrite each marginal using (hident r).map_eq and Measure.map_id,
  -- and use integral_map with measurable_integrated_sq_loss. This includes
  -- m=0 and requires no standard-Borel structure on Ω or S.
  have hlaw : ν.map (fun s r => Z r s) = Measure.pi (fun _ : Fin m => μ) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun r => (hZ r).aemeasurable)).mp hind]
    congr 1
    funext r
    exact (hident r).map_eq.trans (Measure.map_id)
  have hloss := measurable_integrated_sq_loss (m := m) μ label X Y g a
    hlabel hX hY hg
  unfold risk
  rw [← hlaw]
  exact (integral_map (measurable_pi_lambda _ hZ).aemeasurable
    hloss.stronglyMeasurable.aestronglyMeasurable).symm

end

end Causalean.Stat.Nonparametric.HistogramRegression
