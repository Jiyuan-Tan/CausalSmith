module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.BoundedRegularity

/-!
# Dominated convergence for integrable finite-jump payoffs

These analytic bridges allow an integrable, possibly unbounded envelope in
place of a uniform constant. They import no compensation theorem. The energy
bridge explicitly requires absolute time-sample integrability, so its use of
Fubini and dominated convergence cannot rely on a totalized Bochner integral.
-/

public section

open MeasureTheory Filter Set

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Pointwise convergent predictable payoffs dominated by an integrable
absolute event payoff have convergent expected finite jump sums. -/
theorem Model.tendsto_expected_jumpIntegral_of_dominated (M : Model Ω μ)
    [IsProbabilityMeasure μ] (G : ℕ → ℝ → Ω → ℝ) (H : ℝ → Ω → ℝ)
    (hG : ∀ k, M.Predictable (G k))
    (hdom : ∀ k t ω, |G k t ω| ≤ |H t ω|)
    (hjumpAbs : Integrable
      (M.jumpIntegral (fun t ω => |H t ω|) M.horizon) μ)
    (hlim : ∀ t ω, Tendsto (fun k => G k t ω) atTop (nhds (H t ω))) :
    Tendsto (fun k => ∫ ω, M.jumpIntegral (G k) M.horizon ω ∂μ)
      atTop (nhds (∫ ω, M.jumpIntegral H M.horizon ω ∂μ)) := by
  /- Use `tendsto_integral_of_dominated_convergence` with envelope
     `jumpIntegral |H|`. Finset.abs_sum_le_sum_abs and Finset.sum_le_sum
     give domination; `tendsto_finsetSum` gives convergence on each path.
     Measurability is supplied by the closed enumeration module. This is
     purely analytic and must not import Compensator or Regularity. -/
  classical
  apply tendsto_integral_of_dominated_convergence
    (M.jumpIntegral (fun t ω => |H t ω|) M.horizon)
  · intro k
    exact (M.measurable_jumpIntegral (G k)
      (M.predictable_joint_measurable (G k) (hG k))).aestronglyMeasurable
  · exact hjumpAbs
  · intro k
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, Model.jumpIntegral, Model.jumpIntegral]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun t _ => hdom k t ω))
  · apply Eventually.of_forall
    intro ω
    unfold Model.jumpIntegral
    exact tendsto_finsetSum _ (fun t _ => hlim t ω)

/-- Pointwise convergent predictable payoffs dominated by an absolutely
integrable time-sample intensity payoff have convergent expected compensator
integrals. [The model and payoffs](hyp:M,G,H), [their predictability](hyp:hG,hH),
[domination](hyp:hdom), [integrability of the dominating intensity payoff](hyp:hproduct),
and [pointwise convergence](hyp:hlim) give [convergence of expected compensator
integrals](goal). -/
theorem Model.tendsto_expected_energyIntegral_of_dominated (M : Model Ω μ)
    [IsProbabilityMeasure μ] (G : ℕ → ℝ → Ω → ℝ) (H : ℝ → Ω → ℝ)
    (hG : ∀ k, M.Predictable (G k)) (hH : M.Predictable H)
    (hdom : ∀ k t ω, |G k t ω| ≤ |H t ω|)
    (hproduct : Integrable (fun p : ℝ × Ω =>
      |H p.1 p.2| * (M.atRisk p.1 p.2 * M.intensity p.1 p.2))
      ((volume.restrict (Ioc 0 M.horizon)).prod μ))
    (hlim : ∀ t ω, Tendsto (fun k => G k t ω) atTop (nhds (H t ω))) :
    Tendsto (fun k => ∫ ω, M.energyIntegral (G k) M.horizon ω ∂μ)
      atTop (nhds (∫ ω, M.energyIntegral H M.horizon ω ∂μ)) := by
  /- Apply DCT once on the time-sample product, then rewrite each product
     integral as the sample expectation of the time integral using
     `integral_prod_symm`. Nonnegative rates convert norm domination into
     `hdom`. Use `Integrable.mono'` to derive product integrability of each
     approximant and of H from hproduct and joint measurability. Alternatively
     `integrable_prod_iff'` supplies a.e. integrable time sections and the
     integrable absolute energy envelope for two successive applications of
     DCT. Do not infer section integrability solely from integrability of a
     totalized pathwise Bochner integral. -/
  let ν := volume.restrict (Ioc 0 M.horizon)
  let rate : ℝ × Ω → ℝ := fun p => M.atRisk p.1 p.2 * M.intensity p.1 p.2
  have hrmeas : Measurable rate :=
    M.atRisk_joint_measurable.mul M.intensity_joint_measurable
  have hrnonneg (p : ℝ × Ω) : 0 ≤ rate p :=
    mul_nonneg (M.atRisk_nonneg p.1 p.2) (M.intensity_nonneg p.1 p.2)
  have hmeas (k : ℕ) : Measurable (fun p : ℝ × Ω => G k p.1 p.2 * rate p) :=
    (M.predictable_joint_measurable (G k) (hG k)).mul hrmeas
  have hbound (k : ℕ) (p : ℝ × Ω) :
      ‖G k p.1 p.2 * rate p‖ ≤ |H p.1 p.2| * rate p := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hrnonneg p)]
    exact mul_le_mul_of_nonneg_right (hdom k p.1 p.2) (hrnonneg p)
  have hGi (k : ℕ) : Integrable (fun p : ℝ × Ω => G k p.1 p.2 * rate p)
      (ν.prod μ) :=
    hproduct.mono' (hmeas k).aestronglyMeasurable
      (Eventually.of_forall (hbound k))
  have hHi : Integrable (fun p : ℝ × Ω => H p.1 p.2 * rate p) (ν.prod μ) := by
    apply hproduct.mono'
      ((M.predictable_joint_measurable H hH).mul hrmeas).aestronglyMeasurable
    apply Eventually.of_forall
    intro p
    change ‖H p.1 p.2 * rate p‖ ≤ |H p.1 p.2| * rate p
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hrnonneg p)]
  have hconv : Tendsto
      (fun k => ∫ p, G k p.1 p.2 * rate p ∂(ν.prod μ)) atTop
      (nhds (∫ p, H p.1 p.2 * rate p ∂(ν.prod μ))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun p => |H p.1 p.2| * rate p)
    · exact fun k => (hmeas k).aestronglyMeasurable
    · exact hproduct
    · exact fun k => Eventually.of_forall (hbound k)
    · exact Eventually.of_forall
        (fun p => (hlim p.1 p.2).mul tendsto_const_nhds)
  have hGeq (k : ℕ) :
      (∫ p, G k p.1 p.2 * rate p ∂(ν.prod μ)) =
        ∫ ω, M.energyIntegral (G k) M.horizon ω ∂μ :=
    integral_prod_symm _ (hGi k)
  have hHeq : (∫ p, H p.1 p.2 * rate p ∂(ν.prod μ)) =
      ∫ ω, M.energyIntegral H M.horizon ω ∂μ :=
    integral_prod_symm _ hHi
  simpa only [hGeq, hHeq] using hconv

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
