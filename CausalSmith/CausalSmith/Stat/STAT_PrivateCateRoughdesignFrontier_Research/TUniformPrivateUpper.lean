module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ReleaseMoments
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.TunedRisk
/-! Assembly of the uniform private scalar-risk, coverage and length guarantees. -/
public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign
/-- [The constructed kernels are Markov and pure private on every input. Their second moments,
coverage and interval lengths obey the public envelopes throughout the complete model, and public
tuning attains the stated scalar-risk and interval-length constants.](goal)
The [public parameters and their domains](hyp:n,k,epsilon,h,hn,hk,he,hh) and
[published substrate gates](hyp:efronStein_of_gate) specify the conditional scope. -/
-- @node: thm:uniform-private-upper
theorem uniform_private_upper (efronStein_of_gate : EfronSteinReplacement)
    (n k : ℕ) (epsilon h : ℝ)
    (hn : 2 ≤ n) -- @realizes n(sample size at least two)
    (hk : 2 ≤ k) -- @realizes k(cell count at least two)
    (he : 0 < epsilon ∧ epsilon ≤ 1) -- @realizes epsilon(budget in (0,1])
    (hh : 0 < h ∧ h ≤ 1 / 4) : -- @realizes h(radius in (0,1/4])
    IsMarkovKernel (privateRatioRelease n epsilon h k) ∧
    PrivateKernel n epsilon (privateRatioRelease n epsilon h k) ∧
    IsMarkovKernel (Thk n epsilon h k) ∧ PrivateKernel n epsilon (Thk n epsilon h k) ∧
    IsMarkovKernel (Ihk n epsilon h k) ∧ PrivateKernel n epsilon (Ihk n epsilon h k) ∧
    (∀ P : CausalLaw, CompleteModel P →
      (∫⁻ u, ENNReal.ofReal ((u-theta P)^2) ∂(Thk n epsilon h k ∘ₘ dataLaw n P)) ≤
        ENNReal.ofReal (Vbound n epsilon h k) ∧
      9/10 ≤ coverage n (Ihk n epsilon h k) P ∧
      expectedLength n (Ihk n epsilon h k) P ≤
        ENNReal.ofReal (min 2 (2*Real.sqrt (10*Vbound n epsilon h k)))) ∧
    IsMarkovKernel (publicTunedRelease n epsilon) ∧
    PrivateKernel n epsilon (publicTunedRelease n epsilon) ∧
    IsMarkovKernel (publicTunedInterval n epsilon) ∧
    PrivateKernel n epsilon (publicTunedInterval n epsilon) ∧
    worstRisk n (publicTunedRelease n epsilon) ≤ ENNReal.ofReal (2^18*rate n epsilon) ∧
    worstLength n (publicTunedInterval n epsilon) ≤ ENNReal.ofReal (2^22*rate n epsilon) ∧
    (∀ P, CompleteModel P → 9/10 ≤ coverage n (publicTunedInterval n epsilon) P) := by
  have hpair := privateRatioRelease_private n k epsilon h he.1 hh.1 (by omega)
  have hscalar := Thk_private n k epsilon h he.1 hh.1 (by omega)
  have hinterval := Ihk_private n k epsilon h he.1 hh.1 (by omega)
  refine ⟨hpair.markov, hpair, hscalar.markov, hscalar, hinterval.markov, hinterval, ?_⟩
  have htuned := publicTunedRelease_private n epsilon hn he
  have htunedInterval := publicTunedInterval_private n epsilon hn he
  suffices hstats :
      ∀ (k' : ℕ) (h' : ℝ), 2 ≤ k' → (0 < h' ∧ h' ≤ 1/4) →
        ∀ P : CausalLaw, CompleteModel P →
          (∫⁻ u, ENNReal.ofReal ((u-theta P)^2) ∂(Thk n epsilon h' k' ∘ₘ dataLaw n P)) ≤
            ENNReal.ofReal (Vbound n epsilon h' k') by
    refine ⟨?_, htuned.markov, htuned, htunedInterval.markov, htunedInterval,
      publicTunedRelease_worstRisk_of_squared_error_le n epsilon hn he hstats,
      publicTunedInterval_worstLength_le n epsilon hn he, ?_⟩
    · intro P hP
      have hmse := hstats k h hk hh P hP
      exact ⟨hmse, Ihk_coverage_of_squared_error_le n k epsilon h
        (by omega) (by omega) he.1 hh.1 P hP hmse,
        Ihk_expectedLength_le n k epsilon h he.1 P⟩
    · intro P hP
      apply publicTunedInterval_coverage_of_squared_error_le n epsilon hn he P hP
      intro hr
      have hp := public_tuning_parameters n epsilon hn he hr
      exact hstats _ _ hp.2.2.1 ⟨hp.1, hp.2.1⟩ P hP
  intro k' h' hk' hh' P hP
  exact Thk_model_squared_error_le efronStein_of_gate n k' epsilon h' hn hk' he.1 hh' P hP

end CausalSmith.Stat.PrivateCateRoughdesign
