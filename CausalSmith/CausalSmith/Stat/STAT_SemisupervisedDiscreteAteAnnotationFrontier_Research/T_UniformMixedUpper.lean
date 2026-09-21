module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.PoissonHybridRisk
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.FixedSampleHybridTransfer
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.Risk

/-! Uniform risk bound for the mixed-information hybrid. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

-- @node: thm:uniform-mixed-upper
/-- One overlap-dependent constant bounds the hybrid's worst-case MSE by the
annotation-frontier rate for all `n,m,d`.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
theorem uniform_mixed_upper {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∃ C : Real, 0 < C ∧ ∀ (n m d : Nat), 1 ≤ n → 2 ≤ d →
      (⨆ P : ClassLaw d eps,
        twoSampleMSE (annotationLaw P.1 n m) (mixedEstimator n m d eps)
          (ateFunctional P.1)) ≤
          C * frontierRate n m d := by
  obtain ⟨C₁, hC₁, htransfer⟩ := fixed_sample_hybrid_transfer
  obtain ⟨C₂, hC₂, hpoisson⟩ := poisson_hybrid_risk heps heps2
  refine ⟨2 * C₂ + C₁, by positivity, ?_⟩
  intro n m d hn hd
  apply Real.iSup_le
  · intro P
    have hfixed := (htransfer eps heps heps2 n m d hn hd P.1 P.2).2
    have hpois := hpoisson n m d P.1 hn hd P.2
    have hinv := inv_n_le_frontierRate n m d hn
    calc
      twoSampleMSE (annotationLaw P.1 n m) (mixedEstimator n m d eps)
          (ateFunctional P.1)
          ≤ 2 * poissonHybridMSE P.1 n m eps + C₁ / n := hfixed
      _ ≤ 2 * (C₂ * frontierRate n m d) + C₁ * frontierRate n m d := by
        rw [div_eq_mul_inv]
        gcongr
        simpa [one_div] using hinv
      _ = (2 * C₂ + C₁) * frontierRate n m d := by ring
  · have hr := (frontierRate_mem_Ioc_zero_one n m d hn).1
    positivity

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
