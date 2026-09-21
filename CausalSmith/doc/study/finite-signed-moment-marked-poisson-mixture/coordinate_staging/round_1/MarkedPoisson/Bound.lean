import Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.MarkedPoisson.Palm

/-!
# Geometric marked-Poisson mixture bounds

This module combines the Palm comparison and aggregate moment-matching estimate into the reusable one-coordinate geometric TV bound.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

namespace NormalizedFiniteSignedMomentCertificate

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the overlap fraction](hyp:ε), [the support ratio](hyp:κ), [the positive shift](hyp:a), [the support upper bound](hyp:B), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [positive overlap fraction](hyp:hε), [the overlap upper bound](hyp:hεhalf), [the support-ratio identity](hyp:hκ), [positive shift](hyp:ha), [positive upper bound](hyp:hB), [nonnegative labeled intensity](hyp:hu), [nonnegative auxiliary intensity](hyp:hv), [positive total intensity](hyp:ht), [the compact-support condition](hyp:hsupp).  The marked-law discrepancy is at most the labeled Palm intensity
`u * ε * a` times the discrepancy between aggregate treated/control mixtures
of the two Jordan priors.  The result includes `u = 0` and `v = 0`; only the
total intensity must be positive. -/
theorem tvDist_markedPoissonPredictive_le_palm_aggregate
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε κ a B u v : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hκ : κ = (1 - 2 * ε) / ε)
    (ha : 0 < a) (hB : 0 < B)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 < u + v)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    Causalean.Stat.tvDist
        (C.markedPoissonPredictive ε a u v false)
        (C.markedPoissonPredictive ε a u v true) ≤
      u * ε * a *
        Causalean.Stat.tvDist
          (aggregatePoissonPredictive C.positivePrior ε a (u + v))
          (aggregatePoissonPredictive C.negativePrior ε a (u + v)) := by
  have hκpos : 0 < κ := by
    rw [hκ]
    apply div_pos
    · nlinarith
    · exact hε
  let q : unitInterval :=
    ⟨u / (u + v), by
      constructor
      · positivity
      · rw [div_le_one ht]
        linarith⟩
  let P := aggregatePoissonPredictive C.positivePrior ε a (u + v)
  let N := aggregatePoissonPredictive C.negativePrior ε a (u + v)
  let Kf := palmSplitKernel q true
  let Ks := palmSplitKernel q false
  let Mf := C.markedPoissonPredictive ε a u v false
  let Mt := C.markedPoissonPredictive ε a u v true
  let d : ℝ≥0∞ := ENNReal.ofReal (u * ε * a / 2)
  let _ : IsProbabilityMeasure P :=
    Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_isProbability
      C.positivePrior (aggregatePoissonKernel ε a (u + v))
      (fun p => by rw [aggregatePoissonKernel_apply]; infer_instance)
  let _ : IsProbabilityMeasure N :=
    Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_isProbability
      C.negativePrior (aggregatePoissonKernel ε a (u + v))
      (fun p => by rw [aggregatePoissonKernel_apply]; infer_instance)
  let _ : IsProbabilityMeasure Mf :=
    C.markedPoissonPredictive_isProbabilityMeasure
      ε a u v κ B false ha hκpos hsupp
  let _ : IsProbabilityMeasure Mt :=
    C.markedPoissonPredictive_isProbabilityMeasure
      ε a u v κ B true ha hκpos hsupp
  have hc : 0 ≤ u * ε * a := by positivity
  have hd : d.toReal = u * ε * a / 2 := by
    change (ENNReal.ofReal (u * ε * a / 2)).toReal = _
    rw [ENNReal.toReal_ofReal]
    positivity
  let _ : IsFiniteMeasure (d • ((Kf ∘ₘ P) + (Ks ∘ₘ N))) :=
    Measure.smul_finite _ (by simp [d])
  let _ : IsFiniteMeasure (d • ((Kf ∘ₘ N) + (Ks ∘ₘ P))) :=
    Measure.smul_finite _ (by simp [d])
  let _ : IsFiniteMeasure
      (Mf + d • ((Kf ∘ₘ P) + (Ks ∘ₘ N))) := by infer_instance
  let _ : IsFiniteMeasure
      (Mt + d • ((Kf ∘ₘ N) + (Ks ∘ₘ P))) := by infer_instance
  have hbalance :
      Mf + d • ((Kf ∘ₘ P) + (Ks ∘ₘ N)) =
        Mt + d • ((Kf ∘ₘ N) + (Ks ∘ₘ P)) := by
    apply Measure.ext_of_measureReal_singleton
    rintro ⟨⟨x, y⟩, ⟨s, t⟩⟩
    rw [measureReal_add_ennreal_smul_add Mf (Kf ∘ₘ P) (Ks ∘ₘ N)
        d (by simp [d]),
      measureReal_add_ennreal_smul_add Mt (Kf ∘ₘ N) (Ks ∘ₘ P)
        d (by simp [d])]
    rcases x with _ | k
    · rcases y with _ | l
      · have hm : Mf.real {((0, 0), (s, t))} =
            Mt.real {((0, 0), (s, t))} := by
          have hr := congrArg (fun μ : Measure MarkedPoissonObservation =>
              μ.real {((0, 0), (s, t))})
            (C.restrict_markedPoissonPredictive_noLabeledTreated_eq
              ε a u v κ B ha hκpos hsupp)
          simpa [Mf, Mt, Measure.restrict_apply,
            noLabeledTreated] using hr
        have hp := palmSplit_bind_no_labeled_eq q P s t
        have hn := palmSplit_bind_no_labeled_eq q N s t
        change Mf.real {((0, 0), (s, t))} +
            d.toReal * ((Kf ∘ₘ P).real {((0, 0), (s, t))} +
              (Ks ∘ₘ N).real {((0, 0), (s, t))}) =
          Mt.real {((0, 0), (s, t))} +
            d.toReal * ((Kf ∘ₘ N).real {((0, 0), (s, t))} +
              (Ks ∘ₘ P).real {((0, 0), (s, t))})
        change (palmSplitKernel q false ∘ₘ P).real {((0, 0), (s, t))} =
            (palmSplitKernel q true ∘ₘ P).real {((0, 0), (s, t))} at hp
        change (palmSplitKernel q false ∘ₘ N).real {((0, 0), (s, t))} =
            (palmSplitKernel q true ∘ₘ N).real {((0, 0), (s, t))} at hn
        rw [hm, ← hp, ← hn]
        ring
      · have hm := markedPredictive_real_target_sub C ε κ a B u v
            hε hεhalf hκ ha hu hv ht hsupp false l s t
        have hPf := palmSplit_bind_wrong_target q false P l s t
        have hNf := palmSplit_bind_wrong_target q false N l s t
        change Mf.real {palmSplitTarget false l s t} +
            d.toReal * ((Kf ∘ₘ P).real {palmSplitTarget false l s t} +
              (Ks ∘ₘ N).real {palmSplitTarget false l s t}) =
          Mt.real {palmSplitTarget false l s t} +
            d.toReal * ((Kf ∘ₘ N).real {palmSplitTarget false l s t} +
              (Ks ∘ₘ P).real {palmSplitTarget false l s t})
        change Mf.real {palmSplitTarget false l s t} -
            Mt.real {palmSplitTarget false l s t} = _ at hm
        have hm' : Mf.real {palmSplitTarget false l s t} -
              Mt.real {palmSplitTarget false l s t} =
            (u * ε * a / 2) *
              ((Ks ∘ₘ P).real {palmSplitTarget false l s t} -
                (Ks ∘ₘ N).real {palmSplitTarget false l s t}) := by
          simpa [q, P, N, Ks, Mf, Mt] using hm
        change (Kf ∘ₘ P).real {palmSplitTarget false l s t} = 0 at hPf
        change (Kf ∘ₘ N).real {palmSplitTarget false l s t} = 0 at hNf
        rw [hPf, hNf, hd]
        nlinarith [hm']
    · rcases y with _ | l
      · have hm := markedPredictive_real_target_sub C ε κ a B u v
            hε hεhalf hκ ha hu hv ht hsupp true k s t
        have hPs := palmSplit_bind_wrong_target q true P k s t
        have hNs := palmSplit_bind_wrong_target q true N k s t
        change Mf.real {palmSplitTarget true k s t} +
            d.toReal * ((Kf ∘ₘ P).real {palmSplitTarget true k s t} +
              (Ks ∘ₘ N).real {palmSplitTarget true k s t}) =
          Mt.real {palmSplitTarget true k s t} +
            d.toReal * ((Kf ∘ₘ N).real {palmSplitTarget true k s t} +
              (Ks ∘ₘ P).real {palmSplitTarget true k s t})
        change Mf.real {palmSplitTarget true k s t} -
            Mt.real {palmSplitTarget true k s t} = _ at hm
        have hm' : Mf.real {palmSplitTarget true k s t} -
              Mt.real {palmSplitTarget true k s t} =
            -(u * ε * a / 2) *
              ((Kf ∘ₘ P).real {palmSplitTarget true k s t} -
                (Kf ∘ₘ N).real {palmSplitTarget true k s t}) := by
          simpa [q, P, N, Kf, Mf, Mt] using hm
        change (Ks ∘ₘ P).real {palmSplitTarget true k s t} = 0 at hPs
        change (Ks ∘ₘ N).real {palmSplitTarget true k s t} = 0 at hNs
        rw [hPs, hNs, hd]
        nlinarith [hm']
      · have hm := markedPredictive_real_both_positive_sub_eq_zero
            C ε a u v κ B ha hκpos hsupp k l s t
        have hPf := palmSplit_bind_both_positive q true P k l s t
        have hNf := palmSplit_bind_both_positive q true N k l s t
        have hPs := palmSplit_bind_both_positive q false P k l s t
        have hNs := palmSplit_bind_both_positive q false N k l s t
        change Mf.real {((k + 1, l + 1), (s, t))} +
            d.toReal * ((Kf ∘ₘ P).real {((k + 1, l + 1), (s, t))} +
              (Ks ∘ₘ N).real {((k + 1, l + 1), (s, t))}) =
          Mt.real {((k + 1, l + 1), (s, t))} +
            d.toReal * ((Kf ∘ₘ N).real {((k + 1, l + 1), (s, t))} +
              (Ks ∘ₘ P).real {((k + 1, l + 1), (s, t))})
        change Mf.real {((k + 1, l + 1), (s, t))} -
            Mt.real {((k + 1, l + 1), (s, t))} = 0 at hm
        change (Kf ∘ₘ P).real {((k + 1, l + 1), (s, t))} = 0 at hPf
        change (Kf ∘ₘ N).real {((k + 1, l + 1), (s, t))} = 0 at hNf
        change (Ks ∘ₘ P).real {((k + 1, l + 1), (s, t))} = 0 at hPs
        change (Ks ∘ₘ N).real {((k + 1, l + 1), (s, t))} = 0 at hNs
        rw [hPf, hNf, hPs, hNs]
        linarith
  change Causalean.Stat.tvDist Mf Mt ≤
    u * ε * a * Causalean.Stat.tvDist P N
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  have hb := congrArg (fun μ : Measure MarkedPoissonObservation => μ.real A) hbalance
  rw [measureReal_add_ennreal_smul_add Mf (Kf ∘ₘ P) (Ks ∘ₘ N)
      d (by simp [d]),
    measureReal_add_ennreal_smul_add Mt (Kf ∘ₘ N) (Ks ∘ₘ P)
      d (by simp [d])] at hb
  have hf : |(Kf ∘ₘ P).real A - (Kf ∘ₘ N).real A| ≤
      Causalean.Stat.tvDist P N :=
    (Causalean.Stat.abs_measureReal_sub_le_tvDist hA).trans
      (tvDist_bind_le P N Kf)
  have hs : |(Ks ∘ₘ P).real A - (Ks ∘ₘ N).real A| ≤
      Causalean.Stat.tvDist P N :=
    (Causalean.Stat.abs_measureReal_sub_le_tvDist hA).trans
      (tvDist_bind_le P N Ks)
  have hdnonneg : 0 ≤ d.toReal := ENNReal.toReal_nonneg
  rw [hd] at hb hdnonneg
  calc
    |Mf.real A - Mt.real A| =
        (u * ε * a / 2) *
          |((Ks ∘ₘ P).real A - (Ks ∘ₘ N).real A) -
            ((Kf ∘ₘ P).real A - (Kf ∘ₘ N).real A)| := by
      rw [← abs_of_nonneg (by positivity : 0 ≤ u * ε * a / 2), ← abs_mul]
      congr 1
      linarith
    _ ≤ (u * ε * a / 2) *
          (|(Ks ∘ₘ P).real A - (Ks ∘ₘ N).real A| +
            |(Kf ∘ₘ P).real A - (Kf ∘ₘ N).real A|) := by
      gcongr
      exact abs_sub _ _
    _ ≤ u * ε * a * Causalean.Stat.tvDist P N := by
      nlinarith

/-- The [stated conclusion](goal) follows from [the overlap fraction](hyp:ε), [the support ratio](hyp:κ), [positive overlap fraction](hyp:hε), [the overlap upper bound](hyp:hεhalf), [the support-ratio identity](hyp:hκ), [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the positive shift](hyp:a), [the support upper bound](hyp:B), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v).  For fixed overlap and support-ratio parameters there are positive
constants `b,C₀` and a geometric factor `ρ < 1` such that moment matching
through `L` bounds one-coordinate marked-Poisson TV by
`C₀ * u * a * ρ^L` whenever `(u+v)B ≤ bL`.  The statement includes the edge
cases `u = 0` and `v = 0` as long as total intensity is positive. -/
theorem exists_geometric_markedPoisson_tv_bound
    (ε κ : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hκ : κ = (1 - 2 * ε) / ε) :
    ∃ b C₀ ρ : ℝ, 0 < b ∧ 0 < C₀ ∧ ρ ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ {ι : Type*} [Fintype ι] {L : ℕ}
        (C : NormalizedFiniteSignedMomentCertificate ι L)
        (a B u v : ℝ),
        0 < a → 0 < B → 0 ≤ u → 0 ≤ v → 0 < u + v →
        (∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) →
        (u + v) * B ≤ b * L →
        Causalean.Stat.tvDist
            (C.markedPoissonPredictive ε a u v false)
            (C.markedPoissonPredictive ε a u v true) ≤
          C₀ * u * a * ρ ^ L := by
  rcases exists_geometric_aggregatePoisson_jordan_tv_bound ε κ hε hεhalf hκ with
    ⟨b, D, ρ, hb, hD, hρ, hagg⟩
  refine ⟨b, ε * D, ρ, hb, mul_pos hε hD, hρ, ?_⟩
  intro ι _ L C a B u v ha hB hu hv ht hsupp hband
  calc
    Causalean.Stat.tvDist
        (C.markedPoissonPredictive ε a u v false)
        (C.markedPoissonPredictive ε a u v true) ≤
        u * ε * a * Causalean.Stat.tvDist
          (aggregatePoissonPredictive C.positivePrior ε a (u + v))
          (aggregatePoissonPredictive C.negativePrior ε a (u + v)) :=
      C.tvDist_markedPoissonPredictive_le_palm_aggregate
        ε κ a B u v hε hεhalf hκ ha hB hu hv ht hsupp
    _ ≤ u * ε * a * (D * ρ ^ L) := by
      gcongr
      exact hagg C a B (u + v) ha hB ht hsupp hband
    _ = (ε * D) * u * a * ρ ^ L := by ring


end NormalizedFiniteSignedMomentCertificate

end Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
