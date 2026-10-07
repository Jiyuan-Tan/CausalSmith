module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotLocalRiskSupport
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAttainmentSupport

/-! # Exact transcript-law identity for private-pilot local risk -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open MeasureTheory
open scoped BigOperators ENNReal

/-- At every proper finite pilot split for which the local alternative is interior, the transcript-law local risk is exactly the prefix average of the conditional selected-score variances, including the finite main-size factor. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hsub,hn,hlocal), [the pilot Estimator local Risk eq prefix Variance](goal).

Under the stated assumptions, the pilot Estimator local Risk eq prefix Variance. -/
lemma pilotEstimator_localRisk_eq_prefixVariance
    (θ h : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hsub : PilotSublinear m) (n : ℕ) (hn : 2 ≤ n)
    (hlocal : InteriorMeans (localAlternative θ h n)) :
    localRisk (pilotEstimator p ε m select hselect hp hε) θ h p n =
      ENNReal.ofReal
        ((n : ℝ) / (adaptiveMainSize m n : ℝ) *
          ∑ u : Fin (m n) → Fin 4,
            (∏ j : Fin (m n), ∑ a : Fin 4,
              piTheta (localAlternative θ h n) p a *
                rrPilotProbability ε a (u j)) *
            adaptiveScoreVariance select (localAlternative θ h n)
              (pilotAdaptivePrefixTheta p ε m
                (Nat.le_of_lt (hsub.2 n hn).2) u) p ε) := by
  classical
  let θn := localAlternative θ h n
  let P := pilotEstimator p ε m select hselect hp hε
  let μ := transcriptLaw P θn p n
  let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
  let e := fun uv : (Fin (m n) → Fin 4) × (Fin (n - m n) → Fin 14) =>
    pilotAdaptiveEncode hmn uv.1 uv.2
  have htrue : adaptiveTrueParam θ h n = θn :=
    adaptiveTrueParam_eq_localAlternative θ h n hlocal
  have hmain : adaptiveMainSize m n = n - m n := by
    simp [adaptiveMainSize, adaptivePilotSize_eq m hsub hn]
  have hrisk := adaptivePilotPrefix_rootN_meanSquare
    select θ h p ε m hselect hp hθ hε hsub n hn
  rw [htrue] at hrisk
  rw [hmain] at hrisk
  unfold localRisk
  rw [MeasureTheory.lintegral_fintype]
  change (∑ z : Transcript (pilotOutputFamily n),
    ENNReal.ofReal ((scaledError P θ h n z) ^ 2) * μ {z}) = _
  rw [sum_eq_sum_image_of_zero_off_range e
    (pilotAdaptiveEncode_pair_injective hmn)]
  · rw [Fintype.sum_prod_type]
    have hpilot_nonneg (u : Fin (m n) → Fin 4) :
        0 ≤ ∏ j : Fin (m n), ∑ a : Fin 4,
          piTheta θn p a * rrPilotProbability ε a (u j) := by
      apply Finset.prod_nonneg
      intro j _
      apply Finset.sum_nonneg
      intro a _
      exact mul_nonneg (piTheta_pos_interior θn p hp hlocal a).le (by
        unfold rrPilotProbability
        split_ifs <;> positivity)
    have hmain_nonneg (u : Fin (m n) → Fin 4)
        (v : Fin (n - m n) → Fin 14) :
        0 ≤ ∏ j : Fin (n - m n),
          adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
            p ε (v j) := by
      apply Finset.prod_nonneg
      intro j _
      exact adaptiveMainMass_nonneg select θn _ p ε hselect hp hlocal
        (pilotTheta_interior p ε m (pilotAdaptiveEncode hmn u (fun _ => 0)))
        hε (v j)
    have hatom (u : Fin (m n) → Fin 4)
        (v : Fin (n - m n) → Fin 14) :
        μ {e (u, v)} =
          ENNReal.ofReal ((∏ j : Fin (m n), ∑ a : Fin 4,
            piTheta θn p a * rrPilotProbability ε a (u j)) *
            ∏ j : Fin (n - m n),
              adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
                p ε (v j)) := by
      rw [pilotAdaptive_joint_singleton_eq_prefix_mul_mainProduct
        select θn p ε m hselect hp hlocal hε hmn u v]
      rw [← ENNReal.ofReal_mul (hpilot_nonneg u)]
    simp_rw [hatom]
    have herr (u : Fin (m n) → Fin 4)
        (v : Fin (n - m n) → Fin 14) :
        scaledError P θ h n (e (u, v)) =
          Real.sqrt (n : ℝ) *
            (contrast (pilotAdaptivePrefixTheta p ε m hmn u) +
              ((n - m n : ℕ) : ℝ)⁻¹ *
                (∑ j, adaptiveSelectedScore select
                  (pilotAdaptivePrefixTheta p ε m hmn u)
                  p ε (v j)) - contrast θn) := by
      unfold scaledError P
      change Real.sqrt (n : ℝ) *
        (tauStar p ε m (select) (e (u, v)) -
          contrast θn) = _
      rw [tauStar_pilotAdaptiveEncode select p ε m hp hε hmn u v]
    simp_rw [herr]
    simp_rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    have hofReal_sum {A : Type} [Fintype A] (f : A → ℝ)
        (hf : ∀ a, 0 ≤ f a) :
        (∑ a, ENNReal.ofReal (f a)) = ENNReal.ofReal (∑ a, f a) := by
      simpa using (ENNReal.ofReal_sum_of_nonneg
        (s := Finset.univ) (fun a _ => hf a)).symm
    calc
      (∑ u : Fin (m n) → Fin 4,
        ∑ v : Fin (n - m n) → Fin 14,
          ENNReal.ofReal
            ((Real.sqrt (n : ℝ) *
              (contrast (pilotAdaptivePrefixTheta p ε m hmn u) +
                ((n - m n : ℕ) : ℝ)⁻¹ *
                  (∑ j, adaptiveSelectedScore select
                    (pilotAdaptivePrefixTheta p ε m hmn u)
                    p ε (v j)) - contrast θn)) ^ 2 *
              ((∏ j : Fin (m n), ∑ a : Fin 4,
                piTheta θn p a * rrPilotProbability ε a (u j)) *
                ∏ j : Fin (n - m n),
                  adaptiveMainMass select θn
                    (pilotAdaptivePrefixTheta p ε m hmn u)
                    p ε (v j)))) =
          ∑ u : Fin (m n) → Fin 4, ENNReal.ofReal
            (∑ v : Fin (n - m n) → Fin 14,
              (Real.sqrt (n : ℝ) *
                (contrast (pilotAdaptivePrefixTheta p ε m hmn u) +
                  ((n - m n : ℕ) : ℝ)⁻¹ *
                    (∑ j, adaptiveSelectedScore select
                      (pilotAdaptivePrefixTheta p ε m hmn u)
                      p ε (v j)) - contrast θn)) ^ 2 *
                ((∏ j : Fin (m n), ∑ a : Fin 4,
                  piTheta θn p a * rrPilotProbability ε a (u j)) *
                  ∏ j : Fin (n - m n),
                    adaptiveMainMass select θn
                      (pilotAdaptivePrefixTheta p ε m hmn u)
                      p ε (v j))) := by
          apply Finset.sum_congr rfl
          intro u _
          refine hofReal_sum (A := Fin (n - m n) → Fin 14) _ ?_
          intro v
          exact mul_nonneg (sq_nonneg _)
            (mul_nonneg (hpilot_nonneg u) (hmain_nonneg u v))
      _ = ENNReal.ofReal
          (∑ u : Fin (m n) → Fin 4,
            ∑ v : Fin (n - m n) → Fin 14,
              (Real.sqrt (n : ℝ) *
                (contrast (pilotAdaptivePrefixTheta p ε m hmn u) +
                  ((n - m n : ℕ) : ℝ)⁻¹ *
                    (∑ j, adaptiveSelectedScore select
                      (pilotAdaptivePrefixTheta p ε m hmn u)
                      p ε (v j)) - contrast θn)) ^ 2 *
                ((∏ j : Fin (m n), ∑ a : Fin 4,
                  piTheta θn p a * rrPilotProbability ε a (u j)) *
                  ∏ j : Fin (n - m n),
                    adaptiveMainMass select θn
                      (pilotAdaptivePrefixTheta p ε m hmn u)
                      p ε (v j))) := by
          refine hofReal_sum (A := Fin (m n) → Fin 4) _ ?_
          intro u
          exact Finset.sum_nonneg fun v _ => mul_nonneg (sq_nonneg _)
            (mul_nonneg (hpilot_nonneg u) (hmain_nonneg u v))
      _ = _ := by
        congr 1
        calc
        (∑ u : Fin (m n) → Fin 4,
          ∑ v : Fin (n - m n) → Fin 14,
            (Real.sqrt (n : ℝ) *
              (contrast (pilotAdaptivePrefixTheta p ε m hmn u) +
                ((n - m n : ℕ) : ℝ)⁻¹ *
                  (∑ j, adaptiveSelectedScore select
                    (pilotAdaptivePrefixTheta p ε m hmn u)
                    p ε (v j)) - contrast θn)) ^ 2 *
              ((∏ j : Fin (m n), ∑ a : Fin 4,
                piTheta θn p a * rrPilotProbability ε a (u j)) *
                ∏ j : Fin (n - m n),
                  adaptiveMainMass select θn
                    (pilotAdaptivePrefixTheta p ε m hmn u)
                    p ε (v j))) =
            ∑ u : Fin (m n) → Fin 4,
              (∏ j : Fin (m n), ∑ a : Fin 4,
                piTheta θn p a * rrPilotProbability ε a (u j)) *
                ∑ v : Fin (n - m n) → Fin 14,
                  (∏ j, adaptiveMainMass select θn
                    (pilotAdaptivePrefixTheta p ε m hmn u)
                    p ε (v j)) *
                  (Real.sqrt (n : ℝ) *
                    (contrast (pilotAdaptivePrefixTheta p ε m hmn u) +
                      ((n - m n : ℕ) : ℝ)⁻¹ *
                        (∑ j, adaptiveSelectedScore select
                          (pilotAdaptivePrefixTheta p ε m hmn u)
                          p ε (v j)) - contrast θn)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro u _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro v _
            ring
        _ = ∑ u : Fin (m n) → Fin 4,
              (∏ j : Fin (m n), ∑ a : Fin 4,
                piTheta θn p a * rrPilotProbability ε a (u j)) *
              ((n : ℝ) / (n - m n : ℕ) *
                adaptiveScoreVariance select θn
                  (pilotAdaptivePrefixTheta p ε m hmn u) p ε) := by
            simpa only [hmn] using hrisk
        _ = (n : ℝ) / (adaptiveMainSize m n : ℝ) *
              ∑ u : Fin (m n) → Fin 4,
                (∏ j : Fin (m n), ∑ a : Fin 4,
                  piTheta (localAlternative θ h n) p a *
                    rrPilotProbability ε a (u j)) *
                adaptiveScoreVariance select (localAlternative θ h n)
                  (pilotAdaptivePrefixTheta p ε m
                    (Nat.le_of_lt (hsub.2 n hn).2) u) p ε := by
            rw [hmain]
            simp only [θn]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            ring
  · intro z hz
    have hzμ := pilotAdaptive_singleton_zero_of_not_range
      select θn p ε m hselect hp hε hmn z hz
    apply mul_eq_zero.mpr
    right
    simpa only [μ, P] using hzμ

/-- The exact risk identity applies to every direction in the finite-sample local index set; its membership condition supplies precisely the interiority needed by the transcript-law factorization. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hsub,hn,hh), [the pilot Estimator local Risk eq prefix Variance of mem local Index Set](goal).

Under the stated assumptions, the pilot Estimator local Risk eq prefix Variance of mem local Index Set. -/
lemma pilotEstimator_localRisk_eq_prefixVariance_of_mem_localIndexSet
    (θ h : TrialParameter) (p ε H : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hsub : PilotSublinear m) (n : ℕ) (hn : 2 ≤ n)
    (hh : h ∈ localIndexSet θ n H) :
    localRisk (pilotEstimator p ε m select hselect hp hε) θ h p n =
      ENNReal.ofReal
        ((n : ℝ) / (adaptiveMainSize m n : ℝ) *
          ∑ u : Fin (m n) → Fin 4,
            (∏ j : Fin (m n), ∑ a : Fin 4,
              piTheta (localAlternative θ h n) p a *
                rrPilotProbability ε a (u j)) *
            adaptiveScoreVariance select (localAlternative θ h n)
              (pilotAdaptivePrefixTheta p ε m
                (Nat.le_of_lt (hsub.2 n hn).2) u) p ε) := by
  exact pilotEstimator_localRisk_eq_prefixVariance
    select θ h p ε m hselect hp hθ hε hsub n hn hh.2

end CausalSmith.Stat.LdpAteEfficiencySurface
