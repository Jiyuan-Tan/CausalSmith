module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotVarianceConsistency

/-! # Transcript-law wrapper for pilot variance consistency -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

/-- Empirical variance is invariant under transport along an equality of finite
row lengths. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:h,q), these specify the stated inputs. -/
-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
lemma finite_empiricalVariance_cast_eq {N K : ℕ} (h : N = K)
    (q : Fin K → ℝ) :
    (N : ℝ)⁻¹ * ∑ i : Fin N, (q (Fin.cast h i)) ^ 2 -
        ((N : ℝ)⁻¹ * ∑ i : Fin N, q (Fin.cast h i)) ^ 2 =
      (K : ℝ)⁻¹ * ∑ j : Fin K, (q j) ^ 2 -
        ((K : ℝ)⁻¹ * ∑ j : Fin K, q j) ^ 2 := by
  subst K
  rfl

/-- Average squared deviations are invariant under transport along an equality
of finite row lengths. For [the displayed inputs and conditions](hyp:h), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:q), these specify the stated inputs. -/
lemma finite_average_sq_deviation_cast_eq {N K : ℕ} (h : N = K)
    (q : Fin K → ℝ) :
    let qbarN := (N : ℝ)⁻¹ * ∑ i : Fin N, q (Fin.cast h i)
    let qbarK := (K : ℝ)⁻¹ * ∑ j : Fin K, q j
    (N : ℝ)⁻¹ * ∑ i : Fin N, (q (Fin.cast h i) - qbarN) ^ 2 =
      (K : ℝ)⁻¹ * ∑ j : Fin K, (q j - qbarK) ^ 2 := by
  subst K
  rfl

/-- On an encoded row, `VhatStar` equals the adaptive empirical variance after the canonical main-size reindexing. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hmn,hN,hmain), [the Vhat Star pilot Adaptive Encode eq adaptive Empirical Variance](goal).

Under the stated assumptions, the Vhat Star pilot Adaptive Encode eq adaptive Empirical Variance. -/
lemma VhatStar_pilotAdaptiveEncode_eq_adaptiveEmpiricalVariance
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) {n : ℕ}
    (hmn : m n ≤ n) (hN : 0 < adaptiveMainSize m n)
    (hmain : adaptiveMainSize m n = n - m n)
    (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
    VhatStar p ε m (select)
        (pilotAdaptiveEncode hmn u v) =
      adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
        (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
        p ε m hselect hp hε n (fun i => v (Fin.cast hmain i)) := by
  rw [VhatStar_pilotAdaptiveEncode select p ε m hselect hp hε hmn u v]
  rw [adaptivePilotRowEmpiricalVariance_eq_selected
    select θ (fun _ => 0) (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
    p ε m hselect hp hε n hN]
  exact (finite_average_sq_deviation_cast_eq hmain
    (fun j => adaptiveSelectedScore select (pilotAdaptivePrefixTheta p ε m hmn u)
      p ε (v j))).symm

/-- The actual bad-variance transcript event is exactly the real prefix mixture proved consistent in `PilotVarianceConsistency`. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hsub,hn), [the transcript Law Vhat Star bad eq of Real pilot Variance Bad Mass](goal).

Under the stated assumptions, the transcript Law Vhat Star bad eq of Real pilot Variance Bad Mass. -/
lemma transcriptLaw_VhatStar_bad_eq_ofReal_pilotVarianceBadMass
    (θ : TrialParameter) (p ε δ : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hsub : PilotSublinear m) {n : ℕ} (hn : 2 ≤ n) :
    (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        {z | δ < |VhatStar p ε m (select) z -
          Vstar θ p ε|} =
      ENNReal.ofReal (pilotVarianceBadMass select θ p ε δ m hselect hp hε
        (Nat.le_of_lt (hsub.2 n hn).2)) := by
  classical
  let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
  let μ := transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n
  let A : Set (Transcript (pilotOutputFamily n)) :=
    {z | δ < |VhatStar p ε m (select) z - Vstar θ p ε|}
  let e := fun uv : (Fin (m n) → Fin 4) × (Fin (n - m n) → Fin 14) =>
    pilotAdaptiveEncode hmn uv.1 uv.2
  have hN : 0 < adaptiveMainSize m n := by
    rw [adaptiveMainSize, adaptivePilotSize_eq m hsub hn]
    exact Nat.sub_pos_of_lt (hsub.2 n hn).2
  have hmain : adaptiveMainSize m n = n - m n := by
    simp [adaptiveMainSize, adaptivePilotSize_eq m hsub hn]
  have hzero : adaptiveTrueParam θ (fun _ => 0) n = θ := by
    have hlocal : localAlternative θ (fun _ => 0) n = θ := by
      funext k
      simp [localAlternative]
    rw [adaptiveTrueParam_eq_localAlternative]
    · exact hlocal
    · simpa only [hlocal] using hθ
  have hw (u : Fin (m n) → Fin 4) : 0 ≤ pilotPrefixWeight θ p ε m n u :=
    pilotPrefixWeight_nonneg θ p ε m n hp hθ u
  have hm (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
      0 ≤ ∏ j, adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
        p ε (v j) := by
    apply Finset.prod_nonneg
    intro j _
    exact adaptiveMainMass_nonneg select θ _ p ε hselect hp hθ
      (pilotTheta_interior p ε m (pilotAdaptiveEncode hmn u (fun _ => 0)))
      hε (v j)
  have hatom (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
      μ {e (u, v)} = ENNReal.ofReal
        (pilotPrefixWeight θ p ε m n u *
          ∏ j, adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
            p ε (v j)) := by
    rw [pilotAdaptive_joint_singleton_eq_prefix_mul_mainProduct
      select θ p ε m hselect hp hθ hε hmn u v]
    change ENNReal.ofReal (pilotPrefixWeight θ p ε m n u) *
      ENNReal.ofReal (∏ j, adaptiveMainMass select θ
        (pilotAdaptivePrefixTheta p ε m hmn u) p ε (v j)) = _
    exact (ENNReal.ofReal_mul (hw u)).symm
  have hA : MeasurableSet A := MeasurableSet.of_discrete
  rw [show μ A = ∫⁻ z, A.indicator (fun _ => (1 : ENNReal)) z ∂μ by
    rw [lintegral_indicator hA, setLIntegral_one]]
  rw [MeasureTheory.lintegral_fintype]
  rw [sum_eq_sum_image_of_zero_off_range e (pilotAdaptiveEncode_pair_injective hmn)]
  · rw [Fintype.sum_prod_type]
    simp_rw [hatom]
    have hind (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
        A.indicator (fun _ => (1 : ENNReal)) (e (u, v)) =
          if δ < |adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
              (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
              p ε m hselect hp hε n (fun i => v (Fin.cast hmain i)) - Vstar θ p ε|
          then 1 else 0 := by
      rw [Set.indicator_apply]
      simp only [A, Set.mem_ofPred_eq, e,
        VhatStar_pilotAdaptiveEncode_eq_adaptiveEmpiricalVariance
          select θ p ε m hselect hp hε hmn hN hmain u v]
    simp_rw [hind]
    have hindOfReal (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
        (if δ < |adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
            (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
            p ε m hselect hp hε n (fun i => v (Fin.cast hmain i)) - Vstar θ p ε|
          then (1 : ENNReal) else 0) =
        ENNReal.ofReal (if δ < |adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
            (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
            p ε m hselect hp hε n (fun i => v (Fin.cast hmain i)) - Vstar θ p ε|
          then (1 : ℝ) else 0) := by
      split_ifs <;> simp
    simp_rw [hindOfReal]
    have hmul (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
        ENNReal.ofReal (if δ < |adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
            (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
            p ε m hselect hp hε n (fun i => v (Fin.cast hmain i)) - Vstar θ p ε|
          then (1 : ℝ) else 0) *
          ENNReal.ofReal (pilotPrefixWeight θ p ε m n u *
            ∏ j, adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
              p ε (v j)) =
        ENNReal.ofReal ((if δ < |adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
            (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
            p ε m hselect hp hε n (fun i => v (Fin.cast hmain i)) - Vstar θ p ε|
          then (1 : ℝ) else 0) *
          (pilotPrefixWeight θ p ε m n u *
            ∏ j, adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
              p ε (v j))) := by
      exact (ENNReal.ofReal_mul (by split_ifs <;> positivity)).symm
    simp_rw [hmul]
    have hofReal_sum {B : Type} [Fintype B] (f : B → ℝ)
        (hf : ∀ b, 0 ≤ f b) :
        (∑ b, ENNReal.ofReal (f b)) = ENNReal.ofReal (∑ b, f b) := by
      simpa using (ENNReal.ofReal_sum_of_nonneg
        (s := Finset.univ) (fun b _ => hf b)).symm
    calc
      (∑ u : Fin (m n) → Fin 4, ∑ v : Fin (n - m n) → Fin 14,
        ENNReal.ofReal ((if δ < |adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
            (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
            p ε m hselect hp hε n (fun i => v (Fin.cast hmain i)) - Vstar θ p ε|
          then (1 : ℝ) else 0) *
          (pilotPrefixWeight θ p ε m n u *
            ∏ j, adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
              p ε (v j)))) =
        ENNReal.ofReal (∑ u : Fin (m n) → Fin 4,
          ∑ v : Fin (n - m n) → Fin 14,
            (if δ < |adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
                (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
                p ε m hselect hp hε n (fun i => v (Fin.cast hmain i)) - Vstar θ p ε|
              then (1 : ℝ) else 0) *
              (pilotPrefixWeight θ p ε m n u *
                ∏ j, adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
                  p ε (v j))) := by
          rw [show (∑ u : Fin (m n) → Fin 4,
              ∑ v : Fin (n - m n) → Fin 14,
                ENNReal.ofReal ((if δ < |adaptivePilotRowEmpiricalVariance select θ
                    (fun _ => 0) (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
                    p ε m hselect hp hε n (fun i => v (Fin.cast hmain i)) - Vstar θ p ε|
                  then (1 : ℝ) else 0) *
                  (pilotPrefixWeight θ p ε m n u *
                    ∏ j, adaptiveMainMass select θ
                      (pilotAdaptivePrefixTheta p ε m hmn u) p ε (v j)))) =
              ∑ u : Fin (m n) → Fin 4, ENNReal.ofReal
                (∑ v : Fin (n - m n) → Fin 14,
                  (if δ < |adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
                      (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
                      p ε m hselect hp hε n (fun i => v (Fin.cast hmain i)) - Vstar θ p ε|
                    then (1 : ℝ) else 0) *
                    (pilotPrefixWeight θ p ε m n u *
                      ∏ j, adaptiveMainMass select θ
                        (pilotAdaptivePrefixTheta p ε m hmn u) p ε (v j))) by
            apply Finset.sum_congr rfl
            intro u _
            exact hofReal_sum _ (fun v => mul_nonneg
              (by split_ifs <;> positivity) (mul_nonneg (hw u) (hm u v)))]
          exact hofReal_sum _ (fun u => Finset.sum_nonneg fun v _ => mul_nonneg
            (by split_ifs <;> positivity) (mul_nonneg (hw u) (hm u v)))
      _ = ENNReal.ofReal (pilotVarianceBadMass select θ p ε δ m hselect hp hε
          (Nat.le_of_lt (hsub.2 n hn).2)) := by
        congr 1
        rw [show hmn = Nat.le_of_lt (hsub.2 n hn).2 from Subsingleton.elim _ _]
        unfold pilotVarianceBadMass pilotConditionalVarianceBadMass
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum]
        let rowEquiv : (Fin (adaptiveMainSize m n) → Fin 14) ≃
            (Fin (n - m n) → Fin 14) :=
          Equiv.piCongrLeft (fun _ : Fin (n - m n) => Fin 14) (finCongr hmain)
        symm
        apply Fintype.sum_equiv rowEquiv
        intro v
        have happly (i : Fin (adaptiveMainSize m n)) :
            rowEquiv v (Fin.cast hmain i) = v i := by
          rfl
        have happly' (i : Fin (adaptiveMainSize m n)) :
            rowEquiv v ((finCongr hmain) i) = v i := by
          change rowEquiv v (Fin.cast hmain i) = v i
          exact happly i
        have hfun : (fun i => rowEquiv v (Fin.cast hmain i)) = v :=
          funext happly
        have hprod :
            (∏ i : Fin (adaptiveMainSize m n),
              adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
                p ε (v i)) =
            ∏ j : Fin (n - m n),
              adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
                p ε (rowEquiv v j) := by
          simpa only [happly'] using (Equiv.prod_comp (finCongr hmain)
            (fun j : Fin (n - m n) =>
              adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
                p ε (rowEquiv v j)))
        simp only [adaptivePilotRowProductMass, adaptivePilotRowMass, hzero,
          hfun, hprod]
        ring
  · intro z hz
    have hzμ := pilotAdaptive_singleton_zero_of_not_range
      select θ p ε m hselect hp hε hmn z hz
    apply mul_eq_zero.mpr
    right
    simpa only [μ] using hzμ

/-- Under the pilot growth and interiority conditions, the probability under the actual transcript law that `VhatStar` differs from `Vstar` by more than any positive tolerance tends to zero. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hdiv,hsub), [the pilot Vhat Star consistent](goal).

Under the stated assumptions, the pilot Vhat Star consistent. -/
lemma pilot_VhatStar_consistent
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hdiv : PilotDiverges m) (hsub : PilotSublinear m) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        {z | δ < |VhatStar p ε m (select) z -
          Vstar θ p ε|}) atTop (nhds 0) := by
  intro δ hδ
  have hmass := pilotVarianceBadMass_tendsto_zero
    select θ p ε δ m hselect hp hθ hε hdiv hsub hδ
  have hof := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hmass
  simpa only [ENNReal.ofReal_zero] using hof.congr' (by
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [Function.comp_apply, dif_pos hn,
      transcriptLaw_VhatStar_bad_eq_ofReal_pilotVarianceBadMass
        select θ p ε δ m hselect hp hθ hε hsub hn])

end CausalSmith.Stat.LdpAteEfficiencySurface
