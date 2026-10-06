module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotVhatConsistency

/-! # Exact conditional CDF identity for the private pilot estimator

This file separates the finite-sample distributional step from the later
triangular-row Gaussian limit.  The conditional CDF below is the literal iid
main-row product mass evaluated on the centered root-`n` estimator error.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open MeasureTheory
open scoped BigOperators ENNReal

/-- A finite sum is invariant under the canonical transport along an equality
of its row lengths. For [the displayed inputs and conditions](hyp:h,q), [the stated result](goal) follows. -/
lemma finite_sum_cast_eq {N K : ℕ} (h : N = K) (q : Fin K → ℝ) :
    (∑ i : Fin N, q (Fin.cast h i)) = ∑ j : Fin K, q j := by
  subst K
  rfl

/-- The conditional CDF of the centered root-`n` error in one adaptive iid main row. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Pilot Row Scaled CDF](goal) is determined by [the displayed parameters](hyp:select,θ,h,η,p,ε,m,hselect,hp,hε,n,x). -/
def adaptivePilotRowScaledCDF
    (θ h : TrialParameter) (η : ℕ → TrialParameter)
    (p ε : ℝ) (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    (n : ℕ) (x : ℝ) : ℝ :=
  ∑ v : Fin (adaptiveMainSize m n) → Fin 14,
    adaptivePilotRowProductMass select θ h η p ε m hselect hp hε n v *
      if Real.sqrt (n : ℝ) * (adaptiveMainSize m n : ℝ)⁻¹ *
          (∑ j, adaptivePilotRowScore select θ h η p ε hselect hp hε n (v j)) ≤ x
      then 1 else 0

/-- The genuine released-prefix mixture of the conditional adaptive-row CDF. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The pilot Prefix Scaled Error CDF](goal) is determined by [the displayed parameters](hyp:select,θ,h,p,ε,m,hselect,hp,hε,hmn,x). -/
def pilotPrefixScaledErrorCDF
    (θ h : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    {n : ℕ} (hmn : m n ≤ n) (x : ℝ) : ℝ :=
  ∑ u : Fin (m n) → Fin 4,
    pilotPrefixWeight (localAlternative θ h n) p ε m n u *
      adaptivePilotRowScaledCDF select θ h
        (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
        p ε m hselect hp hε n x

/-- On a correctly encoded transcript, the centered scaled estimator error is the scaled average of the literal centered adaptive main-row scores. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hmn,hlocal,hN,hmain), [the scaled Error pilot Adaptive Encode eq adaptive Pilot Row](goal).

Under the stated assumptions, the scaled Error pilot Adaptive Encode eq adaptive Pilot Row. -/
lemma scaledError_pilotAdaptiveEncode_eq_adaptivePilotRow
    (θ h : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) {n : ℕ}
    (hmn : m n ≤ n) (hlocal : InteriorMeans (localAlternative θ h n))
    (hN : 0 < adaptiveMainSize m n)
    (hmain : adaptiveMainSize m n = n - m n)
    (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
    scaledError (pilotEstimator p ε m select hselect hp hε) θ h n
        (pilotAdaptiveEncode hmn u v) =
      Real.sqrt (n : ℝ) * (adaptiveMainSize m n : ℝ)⁻¹ *
        ∑ i, adaptivePilotRowScore select θ h
          (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
          p ε hselect hp hε n (v (Fin.cast hmain i)) := by
  let η := pilotAdaptivePrefixTheta p ε m hmn u
  have htrue : adaptiveTrueParam θ h n = localAlternative θ h n :=
    adaptiveTrueParam_eq_localAlternative θ h n hlocal
  have herr := adaptivePilotRow_estimatorError_eq select θ h (fun _ => η)
    p ε m hselect hp hε n hN (fun i => v (Fin.cast hmain i))
  have hcast : (adaptiveMainSize m n : ℝ) = (n - m n : ℕ) := by
    exact_mod_cast hmain
  have hsum :
      (∑ i : Fin (adaptiveMainSize m n),
        adaptiveSelectedScore select η p ε (v (Fin.cast hmain i))) =
      ∑ j : Fin (n - m n), adaptiveSelectedScore select η p ε (v j) :=
    finite_sum_cast_eq hmain
      (fun j => adaptiveSelectedScore select η p ε (v j))
  unfold scaledError
  change Real.sqrt (n : ℝ) *
    (tauStar p ε m (select)
      (pilotAdaptiveEncode hmn u v) - contrast (localAlternative θ h n)) = _
  rw [tauStar_pilotAdaptiveEncode select p ε m hp hε hmn u v]
  calc
    Real.sqrt (n : ℝ) *
        (contrast η + ((n - m n : ℕ) : ℝ)⁻¹ *
          (∑ j, adaptiveSelectedScore select η p ε (v j)) -
          contrast (localAlternative θ h n)) =
      Real.sqrt (n : ℝ) *
        (contrast η + (adaptiveMainSize m n : ℝ)⁻¹ *
          (∑ i, adaptiveSelectedScore select η p ε
            (v (Fin.cast hmain i))) - contrast (adaptiveTrueParam θ h n)) := by
      rw [htrue, hcast, hsum]
    _ = Real.sqrt (n : ℝ) *
        ((adaptiveMainSize m n : ℝ)⁻¹ *
          ∑ i, adaptivePilotRowScore select θ h (fun _ => η)
            p ε hselect hp hε n (v (Fin.cast hmain i))) := by rw [herr]
    _ = _ := by simp only [η]; ring

/-- At every proper pilot split with an interior local alternative, the actual scaled-error transcript CDF is exactly the released-prefix mixture of the conditional centered iid-row CDFs. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hsub,hn,hlocal), [the transcript Law scaled Error le eq of Real pilot Prefix Scaled Error CDF](goal).

Under the stated assumptions, the transcript Law scaled Error le eq of Real pilot Prefix Scaled Error CDF. -/
lemma transcriptLaw_scaledError_le_eq_ofReal_pilotPrefixScaledErrorCDF
    (θ h : TrialParameter) (p ε x : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    (hsub : PilotSublinear m) {n : ℕ} (hn : 2 ≤ n)
    (hlocal : InteriorMeans (localAlternative θ h n)) :
    (transcriptLaw (pilotEstimator p ε m select hselect hp hε)
      (localAlternative θ h n) p n)
        {z | scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z ≤ x} =
      ENNReal.ofReal
        (pilotPrefixScaledErrorCDF select θ h p ε m hselect hp hε
          (Nat.le_of_lt (hsub.2 n hn).2) x) := by
  classical
  let θn := localAlternative θ h n
  let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
  let μ := transcriptLaw (pilotEstimator p ε m select hselect hp hε) θn p n
  let A : Set (Transcript (pilotOutputFamily n)) :=
    {z | scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z ≤ x}
  let e := fun uv : (Fin (m n) → Fin 4) × (Fin (n - m n) → Fin 14) =>
    pilotAdaptiveEncode hmn uv.1 uv.2
  have hN : 0 < adaptiveMainSize m n := by
    rw [adaptiveMainSize, adaptivePilotSize_eq m hsub hn]
    exact Nat.sub_pos_of_lt (hsub.2 n hn).2
  have hmain : adaptiveMainSize m n = n - m n := by
    simp [adaptiveMainSize, adaptivePilotSize_eq m hsub hn]
  have htrue : adaptiveTrueParam θ h n = θn :=
    adaptiveTrueParam_eq_localAlternative θ h n hlocal
  have hw (u : Fin (m n) → Fin 4) :
      0 ≤ pilotPrefixWeight θn p ε m n u :=
    pilotPrefixWeight_nonneg θn p ε m n hp hlocal u
  have hm (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
      0 ≤ ∏ j, adaptiveMainMass select θn
        (pilotAdaptivePrefixTheta p ε m hmn u) p ε (v j) := by
    apply Finset.prod_nonneg
    intro j _
    exact adaptiveMainMass_nonneg select θn _ p ε hselect hp hlocal
      (pilotTheta_interior p ε m (pilotAdaptiveEncode hmn u (fun _ => 0)))
      hε (v j)
  have hatom (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
      μ {e (u, v)} = ENNReal.ofReal
        (pilotPrefixWeight θn p ε m n u *
          ∏ j, adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
            p ε (v j)) := by
    rw [pilotAdaptive_joint_singleton_eq_prefix_mul_mainProduct
      select θn p ε m hselect hp hlocal hε hmn u v]
    change ENNReal.ofReal (pilotPrefixWeight θn p ε m n u) *
      ENNReal.ofReal (∏ j, adaptiveMainMass select θn
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
          if Real.sqrt (n : ℝ) * (adaptiveMainSize m n : ℝ)⁻¹ *
              (∑ i, adaptivePilotRowScore select θ h
                (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
                p ε hselect hp hε n (v (Fin.cast hmain i))) ≤ x
          then 1 else 0 := by
      rw [Set.indicator_apply]
      simp only [A, Set.mem_ofPred_eq, e,
        scaledError_pilotAdaptiveEncode_eq_adaptivePilotRow
          select θ h p ε m hselect hp hε hmn hlocal hN hmain u v]
    simp_rw [hind]
    have hindOfReal (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
        (if Real.sqrt (n : ℝ) * (adaptiveMainSize m n : ℝ)⁻¹ *
              (∑ i, adaptivePilotRowScore select θ h
                (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
                p ε hselect hp hε n (v (Fin.cast hmain i))) ≤ x
          then (1 : ENNReal) else 0) =
        ENNReal.ofReal
          (if Real.sqrt (n : ℝ) * (adaptiveMainSize m n : ℝ)⁻¹ *
              (∑ i, adaptivePilotRowScore select θ h
                (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
                p ε hselect hp hε n (v (Fin.cast hmain i))) ≤ x
          then (1 : ℝ) else 0) := by
      split_ifs <;> simp
    simp_rw [hindOfReal]
    have hmul (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
        ENNReal.ofReal
          (if Real.sqrt (n : ℝ) * (adaptiveMainSize m n : ℝ)⁻¹ *
              (∑ i, adaptivePilotRowScore select θ h
                (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
                p ε hselect hp hε n (v (Fin.cast hmain i))) ≤ x
          then (1 : ℝ) else 0) *
          ENNReal.ofReal (pilotPrefixWeight θn p ε m n u *
            ∏ j, adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
              p ε (v j)) =
        ENNReal.ofReal
          ((if Real.sqrt (n : ℝ) * (adaptiveMainSize m n : ℝ)⁻¹ *
              (∑ i, adaptivePilotRowScore select θ h
                (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
                p ε hselect hp hε n (v (Fin.cast hmain i))) ≤ x
            then (1 : ℝ) else 0) *
            (pilotPrefixWeight θn p ε m n u *
              ∏ j, adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
                p ε (v j))) := by
      exact (ENNReal.ofReal_mul (by split_ifs <;> positivity)).symm
    simp_rw [hmul]
    have hofReal_sum {B : Type} [Fintype B] (f : B → ℝ)
        (hf : ∀ b, 0 ≤ f b) :
        (∑ b, ENNReal.ofReal (f b)) = ENNReal.ofReal (∑ b, f b) := by
      simpa using (ENNReal.ofReal_sum_of_nonneg
        (s := Finset.univ) (fun b _ => hf b)).symm
    rw [show (∑ u : Fin (m n) → Fin 4, ∑ v : Fin (n - m n) → Fin 14,
        ENNReal.ofReal
          ((if Real.sqrt (n : ℝ) * (adaptiveMainSize m n : ℝ)⁻¹ *
              (∑ i, adaptivePilotRowScore select θ h
                (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
                p ε hselect hp hε n (v (Fin.cast hmain i))) ≤ x
            then (1 : ℝ) else 0) *
            (pilotPrefixWeight θn p ε m n u *
              ∏ j, adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
                p ε (v j)))) =
        ENNReal.ofReal (∑ u : Fin (m n) → Fin 4,
          ∑ v : Fin (n - m n) → Fin 14,
            (if Real.sqrt (n : ℝ) * (adaptiveMainSize m n : ℝ)⁻¹ *
                (∑ i, adaptivePilotRowScore select θ h
                  (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
                  p ε hselect hp hε n (v (Fin.cast hmain i))) ≤ x
              then (1 : ℝ) else 0) *
              (pilotPrefixWeight θn p ε m n u *
                ∏ j, adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
                  p ε (v j))) by
      rw [show (∑ u : Fin (m n) → Fin 4, ∑ v : Fin (n - m n) → Fin 14,
          ENNReal.ofReal
            ((if Real.sqrt (n : ℝ) * (adaptiveMainSize m n : ℝ)⁻¹ *
                (∑ i, adaptivePilotRowScore select θ h
                  (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
                  p ε hselect hp hε n (v (Fin.cast hmain i))) ≤ x
              then (1 : ℝ) else 0) *
              (pilotPrefixWeight θn p ε m n u *
                ∏ j, adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
                  p ε (v j)))) =
          ∑ u : Fin (m n) → Fin 4, ENNReal.ofReal
            (∑ v : Fin (n - m n) → Fin 14,
              (if Real.sqrt (n : ℝ) * (adaptiveMainSize m n : ℝ)⁻¹ *
                  (∑ i, adaptivePilotRowScore select θ h
                    (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
                    p ε hselect hp hε n (v (Fin.cast hmain i))) ≤ x
                then (1 : ℝ) else 0) *
                (pilotPrefixWeight θn p ε m n u *
                  ∏ j, adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
                    p ε (v j))) by
        apply Finset.sum_congr rfl
        intro u _
        exact hofReal_sum _ (fun v => mul_nonneg
          (by split_ifs <;> positivity) (mul_nonneg (hw u) (hm u v))) ]
      exact hofReal_sum _ (fun u => Finset.sum_nonneg fun v _ => mul_nonneg
        (by split_ifs <;> positivity) (mul_nonneg (hw u) (hm u v))) ]
    congr 1
    rw [show hmn = Nat.le_of_lt (hsub.2 n hn).2 from Subsingleton.elim _ _]
    unfold pilotPrefixScaledErrorCDF adaptivePilotRowScaledCDF
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
        rowEquiv v (Fin.cast hmain i) = v i := by rfl
    have happly' (i : Fin (adaptiveMainSize m n)) :
        rowEquiv v ((finCongr hmain) i) = v i := by
      change rowEquiv v (Fin.cast hmain i) = v i
      exact happly i
    have hscores :
        (∑ i : Fin (adaptiveMainSize m n),
          adaptivePilotRowScore select θ h
            (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
            p ε hselect hp hε n (rowEquiv v (Fin.cast hmain i))) =
        ∑ i : Fin (adaptiveMainSize m n),
          adaptivePilotRowScore select θ h
            (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
            p ε hselect hp hε n (v i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [happly]
    have hprod :
        (∏ i : Fin (adaptiveMainSize m n),
          adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
            p ε (v i)) =
        ∏ j : Fin (n - m n),
          adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
            p ε (rowEquiv v j) := by
      simpa only [happly'] using (Equiv.prod_comp (finCongr hmain)
        (fun j : Fin (n - m n) =>
          adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
            p ε (rowEquiv v j)))
    simp only [adaptivePilotRowProductMass, adaptivePilotRowMass, htrue]
    rw [hprod, hscores]
    ring
  · intro z hz
    have hzμ := pilotAdaptive_singleton_zero_of_not_range
      select θn p ε m hselect hp hε hmn z hz
    apply mul_eq_zero.mpr
    right
    simpa only [μ] using hzμ

/-- The real-valued CDF of the actual scaled estimator error is the genuine prefix-weighted conditional row CDF. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hsub,hn,hlocal), [the transcript Law real scaled Error le eq pilot Prefix Scaled Error CDF](goal).

Under the stated assumptions, the transcript Law real scaled Error le eq pilot Prefix Scaled Error CDF. -/
lemma transcriptLaw_real_scaledError_le_eq_pilotPrefixScaledErrorCDF
    (θ h : TrialParameter) (p ε x : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    (hsub : PilotSublinear m) {n : ℕ} (hn : 2 ≤ n)
    (hlocal : InteriorMeans (localAlternative θ h n)) :
    (transcriptLaw (pilotEstimator p ε m select hselect hp hε)
      (localAlternative θ h n) p n).real
        {z | scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z ≤ x} =
      pilotPrefixScaledErrorCDF select θ h p ε m hselect hp hε
        (Nat.le_of_lt (hsub.2 n hn).2) x := by
  let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
  have htrue : adaptiveTrueParam θ h n = localAlternative θ h n :=
    adaptiveTrueParam_eq_localAlternative θ h n hlocal
  have hw (u : Fin (m n) → Fin 4) :
      0 ≤ pilotPrefixWeight (localAlternative θ h n) p ε m n u :=
    pilotPrefixWeight_nonneg (localAlternative θ h n) p ε m n hp hlocal u
  have hmix : 0 ≤ pilotPrefixScaledErrorCDF select θ h p ε m hselect hp hε hmn x := by
    unfold pilotPrefixScaledErrorCDF adaptivePilotRowScaledCDF
    apply Finset.sum_nonneg
    intro u _
    apply mul_nonneg (hw u)
    apply Finset.sum_nonneg
    intro v _
    apply mul_nonneg
    · unfold adaptivePilotRowProductMass adaptivePilotRowMass
      rw [htrue]
      apply Finset.prod_nonneg
      intro j _
      exact adaptiveMainMass_nonneg select (localAlternative θ h n) _ p ε hselect hp hlocal
        (pilotTheta_interior p ε m (pilotAdaptiveEncode hmn u (fun _ => 0)))
        hε (v j)
    · split_ifs <;> positivity
  rw [Measure.real_def,
    transcriptLaw_scaledError_le_eq_ofReal_pilotPrefixScaledErrorCDF
      select θ h p ε x m hselect hp hε hsub hn hlocal]
  exact ENNReal.toReal_ofReal hmix

end CausalSmith.Stat.LdpAteEfficiencySurface
