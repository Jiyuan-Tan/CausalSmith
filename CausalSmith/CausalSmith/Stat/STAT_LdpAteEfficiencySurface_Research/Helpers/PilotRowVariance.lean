module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAttainmentSupport
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotRowInputs

/-!
# Empirical variance identities for adaptive pilot rows

This module identifies the paper's main-sample variance estimator with the literal
empirical variance of the centered finite row.  It also records the encoded-transcript
support factorization and the sample-size scaling used for root-n errors.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open scoped BigOperators ENNReal

/-- The empirical mean of the centered adaptive row score. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Pilot Row Empirical Mean](goal) is determined by [the displayed parameters](hyp:select,θ,h,η,p,ε,m,hselect,hp,hε,n,v). -/
def adaptivePilotRowEmpiricalMean (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (n : ℕ)
    (v : Fin (adaptiveMainSize m n) → Fin 14) : ℝ :=
  (adaptiveMainSize m n : ℝ)⁻¹ *
    ∑ j, adaptivePilotRowScore select θ h η p ε hselect hp hε n (v j)

/-- The empirical second moment of the centered adaptive row score. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Pilot Row Empirical Second](goal) is determined by [the displayed parameters](hyp:select,θ,h,η,p,ε,m,hselect,hp,hε,n,v). -/
def adaptivePilotRowEmpiricalSecond (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (n : ℕ)
    (v : Fin (adaptiveMainSize m n) → Fin 14) : ℝ :=
  (adaptiveMainSize m n : ℝ)⁻¹ *
    ∑ j, (adaptivePilotRowScore select θ h η p ε hselect hp hε n (v j)) ^ 2

/-- The empirical variance of the centered adaptive row score. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Pilot Row Empirical Variance](goal) is determined by [the displayed parameters](hyp:select,θ,h,η,p,ε,m,hselect,hp,hε,n,v). -/
def adaptivePilotRowEmpiricalVariance (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (n : ℕ)
    (v : Fin (adaptiveMainSize m n) → Fin 14) : ℝ :=
  adaptivePilotRowEmpiricalSecond select θ h η p ε m hselect hp hε n v -
    (adaptivePilotRowEmpiricalMean select θ h η p ε m hselect hp hε n v) ^ 2

/-- A finite nonempty sample's second-moment-minus-mean-square formula equals its
average squared deviation from the empirical mean. For [the displayed inputs and conditions](hyp:hN,x), [the stated result](goal) follows. -/
lemma finite_empiricalVariance_eq_average_sq_deviation
    {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) :
    (N : ℝ)⁻¹ * ∑ j, (x j) ^ 2 - ((N : ℝ)⁻¹ * ∑ j, x j) ^ 2 =
      (N : ℝ)⁻¹ * ∑ j, (x j - (N : ℝ)⁻¹ * ∑ k, x k) ^ 2 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, hcard]
  have hsq : (∑ i : Fin N, (N : ℝ)⁻¹ * x i ^ 2) =
      (N : ℝ)⁻¹ * ∑ i, x i ^ 2 := (Finset.mul_sum _ _ _).symm
  have hcross :
      (∑ i : Fin N, 2 * x i * ((N : ℝ)⁻¹ * ∑ j, x j)) =
        (2 * ((N : ℝ)⁻¹ * ∑ j, x j)) * ∑ j, x j := by
    calc
      _ = ∑ i : Fin N, (2 * ((N : ℝ)⁻¹ * ∑ j, x j)) * x i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [hsq, hcross]
  field_simp
  ring

/-- The adaptive row empirical variance is its average squared deviation from the empirical row mean. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hN), [the adaptive Pilot Row Empirical Variance eq average sq deviation](goal).

Under the stated assumptions, the adaptive Pilot Row Empirical Variance eq average sq deviation. -/
lemma adaptivePilotRowEmpiricalVariance_eq_average_sq_deviation
    (θ h : TrialParameter) (η : ℕ → TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (n : ℕ)
    (hN : 0 < adaptiveMainSize m n)
    (v : Fin (adaptiveMainSize m n) → Fin 14) :
    adaptivePilotRowEmpiricalVariance select θ h η p ε m hselect hp hε n v =
      (adaptiveMainSize m n : ℝ)⁻¹ * ∑ j,
        (adaptivePilotRowScore select θ h η p ε hselect hp hε n (v j) -
          adaptivePilotRowEmpiricalMean select θ h η p ε m hselect hp hε n v) ^ 2 := by
  exact finite_empiricalVariance_eq_average_sq_deviation hN
    (fun j => adaptivePilotRowScore select θ h η p ε hselect hp hε n (v j))

/-- On an encoded transcript, summing any transformed main-release score over the full transcript is the corresponding sum over the main row. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hmn), [the pilot Adaptive Encode main score sum](goal).

Under the stated assumptions, the pilot Adaptive Encode main score sum. -/
lemma pilotAdaptiveEncode_main_score_sum
    (p ε : ℝ) (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    {n : ℕ} (hmn : m n ≤ n) (u : Fin (m n) → Fin 4)
    (v : Fin (n - m n) → Fin 14) (g : ℝ → ℝ) :
    (∑ i : Fin n, if m n ≤ i.val then
        g (phiOutput (pilotAdaptivePrefixTheta p ε m hmn u) p ε
          (select) (pilotAdaptiveEncode hmn u v i))
      else 0) =
      ∑ j, g (adaptiveSelectedScore select
        (pilotAdaptivePrefixTheta p ε m hmn u) p ε (v j)) := by
  rw [show (∑ i : Fin n, if m n ≤ i.val then
      g (phiOutput (pilotAdaptivePrefixTheta p ε m hmn u) p ε
        (select) (pilotAdaptiveEncode hmn u v i))
    else 0) =
      ∑ i : Fin n, if hi : i.val < m n then (0 : ℝ)
        else g (adaptiveSelectedScore
          select (pilotAdaptivePrefixTheta p ε m hmn u) p ε
          (v ⟨i.val - m n, by omega⟩)) by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < m n
    · simp [hi]
    · have him : m n ≤ i.val := Nat.le_of_not_gt hi
      simp [hi, him, pilotAdaptiveEncode, phiOutput, adaptiveSelectedScore]]
  rw [fin_sum_split hmn (fun _ : Fin (m n) => (0 : ℝ))
    (fun j : Fin (n - m n) => g (adaptiveSelectedScore
      select (pilotAdaptivePrefixTheta p ε m hmn u) p ε (v j)))]
  simp

/-- On a properly encoded transcript, `VhatStar` is exactly the empirical variance of the selected main-release scores. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hmn), [the Vhat Star pilot Adaptive Encode](goal).

Under the stated assumptions, the Vhat Star pilot Adaptive Encode. -/
lemma VhatStar_pilotAdaptiveEncode
    (p ε : ℝ) (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    {n : ℕ} (hmn : m n ≤ n) (u : Fin (m n) → Fin 4)
    (v : Fin (n - m n) → Fin 14) :
    VhatStar p ε m (select)
        (pilotAdaptiveEncode hmn u v) =
      let η := pilotAdaptivePrefixTheta p ε m hmn u
      let q : Fin 14 → ℝ := adaptiveSelectedScore select η p ε
      let qbar := ((n - m n : ℕ) : ℝ)⁻¹ * ∑ j, q (v j)
      ((n - m n : ℕ) : ℝ)⁻¹ * ∑ j, (q (v j) - qbar) ^ 2 := by
  rw [VhatStar, pilotTheta_pilotAdaptiveEncode p ε m hmn u v]
  dsimp only
  have hsum := pilotAdaptiveEncode_main_score_sum select p ε m hselect hp hε hmn u v id
  simp only [id_eq] at hsum
  rw [hsum]
  rw [pilotAdaptiveEncode_main_score_sum select p ε m hselect hp hε hmn u v
    (fun x => (x - ((n - m n : ℕ) : ℝ)⁻¹ *
      ∑ j, adaptiveSelectedScore select (pilotAdaptivePrefixTheta p ε m hmn u)
        p ε (v j)) ^ 2)]

/-- Centering every selected score by the same population correction does not change its empirical variance. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hN), [the adaptive Pilot Row Empirical Variance eq selected](goal).

Under the stated assumptions, the adaptive Pilot Row Empirical Variance eq selected. -/
lemma adaptivePilotRowEmpiricalVariance_eq_selected
    (θ h : TrialParameter) (η : ℕ → TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (n : ℕ)
    (hN : 0 < adaptiveMainSize m n)
    (v : Fin (adaptiveMainSize m n) → Fin 14) :
    adaptivePilotRowEmpiricalVariance select θ h η p ε m hselect hp hε n v =
      let q : Fin 14 → ℝ := adaptiveSelectedScore select (η n) p ε
      let qbar := (adaptiveMainSize m n : ℝ)⁻¹ * ∑ j, q (v j)
      (adaptiveMainSize m n : ℝ)⁻¹ * ∑ j, (q (v j) - qbar) ^ 2 := by
  rw [adaptivePilotRowEmpiricalVariance_eq_average_sq_deviation
    select θ h η p ε m hselect hp hε n hN v]
  have hNr : (adaptiveMainSize m n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hN)
  have hmean : adaptivePilotRowEmpiricalMean select θ h η p ε m hselect hp hε n v =
      (adaptiveMainSize m n : ℝ)⁻¹ *
          ∑ j, adaptiveSelectedScore select (η n) p ε (v j) -
        (contrast (adaptiveTrueParam θ h n) - contrast (η n)) := by
    unfold adaptivePilotRowEmpiricalMean
    rw [adaptivePilotRowScore_sum_eq select θ h η p ε m hselect hp hε n v]
    field_simp
  rw [hmean]
  apply congrArg ((adaptiveMainSize m n : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro j _
  unfold adaptivePilotRowScore
  ring

/-- The empirical variance of the population-centered scores in an encoded main row. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Encoded Row Empirical Variance](goal) is determined by [the displayed parameters](hyp:select,θ,h,p,ε,m,hselect,hp,hε,hmn,u,v). -/
def adaptiveEncodedRowEmpiricalVariance
    (θ h : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) {n : ℕ}
    (hmn : m n ≤ n) (u : Fin (m n) → Fin 4)
    (v : Fin (n - m n) → Fin 14) : ℝ :=
  let η := pilotAdaptivePrefixTheta p ε m hmn u
  let f : Fin 14 → ℝ := fun s =>
    adaptiveSelectedScore select η p ε s -
      (contrast (adaptiveTrueParam θ h n) - contrast η)
  ((n - m n : ℕ) : ℝ)⁻¹ * ∑ j, (f (v j)) ^ 2 -
    (((n - m n : ℕ) : ℝ)⁻¹ * ∑ j, f (v j)) ^ 2

/-- Under a proper nonempty pilot split, `VhatStar` on an encoded transcript is exactly the empirical variance of the population-centered main-row score. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hmn,hN), [the Vhat Star pilot Adaptive Encode eq row Variance](goal).

Under the stated assumptions, the Vhat Star pilot Adaptive Encode eq row Variance. -/
-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
lemma VhatStar_pilotAdaptiveEncode_eq_rowVariance
    (θ h : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) {n : ℕ}
    (hmn : m n ≤ n) (hN : 0 < n - m n) (u : Fin (m n) → Fin 4)
    (v : Fin (n - m n) → Fin 14) :
    VhatStar p ε m (select)
        (pilotAdaptiveEncode hmn u v) =
      adaptiveEncodedRowEmpiricalVariance select θ h p ε m hselect hp hε hmn u v := by
  rw [VhatStar_pilotAdaptiveEncode select p ε m hselect hp hε hmn u v]
  unfold adaptiveEncodedRowEmpiricalVariance
  dsimp only
  rw [finite_empiricalVariance_eq_average_sq_deviation hN]
  let q : Fin 14 → ℝ :=
    adaptiveSelectedScore select (pilotAdaptivePrefixTheta p ε m hmn u) p ε
  let c := contrast (adaptiveTrueParam θ h n) -
    contrast (pilotAdaptivePrefixTheta p ε m hmn u)
  have hNr : ((n - m n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hN)
  have hmean : ((n - m n : ℕ) : ℝ)⁻¹ * ∑ j, (q (v j) - c) =
      ((n - m n : ℕ) : ℝ)⁻¹ * ∑ j, q (v j) - c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ : Finset (Fin (n - m n))).card = n - m n := by simp
    rw [hcard]
    field_simp
  rw [hmean]
  apply congrArg (((n - m n : ℕ) : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Root-n squared main-estimation error is the row-normalized squared sum multiplied by the exact sample-size ratio `n / adaptiveMainSize m n`. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hN), [the adaptive Pilot Row root N error sq](goal).

Under the stated assumptions, the adaptive Pilot Row root N error sq. -/
-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
lemma adaptivePilotRow_rootN_error_sq
    (θ h : TrialParameter) (η : ℕ → TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (n : ℕ)
    (hN : 0 < adaptiveMainSize m n)
    (v : Fin (adaptiveMainSize m n) → Fin 14) :
    (n : ℝ) *
        (contrast (η n) + (adaptiveMainSize m n : ℝ)⁻¹ *
          (∑ j, adaptiveSelectedScore select (η n) p ε (v j)) -
          contrast (adaptiveTrueParam θ h n)) ^ 2 =
      ((n : ℝ) / (adaptiveMainSize m n : ℝ)) *
        ((Real.sqrt (adaptiveMainSize m n : ℝ))⁻¹ *
          ∑ j, adaptivePilotRowScore select θ h η p ε hselect hp hε n (v j)) ^ 2 := by
  rw [adaptivePilotRow_estimatorError_eq select θ h η p ε m hselect hp hε n hN v]
  have hNr : 0 < (adaptiveMainSize m n : ℝ) := by exact_mod_cast hN
  have hsqrt : (Real.sqrt (adaptiveMainSize m n : ℝ)) ^ 2 =
      adaptiveMainSize m n := Real.sq_sqrt hNr.le
  have hsqrt_ne : Real.sqrt (adaptiveMainSize m n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hNr)
  field_simp
  rw [hsqrt]
  ring

/-- The exact transcript atom is its pilot-prefix mass times the conditional iid main-row product mass. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hmn), [the pilot Adaptive joint singleton eq prefix mul main Product](goal).

Under the stated assumptions, the pilot Adaptive joint singleton eq prefix mul main Product. -/
lemma pilotAdaptive_joint_singleton_eq_prefix_mul_mainProduct
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    {n : ℕ} (hmn : m n ≤ n) (u : Fin (m n) → Fin 4)
    (v : Fin (n - m n) → Fin 14) :
    transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n
        {pilotAdaptiveEncode hmn u v} =
      ENNReal.ofReal (∏ j : Fin (m n),
        ∑ a : Fin 4, piTheta θ p a * rrPilotProbability ε a (u j)) *
      ENNReal.ofReal (∏ j : Fin (n - m n),
        adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
          p ε (v j)) := by
  rw [pilotAdaptive_joint_singleton select θ p ε m hselect hp hθ hε hmn u v]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · rw [ENNReal.ofReal_prod_of_nonneg]
    intro j _
    exact adaptiveMainMass_nonneg select θ _ p ε hselect hp hθ
      (pilotTheta_interior p ε m (pilotAdaptiveEncode hmn u (fun _ => 0))) hε (v j)
  · intro j _
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (piTheta_pos_interior θ p hp hθ a).le (by
      unfold rrPilotProbability
      split_ifs <;> positivity)

end CausalSmith.Stat.LdpAteEfficiencySurface
