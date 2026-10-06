module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelDefinitions
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.KLabelDefinitions
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.Quantization
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.TAllLabelAmbiguity

/-!
# Finite label reciprocal-score geometry

This file records the two-arm algebra used to turn cellwise reciprocal-score
deviations into ordinary absolute score deviations.
-/

@[expose] public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,hOverlap,hK,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma equalWidthRelease_cell_subset_closedBin {ε : ℝ} {K : ℕ}
    (hOverlap : Overlap ε) (hK : 0 < K) (r : LabelSpace K) :
    cell (equalWidthRelease ε K hK) r ⊆
      {e : ScoreSpace ε |
        ε + (r : ℕ) * ((1 - 2 * ε) / K) ≤ (e : ℝ) ∧
        (e : ℝ) ≤ ε + ((r : ℕ) + 1) * ((1 - 2 * ε) / K)} := by
  intro e he
  let L : ℝ := 1 - 2 * ε
  let t : ℝ := (K : ℝ) * ((e : ℝ) - ε) / L
  have hL : 0 < L := by dsimp [L]; linarith [hOverlap.2]
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg
      (mul_nonneg hKreal.le (sub_nonneg.mpr e.property.1)) hL.le
  have hmin : min (Nat.floor t) (K - 1) = (r : ℕ) := by
    have := congrArg Fin.val he
    simpa [cell, equalWidthRelease, t, L] using this
  have hrfloor : (r : ℕ) ≤ Nat.floor t := by omega
  have hlowerT : (r : ℝ) ≤ t := by
    have hcast : ((r : ℕ) : ℝ) ≤ (Nat.floor t : ℕ) := by exact_mod_cast hrfloor
    exact hcast.trans (Nat.floor_le ht0)
  have hlower : ε + (r : ℕ) * (L / K) ≤ (e : ℝ) := by
    dsimp [t] at hlowerT
    have h := (mul_le_mul_of_nonneg_right hlowerT (div_nonneg hL.le hKreal.le))
    field_simp at h ⊢
    nlinarith
  have hupper : (e : ℝ) ≤ ε + ((r : ℕ) + 1) * (L / K) := by
    by_cases hr : (r : ℕ) = K - 1
    · have heUpper := e.property.2
      rw [hr]
      have hKsub : (K - 1 : ℕ) + 1 = K := by omega
      have hKcast : ((K - 1 : ℕ) : ℝ) + 1 = (K : ℝ) := by
        exact_mod_cast hKsub
      rw [hKcast]
      field_simp
      dsimp [L]
      linarith
    · have hfloor : Nat.floor t = (r : ℕ) := by omega
      have htUpper : t < (r : ℕ) + 1 := by
        rw [← hfloor]
        exact Nat.lt_floor_add_one t
      dsimp [t] at htUpper
      have h := (mul_lt_mul_of_pos_right htUpper (div_pos hL hKreal))
      field_simp at h ⊢
      nlinarith
  simpa [L] using ⟨hlower, hupper⟩

/-- For [the specified mathematical inputs](hyp:ε,K,hK,hOverlap,r), [this definition](goal) introduces the corresponding object. -/
@[no_expose]
def equalWidthBinMidpoint (ε : ℝ) (K : ℕ) (hK : 0 < K)
    (hOverlap : Overlap ε) (r : LabelSpace K) : ScoreSpace ε :=
  ⟨ε + ((r : ℕ) + (1 / 2 : ℝ)) * ((1 - 2 * ε) / K), by
    have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
    have hwidth : 0 < 1 - 2 * ε := by linarith [hOverlap.2]
    have hr0 : 0 ≤ (r : ℝ) := by positivity
    have hrK : (r : ℝ) + (1 / 2 : ℝ) ≤ (K : ℝ) := by
      have hrCast : (r : ℝ) + 1 ≤ (K : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr r.isLt)
      linarith
    constructor
    · exact le_add_of_nonneg_right
        (mul_nonneg (by linarith) (div_nonneg hwidth.le hKreal.le))
    · have hratio : ((r : ℝ) + (1 / 2 : ℝ)) / K ≤ 1 :=
        (div_le_one hKreal).mpr hrK
      calc
        ε + ((r : ℕ) + (1 / 2 : ℝ)) * ((1 - 2 * ε) / K) =
            ε + (((r : ℝ) + (1 / 2 : ℝ)) / K) * (1 - 2 * ε) := by ring
        _ ≤ ε + 1 * (1 - 2 * ε) := by
          gcongr
        _ ≤ 1 - ε := by ring_nf; linarith ⟩

-- @node: equalWidthBinMidpoint_val
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,hK,hOverlap,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma equalWidthBinMidpoint_val (ε : ℝ) (K : ℕ) (hK : 0 < K)
    (hOverlap : Overlap ε) (r : LabelSpace K) :
    (equalWidthBinMidpoint ε K hK hOverlap r : ℝ) =
      ε + ((r : ℕ) + (1 / 2 : ℝ)) * ((1 - 2 * ε) / K) := by
  rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,a,r,c,hc), this result [establishes the stated mathematical conclusion](goal). -/
lemma cellAbsoluteDeviation_le_center {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (a : ArmSpace) (r : LabelSpace J) (c : ℝ)
    (hc : c ∈ Icc ((1 - ε)⁻¹) ε⁻¹) :
    cellAbsoluteDeviation H g a r ≤
      ∫ e in cell g r, |1 - c * armProb a e| ∂H := by
  unfold cellAbsoluteDeviation
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨d, hd, rfl⟩
    exact integral_nonneg fun _ => abs_nonneg _
  · exact ⟨c, hc, rfl⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,r,z), this result [establishes the stated mathematical conclusion](goal). -/
lemma sum_cellAbsoluteDeviation_le_commonCenterCandidates
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (hOverlap : Overlap ε) (r : LabelSpace J) (z : ScoreSpace ε) :
    cellAbsoluteDeviation H g true r + cellAbsoluteDeviation H g false r ≤
      (∫ e in cell g r, |1 - (z : ℝ)⁻¹ * armProb true e| ∂H) +
        ∫ e in cell g r, |1 - (1 - (z : ℝ))⁻¹ * armProb false e| ∂H := by
  have hz0 : 0 < (z : ℝ) := hOverlap.1.trans_le z.property.1
  have hz1 : (z : ℝ) < 1 := z.property.2.trans_lt (by linarith [hOverlap.1])
  have hε1 : 0 < 1 - ε := by linarith [hOverlap.1, hOverlap.2]
  have hzCenter : (z : ℝ)⁻¹ ∈ Icc ((1 - ε)⁻¹) ε⁻¹ :=
    ⟨(inv_le_inv₀ hε1 hz0).mpr z.property.2,
      (inv_le_inv₀ hz0 hOverlap.1).mpr z.property.1⟩
  have hcontrolLower : ε ≤ 1 - (z : ℝ) := by linarith [z.property.2]
  have hcontrolUpper : 1 - (z : ℝ) ≤ 1 - ε := by linarith [z.property.1]
  have hcontrolCenter : (1 - (z : ℝ))⁻¹ ∈ Icc ((1 - ε)⁻¹) ε⁻¹ :=
    ⟨(inv_le_inv₀ hε1 (by linarith)).mpr hcontrolUpper,
      (inv_le_inv₀ (by linarith) hOverlap.1).mpr hcontrolLower⟩
  exact add_le_add
    (cellAbsoluteDeviation_le_center H g true r (z : ℝ)⁻¹ hzCenter)
    (cellAbsoluteDeviation_le_center H g false r
      (1 - (z : ℝ))⁻¹ hcontrolCenter)

/-- Given [the stated mathematical inputs and assumptions](hyp:x,z,hz0,hz1), this result [establishes the stated mathematical conclusion](goal). -/
lemma sum_arm_reciprocalDeviation_eq {x z : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1) :
    |1 - z⁻¹ * x| + |1 - (1 - z)⁻¹ * (1 - x)| =
      (z * (1 - z))⁻¹ * |x - z| := by
  have h1z : 0 < 1 - z := by linarith
  have hzInv : 0 ≤ z⁻¹ := inv_nonneg.mpr hz0.le
  have h1zInv : 0 ≤ (1 - z)⁻¹ := inv_nonneg.mpr h1z.le
  have hfirst : |1 - z⁻¹ * x| = z⁻¹ * |x - z| := by
    calc
      |1 - z⁻¹ * x| = |z⁻¹ * (z - x)| := by
        congr 1
        field_simp
      _ = |z⁻¹| * |z - x| := abs_mul _ _
      _ = z⁻¹ * |x - z| := by rw [abs_of_nonneg hzInv, abs_sub_comm]
  have hsecond : |1 - (1 - z)⁻¹ * (1 - x)| =
      (1 - z)⁻¹ * |x - z| := by
    calc
      |1 - (1 - z)⁻¹ * (1 - x)| =
          |(1 - z)⁻¹ * (x - z)| := by
        congr 1
        field_simp
        ring
      _ = |(1 - z)⁻¹| * |x - z| := abs_mul _ _
      _ = (1 - z)⁻¹ * |x - z| := by rw [abs_of_nonneg h1zInv]
  rw [hfirst, hsecond, ← add_mul]
  congr 1
  field_simp
  ring

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,z,hOverlap,hz), this result [establishes the stated mathematical conclusion](goal). -/
lemma sum_arm_reciprocalCoefficient_le {ε z : ℝ}
    (hOverlap : Overlap ε) (hz : z ∈ Icc ε (1 - ε)) :
    (z * (1 - z))⁻¹ ≤ (ε * (1 - ε))⁻¹ := by
  have hε1 : 0 < 1 - ε := by linarith [hOverlap.1, hOverlap.2]
  have hz0 : 0 < z := hOverlap.1.trans_le hz.1
  have hz1 : z < 1 := hz.2.trans_lt (by linarith [hOverlap.1])
  have hprod : ε * (1 - ε) ≤ z * (1 - z) := by
    have hnonneg : 0 ≤ (z - ε) * (1 - ε - z) :=
      mul_nonneg (sub_nonneg.mpr hz.1) (sub_nonneg.mpr hz.2)
    nlinarith
  exact (inv_le_inv₀ (mul_pos hz0 (by linarith))
    (mul_pos hOverlap.1 hε1)).mpr hprod

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,x,z,hOverlap,hz), this result [establishes the stated mathematical conclusion](goal). -/
lemma sum_arm_reciprocalDeviation_le {ε x z : ℝ}
    (hOverlap : Overlap ε) (hz : z ∈ Icc ε (1 - ε)) :
    |1 - z⁻¹ * x| + |1 - (1 - z)⁻¹ * (1 - x)| ≤
      (ε * (1 - ε))⁻¹ * |x - z| := by
  rw [sum_arm_reciprocalDeviation_eq
    (hOverlap.1.trans_le hz.1) (hz.2.trans_lt (by linarith [hOverlap.1]))]
  exact mul_le_mul_of_nonneg_right
    (sum_arm_reciprocalCoefficient_le hOverlap hz) (abs_nonneg _)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hg,hOverlap,r,z), this result [establishes the stated mathematical conclusion](goal). -/
lemma sum_cellAbsoluteDeviation_le_centeredScoreIntegral
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace J) (hg : Measurable g)
    (hOverlap : Overlap ε) (r : LabelSpace J) (z : ScoreSpace ε) :
    cellAbsoluteDeviation H g true r + cellAbsoluteDeviation H g false r ≤
      (ε * (1 - ε))⁻¹ *
        ∫ e in cell g r, |(e : ℝ) - (z : ℝ)| ∂H := by
  have hcell : MeasurableSet (cell g r) :=
    measurableSet_eq_fun hg measurable_const
  have hpBounds (a : ArmSpace) (e : ScoreSpace ε) :
      0 ≤ armProb a e ∧ armProb a e ≤ 1 := by
    rcases e.property with ⟨he0, he1⟩
    have he0' : 0 ≤ (e : ℝ) := hOverlap.1.le.trans he0
    have he1' : (e : ℝ) ≤ 1 := he1.trans (by linarith [hOverlap.1])
    cases a
    · simp only [armProb, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by linarith, by linarith⟩
    · simp only [armProb, ↓reduceIte]
      exact ⟨he0', he1'⟩
  have hcandidateInt (a : ArmSpace) (c : ℝ) :
      IntegrableOn (fun e : ScoreSpace ε => |1 - c * armProb a e|)
        (cell g r) H := by
    apply Integrable.of_bound (by
      cases a <;> simp [armProb] <;> fun_prop) (1 + |c|)
    filter_upwards [] with e
    calc
      ‖|1 - c * armProb a e|‖ = |1 - c * armProb a e| := by simp
      _ ≤ |1| + |c * armProb a e| := abs_sub _ _
      _ ≤ 1 + |c| := by
        rw [abs_one, abs_mul]
        have hmul := mul_le_of_le_one_right (abs_nonneg c)
          (abs_le.mpr ⟨by linarith [(hpBounds a e).1], (hpBounds a e).2⟩)
        linarith
  have hscoreInt : IntegrableOn
      (fun e : ScoreSpace ε => |(e : ℝ) - (z : ℝ)|) (cell g r) H := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with e
    have he := e.property
    have hz := z.property
    have hwidth : 1 - 2 * ε < 1 := by linarith [hOverlap.1]
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_le.mpr
      ⟨by linarith [he.1, he.2, hz.1, hz.2],
        by linarith [he.1, he.2, hz.1, hz.2]⟩
  have hrightInt : IntegrableOn
      (fun e : ScoreSpace ε =>
        (ε * (1 - ε))⁻¹ * |(e : ℝ) - (z : ℝ)|) (cell g r) H :=
    hscoreInt.const_mul _
  calc
    cellAbsoluteDeviation H g true r + cellAbsoluteDeviation H g false r ≤
        (∫ e in cell g r, |1 - (z : ℝ)⁻¹ * armProb true e| ∂H) +
          ∫ e in cell g r,
            |1 - (1 - (z : ℝ))⁻¹ * armProb false e| ∂H :=
      sum_cellAbsoluteDeviation_le_commonCenterCandidates H g hOverlap r z
    _ = ∫ e in cell g r,
        (|1 - (z : ℝ)⁻¹ * armProb true e| +
          |1 - (1 - (z : ℝ))⁻¹ * armProb false e|) ∂H := by
      rw [integral_add (hcandidateInt true (z : ℝ)⁻¹)
        (hcandidateInt false (1 - (z : ℝ))⁻¹)]
    _ ≤ ∫ e in cell g r,
        (ε * (1 - ε))⁻¹ * |(e : ℝ) - (z : ℝ)| ∂H := by
      apply integral_mono
        ((hcandidateInt true (z : ℝ)⁻¹).add
          (hcandidateInt false (1 - (z : ℝ))⁻¹)) hrightInt
      intro e
      simpa [armProb] using sum_arm_reciprocalDeviation_le
        hOverlap z.property (x := (e : ℝ))
    _ = (ε * (1 - ε))⁻¹ *
        ∫ e in cell g r, |(e : ℝ) - (z : ℝ)| ∂H := by
      rw [integral_const_mul]

end
end CausalSmith.PartialID.UnlinkedPropensityAte
