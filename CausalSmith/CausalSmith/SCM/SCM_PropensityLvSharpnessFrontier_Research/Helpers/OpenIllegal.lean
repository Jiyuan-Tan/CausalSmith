import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.BinaryWitness
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.CapBridge
import Causalean.Mathlib.Probability.BernoulliMeasure

/-! # Analytic helpers for open binary illegal regions -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set
open Causalean.Mathlib.Probability

/-- The elementary two-cell expression for binary `f`-divergence. -/
-- @node: binaryDiv
noncomputable def binaryDiv (f : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  z.2 * f (z.1 / z.2) + (1 - z.2) * f ((1 - z.1) / (1 - z.2))

/-- A nonaffine normalized convex generator is strictly below its endpoint
chord at one fixed interior point.  For the specified model objects, [the stated conditions](hyp:hc,hf,hna,hf1), [the stated mathematical relationship holds](goal).
-/
-- @node: chord_strict_at_half_of_nonaffine
lemma chord_strict_at_half_of_nonaffine (f : ℝ → ℝ) (c : ℝ)
    (hc : 1 < c) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (hna : ¬ ∃ b : ℝ, ∀ t ∈ Set.Icc 0 c, f t = b * (t - 1))
    (hf1 : f 1 = 0) :
    f (1 / 2) < (1 - (1 / 2) / c) * f 0 + ((1 / 2) / c) * f c := by
  let ell : ℝ → ℝ := fun t => (1 - t / c) * f 0 + (t / c) * f c
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hhalf : (1 / 2 : ℝ) ∈ Set.Icc 0 c := by
    constructor <;> norm_num <;> linarith
  have hchord (t : ℝ) (ht : t ∈ Set.Icc 0 c) : f t ≤ ell t := by
    have h := hf.2 (show 0 ∈ Set.Ici (0 : ℝ) by simp)
      (show c ∈ Set.Ici (0 : ℝ) by exact hc0.le)
      (show 0 ≤ 1 - t / c by rw [sub_nonneg, div_le_one hc0]; exact ht.2)
      (show 0 ≤ t / c by exact div_nonneg ht.1 hc0.le) (by ring)
    simpa only [ell, smul_eq_mul, mul_zero, zero_add,
      div_mul_cancel₀ t (ne_of_gt hc0)] using h
  apply lt_of_le_of_ne (hchord _ hhalf)
  intro heq
  have hall : ∀ t ∈ Set.Icc (0 : ℝ) c, f t = ell t := by
    intro t ht
    apply le_antisymm (hchord t ht)
    by_cases htx : t ≤ (1 / 2 : ℝ)
    · have hden : 0 < c - t :=
        sub_pos.mpr (lt_of_le_of_lt htx (by norm_num; linarith))
      let A : ℝ := (c - 1 / 2) / (c - t)
      let B : ℝ := (1 / 2 - t) / (c - t)
      have hA : 0 ≤ A := by
        dsimp [A]
        exact div_nonneg (by linarith) hden.le
      have hB : 0 ≤ B := by
        dsimp [B]
        exact div_nonneg (by linarith) hden.le
      have hsum : A + B = 1 := by
        dsimp [A, B]
        field_simp [ne_of_gt hden]
        ring
      have hcv := hf.2 (show t ∈ Set.Ici (0 : ℝ) by exact ht.1)
        (show c ∈ Set.Ici (0 : ℝ) by exact hc0.le) hA hB hsum
      have hcomb : A • t + B • c = (1 / 2 : ℝ) := by
        dsimp [A, B]
        field_simp [ne_of_gt hden]
        ring
      rw [hcomb, heq] at hcv
      have hct := hchord t ht
      dsimp [ell] at hcv hct ⊢
      dsimp [A, B] at hcv
      field_simp [ne_of_gt hden] at hcv ⊢
      nlinarith
    · have hxt : (1 / 2 : ℝ) ≤ t := le_of_not_ge htx
      have htpos : 0 < t := by linarith
      let A : ℝ := 1 - (1 / 2) / t
      let B : ℝ := (1 / 2) / t
      have hA : 0 ≤ A := by rw [sub_nonneg, div_le_one htpos]; exact hxt
      have hB : 0 ≤ B := by exact div_nonneg (by norm_num) htpos.le
      have hsum : A + B = 1 := by dsimp [A, B]; ring
      have hcv := hf.2 (show 0 ∈ Set.Ici (0 : ℝ) by simp)
        (show t ∈ Set.Ici (0 : ℝ) by exact ht.1) hA hB hsum
      have hcomb : A • (0 : ℝ) + B • t = (1 / 2 : ℝ) := by
        dsimp [A, B]
        field_simp [ne_of_gt htpos]
        ring
      rw [hcomb, heq] at hcv
      have hct := hchord t ht
      dsimp [ell] at hcv hct ⊢
      dsimp [A, B] at hcv
      field_simp [ne_of_gt htpos] at hcv ⊢
      nlinarith
  apply hna
  let b : ℝ := (f c - f 0) / c
  have hone : ell 1 = 0 := by
    rw [← hf1]
    exact (hall 1 ⟨zero_le_one, hc.le⟩).symm
  have hfc : f c = b * (c - 1) := by
    dsimp [ell, b] at hone ⊢
    field_simp [ne_of_gt hc0] at hone ⊢
    nlinarith
  have hf0 : f 0 = b * (0 - 1) := by
    dsimp [ell, b] at hone ⊢
    field_simp [ne_of_gt hc0] at hone ⊢
    nlinarith
  refine ⟨b, ?_⟩
  intro t ht
  rw [hall t ht]
  dsimp [ell]
  rw [hf0, hfc]
  field_simp [ne_of_gt hc0]
  ring

/-- The binary divergence expression is continuous throughout the open
probability square for every admissible generator.  For the specified model objects, [the stated conditions](hyp:hf), [the stated mathematical relationship holds](goal).
-/
-- @node: continuousOn_binaryDiv
lemma continuousOn_binaryDiv (f : ℝ → ℝ) (hf : AdmissibleGenerator f) :
    ContinuousOn (binaryDiv f) (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) := by
  intro z hz
  have hr1 : 0 < z.1 / z.2 := div_pos hz.1.1 hz.2.1
  have hr0 : 0 < (1 - z.1) / (1 - z.2) :=
    div_pos (sub_pos.mpr hz.1.2) (sub_pos.mpr hz.2.2)
  have hf1 : ContinuousAt f (z.1 / z.2) :=
    hf.1.continuousAt (Ici_mem_nhds hr1)
  have hf0 : ContinuousAt f ((1 - z.1) / (1 - z.2)) :=
    hf.1.continuousAt (Ici_mem_nhds hr0)
  have hratio1 : ContinuousAt (fun w : ℝ × ℝ => w.1 / w.2) z :=
    continuousAt_fst.div continuousAt_snd (ne_of_gt hz.2.1)
  have hratio0 : ContinuousAt
      (fun w : ℝ × ℝ => (1 - w.1) / (1 - w.2)) z :=
    (continuousAt_const.sub continuousAt_fst).div
      (continuousAt_const.sub continuousAt_snd) (sub_ne_zero.mpr hz.2.2.ne')
  have hcomp1 : ContinuousAt (fun w : ℝ × ℝ => f (w.1 / w.2)) z := by
    convert (ContinuousAt.comp (f := fun w : ℝ × ℝ => w.1 / w.2)
      (g := f) hf1 hratio1) using 1 <;> rfl
  have hcomp0 : ContinuousAt
      (fun w : ℝ × ℝ => f ((1 - w.1) / (1 - w.2))) z := by
    convert (ContinuousAt.comp
      (f := fun w : ℝ × ℝ => (1 - w.1) / (1 - w.2))
      (g := f) hf0 hratio0) using 1 <;> rfl
  exact ((continuousAt_snd.mul hcomp1).add
    ((continuousAt_const.sub continuousAt_snd).mul
      hcomp0)).continuousWithinAt

/-- On two full-support Bernoulli laws, the extended divergence is the usual
two-cell weighted sum.  For the specified model objects, [the stated conditions](hyp:hp,hq), [the stated mathematical relationship holds](goal).
-/
-- @node: binaryLaw_fDiv_eq
lemma binaryLaw_fDiv_eq (f : ℝ → ℝ) (p q : ℝ)
    (hp : p ∈ Set.Ioo 0 1) (hq : q ∈ Set.Ioo 0 1) :
    fDiv f (binaryLaw p) (binaryLaw q) =
      ((binaryDiv f (p, q) : ℝ) : EReal) := by
  have hbp : binaryLaw p = bernoulliBool p := by
    simp [binaryLaw, bernoulliBool, add_comm]
  have hbq : binaryLaw q = bernoulliBool q := by
    simp [binaryLaw, bernoulliBool, add_comm]
  rw [hbp, hbq]
  let g : Bool → ENNReal := fun z =>
    if z then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q))
  have hg : Measurable g := measurable_of_finite g
  have hq0 : 0 < q := hq.1
  have hq1 : q < 1 := hq.2
  have hp0 : 0 ≤ p := hp.1.le
  have hp1 : p ≤ 1 := hp.2.le
  have hwd : bernoulliBool p = (bernoulliBool q).withDensity g := by
    ext s hs
    rw [withDensity_apply _ hs, ← lintegral_indicator hs g]
    unfold bernoulliBool
    dsimp [g]
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    simp only [lintegral_dirac]
    have hq_ne0 : ENNReal.ofReal q ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hq0)
    have h1q_ne0 : ENNReal.ofReal (1 - q) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hq1))
    by_cases ht : true ∈ s <;> by_cases hf : false ∈ s <;>
      simp [ht, hf, ENNReal.ofReal_div_of_pos hq0,
        ENNReal.ofReal_div_of_pos (sub_pos.mpr hq1),
        ENNReal.mul_div_cancel hq_ne0 ENNReal.ofReal_ne_top,
        ENNReal.mul_div_cancel h1q_ne0 ENNReal.ofReal_ne_top]
  let _ : IsProbabilityMeasure (bernoulliBool q) :=
    bernoulliBool_isProbabilityMeasure hq.1.le hq.2.le
  have hrn : (bernoulliBool p).rnDeriv (bernoulliBool q) =ᵐ[bernoulliBool q] g := by
    rw [hwd]
    exact Measure.rnDeriv_withDensity (bernoulliBool q) hg
  have hint : Integrable
      (fun x => f (((bernoulliBool p).rnDeriv (bernoulliBool q) x).toReal))
      (bernoulliBool q) := Integrable.of_finite
  rw [fDiv, if_pos hint]
  trans ((∫ x, f ((g x).toReal) ∂bernoulliBool q : ℝ) : EReal)
  · congr 1
    exact integral_congr_ae <| by
      filter_upwards [hrn] with x hx
      rw [hx]
  · rw [bernoulliBool_integral hq.1.le hq.2.le]
    dsimp [g]
    rw [ENNReal.toReal_ofReal (div_nonneg hp0 hq.1.le),
      ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr hp1)
        (sub_nonneg.mpr hq.2.le))]
    rfl

/-- A full-support binary pair below the propensity cap is illegal for both
mixture classes; a divergence bound places it in both corresponding balls.  For the specified model objects, [the stated conditions](hyp:hPos,hf,hp,hq,hlower,hdiv), [the stated mathematical relationship holds](goal).
-/
-- @node: binaryLaw_common_illegal_of_lt
lemma binaryLaw_common_illegal_of_lt (f : ℝ → ℝ) (e p q : ℝ)
    (hPos : StrictPositivity e) (hf : AdmissibleGenerator f)
    (hp : p ∈ Set.Ioo 0 1) (hq : q ∈ Set.Ioo 0 1)
    (hlower : q < e * p)
    (hdiv : fDiv f (binaryLaw p) (binaryLaw q) ≤ (divRadius f e : EReal)) :
    binaryLaw q ∈ jkBallOneSidedSet f e (binaryLaw p) \
        mixtureClassOneSidedSet e (binaryLaw p) ∧
      binaryLaw q ∈ jkBallSet f e (binaryLaw p) \
        mixtureClassSet e (binaryLaw p) := by
  let hpP : IsProbabilityMeasure (binaryLaw p) :=
    binaryLaw_isProbabilityMeasure p ⟨hp.1.le, hp.2.le⟩
  let hqP : IsProbabilityMeasure (binaryLaw q) :=
    binaryLaw_isProbabilityMeasure q ⟨hq.1.le, hq.2.le⟩
  have hac := binaryLaw_mutuallyAC p q hp hq
  have hnotOne : binaryLaw q ∉ mixtureClassOneSidedSet e (binaryLaw p) := by
    intro hm
    let _ : IsProbabilityMeasure (binaryLaw p) := hpP
    have hle := ((mixture_oneSided_iff_measure_le e (binaryLaw p)
      (binaryLaw q) hPos).1 hm).2 {true}
    have hreal : e * p ≤ q := by
      have : ENNReal.ofReal (e * p) ≤ ENNReal.ofReal q := by
        simpa [Measure.smul_apply, binaryLaw_true p ⟨hp.1.le, hp.2.le⟩,
          binaryLaw_true q ⟨hq.1.le, hq.2.le⟩,
          ENNReal.ofReal_mul hPos.1.le] using hle
      exact (ENNReal.ofReal_le_ofReal_iff hq.1.le).mp this
    exact (not_le_of_gt hlower) hreal
  have hone : binaryLaw q ∈ jkBallOneSidedSet f e (binaryLaw p) :=
    { positivity := hPos
      admissible := hf
      observed_probability := hpP
      candidate_probability := hqP
      forward_support := hac.1
      divergence_le := hdiv }
  have hmutual : binaryLaw q ∈ jkBallSet f e (binaryLaw p) :=
    { positivity := hPos
      admissible := hf
      observed_probability := hpP
      candidate_probability := hqP
      mutual_ac := ⟨hac.2, hac.1⟩
      divergence_le := hdiv }
  refine ⟨⟨hone, hnotOne⟩, hmutual, ?_⟩
  intro hm
  exact hnotOne ((mixture_reverse_support e (binaryLaw p)
    (binaryLaw q) hPos).1 hm).1

end CausalSmith.SCM.PropensityLvSharpnessFrontier
