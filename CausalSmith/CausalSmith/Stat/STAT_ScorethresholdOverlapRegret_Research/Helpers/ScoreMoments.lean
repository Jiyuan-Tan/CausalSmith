module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.WelfareIdentity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Score-threshold overlap regret — welfare and regularization

The concrete potential-outcome law uses Mathlib measures.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

-- @node: zScore_abs_le
/-- The deleted score is uniformly bounded when the logger and outcome are in range. -/
lemma zScore_abs_le (a : ℝ) (e : ℝ → ℝ) (o : Observation)
    (ha : 0 < a ∧ a ≤ 1/4) (he : 0 < e o.X ∧ e o.X < 1)
    (hY : o.Y ∈ Set.Icc (-1:ℝ) 1) :
    |zScore a e o| ≤ 2/a := by
  have hp : 0 < min (e o.X) (1-e o.X) := lt_min he.1 (by linarith [he.2])
  have ha1 : a ≤ 1 := by linarith [ha.2]
  have hg : 0 ≤ offsetG a e o.X ∧ offsetG a e o.X ≤ 1 := by
    unfold offsetG
    constructor
    · exact le_min (by norm_num) (div_nonneg ha.1.le hp.le)
    · exact min_le_left _ _
  have hgamma : |gammaScore a e o| ≤ 1/a := by
    unfold gammaScore
    split_ifs with hpa hA
    · have hae : a ≤ e o.X := le_trans hpa (min_le_left _ _)
      have hYabs : |o.Y| ≤ 1 := abs_le.mpr hY
      rw [abs_div, abs_of_pos he.1]
      exact (div_le_div_of_nonneg_right hYabs he.1.le).trans
        (div_le_div_of_nonneg_left (by norm_num) ha.1 hae)
    · have hae : a ≤ 1-e o.X := le_trans hpa (min_le_right _ _)
      have hYabs : |o.Y| ≤ 1 := abs_le.mpr hY
      rw [abs_neg, abs_div, abs_of_pos (by linarith [he.2] : 0 < 1-e o.X)]
      exact (div_le_div_of_nonneg_right hYabs (by linarith [he.2] : 0 ≤ 1-e o.X)).trans
        (div_le_div_of_nonneg_left (by norm_num) ha.1 hae)
    · simp [le_of_lt ha.1]
  unfold zScore
  calc
    |gammaScore a e o + offsetG a e o.X| ≤
        |gammaScore a e o| + |offsetG a e o.X| := abs_add_le _ _
    _ ≤ 1/a + 1 := by rw [abs_of_nonneg hg.1]; linarith [hgamma, hg.2]
    _ ≤ 2/a := by
      have h : 1 ≤ 1/a := (one_le_div ha.1).2 ha1
      calc
        1/a + 1 ≤ 1/a + 1/a := add_le_add_right h _
        _ = 2/a := by ring

-- @node: zScore_fourth_le_second
/-- The uniform score bound reduces its fourth moment to its second moment. -/
lemma zScore_fourth_le_second (a : ℝ) (e : ℝ → ℝ) (o : Observation)
    (ha : 0 < a ∧ a ≤ 1/4) (he : 0 < e o.X ∧ e o.X < 1)
    (hY : o.Y ∈ Set.Icc (-1:ℝ) 1) :
    (zScore a e o)^4 ≤ (4/a^2) * (zScore a e o)^2 := by
  have habs := zScore_abs_le a e o ha he hY
  have hsq : (zScore a e o)^2 ≤ (2/a)^2 := by
    have hlo := (abs_le.mp habs).1
    have hhi := (abs_le.mp habs).2
    have hnonneg : 0 ≤ 2/a := div_nonneg (by norm_num) ha.1.le
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg (zScore a e o))
  calc
    (zScore a e o)^4 = (zScore a e o)^2 * (zScore a e o)^2 := by ring
    _ ≤ (2/a)^2 * (zScore a e o)^2 := hmul
    _ = (4/a^2) * (zScore a e o)^2 := by ring

-- @node: zScore_abs_ae
/-- The observable score bound holds under the row-law support conditions. -/
lemma zScore_abs_ae (P : RowLaw) (a : ℝ)
    (ha : 0 < a ∧ a ≤ 1/4) (hwf : WellFormed P)
    (hloggerSpace : ∀ x ∈ Set.Icc (0:ℝ) 1, P.logger x ∈ Set.Ioo (0:ℝ) 1) :
    ∀ᵐ o ∂P.obsLaw, |zScore a P.logger o| ≤ 2/a := by
  have hXY : ∀ᵐ o ∂P.obsLaw,
      o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1 := by
    have hX : ∀ᵐ o ∂P.full, o.X ∈ Set.Icc (0:ℝ) 1 :=
      ae_iff.mpr hwf.2.1
    have hY : ∀ᵐ o ∂P.full, o.Y ∈ Set.Icc (-1:ℝ) 1 :=
      ae_iff.mpr hwf.2.2.1
    have hmap : Measurable (fun o : FullRow => (⟨o.X,o.A,o.Y⟩ : Observation)) := by
      apply measurable_comap_iff.mpr
      have hfull : Measurable (fun o : FullRow => (o.X,o.A,o.Y,o.Y0,o.Y1)) :=
        comap_measurable _
      have hproj : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ => (t.1,t.2.1,t.2.2.1)) := by
        fun_prop
      exact hproj.comp hfull
    have hset : MeasurableSet
        {o : Observation | o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1} := by
      apply (MeasurableSpace.measurableSet_comap).2
      refine ⟨{t : ℝ × Bool × ℝ | t.1 ∈ Set.Icc (0:ℝ) 1 ∧
        t.2.2 ∈ Set.Icc (-1:ℝ) 1}, ?_, rfl⟩
      measurability
    apply (ae_map_iff hmap.aemeasurable hset).2
    filter_upwards [hX, hY] with o hxo hyo
    exact ⟨hxo, hyo⟩
  filter_upwards [hXY] with o ho
  have hlogger : 0 < P.logger o.X ∧ P.logger o.X < 1 :=
    hloggerSpace o.X ho.1
  exact zScore_abs_le a P.logger o ha hlogger ho.2

private lemma score_pointwise_retained_two_sq (a e : ℝ)
    (ha : 0 < a ∧ a ≤ 1/4) (he : 0 < e ∧ e < 1)
    (hret : a ≤ min e (1-e)) :
    2 * (e * (1/e^2) + (1-e) * (1/(1-e)^2) +
      (a/min e (1-e))^2) ≤ 6*(a/min e (1-e))/a := by
  let m := min e (1-e)
  let g := a/m
  have hm : 0 < m := lt_min he.1 (by linarith [he.2])
  have hne : 0 < 1-e := by linarith [he.2]
  have hme : m ≤ e := min_le_left _ _
  have hmo : m ≤ 1-e := min_le_right _ _
  have ht1 : 1/e ≤ 1/m := by
    apply (div_le_div_iff₀ he.1 hm).2
    simpa using hme
  have ht0 : 1/(1-e) ≤ 1/m := by
    apply (div_le_div_iff₀ hne hm).2
    simpa using hmo
  have hg0 : 0 ≤ g := div_nonneg ha.1.le hm.le
  have hg1 : g ≤ 1 := (div_le_one hm).2 (by exact_mod_cast hret)
  have hgm : g ≤ 1/m := by
    dsimp [g]
    exact div_le_div_of_nonneg_right (by linarith [ha.2] : a ≤ 1) hm.le
  have hgsq : g^2 ≤ 1/m := by
    have hgsq1 : g^2 ≤ g := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hg1)]
    exact le_trans hgsq1 hgm
  have hident : e * (1/e^2) + (1-e) * (1/(1-e)^2) + g^2 =
      1/e + 1/(1-e) + g^2 := by
    field_simp [ne_of_gt he.1, ne_of_gt hne]
  have hmain : 2 * (e * (1/e^2) + (1-e) * (1/(1-e)^2) + g^2) ≤ 6/m := by
    rw [hident]
    calc
      2 * (1/e + 1/(1-e) + g^2) ≤ 2 * (3*(1/m)) := by
        linarith only [ht1, ht0, hgsq]
      _ = 6/m := by ring
  change 2 * (e * (1/e^2) + (1-e) * (1/(1-e)^2) + g^2) ≤ 6*g/a
  convert hmain using 1
  dsimp [g]
  field_simp [ne_of_gt ha.1, ne_of_gt hm]

private lemma score_pointwise_deleted_two_sq (a : ℝ)
    (ha : 0 < a ∧ a ≤ 1/4) :
    2 * ((0:ℝ) + 0 + 1^2) ≤ 6 * 1 / a := by
  have ha3 : a ≤ 3 := by linarith [ha.2]
  norm_num
  exact (le_div_iff₀ ha.1).2 (by nlinarith [ha3])

/-- Tested second/fourth moment bounds for the regularized observable score. -/
lemma zScore_moment_bounds (P : RowLaw) (a : ℝ)
    (ha : 0 < a ∧ a ≤ 1/4) (hwf : WellFormed P)
    (hbounded : BoundedPotentials P) (hpositive : Positivity P P.logger)
    (hloggerSpace : ∀ x ∈ Set.Icc (0:ℝ) 1, P.logger x ∈ Set.Ioo (0:ℝ) 1) :
    (∀ᵐ o ∂P.obsLaw, |zScore a P.logger o| ≤ 2/a) ∧
    (∀ B : Set ℝ, MeasurableSet B →
      ∫ o in {o | o.X ∈ B}, (zScore a P.logger o)^2 ∂P.obsLaw ≤
        ∫ x in B, 6*offsetG a P.logger x/a ∂P.PX) ∧
    (∀ B : Set ℝ, MeasurableSet B →
      ∫ o in {o | o.X ∈ B}, (zScore a P.logger o)^4 ∂P.obsLaw ≤
        ∫ x in B, 24*offsetG a P.logger x/a^3 ∂P.PX) := by
  have hsecond : ∀ B : Set ℝ, MeasurableSet B →
      Integrable (fun o => (zScore a P.logger o)^2)
        (P.obsLaw.restrict {o | o.X ∈ B}) ∧
      ∫ o in {o | o.X ∈ B}, (zScore a P.logger o)^2 ∂P.obsLaw ≤
        ∫ x in B, 6*offsetG a P.logger x/a ∂P.PX := by
    letI : IsProbabilityMeasure P.full := hwf.1
    have hψ : Measurable (fun o : FullRow => (⟨o.X,o.A,o.Y⟩ : Observation)) := by
      apply measurable_comap_iff.mpr
      have hfull : Measurable (fun o : FullRow => (o.X,o.A,o.Y,o.Y0,o.Y1)) :=
        comap_measurable _
      exact (by fun_prop : Measurable
        (fun t : ℝ × Bool × ℝ × ℝ × ℝ => (t.1,t.2.1,t.2.2.1))).comp hfull
    letI : IsFiniteMeasure P.obsLaw := ⟨by
      rw [RowLaw.obsLaw, Measure.map_apply hψ MeasurableSet.univ]
      simp⟩
    have hlog := logger_aemeasurable P hwf
    let elog : ℝ → ℝ := hlog.mk P.logger
    have helog : Measurable elog := hlog.measurable_mk
    have helog_eq : P.logger =ᵐ[P.PX] elog := hlog.ae_eq_mk
    let retained : ℝ → Prop := fun x => a ≤ min (elog x) (1-elog x)
    have hretained : MeasurableSet {x | retained x} := by
      dsimp [retained]
      exact measurableSet_le measurable_const (helog.min (measurable_const.sub helog))
    let f1 : ℝ → ℝ := fun x => if retained x then 1/(elog x)^2 else 0
    let f0 : ℝ → ℝ := fun x => if retained x then 1/(1-elog x)^2 else 0
    have hf1 : AEStronglyMeasurable f1 P.PX := by
      exact (Measurable.ite hretained
        (show Measurable (fun x => 1 / elog x ^ 2) by fun_prop)
        measurable_const).aestronglyMeasurable
    have hf0 : AEStronglyMeasurable f0 P.PX := by
      exact (Measurable.ite hretained
        (show Measurable (fun x => 1 / (1 - elog x) ^ 2) by fun_prop)
        measurable_const).aestronglyMeasurable
    have hg : AEStronglyMeasurable (fun x => offsetG a P.logger x) P.PX := by
      apply AEMeasurable.aestronglyMeasurable
      unfold offsetG
      fun_prop
    have hXobs : Measurable (fun o : Observation => o.X) := by
      exact (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.1)).comp
        (comap_measurable _)
    have hPXobs : Measure.map (fun o : Observation => o.X) P.obsLaw = P.PX := by
      rw [RowLaw.obsLaw, RowLaw.PX, Measure.map_map hXobs hψ]
      rfl
    have hXobs_qmp : Measure.QuasiMeasurePreserving (fun o : Observation => o.X)
        P.obsLaw P.PX := ⟨hXobs, hPXobs ▸ Measure.AbsolutelyContinuous.rfl⟩
    have helogobs : ∀ᵐ o ∂P.obsLaw, P.logger o.X = elog o.X :=
      hXobs_qmp.ae helog_eq
    have hzmeas : AEStronglyMeasurable (fun o => zScore a P.logger o) P.obsLaw := by
      let z' : Observation → ℝ := fun o => zScore a elog o
      have hz' : Measurable z' := by
        have hA : Measurable (fun o : Observation => o.A) :=
          (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.2.1)).comp
            (comap_measurable _)
        have hY : Measurable (fun o : Observation => o.Y) :=
          (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.2.2)).comp
            (comap_measurable _)
        have hr : MeasurableSet {o : Observation | retained o.X} :=
          hretained.preimage hXobs
        have hAt : MeasurableSet {o : Observation | o.A = true} :=
          hA (measurableSet_singleton true)
        have hγ : Measurable (fun o : Observation => gammaScore a elog o) := by
          unfold gammaScore
          exact Measurable.ite hr
            (Measurable.ite hAt (hY.div (helog.comp hXobs))
              (measurable_neg.comp (hY.div (measurable_const.sub (helog.comp hXobs)))))
            measurable_const
        have hg' : Measurable (fun o : Observation => offsetG a elog o.X) := by
          unfold offsetG
          fun_prop
        exact hγ.add hg'
      apply hz'.aestronglyMeasurable.congr
      filter_upwards [helogobs] with o ho
      simp only [z', zScore, gammaScore, offsetG]
      rw [ho]
    intro B hB
    have hzint : Integrable (fun o => (zScore a P.logger o)^2) P.obsLaw := by
      refine Integrable.mono' (integrable_const ((2/a)^2 : ℝ)) (hzmeas.pow 2) ?_
      filter_upwards [zScore_abs_ae P a ha hwf hloggerSpace] with o ho
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rcases abs_le.mp ho with ⟨hlo, hhi⟩
      have hpa : 0 < 2/a := div_pos (by norm_num) ha.1
      nlinarith
    refine ⟨hzint.integrableOn, ?_⟩
    let F : FullRow → ℝ := fun o =>
      2 * (if o.A = true then f1 o.X else 0) +
      2 * (if o.A = false then f0 o.X else 0) +
      2 * (offsetG a P.logger o.X)^2
    have hXfull : ∀ᵐ o ∂P.full, o.X ∈ Set.Icc (0 : ℝ) 1 := ae_iff.mpr hwf.2.1
    have hYfull : ∀ᵐ o ∂P.full, o.Y ∈ Set.Icc (-1 : ℝ) 1 := ae_iff.mpr hwf.2.2.1
    have hXfull_qmp : Measure.QuasiMeasurePreserving (fun o : FullRow => o.X)
        P.full P.PX := ⟨fullRow_X_measurable,
          (show Measure.map (fun o : FullRow => o.X) P.full = P.PX from rfl) ▸
            Measure.AbsolutelyContinuous.rfl⟩
    have helogfull : ∀ᵐ o ∂P.full, P.logger o.X = elog o.X :=
      hXfull_qmp.ae helog_eq
    have hpoint : ∀ᵐ o ∂P.full,
        (zScore a P.logger (⟨o.X,o.A,o.Y⟩ : Observation))^2 ≤ F o := by
      filter_upwards [hXfull, hYfull, helogfull] with o hx hy hel
      have he := hloggerSpace o.X hx
      have hp : 0 < min (P.logger o.X) (1-P.logger o.X) :=
        lt_min he.1 (by linarith [he.2])
      have hg0 : 0 ≤ offsetG a P.logger o.X := by
        unfold offsetG
        exact le_min (by norm_num) (div_nonneg ha.1.le hp.le)
      have hsnonneg := sq_nonneg
        (gammaScore a P.logger (⟨o.X,o.A,o.Y⟩ : Observation) -
          offsetG a P.logger o.X)
      have hsquare : (gammaScore a P.logger (⟨o.X,o.A,o.Y⟩ : Observation) +
            offsetG a P.logger o.X)^2 ≤
          2 * (gammaScore a P.logger (⟨o.X,o.A,o.Y⟩ : Observation))^2 +
            2 * (offsetG a P.logger o.X)^2 := by nlinarith
      apply hsquare.trans
      unfold F
      have hy2 : o.Y^2 ≤ 1 := by
        rcases hy with ⟨hylo, hyhi⟩
        nlinarith
      unfold gammaScore f1 f0 retained
      rw [← hel]
      by_cases hr : a ≤ min (P.logger o.X) (1-P.logger o.X)
      · cases hA : o.A
        · simp [hr, hA]
          have hden : 0 ≤ (1-P.logger o.X)^2 := sq_nonneg _
          have hd := div_le_div_of_nonneg_right hy2 hden
          simpa [div_pow, one_div] using hd
        · simp [hr, hA]
          have hden : 0 ≤ (P.logger o.X)^2 := sq_nonneg _
          have hd := div_le_div_of_nonneg_right hy2 hden
          simpa [div_pow, one_div] using hd
      · cases o.A <;> simp [hr]
    have hFmeas : AEStronglyMeasurable F P.full := by
      have hf1c : AEStronglyMeasurable (fun o : FullRow => f1 o.X) P.full := by
        exact hf1.comp_quasiMeasurePreserving hXfull_qmp
      have hf0c : AEStronglyMeasurable (fun o : FullRow => f0 o.X) P.full := by
        exact hf0.comp_quasiMeasurePreserving hXfull_qmp
      have hgc : AEStronglyMeasurable
          (fun o : FullRow => offsetG a P.logger o.X) P.full :=
        hg.comp_quasiMeasurePreserving hXfull_qmp
      have hA : Measurable (fun o : FullRow => o.A) := by
        have hfull : Measurable (fun o : FullRow => (o.X,o.A,o.Y,o.Y0,o.Y1)) :=
          comap_measurable _
        exact (by fun_prop : Measurable
          (fun t : ℝ × Bool × ℝ × ℝ × ℝ => t.2.1)).comp hfull
      have hi1 : AEStronglyMeasurable
          (fun o : FullRow => if o.A = true then (1:ℝ) else 0) P.full :=
        (Measurable.ite (hA (measurableSet_singleton true)) measurable_const
          measurable_const).aestronglyMeasurable
      have hi0 : AEStronglyMeasurable
          (fun o : FullRow => if o.A = false then (1:ℝ) else 0) P.full :=
        (Measurable.ite (hA (measurableSet_singleton false)) measurable_const
          measurable_const).aestronglyMeasurable
      unfold F
      convert (((hi1.mul hf1c).const_mul 2).add ((hi0.mul hf0c).const_mul 2)).add
        ((hgc.pow 2).const_mul 2) using 1
      ext o
      cases hAo : o.A <;> simp [hAo]
    have hFint : Integrable F P.full := by
      refine Integrable.mono' (integrable_const (8 * (1/a^2) : ℝ)) hFmeas ?_
      filter_upwards [hXfull, helogfull] with o hx hel
      have he := hloggerSpace o.X hx
      have hp : 0 < min (P.logger o.X) (1-P.logger o.X) := lt_min he.1 (by linarith [he.2])
      have hf1b : 0 ≤ f1 o.X ∧ f1 o.X ≤ 1/a^2 := by
        dsimp [f1, retained]
        split_ifs with hr
        · constructor
          · positivity
          · rw [← hel]
            have hae : a ≤ P.logger o.X := (show a ≤ min (P.logger o.X)
              (1-P.logger o.X) by simpa [← hel] using hr).trans (min_le_left _ _)
            exact one_div_le_one_div_of_le (sq_pos_of_pos ha.1) (by nlinarith)
        · constructor <;> positivity
      have hf0b : 0 ≤ f0 o.X ∧ f0 o.X ≤ 1/a^2 := by
        dsimp [f0, retained]
        split_ifs with hr
        · constructor
          · positivity
          · rw [← hel]
            have hae : a ≤ 1-P.logger o.X := (show a ≤ min (P.logger o.X)
              (1-P.logger o.X) by simpa [← hel] using hr).trans (min_le_right _ _)
            exact one_div_le_one_div_of_le (sq_pos_of_pos ha.1) (by nlinarith)
        · constructor <;> positivity
      have hgb : 0 ≤ offsetG a P.logger o.X ∧ offsetG a P.logger o.X ≤ 1 := by
        unfold offsetG
        constructor
        · exact le_min (by norm_num) (div_nonneg ha.1.le hp.le)
        · exact min_le_left _ _
      have hgsq : (offsetG a P.logger o.X)^2 ≤ 1 := by nlinarith [sq_nonneg (1 - offsetG a P.logger o.X)]
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · have ha1 : a ≤ 1 := by linarith [ha.2]
        have hinv : 1 ≤ 1/a^2 := by
          have hsqa : 0 < a^2 := sq_pos_of_pos ha.1
          have hsqa1 : a^2 ≤ 1 := by nlinarith
          simpa using one_div_le_one_div_of_le hsqa hsqa1
        have hgsq' : (offsetG a P.logger o.X)^2 ≤ 1/a^2 := le_trans hgsq hinv
        cases hA : o.A <;> simp [F, hA] at * <;> linarith [hgsq']
      · cases o.A <;> simp [F] <;> positivity
    have hAm : Measurable (fun o : FullRow => o.A) := by
      have hfull : Measurable (fun o : FullRow => (o.X,o.A,o.Y,o.Y0,o.Y1)) :=
        comap_measurable _
      exact (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ => t.2.1)).comp hfull
    have hC1meas : AEStronglyMeasurable
        (fun o : FullRow => if o.A = true then f1 o.X else 0) P.full := by
      have hi : AEStronglyMeasurable (fun o : FullRow => if o.A = true then (1:ℝ) else 0) P.full :=
        (Measurable.ite (hAm (measurableSet_singleton true)) measurable_const
          measurable_const).aestronglyMeasurable
      have h := hi.mul (hf1.comp_quasiMeasurePreserving hXfull_qmp)
      convert h using 1
      ext o
      cases hA : o.A <;> simp [hA]
    have hC0meas : AEStronglyMeasurable
        (fun o : FullRow => if o.A = false then f0 o.X else 0) P.full := by
      have hi : AEStronglyMeasurable (fun o : FullRow => if o.A = false then (1:ℝ) else 0) P.full :=
        (Measurable.ite (hAm (measurableSet_singleton false)) measurable_const
          measurable_const).aestronglyMeasurable
      have h := hi.mul (hf0.comp_quasiMeasurePreserving hXfull_qmp)
      convert h using 1
      ext o
      cases hA : o.A <;> simp [hA]
    have hGmeas : AEStronglyMeasurable
        (fun o : FullRow => (offsetG a P.logger o.X)^2) P.full :=
      (hg.comp_quasiMeasurePreserving hXfull_qmp).pow 2
    have hFdom : ∀ᵐ o ∂P.full,
        ‖(if o.A = true then f1 o.X else 0)‖ ≤ F o ∧
        ‖(if o.A = false then f0 o.X else 0)‖ ≤ F o ∧
        ‖(offsetG a P.logger o.X)^2‖ ≤ F o := by
      filter_upwards [hXfull] with o hx
      have he := hloggerSpace o.X hx
      have hp : 0 < min (P.logger o.X) (1-P.logger o.X) :=
        lt_min he.1 (by linarith [he.2])
      have hg0 : 0 ≤ offsetG a P.logger o.X := by
        unfold offsetG
        exact le_min (by norm_num) (div_nonneg ha.1.le hp.le)
      have hf1n : 0 ≤ f1 o.X := by dsimp [f1]; split_ifs <;> positivity
      have hf0n : 0 ≤ f0 o.X := by dsimp [f0]; split_ifs <;> positivity
      cases hA : o.A <;>
        simp [F, hA, Real.norm_eq_abs, abs_of_nonneg hf1n, abs_of_nonneg hf0n,
          abs_of_nonneg (sq_nonneg (offsetG a P.logger o.X))] <;>
        constructor <;> try constructor
      all_goals nlinarith [sq_nonneg (offsetG a P.logger o.X)]
    have hC1int : Integrable (fun o : FullRow => if o.A = true then f1 o.X else 0) P.full :=
      Integrable.mono' hFint hC1meas (hFdom.mono fun o ho => ho.1)
    have hC0int : Integrable (fun o : FullRow => if o.A = false then f0 o.X else 0) P.full :=
      Integrable.mono' hFint hC0meas (hFdom.mono fun o ho => ho.2.1)
    have hGint : Integrable (fun o : FullRow => (offsetG a P.logger o.X)^2) P.full :=
      Integrable.mono' hFint hGmeas (hFdom.mono fun o ho => ho.2.2)
    have hmapset :
        ∫ o in {o : Observation | o.X ∈ B}, (zScore a P.logger o)^2 ∂P.obsLaw =
        ∫ o in {o : FullRow | o.X ∈ B},
          (zScore a P.logger (⟨o.X,o.A,o.Y⟩ : Observation))^2 ∂P.full := by
      change (∫ o in (fun o : Observation => o.X) ⁻¹' B,
        (zScore a P.logger o)^2 ∂P.obsLaw) =
        ∫ o in (fun o : FullRow => o.X) ⁻¹' B,
          (zScore a P.logger (⟨o.X,o.A,o.Y⟩ : Observation))^2 ∂P.full
      rw [← integral_indicator (hXobs hB),
        ← integral_indicator (fullRow_X_measurable hB), RowLaw.obsLaw]
      convert integral_map hψ.aemeasurable
        ((hzmeas.pow 2).indicator (hXobs hB)) using 1
      · rfl
      · rfl
    have hArm1 :
        ∫ o in {o : FullRow | o.X ∈ B}, (if o.A = true then f1 o.X else 0) ∂P.full =
          ∫ x in B, P.logger x * f1 x ∂P.PX := by
      have h := tested_arm_weighted P hwf hloggerSpace true (B.indicator f1)
        (hf1.indicator hB)
      change (∫ o in (fun o : FullRow => o.X) ⁻¹' B,
        (if o.A = true then f1 o.X else 0) ∂P.full) =
        (∫ x in B, P.logger x * f1 x ∂P.PX)
      rw [← integral_indicator (fullRow_X_measurable hB),
        ← integral_indicator hB]
      convert h using 1
      · congr 1
        funext o
        by_cases hx : o.X ∈ B <;> by_cases hA : o.A = true <;>
          simp [Set.indicator, hx, hA]
      · congr 1
        funext x
        by_cases hx : x ∈ B <;> simp [Set.indicator, hx]
    have hArm0 :
        ∫ o in {o : FullRow | o.X ∈ B}, (if o.A = false then f0 o.X else 0) ∂P.full =
          ∫ x in B, (1-P.logger x) * f0 x ∂P.PX := by
      have h := tested_arm_weighted P hwf hloggerSpace false (B.indicator f0)
        (hf0.indicator hB)
      change (∫ o in (fun o : FullRow => o.X) ⁻¹' B,
        (if o.A = false then f0 o.X else 0) ∂P.full) =
        (∫ x in B, (1-P.logger x) * f0 x ∂P.PX)
      rw [← integral_indicator (fullRow_X_measurable hB),
        ← integral_indicator hB]
      convert h using 1
      · congr 1
        funext o
        by_cases hx : o.X ∈ B <;> by_cases hA : o.A = false <;>
          simp [Set.indicator, hx, hA]
      · congr 1
        funext x
        by_cases hx : x ∈ B <;> simp [Set.indicator, hx]
    have hGmap :
        ∫ o in {o : FullRow | o.X ∈ B}, (offsetG a P.logger o.X)^2 ∂P.full =
          ∫ x in B, (offsetG a P.logger x)^2 ∂P.PX := by
      change (∫ o in (fun o : FullRow => o.X) ⁻¹' B,
        (offsetG a P.logger o.X)^2 ∂P.full) =
        (∫ x in B, (offsetG a P.logger x)^2 ∂P.PX)
      rw [← integral_indicator (fullRow_X_measurable hB),
        ← integral_indicator hB, RowLaw.PX]
      convert (integral_map fullRow_X_measurable.aemeasurable
        ((hg.pow 2).indicator hB)).symm using 1
      · rfl
      · rfl
    rw [hmapset]
    calc
      _ ≤ ∫ o in {o : FullRow | o.X ∈ B}, F o ∂P.full :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun o => sq_nonneg _))
          hFint.integrableOn (ae_restrict_of_ae hpoint)
      _ = 2 * ∫ x in B, P.logger x * f1 x ∂P.PX +
            2 * ∫ x in B, (1-P.logger x) * f0 x ∂P.PX +
            2 * ∫ x in B, (offsetG a P.logger x)^2 ∂P.PX := by
        change (∫ o in {o : FullRow | o.X ∈ B},
          (2 * (if o.A = true then f1 o.X else 0) +
            2 * (if o.A = false then f0 o.X else 0)) +
            2 * (offsetG a P.logger o.X)^2 ∂P.full) = _
        rw [integral_add, integral_add, integral_const_mul, integral_const_mul,
          integral_const_mul, hArm1, hArm0, hGmap]
        all_goals first
          | exact ((hC1int.const_mul 2).add (hC0int.const_mul 2)).integrableOn
          | exact (hC1int.const_mul 2).integrableOn
          | exact (hC0int.const_mul 2).integrableOn
          | exact (hGint.const_mul 2).integrableOn
      _ ≤ ∫ x in B, 6*offsetG a P.logger x/a ∂P.PX := by
        let U : ℝ → ℝ := fun x => 2 * (P.logger x * f1 x +
          (1-P.logger x) * f0 x + (offsetG a P.logger x)^2)
        let V : ℝ → ℝ := fun x => 6 * offsetG a P.logger x / a
        have hUV : ∀ᵐ x ∂P.PX, U x ≤ V x := by
          filter_upwards [hpositive, helog_eq] with x he hel
          have hp : 0 < min (P.logger x) (1-P.logger x) :=
            lt_min he.1 (by linarith [he.2])
          by_cases hr : a ≤ min (P.logger x) (1-P.logger x)
          · have hr' : retained x := by simpa [retained, ← hel] using hr
            have hgx : offsetG a P.logger x = a / min (P.logger x) (1-P.logger x) := by
              unfold offsetG
              rw [min_eq_right]
              exact (div_le_one hp).2 hr
            simpa [U, V, f1, f0, hr', hgx, ← hel] using
              score_pointwise_retained_two_sq a (P.logger x) ha he hr
          · have hr' : ¬ retained x := by simpa [retained, ← hel] using hr
            have hgx : offsetG a P.logger x = 1 := by
              unfold offsetG
              rw [min_eq_left]
              exact (one_le_div hp).2 (le_of_not_ge hr)
            simpa [U, V, f1, f0, hr', hgx] using
              score_pointwise_deleted_two_sq a ha
        have hVmeas : AEStronglyMeasurable V P.PX := by
          dsimp [V]
          convert hg.const_mul (6/a) using 1
          ext x
          ring
        have hUmeas : AEStronglyMeasurable U P.PX := by
          dsimp [U]
          exact (((hlog.aestronglyMeasurable.mul hf1).add
            ((aestronglyMeasurable_const.sub hlog.aestronglyMeasurable).mul hf0)).add
            (hg.pow 2)).const_mul 2
        have hgb : ∀ᵐ x ∂P.PX,
            0 ≤ offsetG a P.logger x ∧ offsetG a P.logger x ≤ 1 := by
          filter_upwards [hpositive] with x he
          have hp : 0 < min (P.logger x) (1-P.logger x) :=
            lt_min he.1 (by linarith [he.2])
          unfold offsetG
          exact ⟨le_min (by norm_num) (div_nonneg ha.1.le hp.le), min_le_left _ _⟩
        have hVint : Integrable V P.PX := by
          letI : IsFiniteMeasure P.PX := ⟨by
            rw [RowLaw.PX, Measure.map_apply fullRow_X_measurable MeasurableSet.univ]
            simp⟩
          refine Integrable.mono' (integrable_const (6/a : ℝ)) hVmeas ?_
          filter_upwards [hgb] with x hx
          rw [Real.norm_eq_abs, abs_of_nonneg]
          · dsimp [V]
            exact (div_le_div_of_nonneg_right (by nlinarith [hx.2]) ha.1.le)
          · dsimp [V]
            exact div_nonneg (mul_nonneg (by norm_num) hx.1) ha.1.le
        have hUint : Integrable U P.PX := by
          refine Integrable.mono' hVint hUmeas ?_
          filter_upwards [hUV, hpositive, hgb] with x hx he hgx
          have hf1n : 0 ≤ f1 x := by dsimp [f1]; split_ifs <;> positivity
          have hf0n : 0 ≤ f0 x := by dsimp [f0]; split_ifs <;> positivity
          rw [Real.norm_eq_abs, abs_of_nonneg]
          · exact hx
          · dsimp [U]
            have he0 : 0 ≤ 1-P.logger x := by linarith [he.2]
            nlinarith [mul_nonneg he.1.le hf1n, mul_nonneg he0 hf0n,
              sq_nonneg (offsetG a P.logger x)]
        have hUintB : Integrable U (P.PX.restrict B) := hUint.integrableOn
        have hVintB : Integrable V (P.PX.restrict B) := hVint.integrableOn
        have hUVB : ∀ᵐ x ∂P.PX.restrict B, U x ≤ V x := ae_restrict_of_ae hUV
        have hmono := integral_mono_ae hUintB hVintB hUVB
        have h1meas : AEStronglyMeasurable
            (fun x => P.logger x * f1 x) P.PX := hlog.aestronglyMeasurable.mul hf1
        have h0meas : AEStronglyMeasurable
            (fun x => (1-P.logger x) * f0 x) P.PX :=
          (aestronglyMeasurable_const.sub hlog.aestronglyMeasurable).mul hf0
        have h2meas : AEStronglyMeasurable
            (fun x => (offsetG a P.logger x)^2) P.PX := hg.pow 2
        have hterms : ∀ᵐ x ∂P.PX,
            ‖P.logger x * f1 x‖ ≤ U x ∧
            ‖(1-P.logger x) * f0 x‖ ≤ U x ∧
            ‖(offsetG a P.logger x)^2‖ ≤ U x := by
          filter_upwards [hpositive] with x he
          have hf1n : 0 ≤ f1 x := by dsimp [f1]; split_ifs <;> positivity
          have hf0n : 0 ≤ f0 x := by dsimp [f0]; split_ifs <;> positivity
          have he0 : 0 ≤ 1-P.logger x := by linarith [he.2]
          have h1n := mul_nonneg he.1.le hf1n
          have h0n := mul_nonneg he0 hf0n
          dsimp [U]
          simp only [Real.norm_eq_abs, abs_of_nonneg h1n, abs_of_nonneg h0n,
            abs_of_nonneg (sq_nonneg (offsetG a P.logger x))]
          constructor <;> try constructor
          all_goals nlinarith [sq_nonneg (offsetG a P.logger x)]
        have h1int : Integrable (fun x => P.logger x * f1 x) P.PX :=
          Integrable.mono' hUint h1meas (hterms.mono fun x hx => hx.1)
        have h0int : Integrable (fun x => (1-P.logger x) * f0 x) P.PX :=
          Integrable.mono' hUint h0meas (hterms.mono fun x hx => hx.2.1)
        have h2int : Integrable (fun x => (offsetG a P.logger x)^2) P.PX :=
          Integrable.mono' hUint h2meas (hterms.mono fun x hx => hx.2.2)
        have hUeq :
            ∫ x in B, U x ∂P.PX =
              2 * ∫ x in B, P.logger x * f1 x ∂P.PX +
              2 * ∫ x in B, (1-P.logger x) * f0 x ∂P.PX +
              2 * ∫ x in B, (offsetG a P.logger x)^2 ∂P.PX := by
          have hUfun : U = (fun x =>
              (2 * (P.logger x * f1 x) + 2 * ((1-P.logger x) * f0 x)) +
              2 * (offsetG a P.logger x)^2) := by
            funext x
            dsimp [U]
            ring
          rw [hUfun]
          rw [integral_add, integral_add, integral_const_mul,
            integral_const_mul, integral_const_mul]
          all_goals first
            | exact ((h1int.const_mul 2).add (h0int.const_mul 2)).integrableOn
            | exact (h1int.const_mul 2).integrableOn
            | exact (h0int.const_mul 2).integrableOn
            | exact (h2int.const_mul 2).integrableOn
        rw [← hUeq]
        exact hmono
  refine ⟨zScore_abs_ae P a ha hwf hloggerSpace,
    (fun B hB => (hsecond B hB).2), ?_⟩
  intro B hB
  have hnonneg : 0 ≤ 4/a^2 := by positivity
  have hbound : ∀ᵐ o ∂P.obsLaw.restrict {o | o.X ∈ B},
      (zScore a P.logger o)^4 ≤
        (4/a^2) * (zScore a P.logger o)^2 := by
    filter_upwards [ae_restrict_of_ae (zScore_abs_ae P a ha hwf hloggerSpace)] with o ho
    have hsq : (zScore a P.logger o)^2 ≤ (2/a)^2 := by
      have hpos : 0 ≤ 2/a := div_nonneg (by norm_num) ha.1.le
      rcases abs_le.mp ho with ⟨hlo, hhi⟩
      nlinarith
    calc
      (zScore a P.logger o)^4 =
          (zScore a P.logger o)^2 * (zScore a P.logger o)^2 := by ring
      _ ≤ (2/a)^2 * (zScore a P.logger o)^2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = (4/a^2) * (zScore a P.logger o)^2 := by ring
  have hfour :
      ∫ o in {o | o.X ∈ B}, (zScore a P.logger o)^4 ∂P.obsLaw ≤
        (4/a^2) * ∫ o in {o | o.X ∈ B},
          (zScore a P.logger o)^2 ∂P.obsLaw := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun o => by positivity))
      ((hsecond B hB).1.const_mul _) hbound
  calc
    ∫ o in {o | o.X ∈ B}, (zScore a P.logger o)^4 ∂P.obsLaw ≤
        (4/a^2) * ∫ o in {o | o.X ∈ B},
          (zScore a P.logger o)^2 ∂P.obsLaw := hfour
    _ ≤ (4/a^2) * ∫ x in B, 6*offsetG a P.logger x/a ∂P.PX :=
      mul_le_mul_of_nonneg_left (hsecond B hB).2 hnonneg
    _ = ∫ x in B, 24*offsetG a P.logger x/a^3 ∂P.PX := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring


end CausalSmith.Stat.ScorethresholdOverlapRegret
