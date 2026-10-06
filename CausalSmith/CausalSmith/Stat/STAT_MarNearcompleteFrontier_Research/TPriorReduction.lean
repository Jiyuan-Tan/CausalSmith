module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.TPriorReductionPoint

/-!
# Interval reduction and combined lower frontiers

This module converts prior separation and parametric floors into interval and
combined minimax bounds.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

/-- A high-probability event on the concentrated part of a prior remains likely in its mixture. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `Good`](hyp:Good), [the specified input `hgood`](hyp:hgood), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α), [the specified input `β`](hyp:β), [the specified input `hα`](hyp:hα). Given [the specified input `π`](hyp:π), [the specified input `E`](hyp:E), [the specified input `hE`](hyp:hE). -/
-- @node: priorPredictive_event_from_good
lemma priorPredictive_event_from_good {n d : ℕ} {q α β : ℝ}
    (π : PMF (ClassLaw d q)) (E : Set (Fin n → Obs d))
    (Good : ClassLaw d q → Prop)
    (hα : 0 ≤ α) (hgood : 1 - β ≤ priorEventMass d q π Good)
    (hE : ∀ P, Good P → 1 - α ≤ (samplePi P.val n).real E) :
    1 - α - β ≤ (priorPredictive n d q π).real E := by
  classical
  let f : ClassLaw d q → ℝ := fun P => (samplePi P.val n).real E
  let bad : ClassLaw d q → ℝ := fun P => if Good P then 0 else 1
  have hbad : (∫ P, bad P ∂π.toMeasure) ≤ β := by
    have hfail := priorEventMass_failure_le π Good hgood
    have hmeas : MeasurableSet {P : ClassLaw d q | ¬ Good P} := trivial
    have hpoint : bad = {P : ClassLaw d q | ¬ Good P}.indicator (fun _ => 1) := by
      funext P
      by_cases h : Good P <;> simp [bad, Set.indicator, h]
    have hbad_eq : (∫ P, bad P ∂π.toMeasure) =
        priorEventMass d q π (fun P => ¬ Good P) := by
      unfold priorEventMass
      change (∫ P, bad P ∂π.toMeasure) = π.toMeasure.real {P | ¬ Good P}
      rw [hpoint, integral_indicator hmeas]
      simp
    exact hbad_eq.trans_le hfail
  have hfint : Integrable f π.toMeasure := by
    have hm : Measurable f := by intro s hs; trivial
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [] with P
    haveI : IsProbabilityMeasure (samplePi P.val n) := by
      unfold samplePi
      infer_instance
    have hlo : 0 ≤ f P := measureReal_nonneg
    have hhi : f P ≤ 1 := measureReal_le_one
    simp only [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, hhi⟩
  have hbadint : Integrable bad π.toMeasure := by
    have hm : Measurable bad := by intro s hs; trivial
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [] with P
    by_cases h : Good P <;> simp [bad, h]
  have hpoint (P : ClassLaw d q) : 1 - α - bad P ≤ f P := by
    by_cases h : Good P
    · simpa [bad, h, f] using hE P h
    · have hnonneg : 0 ≤ f P := measureReal_nonneg
      simp [bad, h]
      linarith
  haveI : IsProbabilityMeasure π.toMeasure := inferInstance
  have hbound : (∫ P, 1 - α - bad P ∂π.toMeasure) ≤
      ∫ P, f P ∂π.toMeasure :=
    integral_mono ((integrable_const (1 - α)).sub hbadint) hfint hpoint
  have hlin : (∫ P, 1 - α - bad P ∂π.toMeasure) =
      1 - α - ∫ P, bad P ∂π.toMeasure := by
    rw [integral_sub (integrable_const (1 - α)) hbadint]
    simp
  rw [hlin] at hbound
  rw [priorPredictive_event_eq_integral]
  linarith

/-- Integration under a predictive mixture is integration under the prior of sample integrals. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the stated mathematical conclusion holds](goal). Given [the specified input `π`](hyp:π), [the specified input `f`](hyp:f). -/
-- @node: priorPredictive_integral_eq_priorAverage
lemma priorPredictive_integral_eq_priorAverage {n d : ℕ} {q : ℝ}
    (π : PMF (ClassLaw d q)) (f : (Fin n → Obs d) → ℝ) :
    (∫ o, f o ∂priorPredictive n d q π) =
      ∫ P, ∫ o, f o ∂samplePi P.val n ∂π.toMeasure := by
  have hK : Measurable (fun P : ClassLaw d q => samplePi P.val n) := by
    intro s hs
    trivial
  haveI := priorPredictive_isProbability n d q π
  have hf : Integrable f (priorPredictive n d q π) := Integrable.of_finite
  simpa [priorPredictive] using
    (Causalean.Mathlib.MeasureTheory.integral_bind hK hf)

/-- The bounded interval length is integrable over any legal-law prior. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `I`](hyp:I), [the stated mathematical conclusion holds](goal). Given [the specified input `π`](hyp:π). -/
-- @node: intervalLength_integrable_prior
lemma intervalLength_integrable_prior {n d : ℕ} {q : ℝ}
    (π : PMF (ClassLaw d q)) (I : IntervalProc n d) :
    Integrable (fun P : ClassLaw d q =>
      ∫ o, (I.hi o - I.lo o) ∂samplePi P.val n) π.toMeasure := by
  have hmeas : Measurable (fun P : ClassLaw d q =>
      ∫ o, (I.hi o - I.lo o) ∂samplePi P.val n) := by
    intro s hs
    trivial
  apply Integrable.of_bound hmeas.aestronglyMeasurable 2
  filter_upwards [] with P
  haveI : IsProbabilityMeasure (samplePi P.val n) := by
    unfold samplePi
    infer_instance
  have hlo : 0 ≤ ∫ o, (I.hi o - I.lo o) ∂samplePi P.val n :=
    integral_nonneg (fun o => sub_nonneg.mpr (I.bounds o).2.1)
  have hhi : (∫ o, (I.hi o - I.lo o) ∂samplePi P.val n) ≤ 2 := by
    have hpoint (o : Fin n → Obs d) : I.hi o - I.lo o ≤ 2 := by
      have h := I.bounds o
      linarith
    have hInt : Integrable (fun o => I.hi o - I.lo o) (samplePi P.val n) :=
      Integrable.of_finite
    simpa using (integral_mono hInt (integrable_const 2) hpoint)
  simp only [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, hhi⟩

/-- A lower bound on every honest interval's prior-average length passes to minimax length. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `c`](hyp:c), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α), [the specified input `hα`](hyp:hα). Given [the specified input `π`](hyp:π), [the specified input `h`](hyp:h). -/
-- @node: lengthMinimaxRisk_lower_of_prior
lemma lengthMinimaxRisk_lower_of_prior {n d : ℕ} {q α c : ℝ}
    (π : PMF (ClassLaw d q)) (hα : 0 ≤ α)
    (h : ∀ I : HonestIntervalClass n d q α,
      c ≤ ∫ P : ClassLaw d q,
        ∫ o, (I.val.hi o - I.val.lo o) ∂samplePi P.val n ∂π.toMeasure) :
    c ≤ lengthMinimaxRisk n d q α := by
  let Iall : IntervalProc n d :=
    ⟨fun _ => -1, fun _ => 1, measurable_const, measurable_const,
      fun _ => by constructor <;> norm_num⟩
  letI : Nonempty (HonestIntervalClass n d q α) :=
    ⟨⟨Iall, fun P' => by
      haveI : IsProbabilityMeasure (samplePi P'.val n) := by
        unfold samplePi
        infer_instance
      have hτ := tau_range P'.val
      have hevent : {o : Fin n → Obs d |
          tau P'.val ∈ Set.Icc (Iall.lo o) (Iall.hi o)} = Set.univ := by
        ext o
        simp [Iall, hτ]
      rw [hevent, probReal_univ]
      linarith⟩⟩
  unfold lengthMinimaxRisk
  refine le_ciInf fun I => ?_
  let lengthRisk : ClassLaw d q → ℝ := fun P =>
    ∫ o, (I.val.hi o - I.val.lo o) ∂samplePi P.val n
  have hb : BddAbove (Set.range lengthRisk) := by
    refine ⟨2, ?_⟩
    rintro y ⟨P, rfl⟩
    haveI : IsProbabilityMeasure (samplePi P.val n) := by
      unfold samplePi
      infer_instance
    have hpoint (o : Fin n → Obs d) : I.val.hi o - I.val.lo o ≤ 2 := by
      have hI := I.val.bounds o
      linarith
    have hInt : Integrable (fun o => I.val.hi o - I.val.lo o)
        (samplePi P.val n) := Integrable.of_finite
    simpa [lengthRisk] using (integral_mono hInt (integrable_const 2) hpoint)
  let R : ℝ := ⨆ P : ClassLaw d q, lengthRisk P
  have hpoint (P : ClassLaw d q) : lengthRisk P ≤ R := le_ciSup hb P
  have havg := priorAverage_le_of_pointwise π lengthRisk R
    (intervalLength_integrable_prior π I.val) hpoint
  have hc := h I
  dsimp [lengthRisk, R] at havg hc ⊢
  exact hc.trans havg

/-- Length on a predictive sample event bounds its mixture expectation. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `I`](hyp:I), [the specified input `a`](hyp:a), [the specified input `hE`](hyp:hE), [the stated mathematical conclusion holds](goal). Given [the specified input `π`](hyp:π), [the specified input `E`](hyp:E). -/
-- @node: priorPredictive_intervalLength_ge_event
lemma priorPredictive_intervalLength_ge_event {n d : ℕ} {q : ℝ}
    (π : PMF (ClassLaw d q)) (I : IntervalProc n d)
    (E : Set (Fin n → Obs d)) (a : ℝ)
    (hE : ∀ o ∈ E, a ≤ I.hi o - I.lo o) :
    a * (priorPredictive n d q π).real E ≤
      ∫ P : ClassLaw d q, ∫ o, (I.hi o - I.lo o)
        ∂samplePi P.val n ∂π.toMeasure := by
  haveI := priorPredictive_isProbability n d q π
  have hmeas : MeasurableSet E := (Set.toFinite E).measurableSet
  have hpoint (o : Fin n → Obs d) :
      E.indicator (fun _ => a) o ≤ I.hi o - I.lo o := by
    by_cases ho : o ∈ E
    · simpa [Set.indicator, ho] using hE o ho
    · have hnonneg := (I.bounds o).2.1
      simpa [Set.indicator, ho] using hnonneg
  have hInt : Integrable (E.indicator (fun _ : Fin n → Obs d => a))
      (priorPredictive n d q π) := Integrable.of_finite
  have hLen : Integrable (fun o => I.hi o - I.lo o)
      (priorPredictive n d q π) := Integrable.of_finite
  have hbound := integral_mono hInt hLen hpoint
  calc
    a * (priorPredictive n d q π).real E =
        ∫ o, E.indicator (fun _ => a) o ∂priorPredictive n d q π := by
          simp [integral_indicator hmeas, mul_comm]
    _ ≤ ∫ o, I.hi o - I.lo o ∂priorPredictive n d q π := hbound
    _ = ∫ P, ∫ o, I.hi o - I.lo o ∂samplePi P.val n ∂π.toMeasure :=
      priorPredictive_integral_eq_priorAverage π _

/-- The normalized converse gives the stated `5/4` interval-length coefficient. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α). Given [the specified input `hα`](hyp:hα), [the specified input `hq`](hyp:hq), [the specified input `hlarge`](hyp:hlarge). -/
-- @node: priorIntervalRisk_separation
lemma priorIntervalRisk_separation (α : ℝ)
    (hα : α ∈ Set.Ioo 0 ((1 : ℝ) / 2))
    (n d : ℕ) (q : ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hlarge : gScale n d q ^ 2 ≥ 1 / (n : ℝ)) :
    (5 / 4 : ℝ) *
        converseConstant (intervalBeta α) (intervalBeta_valid α hα) *
        (1 - 2 * α) * gScale n d q ≤
      lengthMinimaxRisk n d q α := by
  let β := intervalBeta α
  let a := converseConstant β (intervalBeta_valid α hα) * gScale n d q
  obtain ⟨πminus, πplus, htv, m, hm, hp⟩ :=
    (converseConstant_spec β (intervalBeta_valid α hα)).2 n d q hn hd hq hlarge
  have ha : 0 ≤ a := mul_nonneg
    (le_of_lt (converseConstant_spec β (intervalBeta_valid α hα)).1)
    (gScale_nonneg_of_q n d q hq)
  apply lengthMinimaxRisk_lower_of_prior πplus (le_of_lt hα.1)
  intro I
  let EL : Set (Fin n → Obs d) := {o | I.val.lo o ≤ m - a}
  let ER : Set (Fin n → Obs d) := {o | m + a ≤ I.val.hi o}
  have hL : 1 - α - β ≤ (priorPredictive n d q πminus).real EL := by
    apply priorPredictive_event_from_good πminus EL
      (fun P => tau P.val ≤ m - a) (le_of_lt hα.1) hm
    intro P hP
    haveI : IsProbabilityMeasure (samplePi P.val n) := by
      unfold samplePi
      infer_instance
    have hcov := I.property P
    have hsub : {o | tau P.val ∈ Set.Icc (I.val.lo o) (I.val.hi o)} ⊆ EL := by
      intro o ho
      exact le_trans ho.1 hP
    exact hcov.trans (measureReal_mono hsub (measure_ne_top _ _))
  have hR : 1 - α - β ≤ (priorPredictive n d q πplus).real ER := by
    apply priorPredictive_event_from_good πplus ER
      (fun P => m + a ≤ tau P.val) (le_of_lt hα.1) hp
    intro P hP
    haveI : IsProbabilityMeasure (samplePi P.val n) := by
      unfold samplePi
      infer_instance
    have hcov := I.property P
    have hsub : {o | tau P.val ∈ Set.Icc (I.val.lo o) (I.val.hi o)} ⊆ ER := by
      intro o ho
      exact le_trans hP ho.2
    exact hcov.trans (measureReal_mono hsub (measure_ne_top _ _))
  have hinter := priorPredictive_separated_intersection
    πminus πplus htv EL ER hL hR
  have hlen := priorPredictive_intervalLength_ge_event πplus I.val
    (EL ∩ ER) (2 * a) (by
      intro o ho
      rcases ho with ⟨hoL, hoR⟩
      change I.val.lo o ≤ m - a at hoL
      change m + a ≤ I.val.hi o at hoR
      linarith)
  have hmass : 2 * a * (1 - 2 * α - 3 * β) ≤
      2 * a * (priorPredictive n d q πplus).real (EL ∩ ER) :=
    mul_le_mul_of_nonneg_left hinter (by linarith)
  dsimp [a, β, intervalBeta] at hmass hlen ⊢
  nlinarith

-- @node: lem:prior-reduction
/-- Explicit fuzzy-prior constants, parametric floors and combined lower rates. [the stated mathematical conclusion holds](goal). -/
lemma prior_reduction :
    ∃ cPoint c0 : ℝ, 0 < cPoint ∧ 0 < c0 ∧
      ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 ((1 : ℝ) / 2)),
        ∃ cInterval c0α : ℝ, 0 < cInterval ∧ 0 < c0α ∧
          ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d →
            q ∈ Set.Icc ((1 : ℝ) / 2) 1 →
            (gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
              (13 / 32 : ℝ) * converseConstant pointBeta pointBeta_valid ^ 2 *
                  gScale n d q ^ 2 ≤ pointMinimaxRisk n d q ∧
              (5 / 4 : ℝ) *
                  converseConstant (intervalBeta α) (intervalBeta_valid α hα) *
                  (1 - 2 * α) * gScale n d q ≤
                    lengthMinimaxRisk n d q α) ∧
            c0 / (n : ℝ) ≤ pointMinimaxRisk n d q ∧
            c0α / Real.sqrt n ≤ lengthMinimaxRisk n d q α ∧
            cPoint * rate n d q ≤ pointMinimaxRisk n d q ∧
            cInterval * Real.sqrt (rate n d q) ≤
              lengthMinimaxRisk n d q α := by
  obtain ⟨c0, hc0, hfloorPoint, hfloorInterval⟩ := parametric_floor
  let cSepPoint : ℝ :=
    (13 / 32 : ℝ) * converseConstant pointBeta pointBeta_valid ^ 2
  have hcSepPoint : 0 < cSepPoint := by
    dsimp [cSepPoint]
    have hc := (converseConstant_spec pointBeta pointBeta_valid).1
    positivity
  refine ⟨min c0 cSepPoint / 2, c0, ?_, hc0, ?_⟩
  · positivity
  intro α hα
  obtain ⟨c0α, hc0α, hfloorα⟩ := hfloorInterval α hα
  let cSepInterval : ℝ :=
    (5 / 4 : ℝ) *
      converseConstant (intervalBeta α) (intervalBeta_valid α hα) *
      (1 - 2 * α)
  have hcSepInterval : 0 < cSepInterval := by
    dsimp [cSepInterval]
    have hc := (converseConstant_spec
      (intervalBeta α) (intervalBeta_valid α hα)).1
    have hfac : 0 < 1 - 2 * α := by linarith [hα.2]
    positivity
  refine ⟨min c0α cSepInterval / 2, c0α, ?_, hc0α, ?_⟩
  · positivity
  intro n d q hn hd hq
  have hPointSep : gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
      cSepPoint * gScale n d q ^ 2 ≤ pointMinimaxRisk n d q := by
    intro hlarge
    exact priorPointRisk_separation n d q hn hd hq hlarge
  have hIntervalSep : gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
      cSepInterval * gScale n d q ≤ lengthMinimaxRisk n d q α := by
    intro hlarge
    exact priorIntervalRisk_separation α hα n d q hn hd hq hlarge
  have hPointFloor := hfloorPoint n d q hn hd hq
  have hIntervalFloor := hfloorα n d q hn hd hq
  have hPointRate := pointRate_from_floor_and_separation
    n d q c0 cSepPoint (pointMinimaxRisk n d q) hn
    (le_of_lt hc0) (le_of_lt hcSepPoint) hPointFloor hPointSep
  have hIntervalRate := intervalRate_from_floor_and_separation
    n d q c0α cSepInterval (lengthMinimaxRisk n d q α) hn
    (le_of_lt hc0α) (le_of_lt hcSepInterval) hIntervalFloor hIntervalSep hq
  exact ⟨fun hlarge => ⟨hPointSep hlarge, hIntervalSep hlarge⟩,
    hPointFloor, hIntervalFloor, hPointRate, hIntervalRate⟩

end CausalSmith.Stat.MarNearcompleteFrontier
