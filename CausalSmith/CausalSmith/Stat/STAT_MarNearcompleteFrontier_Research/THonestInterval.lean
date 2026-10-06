module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.TUpperRisk
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.Converse.Target

/-!
# Honest clipped interval from the risk certificate

The radius uses a certified uniform risk constant. Its large-radius branch
covers deterministically, and its smaller branch uses Markov's inequality.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

-- @node: lem:honest-interval-construction
/-- The clipped interval is honest and has the stated pointwise and expected length. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `CU`](hyp:CU), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `hCU`](hyp:hCU), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α). Given [the specified input `hq`](hyp:hq), [the specified input `hα`](hyp:hα). -/
lemma honest_interval_construction
    (n d : ℕ) (q α CU : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hα : α ∈ Set.Ioo 0 ((1 : ℝ) / 2))
    (hCU : UpperRiskCertificate CU) :
    Honest n d q α (intervalMM n d q α CU hCU) ∧
    (∀ o : Fin n → Obs d,
      (intervalMM n d q α CU hCU).hi o - (intervalMM n d q α CU hCU).lo o ≤
        min 2 (2 * intervalRadius n d q α CU)) ∧
    (min 2 (2 * intervalRadius n d q α CU) =
      min 2 (2 * Real.sqrt (CU * rate n d q / α))) ∧
    (∀ P : ClassLaw d q,
      (∫ o, ((intervalMM n d q α CU hCU).hi o -
        (intervalMM n d q α CU hCU).lo o) ∂ samplePi P.val n) ≤
          min 2 (2 * Real.sqrt (CU * rate n d q / α))) ∧
    (intervalRadius n d q α CU < 2 →
      ∀ P : ClassLaw d q,
        (samplePi P.val n).real
          {o | tau P.val ∉ Set.Icc ((intervalMM n d q α CU hCU).lo o)
            ((intervalMM n d q α CU hCU).hi o)} ≤ α) ∧
    (intervalRadius n d q α CU = 2 →
      ∀ (P : ClassLaw d q) (o : Fin n → Obs d),
        tau P.val ∈ Set.Icc ((intervalMM n d q α CU hCU).lo o)
          ((intervalMM n d q α CU hCU).hi o)) := by
  let h := intervalRadius n d q α CU
  let I := intervalMM n d q α CU hCU
  have hh : 0 ≤ h := intervalRadius_nonneg n d q α CU
  have hlen (o : Fin n → Obs d) : I.hi o - I.lo o ≤ min 2 (2 * h) := by
    have hb := I.bounds o
    change min 1 (tauhatMM n d q o + h) -
      max (-1) (tauhatMM n d q o - h) ≤ min 2 (2 * h)
    apply le_min
    · have hl := le_max_left (-1) (tauhatMM n d q o - h)
      have hu := min_le_left 1 (tauhatMM n d q o + h)
      linarith
    · have hl := le_max_right (-1) (tauhatMM n d q o - h)
      have hu := min_le_right 1 (tauhatMM n d q o + h)
      linarith
  have hmin : min 2 (2 * h) =
      min 2 (2 * Real.sqrt (CU * rate n d q / α)) := by
    simp only [h, intervalRadius]
    rcases le_total 2 (Real.sqrt (CU * rate n d q / α)) with hs | hs
    · rw [min_eq_left hs]
      have hs' : 2 ≤ 2 * Real.sqrt (CU * rate n d q / α) := by linarith
      simp [min_eq_left hs']
    · rw [min_eq_right hs]
  have hlarge (hh2 : h = 2) (P : ClassLaw d q) (o : Fin n → Obs d) :
      tau P.val ∈ Set.Icc (I.lo o) (I.hi o) := by
    have ht := tau_range P.val
    have he := tauhatMM_range n d q o
    rcases ht with ⟨htlo, hthi⟩
    rcases he with ⟨helo, hehi⟩
    change max (-1) (tauhatMM n d q o - h) ≤ tau P.val ∧
      tau P.val ≤ min 1 (tauhatMM n d q o + h)
    constructor
    · apply max_le htlo
      rw [hh2]
      linarith
    · apply le_min hthi
      rw [hh2]
      linarith
  have hsmall (hh2 : h < 2) (P : ClassLaw d q) :
      (samplePi P.val n).real {o | tau P.val ∉ Set.Icc (I.lo o) (I.hi o)} ≤ α := by
    let μ := samplePi P.val n
    letI : IsProbabilityMeasure μ := by
      dsimp [μ, samplePi]
      infer_instance
    let f : (Fin n → Obs d) → ℝ := fun o => (tauhatMM n d q o - tau P.val) ^ 2
    have hαpos : 0 < α := hα.1
    have hrate : 0 ≤ rate n d q := by unfold rate; positivity
    have hrad : h = Real.sqrt (CU * rate n d q / α) := by
      dsimp [h, intervalRadius] at hh2 ⊢
      by_cases hs : Real.sqrt (CU * rate n d q / α) ≤ 2
      · exact min_eq_right hs
      · have hs' : 2 ≤ Real.sqrt (CU * rate n d q / α) := le_of_not_ge hs
        simp only [min_eq_left hs'] at hh2
        linarith
    have hsq : h ^ 2 = CU * rate n d q / α := by
      rw [hrad, Real.sq_sqrt (div_nonneg (mul_nonneg (le_of_lt hCU.1) hrate)
        (le_of_lt hαpos))]
    have hpos : 0 < h := by
      rw [hrad]
      apply Real.sqrt_pos.2
      have hrpos : 0 < rate n d q := by
        unfold rate
        have : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
        positivity
      exact div_pos (mul_pos hCU.1 hrpos) hαpos
    have hsubset : {o | tau P.val ∉ Set.Icc (I.lo o) (I.hi o)} ⊆
        {o | h ^ 2 ≤ f o} := by
      intro o ho
      have he := tauhatMM_range n d q o
      change ¬(max (-1) (tauhatMM n d q o - h) ≤ tau P.val ∧
        tau P.val ≤ min 1 (tauhatMM n d q o + h)) at ho
      simp only [not_and_or, not_le] at ho
      change h ^ 2 ≤ (tauhatMM n d q o - tau P.val) ^ 2
      rcases ho with hlo | hhi
      · have ht := (tau_range P.val).1
        have hm : tau P.val < tauhatMM n d q o - h := by
          by_cases hb : -1 ≤ tauhatMM n d q o - h
          · simpa [max_eq_right hb] using hlo
          · have heq : max (-1) (tauhatMM n d q o - h) = -1 :=
              max_eq_left (le_of_not_ge hb)
            rw [heq] at hlo
            linarith
        nlinarith
      · have ht := (tau_range P.val).2
        have hm : tauhatMM n d q o + h < tau P.val := by
          by_cases hb : tauhatMM n d q o + h ≤ 1
          · simpa [min_eq_right hb] using hhi
          · have heq : min 1 (tauhatMM n d q o + h) = 1 :=
              min_eq_left (le_of_not_ge hb)
            rw [heq] at hhi
            linarith
        nlinarith
    have hfint : Integrable f μ := Integrable.of_finite
    have hmarkov : h ^ 2 * μ.real {o | h ^ 2 ≤ f o} ≤ ∫ o, f o ∂μ :=
      mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall (fun o => sq_nonneg _))
        hfint (h ^ 2)
    have hrisk := hCU.2 n d q hn hd hq P μ rfl
    have hmeas : μ.real {o | tau P.val ∉ Set.Icc (I.lo o) (I.hi o)} ≤
        μ.real {o | h ^ 2 ≤ f o} := measureReal_mono hsubset
    have hnonneg : 0 ≤ μ.real {o | tau P.val ∉ Set.Icc (I.lo o) (I.hi o)} := measureReal_nonneg
    have hsqpos : 0 < h ^ 2 := sq_pos_of_pos hpos
    have hprod : CU * rate n d q = α * h ^ 2 := by
      rw [hsq]
      field_simp
    calc
      μ.real {o | tau P.val ∉ Set.Icc (I.lo o) (I.hi o)} ≤
          μ.real {o | h ^ 2 ≤ f o} := hmeas
      _ ≤ α := by
        dsimp [f, μ] at hmarkov hrisk ⊢
        nlinarith [hmarkov, hrisk, hprod]
  refine ⟨?_, hlen, hmin, ?_, hsmall, hlarge⟩
  · intro P
    let μ := samplePi P.val n
    letI : IsProbabilityMeasure μ := by
      dsimp [μ, samplePi]
      infer_instance
    by_cases hh2 : h = 2
    · have heq : {o | tau P.val ∈ Set.Icc (I.lo o) (I.hi o)} = Set.univ := by
        ext o
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact hlarge hh2 P o
      rw [heq]
      have : μ.real Set.univ = 1 := by simp
      change (samplePi P.val n).real Set.univ = 1 at this
      have hαpos : 0 < α := hα.1
      linarith
    · have hlt : h < 2 := lt_of_le_of_ne (min_le_left _ _) hh2
      have hbad := hsmall hlt P
      have hmeas : MeasurableSet {o | tau P.val ∈ Set.Icc (I.lo o) (I.hi o)} := by
        change MeasurableSet ({o | I.lo o ≤ tau P.val} ∩
          {o | tau P.val ≤ I.hi o})
        exact (measurableSet_le I.lo_measurable measurable_const).inter
          (measurableSet_le measurable_const I.hi_measurable)
      have hcomp := measureReal_compl (μ := μ) hmeas
      have hunit : μ.real Set.univ = 1 := by simp
      have heq : {o | tau P.val ∈ Set.Icc (I.lo o) (I.hi o)}ᶜ =
          {o | tau P.val ∉ Set.Icc (I.lo o) (I.hi o)} := rfl
      rw [heq, hunit] at hcomp
      dsimp [μ] at hcomp
      linarith
  · intro P
    letI : IsProbabilityMeasure (samplePi P.val n) := by
      unfold samplePi
      infer_instance
    have hint : Integrable (fun o => I.hi o - I.lo o) (samplePi P.val n) :=
      Integrable.of_finite
    calc
      (∫ o, I.hi o - I.lo o ∂ samplePi P.val n) ≤
          ∫ _o, min 2 (2 * h) ∂ samplePi P.val n :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun o =>
          sub_nonneg.mpr (I.bounds o).2.1))
          (integrable_const _) (Filter.Eventually.of_forall hlen)
      _ = min 2 (2 * Real.sqrt (CU * rate n d q / α)) := by
        simp [hmin]

end CausalSmith.Stat.MarNearcompleteFrontier
