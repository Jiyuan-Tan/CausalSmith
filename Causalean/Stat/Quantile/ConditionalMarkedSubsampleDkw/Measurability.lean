import Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw.Basic

/-!
# Measurability of finite empirical-CDF deviations

This module supplies the separability step needed to treat the supremum over
all real thresholds as an ordinary measurable random variable.  In
particular, callers of the tail-lifting theorem do not need to assume an extra
measurability side condition beyond the fixed-size probability bound.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

namespace Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw

/-- For [a finite real vector](hyp:x) and [a threshold](hyp:y), [its empirical CDF is continuous
from the right at that threshold](goal). -/
lemma empiricalCDFVec_continuousWithinAt_Ici {m : ℕ} (x : Fin m → ℝ) (y : ℝ) :
    ContinuousWithinAt (empiricalCDFVec x) (Ici y) y := by
  classical
  have hstat (i : Fin m) :
      ContinuousWithinAt (fun t : ℝ => Causalean.Stat.cdfStat t (x i)) (Ici y) y := by
    by_cases hxy : x i ≤ y
    · have hc : ContinuousWithinAt (fun _ : ℝ => (1 : ℝ)) (Ici y) y :=
        continuousWithinAt_const
      refine hc.congr ?_ ?_
      · intro z hz
        simp [Causalean.Stat.cdfStat, hxy.trans hz]
      · simp [Causalean.Stat.cdfStat, hxy]
    · have hyx : y < x i := lt_of_not_ge hxy
      have hc : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Ici y) y :=
        continuousWithinAt_const
      refine hc.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hyx)] with z hz
        simp [Causalean.Stat.cdfStat, not_le.mpr hz]
      · simp [Causalean.Stat.cdfStat, hxy]
  have hsum :
      ContinuousWithinAt
        (fun t : ℝ => ∑ i : Fin m, Causalean.Stat.cdfStat t (x i)) (Ici y) y := by
    let s : Finset (Fin m) := Finset.univ
    change ContinuousWithinAt
      (fun t : ℝ => ∑ i ∈ s, Causalean.Stat.cdfStat t (x i)) (Ici y) y
    induction s using Finset.induction_on with
    | empty => simpa using (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Ici y) y)
    | @insert a s ha ih =>
        simp only [Finset.sum_insert, ha, not_false_eq_true]
        exact (hstat a).add ih
  change ContinuousWithinAt
    (fun t : ℝ => (m : ℝ)⁻¹ * ∑ i : Fin m, Causalean.Stat.cdfStat t (x i)) (Ici y) y
  exact hsum.const_mul (m : ℝ)⁻¹

/-- For [a probability law](hyp:ρ), [the uniform empirical-CDF deviation of a finite real vector from that law is measurable](goal). -/
lemma measurable_uniformCDFDeviation {m : ℕ} (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] :
    Measurable (uniformCDFDeviation (m := m) ρ) := by
  -- Reduce the real supremum to a countable dense family of thresholds using right continuity.
  have hpoint (y : ℝ) :
      Measurable (fun x : Fin m → ℝ => |empiricalCDFVec x y - cdf ρ y|) := by
    apply Measurable.abs
    apply Measurable.sub
    · unfold empiricalCDFVec
      fun_prop
    · fun_prop
  have hbound (x : Fin m → ℝ) (y : ℝ) :
      |empiricalCDFVec x y - cdf ρ y| ≤ 1 := by
    have hstat_nonneg : 0 ≤ ∑ i : Fin m, Causalean.Stat.cdfStat y (x i) :=
      Finset.sum_nonneg fun i _ => Causalean.Stat.cdfStat_nonneg y (x i)
    have hstat_le : (∑ i : Fin m, Causalean.Stat.cdfStat y (x i)) ≤ m := by
      calc
        (∑ i : Fin m, Causalean.Stat.cdfStat y (x i)) ≤ ∑ _i : Fin m, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Causalean.Stat.cdfStat_le_one y (x i)
        _ = m := by simp
    have he0 : 0 ≤ empiricalCDFVec x y := by
      simp only [empiricalCDFVec]
      positivity
    have he1 : empiricalCDFVec x y ≤ 1 := by
      by_cases hm : m = 0
      · subst m
        simp [empiricalCDFVec]
      · rw [empiricalCDFVec, inv_mul_le_iff₀ (by positivity)]
        simpa using hstat_le
    have hc0 := cdf_nonneg ρ y
    have hc1 := cdf_le_one ρ y
    rw [abs_le]
    constructor <;> linarith
  have hsep (x : Fin m → ℝ) :
      uniformCDFDeviation ρ x =
        ⨆ q : ℚ, |empiricalCDFVec x (q : ℝ) - cdf ρ (q : ℝ)| := by
    let g : ℝ → ℝ := fun y => |empiricalCDFVec x y - cdf ρ y|
    have hg_bound (y : ℝ) : g y ≤ 1 := hbound x y
    have hreal_bdd : BddAbove (range g) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact hg_bound y
    have hrat_bdd : BddAbove (range fun q : ℚ => g (q : ℝ)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨q, rfl⟩
      exact hg_bound q
    change sSup (range g) = ⨆ q : ℚ, g (q : ℝ)
    apply le_antisymm
    · apply csSup_le
      · exact ⟨g 0, ⟨0, rfl⟩⟩
      · intro z hz
        rcases hz with ⟨y, rfl⟩
        obtain ⟨u, _, hu_above, hu_lim⟩ :=
          Rat.denseRange_cast.exists_seq_strictAnti_tendsto
            Rat.cast_strictMono.monotone y
        have hdev : ContinuousWithinAt g (Ici y) y :=
          ((empiricalCDFVec_continuousWithinAt_Ici x y).sub
            ((cdf ρ).right_continuous y)).abs
        have hu_within : Tendsto (Rat.cast ∘ u) atTop (𝓝[Ici y] y) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu_lim
            (Filter.Eventually.of_forall fun n =>
              Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp (hu_above n))))
        apply le_of_tendsto' (hdev.tendsto.comp hu_within)
        intro n
        exact le_ciSup hrat_bdd (u n)
    · apply ciSup_le
      intro q
      exact le_csSup hreal_bdd ⟨(q : ℝ), rfl⟩
  rw [show uniformCDFDeviation (m := m) ρ =
      fun x => ⨆ q : ℚ, |empiricalCDFVec x (q : ℝ) - cdf ρ (q : ℝ)| from
    funext hsep]
  exact Measurable.iSup fun q => hpoint q

/-- For [a probability law](hyp:ρ) and [a deviation radius](hyp:radius), [the fixed-size uniform empirical-CDF bad set is measurable](goal). -/
lemma measurableSet_fixedCDFBadSet {m : ℕ} (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (radius : ℝ) :
    MeasurableSet (fixedCDFBadSet (m := m) ρ radius) := by
  -- This is the measurable preimage of the open upper ray `(radius, ∞)`.
  change MeasurableSet ((uniformCDFDeviation (m := m) ρ) ⁻¹' Ioi radius)
  exact measurableSet_Ioi.preimage (measurable_uniformCDFDeviation ρ)

end Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw
