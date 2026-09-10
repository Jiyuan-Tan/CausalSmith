import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.EndpointDirectional
import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.TCapacityIdentification
import Causalean.Stat.EmpiricalProcess.CrossFitRate

/-!
# Deterministic and concentration bounds for the uniform guard

Paper-local analytic lemmas used by the alpha-indexed deterministic guard.
-/

open scoped BigOperators ENNReal
open MeasureTheory Filter Topology
open Causalean PO Causalean.Stat

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

variable {𝒳 Ω : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Nonempty 𝒳]
  [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [MeasurableSpace Ω]
variable {K : ℕ} {μ : Measure Ω}

private abbrev GuardMeasure (𝒳 : Type*) (K : ℕ) :=
  @Measure (ObservedDatum 𝒳 K) instMeasurableSpaceObservedDatum

variable {Pobs : GuardMeasure 𝒳 K}

private noncomputable def centeredGuardIndicator
    (Pobs : GuardMeasure 𝒳 K) (e : GuardEventIndex 𝒳 K) :
    ObservedDatum 𝒳 K → ℝ :=
  fun o => (if guardEvent e o then 1 else 0) -
    Pobs.real {u | guardEvent e u = true}

private lemma integral_guardIndicator
    (Pobs : GuardMeasure 𝒳 K)
    [DiscreteMeasurableSpace (ObservedDatum 𝒳 K)] [IsProbabilityMeasure Pobs]
    (e : GuardEventIndex 𝒳 K) :
    ∫ o, (if guardEvent e o then (1 : ℝ) else 0) ∂Pobs =
      Pobs.real {o | guardEvent e o = true} := by
  let E : Set (ObservedDatum 𝒳 K) := {o | guardEvent e o = true}
  have hE : MeasurableSet E := MeasurableSpace.measurableSet_top
  rw [show (fun o => if guardEvent e o then (1 : ℝ) else 0) = E.indicator 1 by
    funext o
    by_cases ho : guardEvent e o = true <;> simp [E, ho]]
  exact integral_indicator_one hE

private lemma integral_centeredGuardIndicator
    (Pobs : GuardMeasure 𝒳 K)
    [DiscreteMeasurableSpace (ObservedDatum 𝒳 K)] [IsProbabilityMeasure Pobs]
    (e : GuardEventIndex 𝒳 K) :
    ∫ o, centeredGuardIndicator Pobs e o ∂Pobs = 0 := by
  unfold centeredGuardIndicator
  rw [integral_sub]
  · rw [integral_guardIndicator]
    simp
  · fun_prop
  · fun_prop

private lemma integral_centeredGuardIndicator_sq
    (Pobs : GuardMeasure 𝒳 K)
    [DiscreteMeasurableSpace (ObservedDatum 𝒳 K)] [IsProbabilityMeasure Pobs]
    (e : GuardEventIndex 𝒳 K) :
    ∫ o, centeredGuardIndicator Pobs e o ^ 2 ∂Pobs =
      Pobs.real {o | guardEvent e o = true} *
        (1 - Pobs.real {o | guardEvent e o = true}) := by
  let p := Pobs.real {o | guardEvent e o = true}
  have hI : Integrable (fun o => if guardEvent e o then (1 : ℝ) else 0) Pobs := by
    fun_prop
  have hc : Integrable (fun _ : ObservedDatum 𝒳 K => p) Pobs := by fun_prop
  have hsq : (fun o => centeredGuardIndicator Pobs e o ^ 2) =
      fun o => (if guardEvent e o then (1 : ℝ) else 0) -
        2 * p * (if guardEvent e o then (1 : ℝ) else 0) + p ^ 2 := by
    funext o
    unfold centeredGuardIndicator
    dsimp [p]
    split <;> ring
  rw [hsq, integral_add, integral_sub]
  · simp only [integral_const_mul, integral_const, smul_eq_mul]
    rw [integral_guardIndicator]
    have hu : Pobs.real Set.univ = 1 := by simp [Measure.real]
    rw [hu]
    dsimp [p]
    ring
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop

private lemma centeredGuardIndicator_memLp
    (Pobs : GuardMeasure 𝒳 K)
    [DiscreteMeasurableSpace (ObservedDatum 𝒳 K)] [IsProbabilityMeasure Pobs]
    (e : GuardEventIndex 𝒳 K) : MemLp (centeredGuardIndicator Pobs e) 2 Pobs := by
  refine MemLp.of_bound (μ := Pobs) (by
    unfold centeredGuardIndicator
    fun_prop) 1 ?_
  filter_upwards [] with o
  have hp0 : 0 ≤ Pobs.real {u | guardEvent e u = true} := measureReal_nonneg
  have hp1 : Pobs.real {u | guardEvent e u = true} ≤ 1 := measureReal_le_one
  unfold centeredGuardIndicator
  split
  · simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg] <;> linarith
  · simp only [Real.norm_eq_abs]
    rw [abs_of_nonpos] <;> linarith

private lemma empiricalFreq_sub_eq_centered_sum
    (O : ℕ → Ω → ObservedDatum 𝒳 K) (e : GuardEventIndex 𝒳 K)
    (hn : 0 < n) (ω : Ω) :
    empiricalFreq O (guardEvent e) n ω -
        Pobs.real {o | guardEvent e o = true} =
      (n : ℝ)⁻¹ * ∑ i : Fin n, centeredGuardIndicator Pobs e (O i ω) := by
  unfold empiricalFreq centeredGuardIndicator
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (if guardEvent e (O i ω) then (1 : ℝ) else 0) -
      Pobs.real {u | guardEvent e u = true}) n]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

private lemma centeredGuardIndicator_comp_memLp
    (O : ℕ → Ω → ObservedDatum 𝒳 K) (hO : Measurable (O i))
    (hLaw : μ.map (O i) = Pobs) [IsProbabilityMeasure Pobs]
    (e : GuardEventIndex 𝒳 K) :
    MemLp (fun ω => centeredGuardIndicator Pobs e (O i ω)) 2 μ := by
  have hmp : MeasurePreserving (O i) μ Pobs := ⟨hO, hLaw⟩
  exact (centeredGuardIndicator_memLp Pobs e).comp_measurePreserving hmp

private lemma integral_centeredGuardIndicator_comp
    (O : ℕ → Ω → ObservedDatum 𝒳 K) (hO : Measurable (O i))
    (hLaw : μ.map (O i) = Pobs) [IsProbabilityMeasure Pobs]
    (e : GuardEventIndex 𝒳 K) :
    ∫ ω, centeredGuardIndicator Pobs e (O i ω) ∂μ = 0 := by
  rw [← integral_map hO.aemeasurable (by
    unfold centeredGuardIndicator
    fun_prop), hLaw, integral_centeredGuardIndicator]

/-- The centered-indicator second-moment route gives the sharp finite-union probability bound for the maximal guard-event deviation. Given [the stated hypotheses](hyp:hsamp,hn,ht), [the stated conclusion follows](goal). -/
theorem maxDeviation_tail_le
    (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (Pobs : GuardMeasure 𝒳 K)
    [DiscreteMeasurableSpace (ObservedDatum 𝒳 K)] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure Pobs]
    (hsamp : FiniteIidSampling n μ Pobs O) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t < maxDeviation O Pobs n ω} ≤
      (guardEvents 𝒳 K).card / (4 * (n : ℝ) * t ^ 2) := by
  classical
  have heTail (e : GuardEventIndex 𝒳 K) :
      μ.real {ω | t ≤ |empiricalFreq O (guardEvent e) n ω -
          Pobs.real {o | guardEvent e o = true}|} ≤ 1 / (4 * (n : ℝ) * t ^ 2) := by
    let X : Fin n → Ω → ℝ := fun i ω => centeredGuardIndicator Pobs e (O i ω)
    let D : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ i : Fin n, X i ω
    have hXLp : ∀ i, MemLp (X i) 2 μ := by
      intro i
      exact centeredGuardIndicator_comp_memLp O
        (hsamp.measurable i i.isLt) (hsamp.law i i.isLt) e
    have hXindep : ProbabilityTheory.iIndepFun X μ := by
      exact hsamp.indep.comp (fun _ => centeredGuardIndicator Pobs e)
        (fun _ => by unfold centeredGuardIndicator; fun_prop)
    have hDLp : MemLp D 2 μ := by
      exact (memLp_finsetSum Finset.univ fun i _ => hXLp i).const_mul _
    have hDmean : ∫ ω, D ω ∂μ = 0 := by
      dsimp [D, X]
      rw [integral_const_mul, integral_finset_sum _
        (fun i _ => (hXLp i).integrable (by norm_num))]
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro i _
      exact integral_centeredGuardIndicator_comp O
        (hsamp.measurable i i.isLt) (hsamp.law i i.isLt) e
    have hvarX : ∀ i, ProbabilityTheory.variance (X i) μ ≤ 1 / 4 := by
      intro i
      have hvar := ProbabilityTheory.variance_le_expectation_sq
        (hXLp i).aestronglyMeasurable
      have hsq : ∫ ω, (X i ω) ^ 2 ∂μ =
          Pobs.real {o | guardEvent e o = true} *
            (1 - Pobs.real {o | guardEvent e o = true}) := by
        change ∫ ω, centeredGuardIndicator Pobs e (O i ω) ^ 2 ∂μ = _
        rw [← integral_map (μ := μ) (φ := O i)
          (f := fun o => centeredGuardIndicator Pobs e o ^ 2)
          (hsamp.measurable i i.isLt).aemeasurable (by fun_prop),
          hsamp.law i i.isLt, integral_centeredGuardIndicator_sq]
      have hp := measureReal_le_one (μ := Pobs) (s := {o | guardEvent e o = true})
      have hp0 : 0 ≤ Pobs.real {o | guardEvent e o = true} := measureReal_nonneg
      calc
        ProbabilityTheory.variance (X i) μ ≤ ∫ ω, (X i ω) ^ 2 ∂μ := by
          simpa only [Pi.pow_apply] using hvar
        _ = _ := hsq
        _ ≤ 1 / 4 := by
          nlinarith [sq_nonneg (Pobs.real {o | guardEvent e o = true} - 1 / 2)]
    have hvarD : ProbabilityTheory.variance D μ ≤ 1 / (4 * (n : ℝ)) := by
      have hpair : Set.Pairwise
          (↑(Finset.univ : Finset (Fin n)) : Set (Fin n))
          (fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ) := by
        intro i _ j _ hij
        exact hXindep.indepFun hij
      have hsum := ProbabilityTheory.IndepFun.variance_sum
        (s := (Finset.univ : Finset (Fin n)))
        (fun i _ => hXLp i) hpair
      have hsum' : ProbabilityTheory.variance (fun ω => ∑ i : Fin n, X i ω) μ =
          ∑ i : Fin n, ProbabilityTheory.variance (X i) μ := by
        calc
          ProbabilityTheory.variance (fun ω => ∑ i : Fin n, X i ω) μ =
              ProbabilityTheory.variance (∑ i : Fin n, X i) μ := by
                congr 2
                funext ω
                simp
          _ = _ := hsum
      dsimp [D]
      rw [ProbabilityTheory.variance_const_mul, hsum']
      have hsumle : ∑ i : Fin n, ProbabilityTheory.variance (X i) μ ≤
          (n : ℝ) / 4 := by
        calc
          _ ≤ ∑ _i : Fin n, (1 / 4 : ℝ) := Finset.sum_le_sum fun i _ => hvarX i
          _ = (n : ℝ) / 4 := by simp [nsmul_eq_mul]; ring
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      calc
        (n : ℝ)⁻¹ ^ 2 * ∑ i : Fin n, ProbabilityTheory.variance (X i) μ ≤
            (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left hsumle (sq_nonneg _)
        _ = 1 / (4 * (n : ℝ)) := by field_simp
    have htail := ProbabilityTheory.meas_ge_le_variance_div_sq hDLp ht
    have hp := measureReal_le_one (μ := Pobs)
      (s := {o | guardEvent e o = true})
    have hp0 : 0 ≤ Pobs.real {o | guardEvent e o = true} := measureReal_nonneg
    have hvar : Pobs.real {o | guardEvent e o = true} *
        (1 - Pobs.real {o | guardEvent e o = true}) ≤ 1 / 4 := by
      nlinarith [sq_nonneg (Pobs.real {o | guardEvent e o = true} - 1 / 2)]
    have hset : {ω | t ≤ |empiricalFreq O (guardEvent e) n ω -
          Pobs.real {o | guardEvent e o = true}|} =
        {ω | t ≤ |D ω - ∫ ω, D ω ∂μ|} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [hDmean, sub_zero, empiricalFreq_sub_eq_centered_sum O e hn]
    rw [hset, Measure.real]
    have hden : 0 < (n : ℝ) * t ^ 2 := mul_pos (by exact_mod_cast hn) (sq_pos_of_pos ht)
    calc
      (μ {ω | t ≤ |D ω - ∫ ω, D ω ∂μ|}).toReal ≤
          (ENNReal.ofReal (ProbabilityTheory.variance D μ / t ^ 2)).toReal :=
        (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 htail
      _ = ProbabilityTheory.variance D μ / t ^ 2 := ENNReal.toReal_ofReal
        (div_nonneg (ProbabilityTheory.variance_nonneg _ _) (sq_nonneg _))
      _ ≤ 1 / (4 * (n : ℝ) * t ^ 2) := by
        calc
          ProbabilityTheory.variance D μ / t ^ 2 ≤
              (1 / (4 * (n : ℝ))) / t ^ 2 :=
            div_le_div_of_nonneg_right hvarD (sq_nonneg _)
          _ = _ := by field_simp
  have hnonempty : (guardEvents 𝒳 K).Nonempty := by
    refine ⟨GuardEventIndex.cell (Classical.choice inferInstance), ?_⟩
    simp [guardEvents]
  have hsubset : {ω | t < maxDeviation O Pobs n ω} ⊆
      ⋃ e : GuardEventIndex 𝒳 K,
        {ω | t ≤ |empiricalFreq O (guardEvent e) n ω -
          Pobs.real {o | guardEvent e o = true}|} := by
    intro ω hω
    change t < maxDeviation O Pobs n ω at hω
    unfold maxDeviation at hω
    simp only [dif_pos hnonempty] at hω
    obtain ⟨e, he, heval⟩ := (Finset.lt_sup'_iff hnonempty).mp hω
    exact Set.mem_iUnion.2 ⟨e, le_of_lt heval⟩
  calc
    μ.real {ω | t < maxDeviation O Pobs n ω} ≤
        μ.real (⋃ e : GuardEventIndex 𝒳 K,
          {ω | t ≤ |empiricalFreq O (guardEvent e) n ω -
            Pobs.real {o | guardEvent e o = true}|}) := measureReal_mono hsubset
    _ ≤ ∑ e : GuardEventIndex 𝒳 K,
        μ.real {ω | t ≤ |empiricalFreq O (guardEvent e) n ω -
          Pobs.real {o | guardEvent e o = true}|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _e : GuardEventIndex 𝒳 K, 1 / (4 * (n : ℝ) * t ^ 2) :=
      Finset.sum_le_sum fun e he => heTail e
    _ = (guardEvents 𝒳 K).card / (4 * (n : ℝ) * t ^ 2) := by
      simp [guardEvents, nsmul_eq_mul]
      ring

/-- Given [the stated hypotheses](hyp:hsamp,hn,hα), [the max deviation union threshold tail le property holds](goal). -/
theorem maxDeviation_unionThreshold_tail_le
    (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (Pobs : GuardMeasure 𝒳 K) [IsProbabilityMeasure Pobs]
    (hsamp : FiniteIidSampling n μ Pobs O)
    (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) :
    μ.real {ω | unionThreshold 𝒳 K n α < maxDeviation O Pobs n ω} ≤ α := by
  letI : IsProbabilityMeasure μ := hsamp.isProbabilityMeasure
  have hcard : 0 < (guardEvents 𝒳 K).card := by
    rw [Finset.card_pos]
    exact ⟨.cell (Classical.choice inferInstance), by simp [guardEvents]⟩
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hfrac : 0 < (guardEvents 𝒳 K).card / (4 * (n : ℝ) * α) := by positivity
  have hb : 0 < unionThreshold 𝒳 K n α := Real.sqrt_pos.2 hfrac
  have ht := maxDeviation_tail_le O Pobs hsamp
    (lt_of_lt_of_le Nat.zero_lt_one hn)
    (unionThreshold 𝒳 K n α) hb
  calc
    _ ≤ (guardEvents 𝒳 K).card /
        (4 * (n : ℝ) * (unionThreshold 𝒳 K n α) ^ 2) := ht
    _ = α := by
      unfold unionThreshold
      rw [Real.sq_sqrt hfrac.le]
      field_simp

/-- Every event coordinate is bounded by the finite guard maximum. [the stated conclusion follows](goal). -/
theorem guardEvent_deviation_le_maxDeviation
    (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (Pobs : GuardMeasure 𝒳 K) [IsProbabilityMeasure Pobs]
    (n : ℕ) (ω : Ω) (e : GuardEventIndex 𝒳 K) :
    |empiricalFreq O (guardEvent e) n ω -
      Pobs.real {o | guardEvent e o = true}| ≤ maxDeviation O Pobs n ω := by
  classical
  have hnon : (guardEvents 𝒳 K).Nonempty := by
    exact ⟨.cell (Classical.choice inferInstance), by simp [guardEvents]⟩
  unfold maxDeviation
  rw [dif_pos hnon]
  exact Finset.le_sup' (fun E : GuardEventIndex 𝒳 K =>
    |empiricalFreq O (guardEvent E) n ω -
      Pobs.real {o | guardEvent E o = true}|) (show e ∈ (guardEvents 𝒳 K) by
    exact Finset.mem_univ e)

/-- [the empirical freq nonneg property holds](goal). -/
theorem empiricalFreq_nonneg (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (E : ObservedDatum 𝒳 K → Bool) (n : ℕ) (ω : Ω) :
    0 ≤ empiricalFreq O E n ω := by
  unfold empiricalFreq
  positivity

/-- Given [the stated hypotheses](hyp:hEF), [the empirical freq mono property holds](goal). -/
theorem empiricalFreq_mono (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (E F : ObservedDatum 𝒳 K → Bool)
    (hEF : ∀ o, E o = true → F o = true) (n : ℕ) (ω : Ω) :
    empiricalFreq O E n ω ≤ empiricalFreq O F n ω := by
  unfold empiricalFreq
  gcongr with r hr
  by_cases hE : E (O r ω) = true
  · simp [hE, hEF _ hE]
  · rw [if_neg hE]
    split <;> norm_num

/-- Given [the stated hypotheses](hyp:hO), [the empirical freq whenever prefix map is measurable](goal). -/
theorem measurable_empiricalFreq_of_prefix
    (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (hO : ∀ i, i < n → Measurable (O i))
    (E : ObservedDatum 𝒳 K → Bool) :
    Measurable (empiricalFreq O E n) := by
  unfold empiricalFreq
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.ite
  · exact ((MeasurableSet.of_discrete : MeasurableSet {o | E o = true}).preimage
      (hO i (by simpa using hi)))
  · exact measurable_const
  · exact measurable_const

/-- Given [the stated hypotheses](hyp:hO), [the max deviation whenever prefix map is measurable](goal). -/
theorem measurable_maxDeviation_of_prefix
    (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (Pobs : GuardMeasure 𝒳 K) [IsProbabilityMeasure Pobs]
    (hO : ∀ i, i < n → Measurable (O i)) :
    Measurable (maxDeviation O Pobs n) := by
  classical
  unfold maxDeviation
  split_ifs with hnon
  · let f : GuardEventIndex 𝒳 K → (Ω → ℝ) := fun e ω =>
      |empiricalFreq O (guardEvent e) n ω -
        Pobs.real {o | guardEvent e o = true}|
    rw [show (fun ω => (guardEvents 𝒳 K).sup' hnon
        (fun e => |empiricalFreq O (guardEvent e) n ω -
          Pobs.real {o | guardEvent e o = true}|)) =
      (guardEvents 𝒳 K).sup' hnon f by
        funext ω
        exact (Finset.sup'_apply hnon f ω).symm]
    apply Finset.measurable_sup' hnon
    intro e he
    have hs : Measurable (fun ω => empiricalFreq O (guardEvent e) n ω -
        Pobs.real {o | guardEvent e o = true}) :=
      (measurable_empiricalFreq_of_prefix O hO (guardEvent e)).sub measurable_const
    simpa only [Real.norm_eq_abs] using hs.norm
  · exact measurable_const

private lemma empiricalConditional_nonneg_le_one {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ empiricalConditional a b ∧ empiricalConditional a b ≤ 1 := by
  unfold empiricalConditional
  by_cases hb : 0 < b
  · rw [if_pos hb]
    exact ⟨div_nonneg ha hb.le, (div_le_one hb).2 hab⟩
  · rw [if_neg hb]
    simp

/-- Stability of one cell-probability-weighted conditional probability. The small-cell branch avoids division by a nearly zero arm probability. Given [the stated hypotheses](hyp:hδ,hε,hεhalf,hp,hph,ha,hap,hoverlap,hb,hba,hah,hbh,hbhah,hpdev,hadev,hbdev), [the stated conclusion follows](goal). -/
lemma weightedConditional_stable
    {p ph a ah b bh δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hp : 0 ≤ p) (hph : 0 ≤ ph)
    (ha : 0 ≤ a) (hap : a ≤ p) (hoverlap : ε * p ≤ a)
    (hb : 0 ≤ b) (hba : b ≤ a)
    (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hbhah : bh ≤ ah)
    (hpdev : |ph - p| ≤ δ) (hadev : |ah - a| ≤ δ)
    (hbdev : |bh - b| ≤ δ) :
    |ph * empiricalConditional bh ah - p * empiricalConditional b a| ≤
      8 * δ / ε ^ 2 := by
  have hph_le : ph ≤ p + δ := by
    have := (le_abs_self (ph - p)).trans hpdev
    linarith
  have hεle : ε ≤ 1 := by linarith
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  by_cases hδzero : δ = 0
  · subst δ
    have hphEq : ph = p := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hpdev (abs_nonneg _)))
    have hahEq : ah = a := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hadev (abs_nonneg _)))
    have hbhEq : bh = b := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hbdev (abs_nonneg _)))
    subst ph; subst ah; subst bh
    simp
  by_cases hsmall : p < 4 * δ / ε
  · obtain ⟨hh0, hh1⟩ := empiricalConditional_nonneg_le_one hbh hbhah
    obtain ⟨hc0, hc1⟩ := empiricalConditional_nonneg_le_one hb hba
    have hleft0 : 0 ≤ ph * empiricalConditional bh ah := mul_nonneg hph hh0
    have hright0 : 0 ≤ p * empiricalConditional b a := mul_nonneg hp hc0
    have hleft : ph * empiricalConditional bh ah ≤ ph := by
      simpa using mul_le_of_le_one_right hph hh1
    have hright : p * empiricalConditional b a ≤ p := by
      simpa using mul_le_of_le_one_right hp hc1
    rw [abs_le]
    constructor
    · have hbound : ε ^ 2 * (p + ph) ≤ 8 * δ := by
        have hpε : ε * p < 4 * δ := by
          simpa [mul_comm] using (lt_div_iff₀ hε).mp hsmall
        have hεsq_le : ε ^ 2 ≤ ε := by nlinarith
        nlinarith [mul_nonneg hεsq.le hp, mul_nonneg hεsq.le hph]
      have : p + ph ≤ 8 * δ / ε ^ 2 :=
        (le_div_iff₀ hεsq).2 (by simpa [mul_comm] using hbound)
      linarith
    · have hbound : ε ^ 2 * (p + ph) ≤ 8 * δ := by
        have hpε : ε * p < 4 * δ := by
          simpa [mul_comm] using (lt_div_iff₀ hε).mp hsmall
        have hεsq_le : ε ^ 2 ≤ ε := by nlinarith
        nlinarith [mul_nonneg hεsq.le hp, mul_nonneg hεsq.le hph]
      have : p + ph ≤ 8 * δ / ε ^ 2 :=
        (le_div_iff₀ hεsq).2 (by simpa [mul_comm] using hbound)
      linarith
  · have hlarge : 4 * δ / ε ≤ p := le_of_not_gt hsmall
    have hpε : 4 * δ ≤ ε * p := by
      simpa [mul_comm] using (div_le_iff₀ hε).mp hlarge
    have ha4 : 4 * δ ≤ a := hpε.trans hoverlap
    have haPos : 0 < a := by
      have hdpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδzero)
      linarith
    have hahLower : a - δ ≤ ah := by
      have := (neg_le_of_abs_le hadev)
      linarith
    have hahPos : 0 < ah := by linarith
    rw [empiricalConditional, if_pos hahPos, empiricalConditional, if_pos haPos]
    have hratio0 : 0 ≤ bh / ah := div_nonneg hbh hahPos.le
    have hratio1 : bh / ah ≤ 1 := (div_le_one hahPos).2 hbhah
    have hpDiff : |ph - p| * (bh / ah) ≤ δ := by
      exact (mul_le_mul_of_nonneg_right hpdev hratio0).trans
        (by simpa [mul_comm] using mul_le_of_le_one_left hδ hratio1)
    have hcross : |bh * a - b * ah| ≤ 2 * δ * a := by
      calc
        |bh * a - b * ah| = |(bh - b) * a + b * (a - ah)| := by ring_nf
        _ ≤ |bh - b| * a + b * |a - ah| := by
          calc
            _ ≤ |(bh - b) * a| + |b * (a - ah)| := abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha,
              abs_of_nonneg hb]
        _ ≤ δ * a + a * δ := add_le_add
          (mul_le_mul_of_nonneg_right hbdev ha)
          (mul_le_mul (hba) (by simpa [abs_sub_comm] using hadev)
            (abs_nonneg _) ha)
        _ = 2 * δ * a := by ring
    have hratioDiff : |bh / ah - b / a| ≤ 8 * δ / (3 * a) := by
      rw [show bh / ah - b / a = (bh * a - b * ah) / (ah * a) by
        field_simp, abs_div, abs_mul, abs_of_pos hahPos,
        abs_of_pos haPos]
      have hdenLower : 3 * a ^ 2 ≤ 4 * (ah * a) := by
        have hm := mul_le_mul_of_nonneg_right hahLower ha
        nlinarith
      have hcross' : 3 * a * |bh * a - b * ah| ≤
          8 * δ * (ah * a) := by
        have hc := mul_le_mul_of_nonneg_left hcross
          (mul_nonneg (show (0 : ℝ) ≤ 3 by norm_num) ha)
        have hd := mul_le_mul_of_nonneg_left hdenLower
          (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hδ)
        nlinarith
      apply (div_le_div_iff₀ (mul_pos hahPos haPos)
        (mul_pos (by norm_num) haPos)).2
      nlinarith
    have hpOverA : p / a ≤ 1 / ε := by
      apply (div_le_div_iff₀ haPos hε).2
      simpa [mul_comm] using hoverlap
    calc
      |ph * (bh / ah) - p * (b / a)| =
          |(ph - p) * (bh / ah) + p * (bh / ah - b / a)| := by ring_nf
      _ ≤ |ph - p| * (bh / ah) + p * |bh / ah - b / a| := by
        calc
          _ ≤ |(ph - p) * (bh / ah)| + |p * (bh / ah - b / a)| :=
            abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hp,
            abs_of_nonneg hratio0]
      _ ≤ δ + p * (8 * δ / (3 * a)) := by gcongr
      _ ≤ 8 * δ / ε ^ 2 := by
        have hpa : p * (8 * δ / (3 * a)) ≤ 8 * δ / (3 * ε) := by
          calc
            p * (8 * δ / (3 * a)) = (8 * δ / 3) * (p / a) := by field_simp
            _ ≤ (8 * δ / 3) * (1 / ε) := by
              gcongr
            _ = 8 * δ / (3 * ε) := by ring
        have hcoarse : δ + 8 * δ / (3 * ε) ≤ 8 * δ / ε ^ 2 := by
          field_simp [hε.ne']
          nlinarith [mul_nonneg hδ (sq_nonneg ε)]
        exact (by linarith : δ + p * (8 * δ / (3 * a)) ≤
          δ + 8 * δ / (3 * ε)) |>.trans hcoarse

/-- Multiplication by nonnegative cell masses commutes with positive-part projection, which is one-Lipschitz against a nonnegative population target. Given [the stated hypotheses](hyp:hp,hph,ha,hR), [the stated conclusion follows](goal). -/
theorem weighted_positivePart_stable {p ph a ah R : ℝ}
    (hp : 0 ≤ p) (hph : 0 ≤ ph) (ha : 0 ≤ a)
    (hR : |ph * ah - p * a| ≤ R) :
    |ph * max ah 0 - p * a| ≤ R := by
  rw [mul_max_of_nonneg _ _ hph, mul_zero]
  by_cases hah : 0 ≤ ph * ah
  · rw [max_eq_left hah]
    exact hR
  · rw [max_eq_right (le_of_not_ge hah)]
    have hpa : 0 ≤ p * a := mul_nonneg hp ha
    rw [abs_of_nonpos (by linarith : ph * ah - p * a ≤ 0)] at hR
    rw [zero_sub, abs_neg, abs_of_nonneg hpa]
    linarith

/-- Elementary denominator-safe quotient perturbation bound used by both endpoints after screening. Given [the stated hypotheses](hyp:hm,hM,hN0,hNM,hA,hAsmall,hMerr,hNerr), [the stated conclusion follows](goal). -/
theorem ratio_error_le_three {M Mh N Nh A m : ℝ}
    (hm : 0 < m) (hM : m ≤ M) (hN0 : 0 ≤ N) (hNM : N ≤ M)
    (hA : 0 ≤ A) (hAsmall : 4 * A < m)
    (hMerr : |Mh - M| ≤ A) (hNerr : |Nh - N| ≤ A) :
    0 < Mh ∧ |Nh / Mh - N / M| ≤ 3 * A / m := by
  have hMpos : 0 < M := lt_of_lt_of_le hm hM
  have hMhLower : M - A ≤ Mh := by
    have := (abs_le.mp hMerr).1
    linarith
  have hMh : 0 < Mh := by nlinarith
  refine ⟨hMh, ?_⟩
  rw [show Nh / Mh - N / M = (Nh - N) / Mh +
      N * (M - Mh) / (M * Mh) by field_simp; ring]
  calc
    |(Nh - N) / Mh + N * (M - Mh) / (M * Mh)| ≤
        |(Nh - N) / Mh| + |N * (M - Mh) / (M * Mh)| := abs_add_le _ _
    _ =
        |Nh - N| / Mh + N * |M - Mh| / (M * Mh) := by
      rw [abs_div, abs_of_pos hMh, abs_div, abs_mul,
        abs_of_nonneg hN0, abs_mul, abs_of_pos hMpos, abs_of_pos hMh]
    _ ≤ A / Mh + M * A / (M * Mh) := by
      gcongr
      · simpa [abs_sub_comm] using hMerr
    _ = 2 * A / Mh := by field_simp; ring
    _ ≤ 3 * A / m := by
      have hhalf : m / 2 < Mh := by nlinarith
      exact (div_le_div_iff₀ hMh hm).2 (by nlinarith)

private lemma abs_finset_sum_sub_le {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) (R : ℝ) (h : ∀ i, |f i - g i| ≤ R) :
    |∑ i, f i - ∑ i, g i| ≤ Fintype.card ι * R := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (f i - g i)| ≤ ∑ i, |f i - g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, R := Finset.sum_le_sum fun i hi => h i
    _ = Fintype.card ι * R := by simp [nsmul_eq_mul]

private lemma abs_sup'_sub_sup'_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) (R : ℝ) (hR : 0 ≤ R) (h : ∀ i, |f i - g i| ≤ R) :
    |Finset.univ.sup' Finset.univ_nonempty f -
      Finset.univ.sup' Finset.univ_nonempty g| ≤ R := by
  rw [abs_le]
  constructor
  · have hs : Finset.univ.sup' Finset.univ_nonempty g ≤
        Finset.univ.sup' Finset.univ_nonempty f + R := by
      apply Finset.sup'_le Finset.univ_nonempty
      intro i hi
      have hi' := (abs_le.mp (h i)).1
      have hle := Finset.le_sup' f (by simp : i ∈ (Finset.univ : Finset ι))
      linarith
    linarith
  · have hs : Finset.univ.sup' Finset.univ_nonempty f ≤
        Finset.univ.sup' Finset.univ_nonempty g + R := by
      apply Finset.sup'_le Finset.univ_nonempty
      intro i hi
      have hi' := (abs_le.mp (h i)).2
      have hle := Finset.le_sup' g (by simp : i ∈ (Finset.univ : Finset ι))
      linarith
    linarith

private lemma abs_inf'_sub_inf'_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) (R : ℝ) (hR : 0 ≤ R) (h : ∀ i, |f i - g i| ≤ R) :
    |Finset.univ.inf' Finset.univ_nonempty f -
      Finset.univ.inf' Finset.univ_nonempty g| ≤ R := by
  rw [abs_le]
  constructor
  · obtain ⟨i, hi, hfi⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty f
    have hgle := Finset.inf'_le g hi
    have hdiff := (abs_le.mp (h i)).1
    rw [hfi]
    linarith
  · obtain ⟨i, hi, hgi⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty g
    have hfle := Finset.inf'_le f hi
    have hdiff := (abs_le.mp (h i)).2
    rw [hgi]
    linarith

private lemma abs_min_sub_min_le {a b c d R : ℝ} (hR : 0 ≤ R)
    (hac : |a - c| ≤ R) (hbd : |b - d| ≤ R) :
    |min a b - min c d| ≤ R := by
  rw [abs_le] at hac hbd ⊢
  by_cases hab : a ≤ b <;> by_cases hcd : c ≤ d
  · simp only [min_eq_left hab, min_eq_left hcd]
    exact hac
  · have hdc : d ≤ c := le_of_not_ge hcd
    simp only [min_eq_left hab, min_eq_right hdc]
    constructor <;> linarith [hac.1, hbd.2]
  · have hba : b ≤ a := le_of_not_ge hab
    simp only [min_eq_right hba, min_eq_left hcd]
    constructor <;> linarith [hac.2, hbd.1]
  · have hba : b ≤ a := le_of_not_ge hab
    have hdc : d ≤ c := le_of_not_ge hcd
    simp only [min_eq_right hba, min_eq_right hdc]
    exact hbd

/-- Coordinatewise perturbations of nonnegative capacities control every branch-free mass and threshold-cut functional without choosing an active face. Given [the stated hypotheses](hyp:he,hcoord), [the stated conclusion follows](goal). -/
theorem capacity_functionals_lipschitz
    (c c' : Capacities 𝒳 K) (e : ℝ) (he : 0 ≤ e)
    (hcoord : ∀ x i, |c'.lower x i - c.lower x i| ≤ e ∧
      |c'.upper x i - c.upper x i| ≤ e) :
    ∀ x, |c'.mass x - c.mass x| ≤ K * e ∧
      |c'.benefitLower x - c.benefitLower x| ≤ 4 * K * e ∧
      |c'.benefitUpper x - c.benefitUpper x| ≤ 4 * K * e := by
  classical
  intro x
  have hq0 : |c'.q0 x - c.q0 x| ≤ K * e := by
    unfold Capacities.q0
    simpa using abs_finset_sum_sub_le (c'.lower x) (c.lower x) e
      (fun i => (hcoord x i).1)
  have hq1 : |c'.q1 x - c.q1 x| ≤ K * e := by
    unfold Capacities.q1
    simpa using abs_finset_sum_sub_le (c'.upper x) (c.upper x) e
      (fun i => (hcoord x i).2)
  have hKe : 0 ≤ (K : ℝ) * e := mul_nonneg (Nat.cast_nonneg _) he
  have hm : |c'.mass x - c.mass x| ≤ K * e := by
    unfold Capacities.mass
    exact abs_min_sub_min_le hKe hq0 hq1
  have hprefLower (k : Fin K) :
      |c'.lowerLe x k - c.lowerLe x k| ≤ K * e := by
    unfold Capacities.lowerLe
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i with i ≤ k, (c'.lower x i - c.lower x i)| ≤
          ∑ i with i ≤ k, |c'.lower x i - c.lower x i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i with i ≤ k, e := Finset.sum_le_sum fun i hi => (hcoord x i).1
      _ ≤ ∑ _i : Fin K, e := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (by intro i hi; simp)
        intro i hi hnot; exact he
      _ = K * e := by simp [nsmul_eq_mul]
  have hprefUpper (k : Fin K) :
      |c'.upperLe x k - c.upperLe x k| ≤ K * e := by
    unfold Capacities.upperLe
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i with i ≤ k, (c'.upper x i - c.upper x i)| ≤
          ∑ i with i ≤ k, |c'.upper x i - c.upper x i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i with i ≤ k, e := Finset.sum_le_sum fun i hi => (hcoord x i).2
      _ ≤ ∑ _i : Fin K, e := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (by intro i hi; simp)
        intro i hi hnot; exact he
      _ = K * e := by simp [nsmul_eq_mul]
  have hstrictLower (k : Fin K) :
      |c'.lowerLt x k - c.lowerLt x k| ≤ K * e := by
    unfold Capacities.lowerLt
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i with i < k, (c'.lower x i - c.lower x i)| ≤
          ∑ i with i < k, |c'.lower x i - c.lower x i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i with i < k, e := Finset.sum_le_sum fun i hi => (hcoord x i).1
      _ ≤ ∑ _i : Fin K, e := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (by intro i hi; simp)
        intro i hi hnot; exact he
      _ = K * e := by simp [nsmul_eq_mul]
  have htailUpper (k : Fin K) :
      |c'.upperGt x k - c.upperGt x k| ≤ K * e := by
    unfold Capacities.upperGt
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i with k < i, (c'.upper x i - c.upper x i)| ≤
          ∑ i with k < i, |c'.upper x i - c.upper x i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i with k < i, e := Finset.sum_le_sum fun i hi => (hcoord x i).2
      _ ≤ ∑ _i : Fin K, e := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (by intro i hi; simp)
        intro i hi hnot; exact he
      _ = K * e := by simp [nsmul_eq_mul]
  have hgap : |c'.gap x - c.gap x| ≤ 2 * K * e := by
    unfold Capacities.gap
    rw [show c'.q1 x - c'.q0 x - (c.q1 x - c.q0 x) =
      (c'.q1 x - c.q1 x) - (c'.q0 x - c.q0 x) by ring]
    calc
      |(c'.q1 x - c.q1 x) - (c'.q0 x - c.q0 x)| ≤
          |c'.q1 x - c.q1 x| + |c'.q0 x - c.q0 x| := abs_sub _ _
      _ ≤ K * e + K * e := add_le_add hq1 hq0
      _ = 2 * K * e := by ring
  have h2Ke : (0 : ℝ) ≤ 2 * (K : ℝ) * e :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) he
  have hgapMin : |min (c'.gap x) 0 - min (c.gap x) 0| ≤ 2 * K * e :=
    abs_min_sub_min_le h2Ke hgap (by simpa using h2Ke)
  have hLowerCand : ∀ t : Option (Fin K),
      |(match t with
        | none => 0
        | some k => c'.lowerLe x k - c'.upperLe x k + min (c'.gap x) 0) -
       (match t with
        | none => 0
        | some k => c.lowerLe x k - c.upperLe x k + min (c.gap x) 0)| ≤
        4 * K * e := by
    intro t
    cases t with
    | none =>
        have hz : (0 : ℝ) ≤ 4 * (K : ℝ) * e := mul_nonneg
          (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (Nat.cast_nonneg _)) he
        simpa using hz
    | some k =>
        change |(c'.lowerLe x k - c'.upperLe x k + min (c'.gap x) 0) -
          (c.lowerLe x k - c.upperLe x k + min (c.gap x) 0)| ≤ 4 * K * e
        rw [show (c'.lowerLe x k - c'.upperLe x k + min (c'.gap x) 0) -
          (c.lowerLe x k - c.upperLe x k + min (c.gap x) 0) =
          ((c'.lowerLe x k - c.lowerLe x k) -
            (c'.upperLe x k - c.upperLe x k)) +
            (min (c'.gap x) 0 - min (c.gap x) 0) by ring]
        let A : ℝ := c'.lowerLe x k - c.lowerLe x k
        let B : ℝ := c'.upperLe x k - c.upperLe x k
        let C : ℝ := min (c'.gap x) 0 - min (c.gap x) 0
        have hab : |A - B| ≤ |A| + |B| := abs_sub A B
        have habc : |(A - B) + C| ≤ |A - B| + |C| := abs_add_le _ _
        calc
          |(c'.lowerLe x k - c.lowerLe x k) -
              (c'.upperLe x k - c.upperLe x k) +
              (min (c'.gap x) 0 - min (c.gap x) 0)| ≤
              |c'.lowerLe x k - c.lowerLe x k| +
              |c'.upperLe x k - c.upperLe x k| +
              |min (c'.gap x) 0 - min (c.gap x) 0| := by
            change |(A - B) + C| ≤ |A| + |B| + |C|
            nlinarith [habc, hab, abs_nonneg C]
          _ ≤ K * e + K * e + 2 * K * e :=
            add_le_add (add_le_add (hprefLower k) (hprefUpper k)) hgapMin
          _ = 4 * K * e := by ring
  have hBL : |c'.benefitLower x - c.benefitLower x| ≤ 4 * K * e := by
    rw [benefitLower_eq_sup_explicit, benefitLower_eq_sup_explicit]
    exact abs_sup'_sub_sup'_le _ _ _ (by positivity) hLowerCand
  have hUpperCand : ∀ t : Option (Fin K),
      |(match t with
        | none => c'.mass x
        | some k => c'.lowerLt x k + c'.upperGt x k) -
       (match t with
        | none => c.mass x
        | some k => c.lowerLt x k + c.upperGt x k)| ≤ 4 * K * e := by
    intro t
    cases t with
    | none => exact hm.trans (by nlinarith [hKe])
    | some k =>
      change |(c'.lowerLt x k + c'.upperGt x k) -
        (c.lowerLt x k + c.upperGt x k)| ≤ 4 * K * e
      rw [show (c'.lowerLt x k + c'.upperGt x k) -
        (c.lowerLt x k + c.upperGt x k) =
        (c'.lowerLt x k - c.lowerLt x k) +
          (c'.upperGt x k - c.upperGt x k) by ring]
      calc
        |(c'.lowerLt x k - c.lowerLt x k) +
            (c'.upperGt x k - c.upperGt x k)| ≤
            |c'.lowerLt x k - c.lowerLt x k| +
              |c'.upperGt x k - c.upperGt x k| := abs_add_le _ _
        _ ≤ K * e + K * e := add_le_add (hstrictLower k) (htailUpper k)
        _ ≤ 4 * K * e := by nlinarith [hKe]
  have hBU : |c'.benefitUpper x - c.benefitUpper x| ≤ 4 * K * e := by
    rw [benefitUpper_eq_inf_explicit, benefitUpper_eq_inf_explicit]
    exact abs_inf'_sub_inf'_le _ _ _ (by positivity) hUpperCand
  exact ⟨hm, hBL, hBU⟩

/-- Multiply all capacity coordinates in a cell by its nonnegative cell mass. -/
noncomputable def weightedCapacities (p : 𝒳 → ℝ) (c : Capacities 𝒳 K) :
    Capacities 𝒳 K where
  lower x i := p x * c.lower x i
  upper x i := p x * c.upper x i

/-- Given [the stated hypotheses](hyp:hp), [the weighted capacities mass property holds](goal). -/
theorem weightedCapacities_mass (p : 𝒳 → ℝ) (c : Capacities 𝒳 K)
    (hp : ∀ x, 0 ≤ p x) (x : 𝒳) :
    (weightedCapacities p c).mass x = p x * c.mass x := by
  unfold Capacities.mass Capacities.q0 Capacities.q1 weightedCapacities
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_min_of_nonneg _ _ (hp x)]

private lemma sup'_mul_of_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℝ) (hp : 0 ≤ p) (f : ι → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => p * f i) =
      p * Finset.univ.sup' Finset.univ_nonempty f := by
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    intro i hi
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' f hi) hp
  · obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_sup'
      Finset.univ_nonempty f
    rw [hfi]
    exact Finset.le_sup' (fun i : ι => p * f i) hi

private lemma inf'_mul_of_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℝ) (hp : 0 ≤ p) (f : ι → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty (fun i => p * f i) =
      p * Finset.univ.inf' Finset.univ_nonempty f := by
  apply le_antisymm
  · obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_inf'
      Finset.univ_nonempty f
    rw [hfi]
    exact Finset.inf'_le _ hi
  · apply Finset.le_inf' Finset.univ_nonempty
    intro i hi
    exact mul_le_mul_of_nonneg_left (Finset.inf'_le f hi) hp

/-- Given [the stated hypotheses](hyp:hp), [the weighted capacities benefit lower property holds](goal). -/
theorem weightedCapacities_benefitLower (p : 𝒳 → ℝ) (c : Capacities 𝒳 K)
    (hp : ∀ x, 0 ≤ p x) (x : 𝒳) :
    (weightedCapacities p c).benefitLower x = p x * c.benefitLower x := by
  rw [benefitLower_eq_sup_explicit, benefitLower_eq_sup_explicit,
    ← sup'_mul_of_nonneg (p x) (hp x)]
  congr 1
  funext t
  cases t with
  | none => simp
  | some k =>
      unfold Capacities.lowerLe Capacities.upperLe Capacities.gap
        Capacities.q0 Capacities.q1 weightedCapacities
      simp only
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [show p x * ∑ i, c.upper x i - p x * ∑ i, c.lower x i =
        p x * (∑ i, c.upper x i - ∑ i, c.lower x i) by ring]
      have hmin : min (p x * (∑ i, c.upper x i - ∑ i, c.lower x i)) 0 =
          p x * min (∑ i, c.upper x i - ∑ i, c.lower x i) 0 := by
        calc
          _ = min (p x * (∑ i, c.upper x i - ∑ i, c.lower x i))
              (p x * 0) := by simp
          _ = _ := (mul_min_of_nonneg _ _ (hp x)).symm
      rw [hmin]
      ring

/-- Given [the stated hypotheses](hyp:hp), [the weighted capacities benefit upper property holds](goal). -/
theorem weightedCapacities_benefitUpper (p : 𝒳 → ℝ) (c : Capacities 𝒳 K)
    (hp : ∀ x, 0 ≤ p x) (x : 𝒳) :
    (weightedCapacities p c).benefitUpper x = p x * c.benefitUpper x := by
  rw [benefitUpper_eq_inf_explicit, benefitUpper_eq_inf_explicit,
    ← inf'_mul_of_nonneg (p x) (hp x)]
  congr 1
  funext t
  cases t with
  | none => exact weightedCapacities_mass p c hp x
  | some k =>
      unfold Capacities.lowerLt Capacities.upperGt weightedCapacities
      simp only
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring

/-- Coordinatewise weighted-capacity control implies simultaneous aggregate mass and endpoint-numerator control. Given [the stated hypotheses](hyp:he,hp,hph,hcoord), [the stated conclusion follows](goal). -/
theorem weightedCapacity_aggregate_close
    (p ph : 𝒳 → ℝ) (c ch : Capacities 𝒳 K) (e : ℝ) (he : 0 ≤ e)
    (hp : ∀ x, 0 ≤ p x) (hph : ∀ x, 0 ≤ ph x)
    (hcoord : ∀ x i,
      |ph x * ch.lower x i - p x * c.lower x i| ≤ e ∧
      |ph x * ch.upper x i - p x * c.upper x i| ≤ e) :
    |(∑ x, ph x * ch.mass x) - ∑ x, p x * c.mass x| ≤
        4 * K * Fintype.card 𝒳 * e ∧
    |(∑ x, ph x * ch.benefitLower x) - ∑ x, p x * c.benefitLower x| ≤
        4 * K * Fintype.card 𝒳 * e ∧
    |(∑ x, ph x * ch.benefitUpper x) - ∑ x, p x * c.benefitUpper x| ≤
        4 * K * Fintype.card 𝒳 * e := by
  let cw := weightedCapacities p c
  let chw := weightedCapacities ph ch
  have hlip (x) := capacity_functionals_lipschitz cw chw e he
    (fun x i => by simpa [chw, cw, weightedCapacities] using hcoord x i) x
  have hR : 0 ≤ 4 * (K : ℝ) * Fintype.card 𝒳 * e := by positivity
  have hm := abs_finset_sum_sub_le
    (fun x => chw.mass x) (fun x => cw.mass x) (4 * K * e)
    (fun x => (hlip x).1.trans (by
      have : 0 ≤ (K : ℝ) * e := mul_nonneg (Nat.cast_nonneg _) he
      nlinarith))
  have hL := abs_finset_sum_sub_le
    (fun x => chw.benefitLower x) (fun x => cw.benefitLower x) (4 * K * e)
    (fun x => (hlip x).2.1)
  have hU := abs_finset_sum_sub_le
    (fun x => chw.benefitUpper x) (fun x => cw.benefitUpper x) (4 * K * e)
    (fun x => (hlip x).2.2)
  dsimp [chw, cw] at hm hL hU
  simp_rw [weightedCapacities_mass ph ch hph,
    weightedCapacities_mass p c hp] at hm
  simp_rw [weightedCapacities_benefitLower ph ch hph,
    weightedCapacities_benefitLower p c hp] at hL
  simp_rw [weightedCapacities_benefitUpper ph ch hph,
    weightedCapacities_benefitUpper p c hp] at hU
  constructor
  · exact hm.trans (by
      convert le_rfl using 1 <;> ring)
  constructor
  · exact hL.trans (by convert le_rfl using 1 <;> ring)
  · exact hU.trans (by convert le_rfl using 1 <;> ring)

/-- Screening at a positive threshold changes each nonnegative empirical total by at most one threshold unit per cell. Given [the stated hypotheses](hyp:hη,hph,hch,hfullM,hfullL,hfullU), [the stated conclusion follows](goal). -/
theorem screenedCapacity_aggregate_close
    (p ph : 𝒳 → ℝ) (c ch : Capacities 𝒳 K) (η R : ℝ)
    (hη : 0 < η) (hph : ∀ x, 0 ≤ ph x) (hch : ValidCapacities ch)
    (hfullM : |(∑ x, ph x * ch.mass x) - ∑ x, p x * c.mass x| ≤ R)
    (hfullL : |(∑ x, ph x * ch.benefitLower x) -
      ∑ x, p x * c.benefitLower x| ≤ R)
    (hfullU : |(∑ x, ph x * ch.benefitUpper x) -
      ∑ x, p x * c.benefitUpper x| ≤ R) :
    let keep := fun x => if η < ph x * ch.mass x then (1 : ℝ) else 0
    |(∑ x, keep x * ph x * ch.mass x) - ∑ x, p x * c.mass x| ≤
        R + Fintype.card 𝒳 * η ∧
    |(∑ x, keep x * ph x * ch.benefitLower x) -
        ∑ x, p x * c.benefitLower x| ≤ R + Fintype.card 𝒳 * η ∧
    |(∑ x, keep x * ph x * ch.benefitUpper x) -
        ∑ x, p x * c.benefitUpper x| ≤ R + Fintype.card 𝒳 * η := by
  dsimp
  have hmass0 (x) : 0 ≤ ch.mass x := by
    unfold Capacities.mass Capacities.q0 Capacities.q1
    exact le_min (Finset.sum_nonneg fun i _ => hch.1 x i)
      (Finset.sum_nonneg fun i _ => hch.2 x i)
  have htermM (x) :
      |(if η < ph x * ch.mass x then (1 : ℝ) else 0) * ph x * ch.mass x -
        ph x * ch.mass x| ≤ η := by
    by_cases hs : η < ph x * ch.mass x
    · simp [hs, hη.le]
    · rw [if_neg hs, zero_mul, zero_mul, zero_sub, abs_neg,
        abs_of_nonneg (mul_nonneg (hph x) (hmass0 x))]
      exact le_of_not_gt hs
  have htermL (x) :
      |(if η < ph x * ch.mass x then (1 : ℝ) else 0) * ph x *
          ch.benefitLower x - ph x * ch.benefitLower x| ≤ η := by
    by_cases hs : η < ph x * ch.mass x
    · simp [hs, hη.le]
    · rw [if_neg hs, zero_mul, zero_mul, zero_sub, abs_neg,
        abs_of_nonneg (mul_nonneg (hph x) (benefitLower_nonneg ch x))]
      exact (mul_le_mul_of_nonneg_left (benefitLower_le_mass ch hch x)
        (hph x)).trans (le_of_not_gt hs)
  have htermU (x) :
      |(if η < ph x * ch.mass x then (1 : ℝ) else 0) * ph x *
          ch.benefitUpper x - ph x * ch.benefitUpper x| ≤ η := by
    by_cases hs : η < ph x * ch.mass x
    · simp [hs, hη.le]
    · rw [if_neg hs, zero_mul, zero_mul, zero_sub, abs_neg,
        abs_of_nonneg (mul_nonneg (hph x) (benefitUpper_nonneg ch hch x))]
      exact (mul_le_mul_of_nonneg_left (benefitUpper_le_mass ch x)
        (hph x)).trans (le_of_not_gt hs)
  have hsM := abs_finset_sum_sub_le
    (fun x => (if η < ph x * ch.mass x then (1 : ℝ) else 0) * ph x * ch.mass x)
    (fun x => ph x * ch.mass x) η htermM
  have hsL := abs_finset_sum_sub_le
    (fun x => (if η < ph x * ch.mass x then (1 : ℝ) else 0) * ph x *
      ch.benefitLower x) (fun x => ph x * ch.benefitLower x) η htermL
  have hsU := abs_finset_sum_sub_le
    (fun x => (if η < ph x * ch.mass x then (1 : ℝ) else 0) * ph x *
      ch.benefitUpper x) (fun x => ph x * ch.benefitUpper x) η htermU
  constructor
  · rw [show (∑ x, (if η < ph x * ch.mass x then (1 : ℝ) else 0) * ph x *
        ch.mass x) - ∑ x, p x * c.mass x =
      ((∑ x, (if η < ph x * ch.mass x then (1 : ℝ) else 0) * ph x *
        ch.mass x) - ∑ x, ph x * ch.mass x) +
      ((∑ x, ph x * ch.mass x) - ∑ x, p x * c.mass x) by ring]
    exact (abs_add_le _ _).trans ((add_le_add hsM hfullM).trans (by
      rw [add_comm]))
  constructor
  · rw [show (∑ x, (if η < ph x * ch.mass x then (1 : ℝ) else 0) * ph x *
        ch.benefitLower x) - ∑ x, p x * c.benefitLower x =
      ((∑ x, (if η < ph x * ch.mass x then (1 : ℝ) else 0) * ph x *
        ch.benefitLower x) - ∑ x, ph x * ch.benefitLower x) +
      ((∑ x, ph x * ch.benefitLower x) -
        ∑ x, p x * c.benefitLower x) by ring]
    exact (abs_add_le _ _).trans ((add_le_add hsL hfullL).trans (by
      rw [add_comm]))
  · rw [show (∑ x, (if η < ph x * ch.mass x then (1 : ℝ) else 0) * ph x *
        ch.benefitUpper x) - ∑ x, p x * c.benefitUpper x =
      ((∑ x, (if η < ph x * ch.mass x then (1 : ℝ) else 0) * ph x *
        ch.benefitUpper x) - ∑ x, ph x * ch.benefitUpper x) +
      ((∑ x, ph x * ch.benefitUpper x) -
        ∑ x, p x * c.benefitUpper x) by ring]
    exact (abs_add_le _ _).trans ((add_le_add hsU hfullU).trans (by
      rw [add_comm]))

/-- The atom-mass-vector construction exactly recovers the observable conditional-probability capacities of a finite observed law. [the stated conclusion follows](goal). -/
theorem capacitiesFromMassVector_measureReal
    (Pobs : Measure (ObservedDatum 𝒳 K)) [IsFiniteMeasure Pobs] :
    capacitiesFromMassVector (fun o => Pobs.real {o}) =
      observableCapacities Pobs := by
  classical
  unfold observableCapacities observableCapacityContrasts
  rw [Capacities.mk.injEq]
  constructor
  · funext x i
    have hden (z : Bool) :
        {o : ObservedDatum 𝒳 K | decide (o.cell = x ∧ o.instrument = z) = true} =
          {o | o.cell = x ∧ o.instrument = z} := by ext o; simp
    have hnum (z treatment : Bool) :
        {o : ObservedDatum 𝒳 K |
            decide (o.cell = x ∧ o.instrument = z ∧ o.treatment = treatment ∧
              o.selected = true ∧ o.outcome = some i) = true} =
          {o | o.cell = x ∧ o.treatment = treatment ∧ o.selected = true ∧
              o.outcome = some i} ∩ {o | o.cell = x ∧ o.instrument = z} := by
      ext o
      simp [and_assoc, and_left_comm, and_comm]
    change empiricalConditional
        (massVectorSum (fun o => Pobs.real {o}) (fun o => decide
          (o.cell = x ∧ o.instrument = false ∧ o.treatment = false ∧
            o.selected = true ∧ o.outcome = some i)))
        (massVectorSum (fun o => Pobs.real {o}) (fun o => decide
          (o.cell = x ∧ o.instrument = false))) -
      empiricalConditional
        (massVectorSum (fun o => Pobs.real {o}) (fun o => decide
          (o.cell = x ∧ o.instrument = true ∧ o.treatment = false ∧
            o.selected = true ∧ o.outcome = some i)))
        (massVectorSum (fun o => Pobs.real {o}) (fun o => decide
          (o.cell = x ∧ o.instrument = true))) =
      conditionalReal Pobs
          {o | o.cell = x ∧ o.treatment = false ∧ o.selected = true ∧
            o.outcome = some i} {o | o.cell = x ∧ o.instrument = false} -
        conditionalReal Pobs
          {o | o.cell = x ∧ o.treatment = false ∧ o.selected = true ∧
            o.outcome = some i} {o | o.cell = x ∧ o.instrument = true}
    unfold empiricalConditional conditionalReal
    simp_rw [massVectorSum_measureReal]
    rw [hden false, hden true, hnum false false, hnum true false]
  · funext x i
    have hden (z : Bool) :
        {o : ObservedDatum 𝒳 K | decide (o.cell = x ∧ o.instrument = z) = true} =
          {o | o.cell = x ∧ o.instrument = z} := by ext o; simp
    have hnum (z treatment : Bool) :
        {o : ObservedDatum 𝒳 K |
            decide (o.cell = x ∧ o.instrument = z ∧ o.treatment = treatment ∧
              o.selected = true ∧ o.outcome = some i) = true} =
          {o | o.cell = x ∧ o.treatment = treatment ∧ o.selected = true ∧
              o.outcome = some i} ∩ {o | o.cell = x ∧ o.instrument = z} := by
      ext o
      simp [and_assoc, and_left_comm, and_comm]
    change empiricalConditional
        (massVectorSum (fun o => Pobs.real {o}) (fun o => decide
          (o.cell = x ∧ o.instrument = true ∧ o.treatment = true ∧
            o.selected = true ∧ o.outcome = some i)))
        (massVectorSum (fun o => Pobs.real {o}) (fun o => decide
          (o.cell = x ∧ o.instrument = true))) -
      empiricalConditional
        (massVectorSum (fun o => Pobs.real {o}) (fun o => decide
          (o.cell = x ∧ o.instrument = false ∧ o.treatment = true ∧
            o.selected = true ∧ o.outcome = some i)))
        (massVectorSum (fun o => Pobs.real {o}) (fun o => decide
          (o.cell = x ∧ o.instrument = false))) =
      conditionalReal Pobs
          {o | o.cell = x ∧ o.treatment = true ∧ o.selected = true ∧
            o.outcome = some i} {o | o.cell = x ∧ o.instrument = true} -
        conditionalReal Pobs
          {o | o.cell = x ∧ o.treatment = true ∧ o.selected = true ∧
            o.outcome = some i} {o | o.cell = x ∧ o.instrument = false}
    unfold empiricalConditional conditionalReal
    simp_rw [massVectorSum_measureReal]
    rw [hden true, hden false, hnum true true, hnum false true]

/-- The observed-law probability of a covariate cell is the system cell mass. [the stated conclusion follows](goal). -/
theorem observedLaw_cell_real {P : POSystem} [StandardBorelSpace P.Ω]
    (Sys : POSlateSystem P 𝒳 K) (x : 𝒳) :
    Sys.observedLaw.real {o | o.cell = x} = Sys.p x := by
  unfold POSlateSystem.observedLaw POSlateSystem.p
  rw [Measure.real, Measure.map_apply
    (observedDatum_measurable_for_identification Sys)
    ((Set.toFinite _).measurableSet)]
  congr 1

/-- Quantitative observed-law arm overlap, including zero-mass cells. Given [the stated hypotheses](hyp:hOverlap), [the stated conclusion follows](goal). -/
theorem observedLaw_arm_ge_overlap {P : POSystem} [StandardBorelSpace P.Ω]
    (Sys : POSlateSystem P 𝒳 K) {ε : ℝ} (hOverlap : InstrumentOverlap Sys ε)
    (x : 𝒳) (z : Bool) :
    ε * Sys.p x ≤ Sys.observedLaw.real
      {o | o.cell = x ∧ o.instrument = z} := by
  have hp : 0 ≤ Sys.p x := by
    unfold POSlateSystem.p
    positivity
  by_cases hpx : Sys.p x = 0
  · rw [hpx, mul_zero]
    positivity
  have hpxpos : 0 < Sys.p x := lt_of_le_of_ne hp (Ne.symm hpx)
  have hov := hOverlap.2.2 x hpxpos
  have hxmeas : MeasurableSet (Sys.xEvent x) :=
    Sys.xVar.measurable_factual (measurableSet_singleton x)
  have hzmeas : Measurable (Sys.factualZ) := Sys.zVar.measurable_factual
  have harmLaw (b : Bool) : Sys.observedLaw.real
      {o | o.cell = x ∧ o.instrument = b} =
      P.μ.real (Sys.xEvent x ∩ Sys.zVar.event b) := by
    unfold POSlateSystem.observedLaw
    rw [Measure.real, Measure.map_apply
      (observedDatum_measurable_for_identification Sys)
      ((Set.toFinite _).measurableSet)]
    congr 1
  have hprop : Sys.propensity x =
      P.μ.real (Sys.xEvent x ∩ Sys.zVar.event true) / Sys.p x := by
    unfold POSlateSystem.propensity conditionalReal
    rw [if_pos (by simpa [POSlateSystem.p] using hpxpos)]
    change P.μ.real ({w | Sys.factualZ w = true} ∩ Sys.xEvent x) /
        P.μ.real (Sys.xEvent x) = _
    rw [show P.μ.real (Sys.xEvent x) = Sys.p x by rfl]
    congr 2
    ext w
    simp [POSlateSystem.xEvent, POVar.event, POSlateSystem.factualZ,
      and_comm]
  cases z with
  | true =>
      rw [harmLaw]
      rw [hprop] at hov
      have := hov.1
      apply (le_div_iff₀ hpxpos).mp at this
      simpa [mul_comm] using this
  | false =>
      rw [harmLaw]
      have htrueMeas : MeasurableSet {w | Sys.factualZ w = true} :=
        hzmeas (measurableSet_singleton true)
      have hfalseMeas : MeasurableSet {w | Sys.factualZ w = false} :=
        hzmeas (measurableSet_singleton false)
      have hu : Sys.xEvent x =
          (Sys.xEvent x ∩ {w | Sys.factualZ w = false}) ∪
            (Sys.xEvent x ∩ {w | Sys.factualZ w = true}) := by
        ext w
        cases h : Sys.factualZ w <;> simp [h]
      have hd : Disjoint
          (Sys.xEvent x ∩ {w | Sys.factualZ w = false})
          (Sys.xEvent x ∩ {w | Sys.factualZ w = true}) := by
        apply Set.disjoint_left.2
        intro w hw0 hw1
        exact Bool.false_ne_true (hw0.2.symm.trans hw1.2)
      have hpart : Sys.p x =
          P.μ.real (Sys.xEvent x ∩ Sys.zVar.event false) +
            P.μ.real (Sys.xEvent x ∩ Sys.zVar.event true) := by
        unfold POSlateSystem.p
        change P.μ.real (Sys.xEvent x) =
          P.μ.real (Sys.xEvent x ∩ {w | Sys.factualZ w = false}) +
            P.μ.real (Sys.xEvent x ∩ {w | Sys.factualZ w = true})
        calc
          _ = P.μ.real ((Sys.xEvent x ∩ {w | Sys.factualZ w = false}) ∪
              (Sys.xEvent x ∩ {w | Sys.factualZ w = true})) := congrArg _ hu
          _ = _ := measureReal_union hd (hxmeas.inter htrueMeas)
      have htrue : P.μ.real (Sys.xEvent x ∩ Sys.zVar.event true) =
          Sys.propensity x * Sys.p x := by
        rw [hprop]
        field_simp
      rw [htrue] at hpart
      nlinarith [hov.2]

/-- On a guard event, every cell-mass-weighted projected capacity coordinate is uniformly close to its population counterpart. Given [the stated hypotheses](hyp:hδ,hε,hεhalf,hoverlap,hvalid,hdev), [the stated conclusion follows](goal). -/
theorem projectedCapacity_weighted_close
    (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (Pobs : GuardMeasure 𝒳 K) [IsProbabilityMeasure Pobs]
    (n : ℕ) (ω : Ω) {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hoverlap : ∀ x z, ε * Pobs.real {o | o.cell = x} ≤
      Pobs.real {o | o.cell = x ∧ o.instrument = z})
    (hvalid : ValidCapacities (observableCapacities Pobs))
    (hdev : maxDeviation O Pobs n ω ≤ δ) :
    ∀ x i,
      |empiricalCellMass O n ω x * (projectedCapacities O n ω).lower x i -
        Pobs.real {o | o.cell = x} * (observableCapacities Pobs).lower x i| ≤
          16 * δ / ε ^ 2 ∧
      |empiricalCellMass O n ω x * (projectedCapacities O n ω).upper x i -
        Pobs.real {o | o.cell = x} * (observableCapacities Pobs).upper x i| ≤
          16 * δ / ε ^ 2 := by
  classical
  intro x i
  let p := Pobs.real {o | o.cell = x}
  let ph := empiricalCellMass O n ω x
  let a := fun z : Bool => Pobs.real {o | o.cell = x ∧ o.instrument = z}
  let ah := fun z : Bool => empiricalFreq O
    (fun o => decide (o.cell = x ∧ o.instrument = z)) n ω
  let b := fun z d : Bool => Pobs.real {o | o.cell = x ∧ o.instrument = z ∧
    o.treatment = d ∧ o.selected = true ∧ o.outcome = some i}
  let bh := fun z d : Bool => empiricalFreq O
    (fun o => decide (o.cell = x ∧ o.instrument = z ∧ o.treatment = d ∧
      o.selected = true ∧ o.outcome = some i)) n ω
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hph : 0 ≤ ph := empiricalFreq_nonneg _ _ _ _
  have hap (z) : a z ≤ p := by
    apply measureReal_mono
    · intro o ho
      exact ho.1
    · exact measure_ne_top _ _
  have hba (z d) : b z d ≤ a z := by
    apply measureReal_mono
    · intro o ho
      exact ⟨ho.1, ho.2.1⟩
    · exact measure_ne_top _ _
  have hbhah (z d) : bh z d ≤ ah z :=
    empiricalFreq_mono _ _ _ (fun o ho => by
      simp only [decide_eq_true_eq] at ho ⊢
      exact ⟨ho.1, ho.2.1⟩) _ _
  have hpdev : |ph - p| ≤ δ := by
    have h := guardEvent_deviation_le_maxDeviation O Pobs n ω (.cell x)
    change |empiricalFreq O (fun o => decide (o.cell = x)) n ω -
      Pobs.real {o | decide (o.cell = x) = true}| ≤ maxDeviation O Pobs n ω at h
    have h' : |empiricalFreq O (fun o => decide (o.cell = x)) n ω -
        Pobs.real {o | o.cell = x}| ≤ maxDeviation O Pobs n ω := by
      simpa only [decide_eq_true_eq] using h
    dsimp [ph, p, empiricalCellMass]
    exact h'.trans hdev
  have hadev (z) : |ah z - a z| ≤ δ := by
    have h := guardEvent_deviation_le_maxDeviation O Pobs n ω (.arm x z)
    change |empiricalFreq O (fun o => decide (o.cell = x ∧ o.instrument = z)) n ω -
      Pobs.real {o | decide (o.cell = x ∧ o.instrument = z) = true}| ≤
        maxDeviation O Pobs n ω at h
    have h' : |empiricalFreq O (fun o => decide (o.cell = x ∧ o.instrument = z)) n ω -
        Pobs.real {o | o.cell = x ∧ o.instrument = z}| ≤ maxDeviation O Pobs n ω := by
      simpa only [decide_eq_true_eq] using h
    dsimp [ah, a]
    exact h'.trans hdev
  have hbdev (z d) : |bh z d - b z d| ≤ δ := by
    have h := guardEvent_deviation_le_maxDeviation O Pobs n ω
      (.selectedOutcome x z d i)
    change |empiricalFreq O (fun o => decide (o.cell = x ∧ o.instrument = z ∧
      o.treatment = d ∧ o.selected = true ∧ o.outcome = some i)) n ω -
      Pobs.real {o | decide (o.cell = x ∧ o.instrument = z ∧ o.treatment = d ∧
        o.selected = true ∧ o.outcome = some i) = true}| ≤ maxDeviation O Pobs n ω at h
    have h' : |empiricalFreq O (fun o => decide (o.cell = x ∧ o.instrument = z ∧
        o.treatment = d ∧ o.selected = true ∧ o.outcome = some i)) n ω -
      Pobs.real {o | o.cell = x ∧ o.instrument = z ∧ o.treatment = d ∧
        o.selected = true ∧ o.outcome = some i}| ≤ maxDeviation O Pobs n ω := by
      simpa only [decide_eq_true_eq] using h
    dsimp [bh, b]
    exact h'.trans hdev
  have hcond (z d) :
      |ph * empiricalConditional (bh z d) (ah z) -
        p * empiricalConditional (b z d) (a z)| ≤ 8 * δ / ε ^ 2 := by
    exact weightedConditional_stable hδ hε hεhalf hp hph
      (by dsimp [a]; positivity) (hap z) (by simpa [a, p] using hoverlap x z)
      (by dsimp [b]; positivity) (hba z d)
      (by dsimp [ah]; exact empiricalFreq_nonneg _ _ _ _)
      (by dsimp [bh]; exact empiricalFreq_nonneg _ _ _ _)
      (hbhah z d) hpdev (hadev z) (hbdev z d)
  have hrawLower :
      |ph * (capacitiesFromMassVector (empiricalProbabilityVector O n ω)).lower x i -
        p * (capacitiesFromMassVector (fun o => Pobs.real {o})).lower x i| ≤
          16 * δ / ε ^ 2 := by
    unfold capacitiesFromMassVector
    simp_rw [massVectorSum_empiricalProbabilityVector, massVectorSum_measureReal]
    simp only [decide_eq_true_eq]
    change |ph * (empiricalConditional (bh false false) (ah false) -
        empiricalConditional (bh true false) (ah true)) -
      p * (empiricalConditional (b false false) (a false) -
        empiricalConditional (b true false) (a true))| ≤ _
    rw [show ph * (_ - _) - p * (_ - _) =
      (ph * empiricalConditional (bh false false) (ah false) -
        p * empiricalConditional (b false false) (a false)) -
      (ph * empiricalConditional (bh true false) (ah true) -
        p * empiricalConditional (b true false) (a true)) by ring]
    exact (abs_sub _ _).trans (by
      calc
        _ ≤ 8 * δ / ε ^ 2 + 8 * δ / ε ^ 2 :=
          add_le_add (hcond false false) (hcond true false)
        _ = _ := by ring)
  have hrawUpper :
      |ph * (capacitiesFromMassVector (empiricalProbabilityVector O n ω)).upper x i -
        p * (capacitiesFromMassVector (fun o => Pobs.real {o})).upper x i| ≤
          16 * δ / ε ^ 2 := by
    unfold capacitiesFromMassVector
    simp_rw [massVectorSum_empiricalProbabilityVector, massVectorSum_measureReal]
    simp only [decide_eq_true_eq]
    change |ph * (empiricalConditional (bh true true) (ah true) -
        empiricalConditional (bh false true) (ah false)) -
      p * (empiricalConditional (b true true) (a true) -
        empiricalConditional (b false true) (a false))| ≤ _
    rw [show ph * (_ - _) - p * (_ - _) =
      (ph * empiricalConditional (bh true true) (ah true) -
        p * empiricalConditional (b true true) (a true)) -
      (ph * empiricalConditional (bh false true) (ah false) -
        p * empiricalConditional (b false true) (a false)) by ring]
    exact (abs_sub _ _).trans (by
      calc
        _ ≤ 8 * δ / ε ^ 2 + 8 * δ / ε ^ 2 :=
          add_le_add (hcond true true) (hcond false true)
        _ = _ := by ring)
  constructor
  · rw [← projectedMassCapacity_empiricalProbabilityVector O n ω]
    change |ph * max
      ((capacitiesFromMassVector (empiricalProbabilityVector O n ω)).lower x i) 0 -
      p * (observableCapacities Pobs).lower x i| ≤ _
    have hr := hrawLower
    rw [capacitiesFromMassVector_measureReal Pobs] at hr
    exact weighted_positivePart_stable hp hph (hvalid.1 x i) hr
  · rw [← projectedMassCapacity_empiricalProbabilityVector O n ω]
    change |ph * max
      ((capacitiesFromMassVector (empiricalProbabilityVector O n ω)).upper x i) 0 -
      p * (observableCapacities Pobs).upper x i| ≤ _
    have hr := hrawUpper
    rw [capacitiesFromMassVector_measureReal Pobs] at hr
    exact weighted_positivePart_stable hp hph (hvalid.2 x i) hr

/-- Complete deterministic guard inequality on a fixed observed law. Given [the stated hypotheses](hyp:hDomain,hη,hmstar,hε,hεhalf,hoverlap,hvalid,hmass,hδ,hdev), [the stated conclusion follows](goal). -/
theorem plugInEndpoints_error_le_of_maxDeviation
    (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (Pobs : GuardMeasure 𝒳 K) [IsProbabilityMeasure Pobs]
    (hDomain : ObservedLawDomain Pobs)
    (n : ℕ) (ω : Ω) (η mstar ε δ : ℝ)
    (hη : 0 < η) (hmstar : 0 < mstar) (hε : 0 < ε)
    (hεhalf : ε < 1 / 2)
    (hoverlap : ∀ x z, ε * Pobs.real {o | o.cell = x} ≤
      Pobs.real {o | o.cell = x ∧ o.instrument = z})
    (hvalid : ValidCapacities (observableCapacities Pobs))
    (hmass : mstar ≤ (observableCapacities Pobs).aggregateMass
      (fun x => Pobs.real {o | o.cell = x}))
    (hδ : 0 ≤ δ) (hdev : maxDeviation O Pobs n ω ≤ δ) :
    let A := 64 * (K : ℝ) * Fintype.card 𝒳 / ε ^ 2 * δ +
      Fintype.card 𝒳 * η
    (max
      |(plugInEndpoints O (fun _ => η) n ω).1 -
        ((observableCapacities Pobs).endpointMap
          (fun x => Pobs.real {o | o.cell = x}) Pobs rfl rfl hvalid
          (fun _ => measureReal_nonneg) (lt_of_lt_of_le hmstar hmass)
          hDomain).endpoints.1|
      |(plugInEndpoints O (fun _ => η) n ω).2 -
        ((observableCapacities Pobs).endpointMap
          (fun x => Pobs.real {o | o.cell = x}) Pobs rfl rfl hvalid
          (fun _ => measureReal_nonneg) (lt_of_lt_of_le hmstar hmass)
          hDomain).endpoints.2| ≤
      min 1 (4 * A / mstar)) ∧
    (4 * A < mstar →
      max
        |(plugInEndpoints O (fun _ => η) n ω).1 -
          ((observableCapacities Pobs).endpointMap
            (fun x => Pobs.real {o | o.cell = x}) Pobs rfl rfl hvalid
            (fun _ => measureReal_nonneg) (lt_of_lt_of_le hmstar hmass)
            hDomain).endpoints.1|
        |(plugInEndpoints O (fun _ => η) n ω).2 -
          ((observableCapacities Pobs).endpointMap
            (fun x => Pobs.real {o | o.cell = x}) Pobs rfl rfl hvalid
            (fun _ => measureReal_nonneg) (lt_of_lt_of_le hmstar hmass)
            hDomain).endpoints.2| ≤
        3 * A / mstar) := by
  classical
  dsimp
  let c := observableCapacities Pobs
  let ch := projectedCapacities O n ω
  let p := fun x => Pobs.real {o | o.cell = x}
  let ph := empiricalCellMass O n ω
  let keep := fun x => if η < ph x * ch.mass x then (1 : ℝ) else 0
  let M := ∑ x, p x * c.mass x
  let NL := ∑ x, p x * c.benefitLower x
  let NU := ∑ x, p x * c.benefitUpper x
  let Mh := ∑ x, keep x * ph x * ch.mass x
  let NLh := ∑ x, keep x * ph x * ch.benefitLower x
  let NUh := ∑ x, keep x * ph x * ch.benefitUpper x
  let A := 64 * (K : ℝ) * Fintype.card 𝒳 / ε ^ 2 * δ +
    Fintype.card 𝒳 * η
  have hp : ∀ x, 0 ≤ p x := fun x => by dsimp [p]; positivity
  have hph : ∀ x, 0 ≤ ph x := fun x => empiricalFreq_nonneg _ _ _ _
  have hch : ValidCapacities ch := by
    constructor <;> intro x i <;> dsimp [ch, projectedCapacities] <;> exact le_max_right _ _
  have hcoord := projectedCapacity_weighted_close O Pobs n ω hδ hε hεhalf
    hoverlap hvalid hdev
  have hfull := weightedCapacity_aggregate_close p ph c ch
    (16 * δ / ε ^ 2) (by positivity) hp hph (by
      intro x i
      simpa [p, ph, c, ch] using hcoord x i)
  have hR : 4 * (K : ℝ) * Fintype.card 𝒳 * (16 * δ / ε ^ 2) =
      64 * (K : ℝ) * Fintype.card 𝒳 / ε ^ 2 * δ := by ring
  rw [hR] at hfull
  have hscreen := screenedCapacity_aggregate_close p ph c ch η
    (64 * (K : ℝ) * Fintype.card 𝒳 / ε ^ 2 * δ) hη hph hch
    hfull.1 hfull.2.1 hfull.2.2
  have herrM : |Mh - M| ≤ A := by simpa [Mh, M, keep, A] using hscreen.1
  have herrL : |NLh - NL| ≤ A := by simpa [NLh, NL, keep, A] using hscreen.2.1
  have herrU : |NUh - NU| ≤ A := by simpa [NUh, NU, keep, A] using hscreen.2.2
  have hM : mstar ≤ M := by simpa [M, c, p, Capacities.aggregateMass] using hmass
  have hmass0 (x) : 0 ≤ c.mass x := by
    unfold Capacities.mass Capacities.q0 Capacities.q1
    exact le_min (Finset.sum_nonneg fun i _ => hvalid.1 x i)
      (Finset.sum_nonneg fun i _ => hvalid.2 x i)
  have hNL0 : 0 ≤ NL := Finset.sum_nonneg fun x _ =>
    mul_nonneg (hp x) (benefitLower_nonneg c x)
  have hNU0 : 0 ≤ NU := Finset.sum_nonneg fun x _ =>
    mul_nonneg (hp x) (benefitUpper_nonneg c hvalid x)
  have hNLM : NL ≤ M := by
    apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left (benefitLower_le_mass c hvalid x) (hp x)
  have hNUM : NU ≤ M := by
    apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left (benefitUpper_le_mass c x) (hp x)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hMh0 : 0 ≤ Mh := Finset.sum_nonneg fun x _ => by
    dsimp [keep]
    exact mul_nonneg (mul_nonneg (by split <;> positivity) (hph x))
      (by
        unfold Capacities.mass Capacities.q0 Capacities.q1
        exact le_min (Finset.sum_nonneg fun i _ => hch.1 x i)
          (Finset.sum_nonneg fun i _ => hch.2 x i))
  have hNLh0 : 0 ≤ NLh := Finset.sum_nonneg fun x _ => by
    dsimp [keep]
    exact mul_nonneg (mul_nonneg (by split <;> positivity) (hph x))
      (benefitLower_nonneg ch x)
  have hNUh0 : 0 ≤ NUh := Finset.sum_nonneg fun x _ => by
    dsimp [keep]
    exact mul_nonneg (mul_nonneg (by split <;> positivity) (hph x))
      (benefitUpper_nonneg ch hch x)
  have hNLhM : NLh ≤ Mh := by
    apply Finset.sum_le_sum
    intro x hx
    dsimp [NLh, Mh, keep]
    exact mul_le_mul_of_nonneg_left (benefitLower_le_mass ch hch x)
      (mul_nonneg (by split <;> positivity) (hph x))
  have hNUhM : NUh ≤ Mh := by
    apply Finset.sum_le_sum
    intro x hx
    dsimp [NUh, Mh, keep]
    exact mul_le_mul_of_nonneg_left (benefitUpper_le_mass ch x)
      (mul_nonneg (by split <;> positivity) (hph x))
  constructor
  · by_cases hsmall : 4 * A < mstar
    · have hL := ratio_error_le_three hmstar hM hNL0 hNLM hA hsmall herrM herrL
      have hU := ratio_error_le_three hmstar hM hNU0 hNUM hA hsmall herrM herrU
      have hplug : plugInEndpoints O (fun _ => η) n ω = (NLh / Mh, NUh / Mh) := by
        unfold plugInEndpoints screenedCell
        dsimp [ch, ph, keep, Mh, NLh, NUh]
        rw [if_pos hL.1]
      rw [hplug]
      change max |NLh / Mh - NL / M| |NUh / Mh - NU / M| ≤ _
      rw [min_eq_right (le_of_lt ((div_lt_one hmstar).2 hsmall))]
      have h34 : 3 * A / mstar ≤ 4 * A / mstar := by
        gcongr
        nlinarith
      exact max_le (hL.2.trans h34) (hU.2.trans h34)
    · have hguard : 1 ≤ 4 * A / mstar := by
        rw [le_div_iff₀ hmstar]
        simpa using le_of_not_gt hsmall
      rw [min_eq_left hguard]
      have htargetL0 : 0 ≤ NL / M := div_nonneg hNL0 (le_trans hmstar.le hM)
      have htargetU0 : 0 ≤ NU / M := div_nonneg hNU0 (le_trans hmstar.le hM)
      have htargetL1 : NL / M ≤ 1 := (div_le_one (lt_of_lt_of_le hmstar hM)).2 hNLM
      have htargetU1 : NU / M ≤ 1 := (div_le_one (lt_of_lt_of_le hmstar hM)).2 hNUM
      have hplugBounds :
          0 ≤ (plugInEndpoints O (fun _ => η) n ω).1 ∧
          (plugInEndpoints O (fun _ => η) n ω).1 ≤ 1 ∧
          0 ≤ (plugInEndpoints O (fun _ => η) n ω).2 ∧
          (plugInEndpoints O (fun _ => η) n ω).2 ≤ 1 := by
        unfold plugInEndpoints screenedCell
        dsimp [ch, ph, keep, Mh, NLh, NUh]
        split_ifs with hpos
        · exact ⟨div_nonneg hNLh0 hpos.le, (div_le_one hpos).2 hNLhM,
            div_nonneg hNUh0 hpos.le, (div_le_one hpos).2 hNUhM⟩
        · simp
      change max |(plugInEndpoints O (fun _ => η) n ω).1 - NL / M|
        |(plugInEndpoints O (fun _ => η) n ω).2 - NU / M| ≤ 1
      apply max_le <;> rw [abs_le] <;> constructor <;> linarith [hplugBounds.1,
        hplugBounds.2.1, hplugBounds.2.2.1, hplugBounds.2.2.2]
  · intro hsmall
    have hL := ratio_error_le_three hmstar hM hNL0 hNLM hA hsmall herrM herrL
    have hU := ratio_error_le_three hmstar hM hNU0 hNUM hA hsmall herrM herrU
    have hplug : plugInEndpoints O (fun _ => η) n ω = (NLh / Mh, NUh / Mh) := by
      unfold plugInEndpoints screenedCell
      dsimp [ch, ph, keep, Mh, NLh, NUh]
      rw [if_pos hL.1]
    rw [hplug]
    exact max_le hL.2 hU.2

/-- Given [the stated hypotheses](hyp:hcObs,hpObs,hp,hc,hM,hDomain), [the endpoint map bounds property holds](goal). -/
theorem endpointMap_bounds (Pobs : Measure (ObservedDatum 𝒳 K))
    (p : 𝒳 → ℝ) (c : Capacities 𝒳 K)
    (hcObs : c = observableCapacities Pobs)
    (hpObs : p = Capacities.observedCellWeights Pobs)
    (hp : ∀ x, 0 ≤ p x) (hc : ValidCapacities c)
    (hM : 0 < c.aggregateMass p) (hDomain : ObservedLawDomain Pobs) :
    0 ≤ (c.endpointMap p Pobs hcObs hpObs hc hp hM hDomain).endpoints.1 ∧
      (c.endpointMap p Pobs hcObs hpObs hc hp hM hDomain).endpoints.1 ≤ 1 ∧
    0 ≤ (c.endpointMap p Pobs hcObs hpObs hc hp hM hDomain).endpoints.2 ∧
      (c.endpointMap p Pobs hcObs hpObs hc hp hM hDomain).endpoints.2 ≤ 1 := by
  have hL0 : 0 ≤ ∑ x, p x * c.benefitLower x :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (benefitLower_nonneg c x)
  have hU0 : 0 ≤ ∑ x, p x * c.benefitUpper x :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (benefitUpper_nonneg c hc x)
  have hLM : (∑ x, p x * c.benefitLower x) ≤ c.aggregateMass p := by
    unfold Capacities.aggregateMass
    exact Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (benefitLower_le_mass c hc x) (hp x)
  have hUM : (∑ x, p x * c.benefitUpper x) ≤ c.aggregateMass p := by
    unfold Capacities.aggregateMass
    exact Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (benefitUpper_le_mass c x) (hp x)
  unfold Capacities.endpointMap
  exact ⟨div_nonneg hL0 hM.le, (div_le_one hM).2 hLM,
    div_nonneg hU0 hM.le, (div_le_one hM).2 hUM⟩

/-- Given [the stated hypotheses](hyp:hc,h), [the inverse sqrt eta tail tendsto zero property holds](goal). -/
theorem inverse_sqrtEta_tail_tendsto_zero (η : ℕ → ℝ) {c C : ℝ}
    (hc : 0 < c)
    (h : Tendsto (fun n : ℕ => Real.sqrt n * η n) atTop atTop) :
    Tendsto (fun n : ℕ => C / (4 * (n : ℝ) * (c * η n) ^ 2))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (Real.sqrt n * η n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h
  have hcst : Tendsto (fun _ : ℕ => C / (4 * c ^ 2)) atTop
      (𝓝 (C / (4 * c ^ 2))) := tendsto_const_nhds
  have hs0 := hcst.mul (hi.mul hi)
  have hs : Tendsto (fun n : ℕ => (C / (4 * c ^ 2)) *
      ((Real.sqrt n * η n)⁻¹ * (Real.sqrt n * η n)⁻¹)) atTop (𝓝 0) := by
    simpa using hs0
  apply hs.congr'
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt n * η n :=
    (tendsto_atTop.1 h 1).mono fun n hn => lt_of_lt_of_le zero_lt_one hn
  filter_upwards [eventually_ge_atTop 1, hpos] with n hn hnη
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hηne : η n ≠ 0 := by
    intro hz
    simp [hz] at hnη
  field_simp [hc.ne', hnpos.ne', Real.sqrt_ne_zero'.2 hnpos, hηne]
  rw [hsqrt]

end CausalSmith.PartialID.SlateBenefitPartialTransport
