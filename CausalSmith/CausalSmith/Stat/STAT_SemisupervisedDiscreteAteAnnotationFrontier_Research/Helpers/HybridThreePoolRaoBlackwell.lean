module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridThreePoolPoissonLaw

/-! Explicit evaluation of the paper's three-pool Rao--Blackwell statistic. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory Causalean.Stat
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily

private def packThreeNat (z : Nat × (Nat × Nat)) : ThreePoolIndex → Nat
  | .complete => z.1
  | .sharedLeft => z.2.1
  | .sharedRight => z.2.2

private lemma packThreeNat_unpack (z : ThreePoolIndex → Nat) :
    packThreeNat (unpackThreePool z) = z := by
  funext i
  cases i <;> rfl

private lemma forall_threePoolIndex (p : ThreePoolIndex → Prop) :
    (∀ i, p i) ↔ p .complete ∧ p .sharedLeft ∧ p .sharedRight := by
  constructor
  · intro h
    exact ⟨h .complete, h .sharedLeft, h .sharedRight⟩
  · rintro ⟨h0, hp, hf⟩ i
    cases i <;> assumption

/-- On calibration, the abstract three-pool conditional expectation is exactly
the displayed finite weighted sum defining `mixedEstimator`.  [the stated conditions](hyp:hcal) [the stated conclusion](goal). -/
lemma prefixRaoBlackwellStatistic_hybridFixedPools {n m d : Nat}
    (eps : Real) (hcal : calibrationPredicate n m eps)
    (sample : Sample n m d) :
    prefixRaoBlackwellStatistic
        (threePoolIntensity
          (Real.toNNReal ((blockSizes n m).M0 / 8 : Real))
          (Real.toNNReal
            (((blockSizes n m).np + (blockSizes n m).mp : Nat) / 8 : Real))
          (Real.toNNReal
            (((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8 : Real)))
        (finitePrefixHybridStatistic n m eps) 0 (hybridFixedPools sample) =
      mixedEstimator n m d eps sample := by
  classical
  let bs := blockSizes n m
  let u : Real := bs.M0 / 8
  let tp : Real := (bs.np + bs.mp : Nat) / 8
  let t : Real := (bs.nf + bs.mf : Nat) / 8
  let T := finitePrefixHybridStatistic (d := d) n m eps
  let lam := threePoolIntensity (Real.toNNReal u)
    (Real.toNNReal tp) (Real.toNNReal t)
  let pools := hybridFixedPools sample
  rw [prefixRaoBlackwellStatistic_eq_integral lam T
      (measurable_finitePrefixHybridStatistic n m eps) 0 pools]
  let f : (ThreePoolIndex → Nat) → Real := fun counts ↦
    cappedPrefixStatistic T 0 (fun i ↦ (pools i, counts i))
  let g : Nat × (Nat × Nat) → Real := fun counts ↦ f (packThreeNat counts)
  have hfg : f = g ∘ unpackThreePool := by
    funext counts
    simp only [Function.comp_apply, g, packThreeNat_unpack]
  change (∫ counts, f counts ∂Measure.pi (fun i ↦ poissonMeasure (lam i))) = _
  rw [hfg]
  have hg : AEStronglyMeasurable g
      (Measure.map unpackThreePool
        (Measure.pi (fun i ↦ poissonMeasure (lam i)))) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hIntegral :
      (∫ counts, (g ∘ unpackThreePool) counts
          ∂Measure.pi (fun i ↦ poissonMeasure (lam i))) =
        ∫ z, g z ∂Measure.map unpackThreePool
          (Measure.pi (fun i ↦ poissonMeasure (lam i))) :=
    (integral_map measurable_unpackThreePool.aemeasurable hg).symm
  rw [hIntegral]
  rw [map_unpackThreePool_pi]
  simp only [lam, threePoolIntensity]
  have hgBound (z : Nat × (Nat × Nat)) : ‖g z‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    by_cases hz : ∀ i, (packThreeNat z i) ≤
        threePoolCapacity (blockSizes n m).M0
          ((blockSizes n m).np + (blockSizes n m).mp)
          ((blockSizes n m).nf + (blockSizes n m).mf) i
    · rw [show g z = T (fun i ↦
          Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.prefixOfLE
            (pools i) (packThreeNat z i) (hz i)) by
          simp only [g, f, cappedPrefixStatistic, dif_pos hz]]
      exact abs_le.2 (finitePrefixHybridStatistic_mem_Icc n m eps _)
    · simp only [g, f, cappedPrefixStatistic, dif_neg hz, abs_zero]
      norm_num
  have hint : Integrable g
      ((poissonMeasure (Real.toNNReal u)).prod
        ((poissonMeasure (Real.toNNReal tp)).prod
          (poissonMeasure (Real.toNNReal t)))) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    filter_upwards [] with z
    exact hgBound z
  rw [integral_prod _ hint, integral_poissonMeasure]
  simp only [smul_eq_mul]
  rw [tsum_eq_sum (s := Finset.range (bs.M0 + 1))]
  · simp only [mixedEstimator, hcal, if_true]
    apply Finset.sum_congr rfl
    intro r0 hr0
    have hr0le : r0 ≤ bs.M0 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr0)
    have hintPF : Integrable (fun z : Nat × Nat ↦ g (r0, z))
        ((poissonMeasure (Real.toNNReal tp)).prod
          (poissonMeasure (Real.toNNReal t))) := by
      apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      filter_upwards [] with z
      exact hgBound (r0, z)
    rw [integral_prod _ hintPF, integral_poissonMeasure]
    simp only [smul_eq_mul]
    rw [tsum_eq_sum (s := Finset.range (bs.np + bs.mp + 1))]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rp hrp
      have hrple : rp ≤ bs.np + bs.mp :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hrp)
      rw [integral_poissonMeasure]
      simp only [smul_eq_mul]
      rw [tsum_eq_sum (s := Finset.range (bs.nf + bs.mf + 1))]
      · simp only [mixedEstimator, hcal, if_true, bs, u, tp, t]
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro rf hrf
        have hrfle : rf ≤ bs.nf + bs.mf :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hrf)
        rw [show g (r0, rp, rf) = prefixOutput eps sample r0 rp rf by
          have hz : ∀ i, packThreeNat (r0, rp, rf) i ≤
              threePoolCapacity (blockSizes n m).M0
                ((blockSizes n m).np + (blockSizes n m).mp)
                ((blockSizes n m).nf + (blockSizes n m).mf) i := by
            intro i
            cases i <;> assumption
          simp only [g, f, cappedPrefixStatistic, dif_pos hz]
          exact finitePrefixHybridStatistic_fixedPools eps sample r0 rp rf
            hr0le hrple hrfle]
        simp only [ProbabilityTheory.poissonMeasure_singleton,
          MeasureTheory.measureReal_def]
        rw [ENNReal.toReal_ofReal (by positivity),
          ENNReal.toReal_ofReal (by positivity),
          ENNReal.toReal_ofReal (by positivity)]
        ring
      · intro rf hrf
        have hn : ¬ rf ≤ bs.nf + bs.mf :=
          fun h ↦ hrf (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr h))
        have hz : ¬ ∀ i, packThreeNat (r0, rp, rf) i ≤
            threePoolCapacity (blockSizes n m).M0
              ((blockSizes n m).np + (blockSizes n m).mp)
              ((blockSizes n m).nf + (blockSizes n m).mf) i :=
          fun h ↦ hn (h .sharedRight)
        simp [g, f, cappedPrefixStatistic, hz]
    · intro rp hrp
      have hn : ¬ rp ≤ bs.np + bs.mp :=
        fun h ↦ hrp (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr h))
      have hzero (rf : Nat) : g (r0, rp, rf) = 0 := by
        have hz : ¬ ∀ i, packThreeNat (r0, rp, rf) i ≤
            threePoolCapacity (blockSizes n m).M0
              ((blockSizes n m).np + (blockSizes n m).mp)
              ((blockSizes n m).nf + (blockSizes n m).mf) i :=
          fun h ↦ hn (h .sharedLeft)
        simp [g, f, cappedPrefixStatistic, hz]
      simp_rw [hzero]
      simp
  · intro r0 hr0
    have hn : ¬ r0 ≤ bs.M0 :=
      fun h ↦ hr0 (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr h))
    have hzero (z : Nat × Nat) : g (r0, z) = 0 := by
      have hz : ¬ ∀ i, packThreeNat (r0, z) i ≤
          threePoolCapacity (blockSizes n m).M0
            ((blockSizes n m).np + (blockSizes n m).mp)
            ((blockSizes n m).nf + (blockSizes n m).mf) i :=
        fun h ↦ hn (h .complete)
      simp [g, f, cappedPrefixStatistic, hz]
    simp_rw [hzero]
    simp

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
