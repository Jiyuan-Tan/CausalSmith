module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerSparseCalibration

/-! # Sparse lower bounds for the full observed histogram

Reorder the four counts in each cell without losing any observations. Identify
this experiment with the inflated Poisson counts of the normalized sparse law,
and transport the packet Bayes lower bound to arbitrary histogram estimators.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Minimax.MomentMatchedMixture
open Causalean.Stat.Minimax.FuzzyHypotheses
open scoped BigOperators ENNReal


-- @node: sparseCountEquiv
/-- All observed histogram counts, reversibly arranged into four-count cells.

For [the displayed parameters](hyp:d), [sparseCountEquiv](goal) is the object specified by this definition. -/
noncomputable def sparseCountEquiv (d : ℕ) :
    (Obs d → ℕ) ≃ᵐ (Fin d → (Fin 4 → ℕ)) where
  toFun N := fun x j => N (x, j.val / 2 = 1, j.val % 2 = 1)
  invFun N := fun o => N o.1 (cellIdx o.2.1 o.2.2)
  left_inv N := by
    funext o
    rcases o with ⟨x, a, y⟩
    cases a <;> cases y <;> simp [cellIdx]
  right_inv N := by
    funext x j
    fin_cases j <;> rfl
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

/-- The observed histogram version of the full sparse four-count experiment.

For [the displayed parameters](hyp:B,n,d,M,hMpaper), [sparseFullObservedPoissonKernel](goal) is the object specified by this definition. -/
noncomputable def sparseFullObservedPoissonKernel (B : ℝ) (n d : ℕ) (ε M : ℝ) (hMpaper : 2 ≤ M) :
    Kernel (Fin d → ℝ) (Obs d → ℕ) :=
  (sparseProductPoissonKernel (hMpaper := hMpaper) B n d ε M).map (sparseCountEquiv d).symm

/-- The full observed experiment has probability fibres. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hMpaper), the [stated conclusion](goal) holds. -/
lemma sparseFullObservedPoissonKernel_probability (B : ℝ) (n d : ℕ) (ε M : ℝ)
    (θ : Fin d → ℝ) (hMpaper : 2 ≤ M) :
    IsProbabilityMeasure (sparseFullObservedPoissonKernel (hMpaper := hMpaper) B n d ε M θ) := by
  rw [sparseFullObservedPoissonKernel, Kernel.map_apply _ (sparseCountEquiv d).symm.measurable]
  letI := sparseProductPoissonKernel_probability (hMpaper := hMpaper) B n d ε M θ
  exact Measure.isProbabilityMeasure_map (sparseCountEquiv d).symm.measurable.aemeasurable

/-- Normalization of the observed law cancels the total-mean inflation, yielding exactly the four unnormalized Poisson intensities in (34). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,hz), the [stated conclusion](goal) holds. -/
lemma sparseLaw_poissonMeans {d : ℕ} (hd : 0 < d) (ε M B : ℝ) (n : ℕ)
    (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (z : Fin d → ℝ)
    (hz : ∀ x, z x ∈ Set.Icc 0 M) (x : Fin d) (a y : Bool) :
    (B * n * sparseNormalizerFormula d ε M z hz) *
      jointMass (sparseLaw hd ε M ⟨hε, hεhi⟩ z hz) x a y =
        poissonCellMean B n d ε (z x) (cellIdx a y) := by
  have hS : 0 < sparseNormalizerFormula d ε M z hz := by
    have h := sparseNormalizer_ge_half hε.le hεhi z hz
    linarith
  rw [sparseLaw_jointMass]
  unfold sparseMass
  rw [mul_assoc, mul_div_cancel₀ _ hS.ne']
  cases a <;> cases y <;> simp [sparseUnnormalizedMass, poissonCellMean, cellIdx]

/-- Reordering the independent observed counts gives precisely the full sparse product experiment. The Poisson total mean is B n S, as in (49). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,hMpaper,hz), the [stated conclusion](goal) holds. -/
lemma sparseProductPoissonKernel_eq_observedCounts {d : ℕ} (hd : 0 < d)
    (ε M B : ℝ) (n : ℕ) (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (hMpaper : 2 ≤ M)
    (θ : Fin d → ℝ) (hz : ∀ x, θ x + sparseReference (_hMpaper := hMpaper) M ∈ Set.Icc 0 M) :
    Measure.map (sparseCountEquiv d)
      (Measure.pi fun o : Obs d => poissonMeasure (Real.toNNReal
        ((B * n * sparseNormalizerFormula d ε M (fun x => θ x + sparseReference (_hMpaper := hMpaper) M) hz) *
          jointMass (sparseLaw hd ε M ⟨hε, hεhi⟩
            (fun x => θ x + sparseReference (_hMpaper := hMpaper) M) hz) o.1 o.2.1 o.2.2))) =
      sparseProductPoissonKernel (hMpaper := hMpaper) B n d ε M θ := by
  apply Measure.ext_of_singleton
  intro N
  rw [Measure.map_apply (sparseCountEquiv d).measurable (measurableSet_singleton _)]
  have hpre : (sparseCountEquiv d) ⁻¹' {N} = {(sparseCountEquiv d).symm N} := by
    ext T
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (sparseCountEquiv d).apply_eq_iff_eq_symm_apply
  rw [hpre, Measure.pi_singleton]
  change _ = (Measure.pi fun x => poissonCellLaw B n d ε (θ x + sparseReference (_hMpaper := hMpaper) M)) {N}
  simp only [poissonCellLaw, Measure.pi_singleton, Obs, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro x _
  simp_rw [sparseLaw_poissonMeans hd ε M B n hε hεhi]
  simp [Fintype.prod_bool, Fin.prod_univ_four, sparseCountEquiv, cellIdx]
  let f (j : Fin 4) := (poissonMeasure (Real.toNNReal
    (poissonCellMean B n d ε (θ x + sparseReference (_hMpaper := hMpaper) M) j))) {N x j}
  change f 3 * f 2 * (f 1 * f 0) = f 0 * f 1 * f 2 * f 3
  ac_rfl

/-- Undoing the count reordering recovers the exact independent Poisson histogram law of the legal sparse observed model on the prior support. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,hMpaper,hz), the [stated conclusion](goal) holds. -/
lemma sparseFullObservedPoissonKernel_eq {d : ℕ} (hd : 0 < d)
    (ε M B : ℝ) (n : ℕ) (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (hMpaper : 2 ≤ M)
    (θ : Fin d → ℝ) (hz : ∀ x, θ x + sparseReference (_hMpaper := hMpaper) M ∈ Set.Icc 0 M) :
    sparseFullObservedPoissonKernel (hMpaper := hMpaper) B n d ε M θ =
      Measure.pi fun o : Obs d => poissonMeasure (Real.toNNReal
        ((B * n * sparseNormalizerFormula d ε M (fun x => θ x + sparseReference (_hMpaper := hMpaper) M) hz) *
          jointMass (sparseLaw hd ε M ⟨hε, hεhi⟩
            (fun x => θ x + sparseReference (_hMpaper := hMpaper) M) hz) o.1 o.2.1 o.2.2)) := by
  rw [sparseFullObservedPoissonKernel,
    Kernel.map_apply _ (sparseCountEquiv d).symm.measurable]
  rw [← sparseProductPoissonKernel_eq_observedCounts (hMpaper := hMpaper) hd ε M B n hε hεhi θ hz]
  rw [Measure.map_map (sparseCountEquiv d).symm.measurable (sparseCountEquiv d).measurable]
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply, Measure.map_id']

/-- Every histogram estimator has exactly the same Bayes risk after the reversible arrangement into cells; none of the four counts is discarded. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hest,hMpaper), the [stated conclusion](goal) holds. -/
lemma sparse_full_observed_bayesRisk_eq (B : ℝ) (n d : ℕ) (ε M : ℝ)
    (π : Measure (Fin d → ℝ)) (target : (Fin d → ℝ) → ℝ)
    (est : (Obs d → ℕ) → ℝ) (hest : Measurable est) (hMpaper : 2 ≤ M) :
    bayesSquaredRisk π (sparseFullObservedPoissonKernel (hMpaper := hMpaper) B n d ε M) target est =
      bayesSquaredRisk π (sparseProductPoissonKernel (hMpaper := hMpaper) B n d ε M) target
        (fun N => est ((sparseCountEquiv d).symm N)) := by
  unfold bayesSquaredRisk squaredRisk
  apply lintegral_congr
  intro θ
  rw [sparseFullObservedPoissonKernel,
    Kernel.map_apply _ (sparseCountEquiv d).symm.measurable]
  exact lintegral_map (by fun_prop) (sparseCountEquiv d).symm.measurable


-- @node: sparseObservedModel
/-- Clip only outside the prior support to obtain a legal normalized sparse observed model at every centered parameter vector. For the displayed parameters, sparseObservedModel is the object specified by this definition. -/
 noncomputable def sparseObservedModel {d : ℕ} (hd : 2 ≤ d) (ε M : ℝ) (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (hM : 2 ≤ M) (θ : Fin d → ℝ) : ModelLaw d ε := ⟨sparseLaw (by omega) ε M ⟨hε, hεhi⟩ (fun x => sparseClippedIntensity (hMpaper := hM) M (θ x)) (fun _ => sparseClippedIntensity_mem (hMpaper := hM) (by linarith) _), (sparse_likelihood 1 d ε M 4 (fun x => sparseClippedIntensity (hMpaper := hM) M (θ x)) (by norm_num) hd hε hεhi hM (by norm_num) (fun _ => sparseClippedIntensity_mem (hMpaper := hM) (by linarith) _)).1⟩ 
/-- The legal observed model has exactly the normalized target used in sparse concentration and fuzzy testing. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,hM), the [stated conclusion](goal) holds. -/
lemma sparseObservedModel_value {d : ℕ} (hd : 2 ≤ d) (ε M : ℝ)
    (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (hM : 2 ≤ M) (θ : Fin d → ℝ) :
    observedValue (sparseObservedModel hd ε M hε hεhi hM θ).1 =
      sparsePriorTarget (hMpaper := hM) d ε M θ := by
  have hval := (sparse_likelihood 1 d ε M 4
    (fun x => sparseClippedIntensity (hMpaper := hM) M (θ x)) (by norm_num) hd hε hεhi hM
    (by norm_num) (fun _ => sparseClippedIntensity_mem (hMpaper := hM) (by linarith) _)).2.2.1
  rw [sparseObservedModel, hval]
  unfold sparsePriorTarget sparseNormalizerFormula
  rw [div_mul_eq_mul_div]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The explicit packet sparse lower order holds for every estimator using all observed histogram counts and the actual legal observed value as target, with concentration and likelihood closeness derived from the packet construction and the logarithmic alphabet cutoff. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma sparse_full_observed_logDegree_bayesRisk_lower :
    ∃ (c η C : ℝ) (A D : ℕ),
      0 < c ∧ 0 < η ∧ 2 ≤ C ∧ 1 ≤ A ∧ 2 ≤ D ∧
      ∀ (n d : ℕ) (ε M B : ℝ) (hd2 : 2 ≤ d)
        (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (hM : 2 ≤ M),
        1 ≤ n → D ≤ d →
        M ≤ (lowerLogDegree C d : ℝ) ^ 2 → 2 < B →
        M ≤ η * d * lowerLogDegree C d / (B * n * ε) →
        ∃ (P : ConstrainedPriorPair (lowerLogDegree C d) M),
          ∃ hdom : CommonAtomDomain
            (packetPositive A (lowerLogDegree C d) M)
            (packetNegative A (lowerLogDegree C d) M),
            commonAtomCompletion
              (packetPositive A (lowerLogDegree C d) M)
              (packetNegative A (lowerLogDegree C d) M) hdom = (P.ν₀, P.ν₁) ∧
            ∀ est : (Obs d → ℕ) → ℝ, Measurable est →
              ENNReal.ofReal (c * M / (lowerLogDegree C d : ℝ) ^ 2) ≤
                max
                  (bayesSquaredRisk
                    (productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₀))
                    (sparseFullObservedPoissonKernel (hMpaper := hM) B n d ε M)
                    (fun θ => observedValue (sparseObservedModel hd2 ε M hε hεhi hM θ).1) est)
                  (bayesSquaredRisk
                    (productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₁))
                    (sparseFullObservedPoissonKernel (hMpaper := hM) B n d ε M)
                    (fun θ => observedValue (sparseObservedModel hd2 ε M hε hεhi hM θ).1) est) := by
  obtain ⟨c, η, C, A, D, hc, hη, hC, hA, hD, hbound⟩ :=
    sparse_packet_bayesRisk_lower_largeAlphabet
  refine ⟨c, η, C, A, D, hc, hη, hC, hA, hD, ?_⟩
  intro n d ε M B hd2 hε hεhi hM hn hd hMhi hB hband
  obtain ⟨P, hdom, hcompletion, hP⟩ := hbound n d ε M B hn hd hε hεhi hM hMhi hB hband
  refine ⟨P, hdom, hcompletion, ?_⟩
  intro est hest
  simp_rw [sparseObservedModel_value]
  rw [sparse_full_observed_bayesRisk_eq (hMpaper := hM) B n d ε M _ _ est hest,
    sparse_full_observed_bayesRisk_eq (hMpaper := hM) B n d ε M _ _ est hest]
  exact hP _ (hest.comp (sparseCountEquiv d).symm.measurable)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
