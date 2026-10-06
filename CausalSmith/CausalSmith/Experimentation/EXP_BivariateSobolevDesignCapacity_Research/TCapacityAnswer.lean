module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.TLogFreeBivariateCapacity

/-! # Complete answer to the bivariate design-capacity question

This capstone retains the concrete attaining kernel, legal prior, actual Gaussian HT
transfer, exact frozen-class capacity, and the entire dimension-sequence equivalence.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

-- @node: thm:capacity-answer
/-- The single smoothness-free kernel and independent legal prior give the complete
capacity answer, including actual HT excess and exact published-law minimax transfer. This uses [the hContraction_of_gate hypothesis](hyp:hContraction_of_gate), [the hExcess_of_gate hypothesis](hyp:hExcess_of_gate), [the stated conclusion](goal). -/
theorem capacity_answer
    (hContraction_of_gate : ClassicalRademacherContraction)
    (hExcess_of_gate : PublishedHTExcessIdentity) :
    (∀ (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d),
      DesignClass n d (piStar n d) ∧
      (n ≤ pairCount d → piStar n d = fairSignKernel n d) ∧
      (pairCount d < n → (piStar n d).val = spectralRoundingKernel n d) ∧
      (∀ seed : SpectralSeeds n d, (∀ h, seed.2.2 h ∈ Icc (0 : ℝ) 1) →
        ∀ x i, (roundingIteration
          (spectralRows (shiftedSample x seed.1 seed.2.1)) seed.2.2 n).1 i =
            sgn (spectralSigns x seed i)) ∧
      ∀ s : ℝ, 0 < s → s ≤ 1 →
        aScale n d s = bScale n d s ∧ 0 < cLower 1 ∧ cLower 1 ≤ cLower s ∧
        ENNReal.ofReal (cLower s * aScale n d s) ≤ capacity n d s ∧
        capacity n d s ≤ worstLoss (piStar n d) s ∧
        worstLoss (piStar n d) s ≤ ENNReal.ofReal (3072 * aScale n d s) ∧
        (∀ ξ : PairIdx d (priorCutoff n d) → Bool,
          ∃ hm : Measurable (mXi s (priorCutoff n d) ξ) ∧
            MemLp (mXi s (priorCutoff n d) ξ) 2 (cubeMeasure d) ∧
            (∫ x, mXi s (priorCutoff n d) ξ x ∂cubeMeasure d) = 0,
            SobolevClass d s ⟨mXi s (priorCutoff n d) ξ, hm⟩) ∧
        (∀ π : Design n d, DesignClass n d π →
          ENNReal.ofReal (cLower s * aScale n d s) ≤ priorRisk π s) ∧
        (∀ π : Design n d, DesignClass n d π → ∀ m : CenteredL2Fn d,
          SobolevClass d s m → loss π m.val < ⊤ ∧
          (n : ℝ) * variance (fun ω => htEstimator ω.1.2 ω.2)
            (experimentLaw (covLaw n d)
              (gaussianCompletion (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) m) π.val) -
              4.01 = (loss π m.val).toReal) ∧
        gaussianCapacity n d (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) s = capacity n d s ∧
        gaussianWorst (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) (piStar n d) s =
          worstLoss (piStar n d) s ∧
        publishedCapacity n d (frozenUniformClass d s) = capacity n d s) ∧
    (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ ds : ℕ → ℕ, (∀ n, 2 ≤ ds n) →
      (Tendsto (fun n => capacity n (ds n) s) atTop (𝓝 0) ↔
        Tendsto (fun n => (pairCount (ds n) : ℝ) / n) atTop (𝓝 0)) ∧
      (Tendsto (fun n => (pairCount (ds n) : ℝ) / n) atTop (𝓝 0) ↔
        Asymptotics.IsLittleO atTop (fun n => (ds n : ℝ)) (fun n => Real.sqrt (n : ℝ)))) :=
  by
    obtain ⟨hCapacity, hVanishing, _⟩ := log_free_bivariate_capacity
      hContraction_of_gate hExcess_of_gate
    refine ⟨?_, hVanishing⟩
    intro n d hn hd
    obtain ⟨hDesign, hFairBranch, hSpectralBranch, hMoves, hSmoothness⟩ :=
      hCapacity n d hn hd
    refine ⟨hDesign, hFairBranch, hSpectralBranch, hMoves, ?_⟩
    intro s hs hs1
    obtain ⟨hScale, _, _, hPositive, hConstant, _, _, hLower, hMiddle,
      hUpper, hLegal, hPrior, hPublished, _, hGaussianCapacity,
      hGaussianWorst, _, _, hHT, _, _⟩ := hSmoothness s hs hs1
    refine ⟨hScale, hPositive, hConstant, hLower, hMiddle, hUpper, hLegal,
      hPrior, ?_, hGaussianCapacity, hGaussianWorst, hPublished⟩
    intro π hπ m hm
    obtain ⟨hIdentity, hFinite⟩ := hHT π hπ m hm
    exact ⟨hFinite, hIdentity⟩

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
