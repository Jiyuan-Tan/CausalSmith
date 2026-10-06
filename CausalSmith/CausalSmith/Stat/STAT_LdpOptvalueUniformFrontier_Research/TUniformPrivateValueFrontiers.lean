module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.UpperCalibration
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.ValueSequences
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.TTwoCellCalibration

/-!
# TUniformPrivateValueFrontiers

Finite original-record private value frontiers: TUniformPrivateValueFrontiers.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

variable {n d : ℕ}


/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [the Cai–Low moment-duality theorem](hyp:hDual), and [the Bernstein absolute-approximation limit](hyp:hBernstein). [Per-decision sequential lower bounds survive both minimax infima](goal). -/
-- @node: frontier_minimax_lower_of_gate
lemma frontier_minimax_lower_of_gate (hRN : MeasurableKernelRadonNikodym)
    (hDual : CaiLowMomentDuality) (hBernstein : BernsteinAbsoluteApproximationLimit) :
    ∃ c : ℝ, 0 < c ∧ ∀ n d eps, Allowed n d eps →
      ∀ S : SamplingScheme n d, IidPeople S → IndependentRandomness S →
      ∀ C : ProtocolClassLabel,
        ENNReal.ofReal (c*rateR C n d eps) ≤ minimaxRisk S C eps ∧
        ENNReal.ofReal (c*rateH C n d eps) ≤ honestLength S C eps := by
  obtain ⟨c, hc, hLower⟩ := frontier_lower_of_gate hRN hDual hBernstein
  refine ⟨c, hc, ?_⟩
  intro n d eps hAllowed S hIID hRandom C
  have hSeq : ∀ Q : LocalProtocol n (ObsRecord d), protocolClass C Q eps →
      SequentialClass Q eps := by
    intro Q hQ
    cases C with
    | NI => exact NoninteractiveClass.toSequentialClass Q eps hQ
    | SI => exact hQ
  constructor
  · unfold minimaxRisk riskValue Causalean.Stat.minimaxValueENNReal
    apply le_iInf
    intro e
    exact (hLower n d eps hAllowed S hIID hRandom e.1.1 (hSeq _ e.1.2)).1 e.2
  · unfold honestLength lengthValue Causalean.Stat.minimaxValueENNReal
    apply le_iInf
    intro e
    exact (hLower n d eps hAllowed S hIID hRandom e.1.1 (hSeq _ e.1.2)).2 e.2.1 e.2.2

/-- Assume [the stated hc condition](hyp:hc), [the stated c condition](hyp:hC), [the stated hr condition](hyp:hr), [the stated r assumption and the function H](hyp:R,H), [the stated rlo condition](hyp:hRlo), [the stated rhi condition](hyp:hRhi), [the stated hlo condition](hyp:hHlo), and [the stated hhi condition](hyp:hHhi). [Separate risk and honest-length bounds imply their square-root comparison](goal). -/
-- @node: frontier_square_comparison
lemma frontier_square_comparison (c C r : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hr : 0 ≤ r) (R H : ℝ≥0∞)
    (hRlo : ENNReal.ofReal (c*r) ≤ R) (hRhi : R ≤ ENNReal.ofReal (C*r))
    (hHlo : ENNReal.ofReal (c*Real.sqrt r) ≤ H)
    (hHhi : H ≤ ENNReal.ofReal (C*Real.sqrt r)) :
    ENNReal.ofReal (c^2/C)*R ≤ H^2 ∧ H^2 ≤ ENNReal.ofReal (C^2/c)*R := by
  have hRf : R ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hRhi
  have hHf : H ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hHhi
  have hRl : c*r ≤ R.toReal := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hc.le hr)] using
      ENNReal.toReal_mono hRf hRlo
  have hRu : R.toReal ≤ C*r := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hC.le hr)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hRhi
  have hHl : c*Real.sqrt r ≤ H.toReal := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hc.le (Real.sqrt_nonneg r))] using
      ENNReal.toReal_mono hHf hHlo
  have hHu : H.toReal ≤ C*Real.sqrt r := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.sqrt_nonneg r))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hHhi
  have hsqlo : c^2*r ≤ H.toReal^2 := by
    have h := mul_le_mul hHl hHl
      (mul_nonneg hc.le (Real.sqrt_nonneg r)) ENNReal.toReal_nonneg
    simpa only [← sq, mul_pow, Real.sq_sqrt hr] using h
  have hsqup : H.toReal^2 ≤ C^2*r := by
    have h := mul_le_mul hHu hHu ENNReal.toReal_nonneg
      (mul_nonneg hC.le (Real.sqrt_nonneg r))
    simpa only [← sq, mul_pow, Real.sq_sqrt hr] using h
  constructor
  · apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRf)
      (ENNReal.pow_ne_top hHf)).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ c^2/C)]
    calc
      (c^2/C)*R.toReal ≤ (c^2/C)*(C*r) :=
        mul_le_mul_of_nonneg_left hRu (by positivity)
      _ = c^2*r := by field_simp <;> ring
      _ ≤ H.toReal^2 := hsqlo
  · apply (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top hHf)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRf)).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ C^2/c)]
    calc
      H.toReal^2 ≤ C^2*r := hsqup
      _ = (C^2/c)*(c*r) := by field_simp <;> ring
      _ ≤ (C^2/c)*R.toReal := mul_le_mul_of_nonneg_left hRl (by positivity)

/-- Assume [the stated hc condition](hyp:hc), [the stated c condition](hyp:hC), [the stated hr condition](hyp:hr), [the stated a assumption and the constant B](hyp:A,B), [the stated ba condition](hyp:hBA), [the stated blo condition](hyp:hBlo), and [the stated ahi condition](hyp:hAhi). [Nested finite positive values with common rate bounds have bounded ratios](goal). -/
-- @node: frontier_ratio_comparison
lemma frontier_ratio_comparison (c C r : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hr : 0 < r) (A B : ℝ≥0∞) (hBA : B ≤ A)
    (hBlo : ENNReal.ofReal (c*r) ≤ B) (hAhi : A ≤ ENNReal.ofReal (C*r)) :
    1 ≤ A/B ∧ A/B ≤ ENNReal.ofReal (C/c) := by
  have hAf : A ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hAhi
  have hBf : B ≠ ∞ := ne_top_of_le_ne_top hAf hBA
  have hBp : 0 < B := (ENNReal.ofReal_pos.mpr (mul_pos hc hr)).trans_le hBlo
  have hB0 : B ≠ 0 := ne_of_gt hBp
  have hBt : 0 < B.toReal := ENNReal.toReal_pos hB0 hBf
  have hBl : c*r ≤ B.toReal := by
    simpa only [ENNReal.toReal_ofReal (mul_pos hc hr).le] using
      ENNReal.toReal_mono hBf hBlo
  have hAu : A.toReal ≤ C*r := by
    simpa only [ENNReal.toReal_ofReal (mul_pos hC hr).le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hAhi
  have hAB : B.toReal ≤ A.toReal := ENNReal.toReal_mono hAf hBA
  have hdivf : A/B ≠ ∞ := ENNReal.div_ne_top hAf hB0
  constructor
  · apply (ENNReal.toReal_le_toReal (by simp) hdivf).mp
    simp only [ENNReal.toReal_one, ENNReal.toReal_div]
    exact (le_div_iff₀ hBt).mpr (by simpa using hAB)
  · apply (ENNReal.toReal_le_toReal hdivf ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity : 0 ≤ C/c)]
    apply (div_le_iff₀ hBt).mpr
    calc
      A.toReal ≤ C*r := hAu
      _ = (C/c)*(c*r) := by field_simp <;> ring
      _ ≤ (C/c)*B.toReal := mul_le_mul_of_nonneg_left hBl (by positivity)

/-- Fix [the sampling scheme S](hyp:S) and [the privacy budget and the constant C0](hyp:eps,C0). [Every finite causal upper bound is attained by the resource-selected explicit protocol](goal). -/
def ConcreteCausalAttainment (S : SamplingScheme n d) (eps C0 : ℝ) : Prop :=
  let design := frontierDesign n d eps
  NoninteractiveClass design.protocol eps ∧
    ∀ P ∈ causalClass d,
      squaredRisk (decisionLaw S design.protocol P) design.estimator
        (value P) ≤
        ENNReal.ofReal (C0*rateR .NI n d eps) ∧
      (0.90 : ℝ) ≤ coverage (decisionLaw S design.protocol P)
        design.interval (value P) ∧
      expectedLength (decisionLaw S design.protocol P) design.interval ≤
        ENNReal.ofReal (C0*rateH .NI n d eps)

-- @node: thm:uniform-private-value-frontiers
/-- Given the [Bernstein absolute-approximation limit](hyp:hBernstein_of_gate), the causal experiment
satisfies the [complete finite-resource
frontier, explicit attainment, NI/SI and risk/length comparisons, saturation, consistency,
private-parametric boundary, and growing-dimension elbow](goal). -/
theorem uniform_private_value_frontiers
    (hBernstein_of_gate : BernsteinAbsoluteApproximationLimit) :
    ∃ c C0 : ℝ, 0 < c ∧ c ≤ C0 ∧
      -- @realizes c(universal positive lower constant); @realizes C_0(universal finite upper constant)
    (∀ (n d : ℕ) (eps : ℝ), Allowed n d eps →
      ∀ (S : SamplingScheme n d), IidPeople S → IndependentRandomness S →
        (∀ C : ProtocolClassLabel,
          ENNReal.ofReal (c*rateR C n d eps) ≤ minimaxRisk S C eps ∧
          minimaxRisk S C eps ≤ ENNReal.ofReal (C0*rateR C n d eps) ∧
          ENNReal.ofReal (c*rateH C n d eps) ≤ honestLength S C eps ∧
          honestLength S C eps ≤ ENNReal.ofReal (C0*rateH C n d eps) ∧
          CausalAttainment S eps (rateR C n d eps) (rateH C n d eps) C0 ∧
          ENNReal.ofReal (c^2/C0) * minimaxRisk S C eps ≤ (honestLength S C eps)^2 ∧
          (honestLength S C eps)^2 ≤ ENNReal.ofReal (C0^2/c) * minimaxRisk S C eps) ∧
        ConcreteCausalAttainment S eps C0 ∧
        (1 : ℝ≥0∞) ≤ minimaxRisk S .NI eps / minimaxRisk S .SI eps ∧
        minimaxRisk S .NI eps / minimaxRisk S .SI eps ≤ ENNReal.ofReal (C0/c) ∧
        (1 : ℝ≥0∞) ≤ honestLength S .NI eps / honestLength S .SI eps ∧
        honestLength S .NI eps / honestLength S .SI eps ≤ ENNReal.ofReal (C0/c)) ∧
    RateResourceConclusions ∧
    (∀ (schemes : (n d : ℕ) → SamplingScheme n d),
      (∀ n d, IidPeople (schemes n d)) → (∀ n d, IndependentRandomness (schemes n d)) →
      ∀ C : ProtocolClassLabel,
        ValueSequenceConclusions
          (fun n d eps => (minimaxRisk (schemes n d) C eps).toReal)
          (fun n d eps => (honestLength (schemes n d) C eps).toReal)) := by
  -- Assemble the explicit NI upper bound with the per-decision SI converse.
  have hFinite :
    ∃ c C0 : ℝ, 0 < c ∧ c ≤ C0 ∧
      -- @realizes c(universal positive lower constant); @realizes C_0(universal finite upper constant)
    (∀ (n d : ℕ) (eps : ℝ), Allowed n d eps →
      ∀ (S : SamplingScheme n d), IidPeople S → IndependentRandomness S →
        (∀ C : ProtocolClassLabel,
          ENNReal.ofReal (c*rateR C n d eps) ≤ minimaxRisk S C eps ∧
          minimaxRisk S C eps ≤ ENNReal.ofReal (C0*rateR C n d eps) ∧
          ENNReal.ofReal (c*rateH C n d eps) ≤ honestLength S C eps ∧
          honestLength S C eps ≤ ENNReal.ofReal (C0*rateH C n d eps) ∧
          CausalAttainment S eps (rateR C n d eps) (rateH C n d eps) C0 ∧
          ENNReal.ofReal (c^2/C0) * minimaxRisk S C eps ≤ (honestLength S C eps)^2 ∧
          (honestLength S C eps)^2 ≤ ENNReal.ofReal (C0^2/c) * minimaxRisk S C eps) ∧
        ConcreteCausalAttainment S eps C0 ∧
        (1 : ℝ≥0∞) ≤ minimaxRisk S .NI eps / minimaxRisk S .SI eps ∧
        minimaxRisk S .NI eps / minimaxRisk S .SI eps ≤ ENNReal.ofReal (C0/c) ∧
        (1 : ℝ≥0∞) ≤ honestLength S .NI eps / honestLength S .SI eps ∧
        honestLength S .NI eps / honestLength S .SI eps ≤ ENNReal.ofReal (C0/c)) := by
    obtain ⟨cLower, hcLower, hLower⟩ :=
      frontier_minimax_lower_of_gate measurableKernelRadonNikodym_proved
        caiLowMomentDuality_proved hBernstein_of_gate
    obtain ⟨cUpper, hcUpper, hUpper⟩ :=
      frontier_upper_of_gate caiLowChebyshevApproximation_proved boundedMeanConcentration_proved
    let c := min cLower 1
    let C0 := max 1 (max cUpper (Real.sqrt (40*cUpper)))
    have hc : 0 < c := lt_min hcLower (by norm_num)
    have hC0 : 0 < C0 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hcC : c ≤ C0 := (min_le_right _ _).trans (le_max_left _ _)
    have hUpperC : cUpper ≤ C0 := (le_max_left _ _).trans (le_max_right _ _)
    have hLengthC : Real.sqrt (40*cUpper) ≤ C0 :=
      (le_max_right _ _).trans (le_max_right _ _)
    refine ⟨c, C0, hc, hcC, ?_⟩
    intro n d eps hAllowed S hIID hRandom
    have hn : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by have := hAllowed.1; omega)
    have ht : 0 < (n : ℝ)*eps^2 := mul_pos hn (sq_pos_of_pos hAllowed.2.2.1)
    have hr : 0 < rateR .NI n d eps :=
      (by positivity : (0 : ℝ) < min 1 (1/(n*eps^2))).trans_le
        (rho_elementary_comparisons n d eps hAllowed).1
    have hh : 0 < rateH .NI n d eps := Real.sqrt_pos.mpr hr
    obtain ⟨hNI, hDesign⟩ := hUpper n d eps hAllowed S hIID hRandom
    have hBounds : ∀ P ∈ causalClass d,
        squaredRisk (decisionLaw S (frontierProtocol n d eps) P)
          (frontierEstimator n d eps) (value P) ≤ ENNReal.ofReal (C0*rateR .NI n d eps) ∧
        (0.90 : ℝ) ≤ coverage (decisionLaw S (frontierProtocol n d eps) P)
          (frontierInterval n d eps) (value P) ∧
        expectedLength (decisionLaw S (frontierProtocol n d eps) P)
          (frontierInterval n d eps) ≤ ENNReal.ofReal (C0*rateH .NI n d eps) := by
      intro P hP
      obtain ⟨hR, hCov, hH⟩ := hDesign P hP
      exact ⟨hR.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hUpperC hr.le)), hCov,
        hH.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hLengthC hh.le))⟩
    have hAttain : CausalAttainment S eps (rateR .NI n d eps) (rateH .NI n d eps) C0 := by
      refine ⟨frontierProtocol n d eps, hNI, frontierEstimator n d eps,
        frontierInterval n d eps, ?_, hBounds⟩
      refine ⟨fun z => frontierEstimate n d eps (z, (0 : Fin 1), 0), ?_, ?_⟩
      · exact (frontierEstimate_measurable n d eps).comp
            (by fun_prop : Measurable (fun z : ProtocolTranscript (frontierProtocol n d eps) =>
              (z, (0 : Fin 1), (0 : ℝ))))
      · intro w
        rfl
    have hBase : ∀ C : ProtocolClassLabel,
        ENNReal.ofReal (c*rateR C n d eps) ≤ minimaxRisk S C eps ∧
        minimaxRisk S C eps ≤ ENNReal.ofReal (C0*rateR C n d eps) ∧
        ENNReal.ofReal (c*rateH C n d eps) ≤ honestLength S C eps ∧
        honestLength S C eps ≤ ENNReal.ofReal (C0*rateH C n d eps) := by
      intro C
      obtain ⟨hRl, hHl⟩ := hLower n d eps hAllowed S hIID hRandom C
      obtain ⟨hRu, hHu⟩ := causalAttainment_minimax_upper S eps _ _ C0 hAttain C
      exact ⟨(ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (min_le_left cLower 1) hr.le)).trans hRl,
        hRu, (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (min_le_left cLower 1) hh.le)).trans hHl, hHu⟩
    have hInclusion := ni_si_values S eps
    have hRiskRatio := frontier_ratio_comparison c C0 (rateR .NI n d eps) hc hC0 hr
      (minimaxRisk S .NI eps) (minimaxRisk S .SI eps) hInclusion.1
      (hBase .SI).1 (hBase .NI).2.1
    have hLengthRatio := frontier_ratio_comparison c C0 (rateH .NI n d eps) hc hC0 hh
      (honestLength S .NI eps) (honestLength S .SI eps) hInclusion.2
      (hBase .SI).2.2.1 (hBase .NI).2.2.2
    refine ⟨?_, ⟨hNI, hBounds⟩, hRiskRatio.1, hRiskRatio.2,
      hLengthRatio.1, hLengthRatio.2⟩
    intro C
    obtain ⟨hRl, hRu, hHl, hHu⟩ := hBase C
    have hSquare := frontier_square_comparison c C0 (rateR C n d eps) hc hC0 hr.le
      (minimaxRisk S C eps) (honestLength S C eps) hRl hRu hHl hHu
    exact ⟨hRl, hRu, hHl, hHu, hAttain, hSquare⟩
  obtain ⟨c, C0, hc, hcC, hFinite⟩ := hFinite
  refine ⟨c, C0, hc, hcC, hFinite, rate_resource_conclusions, ?_⟩
  intro schemes hIID hRandom C
  apply value_sequence_conclusions_of_bounds _ _ c C0 hc hcC
  intro n d eps hAllowed
  obtain ⟨hRlo, hRhi, hHlo, hHhi, _⟩ :=
    (hFinite n d eps hAllowed (schemes n d) (hIID n d) (hRandom n d)).1 C
  have hRfin : minimaxRisk (schemes n d) C eps ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hRhi
  have hHfin : honestLength (schemes n d) C eps ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hHhi
  have hrho : 0 ≤ rho (n*eps^2) d :=
    (by positivity : (0 : ℝ) ≤ min 1 (1/(n*eps^2))).trans
      (rho_elementary_comparisons n d eps hAllowed).1
  have hC0 : 0 < C0 := hc.trans_le hcC
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [rateR, ENNReal.toReal_ofReal (mul_nonneg hc.le hrho)] using
      ENNReal.toReal_mono hRfin hRlo
  · simpa only [rateR, ENNReal.toReal_ofReal (mul_nonneg hC0.le hrho)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hRhi
  · simpa only [rateH, rateR,
      ENNReal.toReal_ofReal (mul_nonneg hc.le (Real.sqrt_nonneg _))] using
      ENNReal.toReal_mono hHfin hHlo
  · simpa only [rateH, rateR,
      ENNReal.toReal_ofReal (mul_nonneg hC0.le (Real.sqrt_nonneg _))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hHhi


end CausalSmith.Stat.LdpOptvalueUniformFrontier
