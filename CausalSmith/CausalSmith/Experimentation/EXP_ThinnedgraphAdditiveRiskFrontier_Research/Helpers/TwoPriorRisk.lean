module
public import Causalean.Stat.Minimax.LeCam
public import Causalean.Stat.Minimax.TotalVariation
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockPrior

/-!
# Full original-record two-prior risk reduction
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

variable {V Ξ : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace Ξ]

omit [DecidableEq V] in
/-- [Joint measurability of the record channel](hyp:hm) makes [its component laws measurable](goal). -/
-- @node: measurable_record_components
@[fun_prop] lemma measurable_record_components
    (D : Measure (Assign V × Audit V)) [IsProbabilityMeasure D]
    (s : Ξ → Schedule V)
    (hm : Measurable (fun x : Ξ × (Assign V × Audit V) => recordOf (s x.1) x.2)) :
    Measurable (fun ξ => D.map (recordOf (s ξ))) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  have hr (ξ : Ξ) : Measurable (recordOf (s ξ)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  simp_rw [Measure.map_apply (hr _) hE]
  exact measurable_measure_prodMk_left (hm hE)

/-- A measurable mixture of probability record channels is a probability law.  [For the stated data and conditions](hyp:D,π,s,hm), [the stated conclusion holds](goal). -/
-- @node: mixtureLaw_probability
lemma mixtureLaw_probability
    (D : Measure (Assign V × Audit V)) [IsProbabilityMeasure D]
    (π : Measure Ξ) [IsProbabilityMeasure π] (s : Ξ → Schedule V)
    (hm : Measurable (fun x : Ξ × (Assign V × Audit V) => recordOf (s x.1) x.2)) :
    IsProbabilityMeasure (mixtureLaw D π s) := by
  constructor
  unfold mixtureLaw
  rw [Measure.bind_apply MeasurableSet.univ (measurable_record_components D s hm).aemeasurable]
  have hr (ξ : Ξ) : Measurable (recordOf (s ξ)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  simp [Measure.map_apply (hr _) MeasurableSet.univ]

/-- Prior averaging of a constant-target family's seeded squared risk is bounded by the
worst fixed-schedule risk.  [For the stated data and conditions](hyp:D,π,s,hm,d,a,hs,T), [the stated conclusion holds](goal). -/
-- @node: mixture_seeded_risk_le_worst
lemma mixture_seeded_risk_le_worst
    (D : Measure (Assign V × Audit V)) [IsProbabilityMeasure D]
    (π : Measure Ξ) [IsProbabilityMeasure π] (s : Ξ → Schedule V)
    (hm : Measurable (fun x : Ξ × (Assign V × Audit V) => recordOf (s x.1) x.2))
    (d : ℕ) (a : ℝ) (hs : ∀ᵐ ξ ∂π, ScheduleClass (s ξ) d ∧ tte (s ξ) = a)
    (T : Estimator V) :
    (∫⁻ x, ENNReal.ofReal ((T.1 x - a) ^ 2)
      ∂((mixtureLaw D π s).prod seedLaw)) ≤ worstRisk D d T := by
  let : IsProbabilityMeasure seedLaw := ⟨by simp [seedLaw, Real.volume_Icc]⟩
  let : IsProbabilityMeasure (mixtureLaw D π s) := mixtureLaw_probability D π s hm
  have hf : Measurable (fun x : Record V × ℝ => ENNReal.ofReal ((T.1 x - a) ^ 2)) := by
    exact ((T.2.sub measurable_const).pow_const 2).ennreal_ofReal
  rw [lintegral_prod _ hf.aemeasurable]
  unfold mixtureLaw
  rw [Measure.lintegral_bind (measurable_record_components D s hm).aemeasurable
    hf.lintegral_prod_right'.aemeasurable]
  calc
    _ ≤ ∫⁻ _ : Ξ, worstRisk D d T ∂π := by
      apply lintegral_mono_ae
      filter_upwards [hs] with ξ hξ
      have hr : Measurable (recordOf (s ξ)) :=
        hm.comp (measurable_const.prodMk measurable_id)
      rw [lintegral_map hf.lintegral_prod_right' hr]
      have heq : (∫⁻ ω, ∫⁻ u, ENNReal.ofReal ((T.1 (recordOf (s ξ) ω, u) - a) ^ 2)
          ∂seedLaw ∂D) = sqLoss D (s ξ) T := by
        unfold sqLoss recordLaw
        rw [hξ.2]
        have hmseed : Measurable (fun ω : (Assign V × Audit V) × ℝ =>
            (recordOf (s ξ) ω.1, ω.2)) :=
          (hr.comp measurable_fst).prodMk measurable_snd
        rw [lintegral_map hf hmseed]
        exact (lintegral_prod _ (hf.comp hmseed).aemeasurable).symm
      rw [heq]
      exact le_iSup (fun θ : {θ : Schedule V // ScheduleClass θ d} => sqLoss D θ.1 T)
        ⟨s ξ, hξ.1⟩
    _ = worstRisk D d T := by simp

/-- Each sign error costs at least the squared target amplitude, also for infinite risk.  [For the stated data and conditions](hyp:X,P,t,ht,a,ha,σ), [the stated conclusion holds](goal). -/
-- @node: threshold_squared_error_le_risk
lemma threshold_squared_error_le_risk {X : Type*} [MeasurableSpace X]
    (P : Measure X) (t : X → ℝ) (ht : Measurable t) (a : ℝ) (ha : 0 ≤ a)
    (σ : Bool) :
    ENNReal.ofReal (a ^ 2) * P (if σ then {x | t x < 0} else {x | t x < 0}ᶜ) ≤
      ∫⁻ x, ENNReal.ofReal ((t x - signOf σ * a) ^ 2) ∂P := by
  have hE : MeasurableSet {x | t x < 0} := measurableSet_lt ht measurable_const
  have hmeas : MeasurableSet (if σ then {x | t x < 0} else {x | t x < 0}ᶜ) := by
    cases σ <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> first | exact hE | exact hE.compl
  rw [← lintegral_indicator_const hmeas]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ (if σ then {x | t x < 0} else {x | t x < 0}ᶜ)
  · rw [Set.indicator_of_mem hx]
    apply ENNReal.ofReal_le_ofReal
    cases σ
    · have hx' : 0 ≤ t x := by simpa using hx
      simp only [signOf, Bool.false_eq_true, ↓reduceIte]
      nlinarith [sq_nonneg (t x)]
    · have hx' : t x < 0 := hx
      simp only [signOf, ↓reduceIte]
      nlinarith [sq_nonneg (t x)]
  · rw [Set.indicator_of_notMem hx]
    exact bot_le

/-- Threshold testing of two opposite targets bounds any common upper bound on their risks.  [For the stated data and conditions](hyp:X,P,M,t,ht,a,ha,R,hP,hM), [the stated conclusion holds](goal). -/
-- @node: two_prior_squared_testing
lemma two_prior_squared_testing {X : Type*} [MeasurableSpace X]
    (P M : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure M]
    (t : X → ℝ) (ht : Measurable t) (a : ℝ) (ha : 0 < a) (R : ℝ≥0∞)
    (hP : (∫⁻ x, ENNReal.ofReal ((t x - a) ^ 2) ∂P) ≤ R)
    (hM : (∫⁻ x, ENNReal.ofReal ((t x - -a) ^ 2) ∂M) ≤ R) :
    ENNReal.ofReal (a ^ 2 / 2 * (1 - Causalean.Stat.tvDist P M)) ≤ R := by
  have hE : MeasurableSet {x | t x < 0} := measurableSet_lt ht measurable_const
  have htest := ENNReal.ofReal_le_ofReal
    (Causalean.Stat.one_sub_tvDist_le_test (μ := P) (ν := M) hE)
  rw [ENNReal.ofReal_add (measureReal_nonneg) (measureReal_nonneg),
    ofReal_measureReal, ofReal_measureReal] at htest
  have hplus := threshold_squared_error_le_risk P t ht a ha.le true
  have hminus := threshold_squared_error_le_risk M t ht a ha.le false
  simp only [signOf, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at hplus hminus
  have hsum : ENNReal.ofReal (a ^ 2) * ENNReal.ofReal (1 - Causalean.Stat.tvDist P M) ≤
      2 * R := by
    calc
      _ ≤ ENNReal.ofReal (a ^ 2) * (P {x | t x < 0} + M {x | t x < 0}ᶜ) :=
        mul_le_mul le_rfl htest zero_le zero_le
      _ ≤ R + R := by rw [mul_add]; exact add_le_add (hplus.trans hP) (hminus.trans hM)
      _ = 2 * R := (two_mul R).symm
  have hconst : ENNReal.ofReal (a ^ 2) * ENNReal.ofReal (1 - Causalean.Stat.tvDist P M) =
      2 * ENNReal.ofReal (a ^ 2 / 2 * (1 - Causalean.Stat.tvDist P M)) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg a), ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    congr 1
    ring
  rw [hconst] at hsum
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hsum

variable {ΞPlus ΞMinus : Type*}
    [MeasurableSpace ΞPlus] [MeasurableSpace ΞMinus]

/-- Opposite constant-target priors give the full-record lower bound for every measurable seeded
estimator.  [For the stated data and conditions](hyp:n,d,q,hn,hd,hdu,hq,πPlus,πMinus,sPlus,sMinus,hmPlus,hmMinus,Δ,hΔ,hPlus,hMinus), [the stated conclusion holds](goal). -/
-- @node: lem:full-record-two-prior-risk
lemma full_record_two_prior_risk (n d : ℕ) (q : ℝ)
    (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n - 1) (hq : q ∈ Set.Icc 0 1)
    (πPlus : Measure ΞPlus) (πMinus : Measure ΞMinus)
    [IsProbabilityMeasure πPlus] [IsProbabilityMeasure πMinus]
    (sPlus : ΞPlus → Schedule (Fin n)) (sMinus : ΞMinus → Schedule (Fin n))
    (hmPlus : Measurable (fun x : ΞPlus × (Assign (Fin n) × Audit (Fin n)) =>
      recordOf (sPlus x.1) x.2))
    (hmMinus : Measurable (fun x : ΞMinus × (Assign (Fin n) × Audit (Fin n)) =>
      recordOf (sMinus x.1) x.2))
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hPlus : ∀ᵐ ξ ∂πPlus, ScheduleClass (sPlus ξ) d ∧ tte (sPlus ξ) = Δ)
    (hMinus : ∀ᵐ ξ ∂πMinus, ScheduleClass (sMinus ξ) d ∧ tte (sMinus ξ) = -Δ) :
    ENNReal.ofReal (Δ ^ 2 / 2 * (1 - Causalean.Stat.tvDist
      (mixtureLaw (thinnedDesign (Fin n) q) πPlus sPlus)
      (mixtureLaw (thinnedDesign (Fin n) q) πMinus sMinus))) ≤
        minimaxRisk (thinnedDesign (Fin n) q) d := by
  have _population_regime := hn
  have _degree_lower := hd
  have _degree_upper := hdu
  let D := thinnedDesign (Fin n) q
  let : IsProbabilityMeasure D := thinnedDesign_probabilityDesign q hq
  let : IsProbabilityMeasure seedLaw := ⟨by simp [seedLaw, Real.volume_Icc]⟩
  let P := mixtureLaw D πPlus sPlus
  let M := mixtureLaw D πMinus sMinus
  let : IsProbabilityMeasure P := mixtureLaw_probability D πPlus sPlus hmPlus
  let : IsProbabilityMeasure M := mixtureLaw_probability D πMinus sMinus hmMinus
  have htv : Causalean.Stat.tvDist (P.prod seedLaw) (M.prod seedLaw) =
      Causalean.Stat.tvDist P M := by
    simpa using Causalean.Stat.tvDist_compProd_eq P M (ProbabilityTheory.Kernel.const _ seedLaw)
  change _ ≤ ⨅ T : Estimator (Fin n), worstRisk D d T
  apply le_iInf
  intro T
  have hP := mixture_seeded_risk_le_worst D πPlus sPlus hmPlus d Δ hPlus T
  have hM := mixture_seeded_risk_le_worst D πMinus sMinus hmMinus d (-Δ) hMinus T
  have htest := two_prior_squared_testing (P.prod seedLaw) (M.prod seedLaw)
    T.1 T.2 Δ hΔ (worstRisk D d T) hP hM
  rw [htv] at htest
  exact htest

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
