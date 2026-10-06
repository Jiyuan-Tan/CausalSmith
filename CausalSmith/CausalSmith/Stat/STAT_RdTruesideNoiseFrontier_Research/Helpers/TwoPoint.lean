module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.LowerWitness
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product
public import Causalean.Stat.Minimax.OverlapCoupling

/-!
# True-side Gaussian measurement-error endpoint frontier

Helpers/Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


/-- The common submeasure bounds the sum of extended absolute risks by separation times overlap. Given [the displayed inputs and assumptions](hyp:Ω,A,B,T,hT,a,b), [the stated mathematical conclusion holds](goal). -/
lemma twoPoint_absRisk_sum {Ω : Type*} [MeasurableSpace Ω] (A B : Measure Ω)
    [IsProbabilityMeasure A] [IsProbabilityMeasure B]
    (T : Ω → ℝ) (hT : Measurable T) (a b : ℝ) :
    ENNReal.ofReal (|a-b| * (1 - tvDist A B)) ≤
      (∫⁻ z, ENNReal.ofReal |T z - a| ∂A) +
      (∫⁻ z, ENNReal.ofReal |T z - b| ∂B) := by
  let R := Causalean.Stat.rnCommonPart A B (A+B)
  have ha : A ≪ A+B := (le_add_of_nonneg_right bot_le).absolutelyContinuous
  have hb : B ≪ A+B := (le_add_of_nonneg_left bot_le).absolutelyContinuous
  have hRA := Causalean.Stat.rnCommonPart_le_left A B (A+B) ha
  have hRB := Causalean.Stat.rnCommonPart_le_right A B (A+B) hb
  have hmass := Causalean.Stat.rnCommonPart_mass_eq_one_sub_tvDist A B (A+B) ha hb
  calc
    ENNReal.ofReal (|a-b| * (1 - tvDist A B)) = ∫⁻ z, ENNReal.ofReal |a-b| ∂(R) := by
      rw [lintegral_const, hmass, ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ ∫⁻ z, ENNReal.ofReal |T z - a| + ENNReal.ofReal |T z - b| ∂(R) := by
      apply lintegral_mono
      intro z
      calc
        ENNReal.ofReal |a-b| ≤ ENNReal.ofReal (|T z-a| + |T z-b|) := by
          apply ENNReal.ofReal_le_ofReal
          simpa [abs_sub_comm] using abs_sub_le a (T z) b
        _ ≤ _ := ENNReal.ofReal_add_le
    _ = (∫⁻ z, ENNReal.ofReal |T z-a| ∂(R)) +
        (∫⁻ z, ENNReal.ofReal |T z-b| ∂(R)) := by
      apply lintegral_add_left
      fun_prop
    _ ≤ _ := add_le_add (lintegral_mono' hRA le_rfl) (lintegral_mono' hRB le_rfl)

/-- Honesty at two targets and total variation at most one fifth force expected length at least three fifths of separation. Given [the displayed inputs and assumptions](hyp:Ω,A,B,lo,hi,hlo,hhi,a,b,ha,hb,htv), [the stated mathematical conclusion holds](goal). -/
lemma twoPoint_interval_lower {Ω : Type*} [MeasurableSpace Ω] (A B : Measure Ω)
    [IsProbabilityMeasure A] [IsProbabilityMeasure B]
    (lo hi : Ω → ℝ) (hlo : Measurable lo) (hhi : Measurable hi) (a b : ℝ)
    (ha : (9/10 : ℝ) ≤ A.real (Causalean.Stat.coverageEvent lo hi a))
    (hb : (9/10 : ℝ) ≤ B.real (Causalean.Stat.coverageEvent lo hi b))
    (htv : tvDist A B ≤ (1/5 : ℝ)) :
    ENNReal.ofReal ((3/5 : ℝ) * |a-b|) ≤
      ∫⁻ z, ENNReal.ofReal (Causalean.Stat.intervalLength (lo z) (hi z)) ∂B := by
  let E := Causalean.Stat.coverageEvent lo hi a
  let F := Causalean.Stat.coverageEvent lo hi b
  have hE : MeasurableSet E := Causalean.Stat.measurableSet_coverageEvent hlo hhi
  have hF : MeasurableSet F := Causalean.Stat.measurableSet_coverageEvent hlo hhi
  have hgap := Causalean.Stat.abs_measureReal_sub_le_tvDist (μ := A) (ν := B) hE
  have hboth : (3/5 : ℝ) ≤ B.real (E ∩ F) := by
    have hu := measureReal_union_add_inter (μ := B) hF (s := E)
    have hule : B.real (E ∪ F) ≤ 1 := measureReal_le_one
    change (9/10 : ℝ) ≤ A.real E at ha
    change (9/10 : ℝ) ≤ B.real F at hb
    have hg := (abs_le.mp (hgap.trans htv)).2
    linarith
  calc
    ENNReal.ofReal ((3/5 : ℝ) * |a-b|) ≤ ENNReal.ofReal |a-b| * B (E ∩ F) := by
      rw [mul_comm (3/5 : ℝ), ENNReal.ofReal_mul (abs_nonneg _)]
      apply mul_le_mul_right
      rw [← ENNReal.ofReal_toReal (measure_ne_top B _)]
      exact ENNReal.ofReal_le_ofReal hboth
    _ = ∫⁻ z, (E ∩ F).indicator (fun _ => ENNReal.ofReal |a-b|) z ∂B := by
      rw [lintegral_indicator (hE.inter hF), lintegral_const, Measure.restrict_apply_univ]
    _ ≤ _ := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ E ∩ F
      · rw [Set.indicator_of_mem hz]
        apply ENNReal.ofReal_le_ofReal
        rcases hz with ⟨hza, hzb⟩
        change lo z ≤ a ∧ a ≤ hi z at hza
        change lo z ≤ b ∧ b ≤ hi z at hzb
        unfold Causalean.Stat.intervalLength
        exact (show |a-b| ≤ hi z - lo z from abs_le.mpr ⟨by linarith [hza.1, hzb.2], by linarith [hza.2, hzb.1]⟩).trans (le_max_right _ _)
      · simp [Set.indicator_of_notMem hz]
/-- The independent observed sample is a probability law. Given [the displayed inputs and assumptions](hyp:P,σ,n), [the stated mathematical conclusion holds](goal). -/
lemma sampleLaw_probability (P : LatentLaw) (σ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sampleLaw P σ n) := by
  letI := P.prob
  haveI : IsProbabilityMeasure (Pobs P σ) := by
    unfold Pobs
    exact Measure.isProbabilityMeasure_map (obs_measurable σ).aemeasurable
  unfold sampleLaw
  infer_instance

/-- Appending the independent uniform seed preserves probability normalization. Given [the displayed inputs and assumptions](hyp:P,σ,n), [the stated mathematical conclusion holds](goal). -/
lemma experiment_probability (P : LatentLaw) (σ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (experiment P σ n) := by
  letI := sampleLaw_probability P σ n
  unfold experiment seedLaw
  infer_instance

/-- Appending the same independent seed cannot increase total variation. Given [the displayed inputs and assumptions](hyp:P,Q,σ,n), [the stated mathematical conclusion holds](goal). -/
lemma experiment_tv_le (P Q : LatentLaw) (σ : ℝ) (n : ℕ) :
    tvDist (experiment P σ n) (experiment Q σ n) ≤
      tvDist (sampleLaw P σ n) (sampleLaw Q σ n) := by
  letI := sampleLaw_probability P σ n
  letI := sampleLaw_probability Q σ n
  haveI : IsProbabilityMeasure seedLaw := by unfold seedLaw; infer_instance
  have h := Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_prod_le_add
    (sampleLaw P σ n) (sampleLaw Q σ n) seedLaw seedLaw
  have hz : tvDist seedLaw seedLaw = 0 := by
    unfold tvDist Causalean.Stat.tvDist
    simp
  simpa [experiment, hz] using h

/-- Interior conditional-mean bounds put the target contrast in the half-unit interval. Given [the displayed inputs and assumptions](hyp:β,σ,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma theta_model_bounds (β σ : ℝ) (P : LatentLaw) (hP : Model β σ P) :
    |theta P| ≤ 1/2 := by
  have h₀ := hP.means false 0 (by norm_num)
  have h₁ := hP.means true 0 (by norm_num)
  unfold theta
  exact abs_le.mpr ⟨by linarith [h₀.1, h₁.2], by linarith [h₁.1, h₀.2]⟩

/-- A lower bound on the sum of two extended risks yields half that bound for their maximum. Given [the displayed inputs and assumptions](hyp:x,y,c,hc,hsum), [the stated mathematical conclusion holds](goal). -/
lemma twoPoint_max_of_sum (x y : ℝ≥0∞) (c : ℝ) (hc : 0 ≤ c)
    (hsum : ENNReal.ofReal (2*c) ≤ x+y) : ENNReal.ofReal c ≤ max x y := by
  by_contra h
  have hx : x < ENNReal.ofReal c := (le_max_left _ _).trans_lt (lt_of_not_ge h)
  have hy : y < ENNReal.ofReal c := (le_max_right _ _).trans_lt (lt_of_not_ge h)
  have hadd := ENNReal.add_lt_add hx hy
  rw [← ENNReal.ofReal_add hc hc, ← two_mul] at hadd
  exact (not_lt_of_ge hsum) hadd

/-- The constant-zero estimator makes the extended minimax absolute risk finite. Given [the displayed inputs and assumptions](hyp:β,σ,n), [the stated mathematical conclusion holds](goal). -/
lemma risk_value_ne_top (β σ : ℝ) (n : ℕ) :
    Causalean.Stat.minimaxValueENNReal
      (fun (T : Estimator n) (P : {P // Model β σ P}) => absRisk P.val σ n T.val) ≠ ⊤ := by
  let T : Estimator n := ⟨fun _ => 0, measurable_const⟩
  apply ne_top_of_le_ne_top (show (ENNReal.ofReal (1/2 : ℝ)) ≠ ⊤ from ENNReal.ofReal_ne_top)
  apply (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk T).trans
  apply iSup_le
  intro P
  letI := experiment_probability P.val σ n
  change (∫⁻ z, ENNReal.ofReal |0-theta P.val| ∂experiment P.val σ n) ≤ _
  simp only [lintegral_const, measure_univ, mul_one]
  apply ENNReal.ofReal_le_ofReal
  simpa using theta_model_bounds β σ P.val P.property

/-- The full target interval is honest and makes the extended minimax length finite. Given [the displayed inputs and assumptions](hyp:β,σ,n), [the stated mathematical conclusion holds](goal). -/
lemma length_value_ne_top (β σ : ℝ) (n : ℕ) :
    Causalean.Stat.minimaxValueENNReal
      (fun (I : {I // I ∈ honestIntervals β n σ}) (P : {P // Model β σ P}) =>
        expectedLength P.val σ n I.val) ≠ ⊤ := by
  let I : IntervalProc n := ⟨fun _ => -1, fun _ => 1, measurable_const,
    measurable_const, fun _ => by norm_num⟩
  have hI : I ∈ honestIntervals β n σ := by
    intro P hP
    letI := experiment_probability P σ n
    have ht := theta_model_bounds β σ P hP
    have he : Causalean.Stat.coverageEvent I.lo I.hi (theta P) = univ := by
      ext z
      simp only [Causalean.Stat.coverageEvent, mem_setOf_eq, mem_Icc, mem_univ, iff_true]
      change -1 ≤ theta P ∧ theta P ≤ 1
      have h := abs_le.mp ht
      constructor <;> linarith [h.1, h.2]
    rw [he, probReal_univ]
    norm_num
  apply ne_top_of_le_ne_top (show (ENNReal.ofReal (2 : ℝ)) ≠ ⊤ from ENNReal.ofReal_ne_top)
  apply (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk ⟨I, hI⟩).trans
  apply iSup_le
  intro P
  letI := experiment_probability P.val σ n
  change (∫⁻ z, ENNReal.ofReal (Causalean.Stat.intervalLength (-1) 1)
    ∂experiment P.val σ n) ≤ _
  norm_num [Causalean.Stat.intervalLength, lintegral_const]

/-- The two-point converse includes the independent random seed and all measurable decisions. Given [the displayed inputs and assumptions](hyp:β,b,σ,n,m,hβ,hb,hm,hn,hσ,htv), [the stated mathematical conclusion holds](goal). -/
-- @node: lem:two-point-transfer
lemma two_point_transfer (β b σ : ℝ) (n m : ℕ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (htv : tvDist (sampleLaw (altLaw classicalLegendreFacts β b m true hβ hb hm) σ n)
      (sampleLaw (altLaw classicalLegendreFacts β b m false hβ hb hm) σ n) ≤ (1/5 : ℝ)) :
    (4/5 : ℝ) * kappa * (b/(m : ℝ)^2)^β ≤ risk β n σ ∧
    (6/5 : ℝ) * kappa * (b/(m : ℝ)^2)^β ≤ lengthRisk β n σ := by
  let legendre_of_gate : ClassicalLegendreFacts := classicalLegendreFacts
  let P := altLaw legendre_of_gate β b m true hβ hb hm
  let Q := altLaw legendre_of_gate β b m false hβ hb hm
  have hlegal := legal_cancellation β b σ m hβ hb hm
  have hP : Model β σ P := hlegal.2.2.2.2.2.2.2.1 true
  have hQ : Model β σ Q := hlegal.2.2.2.2.2.2.2.1 false
  have hsep : |theta P - theta Q| = 2 * kappa * (b/(m : ℝ)^2)^β :=
    hlegal.2.2.2.2.2.2.2.2
  letI := experiment_probability P σ n
  letI := experiment_probability Q σ n
  have ht : tvDist (experiment P σ n) (experiment Q σ n) ≤ (1/5 : ℝ) :=
    (experiment_tv_le P Q σ n).trans htv
  have hk : 0 ≤ kappa * (b/(m : ℝ)^2)^β := by
    apply mul_nonneg (by norm_num [kappa])
    exact Real.rpow_nonneg (div_nonneg hb.1.le (sq_nonneg _)) _
  constructor
  · apply (ENNReal.ofReal_le_iff_le_toReal (risk_value_ne_top β σ n)).mp
    apply Causalean.Stat.le_minimaxValueENNReal_of_two_point
      (⟨P,hP⟩ : {P // Model β σ P}) (⟨Q,hQ⟩ : {P // Model β σ P})
    intro T
    apply twoPoint_max_of_sum _ _ _ (by nlinarith [hk])
    have hs := twoPoint_absRisk_sum (experiment P σ n) (experiment Q σ n)
      T.val T.property (theta P) (theta Q)
    change ENNReal.ofReal (2 * ((4/5 : ℝ) * kappa * (b/(m : ℝ)^2)^β)) ≤ _
    apply le_trans _ hs
    apply ENNReal.ofReal_le_ofReal
    rw [hsep]
    nlinarith
  · apply (ENNReal.ofReal_le_iff_le_toReal (length_value_ne_top β σ n)).mp
    apply Causalean.Stat.le_minimaxValueENNReal
    intro I
    have hs := twoPoint_interval_lower (experiment P σ n) (experiment Q σ n)
      I.val.lo I.val.hi I.val.lo_meas I.val.hi_meas (theta P) (theta Q)
      (I.property P hP) (I.property Q hQ) ht
    rw [hsep] at hs
    have he : (3/5 : ℝ) * (2 * kappa * (b/(m : ℝ)^2)^β) =
        (6/5 : ℝ) * kappa * (b/(m : ℝ)^2)^β := by ring
    rw [he] at hs
    exact hs.trans (Causalean.Stat.le_worstCaseRiskENNReal (risk := fun (I : {I // I ∈ honestIntervals β n σ}) (L : {L // Model β σ L}) => expectedLength L.val σ n I.val) I ⟨Q,hQ⟩)


end CausalSmith.Stat.RdTruesideNoiseFrontier
