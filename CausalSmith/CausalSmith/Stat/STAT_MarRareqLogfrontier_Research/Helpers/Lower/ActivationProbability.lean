module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationLikelihood
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationTarget

/-! Probability certificates and fixed-sample projection for the activated
experiment used in equation (6) of the connected-interval lower bound. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,x,a,flag,hz), [the stated mathematical conclusion holds](goal). -/
-- @node: augmentedOutcomeWeight_sum
lemma augmentedOutcomeWeight_sum (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (x : Fin d) (a flag : Bool)
    (hz : 1 ≤ z x ∧ z x ≤ lowerEndpoint n q) :
    (∑ arrival : Bool, ∑ one : Bool,
      augmentedOutcomeWeight η n d q z x a flag arrival one) = 1 := by
  have hH : lowerEndpoint n q ≠ 0 := by linarith [hz.1, hz.2]
  simp only [Fintype.sum_bool]
  by_cases hr : x.val < rareCount η n d q
  · cases a <;> cases flag <;>
      simp [augmentedOutcomeWeight, lowerCellZ, hr]
    all_goals field_simp; ring
  · cases a <;> cases flag <;>
      simp [augmentedOutcomeWeight, lowerCellZ, hr, hH]

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hn,hd,hb,hq,hslice,hz), [the stated mathematical conclusion holds](goal). -/
-- @node: augmentedOneRecord_univ
lemma augmentedOneRecord_univ (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q)) :
    augmentedOneRecord η n d q z hz univ = 1 := by
  have hobs : Measurable (obs : FullRecord d → ObsRecord d) := by fun_prop
  have hp := activated_projection η n d q z hn hd hq hslice hz
  have hm := congrArg (fun μ : Measure (ObsRecord d) => μ univ) hp
  simpa only [Measure.map_apply measurable_snd MeasurableSet.univ,
    Measure.map_apply hobs MeasurableSet.univ,
    Set.preimage_univ, activatedLaw_univ η n d q z hd hb hq hslice hz] using hm

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hn,hd,hb,hq,hslice,hz), [the stated mathematical conclusion holds](goal). -/
-- @node: augmentedOneRecord_isProbabilityMeasure
lemma augmentedOneRecord_isProbabilityMeasure (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q)) :
    IsProbabilityMeasure (augmentedOneRecord η n d q z hz) :=
  ⟨augmentedOneRecord_univ η n d q z hn hd hb hq hslice hz⟩

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hn,hd,hb,hq,hslice,hz), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_sample_projection
lemma activated_sample_projection (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q)) :
    (Measure.pi (fun _ : Fin n => augmentedOneRecord η n d q z hz)).map
      (fun s i => (s i).2) =
        sampleLaw n (activatedFullLaw η n d q z hd hb hq hslice hz) := by
  let := augmentedOneRecord_isProbabilityMeasure η n d q z hn hd hb hq hslice hz
  rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
  simp_rw [activated_projection η n d q z hn hd hq hslice hz]
  rfl

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,x,a,flag,hz), [the stated mathematical conclusion holds](goal). -/
-- @node: augmentedOneRecord_marginal_weight
lemma augmentedOneRecord_marginal_weight (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (x : Fin d) (a flag : Bool)
    (hz : 1 ≤ z x ∧ z x ≤ lowerEndpoint n q) :
    (∑ arrival : Bool, ∑ one : Bool,
      ENNReal.ofReal (baselineMass η n d q x / 2 *
        bernWeight (q * lowerEndpoint n q) flag *
        augmentedOutcomeWeight η n d q z x a flag arrival one)) =
      ENNReal.ofReal (baselineMass η n d q x / 2 *
        bernWeight (q * lowerEndpoint n q) flag) := by
  let b := baselineMass η n d q x / 2 * bernWeight (q * lowerEndpoint n q) flag
  change (∑ arrival : Bool, ∑ one : Bool,
    ENNReal.ofReal (b * augmentedOutcomeWeight η n d q z x a flag arrival one)) = _
  simp_rw [ofReal_signed_mul_bool_sum b _ (fun one =>
    augmentedOutcomeWeight_nonneg η n d q z x a flag _ one hz)]
  rw [ofReal_signed_mul_bool_sum b _ (fun arrival =>
    Finset.sum_nonneg (fun one _ =>
      augmentedOutcomeWeight_nonneg η n d q z x a flag arrival one hz))]
  rw [augmentedOutcomeWeight_sum η n d q z x a flag hz, mul_one]

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hz), [the stated mathematical conclusion holds](goal). -/
-- @node: augmentedOneRecord_membership_activation_map
lemma augmentedOneRecord_membership_activation_map (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q)) :
    (augmentedOneRecord η n d q z hz).map
      (fun r => (r.2.X, r.2.A, r.1)) =
    ∑ x : Fin d, ∑ a : Bool, ∑ flag : Bool,
      ENNReal.ofReal (baselineMass η n d q x / 2 *
        bernWeight (q * lowerEndpoint n q) flag) • Measure.dirac (x, a, flag) := by
  classical
  have hf : Measurable (fun r : Bool × ObsRecord d => (r.2.X, r.2.A, r.1)) := by
    fun_prop
  unfold augmentedOneRecord
  simp_rw [Measure.map_finset_sum' hf.aemeasurable, Measure.map_smul,
    Measure.map_dirac]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro flag _
  simp_rw [← Finset.sum_smul]
  rw [augmentedOneRecord_marginal_weight η n d q z x a flag (hz x)]

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hn,hd,hb,hq,hslice,hz), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_sample_membership_activation_map
lemma activated_sample_membership_activation_map (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q)) :
    (Measure.pi (fun _ : Fin n => augmentedOneRecord η n d q z hz)).map
      (fun s i => ((s i).2.X, (s i).2.A, (s i).1)) =
    Measure.pi (fun _ : Fin n =>
      ∑ x : Fin d, ∑ a : Bool, ∑ flag : Bool,
        ENNReal.ofReal (baselineMass η n d q x / 2 *
          bernWeight (q * lowerEndpoint n q) flag) • Measure.dirac (x, a, flag)) := by
  let := augmentedOneRecord_isProbabilityMeasure η n d q z hn hd hb hq hslice hz
  have hf : Measurable (fun r : Bool × ObsRecord d => (r.2.X, r.2.A, r.1)) := by
    fun_prop
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  simp_rw [augmentedOneRecord_membership_activation_map η n d q z hz]

end CausalSmith.Stat.MarRareqLogfrontier
