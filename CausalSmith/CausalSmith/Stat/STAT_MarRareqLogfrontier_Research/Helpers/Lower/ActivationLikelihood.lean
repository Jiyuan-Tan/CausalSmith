module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Activation

/-! Projection from the activated experiment to every observed record. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: activation_atom_weight
/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,x,a,arrival,one,hz), [the stated mathematical conclusion holds](goal). -/
lemma activation_atom_weight (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (x : Fin d) (a arrival one : Bool)
    (hz : 1 ≤ z x ∧ z x ≤ lowerEndpoint n q) :
    (∑ flag : Bool, bernWeight (q * lowerEndpoint n q) flag *
      augmentedOutcomeWeight η n d q z x a flag arrival one) =
    ∑ y₁ : Bool,
      bernWeight (if x.val < rareCount η n d q then (z x)⁻¹ else 0) y₁ *
        bernWeight (q * lowerCellZ η n d q z x) arrival *
        (if (arrival && (a && y₁)) = one then (1 : ℝ) else 0) := by
  have hH : lowerEndpoint n q ≠ 0 := by linarith
  have hz0 : z x ≠ 0 := by linarith
  by_cases hr : x.val < rareCount η n d q
  · cases a <;> cases arrival <;> cases one <;>
      simp [bernWeight, augmentedOutcomeWeight, lowerCellZ, hr] <;>
      field_simp <;> ring
  · cases a <;> cases arrival <;> cases one <;>
      simp [bernWeight, augmentedOutcomeWeight, lowerCellZ, hr] <;>
      field_simp <;> simp

-- @node: augmentedOutcomeWeight_nonneg
/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,x,a,flag,arrival,one,hz), [the stated mathematical conclusion holds](goal). -/
lemma augmentedOutcomeWeight_nonneg (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (x : Fin d) (a flag arrival one : Bool)
    (hz : 1 ≤ z x ∧ z x ≤ lowerEndpoint n q) :
    0 ≤ augmentedOutcomeWeight η n d q z x a flag arrival one := by
  have hH : 0 < lowerEndpoint n q := by linarith [hz.1, hz.2]
  have hcell : 0 ≤ lowerCellZ η n d q z x ∧
      lowerCellZ η n d q z x ≤ lowerEndpoint n q := by
    unfold lowerCellZ
    split_ifs <;> constructor <;> linarith [hz.1, hz.2]
  unfold augmentedOutcomeWeight
  split_ifs <;> try positivity
  all_goals try exact div_nonneg (by linarith [hz.1]) (le_of_lt hH)
  all_goals apply sub_nonneg.mpr
  all_goals exact (div_le_one hH).2 hcell.2

-- @node: ofReal_signed_mul_bool_sum
/-- Given [the specified inputs and assumptions](hyp:b,w,hw), [the stated mathematical conclusion holds](goal). -/
lemma ofReal_signed_mul_bool_sum (b : ℝ) (w : Bool → ℝ)
    (hw : ∀ flag, 0 ≤ w flag) :
    (∑ flag : Bool, ENNReal.ofReal (b * w flag)) =
      ENNReal.ofReal (b * ∑ flag : Bool, w flag) := by
  simp_rw [ENNReal.ofReal_mul' (hw _)]
  rw [← Finset.mul_sum]
  rw [ENNReal.ofReal_mul' (Finset.sum_nonneg (fun flag _ => hw flag))]
  rw [ENNReal.ofReal_sum_of_nonneg (fun flag _ => hw flag)]

-- @node: activated_projection
/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,_hn,_hd,hq,hslice,hz), [the stated mathematical conclusion holds](goal). -/
lemma activated_projection (η : ℝ) (n d : ℕ) (q : ℝ) (z : Fin d → ℝ)
    (_hn : 1 ≤ n) (_hd : 1 ≤ d) (hq : 0 < q)
    (hslice : RareArrivalSlice n q)
    (hz : ∀ x, 1 ≤ z x ∧ z x ≤ lowerEndpoint n q)
      -- @realizes \(Z\)(latent reciprocal variable in [1,H])
    :
    (augmentedOneRecord η n d q z (by simpa [Set.mem_Icc] using hz)).map Prod.snd =
      (activatedLaw η n d q z (by simpa [Set.mem_Icc] using hz)).map obs := by
  classical
  have hH : q * lowerEndpoint n q ≤ 1 :=
    lower_activation_probability_le_one n q (le_of_lt hq) hslice
  have hHpos : 0 ≤ lowerEndpoint n q := by
    unfold lowerEndpoint
    positivity
  have hcell (x : Fin d) : 0 ≤ lowerCellZ η n d q z x ∧
      lowerCellZ η n d q z x ≤ lowerEndpoint n q := by
    unfold lowerCellZ
    split_ifs <;> constructor <;> linarith [(hz x).1, (hz x).2]
  have hprob (x : Fin d) : 0 ≤ q * lowerCellZ η n d q z x ∧
      q * lowerCellZ η n d q z x ≤ 1 := by
    constructor
    · exact mul_nonneg (le_of_lt hq) (hcell x).1
    · exact (mul_le_mul_of_nonneg_left (hcell x).2 (le_of_lt hq)).trans hH
  have hbw (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (v : Bool) : 0 ≤ bernWeight p v := by
    cases v <;> simp [bernWeight] <;> linarith [hp.1, hp.2]
  have hyprob (x : Fin d) :
      0 ≤ (if x.val < rareCount η n d q then (z x)⁻¹ else 0) ∧
      (if x.val < rareCount η n d q then (z x)⁻¹ else 0) ≤ 1 := by
    split_ifs
    · constructor
      · exact inv_nonneg.mpr (le_trans (by norm_num) (hz x).1)
      · exact inv_le_one₀ (by linarith [(hz x).1]) |>.mpr (hz x).1
    · constructor <;> norm_num
  have hcoeff (x : Fin d) (a arrival one : Bool) :
      (∑ flag : Bool, ENNReal.ofReal
        (baselineMass η n d q x / 2 * bernWeight (q * lowerEndpoint n q) flag *
          augmentedOutcomeWeight η n d q z x a flag arrival one)) =
      ∑ y₁ : Bool, ENNReal.ofReal
        (baselineMass η n d q x / 2 *
          (bernWeight (if x.val < rareCount η n d q then (z x)⁻¹ else 0) y₁ *
            bernWeight (q * lowerCellZ η n d q z x) arrival *
            (if (arrival && (a && y₁)) = one then (1 : ℝ) else 0))) := by
    let b := baselineMass η n d q x / 2
    have hleft (flag : Bool) :
        0 ≤ bernWeight (q * lowerEndpoint n q) flag *
          augmentedOutcomeWeight η n d q z x a flag arrival one :=
      mul_nonneg (hbw _ ⟨mul_nonneg (le_of_lt hq) hHpos, hH⟩ flag)
        (augmentedOutcomeWeight_nonneg η n d q z x a flag arrival one (hz x))
    have hright (y₁ : Bool) :
        0 ≤ bernWeight (if x.val < rareCount η n d q then (z x)⁻¹ else 0) y₁ *
          bernWeight (q * lowerCellZ η n d q z x) arrival *
          (if (arrival && (a && y₁)) = one then (1 : ℝ) else 0) := by
      apply mul_nonneg
      · exact mul_nonneg (hbw _ (hyprob x) y₁) (hbw _ (hprob x) arrival)
      · split_ifs <;> norm_num
    simp_rw [show ∀ flag : Bool,
      baselineMass η n d q x / 2 * bernWeight (q * lowerEndpoint n q) flag *
        augmentedOutcomeWeight η n d q z x a flag arrival one =
      b * (bernWeight (q * lowerEndpoint n q) flag *
        augmentedOutcomeWeight η n d q z x a flag arrival one) from
      fun _ => by simp [b, mul_assoc]]
    rw [ofReal_signed_mul_bool_sum b _ hleft]
    rw [activation_atom_weight η n d q z x a arrival one (hz x)]
    rw [← ofReal_signed_mul_bool_sum b _ hright]
  have hsnd : Measurable (Prod.snd : Bool × ObsRecord d → ObsRecord d) := measurable_snd
  have hobs : Measurable (obs : FullRecord d → ObsRecord d) := by fun_prop
  simp only [augmentedOneRecord, activatedLaw]
  rw [Measure.map_finset_sum' hsnd.aemeasurable]
  rw [Measure.map_finset_sum' hobs.aemeasurable]
  simp_rw [Measure.map_finset_sum' hsnd.aemeasurable]
  simp_rw [Measure.map_finset_sum' hobs.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac, obs, lowerFullRecord,
    FullRecord.S, FullRecord.Y]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro arrival _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  simp_rw [hcoeff x a arrival]
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y₁ _
  cases a <;> cases arrival <;> cases y₁ <;>
    simp [mul_assoc]

end CausalSmith.Stat.MarRareqLogfrontier
