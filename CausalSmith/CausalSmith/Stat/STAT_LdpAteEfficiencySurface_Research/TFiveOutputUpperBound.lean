module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SparseSaddle

/-! # Five-output upper bound

An optimal finite staircase design has at most five positive pattern weights,
and therefore at most five active released symbols. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory

open Classical in
/-- the staircase support is the mathematical object specified below. [The staircase Support](goal) is determined by [the displayed parameters](hyp:α). -/
def staircaseSupport (α : StaircaseWeight) : Finset (Fin 14) :=
  Finset.univ.filter (fun s => α s ≠ 0)

-- @node: staircase_output_zero_of_weight_zero
/-- Under [the supplied quantities and conditions](hyp:p), [the staircase output zero of weight zero assertion](goal) holds. For [the displayed quantities and conditions](hyp:s,hs), these specify the stated inputs. -/
lemma staircase_output_zero_of_weight_zero (θ : TrialParameter) (p ε : ℝ)
    (α : StaircaseWeight) (s : Fin 14) (hs : α s = 0) :
    outputLaw θ p (staircaseChannel ε α) {s} = 0 := by
  simp only [outputLaw]
  simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_eq_zero_iff, Finset.mem_univ,
    mul_eq_zero, ENNReal.ofReal_eq_zero, forall_const]
  intro j
  have hrow : (staircaseChannel ε α) j {s} = 0 := by
    change (Measure.count.withDensity (fun u : Fin 14 =>
      ENNReal.ofReal (α u * patternRay ε u j))) {s} = 0
    simp [withDensity_apply _ (measurableSet_singleton s), hs]
  exact Or.inr hrow

-- @node: outputCardinality_staircase_le_support_card
/-- [the output cardinality staircase le support card assertion](goal) holds. For [the displayed quantities and conditions](hyp:p), these specify the stated inputs. -/
lemma outputCardinality_staircase_le_support_card (θ : TrialParameter)
    (p ε : ℝ) (α : StaircaseWeight) :
    outputCardinality θ p (staircaseChannel ε α) ≤
      (staircaseSupport α).card := by
  let A : Set (Fin 14) :=
    {s | outputLaw θ p (staircaseChannel ε α) {s} ≠ 0}
  have hsubset : A ⊆ (staircaseSupport α : Set (Fin 14)) := by
    intro s hs
    simp only [staircaseSupport, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_contra hz
    exact hs (staircase_output_zero_of_weight_zero θ p ε α s hz)
  have hbound := Set.encard_le_encard hsubset
  simp only [Set.encard_coe_eq_coe_finsetCard] at hbound
  change A.encard ≤ _ at hbound
  simpa only [outputCardinality, dif_pos (inferInstance : Finite (Fin 14))] using hbound

-- @node: staircase_output_pos_of_weight_pos
/-- Under the supplied quantities and conditions, the staircase output pos of weight pos assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hs), [the staircase output pos of weight pos](goal).

Under the stated assumptions, the staircase output pos of weight pos. -/
lemma staircase_output_pos_of_weight_pos (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (α : StaircaseWeight) (s : Fin 14) (hs : 0 < α s) :
    outputLaw θ p (staircaseChannel ε α) {s} ≠ 0 := by
  have hπ : 0 < piTheta θ p 0 := by
    rcases hp with ⟨hp0, hp1⟩
    rcases hθ with ⟨h0, h0', h1, h1'⟩
    simp only [piTheta, controlProb]
    exact mul_pos (by linarith) (by linarith)
  have hr : 0 < patternRay ε s 0 := by
    unfold patternRay privacyIncrement privacyRatio
    split_ifs <;> simp_all <;> positivity
  have hrow : (staircaseChannel ε α) 0 {s} ≠ 0 := by
    change (Measure.count.withDensity (fun u : Fin 14 =>
      ENNReal.ofReal (α u * patternRay ε u 0))) {s} ≠ 0
    simp [withDensity_apply _ (measurableSet_singleton s)]
    exact mul_pos hs hr
  have hterm : ENNReal.ofReal (piTheta θ p 0) •
      (staircaseChannel ε α) 0 {s} ≠ 0 := by
    simp [hrow]
    exact hπ
  intro hz
  have hle : ENNReal.ofReal (piTheta θ p 0) •
      (staircaseChannel ε α) 0 {s} ≤
      outputLaw θ p (staircaseChannel ε α) {s} := by
    simp only [outputLaw, Measure.coe_finsetSum, Finset.sum_apply]
    exact Finset.single_le_sum
      (f := fun j : Fin 4 =>
        (ENNReal.ofReal (piTheta θ p j) • (staircaseChannel ε α) j) {s})
      (s := Finset.univ) (a := (0 : Fin 4))
      (fun j hj => zero_le) (Finset.mem_univ _)
  exact hterm (le_antisymm (hz ▸ hle) zero_le)

-- @node: outputCardinality_staircase_eq_support_card
/-- the output cardinality staircase eq support card assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hα), [the output Cardinality staircase eq support card](goal).

Under the stated assumptions, the output Cardinality staircase eq support card. -/
lemma outputCardinality_staircase_eq_support_card (θ : TrialParameter)
    (p ε : ℝ) (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (α : StaircaseWeight) (hα : ∀ s, 0 ≤ α s) :
    outputCardinality θ p (staircaseChannel ε α) =
      (staircaseSupport α).card := by
  let A : Set (Fin 14) :=
    {s | outputLaw θ p (staircaseChannel ε α) {s} ≠ 0}
  have hsets : A = (staircaseSupport α : Set (Fin 14)) := by
    ext s
    constructor
    · intro hs
      simp only [staircaseSupport, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and]
      by_contra hz
      exact hs (staircase_output_zero_of_weight_zero θ p ε α s hz)
    · intro hs
      have hne : α s ≠ 0 := by simpa [staircaseSupport] using hs
      exact staircase_output_pos_of_weight_pos θ p ε hp hθ α s
        (lt_of_le_of_ne (hα s) (Ne.symm hne))
  simp only [outputCardinality, dif_pos (inferInstance : Finite (Fin 14))]
  change A.encard = ↑(staircaseSupport α).card
  rw [hsets]
  exact Set.encard_coe_eq_coe_finsetCard _

-- @node: thm:five-output-upper-bound
/-- Under the supplied quantities and conditions, the five output upper bound assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the five output upper bound](goal).

Under the stated assumptions, the five output upper bound. -/
theorem five_output_upper_bound (θ : TrialParameter) (p ε : ℝ)
    (hp : 0 < p ∧ p < 1)
    (hθ : 0 < θ 0 ∧ θ 0 < 1 ∧ 0 < θ 1 ∧ θ 1 < 1)
    (hε : 0 < ε) :
    ∃ α : StaircaseWeight,
      staircaseFeasible ε α ∧
      Jstar θ p ε =
        sInf {u : ℝ | ∃ t : ℝ, u = informationObjective θ p ε α t} ∧
      (staircaseSupport α).card ≤ 5 ∧
      outputCardinality θ p (staircaseChannel ε α) ≤ 5 := by
  obtain ⟨α, hfeasible, hoptimal, hsupport'⟩ :=
    exists_sparse_staircase_saddle θ p ε hp hθ hε
  have hsupport : (staircaseSupport α).card ≤ 5 := by
    simpa [staircaseSupport,
      Causalean.Mathlib.Optimization.weightSupport] using hsupport'
  exact ⟨α, hfeasible, hoptimal, hsupport,
    (outputCardinality_staircase_le_support_card θ p ε α).trans
      (by exact_mod_cast hsupport)⟩

end CausalSmith.Stat.LdpAteEfficiencySurface
