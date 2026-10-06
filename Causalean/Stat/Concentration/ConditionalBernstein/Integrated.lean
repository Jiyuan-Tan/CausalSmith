module
public import Causalean.Stat.Concentration.ConditionalBernstein.Disintegration
public import Causalean.Stat.Concentration.ConditionalBernstein.Simultaneous

/-!
# IID joint-law finite-partition conditional Bernstein histogram tails

The headline theorem bounds simultaneous cell/bin count deviations under the IID
product of a design marginal attached to a measurable conditional outcome kernel.
It first proves the conditional bound given the entire design vector, integrates that
bound, and transports back to the IID law. The probability envelope need only hold
almost everywhere under the design marginal. There is no lower-count hypothesis.

For all pairs, the radius is `sqrt (2 * pMax * N_c * u) + u`, and the total failure
probability is at most `2 * card C * card B * exp (-u)`. A deterministic adapter permits
division by the cell count only when a separate positive-count hypothesis is available.
-/

public section

namespace Causalean.Stat.Concentration.ConditionalBernstein
open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

variable {D Y C B : Type*} [MeasurableSpace D] [MeasurableSpace Y] {n : ℕ}

/-- An [almost-everywhere conditional bin envelope under a design marginal](hyp:henvelope)
also holds [simultaneously at every coordinate of almost every IID design vector](goal).
-/
theorem ae_design_vector_envelope (Q : Measure D) [IsProbabilityMeasure Q]
    (K : Kernel D Y) (key : D → C) (bins : B → Set Y) (pMax : ℝ)
    (henvelope : ∀ᵐ d ∂Q, ∀ c b, key d = c → binProbability K (bins b) d ≤ pMax) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => Q),
      ∀ c b i, key (x i) = c → binProbability K (bins b) (x i) ≤ pMax := by
  have hcoord (i : Fin n) : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => Q),
      ∀ c b, key (x i) = c → binProbability K (bins b) (x i) ≤ pMax :=
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => Q) (i := i)).eventually henvelope
  filter_upwards [(ae_all_iff).mpr hcoord] with x hx
  exact fun c b i => hx i c b

/-- Under a [probability design marginal and Markov outcome kernel](hyp:Q,K),
[finite measurable cells and bins](hyp:key,bins,hcell,hbins) with an [almost-everywhere
nonnegative conditional bin envelope](hyp:henvelope,hpMax) satisfy [the simultaneous
two-sided count bound under the retained-design law](goal) at [nonnegative tail parameter](hyp:hu).

Use `ae_design_vector_envelope` and `fibre_simultaneous_tail_le`, then integrate with
`compProd_real_le_of_fibre_real_le` and `measurableSet_histogramBadEvent`.
Instantiate the base measure as `Measure.pi (fun _ : Fin n => Q)` and the
kernel as `Causalean.Stat.finProductKernel n K`; their probability/Markov instances
are already available. The union-bound constant is nonnegative by `positivity`,
including when either family is empty. A single `filter_upwards` over the
design-vector envelope supplies the pointwise hypothesis of the fibre theorem.
-/
theorem attached_simultaneous_tail_le [Fintype C] [Fintype B]
    (Q : Measure D) [IsProbabilityMeasure Q]
    (K : Kernel D Y) [IsMarkovKernel K] (key : D → C) (bins : B → Set Y)
    (hcell : ∀ c, MeasurableSet {d | key d = c})
    (hbins : ∀ b, MeasurableSet (bins b))
    {pMax u : ℝ} (hpMax : 0 ≤ pMax) (hu : 0 ≤ u)
    (henvelope : ∀ᵐ d ∂Q, ∀ c b, key d = c → binProbability K (bins b) d ≤ pMax) :
    (Measure.pi (fun _ : Fin n => Q) ⊗ₘ Causalean.Stat.finProductKernel n K).real
      (histogramBadEvent key K bins pMax u) ≤
      2 * (Fintype.card C : ℝ) * (Fintype.card B : ℝ) * Real.exp (-u) := by
  refine compProd_real_le_of_fibre_real_le
    (Measure.pi (fun _ : Fin n => Q)) (Causalean.Stat.finProductKernel n K)
    (measurableSet_histogramBadEvent key K bins hcell hbins pMax u)
    (by positivity) ?_
  filter_upwards [ae_design_vector_envelope Q K key bins pMax henvelope] with x hx
  exact fibre_simultaneous_tail_le key K bins hbins x hpMax hu hx

/-- An [IID sample from a joint design/outcome law represented by a probability design
marginal and Markov outcome kernel](hyp:Q,K), with
[finite measurable cells and bins](hyp:key,bins,hcell,hbins)
and an [almost-everywhere nonnegative bin-probability envelope](hyp:henvelope,hpMax), has
[simultaneous count deviations at most the cell-dependent Bernstein radius outside
an event of probability at most twice the number of cell/bin pairs times the
exponential tail](goal), for [nonnegative tail parameter](hyp:hu).

Transport `attached_simultaneous_tail_le` along `iid_joint_map_split`. The event is
strict failure of the non-strict count bound, so it includes zero-count cells correctly.
The empirical counts and conditional means are exactly the definitions in `Basic`.
The splitting map is measurable by `Measurable.prodMk` and `measurable_pi_lambda`,
using the first/second projection of each coordinate evaluation. Apply
`Measure.map_apply` to `measurableSet_histogramBadEvent`, rewrite the mapped
measure with `iid_joint_map_split`, and apply `congrArg ENNReal.toReal` to
transport its real-valued event measure. The displayed IID event is definitionally
the preimage of `histogramBadEvent` under this map.
-/
theorem iid_joint_simultaneous_tail_le [Fintype C] [Fintype B]
    (Q : Measure D) [IsProbabilityMeasure Q]
    (K : Kernel D Y) [IsMarkovKernel K] (key : D → C) (bins : B → Set Y)
    (hcell : ∀ c, MeasurableSet {d | key d = c})
    (hbins : ∀ b, MeasurableSet (bins b))
    {pMax u : ℝ} (hpMax : 0 ≤ pMax) (hu : 0 ≤ u)
    (henvelope : ∀ᵐ d ∂Q, ∀ c b, key d = c → binProbability K (bins b) d ≤ pMax) :
    (Measure.pi (fun _ : Fin n => Q ⊗ₘ K)).real
      {z | ∃ c b,
        bernsteinRadius (pMax * (cellCount key c (fun i => (z i).1) : ℝ)) u <
          |(jointCount key (bins b) c (fun i => (z i).1) (fun i => (z i).2) : ℝ) -
            conditionalMean key K (bins b) c (fun i => (z i).1)|} ≤
      2 * (Fintype.card C : ℝ) * (Fintype.card B : ℝ) * Real.exp (-u) := by
  have hsplit : Measurable (fun z : Fin n → D × Y =>
      (fun i => (z i).1, fun i => (z i).2)) :=
    (measurable_pi_lambda _ (fun i => (measurable_pi_apply i).fst)).prodMk
      (measurable_pi_lambda _ (fun i => (measurable_pi_apply i).snd))
  have hmap := Measure.map_apply hsplit
    (measurableSet_histogramBadEvent (n := n) key K bins hcell hbins pMax u)
    (μ := Measure.pi (fun _ : Fin n => Q ⊗ₘ K))
  rw [iid_joint_map_split n Q K] at hmap
  have hreal := congrArg ENNReal.toReal hmap
  change (Measure.pi (fun _ : Fin n => Q) ⊗ₘ Causalean.Stat.finProductKernel n K).real
      (histogramBadEvent key K bins pMax u) =
    (Measure.pi (fun _ : Fin n => Q ⊗ₘ K)).real
      {z | ∃ c b,
        bernsteinRadius (pMax * (cellCount key c (fun i => (z i).1) : ℝ)) u <
          |(jointCount key (bins b) c (fun i => (z i).1) (fun i => (z i).2) : ℝ) -
            conditionalMean key K (bins b) c (fun i => (z i).1)|} at hreal
  rw [← hreal]
  exact attached_simultaneous_tail_le Q K key bins hcell hbins hpMax hu henvelope

/-- A [count deviation bounded by its Bernstein radius](hyp:hdev) in a
[cell of positive count](hyp:hcount) gives [the corresponding bound for the
empirical bin proportion minus the conditional mean divided by that count](goal).
-/
theorem normalized_deviation_le
    (key : D → C) (K : Kernel D Y) (bin : Set Y) (c : C)
    (x : Fin n → D) (y : Fin n → Y) (pMax u : ℝ)
    (hcount : 0 < cellCount key c x)
    (hdev : |(jointCount key bin c x y : ℝ) - conditionalMean key K bin c x| ≤
      bernsteinRadius (pMax * (cellCount key c x : ℝ)) u) :
    |(jointCount key bin c x y : ℝ) / (cellCount key c x : ℝ) -
      conditionalMean key K bin c x / (cellCount key c x : ℝ)| ≤
        bernsteinRadius (pMax * (cellCount key c x : ℝ)) u / (cellCount key c x : ℝ) := by
  have hpos : (0 : ℝ) < cellCount key c x := by exact_mod_cast hcount
  rw [← sub_div, abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_right hdev hpos.le

end Causalean.Stat.Concentration.ConditionalBernstein
