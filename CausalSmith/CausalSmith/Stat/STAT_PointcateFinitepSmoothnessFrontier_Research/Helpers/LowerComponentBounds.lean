module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerHellinger
public import Mathlib.Probability.Independence.Basic

/-! Reindexing component likelihoods and their Hellinger bounds on record subsets. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
variable (κ : Params) (n : ℕ)

/-- Conditional mixture density restricted to one vertex subset. -/
-- @node: subsetDensity
def subsetDensity (S : Finset (Fin n)) (x : Fin n → unitInterval) (s t : ℝ)
    (z : Fin n → Bool × ℝ) : ℝ :=
  (Fintype.card (Signs κ n) : ℝ)⁻¹ * ∑ v : Signs κ n,
    ∏ i ∈ S, lowerDensity κ n s t v (x i) (z i)

/-- The reference treatment score is Borel on its finite domain. -/
-- @node: measurable_markU
@[fun_prop] lemma measurable_markU : Measurable markU := by
  exact measurable_of_finite _

/-- A conditional likelihood is Borel in the original mark. -/
-- @node: measurable_lowerDensity_mark
@[fun_prop] lemma measurable_lowerDensity_mark (s t : ℝ) (v : Signs κ n)
    (x : unitInterval) : Measurable (lowerDensity κ n s t v x) := by
  unfold lowerDensity markV
  fun_prop

/-- Averaging the finite sign prior preserves mark measurability. -/
-- @node: measurable_componentDensity_marks
@[fun_prop] lemma measurable_componentDensity_marks (m : ℕ) (x : Fin m → unitInterval)
    (s t : ℝ) : Measurable (componentDensity κ n m x s t) := by
  unfold componentDensity
  fun_prop

/-- Enumerating a record subset turns its likelihood into the already bounded component density. -/
-- @node: subset_density_reindex
lemma subset_density_reindex (S : Finset (Fin n)) (x : Fin n → unitInterval)
    (s t : ℝ) (z : Fin n → Bool × ℝ) :
    subsetDensity κ n S x s t z = componentDensity κ n S.card
      (fun i => x (S.equivFin.symm i)) s t (fun i => z (S.equivFin.symm i)) := by
  unfold subsetDensity componentDensity
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [← S.prod_coe_sort]
  exact (Equiv.prod_comp S.equivFin.symm
    (fun i : S => lowerDensity κ n s t v (x i) (z i))).symm

/-- The mark law on distinct selected records is the corresponding finite product reference law. -/
-- @node: subset_marks_map
lemma subset_marks_map (hκ : κ.Valid) (hn : 2 ≤ n) (S : Finset (Fin n)) :
    (Measure.pi (fun _ : Fin n => referenceMarks κ n)).map
      (fun (z : Fin n → Bool × ℝ) (i : Fin S.card) => z (S.equivFin.symm i)) =
        Measure.pi (fun _ : Fin S.card => referenceMarks κ n) := by
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  have hi := (iIndepFun_pi (μ := fun _ : Fin n => referenceMarks κ n)
    (X := fun _ => id) (fun _ => aemeasurable_id)).precomp
      (show Function.Injective (fun i : Fin S.card => (S.equivFin.symm i : Fin n)) from
        Subtype.val_injective.comp S.equivFin.symm.injective)
  have hm := hi.map_fun_eq_pi_map (fun i => (measurable_pi_apply _).aemeasurable)
  simpa only [(measurePreserving_eval (fun _ : Fin n => referenceMarks κ n) _).map_eq] using hm

/-- Subset Hellinger loss is unchanged by discarding the unused independent mark coordinates. -/
-- @node: subset_hellinger_reindex
lemma subset_hellinger_reindex (hκ : κ.Valid) (hn : 2 ≤ n)
    (S : Finset (Fin n)) (x : Fin n → unitInterval) (s t u : ℝ) :
    Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => referenceMarks κ n))
      (subsetDensity κ n S x s t) (subsetDensity κ n S x s u) =
    Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin S.card => referenceMarks κ n))
      (componentDensity κ n S.card (fun i => x (S.equivFin.symm i)) s t)
      (componentDensity κ n S.card (fun i => x (S.equivFin.symm i)) s u) := by
  unfold Causalean.Stat.hellingerSqDensity
  simp_rw [subset_density_reindex]
  rw [← subset_marks_map κ n hκ hn S]
  apply (integral_map
    (φ := fun (z : Fin n → Bool × ℝ) (i : Fin S.card) => z (S.equivFin.symm i))
    (f := fun z => (Real.sqrt (componentDensity κ n S.card
      (fun i => x (S.equivFin.symm i)) s t z) - Real.sqrt (componentDensity κ n S.card
      (fun i => x (S.equivFin.symm i)) s u z))^2) ((by fun_prop : Measurable _).aemeasurable) ?_).symm
  apply Measurable.aestronglyMeasurable
  fun_prop

/-- The all-size component estimate applies to a subset inside the full conditional mark space. -/
-- @node: subset_hellinger_bound
lemma subset_hellinger_bound (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (S : Finset (Fin n)) (hS : 2 ≤ S.card) (x : Fin n → unitInterval) :
    Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => referenceMarks κ n))
      (subsetDensity κ n S x (lowerA κ n) (lowerB κ n))
      (subsetDensity κ n S x (lowerA κ n) (-lowerB κ n)) ≤
    144*lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2)*
      (S.card : ℝ)^4*(9/2 : ℝ)^S.card := by
  rw [subset_hellinger_reindex κ n hκ hn]
  exact component_hellinger_bound κ n hκ hb hn S.card hS _

/-- Every singleton record has the common reference density after averaging the latent signs. -/
-- @node: subset_density_singleton
lemma subset_density_singleton (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (i : Fin n) (x : Fin n → unitInterval) (s t : ℝ)
    (hs : |s| ≤ lowerA κ n) (ht : |t| ≤ lowerB κ n) (z : Fin n → Bool × ℝ) :
    subsetDensity κ n {i} x s t z = 1 := by
  simpa only [subsetDensity, Finset.prod_singleton] using
    singleton_cancellation κ n hκ hb hn s t hs ht (x i) (z i)

/-- An empty record subset has the constant likelihood one. -/
-- @node: subset_density_empty
lemma subset_density_empty (x : Fin n → unitInterval) (s t : ℝ)
    (z : Fin n → Bool × ℝ) : subsetDensity κ n ∅ x s t z = 1 := by
  have hc : (Fintype.card (Signs κ n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [subsetDensity, hc]

/-- Exact singleton cancellation removes the singleton Hellinger defect. -/
-- @node: subset_hellinger_singleton
lemma subset_hellinger_singleton (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (i : Fin n) (x : Fin n → unitInterval) :
    Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => referenceMarks κ n))
      (subsetDensity κ n {i} x (lowerA κ n) (lowerB κ n))
      (subsetDensity κ n {i} x (lowerA κ n) (-lowerB κ n)) = 0 := by
  have ha := (lower_scale_small κ n hκ hn).2.1.1.le
  have hb0 := (lower_scale_small κ n hκ hn).2.2.1.le
  unfold Causalean.Stat.hellingerSqDensity
  simp_rw [subset_density_singleton κ n hκ hb hn i x (lowerA κ n) (lowerB κ n)
    (by simp [abs_of_nonneg ha]) (by simp [abs_of_nonneg hb0]),
    subset_density_singleton κ n hκ hb hn i x (lowerA κ n) (-lowerB κ n)
    (by simp [abs_of_nonneg ha]) (by simp [abs_of_nonneg hb0])]
  simp

/-- A record outside the macro window has its unperturbed reference mark density. -/
-- @node: lower_density_outside_window
lemma lower_density_outside_window (hn : 0 < n) (x : unitInterval)
    (hx : lowerH κ n ≤ |(x : ℝ)-1/2|) (s t : ℝ) (v : Signs κ n) (z : Bool × ℝ) :
    lowerDensity κ n s t v x z = 1 := by
  have hh : 0 < lowerH κ n := Real.rpow_pos_of_pos (lowerEll_pos κ n hn) _
  have hk : lowerCutoff κ n x = 0 := by
    unfold lowerCutoff
    rw [max_eq_left]
    have hd : 1 ≤ |(x : ℝ)-1/2|/lowerH κ n :=
      (le_div_iff₀ hh).mpr (by simpa using hx)
    linarith
  simp [lowerDensity, lowerField, lowerSquare, hk]

/-- A subset entirely outside the macro window contributes no conditional Hellinger defect. -/
-- @node: subset_density_outside_window
lemma subset_density_outside_window (hn : 0 < n) (S : Finset (Fin n))
    (x : Fin n → unitInterval) (hx : ∀ i ∈ S, lowerH κ n ≤ |(x i : ℝ)-1/2|)
    (s t : ℝ) (z : Fin n → Bool × ℝ) : subsetDensity κ n S x s t z = 1 := by
  have hp (v : Signs κ n) : ∏ i ∈ S, lowerDensity κ n s t v (x i) (z i) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    exact lower_density_outside_window κ n hn (x i) (hx i hi) s t v (z i)
  have hc : (Fintype.card (Signs κ n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [subsetDensity, hp, hc]

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
