module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationRoles
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RectangularKernelEnergy

/-! # Transport of rectangular kernels to original records
The treatment and outcome records in a rectangular pair have the product of
their respective marginal laws, including pairs using auxiliary records.
Consequently their kernel energies are those calculated under the product law.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Distinct labeled records have their full observation product law.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the specified input i](hyp:i), [the specified input j](hyp:j), [the specified input hij](hyp:hij), [the rectangular distinct labeled pair integral conclusion](goal) holds. -/
lemma rectangular_distinct_labeled_pair_integral {d n m : ℕ} (P : PrimitiveLaw d)
    (H : (Cov d × Bool × Bool) × (Cov d × Bool × Bool) → ℝ)
    (hH : Measurable H) (i j : Fin n) (hij : i ≠ j) :
    (∫ w : Sample d n m, H (w.1.1 i, w.1.1 j) ∂experiment P n m) =
      ∫ p, H p ∂(obsLaw P).prod (obsLaw P) := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  letI := population_randomizer_probability
  rw [experiment_integral_dataset P (fun D : Dataset d n m => H (D.1 i, D.1 j))]
  rw [integral_fun_fst (fun D : Fin n → Cov d × Bool × Bool => H (D i, D j))]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  have hind := (iIndepFun_pi (μ := fun _ : Fin n => obsLaw P)
    (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
  have hmap := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin n => obsLaw P) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => obsLaw P) j).map_eq] at hmap
  rw [← hmap, integral_map (by fun_prop) hH.aestronglyMeasurable]

/-- Any Borel rectangular kernel has the product-law expectation on a pair of disjoint roles.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the specified input i](hyp:i), [the specified input j](hyp:j), [the specified input hi](hyp:hi), [the specified input hj](hyp:hj), [the rectangular role pair integral conclusion](goal) holds. -/
lemma rectangular_role_pair_integral {d n m : ℕ} (P : PrimitiveLaw d)
    (H : (Cov d × Bool) × (Cov d × Bool × Bool) → ℝ) (hH : Measurable H)
    (i : Fin (n+m)) (j : Fin n)
    (hi : i ∈ (roleSplit n m).2) (hj : j ∈ (roleSplit n m).1) :
    (∫ w : Sample d n m, H (treatmentRecords w.1 i, w.1.1 j) ∂experiment P n m) =
      ∫ p, H p ∂(xaLaw P).prod (obsLaw P) := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  letI := population_randomizer_probability
  revert hi
  refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) i
  · simp only [treatmentRecords, Fin.addCases_left]
    have hij : i ≠ j := by
      have hit : n/2 ≤ i.val := (Finset.mem_filter.mp hi).2
      have hjt : j.val < n/2 := (Finset.mem_filter.mp hj).2
      intro heq
      have := congrArg Fin.val heq
      omega
    rw [rectangular_distinct_labeled_pair_integral P
      (fun p => H ((p.1.1,p.1.2.1),p.2)) (by fun_prop) i j hij]
    have he := Measure.map_prod_map (obsLaw P) (obsLaw P)
      (f := fun z : Cov d × Bool × Bool => (z.1,z.2.1)) (g := id)
      (by fun_prop) measurable_id
    rw [obsLaw_map_treatment P, Measure.map_id] at he
    rw [he, integral_map (by fun_prop) hH.aestronglyMeasurable]
    rfl
  · simp only [treatmentRecords, Fin.addCases_right]
    rw [experiment_integral_dataset P (fun D : Dataset d n m => H (D.2 i, D.1 j))]
    have hmap :
        ((Measure.pi (fun _ : Fin n => obsLaw P)).prod
          (Measure.pi (fun _ : Fin m => xaLaw P))).map
            (fun D => (D.2 i, D.1 j)) = (xaLaw P).prod (obsLaw P) := by
      have he := Measure.map_prod_map
        (Measure.pi (fun _ : Fin n => obsLaw P))
        (Measure.pi (fun _ : Fin m => xaLaw P))
        (measurable_pi_apply j) (measurable_pi_apply i)
      rw [(measurePreserving_eval (fun _ : Fin n => obsLaw P) j).map_eq,
        (measurePreserving_eval (fun _ : Fin m => xaLaw P) i).map_eq] at he
      have hs := Measure.map_map measurable_swap
        ((measurable_pi_apply j).prodMap (measurable_pi_apply i))
          (μ := (Measure.pi (fun _ : Fin n => obsLaw P)).prod
            (Measure.pi (fun _ : Fin m => xaLaw P)))
      rw [← he, Measure.prod_swap] at hs
      exact hs.symm
    rw [← hmap, integral_map (by fun_prop) hH.aestronglyMeasurable]

/-- Squared kernel energy on an original-record pair equals its independent product-law energy.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the specified input i](hyp:i), [the specified input j](hyp:j), [the specified input hi](hyp:hi), [the specified input hj](hyp:hj), [the rectangular role pair square integral conclusion](goal) holds. -/
lemma rectangular_role_pair_square_integral {d n m : ℕ} (P : PrimitiveLaw d)
    (H : (Cov d × Bool) × (Cov d × Bool × Bool) → ℝ) (hH : Measurable H)
    (i : Fin (n+m)) (j : Fin n)
    (hi : i ∈ (roleSplit n m).2) (hj : j ∈ (roleSplit n m).1) :
    (∫ w : Sample d n m, (H (treatmentRecords w.1 i, w.1.1 j))^2
      ∂experiment P n m) = ∫ p, (H p)^2 ∂(xaLaw P).prod (obsLaw P) := by
  exact rectangular_role_pair_integral P (fun p => (H p)^2) (by fun_prop) i j hi hj

/-- Averaging a full observation statistic over the outcome role has the usual iid variance.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input hn](hyp:hn), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the rectangular outcome role centered energy conclusion](goal) holds. -/
lemma rectangular_outcome_role_centered_energy {d n m : ℕ} (P : PrimitiveLaw d)
    (hn : 2 ≤ n) (f : Cov d × Bool × Bool → ℝ) (hf : MemLp f 2 (obsLaw P)) :
    (∫ w : Sample d n m, ((outcomeCount n : ℝ)⁻¹ *
      ∑ j ∈ (roleSplit n m).1, f (w.1.1 j) - ∫ z, f z ∂obsLaw P)^2
      ∂experiment P n m) = (outcomeCount n : ℝ)⁻¹ * Var[f; obsLaw P] := by
  classical
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  letI := population_randomizer_probability
  let μ := Measure.pi (fun _ : Fin n => obsLaw P)
  let X := fun j : Fin n => fun D : Fin n → Cov d × Bool × Bool => f (D j)
  let F := fun D : Fin n → Cov d × Bool × Bool =>
    (outcomeCount n : ℝ)⁻¹ * ∑ j ∈ (roleSplit n m).1, f (D j)
  have hX (j : Fin n) : MemLp (X j) 2 μ :=
    hf.comp_measurePreserving (measurePreserving_eval _ j)
  have hF : MemLp F 2 μ :=
    (memLp_finsetSum _ (fun j _ => hX j)).const_mul _
  have hc : (outcomeCount n : ℝ) ≠ 0 := by
    exact_mod_cast (population_role_counts_pos n m hn).1.ne'
  have hmean : (∫ D, F D ∂μ) = ∫ z, f z ∂obsLaw P := by
    dsimp only [F]
    rw [integral_const_mul, integral_finsetSum _ (fun j _ => (hX j).integrable (by norm_num))]
    dsimp only [X, μ]
    simp_rw [integral_comp_eval (μ := fun _ : Fin n => obsLaw P) (f := f)
      hf.aestronglyMeasurable]
    simp only [Finset.sum_const, nsmul_eq_mul, (population_role_cardinalities n m).1]
    field_simp
  have hv : Var[F; μ] = (outcomeCount n : ℝ)⁻¹ * Var[f; obsLaw P] := by
    have heF : F = fun D => (outcomeCount n : ℝ)⁻¹ *
        (∑ j ∈ (roleSplit n m).1, X j) D := by
      funext D
      simp only [F, X, Finset.sum_apply]
    rw [heF]
    rw [variance_const_mul, IndepFun.variance_sum (fun j _ => hX j)]
    · have he (j : Fin n) : Var[X j; μ] = Var[f; obsLaw P] :=
        (measurePreserving_eval (fun _ : Fin n => obsLaw P) j).variance_fun_comp hf.aemeasurable
      simp_rw [he]
      simp only [Finset.sum_const, nsmul_eq_mul, (population_role_cardinalities n m).1]
      field_simp
    · intro i _ j _ hij
      exact (iIndepFun_pi (μ := fun _ : Fin n => obsLaw P)
        (X := fun _ => f) (fun _ => hf.aemeasurable)).indepFun hij
  rw [experiment_integral_dataset P (fun D : Dataset d n m =>
    ((outcomeCount n : ℝ)⁻¹ * ∑ j ∈ (roleSplit n m).1, f (D.1 j) -
      ∫ z, f z ∂obsLaw P)^2)]
  rw [integral_fun_fst (fun D : Fin n → Cov d × Bool × Bool =>
    (F D - ∫ z, f z ∂obsLaw P)^2)]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [← hmean, ← variance_eq_integral hF.aemeasurable]
  exact hv

/-- The outcome-role first-order centered energy has labeled-sample inverse-volume order.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input hn](hyp:hn), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the rectangular outcome role energy le conclusion](goal) holds. -/
lemma rectangular_outcome_role_energy_le {d n m : ℕ} (P : PrimitiveLaw d)
    (hn : 2 ≤ n) (f : Cov d × Bool × Bool → ℝ) (hf : MemLp f 2 (obsLaw P)) :
    (∫ w : Sample d n m, ((outcomeCount n : ℝ)⁻¹ *
      ∑ j ∈ (roleSplit n m).1, f (w.1.1 j) - ∫ z, f z ∂obsLaw P)^2
      ∂experiment P n m) ≤ (3/(n:ℝ)) * (∫ z, (f z)^2 ∂obsLaw P) := by
  letI := obsLaw_probability P
  rw [rectangular_outcome_role_centered_energy P hn f hf]
  have hv : Var[f; obsLaw P] ≤ ∫ z, (f z)^2 ∂obsLaw P := by
    rw [variance_eq_integral hf.aemeasurable]
    exact rectangular_centered_energy_le (obsLaw P) f hf
  exact mul_le_mul (rectangular_role_inverse_bounds n m hn).1 hv
    (variance_nonneg f (obsLaw P)) (by positivity)

/-- The vector correction's squared kernel bound holds on every actual rectangular pair.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the specified input i](hyp:i), [the specified input j](hyp:j), [the specified input hi](hyp:hi), [the specified input hj](hyp:hj), [the rectangular experiment r kernel energy conclusion](goal) holds. -/
lemma rectangular_experiment_r_kernel_energy {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (u : PolyIdx d) (i : Fin (n+m)) (j : Fin n)
    (hi : i ∈ (roleSplit n m).2) (hj : j ∈ (roleSplit n m).1) :
    (∫ w : Sample d n m,
      (locWeight h (treatmentRecords w.1 i).1 * locWeight h (w.1.1 j).1 *
        coarseBasis h (treatmentRecords w.1 i).1 u * bit (treatmentRecords w.1 i).2 *
        fineKernel d h J (treatmentRecords w.1 i).1 (w.1.1 j).1 *
        bit (w.1.1 j).2.2)^2 ∂experiment P n m) ≤
      ((4:ℝ)^d)^2 * ((Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d / h^(2*d)) := by
  rw [rectangular_role_pair_square_integral P
    (fun p => locWeight h p.1.1 * locWeight h p.2.1 * coarseBasis h p.1.1 u *
      bit p.1.2 * fineKernel d h J p.1.1 p.2.1 * bit p.2.2.2) (by fun_prop) i j hi hj]
  exact rectangular_r_kernel_energy P hP h J hh hh' hJ u

/-- The raw Gram correction's squared kernel bound holds on every actual rectangular pair.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the specified input v](hyp:v), [the specified input i](hyp:i), [the specified input j](hyp:j), [the specified input hi](hyp:hi), [the specified input hj](hyp:hj), [the rectangular experiment q kernel energy conclusion](goal) holds. -/
lemma rectangular_experiment_q_kernel_energy {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (u v : PolyIdx d) (i : Fin (n+m)) (j : Fin n)
    (hi : i ∈ (roleSplit n m).2) (hj : j ∈ (roleSplit n m).1) :
    (∫ w : Sample d n m,
      (locWeight h (treatmentRecords w.1 i).1 * locWeight h (w.1.1 j).1 *
        coarseBasis h (treatmentRecords w.1 i).1 u * coarseBasis h (w.1.1 j).1 v *
        bit (treatmentRecords w.1 i).2 * bit (w.1.1 j).2.1 *
        fineKernel d h J (treatmentRecords w.1 i).1 (w.1.1 j).1)^2 ∂experiment P n m) ≤
      ((4:ℝ)^d)^4 * ((Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d / h^(2*d)) := by
  rw [rectangular_role_pair_square_integral P
    (fun p => locWeight h p.1.1 * locWeight h p.2.1 * coarseBasis h p.1.1 u *
      coarseBasis h p.2.1 v * bit p.1.2 * bit p.2.2.1 *
      fineKernel d h J p.1.1 p.2.1) (by fun_prop) i j hi hj]
  exact rectangular_q_kernel_energy P hP h J hh hh' hJ u v

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
