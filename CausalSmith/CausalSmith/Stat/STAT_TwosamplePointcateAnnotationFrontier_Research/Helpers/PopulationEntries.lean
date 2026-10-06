module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationRoles

/-!
# Population Gram entries

Finite kernel expansion and independence of the two roles compute the population
Gram entries directly from the original-record experiment.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 800000
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Bounded treatment features remain integrable after averaging over the outcome role.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hfB](hyp:hfB), [the population outcome role integrable conclusion](goal) holds. -/
lemma population_outcome_role_integrable {d n m : ℕ} (P : PrimitiveLaw d)
    (f : Cov d × Bool → ℝ) (hf : Measurable f) (B : ℝ) (hfB : ∀ z, ‖f z‖ ≤ B) :
    Integrable (fun w : Sample d n m => (outcomeCount n : ℝ)⁻¹ *
      ∑ j ∈ (roleSplit n m).1, f ((w.1.1 j).1, (w.1.1 j).2.1)) (experiment P n m) := by
  classical
  letI := population_experiment_probability P n m
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro j _
  exact population_integrable_bounded _ _ (hf.comp (by fun_prop)) B (fun w => hfB _)

/-- Products of bounded features are integrable over the rectangular role average.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input B](hyp:B), [the specified input C](hyp:C), [the specified input hfB](hyp:hfB), [the specified input hgC](hyp:hgC), [the population rectangular role integrable conclusion](goal) holds. -/
lemma population_rectangular_role_integrable {d n m : ℕ} (P : PrimitiveLaw d)
    (f g : Cov d × Bool → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B C : ℝ) (hfB : ∀ z, ‖f z‖ ≤ B) (hgC : ∀ z, ‖g z‖ ≤ C) :
    Integrable (fun w : Sample d n m => ((treatmentCount n m : ℝ)*(outcomeCount n : ℝ))⁻¹ *
      ∑ i ∈ (roleSplit n m).2, ∑ j ∈ (roleSplit n m).1,
        f (treatmentRecords w.1 i) * g ((w.1.1 j).1, (w.1.1 j).2.1)) (experiment P n m) := by
  classical
  letI := population_experiment_probability P n m
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply population_integrable_bounded _ _ (by fun_prop) (B*C)
  intro w
  rw [norm_mul]
  exact mul_le_mul (hfB _) (hgC _) (norm_nonneg _)
    ((norm_nonneg (f (treatmentRecords w.1 i))).trans (hfB _))

/-- Coarse products and coarse-fine products have finite bounds on the localization box.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the specified input v](hyp:v), [the specified input z](hyp:z), [the population basis product bounds conclusion](goal) holds. -/
lemma population_basis_product_bounds (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hJ : 1 ≤ J) (u v : PolyIdx d) (z : FineIdx d J) :
    (∀ x ∈ locCube d h, ‖coarseBasis h x u * coarseBasis h x v‖ ≤ (4:ℝ)^d * (4:ℝ)^d) ∧
    (∀ x ∈ locCube d h, ‖coarseBasis h x u * fineBasis h J x z‖ ≤
      (4:ℝ)^d * (Real.sqrt ((J:ℝ)^d) * (4:ℝ)^d)) := by
  constructor
  · intro x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (coarseBasis_abs_bound d h hh x hx u)
      (coarseBasis_abs_bound d h hh x hx v) (abs_nonneg _) (by positivity)
  · intro x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (coarseBasis_abs_bound d h hh x hx u)
      (fineBasis_abs_bound d h J hh hJ x z) (abs_nonneg _) (by positivity)

/-- Expanding the fine kernel decomposes the raw Gram entry into finite role averages.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input D](hyp:D), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input u](hyp:u), [the specified input v](hyp:v), [the q raw finite role expansion conclusion](goal) holds. -/
lemma qRaw_finite_role_expansion {d n m : ℕ} (D : Dataset d n m)
    (h : ℝ) (J : ℕ) (u v : PolyIdx d) :
    qRaw D h J u v =
      (outcomeCount n : ℝ)⁻¹ * ∑ j ∈ (roleSplit n m).1,
        weightedTreatmentFeature h (fun x => coarseBasis h x u * coarseBasis h x v)
          ((D.1 j).1, (D.1 j).2.1) -
      ∑ z : FineIdx d J, ((treatmentCount n m : ℝ)*(outcomeCount n : ℝ))⁻¹ *
        ∑ i ∈ (roleSplit n m).2, ∑ j ∈ (roleSplit n m).1,
          weightedTreatmentFeature h (fun x => coarseBasis h x u * fineBasis h J x z)
            (treatmentRecords D i) *
          weightedTreatmentFeature h (fun x => coarseBasis h x v * fineBasis h J x z)
            ((D.1 j).1, (D.1 j).2.1) := by
  classical
  unfold qRaw weightedTreatmentFeature fineKernel
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp only [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro z _
    ring

/-- Raw Gram entries are integrable and have the expected localized coordinate formula.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input J](hyp:J), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the specified input v](hyp:v), [the population raw gram entries conclusion](goal) holds. -/
lemma population_raw_gram_entries {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (n m : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (J : ℕ) (hJ : 1 ≤ J) (u v : PolyIdx d) :
    Integrable (fun w : Sample d n m => qRaw w.1 h J u v) (experiment P n m) ∧
    (∫ w : Sample d n m, qRaw w.1 h J u v ∂experiment P n m) =
      (∫ x, coarseBasis h x u * (designatedPropensity P hP x * coarseBasis h x v) ∂locLaw d h) -
      ∑ z : FineIdx d J,
        (∫ x, fineBasis h J x z * (designatedPropensity P hP x * coarseBasis h x u) ∂locLaw d h) *
        (∫ x, fineBasis h J x z * (designatedPropensity P hP x * coarseBasis h x v) ∂locLaw d h) := by
  classical
  let f := weightedTreatmentFeature h (fun x => coarseBasis h x u * coarseBasis h x v)
  let g := fun (a : PolyIdx d) (z : FineIdx d J) =>
    weightedTreatmentFeature h (fun x => coarseBasis h x a * fineBasis h J x z)
  let B : ℝ := h^(-(d:ℝ)) * ((4:ℝ)^d * (4:ℝ)^d)
  let C : ℝ := h^(-(d:ℝ)) * ((4:ℝ)^d * (Real.sqrt ((J:ℝ)^d) * (4:ℝ)^d))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg (a z) : Measurable (g a z) := by dsimp [g]; fun_prop
  have hfB (w) : ‖f w‖ ≤ B := weightedTreatmentFeature_norm_bound h hh _ _ (by positivity)
    (fun x hx => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (coarseBasis_abs_bound d h hh x hx u)
        (coarseBasis_abs_bound d h hh x hx v) (abs_nonneg _) (by positivity)) w
  have hgC (a z w) : ‖g a z w‖ ≤ C := weightedTreatmentFeature_norm_bound h hh _ _ (by positivity)
    (population_basis_product_bounds d h J hh hJ a a z).2 w
  have hi := population_outcome_role_integrable (n := n) (m := m) P f hf B hfB
  have hj (z) := population_rectangular_role_integrable (n := n) (m := m) P
    (g u z) (g v z) (hg u z) (hg v z) C C (hgC u z) (hgC v z)
  have heq := qRaw_finite_role_expansion (d := d) (n := n) (m := m)
  constructor
  · simp_rw [heq]
    exact hi.sub (integrable_finsetSum _ (fun z _ => hj z))
  · simp_rw [heq]
    rw [integral_sub hi (integrable_finsetSum _ (fun z _ => hj z)),
      integral_finsetSum _ (fun z _ => hj z), population_outcome_role_mean P hn f hf B hfB]
    simp_rw [population_rectangular_role_mean P hn (g u _) (g v _) (hg u _) (hg v _)
      C C (hgC u _) (hgC v _)]
    have hfm := designated_local_treatment_moment P hP h hh hh'
      (fun x => coarseBasis h x u * coarseBasis h x v) (by fun_prop)
      ((4:ℝ)^d * (4:ℝ)^d) (by positivity)
      (fun x hx => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (coarseBasis_abs_bound d h hh x hx u)
        (coarseBasis_abs_bound d h hh x hx v) (abs_nonneg _) (by positivity))
    have hgm (a z) := designated_local_treatment_moment P hP h hh hh'
      (fun x => coarseBasis h x a * fineBasis h J x z) (by fun_prop)
      ((4:ℝ)^d * (Real.sqrt ((J:ℝ)^d) * (4:ℝ)^d)) (by positivity)
      (population_basis_product_bounds d h J hh hJ a a z).2
    change (∫ w, locWeight h w.1 * (coarseBasis h w.1 u * coarseBasis h w.1 v) * bit w.2 ∂xaLaw P) -
      ∑ z, (∫ w, locWeight h w.1 * (coarseBasis h w.1 u * fineBasis h J w.1 z) * bit w.2 ∂xaLaw P) *
        (∫ w, locWeight h w.1 * (coarseBasis h w.1 v * fineBasis h J w.1 z) * bit w.2 ∂xaLaw P) = _
    rw [hfm]
    simp_rw [hgm]
    congr 1
    · apply integral_congr_ae
      filter_upwards [] with x
      ring
    · apply Finset.sum_congr rfl
      intro z _
      congr 1 <;> apply integral_congr_ae <;> filter_upwards [] with x <;> ring

/-- Symmetrization preserves the symmetric localized population Gram formula.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input J](hyp:J), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the specified input v](hyp:v), [the population gram entries conclusion](goal) holds. -/
lemma population_gram_entries {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (n m : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (J : ℕ) (hJ : 1 ≤ J) (u v : PolyIdx d) :
    qPop P n m h J u v =
      (∫ x, coarseBasis h x u * (designatedPropensity P hP x * coarseBasis h x v) ∂locLaw d h) -
      ∑ z : FineIdx d J,
        (∫ x, fineBasis h J x z * (designatedPropensity P hP x * coarseBasis h x u) ∂locLaw d h) *
        (∫ x, fineBasis h J x z * (designatedPropensity P hP x * coarseBasis h x v) ∂locLaw d h) := by
  have huv := population_raw_gram_entries P hP n m hn h hh hh' J hJ u v
  have hvu := population_raw_gram_entries P hP n m hn h hh hh' J hJ v u
  unfold qPop qHat
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, integral_add huv.1 hvu.1, huv.2, hvu.2]
  have hs : (∫ x, coarseBasis h x v * (designatedPropensity P hP x * coarseBasis h x u) ∂locLaw d h) =
      ∫ x, coarseBasis h x u * (designatedPropensity P hP x * coarseBasis h x v) ∂locLaw d h := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hs]
  simp_rw [mul_comm (∫ x, fineBasis h J x _ * (designatedPropensity P hP x * coarseBasis h x v) ∂locLaw d h)]
  ring

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

