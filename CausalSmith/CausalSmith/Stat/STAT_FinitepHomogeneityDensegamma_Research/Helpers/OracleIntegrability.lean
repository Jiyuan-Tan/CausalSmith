module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.OracleRule
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreIntegrability
public import Mathlib.MeasureTheory.Function.L2Space

/-! Centered oracle features and finite moments on the full supplied-function domain. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Centering subtracts the coordinate average from each coordinate. [This is the stated conclusion](goal). -/
-- @node: centerVec_apply
lemma centerVec_apply {J : ℕ} (z : Vec J) (j : Fin J) :
    centerVec z j = z j-(∑ k : Fin J, z k)/(J:ℝ) := by
  simp [centerVec]

/-- The centered coordinates sum to zero, including the empty rank. [This is the stated conclusion](goal). -/
-- @node: centerVec_sum_zero
lemma centerVec_sum_zero {J : ℕ} (z : Vec J) :
    (∑ j : Fin J, centerVec z j) = 0 := by
  simp only [centerVec_apply, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hJ : J = 0
  · subst J; simp
  · field_simp
    ring

/-- Centering removes every constant-coordinate vector. [This is the stated conclusion](goal). -/
-- @node: centerVec_const
lemma centerVec_const (J : ℕ) (c : ℝ) :
    centerVec (WithLp.toLp 2 (fun _ : Fin J => c)) = 0 := by
  ext j
  have hJ : (J:ℝ) ≠ 0 := by exact_mod_cast (show J ≠ 0 by have := j.isLt; omega)
  simp [centerVec_apply, hJ]

/-- A second centering leaves the first centered vector unchanged. [This is the stated conclusion](goal). -/
-- @node: centerVec_idempotent
lemma centerVec_idempotent {J : ℕ} (z : Vec J) : centerVec (centerVec z) = centerVec z := by
  ext j
  rw [centerVec_apply, centerVec_sum_zero]
  simp

/-- Centering is self-adjoint for the Euclidean inner product. [This is the stated conclusion](goal). -/
-- @node: centerVec_inner
lemma centerVec_inner {J : ℕ} (u z : Vec J) :
    inner ℝ u (centerVec z) = inner ℝ (centerVec u) z := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, centerVec_apply,
    sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- Centering decreases squared Euclidean norm by the energy of the constant coordinate. This statement assumes [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: centerVec_norm_sq
lemma centerVec_norm_sq {J : ℕ} (hJ : 0 < J) (z : Vec J) :
    ‖centerVec z‖^2 = ‖z‖^2-(∑ j : Fin J, z j)^2/(J:ℝ) := by
  have hJr : (J:ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp_rw [centerVec_apply, sub_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul,
    ← Finset.mul_sum]
  field_simp
  ring

/-- The centering map is a contraction, also at rank zero. [This is the stated conclusion](goal). -/
-- @node: centerVec_norm_le
lemma centerVec_norm_le {J : ℕ} (z : Vec J) : ‖centerVec z‖ ≤ ‖z‖ := by
  by_cases hJ : 0 < J
  · have he := centerVec_norm_sq hJ z
    have hd : 0 ≤ (∑ j : Fin J, z j)^2/(J:ℝ) := by positivity
    nlinarith [norm_nonneg (centerVec z), norm_nonneg z]
  · have : J = 0 := by omega
    subst J
    have hz : z = 0 := Subsingleton.elim _ _
    simp [hz, centerVec]

/-- Centered-feature energy is bounded by the original contrast norm. This statement assumes [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: centered_feature_energy_le
lemma centered_feature_energy_le (J : ℕ) (hJ : 0 < J) (u : Vec J) :
    (∫ x, (inner ℝ u (centerVec (featureMap J x)))^2 ∂design) ≤ ‖u‖^2 := by
  simp_rw [centerVec_inner]
  rw [feature_isometry J hJ]
  exact pow_le_pow_left₀ (norm_nonneg _) (centerVec_norm_le u) 2

/-- The extension clips every supplied function into the common overlap interval. [This is the stated conclusion](goal). -/
-- @node: clipProp_bounds
lemma clipProp_bounds (f : Nuisance) (x : unitInterval) :
    (1/4:ℝ) ≤ clipProp f x ∧ clipProp f x ≤ 3/4 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

/-- A clipped inverse-propensity score has a finite bound even outside the model. [This is the stated conclusion](goal). -/
-- @node: ipwScore_abs_bound
lemma ipwScore_abs_bound (f : Nuisance) (T : ℝ) (o : Record) :
    |ipwScore f T o| ≤ 4*|T| := by
  have hc := clipProp_bounds f (X o)
  have he : 0 < clipProp f (X o) := by linarith
  have hne : 0 < 1-clipProp f (X o) := by linarith
  have hy : |clipY T (Y o)| ≤ |T| := by
    by_cases hT : 0 ≤ T
    · simpa [abs_of_nonneg hT] using clipY_abs_le T (Y o) hT
    · have ht : min (Y o) T ≤ -T := (min_le_right _ _).trans (by linarith)
      simp [clipY, max_eq_left ht]
  cases hA : A o
  · have hs : ipwScore f T o = -(clipY T (Y o)/(1-clipProp f (X o))) := by
      simp [ipwScore, treatment, hA]
    rw [hs, abs_neg, abs_div, abs_of_pos hne]
    apply (div_le_iff₀ hne).mpr
    nlinarith [abs_nonneg T]
  · have hs : ipwScore f T o = clipY T (Y o)/clipProp f (X o) := by
      simp [ipwScore, treatment, hA]
    rw [hs, abs_div, abs_of_pos he]
    apply (div_le_iff₀ he).mpr
    nlinarith [abs_nonneg T]

/-- Every measurable record map yields a bounded oracle score. This statement assumes [the ho condition](hyp:ho). [This is the stated conclusion](goal). -/
-- @node: ipwScore_memLp_top
lemma ipwScore_memLp_top {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Nuisance) (T : ℝ) (o : Ω → Record) (ho : Measurable o) :
    MemLp (fun d => ipwScore f T (o d)) ∞ μ := by
  have hm : Measurable (fun d => ipwScore f T (o d)) :=
    (measurable_ipwScore T).comp (measurable_const.prodMk ho)
  apply memLp_top_of_bound hm.aestronglyMeasurable (4*|T|)
  exact ae_of_all _ (fun d => by simpa [Real.norm_eq_abs] using ipwScore_abs_bound f T (o d))

/-- Composed centered histogram features remain uniformly bounded. This statement assumes [the hx condition](hyp:hx). [This is the stated conclusion](goal). -/
-- @node: centeredFeature_memLp_top
lemma centeredFeature_memLp_top {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ℕ) (x : Ω → unitInterval) (hx : Measurable x) :
    MemLp (fun d => centerVec (featureMap J (x d))) ∞ μ := by
  have hm := (continuous_centerVec J).measurable.comp ((measurable_featureMap J).comp hx)
  apply memLp_top_of_bound hm.aestronglyMeasurable (Real.sqrt ((J:ℝ)*J))
  exact ae_of_all _ (fun d => (centerVec_norm_le _).trans (featureMap_norm_bound J (x d)))

/-- The finite oracle block is bounded for every dataset and supplied function. [This is the stated conclusion](goal). -/
-- @node: oracleBlockVec_memLp_top
lemma oracleBlockVec_memLp_top (n : ℕ) (v : Params) (f : Nuisance) (b : Bool)
    (μ : Measure (Dataset n)) : MemLp (oracleBlockVec n v f b) ∞ μ := by
  unfold oracleBlockVec
  change MemLp ((_ : ℝ) • (fun data : Dataset n => (_ : Vec (oracleJ n v)))) ∞ μ
  apply MemLp.const_smul
  apply memLp_finsetSum
  intro i _
  exact (centeredFeature_memLp_top μ _ (fun d => X (d i)) (by unfold X; fun_prop)).smul
    (ipwScore_memLp_top μ f _ (fun d => d i) (by fun_prop))

/-- On any finite sampling measure the oracle block has every finite moment. This statement assumes [the p condition](hyp:p). [This is the stated conclusion](goal). -/
-- @node: oracleBlockVec_memLp
lemma oracleBlockVec_memLp (n : ℕ) (v : Params) (f : Nuisance) (b : Bool)
    (μ : Measure (Dataset n)) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (oracleBlockVec n v f b) p μ :=
  (oracleBlockVec_memLp_top n v f b μ).mono_exponent le_top

/-- Every scalar oracle contrast is square integrable under the original sampling law. [This is the stated conclusion](goal). -/
-- @node: oracleBlockVec_inner_memLp
lemma oracleBlockVec_inner_memLp (n : ℕ) (v : Params) (f : Nuisance) (b : Bool)
    (law : ObservedLaw) (u : Vec (oracleJ n v)) :
    MemLp (fun data => inner ℝ u (oracleBlockVec n v f b data)) 2
      (Measure.pi fun _ : Fin n => law.P) :=
  (oracleBlockVec_memLp n v f b _ 2).const_inner u

end CausalSmith.Stat.FinitepHomogeneityDensegamma
