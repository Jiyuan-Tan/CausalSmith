module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.SigningSymmetrization

/-! # Conditional cross-group expectations

Finite projection classes retain their exact Rademacher average after centering
and contraction. For a fixed complementary sample this gives the conditional
cross-group bound used in the isotropic signing roadmap.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Isotropic projections have integrable absolute values.](goal) Under [the stated conditions](hyp:hmom). -/
-- @node: isotropic_abs_projection_integrable
lemma isotropic_abs_projection_integrable (r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P) (u : EuclideanSpace ℝ (Fin r)) :
    Integrable (fun v => |inner ℝ u v|) P := by
  have h : MemLp (fun v => inner ℝ u v) 2 P :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (isotropic_projection_sq_integrable r P hmom u)
  exact (h.integrable (by norm_num)).abs

/-- [ Centering a finite bounded direction class costs at most its radius times the
sample size. The remaining term is the actual centered supremum.](goal) Under [the stated conditions](hyp:hmom,hiso,hu). -/
-- @node: finite_projection_sum_le_centered
lemma finite_projection_sum_le_centered {ι : Type} [Finite ι] [Nonempty ι]
    (n r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P)
    (hiso : ∀ h k, (∫ v, v h * v k ∂P) = if h = k then 1 else 0)
    (u : ι → EuclideanSpace ℝ (Fin r)) {R : ℝ} (hu : ∀ a, ‖u a‖ ≤ R)
    (x : Fin n → EuclideanSpace ℝ (Fin r)) :
    (⨆ a, ∑ i, |inner ℝ (u a) (x i)|) ≤ (n : ℝ) * R +
      finiteCenteredSumSup P (fun a v => |inner ℝ (u a) v|) x := by
  apply ciSup_le
  intro a
  have hc := (isotropic_projection_abs_integral_le r P hmom hiso (u a)).trans (hu a)
  have hs := le_ciSup (Finite.bddAbove_range
    (fun a => |∑ i, (|inner ℝ (u a) (x i)| - ∫ v, |inner ℝ (u a) v| ∂P)|)) a
  have he : (∑ i, |inner ℝ (u a) (x i)|) =
      (∑ i, (|inner ℝ (u a) (x i)| - ∫ v, |inner ℝ (u a) v| ∂P)) +
        (n : ℝ) * (∫ v, |inner ℝ (u a) v| ∂P) := by
    simp [Finset.sum_sub_distrib]
  dsimp only [finiteCenteredSumSup] at ⊢
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  linarith [le_abs_self (∑ i, (|inner ℝ (u a) (x i)| - ∫ v, |inner ℝ (u a) v| ∂P))]

/-- [ Symmetrization and contraction bound the uncentered finite projection supremum
while preserving the exact linear Rademacher average for the independent-group step.](goal) Under [the stated conditions](hyp:hContraction,hmom,hiso,hu). -/
-- @node: finite_projection_sum_integral_le_exact_rad
lemma finite_projection_sum_integral_le_exact_rad {ι : Type} [Finite ι] [Nonempty ι]
    (hContraction : ClassicalRademacherContraction)
    (n r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P)
    (hiso : ∀ h k, (∫ v, v h * v k ∂P) = if h = k then 1 else 0)
    (u : ι → EuclideanSpace ℝ (Fin r)) {R : ℝ} (hu : ∀ a, ‖u a‖ ≤ R) :
    (∫ x : Fin n → EuclideanSpace ℝ (Fin r), ⨆ a, ∑ i, |inner ℝ (u a) (x i)|
      ∂Measure.pi (fun _ : Fin n => P)) ≤ (n : ℝ) * R +
        4 * (∫ x : Fin n → EuclideanSpace ℝ (Fin r),
          ∫ z : Signs n, finiteRadSumSup (fun a v => inner ℝ (u a) v) x z
            ∂fairSigns n ∂Measure.pi (fun _ : Fin n => P)) := by
  let f : ι → EuclideanSpace ℝ (Fin r) → ℝ := fun a v => inner ℝ (u a) v
  have hm : ∀ a, Measurable (f a) := by intro a; fun_prop
  have hi : ∀ a, Integrable (f a) P := by
    intro a
    exact ((memLp_two_iff_integrable_sq (hm a).aestronglyMeasurable).mpr
      (isotropic_projection_sq_integrable r P hmom (u a))).integrable (by norm_num)
  have hC := finiteCenteredSumSup_integrable P (fun a v => |f a v|)
    (fun a => (hm a).abs) (fun a => (hi a).abs) n
  have hL : Integrable (fun x : Fin n → EuclideanSpace ℝ (Fin r) =>
      ⨆ a, ∑ i, |f a (x i)|) (Measure.pi (fun _ : Fin n => P)) := by
    have h := finite_abs_sup_integrable (Measure.pi (fun _ : Fin n => P))
      (fun a x => ∑ i, |f a (x i)|) (by intro a; fun_prop)
      (fun a => integrable_finsetSum _ (fun i _ =>
        (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable
          (hi a).abs))
    have he (x : Fin n → EuclideanSpace ℝ (Fin r)) (a : ι) :
        |(∑ i, |f a (x i)|)| = ∑ i, |f a (x i)| :=
      abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    simpa only [he] using h
  have hcenter := finite_abs_centered_ofReal_le_contraction hContraction P f hm hi n
  rw [finiteRadSumSup_radAverage_eq P f hm hi n] at hcenter
  have hnonneg : 0 ≤ (∫ x : Fin n → EuclideanSpace ℝ (Fin r),
      ∫ z : Signs n, finiteRadSumSup f x z ∂fairSigns n
        ∂Measure.pi (fun _ : Fin n => P)) := by
    apply integral_nonneg; intro x
    apply integral_nonneg; intro z
    obtain ⟨a⟩ := (inferInstance : Nonempty ι)
    unfold finiteRadSumSup
    exact (abs_nonneg _).trans (le_ciSup (Finite.bddAbove_range
      (fun a => |∑ i, sgn (z i) * f a (x i)|)) a)
  have hfour : (4 : ENNReal) = ENNReal.ofReal 4 := by norm_num
  rw [hfour, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)] at hcenter
  have hbound := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num) hnonneg)).mp hcenter
  have hmono := integral_mono hL ((integrable_const ((n : ℝ) * R)).add hC)
    (finite_projection_sum_le_centered n r P hmom hiso u hu)
  simp only [Pi.add_apply] at hmono
  rw [integral_add (integrable_const _) hC, integral_const] at hmono
  simp only [probReal_univ, one_smul] at hmono
  exact hmono.trans (add_le_add_right hbound ((n : ℝ) * R))

/-- Cross-group sign optimization as a finite class of absolute projections. -/
-- @node: twoGroupCrossMax
def twoGroupCrossMax {a b r : ℕ} (x : Fin a → EuclideanSpace ℝ (Fin r))
    (y : Fin b → EuclideanSpace ℝ (Fin r)) : ℝ :=
  ⨆ w : Signs b, ∑ i, |inner ℝ (∑ j, sgn (w j) • y j) (x i)|

/-- The cross-group maximum is nonnegative, also for empty groups. [The asserted mathematical result follows](goal). -/
-- @node: twoGroupCrossMax_nonneg
lemma twoGroupCrossMax_nonneg {a b r : ℕ} (x : Fin a → EuclideanSpace ℝ (Fin r))
    (y : Fin b → EuclideanSpace ℝ (Fin r)) : 0 ≤ twoGroupCrossMax x y := by
  unfold twoGroupCrossMax
  exact (Finset.sum_nonneg (fun _ _ => abs_nonneg _)).trans
    (le_ciSup (Finite.bddAbove_range (fun w : Signs b =>
      ∑ i, |inner ℝ (∑ j, sgn (w j) • y j) (x i)|)) (fun _ => true))

/-- Two independent groups give a product-integrable cross maximum under the
common envelope consisting of the product of their summed row norms. Under [the stated conditions](hyp:hmom), [the asserted mathematical result follows](goal). -/
-- @node: twoGroupCrossMax_joint_integrable
lemma twoGroupCrossMax_joint_integrable (a b r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P) :
    Integrable (fun p : (Fin b → EuclideanSpace ℝ (Fin r)) ×
        (Fin a → EuclideanSpace ℝ (Fin r)) => twoGroupCrossMax p.2 p.1)
      ((Measure.pi (fun _ : Fin b => P)).prod (Measure.pi (fun _ : Fin a => P))) := by
  have hn : Integrable (fun v : EuclideanSpace ℝ (Fin r) => ‖v‖) P :=
    ((memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (isotropic_norm_sq_integrable r P hmom)).integrable (by norm_num)
  have hs (k : ℕ) : Integrable (fun x : Fin k → EuclideanSpace ℝ (Fin r) => ∑ i, ‖x i‖)
      (Measure.pi (fun _ : Fin k => P)) := integrable_finsetSum _ (fun i _ =>
    (measurePreserving_eval (fun _ : Fin k => P) i).integrable_comp_of_integrable hn)
  apply ((hs b).mul_prod (hs a)).mono' (by
    unfold twoGroupCrossMax
    apply Measurable.aestronglyMeasurable
    apply Measurable.iSup
    intro w
    fun_prop)
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (twoGroupCrossMax_nonneg _ _)]
  unfold twoGroupCrossMax
  apply ciSup_le
  intro w
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply (abs_real_inner_le_norm _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖∑ j, sgn (w j) • p.1 j‖ ≤ ∑ j, ‖sgn (w j) • p.1 j‖ := norm_sum_le _ _
    _ = ∑ j, ‖p.1 j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      cases w j <;> simp [sgn]

/-- [ For a fixed complementary sample, the finite class of its signed sums gives
the conditional cross-group bound with no loss of the independent-group structure.](goal) Under [the stated conditions](hyp:hContraction,hmom,hiso). -/
-- @node: fixed_group_cross_integral_le_exact_rad
lemma fixed_group_cross_integral_le_exact_rad (hContraction : ClassicalRademacherContraction)
    (a b r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P)
    (hiso : ∀ h k, (∫ v, v h * v k ∂P) = if h = k then 1 else 0)
    (y : Fin b → EuclideanSpace ℝ (Fin r)) :
    (∫ x : Fin a → EuclideanSpace ℝ (Fin r),
      ⨆ w : Signs b, ∑ i, |inner ℝ (∑ j, sgn (w j) • y j) (x i)|
        ∂Measure.pi (fun _ : Fin a => P)) ≤ (a : ℝ) * signingNormMax y +
      4 * (∫ x : Fin a → EuclideanSpace ℝ (Fin r),
        ∫ z : Signs a, ∑ j, |inner ℝ (∑ i, sgn (z i) • x i) (y j)|
          ∂fairSigns a ∂Measure.pi (fun _ : Fin a => P)) := by
  have h := finite_projection_sum_integral_le_exact_rad hContraction a r P hmom hiso
    (fun w : Signs b => ∑ j, sgn (w j) • y j) (fun w => signing_norm_le_max y w)
  have he (x : Fin a → EuclideanSpace ℝ (Fin r)) (z : Signs a) :
      finiteRadSumSup (fun (w : Signs b) v => inner ℝ (∑ j, sgn (w j) • y j) v) x z =
        ∑ j, |inner ℝ (∑ i, sgn (z i) • x i) (y j)| := by
    unfold finiteRadSumSup
    have hsum (w : Signs b) :
        (∑ i, sgn (z i) * inner ℝ (∑ j, sgn (w j) • y j) (x i)) =
          inner ℝ (∑ i, sgn (z i) • x i) (∑ j, sgn (w j) • y j) := by
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_smul_left, real_inner_comm]
    simp_rw [hsum]
    exact signing_projection_max_eq_sum_abs y _
  simpa only [he] using h

/-- [ An independent group of isotropic rows costs at most its size times the norm
of a fixed direction, including the empty-group convention.](goal) Under [the stated conditions](hyp:hmom,hiso). -/
-- @node: isotropic_group_abs_projection_integral_le
lemma isotropic_group_abs_projection_integral_le (b r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P)
    (hiso : ∀ h k, (∫ v, v h * v k ∂P) = if h = k then 1 else 0)
    (u : EuclideanSpace ℝ (Fin r)) :
    (∫ y : Fin b → EuclideanSpace ℝ (Fin r), ∑ j, |inner ℝ u (y j)|
      ∂Measure.pi (fun _ : Fin b => P)) ≤ (b : ℝ) * ‖u‖ := by
  have hi := isotropic_abs_projection_integrable r P hmom u
  have he (j : Fin b) : Integrable (fun y : Fin b → EuclideanSpace ℝ (Fin r) =>
      |inner ℝ u (y j)|) (Measure.pi (fun _ : Fin b => P)) :=
    (measurePreserving_eval (fun _ : Fin b => P) j).integrable_comp_of_integrable hi
  rw [integral_finsetSum _ (fun j _ => he j)]
  simp_rw [integral_comp_eval (μ := fun _ : Fin b => P) hi.aestronglyMeasurable]
  simpa using mul_le_mul_of_nonneg_left
    (isotropic_projection_abs_integral_le r P hmom hiso u)
      (Nat.cast_nonneg b : (0 : ℝ) ≤ b)

/-- [ The signed first-group norm is jointly integrable under rows and fresh signs.](goal) Under [the stated conditions](hyp:hmom). -/
-- @node: isotropic_rademacher_norm_integrable
lemma isotropic_rademacher_norm_integrable (a r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P) :
    Integrable (fun ω : (Fin a → EuclideanSpace ℝ (Fin r)) × Signs a =>
      ‖∑ i, sgn (ω.2 i) • ω.1 i‖)
      ((Measure.pi (fun _ : Fin a => P)).prod (fairSigns a)) := by
  let := fairSigns_probability a
  exact ((memLp_two_iff_integrable_sq (by fun_prop)).mpr
    (isotropic_rademacher_norm_sq_integrable a r P hmom)).integrable (by norm_num)

/-- [ The linear Rademacher cross term has a product-integrable norm envelope;
this justifies exchanging the two independent groups without higher moments.](goal) Under [the stated conditions](hyp:hmom). -/
-- @node: rademacher_group_projection_joint_integrable
lemma rademacher_group_projection_joint_integrable (a b r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P) :
    Integrable (fun p : ((Fin a → EuclideanSpace ℝ (Fin r)) × Signs a) ×
        (Fin b → EuclideanSpace ℝ (Fin r)) =>
      ∑ j, |inner ℝ (∑ i, sgn (p.1.2 i) • p.1.1 i) (p.2 j)|)
      (((Measure.pi (fun _ : Fin a => P)).prod (fairSigns a)).prod
        (Measure.pi (fun _ : Fin b => P))) := by
  let := fairSigns_probability a
  have hn : Integrable (fun v : EuclideanSpace ℝ (Fin r) => ‖v‖) P :=
    ((memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (isotropic_norm_sq_integrable r P hmom)).integrable (by norm_num)
  have hy : Integrable (fun y : Fin b → EuclideanSpace ℝ (Fin r) => ∑ j, ‖y j‖)
      (Measure.pi (fun _ : Fin b => P)) := integrable_finsetSum _ (fun j _ =>
    (measurePreserving_eval (fun _ : Fin b => P) j).integrable_comp_of_integrable hn)
  apply ((isotropic_rademacher_norm_integrable a r P hmom).mul_prod hy).mono'
    (by fun_prop)
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)),
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => abs_real_inner_le_norm _ _)

/-- [ After exchanging the independent samples, isotropy bounds the exact cross
Rademacher average by the second-group size times the first-group square-root scale.](goal) Under [the stated conditions](hyp:hmom,hiso). -/
-- @node: independent_group_rad_projection_integral_le
lemma independent_group_rad_projection_integral_le (a b r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P)
    (hiso : ∀ h k, (∫ v, v h * v k ∂P) = if h = k then 1 else 0) :
    (∫ y : Fin b → EuclideanSpace ℝ (Fin r),
      ∫ ω : (Fin a → EuclideanSpace ℝ (Fin r)) × Signs a,
        ∑ j, |inner ℝ (∑ i, sgn (ω.2 i) • ω.1 i) (y j)|
          ∂(Measure.pi (fun _ : Fin a => P)).prod (fairSigns a)
          ∂Measure.pi (fun _ : Fin b => P)) ≤ (b : ℝ) * Real.sqrt ((a : ℝ) * r) := by
  let := fairSigns_probability a
  have hI := rademacher_group_projection_joint_integrable a b r P hmom
  rw [← integral_integral_swap (f := fun
    (ω : (Fin a → EuclideanSpace ℝ (Fin r)) × Signs a)
    (y : Fin b → EuclideanSpace ℝ (Fin r)) =>
      ∑ j, |inner ℝ (∑ i, sgn (ω.2 i) • ω.1 i) (y j)|) hI]
  have hnorm := isotropic_rademacher_norm_integrable a r P hmom
  have hmono := integral_mono hI.integral_prod_left (hnorm.const_mul (b : ℝ))
    (fun (ω : (Fin a → EuclideanSpace ℝ (Fin r)) × Signs a) =>
      isotropic_group_abs_projection_integral_le b r P hmom hiso
        (∑ i, sgn (ω.2 i) • ω.1 i))
  have heq : (∫ ω : (Fin a → EuclideanSpace ℝ (Fin r)) × Signs a,
      (b : ℝ) * ‖∑ i, sgn (ω.2 i) • ω.1 i‖
        ∂(Measure.pi (fun _ : Fin a => P)).prod (fairSigns a)) =
      (b : ℝ) * (∫ x : Fin a → EuclideanSpace ℝ (Fin r),
        ∫ z : Signs a, ‖∑ i, sgn (z i) • x i‖ ∂fairSigns a
          ∂Measure.pi (fun _ : Fin a => P)) := by
    rw [integral_const_mul]
    congr 1
    exact integral_prod _ hnorm
  rw [heq] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left
    (isotropic_rademacher_norm_integral_le a r P hmom hiso)
      (Nat.cast_nonneg b : (0 : ℝ) ≤ b))

/-- [ Integrating the conditional finite-class bound gives the cross-group
estimate in terms of the complementary group's expected maximum norm. Its
Rademacher term already has the sharp independent-group square-root scale.](goal) Under [the stated conditions](hyp:hContraction,hmom,hiso). -/
-- @node: independent_group_cross_integral_le
lemma independent_group_cross_integral_le (hContraction : ClassicalRademacherContraction)
    (a b r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P)
    (hiso : ∀ h k, (∫ v, v h * v k ∂P) = if h = k then 1 else 0) :
    (∫ y : Fin b → EuclideanSpace ℝ (Fin r),
      ∫ x : Fin a → EuclideanSpace ℝ (Fin r), twoGroupCrossMax x y
        ∂Measure.pi (fun _ : Fin a => P) ∂Measure.pi (fun _ : Fin b => P)) ≤
      (a : ℝ) * (∫ y : Fin b → EuclideanSpace ℝ (Fin r), signingNormMax y
        ∂Measure.pi (fun _ : Fin b => P)) + 4 * b * Real.sqrt ((a : ℝ) * r) := by
  let := fairSigns_probability a
  have hI := rademacher_group_projection_joint_integrable a b r P hmom
  have hnorm := isotropic_rademacher_norm_integrable a r P hmom
  have hfixed (y : Fin b → EuclideanSpace ℝ (Fin r)) :
      Integrable (fun ω : (Fin a → EuclideanSpace ℝ (Fin r)) × Signs a =>
        ∑ j, |inner ℝ (∑ i, sgn (ω.2 i) • ω.1 i) (y j)|)
        ((Measure.pi (fun _ : Fin a => P)).prod (fairSigns a)) := by
    apply (hnorm.mul_const (∑ j, ‖y j‖)).mono' (by fun_prop)
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)),
      Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => abs_real_inner_le_norm _ _)
  have hpoint (y : Fin b → EuclideanSpace ℝ (Fin r)) :=
    fixed_group_cross_integral_le_exact_rad hContraction a b r P hmom hiso y
  simp_rw [← integral_prod _ (hfixed _)] at hpoint
  have hmono := integral_mono (twoGroupCrossMax_joint_integrable a b r P hmom).integral_prod_left
    (((signingNormMax_integrable b r P hmom).const_mul (a : ℝ)).add
      (hI.integral_prod_right.const_mul 4)) hpoint
  simp only [Pi.add_apply] at hmono
  rw [integral_add ((signingNormMax_integrable b r P hmom).const_mul (a : ℝ))
    (hI.integral_prod_right.const_mul 4), integral_const_mul, integral_const_mul] at hmono
  have hrad := independent_group_rad_projection_integral_le a b r P hmom hiso
  nlinarith

/-- [ Finite classes of unit directions obey the uncentered isotropic projection bound.](goal) Under [the stated conditions](hyp:hContraction,hmom,hiso,hu). -/
-- @node: finite_unit_projection_sum_integral_le
lemma finite_unit_projection_sum_integral_le {ι : Type} [Finite ι] [Nonempty ι]
    (hContraction : ClassicalRademacherContraction)
    (n r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P)
    (hiso : ∀ h k, (∫ v, v h * v k ∂P) = if h = k then 1 else 0)
    (u : ι → EuclideanSpace ℝ (Fin r)) (hu : ∀ a, ‖u a‖ ≤ 1) :
    (∫ x : Fin n → EuclideanSpace ℝ (Fin r), ⨆ a, ∑ i, |inner ℝ (u a) (x i)|
      ∂Measure.pi (fun _ : Fin n => P)) ≤ n + 4 * Real.sqrt ((n : ℝ) * r) := by
  have hC := finiteCenteredSumSup_integrable P (fun a v => |inner ℝ (u a) v|)
    (by intro a; fun_prop) (fun a => isotropic_abs_projection_integrable r P hmom (u a)) n
  have hL : Integrable (fun x : Fin n → EuclideanSpace ℝ (Fin r) =>
      ⨆ a, ∑ i, |inner ℝ (u a) (x i)|) (Measure.pi (fun _ : Fin n => P)) := by
    have h := finite_abs_sup_integrable (Measure.pi (fun _ : Fin n => P))
      (fun a x => ∑ i, |inner ℝ (u a) (x i)|) (by intro a; fun_prop)
      (fun a => integrable_finsetSum _ (fun i _ =>
        (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable
          (isotropic_abs_projection_integrable r P hmom (u a))))
    have he (x : Fin n → EuclideanSpace ℝ (Fin r)) (a : ι) :
        |(∑ i, |inner ℝ (u a) (x i)|)| = ∑ i, |inner ℝ (u a) (x i)| :=
      abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    simpa only [he] using h
  have hmono := integral_mono hL ((integrable_const (n : ℝ)).add hC)
    (by intro x; simpa using finite_projection_sum_le_centered n r P hmom hiso u hu x)
  simp only [Pi.add_apply] at hmono
  rw [integral_add (integrable_const _) hC, integral_const] at hmono
  simp only [probReal_univ, one_smul] at hmono
  have hc := finite_projection_centered_integral_le hContraction n r P hmom hiso
    u (R := 1) (by norm_num) hu
  simpa only [mul_one] using hmono.trans (add_le_add (le_refl (n : ℝ)) hc)

/-- [ A finite net of unit directions approximates the signed norm maximum uniformly
on every sample, with an error controlled by the sum of row norms.](goal) Under [the stated conditions](hyp:hnet). -/
-- @node: signingNormMax_le_finite_net
lemma signingNormMax_le_finite_net {n r : ℕ} {ι : Type} [Finite ι] [Nonempty ι]
    (u : ι → EuclideanSpace ℝ (Fin r)) {ε : ℝ}
    (hnet : ∀ v : EuclideanSpace ℝ (Fin r), ‖v‖ ≤ 1 → ∃ a, ‖v - u a‖ ≤ ε)
    (x : Fin n → EuclideanSpace ℝ (Fin r)) :
    signingNormMax x ≤ (⨆ a, ∑ i, |inner ℝ (u a) (x i)|) + ε * ∑ i, ‖x i‖ := by
  letI : Nonempty {v : EuclideanSpace ℝ (Fin r) // ‖v‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  rw [signingNormMax_eq_unit_projection_sum]
  apply ciSup_le
  intro v
  obtain ⟨a, ha⟩ := hnet v.val v.property
  have hpoint (i : Fin n) :
      |inner ℝ v.val (x i)| ≤ |inner ℝ (u a) (x i)| + ε * ‖x i‖ := by
    have hinner := abs_real_inner_le_norm (v.val - u a) (x i)
    have hmul := mul_le_mul_of_nonneg_right ha (norm_nonneg (x i))
    have ht := abs_add_le (inner ℝ (u a) (x i)) (inner ℝ (v.val - u a) (x i))
    rw [inner_sub_left] at ht hinner
    have he : inner ℝ (u a) (x i) + (inner ℝ v.val (x i) - inner ℝ (u a) (x i)) =
        inner ℝ v.val (x i) := by ring
    rw [he] at ht
    linarith
  calc
    _ ≤ ∑ i, (|inner ℝ (u a) (x i)| + ε * ‖x i‖) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (∑ i, |inner ℝ (u a) (x i)|) + ε * ∑ i, ‖x i‖ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add (le_ciSup (Finite.bddAbove_range
      (fun a => ∑ i, |inner ℝ (u a) (x i)|)) a) (le_refl _)

/-- [ Compact unit-ball approximation passes finite-class symmetrization and
contraction to the expected maximum signed norm, with no extra moment assumption.](goal) Under [the stated conditions](hyp:hContraction,hmom,hiso). -/
-- @node: isotropic_signingNormMax_integral_le
lemma isotropic_signingNormMax_integral_le (hContraction : ClassicalRademacherContraction)
    (n r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P)
    (hiso : ∀ h k, (∫ v, v h * v k ∂P) = if h = k then 1 else 0) :
    (∫ x : Fin n → EuclideanSpace ℝ (Fin r), signingNormMax x
      ∂Measure.pi (fun _ : Fin n => P)) ≤ n + 4 * Real.sqrt ((n : ℝ) * r) := by
  classical
  have hn : Integrable (fun v : EuclideanSpace ℝ (Fin r) => ‖v‖) P :=
    ((memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (isotropic_norm_sq_integrable r P hmom)).integrable (by norm_num)
  have hs : Integrable (fun x : Fin n → EuclideanSpace ℝ (Fin r) => ∑ i, ‖x i‖)
      (Measure.pi (fun _ : Fin n => P)) := integrable_finsetSum _ (fun i _ =>
    (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable hn)
  let A := ∫ x : Fin n → EuclideanSpace ℝ (Fin r), ∑ i, ‖x i‖
    ∂Measure.pi (fun _ : Fin n => P)
  have hA : 0 ≤ A := integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => norm_nonneg _))
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := δ / (A + 1)
  have hε : 0 < ε := div_pos hδ (by linarith)
  obtain ⟨t, ht, htfin, hcover⟩ := (isCompact_closedBall
    (0 : EuclideanSpace ℝ (Fin r)) 1).finite_cover_balls hε
  have hzero : (0 : EuclideanSpace ℝ (Fin r)) ∈ Metric.closedBall 0 1 := by simp
  obtain ⟨v, hvt, hv⟩ := Set.mem_iUnion₂.mp (hcover hzero)
  letI : Finite t := htfin.to_subtype
  letI : Nonempty t := ⟨⟨v, hvt⟩⟩
  have hu (a : t) : ‖a.val‖ ≤ 1 := by simpa using ht a.property
  have hnet (v : EuclideanSpace ℝ (Fin r)) (hv : ‖v‖ ≤ 1) :
      ∃ a : t, ‖v - a.val‖ ≤ ε := by
    have hv' : v ∈ Metric.closedBall 0 1 := by simpa using hv
    obtain ⟨a, hat, ha⟩ := Set.mem_iUnion₂.mp (hcover hv')
    refine ⟨⟨a, hat⟩, ?_⟩
    exact le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using ha)
  have hL : Integrable (fun x : Fin n → EuclideanSpace ℝ (Fin r) =>
      ⨆ a : t, ∑ i, |inner ℝ a.val (x i)|) (Measure.pi (fun _ : Fin n => P)) := by
    have h := finite_abs_sup_integrable (Measure.pi (fun _ : Fin n => P))
      (fun (a : t) x => ∑ i, |inner ℝ a.val (x i)|) (by intro a; fun_prop)
      (fun a => integrable_finsetSum _ (fun i _ =>
        (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable
          (isotropic_abs_projection_integrable r P hmom a.val)))
    have he (x : Fin n → EuclideanSpace ℝ (Fin r)) (a : t) :
        |(∑ i, |inner ℝ a.val (x i)|)| = ∑ i, |inner ℝ a.val (x i)| :=
      abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    simpa only [he] using h
  have hmono := integral_mono (signingNormMax_integrable n r P hmom)
    (hL.add (hs.const_mul ε)) (signingNormMax_le_finite_net (fun a : t => a.val) hnet)
  simp only [Pi.add_apply] at hmono
  rw [integral_add hL (hs.const_mul ε), integral_const_mul] at hmono
  have hfinite := finite_unit_projection_sum_integral_le hContraction n r P hmom hiso
    (fun a : t => a.val) hu
  have herr : ε * A ≤ δ := by
    dsimp [ε]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by linarith : 0 < A + 1)).2
    nlinarith
  change _ ≤ _ + ε * A at hmono
  linarith

/-- [ The two independent groups satisfy the roadmap's explicit cross bound.](goal) Under [the stated conditions](hyp:hContraction,hmom,hiso). -/
-- @node: independent_group_cross_integral_le_explicit
lemma independent_group_cross_integral_le_explicit (hContraction : ClassicalRademacherContraction)
    (a b r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P)
    (hiso : ∀ h k, (∫ v, v h * v k ∂P) = if h = k then 1 else 0) :
    (∫ y : Fin b → EuclideanSpace ℝ (Fin r),
      ∫ x : Fin a → EuclideanSpace ℝ (Fin r), twoGroupCrossMax x y
        ∂Measure.pi (fun _ : Fin a => P) ∂Measure.pi (fun _ : Fin b => P)) ≤
      (a : ℝ) * b + 4 * a * Real.sqrt ((b : ℝ) * r) +
        4 * b * Real.sqrt ((a : ℝ) * r) := by
  have hcross := independent_group_cross_integral_le hContraction a b r P hmom hiso
  have hnorm := isotropic_signingNormMax_integral_le hContraction b r P hmom hiso
  have hmul := mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  nlinarith

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
