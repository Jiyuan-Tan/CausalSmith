module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.SigningDuality
public import Causalean.Stat.EmpiricalProcess.Countable.ProductSwap

/-! # First-moment symmetrization for finite projection classes

The row-signing roadmap introduces an independent ghost sample, exchanges
paired observations with fair signs, and uses the triangle inequality before
contraction. These comparisons need only integrability of the finite class;
no boundedness or higher moments are imposed.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ A finite absolute supremum is integrable if each measurable member is integrable.](goal) Under [the stated conditions](hyp:hm,hi). -/
-- @node: finite_abs_sup_integrable
lemma finite_abs_sup_integrable {Ω ι : Type} [MeasurableSpace Ω]
    [Finite ι] [Nonempty ι] (μ : Measure Ω) (f : ι → Ω → ℝ)
    (hm : ∀ a, Measurable (f a)) (hi : ∀ a, Integrable (f a) μ) :
    Integrable (fun x => ⨆ a, |f a x|) μ := by
  classical
  let := Fintype.ofFinite ι
  have hs : Integrable (fun x => ∑ a, |f a x|) μ :=
    integrable_finsetSum _ (fun a _ => (hi a).abs)
  apply hs.mono' (Measurable.iSup (fun a => (hm a).abs)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hn : 0 ≤ ⨆ a, |f a x| :=
    (abs_nonneg (f (Classical.choice (inferInstance : Nonempty ι)) x)).trans
      (le_ciSup (Finite.bddAbove_range (fun a => |f a x|)) _)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  apply ciSup_le
  intro a
  exact Finset.single_le_sum (fun b _ => abs_nonneg (f b x)) (Finset.mem_univ a)

/-- [ Largest population-centered sum over a deterministic finite class. -/
-- @node: finiteCenteredSumSup
def finiteCenteredSumSup {Ω ι : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ι → Ω → ℝ) {n : ℕ} (x : Fin n → Ω) : ℝ :=
  ⨆ a, |∑ i, (f a (x i) - ∫ v, f a v ∂μ)|

/-- Largest two-copy empirical difference over a deterministic finite class. -/
-- @node: finiteGhostSumSup
def finiteGhostSumSup {Ω ι : Type} (f : ι → Ω → ℝ) {n : ℕ}
    (x y : Fin n → Ω) : ℝ :=
  ⨆ a, |∑ i, (f a (x i) - f a (y i))|

/-- Largest signed empirical sum over a deterministic finite class. -/
-- @node: finiteRadSumSup
def finiteRadSumSup {Ω ι : Type} (f : ι → Ω → ℝ) {n : ℕ}
    (x : Fin n → Ω) (z : Signs n) : ℝ :=
  ⨆ a, |∑ i, sgn (z i) * f a (x i)|

variable {Ω ι : Type} [MeasurableSpace Ω] [Finite ι] [Nonempty ι]

/-- Centered empirical sums have an integrable finite supremum under the iid law.](goal) Under [the stated conditions](hyp:hm,hi). This uses [the stated conclusion](goal). -/
-- @node: finiteCenteredSumSup_integrable
lemma finiteCenteredSumSup_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ι → Ω → ℝ) (hm : ∀ a, Measurable (f a))
    (hi : ∀ a, Integrable (f a) μ) (n : ℕ) :
    Integrable (finiteCenteredSumSup μ f (n := n)) (Measure.pi (fun _ : Fin n => μ)) := by
  apply finite_abs_sup_integrable
  · intro a; fun_prop
  · intro a
    exact integrable_finsetSum _ (fun i _ =>
      (integrable_comp_eval (hi a)).sub (integrable_const _))

/-- [ Ghost differences have an integrable finite supremum under the two-copy law.](goal) Under [the stated conditions](hyp:hm,hi). -/
-- @node: finiteGhostSumSup_integrable
lemma finiteGhostSumSup_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ι → Ω → ℝ) (hm : ∀ a, Measurable (f a))
    (hi : ∀ a, Integrable (f a) μ) (n : ℕ) :
    Integrable (fun p : (Fin n → Ω) × (Fin n → Ω) => finiteGhostSumSup f p.1 p.2)
      ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ))) := by
  apply finite_abs_sup_integrable
  · intro a; fun_prop
  · intro a
    exact integrable_finsetSum _ (fun i _ =>
      ((integrable_comp_eval (μ := fun _ : Fin n => μ) (i := i) (hi a)).comp_fst _).sub
        ((integrable_comp_eval (μ := fun _ : Fin n => μ) (i := i) (hi a)).comp_snd _))

/-- [ Each fixed-sign empirical supremum is integrable under the iid law.](goal) Under [the stated conditions](hyp:hm,hi). -/
-- @node: finiteRadSumSup_integrable
lemma finiteRadSumSup_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ι → Ω → ℝ) (hm : ∀ a, Measurable (f a))
    (hi : ∀ a, Integrable (f a) μ) (n : ℕ) (z : Signs n) :
    Integrable (fun x : Fin n → Ω => finiteRadSumSup f x z)
      (Measure.pi (fun _ : Fin n => μ)) := by
  apply finite_abs_sup_integrable
  · intro a; fun_prop
  · intro a
    exact integrable_finsetSum _ (fun i _ => (integrable_comp_eval (hi a)).const_mul _)

omit [Finite ι] [Nonempty ι] in
/-- [ A centered empirical sum is exactly the expectation of its ghost difference.](goal) Under [the stated conditions](hyp:hi). -/
-- @node: finite_centered_sum_eq_ghost_integral
lemma finite_centered_sum_eq_ghost_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ι → Ω → ℝ) (hi : ∀ a, Integrable (f a) μ)
    {n : ℕ} (x : Fin n → Ω) (a : ι) :
    (∑ i, (f a (x i) - ∫ v, f a v ∂μ)) =
      ∫ y : Fin n → Ω, ∑ i, (f a (x i) - f a (y i))
        ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_finsetSum (f := fun (i : Fin n) (y : Fin n → Ω) => f a (x i) - f a (y i))
    Finset.univ (fun i _ =>
    (integrable_const _).sub (integrable_comp_eval (μ := fun _ : Fin n => μ) (i := i) (hi a)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_sub (integrable_const _) (integrable_comp_eval (hi a)),
    integral_comp_eval (hi a).aestronglyMeasurable]
  simp

/-- [ Conditional Jensen compares the centered supremum to an independent ghost sample.](goal) Under [the stated conditions](hyp:hm,hi). -/
-- @node: finiteCenteredSumSup_le_ghost_integral
lemma finiteCenteredSumSup_le_ghost_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ι → Ω → ℝ) (hm : ∀ a, Measurable (f a))
    (hi : ∀ a, Integrable (f a) μ) {n : ℕ} (x : Fin n → Ω) :
    finiteCenteredSumSup μ f x ≤
      ∫ y : Fin n → Ω, finiteGhostSumSup f x y ∂Measure.pi (fun _ : Fin n => μ) := by
  have hG : Integrable (fun y : Fin n → Ω => finiteGhostSumSup f x y)
      (Measure.pi (fun _ : Fin n => μ)) := by
    apply finite_abs_sup_integrable
    · intro a; fun_prop
    · intro a
      exact integrable_finsetSum _ (fun i _ =>
        (integrable_const _).sub (integrable_comp_eval (hi a)))
  apply ciSup_le
  intro a
  have hg : Integrable (fun y : Fin n → Ω => ∑ i, (f a (x i) - f a (y i)))
      (Measure.pi (fun _ : Fin n => μ)) :=
    integrable_finsetSum _ (fun i _ =>
      (integrable_const _).sub (integrable_comp_eval (hi a)))
  rw [finite_centered_sum_eq_ghost_integral μ f hi]
  calc
    _ ≤ ∫ y : Fin n → Ω, |∑ i, (f a (x i) - f a (y i))|
        ∂Measure.pi (fun _ : Fin n => μ) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun y : Fin n → Ω => ∑ i, (f a (x i) - f a (y i)))
    _ ≤ _ := integral_mono hg.abs hG (fun y =>
      le_ciSup (Finite.bddAbove_range (fun a => |∑ i, (f a (x i) - f a (y i))|)) a)

omit [Finite ι] [Nonempty ι] in
/-- Paired-coordinate exchange turns each ghost difference into its fixed-sign version. [The asserted mathematical result follows](goal). -/
-- @node: finiteGhostSumSup_swap_eq
lemma finiteGhostSumSup_swap_eq (f : ι → Ω → ℝ) {n : ℕ} (z : Signs n)
    (p : (Fin n → Ω) × (Fin n → Ω)) :
    finiteGhostSumSup f
      ((Causalean.Stat.EmpiricalProcess.Countable.pairedSampleSwap z p).1)
      ((Causalean.Stat.EmpiricalProcess.Countable.pairedSampleSwap z p).2) =
      ⨆ a, |∑ i, sgn (z i) * (f a (p.1 i) - f a (p.2 i))| := by
  unfold finiteGhostSumSup
  congr 1
  funext a
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases h : z i <;> simp [Causalean.Stat.EmpiricalProcess.Countable.pairedSampleSwap,
    h, sgn, sub_eq_add_neg, add_comm]

omit [MeasurableSpace Ω] in
/-- [ The signed ghost supremum is bounded by the two separate signed suprema.](goal) -/
-- @node: finite_signed_ghost_triangle
lemma finite_signed_ghost_triangle (f : ι → Ω → ℝ) {n : ℕ}
    (x y : Fin n → Ω) (z : Signs n) :
    (⨆ a, |∑ i, sgn (z i) * (f a (x i) - f a (y i))|) ≤
      finiteRadSumSup f x z + finiteRadSumSup f y z := by
  apply ciSup_le
  intro a
  simp only [mul_sub, Finset.sum_sub_distrib]
  exact (abs_sub _ _).trans (add_le_add
    (le_ciSup (Finite.bddAbove_range (fun a => |∑ i, sgn (z i) * f a (x i)|)) a)
    (le_ciSup (Finite.bddAbove_range (fun a => |∑ i, sgn (z i) * f a (y i)|)) a))

/-- The product-law symmetry and triangle inequality give the factor-two ghost bound
for every fixed signing, before taking the fair-sign average. Under [the stated conditions](hyp:hm,hi), [the asserted mathematical result follows](goal). -/
-- @node: finiteGhostSumSup_integral_le_fixed_sign
lemma finiteGhostSumSup_integral_le_fixed_sign (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ι → Ω → ℝ) (hm : ∀ a, Measurable (f a))
    (hi : ∀ a, Integrable (f a) μ) (n : ℕ) (z : Signs n) :
    (∫ p : (Fin n → Ω) × (Fin n → Ω), finiteGhostSumSup f p.1 p.2
      ∂((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ)))) ≤
      2 * ∫ x : Fin n → Ω, finiteRadSumSup f x z ∂Measure.pi (fun _ : Fin n => μ) := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  have hswap := Causalean.Stat.EmpiricalProcess.Countable.pairedSampleSwap_measurePreserving μ z
  have hG := finiteGhostSumSup_integrable μ f hm hi n
  have hR := finiteRadSumSup_integrable μ f hm hi n z
  rw [← hswap.integral_comp' (fun p => finiteGhostSumSup f p.1 p.2)]
  simp_rw [finiteGhostSumSup_swap_eq]
  calc
    _ ≤ ∫ p : (Fin n → Ω) × (Fin n → Ω),
        finiteRadSumSup f p.1 z + finiteRadSumSup f p.2 z ∂ν.prod ν := by
      apply integral_mono
      · simpa only [Function.comp_def, finiteGhostSumSup_swap_eq] using
          hswap.integrable_comp_of_integrable hG
      · exact (hR.comp_fst ν).add (hR.comp_snd ν)
      · intro p; exact finite_signed_ghost_triangle f p.1 p.2 z
    _ = _ := by
      rw [integral_add (hR.comp_fst ν) (hR.comp_snd ν),
        integral_fun_fst (fun x => finiteRadSumSup f x z),
        integral_fun_snd (fun x => finiteRadSumSup f x z)]
      simp only [probReal_univ, one_smul]
      ring

/-- [ The fair-sign empirical supremum is jointly integrable under sample and sign laws.](goal) Under [the stated conditions](hyp:hm,hi). -/
-- @node: finiteRadSumSup_joint_integrable
lemma finiteRadSumSup_joint_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ι → Ω → ℝ) (hm : ∀ a, Measurable (f a))
    (hi : ∀ a, Integrable (f a) μ) (n : ℕ) :
    Integrable (fun p : (Fin n → Ω) × Signs n => finiteRadSumSup f p.1 p.2)
      ((Measure.pi (fun _ : Fin n => μ)).prod (fairSigns n)) := by
  let := fairSigns_probability n
  apply finite_abs_sup_integrable
  · intro a; fun_prop
  · intro a
    apply integrable_finsetSum
    intro i _
    simpa only [mul_comm] using
      (integrable_comp_eval (μ := fun _ : Fin n => μ) (i := i) (hi a)).mul_prod
        (Integrable.of_finite : Integrable (fun z : Signs n => sgn (z i)) (fairSigns n))

/-- [ Averaging conditional Jensen bounds the centered expectation by the ghost expectation.](goal) Under [the stated conditions](hyp:hm,hi). -/
-- @node: finite_centered_integral_le_ghost
lemma finite_centered_integral_le_ghost (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ι → Ω → ℝ) (hm : ∀ a, Measurable (f a))
    (hi : ∀ a, Integrable (f a) μ) (n : ℕ) :
    (∫ x : Fin n → Ω, finiteCenteredSumSup μ f x ∂Measure.pi (fun _ : Fin n => μ)) ≤
      ∫ p : (Fin n → Ω) × (Fin n → Ω), finiteGhostSumSup f p.1 p.2
        ∂((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ))) := by
  have hG := finiteGhostSumSup_integrable μ f hm hi n
  rw [integral_prod _ hG]
  exact integral_mono (finiteCenteredSumSup_integrable μ f hm hi n)
    hG.integral_prod_left (fun x => finiteCenteredSumSup_le_ghost_integral μ f hm hi x)

/-- [ A finite integrable class satisfies first-moment Rademacher symmetrization
with factor two, including an empty sample.](goal) Under [the stated conditions](hyp:hm,hi). -/
-- @node: finite_first_moment_symmetrization
lemma finite_first_moment_symmetrization (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ι → Ω → ℝ) (hm : ∀ a, Measurable (f a))
    (hi : ∀ a, Integrable (f a) μ) (n : ℕ) :
    (∫ x : Fin n → Ω, finiteCenteredSumSup μ f x ∂Measure.pi (fun _ : Fin n => μ)) ≤
      2 * ∫ x : Fin n → Ω, ∫ z : Signs n, finiteRadSumSup f x z ∂fairSigns n
        ∂Measure.pi (fun _ : Fin n => μ) := by
  let := fairSigns_probability n
  have hR := finiteRadSumSup_joint_integrable μ f hm hi n
  have hfixed := finiteGhostSumSup_integral_le_fixed_sign μ f hm hi n
  have havg := integral_mono (μ := fairSigns n) (integrable_const _)
    (hR.integral_prod_right.const_mul 2) hfixed
  rw [integral_const, integral_const_mul, ← integral_integral_swap hR] at havg
  simp only [probReal_univ, one_smul] at havg
  exact (finite_centered_integral_le_ghost μ f hm hi n).trans havg

/-- Passing a finite real supremum through `ofReal` agrees with the nonnegative supremum. [The asserted mathematical result follows](goal). -/
-- @node: ofReal_finite_abs_sup
lemma ofReal_finite_abs_sup (g : ι → ℝ) :
    ENNReal.ofReal (⨆ a, |g a|) = ⨆ a, ENNReal.ofReal |g a| := by
  obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite (f := fun a => |g a|)
  apply le_antisymm
  · rw [← ha]
    exact le_iSup (fun a => ENNReal.ofReal |g a|) a
  · apply iSup_le
    intro b
    exact ENNReal.ofReal_le_ofReal (le_ciSup (Finite.bddAbove_range (fun a => |g a|)) b)

/-- The finite-class real signed supremum represents the extended-valued contraction
interface exactly, with no moment lost in the change of codomain. Under [the stated conditions](hyp:hm,hi), [the asserted mathematical result follows](goal). -/
-- @node: finiteRadSumSup_radAverage_eq
lemma finiteRadSumSup_radAverage_eq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ι → Ω → ℝ) (hm : ∀ a, Measurable (f a))
    (hi : ∀ a, Integrable (f a) μ) (n : ℕ) :
    radAverage μ n (range f) id =
      ENNReal.ofReal (∫ x : Fin n → Ω, ∫ z : Signs n, finiteRadSumSup f x z
        ∂fairSigns n ∂Measure.pi (fun _ : Fin n => μ)) := by
  let := fairSigns_probability n
  have hR := finiteRadSumSup_joint_integrable μ f hm hi n
  unfold radAverage
  simp only [id_eq]
  have he (x : Fin n → Ω) (z : Signs n) :
      (⨆ g : range f, ENNReal.ofReal |∑ i, sgn (z i) * g.val (x i)|) =
        ENNReal.ofReal (finiteRadSumSup f x z) := by
    rw [iSup_range' (fun g : Ω → ℝ => ENNReal.ofReal |∑ i, sgn (z i) * g (x i)|) f]
    exact (ofReal_finite_abs_sup (fun a => ∑ i, sgn (z i) * f a (x i))).symm
  simp_rw [he]
  rw [← lintegral_prod (fun p : (Fin n → Ω) × Signs n =>
      ENNReal.ofReal (finiteRadSumSup f p.1 p.2)) (by
        unfold finiteRadSumSup; fun_prop),
    ← ofReal_integral_eq_lintegral_ofReal hR (Filter.Eventually.of_forall (fun p => by
      obtain ⟨a⟩ := (inferInstance : Nonempty ι)
      exact (abs_nonneg _).trans (le_ciSup (Finite.bddAbove_range
        (fun a => |∑ i, sgn (p.2 i) * f a (p.1 i)|)) a))),
    integral_prod _ hR]

omit [Finite ι] [Nonempty ι] in
/-- Absolute transformation of a finite class agrees exactly with the signed
supremum used in the contraction interface. [The asserted mathematical result follows](goal). -/
-- @node: finite_radAverage_abs_eq
lemma finite_radAverage_abs_eq (μ : Measure Ω) (f : ι → Ω → ℝ) (n : ℕ) :
    radAverage μ n (range f) abs = radAverage μ n (range (fun a v => |f a v|)) id := by
  unfold radAverage
  congr 1
  funext x
  congr 1
  funext z
  rw [iSup_range' (fun g : Ω → ℝ =>
    ENNReal.ofReal |∑ i, sgn (z i) * abs (g (x i))|) f,
    iSup_range' (fun g : Ω → ℝ =>
    ENNReal.ofReal |∑ i, sgn (z i) * id (g (x i))|) (fun a v => |f a v|)]
  rfl

/-- Symmetrization followed by the cited contraction controls a finite class of
absolute functions by four times the original linear Rademacher average. Keeping
the exact average permits the subsequent independent-group isotropy argument. Under [the stated conditions](hyp:hContraction,hm,hi), [the asserted mathematical result follows](goal). -/
-- @node: finite_abs_centered_ofReal_le_contraction
lemma finite_abs_centered_ofReal_le_contraction (hContraction : ClassicalRademacherContraction)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ι → Ω → ℝ)
    (hm : ∀ a, Measurable (f a)) (hi : ∀ a, Integrable (f a) μ) (n : ℕ) :
    ENNReal.ofReal (∫ x : Fin n → Ω, finiteCenteredSumSup μ (fun a v => |f a v|) x
      ∂Measure.pi (fun _ : Fin n => μ)) ≤ 4 * radAverage μ n (range f) id := by
  classical
  let := Fintype.ofFinite ι
  have hgate := hContraction Ω μ inferInstance n (range f)
    (finite_pointwiseSeparable (finite_range _)) (by rintro g ⟨a, rfl⟩; exact hm a)
    ⟨fun v => ∑ a, |f a v|, integrable_finsetSum _ (fun a _ => (hi a).abs),
      Filter.Eventually.of_forall (by
        rintro v g ⟨a, rfl⟩
        exact Finset.single_le_sum (fun b _ => abs_nonneg (f b v)) (Finset.mem_univ a))⟩
    abs (by
      convert (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)) using 1 <;> rfl)
    abs_zero
  have hsym := ENNReal.ofReal_le_ofReal (finite_first_moment_symmetrization μ
    (fun a v => |f a v|) (fun a => (hm a).abs) (fun a => (hi a).abs) n)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← finiteRadSumSup_radAverage_eq μ (fun a v => |f a v|)
      (fun a => (hm a).abs) (fun a => (hi a).abs) n,
    ← finite_radAverage_abs_eq] at hsym
  calc
    _ ≤ 2 * radAverage μ n (range f) abs := by simpa using hsym
    _ ≤ 2 * (2 * radAverage μ n (range f) id) := mul_le_mul_right hgate 2
    _ = _ := by ring

/-- [ Absolute projections in any finite bounded direction class have expected centered
supremum at most four times its radius times the isotropic square-root scale.](goal) Under [the stated conditions](hyp:hContraction,hmom,hiso,hR,hu). -/
-- @node: finite_projection_centered_integral_le
lemma finite_projection_centered_integral_le (hContraction : ClassicalRademacherContraction)
    (n r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P)
    (hiso : ∀ h k, (∫ v, v h * v k ∂P) = if h = k then 1 else 0)
    (u : ι → EuclideanSpace ℝ (Fin r)) {R : ℝ} (hR : 0 ≤ R)
    (hu : ∀ a, ‖u a‖ ≤ R) :
    (∫ x : Fin n → EuclideanSpace ℝ (Fin r),
      finiteCenteredSumSup P (fun a v => |inner ℝ (u a) v|) x
        ∂Measure.pi (fun _ : Fin n => P)) ≤ 4 * R * Real.sqrt ((n : ℝ) * r) := by
  let f : ι → EuclideanSpace ℝ (Fin r) → ℝ := fun a v => inner ℝ (u a) v
  have hm : ∀ a, Measurable (f a) := by intro a; fun_prop
  have hi : ∀ a, Integrable (f a) P := by
    intro a
    exact ((memLp_two_iff_integrable_sq (hm a).aestronglyMeasurable).mpr
      (isotropic_projection_sq_integrable r P hmom (u a))).integrable (by norm_num)
  have hsym := finite_first_moment_symmetrization P (fun a v => |f a v|)
    (fun a => (hm a).abs) (fun a => (hi a).abs) n
  have hcontract := finite_projection_abs_contraction hContraction n r P hmom hiso u hR hu
  have heq := finite_radAverage_abs_eq P f n
  rw [heq, finiteRadSumSup_radAverage_eq P (fun a v => |f a v|)
    (fun a => (hm a).abs) (fun a => (hi a).abs) n] at hcontract
  have htwo : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
  have hrhs : 2 * ENNReal.ofReal (R * Real.sqrt ((n : ℝ) * r)) =
      ENNReal.ofReal (2 * (R * Real.sqrt ((n : ℝ) * r))) := by
    rw [htwo, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hrhs] at hcontract
  have hbound : (∫ x : Fin n → EuclideanSpace ℝ (Fin r),
      ∫ z : Signs n, finiteRadSumSup (fun a v => |f a v|) x z ∂fairSigns n
        ∂Measure.pi (fun _ : Fin n => P)) ≤ 2 * (R * Real.sqrt ((n : ℝ) * r)) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcontract
  dsimp only [f] at hsym hbound
  linarith

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
