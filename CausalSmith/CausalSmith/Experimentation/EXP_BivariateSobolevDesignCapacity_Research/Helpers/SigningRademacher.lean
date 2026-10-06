module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.IsotropicSigning

/-! # Rademacher moments for isotropic signing

Independent fair signs cancel every off-diagonal term without centering the row law.
The resulting exact second moment gives the square-root first-moment estimate used
by the symmetrization and contraction roadmap. Finite projection classes satisfy the
cited contraction bound, and cross-group maxima are expressed as absolute projections.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Fair signs annihilate the entire off-diagonal form for deterministic rows.](goal) -/
-- @node: signingOffDiagonal_fair_integral_zero
lemma signingOffDiagonal_fair_integral_zero {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) :
    (∫ z, signingOffDiagonal vs z ∂fairSigns n) = 0 := by
  classical
  let := fairSigns_probability n
  unfold signingOffDiagonal
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simp only [if_neg hij]
    rw [integral_mul_const, fairSigns_distinct_product_mean_zero n i j hij, zero_mul]

/-- [ The fair-sign second moment is precisely the deterministic diagonal energy.](goal) -/
-- @node: signing_fair_norm_sq_integral
lemma signing_fair_norm_sq_integral {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) :
    (∫ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ^ 2 ∂fairSigns n) =
      ∑ i, ‖vs i‖ ^ 2 := by
  let := fairSigns_probability n
  simp_rw [signing_norm_sq_eq_diagonal_add]
  rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
    signingOffDiagonal_fair_integral_zero]
  simp

/-- [ The fair-sign first moment is bounded by the square root of diagonal energy.](goal) -/
-- @node: signing_fair_norm_integral_le
lemma signing_fair_norm_integral_le {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) :
    (∫ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ∂fairSigns n) ≤
      Real.sqrt (∑ i, ‖vs i‖ ^ 2) := by
  let := fairSigns_probability n
  have hp : MemLp (fun z : Signs n => ‖∑ i, sgn (z i) • vs i‖) 2 (fairSigns n) :=
    (memLp_two_iff_integrable_sq (measurable_of_finite _).aestronglyMeasurable).mpr
      Integrable.of_finite
  have hv := variance_nonneg (X := fun z : Signs n => ‖∑ i, sgn (z i) • vs i‖)
    (μ := fairSigns n)
  rw [variance_eq_sub hp] at hv
  simp only [Pi.pow_apply] at hv
  rw [signing_fair_norm_sq_integral] at hv
  have henergy : 0 ≤ ∑ i, ‖vs i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [Real.sqrt_nonneg (∑ i, ‖vs i‖ ^ 2), Real.sq_sqrt henergy]

/-- Averaging the exact fair-sign moment over isotropic rows gives sample size times dimension. Under [the stated conditions](hyp:hmom,hiso), [the asserted mathematical result follows](goal). -/
-- @node: isotropic_rademacher_norm_sq_integral
lemma isotropic_rademacher_norm_sq_integral (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0) :
    (∫ vs : Fin n → EuclideanSpace ℝ (Fin r),
      ∫ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ^ 2 ∂fairSigns n
        ∂Measure.pi (fun _ : Fin n => P)) = (n : ℝ) * r := by
  simp_rw [signing_fair_norm_sq_integral]
  exact isotropic_sample_diagonal_integral n r P hmom hiso

/-- [ Joint row/sign squared energy is integrable using only coordinate second moments.](goal) Under [the stated conditions](hyp:hmom). -/
-- @node: isotropic_rademacher_norm_sq_integrable
lemma isotropic_rademacher_norm_sq_integrable (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) :
    Integrable (fun ω : (Fin n → EuclideanSpace ℝ (Fin r)) × Signs n =>
      ‖∑ i, sgn (ω.2 i) • ω.1 i‖ ^ 2)
      ((Measure.pi (fun _ : Fin n => P)).prod (fairSigns n)) := by
  let := fairSigns_probability n
  apply (integrable_prod_iff (by fun_prop)).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun _ => Integrable.of_finite)
  · simp only [norm_pow, norm_norm]
    simp_rw [signing_fair_norm_sq_integral]
    exact integrable_finsetSum _ (fun i _ =>
      (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable
        (isotropic_norm_sq_integrable r P hmom))

/-- [ Joint Rademacher averaging has first moment at most the isotropic square-root scale.](goal) Under [the stated conditions](hyp:hmom,hiso). -/
-- @node: isotropic_rademacher_norm_integral_le
lemma isotropic_rademacher_norm_integral_le (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0) :
    (∫ vs : Fin n → EuclideanSpace ℝ (Fin r),
      ∫ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ∂fairSigns n
        ∂Measure.pi (fun _ : Fin n => P)) ≤ Real.sqrt ((n : ℝ) * r) := by
  let := fairSigns_probability n
  let Q := (Measure.pi (fun _ : Fin n => P)).prod (fairSigns n)
  let f := fun ω : (Fin n → EuclideanSpace ℝ (Fin r)) × Signs n =>
    ‖∑ i, sgn (ω.2 i) • ω.1 i‖
  have hp : MemLp f 2 Q := (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    (isotropic_rademacher_norm_sq_integrable n r P hmom)
  have hv := variance_nonneg (X := f) (μ := Q)
  rw [variance_eq_sub hp] at hv
  have hsecond : (∫ ω, f ω ^ 2 ∂Q) = (n : ℝ) * r := by
    rw [integral_prod _ (isotropic_rademacher_norm_sq_integrable n r P hmom)]
    exact isotropic_rademacher_norm_sq_integral n r P hmom hiso
  simp only [Pi.pow_apply] at hv
  rw [hsecond] at hv
  have hfirst : (∫ ω, f ω ∂Q) ≤ Real.sqrt ((n : ℝ) * r) := by
    nlinarith [Real.sqrt_nonneg ((n : ℝ) * r),
      Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg r))]
  rw [integral_prod _ (hp.integrable (by norm_num))] at hfirst
  exact hfirst

/-- [ A finite function class is its own countable pointwise-dense subclass.](goal) Under [the stated conditions](hyp:hG). -/
-- @node: finite_pointwiseSeparable
lemma finite_pointwiseSeparable {S : Type} {G : Set (S → ℝ)} (hG : G.Finite) :
    PointwiseSeparable G := by
  refine ⟨G, hG.countable, subset_rfl, ?_⟩
  intro g hg xs ε hε
  exact ⟨g, hg, fun x _ => by simpa using hε⟩

/-- [ Linear projections in a bounded direction class are controlled by the random signed norm.](goal) Under [the stated conditions](hyp:hmom,hiso,hR,hu). -/
-- @node: projection_radAverage_id_le
lemma projection_radAverage_id_le (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0)
    {ι : Type} (u : ι → EuclideanSpace ℝ (Fin r)) {R : ℝ} (hR : 0 ≤ R)
    (hu : ∀ a, ‖u a‖ ≤ R) :
    radAverage P n (range (fun a => fun v => inner ℝ (u a) v)) id ≤
      ENNReal.ofReal (R * Real.sqrt ((n : ℝ) * r)) := by
  let := fairSigns_probability n
  let Q := (Measure.pi (fun _ : Fin n => P)).prod (fairSigns n)
  let f := fun ω : (Fin n → EuclideanSpace ℝ (Fin r)) × Signs n =>
    ‖∑ i, sgn (ω.2 i) • ω.1 i‖
  have hp : MemLp f 2 Q := (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    (isotropic_rademacher_norm_sq_integrable n r P hmom)
  have hf : Integrable f Q := hp.integrable (by norm_num)
  have hpoint (vs : Fin n → EuclideanSpace ℝ (Fin r)) (z : Signs n) :
      (⨆ g : range (fun a => fun v => inner ℝ (u a) v),
        ENNReal.ofReal |∑ i, sgn (z i) * id (g.val (vs i))|) ≤
      ENNReal.ofReal (R * ‖∑ i, sgn (z i) • vs i‖) := by
    apply iSup_le
    intro g
    obtain ⟨a, ha⟩ := g.property
    rw [← ha]
    simp only [id_eq, ← real_inner_smul_right, ← inner_sum]
    exact ENNReal.ofReal_le_ofReal ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hu a) (norm_nonneg _)))
  calc
    radAverage P n (range (fun a => fun v => inner ℝ (u a) v)) id ≤
        ∫⁻ vs : Fin n → EuclideanSpace ℝ (Fin r),
          ∫⁻ z : Signs n, ENNReal.ofReal (R * ‖∑ i, sgn (z i) • vs i‖)
            ∂fairSigns n ∂Measure.pi (fun _ : Fin n => P) :=
      lintegral_mono (fun vs => lintegral_mono (hpoint vs))
    _ = ENNReal.ofReal (R * ∫ ω, f ω ∂Q) := by
      rw [← lintegral_prod (fun ω : (Fin n → EuclideanSpace ℝ (Fin r)) × Signs n =>
          ENNReal.ofReal (R * f ω)) (by fun_prop),
        ← ofReal_integral_eq_lintegral_ofReal (hf.const_mul R)
          (Filter.Eventually.of_forall (fun ω => mul_nonneg hR (norm_nonneg _))),
        integral_const_mul]
    _ ≤ ENNReal.ofReal (R * Real.sqrt ((n : ℝ) * r)) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hR
      rw [integral_prod _ hf]
      exact isotropic_rademacher_norm_integral_le n r P hmom hiso

/-- [ The cited factor-two contraction applies to every finite bounded projection family.
This is the deterministic class used after conditioning on the other row group.](goal) Under [the stated conditions](hyp:hContraction,hmom,hiso,hR,hu). -/
-- @node: finite_projection_abs_contraction
lemma finite_projection_abs_contraction (hContraction : ClassicalRademacherContraction)
    (n r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0)
    {ι : Type} [Finite ι] (u : ι → EuclideanSpace ℝ (Fin r))
    {R : ℝ} (hR : 0 ≤ R) (hu : ∀ a, ‖u a‖ ≤ R) :
    radAverage P n (range (fun a => fun v => inner ℝ (u a) v)) abs ≤
      2 * ENNReal.ofReal (R * Real.sqrt ((n : ℝ) * r)) := by
  have hnorm : Integrable (fun v : EuclideanSpace ℝ (Fin r) => ‖v‖) P :=
    ((memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (isotropic_norm_sq_integrable r P hmom)).integrable (by norm_num)
  have hgate := hContraction (EuclideanSpace ℝ (Fin r)) P inferInstance n
    (range (fun a => fun v => inner ℝ (u a) v))
    (finite_pointwiseSeparable (finite_range _))
    (by rintro g ⟨a, rfl⟩; fun_prop)
    ⟨fun v => R * ‖v‖, hnorm.const_mul R, Filter.Eventually.of_forall (by
      intro v g hg
      obtain ⟨a, rfl⟩ := hg
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hu a) (norm_nonneg _)))⟩
    abs (by
      convert (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)) using 1 <;>
        rfl) (abs_zero)
  exact hgate.trans (mul_le_mul_right (projection_radAverage_id_le n r P hmom hiso u hR hu) 2)

/-- Signs chosen according to a fixed projection attain the sum of absolute projections. [The asserted mathematical result follows](goal). -/
-- @node: signing_projection_max_eq_sum_abs
lemma signing_projection_max_eq_sum_abs {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) (u : EuclideanSpace ℝ (Fin r)) :
    (⨆ z : Signs n, |inner ℝ u (∑ i, sgn (z i) • vs i)|) =
      ∑ i, |inner ℝ u (vs i)| := by
  classical
  apply le_antisymm
  · apply ciSup_le
    intro z
    simp only [inner_sum, real_inner_smul_right]
    calc
      |∑ i, sgn (z i) * inner ℝ u (vs i)| ≤
          ∑ i, |sgn (z i) * inner ℝ u (vs i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |inner ℝ u (vs i)| := by
        apply Finset.sum_congr rfl
        intro i _
        cases z i <;> simp [sgn]
  · let z : Signs n := fun i => decide (0 ≤ inner ℝ u (vs i))
    have he : inner ℝ u (∑ i, sgn (z i) • vs i) =
        ∑ i, |inner ℝ u (vs i)| := by
      simp only [inner_sum, real_inner_smul_right]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : 0 ≤ inner ℝ u (vs i)
      · simp [z, hi, sgn, abs_of_nonneg hi]
      · simp [z, hi, sgn, abs_of_neg (lt_of_not_ge hi)]
    have h := le_ciSup (Finite.bddAbove_range
      (fun z : Signs n => |inner ℝ u (∑ i, sgn (z i) • vs i)|)) z
    rwa [he, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))] at h

/-- [ Maximum norm over all signings of deterministic rows. -/
-- @node: signingNormMax
def signingNormMax {n r : ℕ} (vs : Fin n → EuclideanSpace ℝ (Fin r)) : ℝ :=
  ⨆ z : Signs n, ‖∑ i, sgn (z i) • vs i‖

/-- Every signed norm is at most the finite maximum.](goal) This uses [the stated conclusion](goal). -/
-- @node: signing_norm_le_max
lemma signing_norm_le_max {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) (z : Signs n) :
    ‖∑ i, sgn (z i) • vs i‖ ≤ signingNormMax vs :=
  le_ciSup (Finite.bddAbove_range (fun z : Signs n => ‖∑ i, sgn (z i) • vs i‖)) z

/-- [ The maximum signed norm is nonnegative, including the empty sample.](goal) -/
-- @node: signingNormMax_nonneg
lemma signingNormMax_nonneg {n r : ℕ} (vs : Fin n → EuclideanSpace ℝ (Fin r)) :
    0 ≤ signingNormMax vs :=
  (norm_nonneg _).trans (signing_norm_le_max vs (fun _ => true))

/-- [ The sum of row lengths is a common envelope for all signed norms.](goal) -/
-- @node: signingNormMax_le_sum_norm
lemma signingNormMax_le_sum_norm {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) :
    signingNormMax vs ≤ ∑ i, ‖vs i‖ := by
  apply ciSup_le
  intro z
  calc
    ‖∑ i, sgn (z i) • vs i‖ ≤ ∑ i, ‖sgn (z i) • vs i‖ := norm_sum_le _ _
    _ = ∑ i, ‖vs i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      cases z i <;> simp [sgn]

/-- The finite signed-norm maximum is Borel. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: signingNormMax_measurable
lemma signingNormMax_measurable (n r : ℕ) :
    Measurable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) => signingNormMax vs) := by
  unfold signingNormMax
  apply Measurable.iSup
  intro z
  fun_prop

/-- Coordinate second moments integrate the signed-norm maximum's common envelope. Under [the stated conditions](hyp:hmom), [the asserted mathematical result follows](goal). -/
-- @node: signingNormMax_integrable
lemma signingNormMax_integrable (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) :
    Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) => signingNormMax vs)
      (Measure.pi (fun _ : Fin n => P)) := by
  have hnorm : Integrable (fun v : EuclideanSpace ℝ (Fin r) => ‖v‖) P :=
    ((memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (isotropic_norm_sq_integrable r P hmom)).integrable (by norm_num)
  have hsum : Integrable (fun vs : Fin n → EuclideanSpace ℝ (Fin r) => ∑ i, ‖vs i‖)
      (Measure.pi (fun _ : Fin n => P)) :=
    integrable_finsetSum _ (fun i _ =>
      (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable hnorm)
  apply hsum.mono' (signingNormMax_measurable n r).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro vs
  rw [Real.norm_eq_abs, abs_of_nonneg (signingNormMax_nonneg vs)]
  exact signingNormMax_le_sum_norm vs

/-- [ The conditional finite class of all signed sums satisfies the contraction bound.](goal) Under [the stated conditions](hyp:hContraction,hmom,hiso). -/
-- @node: signed_sum_projection_abs_contraction
lemma signed_sum_projection_abs_contraction (hContraction : ClassicalRademacherContraction)
    (a b r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P)
    (hiso : ∀ h k, (∫ v, v h * v k ∂P) = if h = k then 1 else 0)
    (vs : Fin b → EuclideanSpace ℝ (Fin r)) :
    radAverage P a (range (fun z : Signs b => fun v =>
      inner ℝ (∑ j, sgn (z j) • vs j) v)) abs ≤
      2 * ENNReal.ofReal (signingNormMax vs * Real.sqrt ((a : ℝ) * r)) := by
  exact finite_projection_abs_contraction hContraction a r P hmom hiso
    (fun z : Signs b => ∑ j, sgn (z j) • vs j) (signingNormMax_nonneg vs)
      (signing_norm_le_max vs)

/-- Disjoint groups allow their signs to be optimized independently, even though the
original cross form uses a single signing of all rows. [The asserted mathematical result follows](goal). -/
-- @node: signingPartitionCrossMax_eq_two_signings
lemma signingPartitionCrossMax_eq_two_signings {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) (η : Signs n) :
    signingPartitionCrossMax vs η =
      ⨆ w : Signs n, ⨆ z : Signs n,
        |inner ℝ (∑ i, if η i = true then sgn (z i) • vs i else 0)
          (∑ j, if η j = false then sgn (w j) • vs j else 0)| := by
  classical
  apply le_antisymm
  · apply ciSup_le
    intro z
    rw [signingPartitionCross_eq_inner]
    let H (w q : Signs n) : ℝ :=
      |inner ℝ (∑ i, if η i = true then sgn (q i) • vs i else 0)
        (∑ j, if η j = false then sgn (w j) • vs j else 0)|
    have h1 : H z z ≤ ⨆ q : Signs n, H z q :=
      le_ciSup (Finite.bddAbove_range (H z)) z
    have h2 : (⨆ q : Signs n, H z q) ≤ ⨆ w : Signs n, ⨆ q : Signs n, H w q :=
      le_ciSup (Finite.bddAbove_range (fun w : Signs n => ⨆ q : Signs n, H w q)) z
    exact h1.trans h2
  · apply ciSup_le
    intro w
    apply ciSup_le
    intro z
    let q : Signs n := fun i => if η i = true then z i else w i
    have hleft : (∑ i, if η i = true then sgn (q i) • vs i else 0) =
        ∑ i, if η i = true then sgn (z i) • vs i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases hη : η i <;> simp [q, hη]
    have hright : (∑ i, if η i = false then sgn (q i) • vs i else 0) =
        ∑ i, if η i = false then sgn (w i) • vs i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases hη : η i <;> simp [q, hη]
    have h := le_ciSup (Finite.bddAbove_range
      (fun q : Signs n => |signingPartitionCross vs q η|)) q
    rwa [signingPartitionCross_eq_inner, hleft, hright] at h

/-- [ Conditional on the complementary group, the cross-group maximum is exactly a
finite supremum of sums of absolute projections, as in the proof roadmap.](goal) -/
-- @node: signingPartitionCrossMax_eq_projection_sum
lemma signingPartitionCrossMax_eq_projection_sum {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) (η : Signs n) :
    signingPartitionCrossMax vs η =
      ⨆ w : Signs n, ∑ i, if η i = true then
        |inner ℝ (vs i) (∑ j, if η j = false then sgn (w j) • vs j else 0)| else 0 := by
  classical
  rw [signingPartitionCrossMax_eq_two_signings]
  congr 1
  funext w
  have h := signing_projection_max_eq_sum_abs
    (fun i => if η i = true then vs i else 0)
    (∑ j, if η j = false then sgn (w j) • vs j else 0)
  simp only [smul_ite, smul_zero, real_inner_comm] at h ⊢
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [*]

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
