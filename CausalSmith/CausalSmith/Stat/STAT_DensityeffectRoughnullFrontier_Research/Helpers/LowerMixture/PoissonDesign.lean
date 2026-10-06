module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.ChiSquare

/-!
Poisson averaging under the actual shared-sign null design in unit cell coordinates.
The fixed-count design is a pushforward of normalized observed laws, so validity
and normalization are proved rather than supplied as assumptions. The coefficient
bounds retain the exact singleton coefficient before outcome-sign averaging.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- A positive bounded cell tilt is an admissible one-cell null-law parameter. -/
-- @node: lower_unit_parameters
lemma lower_unit_parameters (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4)) :
    LowerParameters tau 1 1 := by
  refine ⟨ht, ⟨0, by norm_num⟩, ⟨0, by norm_num⟩, ?_⟩
  simp

/-- A single latent sign is shared by every observation of the unit-cell null law. -/
-- @node: lowerUnitNullFamily
def lowerUnitNullFamily (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (ell : Bool) : ObsLaw :=
  lowerNullLaw tau 1 1 (lower_unit_parameters tau ht) (fun _ => ell) (fun _ => false)

/-- The actual observation sample is reported as bounded bump scores and treatment flags. -/
-- @node: lowerUnitCellData
def lowerUnitCellData (m : ℕ) (o : Data m) :
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m :=
  (fun i => lowerBump (X (o i)), (fun i => A (o i)), (fun i => A (o i)))

/-- Reporting bump scores and treatment flags is measurable. -/
-- @node: measurable_lowerUnitCellData
@[fun_prop] lemma measurable_lowerUnitCellData (m : ℕ) :
    Measurable (lowerUnitCellData m) := by
  unfold lowerUnitCellData X A
  fun_prop

/-- Bump amplitudes are bounded everywhere and every selected record is treated. -/
-- @node: lowerUnitCellData_valid
lemma lowerUnitCellData_valid (m : ℕ) (o : Data m) :
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Valid (lowerUnitCellData m o) := by
  refine ⟨fun i => lowerBump_abs_le_one _, ?_⟩
  exact Finset.Subset.refl _

/-- Fixed-count null design with the shared sign averaged after iid sampling. -/
-- @node: lowerUnitCellDesign
def lowerUnitCellDesign (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4)) (m : ℕ) :
    Measure (Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m) :=
  (uniformSampleMixture m (lowerUnitNullFamily tau ht)).map (lowerUnitCellData m)

/-- The concrete null design is a probability measure at every count, including zero. -/
-- @node: lowerUnitCellDesign_probability
instance lowerUnitCellDesign_probability (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (m : ℕ) : IsProbabilityMeasure (lowerUnitCellDesign tau ht m) := by
  haveI : ∀ ell : Bool, IsProbabilityMeasure (dataLaw (lowerUnitNullFamily tau ht ell) m) :=
    fun ell => by unfold dataLaw; infer_instance
  haveI : IsProbabilityMeasure (uniformSampleMixture m (lowerUnitNullFamily tau ht)) :=
    Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability _
  exact Measure.isProbabilityMeasure_map (measurable_lowerUnitCellData m).aemeasurable

/-- The concrete null design satisfies the reusable posterior validity contract. -/
-- @node: lowerUnitCellDesign_valid
lemma lowerUnitCellDesign_valid (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4)) (m : ℕ) :
    ∀ᵐ c ∂lowerUnitCellDesign tau ht m,
      Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Valid c := by
  unfold lowerUnitCellDesign
  apply (ae_map_iff (measurable_lowerUnitCellData m).aemeasurable ?_).2
  · exact Filter.Eventually.of_forall (lowerUnitCellData_valid m)
  · unfold Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Valid
    simp only [Causalean.Stat.Minimax.Mixture.PoissonLatentSign.selected,
      Causalean.Stat.Minimax.Mixture.PoissonLatentSign.active, Finset.subset_iff,
      Finset.mem_filter, Finset.mem_univ, true_and]
    apply MeasurableSet.inter
    · have h := (MeasurableSet.iInter fun i : Fin m =>
        measurableSet_le (show Measurable (fun c :
          Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m => |c.1 i|) by fun_prop)
          (measurable_const : Measurable (fun _ => (1 : ℝ))))
      simp only [Set.iInter_setOf] at h
      convert h using 1
      apply Iff.of_eq
      apply congrArg MeasurableSet
      funext c
      rfl
    · have hi (i : Fin m) : MeasurableSet {c :
          Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m |
          c.2.2 i = true → c.2.1 i = true} := by
        have h1 : MeasurableSet {c : Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m |
            c.2.2 i = true} := measurableSet_eq_fun (by fun_prop) measurable_const
        have h2 : MeasurableSet {c : Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m |
            c.2.1 i = true} := measurableSet_eq_fun (by fun_prop) measurable_const
        convert h1.compl.union h2 using 1
        ext c
        simp [imp_iff_not_or]
      have h := MeasurableSet.iInter hi
      simp only [Set.iInter_setOf] at h
      convert h using 1
      apply Iff.of_eq
      apply congrArg MeasurableSet
      funext c
      rfl


/-- Order-d coefficient under the actual shared-sign null design and Poisson count. -/
-- @node: lowerPoissonCoefficient
def lowerPoissonCoefficient (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (xi : NNReal) (gamma : ℝ) (d : ℕ) : ℝ :=
  Causalean.Stat.Minimax.Mixture.PoissonLatentSign.coefficient
    (lowerUnitCellDesign tau ht) xi tau gamma d

/-- Coefficients are nonnegative because they average squared posterior coefficients. -/
-- @node: lowerPoissonCoefficient_nonneg
lemma lowerPoissonCoefficient_nonneg (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (xi : NNReal) (gamma : ℝ) (d : ℕ) :
    0 ≤ lowerPoissonCoefficient tau ht xi gamma d :=
  Causalean.Stat.Minimax.Mixture.PoissonLatentSign.coefficient_nonneg _ _ _ _ _

/-- The collision gain for the singleton coefficient is exactly the paper's bound (36). -/
-- @node: lowerPoissonCoefficient_one_le
lemma lowerPoissonCoefficient_one_le (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (xi : NNReal) (hx : (xi : ℝ) ≤ 1) (gamma : ℝ) :
    lowerPoissonCoefficient tau ht xi gamma 1 ≤
      (Real.exp ((5 / 3 : ℝ) ^ 2 - 1) *
        ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4)) * (xi : ℝ) ^ 2 * tau ^ 2 * gamma ^ 2 := by
  exact Causalean.Stat.Minimax.Mixture.PoissonLatentSign.coefficient_one_le _ hx
    (by rw [abs_of_pos ht.1]; exact ht.2) (lowerUnitCellDesign_valid tau ht) gamma

/-- Poisson factorial averaging gives (37) at every order. -/
-- @node: lowerPoissonCoefficient_le_factorial
lemma lowerPoissonCoefficient_le_factorial (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (xi : NNReal) (gamma : ℝ) (d : ℕ) :
    lowerPoissonCoefficient tau ht xi gamma d ≤
      (4 * (xi : ℝ) * gamma ^ 2) ^ d / (d.factorial : ℝ) := by
  exact Causalean.Stat.Minimax.Mixture.PoissonLatentSign.coefficient_le_factorial _ xi
    (by rw [abs_of_pos ht.1]; exact ht.2) (lowerUnitCellDesign_valid tau ht) gamma d

/-- The unconditional cell cross-moment series. -/
-- @node: lowerPoissonOverlap
def lowerPoissonOverlap (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (xi : NNReal) (gamma z : ℝ) : ℝ :=
  Causalean.Stat.Minimax.Mixture.PoissonLatentSign.overlapSeries
    (lowerPoissonCoefficient tau ht xi gamma) z

/-- Count and actual null-design averaging recover the coefficient series in (31). -/
-- @node: lowerPoissonOverlap_eq_integral
lemma lowerPoissonOverlap_eq_integral (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (xi : NNReal) (gamma z : ℝ) :
    lowerPoissonOverlap tau ht xi gamma z =
      ∫ m : ℕ, ∫ c,
        Causalean.Stat.Minimax.Mixture.PoissonLatentSign.cellOverlap tau gamma z c
        ∂lowerUnitCellDesign tau ht m ∂poissonMeasure xi := by
  exact (Causalean.Stat.Minimax.Mixture.PoissonLatentSign.integral_cellOverlap_eq_series
    _ xi (by rw [abs_of_pos ht.1]; exact ht.2) (lowerUnitCellDesign_valid tau ht) gamma z).symm

/-- The absolutely convergent higher-order tail has the bound (38). -/
-- @node: lowerPoissonOverlap_remainder
lemma lowerPoissonOverlap_remainder (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (xi : NNReal) (gamma z : ℝ) (hr : 4 * (xi : ℝ) * gamma ^ 2 * |z| ≤ 1 / 2) :
    |lowerPoissonOverlap tau ht xi gamma z - 1 -
      lowerPoissonCoefficient tau ht xi gamma 1 * z| ≤
      16 * (xi : ℝ) ^ 2 * gamma ^ 4 * z ^ 2 := by
  have h := Causalean.Stat.Minimax.Mixture.PoissonLatentSign.overlapSeries_remainder
    (b := 4 * (xi : ℝ) * gamma ^ 2) (by positivity)
    (fun d _ => ⟨lowerPoissonCoefficient_nonneg tau ht xi gamma d,
      lowerPoissonCoefficient_le_factorial tau ht xi gamma d⟩) hr
  change |lowerPoissonOverlap tau ht xi gamma z - 1 -
    lowerPoissonCoefficient tau ht xi gamma 1 * z| ≤ _ at h
  convert h using 1 <;> ring

/-- The exact singleton coefficient is retained for overlaps of either sign in (39). -/
-- @node: lowerPoissonOverlap_pow_le_exp
lemma lowerPoissonOverlap_pow_le_exp (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (xi : NNReal) (gamma z : ℝ) (hr : 4 * (xi : ℝ) * gamma ^ 2 * |z| ≤ 1 / 2) (k : ℕ) :
    lowerPoissonOverlap tau ht xi gamma z ^ k ≤
      Real.exp (((k : ℝ) * lowerPoissonCoefficient tau ht xi gamma 1) * z +
        16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4 * z ^ 2) := by
  exact Causalean.Stat.Minimax.Mixture.PoissonLatentSign.poisson_overlap_pow_le_exp
    _ xi (by rw [abs_of_pos ht.1]; exact ht.2) (lowerUnitCellDesign_valid tau ht) hr k

/-- Independent Poisson cell counts and their conditional shared-sign designs factor
exactly into the power of the unconditional cell cross moment in (40). This
establishes the product-experiment calculation; identifying that experiment with
ordered Poisson observations is a separate partition-and-ordering step. -/
-- @node: lowerPoissonOverlap_independent_cells
lemma lowerPoissonOverlap_independent_cells (tau : ℝ)
    (ht : tau ∈ Set.Ioc 0 (1 / 4)) (xi : NNReal) (gamma z : ℝ) (k : ℕ) :
    (∫ counts : Fin k → ℕ,
      ∫ cells : (i : Fin k) → Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell (counts i),
        ∏ i : Fin k,
          Causalean.Stat.Minimax.Mixture.PoissonLatentSign.cellOverlap tau gamma z (cells i)
        ∂Measure.pi (fun i => lowerUnitCellDesign tau ht (counts i))
      ∂Measure.pi (fun _ : Fin k => poissonMeasure xi)) =
      lowerPoissonOverlap tau ht xi gamma z ^ k := by
  simp_rw [integral_fintype_prod_eq_prod]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin k => fun m : ℕ =>
    ∫ c, Causalean.Stat.Minimax.Mixture.PoissonLatentSign.cellOverlap tau gamma z c
      ∂lowerUnitCellDesign tau ht m)]
  simp_rw [← lowerPoissonOverlap_eq_integral tau ht xi gamma z]
  simp

/-- Equal finite prior weights preserve pointwise bounds on outcome-sign pairs. -/
-- @node: signPairExpectation_mono
lemma signPairExpectation_mono (j : ℕ)
    (f g : (Fin j → Bool) → (Fin j → Bool) → ℝ)
    (h : ∀ omega op, f omega op ≤ g omega op) :
    signPairExpectation j f ≤ signPairExpectation j g := by
  classical
  unfold signPairExpectation
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun omega _ => Finset.sum_le_sum fun op _ => h omega op
  · positivity

/-- Independent-cell cross moments averaged over the outcome signs have the
Gaussian square-completion envelope (42), with the singleton coefficient exact. -/
-- @node: lowerPoissonOverlap_sign_average_bound
lemma lowerPoissonOverlap_sign_average_bound (tau : ℝ)
    (ht : tau ∈ Set.Ioc 0 (1 / 4)) (xi : NNReal) (gamma : ℝ)
    (k j : ℕ) (w : Fin j → ℝ)
    (hr : ∀ omega op, 4 * (xi : ℝ) * gamma ^ 2 *
      |weightedSignOverlap j w omega op| ≤ 1 / 2)
    (hsmall : 2 * (∑ i : Fin j, (w i) ^ 2) *
      (16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4) < 1) :
    signPairExpectation j (fun omega op =>
      lowerPoissonOverlap tau ht xi gamma (weightedSignOverlap j w omega op) ^ k) ≤
      (1 - 2 * (∑ i : Fin j, (w i) ^ 2) *
        (16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4)) ^ (-1 / 2 : ℝ) *
      Real.exp ((∑ i : Fin j, (w i) ^ 2) *
        ((k : ℝ) * lowerPoissonCoefficient tau ht xi gamma 1) ^ 2 /
        (2 * (1 - 2 * (∑ i : Fin j, (w i) ^ 2) *
          (16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4)))) := by
  calc
    _ ≤ signPairExpectation j (fun omega op =>
        Real.exp (((k : ℝ) * lowerPoissonCoefficient tau ht xi gamma 1) *
          weightedSignOverlap j w omega op +
          (16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4) *
            (weightedSignOverlap j w omega op) ^ 2)) :=
      signPairExpectation_mono j _ _ fun omega op =>
        lowerPoissonOverlap_pow_le_exp tau ht xi gamma _ (hr omega op) k
    _ ≤ _ := weighted_sign_quadratic_bound j w
      ((k : ℝ) * lowerPoissonCoefficient tau ht xi gamma 1)
      (16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4) (by positivity) hsmall

/-- On the compact range used in (43), the exponential has a linear upper bound. -/
-- @node: lower_exp_le_one_add_twice
lemma lower_exp_le_one_add_twice (v : ℝ) (hv : v ∈ Set.Icc 0 (1 / 2)) :
    Real.exp v ≤ 1 + 2 * v := by
  calc
    _ ≤ 1 / (1 - v) := Real.exp_bound_div_one_sub_of_interval hv.1 (by linarith [hv.2])
    _ ≤ _ := by
      apply (div_le_iff₀ (by linarith [hv.2] : 0 < 1 - v)).2
      nlinarith [mul_nonneg hv.1 (show 0 ≤ 1 - 2 * v by linarith [hv.2])]

/-- The inverse square-root factor in (42) is bounded by its linear envelope. -/
-- @node: lower_inverse_sqrt_le
lemma lower_inverse_sqrt_le (t : ℝ) (ht : t ∈ Set.Icc 0 (1 / 2)) :
    (1 - t) ^ (-1 / 2 : ℝ) ≤ 1 + 2 * t := by
  have hu : 0 < 1 - t := by linarith [ht.2]
  have hs : 1 - t ≤ Real.sqrt (1 - t) := by
    apply (Real.le_sqrt hu.le hu.le).2
    nlinarith [mul_nonneg ht.1 (show 0 ≤ 1 - t by linarith [ht.2])]
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hu.le,
    ← Real.sqrt_eq_rpow]
  calc
    _ = 1 / Real.sqrt (1 - t) := by rw [one_div]
    _ ≤ 1 / (1 - t) := one_div_le_one_div_of_le hu hs
    _ ≤ _ := by
      apply (div_le_iff₀ hu).2
      nlinarith [mul_nonneg ht.1 (show 0 ≤ 1 - 2 * t by linarith [ht.2])]

/-- The Gaussian envelope gives an explicit first inequality in (43), with
constant eight and precisely the linear-square and quadratic scale terms. -/
-- @node: lower_gaussian_envelope_le
lemma lower_gaussian_envelope_le (s a d : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (ht : 2 * s * d ≤ 1 / 2) (ha : s * a ^ 2 ≤ 1 / 2) :
    (1 - 2 * s * d) ^ (-1 / 2 : ℝ) *
      Real.exp (s * a ^ 2 / (2 * (1 - 2 * s * d))) ≤
        1 + 8 * (s * a ^ 2 + s * d) := by
  let t := 2 * s * d
  let v := s * a ^ 2 / (2 * (1 - t))
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 / 2 := ht
  have hden : 0 < 2 * (1 - t) := by linarith
  have hv0 : 0 ≤ v := div_nonneg (mul_nonneg hs (sq_nonneg a)) hden.le
  have hvs : v ≤ s * a ^ 2 := by
    apply (div_le_iff₀ hden).2
    have hp := mul_nonneg (mul_nonneg hs (sq_nonneg a))
      (show 0 ≤ 1 - 2 * t by linarith)
    nlinarith
  have hv1 : v ≤ 1 / 2 := hvs.trans ha
  have hbound := mul_le_mul (lower_inverse_sqrt_le t ⟨ht0, ht1⟩)
    (lower_exp_le_one_add_twice v ⟨hv0, hv1⟩) (Real.exp_pos _).le
    (by linarith : 0 ≤ 1 + 2 * t)
  change (1 - t) ^ (-1 / 2 : ℝ) * Real.exp v ≤ _
  calc
    _ ≤ (1 + 2 * t) * (1 + 2 * v) := hbound
    _ ≤ 1 + 4 * t + 4 * v := by
      nlinarith [mul_nonneg ht0 (show 0 ≤ 1 - 2 * v by linarith)]
    _ ≤ _ := by dsimp [t] at *; nlinarith

/-- Averaging independent-cell overlaps over outcome signs gives the quantitative
excess bound (43); the design-dependent singleton coefficient remains exact. -/
-- @node: lowerPoissonOverlap_sign_excess_le
lemma lowerPoissonOverlap_sign_excess_le (tau : ℝ)
    (ht : tau ∈ Set.Ioc 0 (1 / 4)) (xi : NNReal) (gamma : ℝ)
    (k j : ℕ) (w : Fin j → ℝ)
    (hr : ∀ omega op, 4 * (xi : ℝ) * gamma ^ 2 *
      |weightedSignOverlap j w omega op| ≤ 1 / 2)
    (hd : 2 * (∑ i : Fin j, (w i) ^ 2) *
      (16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4) ≤ 1 / 2)
    (ha : (∑ i : Fin j, (w i) ^ 2) *
      ((k : ℝ) * lowerPoissonCoefficient tau ht xi gamma 1) ^ 2 ≤ 1 / 2) :
    signPairExpectation j (fun omega op =>
      lowerPoissonOverlap tau ht xi gamma (weightedSignOverlap j w omega op) ^ k) - 1 ≤
      8 * ((∑ i : Fin j, (w i) ^ 2) *
        ((k : ℝ) * lowerPoissonCoefficient tau ht xi gamma 1) ^ 2 +
        (∑ i : Fin j, (w i) ^ 2) *
          (16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4)) := by
  have hbound := lowerPoissonOverlap_sign_average_bound tau ht xi gamma k j w hr
    (by linarith)
  have hcompact := lower_gaussian_envelope_le (∑ i : Fin j, (w i) ^ 2)
    ((k : ℝ) * lowerPoissonCoefficient tau ht xi gamma 1)
    (16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4) (by positivity) (by positivity) hd ha
  exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hbound.trans hcompact)

end CausalSmith.Stat.DensityEffectRoughNull
