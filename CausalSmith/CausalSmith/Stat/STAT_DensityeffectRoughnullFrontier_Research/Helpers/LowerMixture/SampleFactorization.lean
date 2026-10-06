module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.CellMeasureBridge
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Function.Floor

/-!
Factorization of actual ordered-sample sign-mixture densities over covariate cells.
The allocation includes boundary records and empty cells, so the likelihood identity
holds pointwise, before any Poisson count or design averaging.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Zero-based covariate cell, with the right endpoint assigned to the last cell. -/
-- @node: lowerCellIndex
def lowerCellIndex (k : ℕ) (hk : 0 < k) (x : ℝ) : Fin k :=
  ⟨min (k - 1) ⌊(k : ℝ) * x⌋₊, lt_of_le_of_lt (min_le_left _ _) (by omega)⟩

/-- Allocation to cells is measurable, including outside the unit interval. -/
-- @node: measurable_lowerCellIndex
@[fun_prop] lemma measurable_lowerCellIndex (k : ℕ) (hk : 0 < k) :
    Measurable (lowerCellIndex k hk) := by
  exact (measurable_of_countable (fun n : ℕ =>
    (⟨min (k - 1) n, lt_of_le_of_lt (min_le_left _ _) (by omega)⟩ : Fin k))).comp
      (Measurable.nat_floor (show Measurable (fun x : ℝ => (k : ℝ) * x) by fun_prop))

/-- Every nonzero scaled bump belongs to its allocated cell. -/
-- @node: lowerCellIndex_eq_of_bump_ne_zero
lemma lowerCellIndex_eq_of_bump_ne_zero (k : ℕ) (hk : 0 < k) (x : ℝ)
    (r : Fin k) (hr : lowerBump ((k : ℝ) * x - r.val) ≠ 0) :
    lowerCellIndex k hk x = r := by
  have hs := lowerBump_nonzero_support hr
  have hn : 0 ≤ (k : ℝ) * x := by
    linarith [hs.1, (Nat.cast_nonneg r.val : (0 : ℝ) ≤ r.val)]
  have hf : ⌊(k : ℝ) * x⌋₊ = r.val :=
    (Nat.floor_eq_iff hn).2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
  apply Fin.ext
  simp only [lowerCellIndex, hf]
  exact min_eq_right (by omega)

/-- The allocated cell is the only signed summand, even when its bump vanishes. -/
-- @node: signedBumps_eq_allocated
lemma signedBumps_eq_allocated (k : ℕ) (hk : 0 < k) (lambda : Fin k → Bool)
    (x : ℝ) :
    signedBumps k lambda x = signValue (lambda (lowerCellIndex k hk x)) *
      lowerBump ((k : ℝ) * x - (lowerCellIndex k hk x).val) := by
  classical
  unfold signedBumps
  apply Finset.sum_eq_single (lowerCellIndex k hk x)
  · intro r _ hr
    have hz : lowerBump ((k : ℝ) * x - r.val) = 0 := by
      by_contra hn
      exact hr (lowerCellIndex_eq_of_bump_ne_zero k hk x r hn).symm
    simp only [hz, mul_zero]
  · simp

/-- Averaging independent Boolean signs factors any product whose records each depend
on the sign of just one allocated cell. This includes empty fibers. -/
-- @node: lower_sign_sum_fiberwise
lemma lower_sign_sum_fiberwise {n k : ℕ} (allocation : Fin n → Fin k)
    (f : Fin n → Bool → ℝ) :
    (∑ lambda : Fin k → Bool, ∏ i : Fin n, f i (lambda (allocation i))) =
      ∏ r : Fin k, ∑ b : Bool, ∏ i : {i : Fin n // allocation i = r}, f i.val b := by
  classical
  calc
    _ = ∑ lambda : Fin k → Bool,
        ∏ r : Fin k, ∏ i : {i : Fin n // allocation i = r}, f i.val (lambda r) := by
      apply Finset.sum_congr rfl
      intro lambda _
      rw [← Fintype.prod_fiberwise allocation (fun i => f i (lambda (allocation i)))]
      apply Finset.prod_congr rfl
      intro r _
      apply Finset.prod_congr rfl
      intro i _
      rw [i.property]
    _ = _ := (Fintype.prod_sum (fun r b =>
      ∏ i : {i : Fin n // allocation i = r}, f i.val b)).symm

/-- Under either experiment, a record density depends only on its allocated propensity
sign. The common outcome sign vector is held fixed. -/
-- @node: lower_record_density_depends_on_cell
lemma lower_record_density_depends_on_cell (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (lambda : Fin k → Bool) (omega : Fin j → Bool)
    (o : Omega) :
    let r := lowerCellIndex k hk (X o)
    lowerRecordDensity (lowerNullLaw theta k j hp lambda omega) o =
      lowerRecordDensity (lowerNullLaw theta k j hp (fun _ => lambda r) omega) o ∧
    lowerRecordDensity (lowerAlternativeLaw theta k j hp lambda omega) o =
      lowerRecordDensity (lowerAlternativeLaw theta k j hp (fun _ => lambda r) omega) o := by
  dsimp only
  have h : signedBumps k lambda (X o) =
      signedBumps k (fun _ => lambda (lowerCellIndex k hk (X o))) (X o) := by
    rw [signedBumps_eq_allocated k hk, signedBumps_eq_allocated k hk]
  constructor <;> change armProbability (lowerPropensity theta k lambda) (A o) (X o) * _ = _
  · simp only [armProbability, lowerPropensity, lowerNullLaw, lowerNullDensity, lowerRecordDensity,
      ObsLaw.ofNuisance, h]
  · simp only [armProbability, lowerPropensity, lowerAlternativeLaw, lowerAlternativeDensity,
      lowerRecordDensity, ObsLaw.ofNuisance, h]

/-- The actual ordered null sample, averaged over its shared cell signs, is the product
of two-sign cell densities. -/
-- @node: lower_null_sample_sign_sum_factors
lemma lower_null_sample_sign_sum_factors (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (omega : Fin j → Bool) (o : Data n) :
    let allocation := fun i => lowerCellIndex k hk (X (o i))
    (∑ lambda : Fin k → Bool, ∏ i : Fin n,
      lowerRecordDensity (lowerNullLaw theta k j hp lambda omega) (o i)) =
    ∏ r : Fin k, ∑ b : Bool, ∏ i : {i : Fin n // allocation i = r},
      lowerRecordDensity (lowerNullLaw theta k j hp (fun _ => b) omega) (o i.val) := by
  dsimp only
  calc
    _ = ∑ lambda : Fin k → Bool, ∏ i : Fin n,
        lowerRecordDensity (lowerNullLaw theta k j hp
          (fun _ => lambda (lowerCellIndex k hk (X (o i)))) omega) (o i) := by
      apply Finset.sum_congr rfl
      intro lambda _
      apply Finset.prod_congr rfl
      intro i _
      exact (lower_record_density_depends_on_cell theta k j hp hk lambda omega (o i)).1
    _ = _ := lower_sign_sum_fiberwise (fun i => lowerCellIndex k hk (X (o i)))
      (fun i b => lowerRecordDensity (lowerNullLaw theta k j hp (fun _ => b) omega) (o i))

/-- Conditional on the common outcome signs, the actual alternative sample density
has the same cell factorization as the null sample. -/
-- @node: lower_alternative_sample_sign_sum_factors
lemma lower_alternative_sample_sign_sum_factors (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (omega : Fin j → Bool) (o : Data n) :
    let allocation := fun i => lowerCellIndex k hk (X (o i))
    (∑ lambda : Fin k → Bool, ∏ i : Fin n,
      lowerRecordDensity (lowerAlternativeLaw theta k j hp lambda omega) (o i)) =
    ∏ r : Fin k, ∑ b : Bool, ∏ i : {i : Fin n // allocation i = r},
      lowerRecordDensity (lowerAlternativeLaw theta k j hp (fun _ => b) omega) (o i.val) := by
  dsimp only
  calc
    _ = ∑ lambda : Fin k → Bool, ∏ i : Fin n,
        lowerRecordDensity (lowerAlternativeLaw theta k j hp
          (fun _ => lambda (lowerCellIndex k hk (X (o i)))) omega) (o i) := by
      apply Finset.sum_congr rfl
      intro lambda _
      apply Finset.prod_congr rfl
      intro i _
      exact (lower_record_density_depends_on_cell theta k j hp hk lambda omega (o i)).2
    _ = _ := lower_sign_sum_fiberwise (fun i => lowerCellIndex k hk (X (o i)))
      (fun i b => lowerRecordDensity (lowerAlternativeLaw theta k j hp (fun _ => b) omega) (o i))

/-- The likelihood quotient for a fixed outcome sign vector is the product of the
actual two-sign cell quotients. The same cell sign is shared by every record in a fiber. -/
-- @node: lower_sample_sign_quotient_factors
lemma lower_sample_sign_quotient_factors (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (omega : Fin j → Bool) (o : Data n) :
    let allocation := fun i => lowerCellIndex k hk (X (o i))
    (∑ lambda : Fin k → Bool, ∏ i : Fin n,
      lowerRecordDensity (lowerAlternativeLaw theta k j hp lambda omega) (o i)) /
    (∑ lambda : Fin k → Bool, ∏ i : Fin n,
      lowerRecordDensity (lowerNullLaw theta k j hp lambda omega) (o i)) =
    ∏ r : Fin k,
      (∑ b : Bool, ∏ i : {i : Fin n // allocation i = r},
        lowerRecordDensity (lowerAlternativeLaw theta k j hp (fun _ => b) omega) (o i.val)) /
      (∑ b : Bool, ∏ i : {i : Fin n // allocation i = r},
        lowerRecordDensity (lowerNullLaw theta k j hp (fun _ => b) omega) (o i.val)) := by
  dsimp only
  rw [lower_null_sample_sign_sum_factors theta k j n hp hk,
    lower_alternative_sample_sign_sum_factors theta k j n hp hk,
    Finset.prod_div_distrib]

/-- Records in one cell are enumerated on a finite index type; likelihood products
are invariant under the chosen enumeration. -/
-- @node: lowerAllocatedSample
def lowerAllocatedSample {n k : ℕ} (allocation : Fin n → Fin k) (o : Data n) (r : Fin k) :
    Data (Fintype.card {i : Fin n // allocation i = r}) :=
  fun i => o (((Fintype.equivFin {i : Fin n // allocation i = r}).symm i).val)

/-- Enumerating a fiber preserves any product of record factors. -/
-- @node: lowerAllocatedSample_prod
lemma lowerAllocatedSample_prod {n k : ℕ} (allocation : Fin n → Fin k) (o : Data n)
    (r : Fin k) (f : Omega → ℝ) :
    (∏ i, f (lowerAllocatedSample allocation o r i)) =
      ∏ i : {i : Fin n // allocation i = r}, f (o i.val) := by
  exact (Fintype.equivFin {i : Fin n // allocation i = r}).symm.prod_comp
    (fun i => f (o i.val))

/-- Every enumerated record is localized to the specified cell, for either sign update. -/
-- @node: lowerAllocatedSample_localization
lemma lowerAllocatedSample_localization (k n : ℕ) (hk : 0 < k) (o : Data n) (r : Fin k)
    (lambda : Fin k → Bool) (b : Bool) :
    let allocation := fun i => lowerCellIndex k hk (X (o i))
    ∀ i, signedBumps k (Function.update lambda r b)
        (X (lowerAllocatedSample allocation o r i)) =
      signValue b * lowerBump ((k : ℝ) * X (lowerAllocatedSample allocation o r i) - r.val) := by
  dsimp only
  intro i
  have hr := ((Fintype.equivFin
    {i : Fin n // lowerCellIndex k hk (X (o i)) = r}).symm i).property
  have hr' : lowerCellIndex k hk (X (lowerAllocatedSample
      (fun i => lowerCellIndex k hk (X (o i))) o r i)) = r := hr
  rw [signedBumps_eq_allocated k hk, hr', Function.update_self]

/-- The abstract cell likelihood is the actual two-sign density quotient on an allocated
fiber. This applies to the empty fiber as well. -/
-- @node: lowerAllocatedSample_ratio_eq
lemma lowerAllocatedSample_ratio_eq (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (omega : Fin j → Bool) (o : Data n)
    (r : Fin k) :
    let allocation := fun i => lowerCellIndex k hk (X (o i))
    let records := lowerAllocatedSample allocation o r
    cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j)
      (fun i => lowerBump ((k : ℝ) * X (records i) - r.val)) (fun i => A (records i))
      (fun i => signedBumps j omega (Y (records i)) / baselineDensity (Y (records i))) =
    (∑ b : Bool, ∏ i : {i : Fin n // allocation i = r},
      lowerRecordDensity (lowerAlternativeLaw theta k j hp (fun _ => b) omega) (o i.val)) /
    (∑ b : Bool, ∏ i : {i : Fin n // allocation i = r},
      lowerRecordDensity (lowerNullLaw theta k j hp (fun _ => b) omega) (o i.val)) := by
  dsimp only
  let allocation := fun i => lowerCellIndex k hk (X (o i))
  let records := lowerAllocatedSample allocation o r
  have hcell (b : Bool) (i : Fin (Fintype.card {i : Fin n // allocation i = r})) :
      signedBumps k (Function.update (fun _ => false) r b) (X (records i)) =
        signValue b * lowerBump ((k : ℝ) * X (records i) - r.val) :=
    lowerAllocatedSample_localization k n hk o r (fun _ => false) b i
  have hbridge := cellAlternativeRatio_eq_lowerLaw_cellMixture theta k j hp
    (fun _ => false) omega r (fun i => X (records i)) (fun i => Y (records i))
    (fun i => A (records i)) (fun i => lowerBump ((k : ℝ) * X (records i) - r.val)) hcell
  have hrecord (b : Bool) (i : Fin (Fintype.card {i : Fin n // allocation i = r})) :
      signedBumps k (Function.update (fun _ => false) r b) (X (records i)) =
        signedBumps k (fun _ => b) (X (records i)) := by
    rw [hcell, signedBumps_eq_allocated k hk]
    have hr := ((Fintype.equivFin {i : Fin n // allocation i = r}).symm i).property
    change _ = signValue b * lowerBump ((k : ℝ) * X (records i) -
      (lowerCellIndex k hk (X (records i))).val)
    rw [show lowerCellIndex k hk (X (records i)) = r from hr]
  have hnull (b : Bool) (i : Fin (Fintype.card {i : Fin n // allocation i = r})) :
      lowerRecordDensity (lowerNullLaw theta k j hp
        (Function.update (fun _ => false) r b) omega) (records i) =
      lowerRecordDensity (lowerNullLaw theta k j hp (fun _ => b) omega) (records i) := by
    change armProbability (lowerPropensity theta k _) (A (records i)) (X (records i)) *
      baselineDensity (Y (records i)) = _
    simp only [lowerRecordDensity, lowerNullLaw, ObsLaw.ofNuisance,
      lowerNullDensity, armProbability, lowerPropensity, hrecord]
  have halt (b : Bool) (i : Fin (Fintype.card {i : Fin n // allocation i = r})) :
      lowerRecordDensity (lowerAlternativeLaw theta k j hp
        (Function.update (fun _ => false) r b) omega) (records i) =
      lowerRecordDensity (lowerAlternativeLaw theta k j hp (fun _ => b) omega) (records i) := by
    change armProbability (lowerPropensity theta k _) (A (records i)) (X (records i)) *
      lowerAlternativeDensity theta k j _ omega (A (records i)) (X (records i)) (Y (records i)) = _
    simp only [lowerRecordDensity, lowerAlternativeLaw, ObsLaw.ofNuisance,
      lowerAlternativeDensity, armProbability, lowerPropensity, hrecord]
  change _ =
    (∑ b : Bool, ∏ i : Fin (Fintype.card {i : Fin n // allocation i = r}),
      lowerRecordDensity (lowerAlternativeLaw theta k j hp
        (Function.update (fun _ => false) r b) omega) (records i)) /
    (∑ b : Bool, ∏ i : Fin (Fintype.card {i : Fin n // allocation i = r}),
      lowerRecordDensity (lowerNullLaw theta k j hp
        (Function.update (fun _ => false) r b) omega) (records i)) at hbridge
  simp_rw [hnull, halt] at hbridge
  simpa only [records, lowerAllocatedSample_prod] using hbridge

/-- Product of the paper's cell likelihoods in the actual ordered sample. -/
-- @node: lowerSampleCellRatio
def lowerSampleCellRatio (theta : ℝ) (k j n : ℕ) (hk : 0 < k)
    (omega : Fin j → Bool) (o : Data n) : ℝ :=
  let allocation := fun i => lowerCellIndex k hk (X (o i))
  ∏ r : Fin k,
    let records := lowerAllocatedSample allocation o r
    cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j)
      (fun i => lowerBump ((k : ℝ) * X (records i) - r.val)) (fun i => A (records i))
      (fun i => signedBumps j omega (Y (records i)) / baselineDensity (Y (records i)))

/-- Global shared-sign averaging yields exactly the product of localized cell likelihoods. -/
-- @node: lower_sample_sign_quotient_eq_cell_product
lemma lower_sample_sign_quotient_eq_cell_product (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (omega : Fin j → Bool) (o : Data n) :
    (∑ lambda : Fin k → Bool, ∏ i : Fin n,
      lowerRecordDensity (lowerAlternativeLaw theta k j hp lambda omega) (o i)) /
    (∑ lambda : Fin k → Bool, ∏ i : Fin n,
      lowerRecordDensity (lowerNullLaw theta k j hp lambda omega) (o i)) =
      lowerSampleCellRatio theta k j n hk omega o := by
  rw [lower_sample_sign_quotient_factors theta k j n hp hk]
  unfold lowerSampleCellRatio
  dsimp only
  apply Finset.prod_congr rfl
  intro r _
  exact (lowerAllocatedSample_ratio_eq theta k j n hp hk omega o r).symm

/-- A finite prior density is the ordinary real average of its nonnegative sample
products, embedded into the extended nonnegative reals. -/
-- @node: lower_uniform_sample_density_eq_ofReal
lemma lower_uniform_sample_density_eq_ofReal {S : Type*} [Fintype S] [Nonempty S]
    (family : S → ObsLaw) (h : ∀ s o, 0 ≤ lowerRecordDensity (family s) o)
    (n : ℕ) (o : Data n) :
    lowerUniformSampleDensity family n o = ENNReal.ofReal
      ((Fintype.card S : ℝ)⁻¹ * ∑ s, ∏ i, lowerRecordDensity (family s) (o i)) := by
  have hc : 0 < (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos
  have hprod (s : S) : ENNReal.ofReal (∏ i, lowerRecordDensity (family s) (o i)) =
      ∏ i, ENNReal.ofReal (lowerRecordDensity (family s) (o i)) :=
    ENNReal.ofReal_prod_of_nonneg (fun i _ => h s (o i))
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), ENNReal.ofReal_sum_of_nonneg
    (fun s _ => Finset.prod_nonneg (fun i _ => h s (o i)))]
  simp only [lowerUniformSampleDensity, lowerSampleDensity, hprod]
  rw [ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast]

/-- For fixed outcome signs, the actual full-sample density quotient is the cell
likelihood product, with no localization assumptions or artificial design law. -/
-- @node: lower_sample_density_quotient_eq_cell_product
lemma lower_sample_density_quotient_eq_cell_product (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (omega : Fin j → Bool) (o : Data n) :
    lowerUniformSampleDensity
      (fun lambda => lowerAlternativeLaw theta k j hp lambda omega) n o /
    lowerUniformSampleDensity
      (fun lambda => lowerNullLaw theta k j hp lambda omega) n o =
      ENNReal.ofReal (lowerSampleCellRatio theta k j n hk omega o) := by
  rw [lower_uniform_sample_density_eq_ofReal _
      (fun lambda o => lower_alternative_recordDensity_nonneg theta k j hp lambda omega o),
    lower_uniform_sample_density_eq_ofReal _
      (fun lambda o => (lower_null_recordDensity_pos theta k j hp lambda omega o).le)]
  have hc : 0 < (Fintype.card (Fin k → Bool) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn : 0 < ∑ lambda : Fin k → Bool, ∏ i : Fin n,
      lowerRecordDensity (lowerNullLaw theta k j hp lambda omega) (o i) :=
    Finset.sum_pos (fun lambda _ => Finset.prod_pos (fun i _ =>
      lower_null_recordDensity_pos theta k j hp lambda omega (o i))) Finset.univ_nonempty
  rw [← ENNReal.ofReal_div_of_pos (mul_pos (inv_pos.mpr hc) hn),
    mul_div_mul_left _ _ (ne_of_gt (inv_pos.mpr hc)),
    lower_sample_sign_quotient_eq_cell_product theta k j n hp hk]

/-- The ordered alternative experiment with fixed outcome signs is the actual null
experiment weighted by the product of the established cell likelihoods. -/
-- @node: lower_ordered_mixture_withDensity_cell_product
lemma lower_ordered_mixture_withDensity_cell_product (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (omega : Fin j → Bool) :
    uniformSampleMixture n (fun lambda => lowerAlternativeLaw theta k j hp lambda omega) =
      (uniformSampleMixture n (fun lambda => lowerNullLaw theta k j hp lambda omega)).withDensity
        (fun o => ENNReal.ofReal (lowerSampleCellRatio theta k j n hk omega o)) := by
  rw [lower_sign_mixture_withDensity_quotient theta k j hp
    (fun lambda : Fin k → Bool => lambda) (fun _ => omega) n]
  congr 1
  funext o
  exact lower_sample_density_quotient_eq_cell_product theta k j n hp hk omega o

/-- The Radon--Nikodym derivative in the ordered experiment is the cell likelihood product. -/
-- @node: lower_ordered_mixture_rnDeriv_cell_product
lemma lower_ordered_mixture_rnDeriv_cell_product (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (omega : Fin j → Bool) :
    (uniformSampleMixture n (fun lambda => lowerAlternativeLaw theta k j hp lambda omega)).rnDeriv
      (uniformSampleMixture n (fun lambda => lowerNullLaw theta k j hp lambda omega)) =ᵐ[
        uniformSampleMixture n (fun lambda => lowerNullLaw theta k j hp lambda omega)]
      (fun o => ENNReal.ofReal (lowerSampleCellRatio theta k j n hk omega o)) := by
  exact (lower_sign_mixture_rnDeriv theta k j hp
    (fun lambda : Fin k → Bool => lambda) (fun _ => omega) n).trans
    (Filter.Eventually.of_forall
      (lower_sample_density_quotient_eq_cell_product theta k j n hp hk omega))

/-- A shared-sign prior's density quotient is the quotient of its real sample sums;
the common uniform-prior normalization cancels exactly. -/
-- @node: lower_sign_prior_density_quotient_real
lemma lower_sign_prior_density_quotient_real {S : Type*} [Fintype S] [Nonempty S]
    (theta : ℝ) (k j n : ℕ) (hp : LowerParameters theta k j)
    (lambda : S → Fin k → Bool) (omega : S → Fin j → Bool) (o : Data n) :
    lowerUniformSampleDensity
      (fun s => lowerAlternativeLaw theta k j hp (lambda s) (omega s)) n o /
    lowerUniformSampleDensity
      (fun s => lowerNullLaw theta k j hp (lambda s) (omega s)) n o =
    ENNReal.ofReal
      ((∑ s, ∏ i : Fin n, lowerRecordDensity
        (lowerAlternativeLaw theta k j hp (lambda s) (omega s)) (o i)) /
      (∑ s, ∏ i : Fin n, lowerRecordDensity
        (lowerNullLaw theta k j hp (lambda s) (omega s)) (o i))) := by
  rw [lower_uniform_sample_density_eq_ofReal _
      (fun s o => lower_alternative_recordDensity_nonneg theta k j hp (lambda s) (omega s) o),
    lower_uniform_sample_density_eq_ofReal _
      (fun s o => (lower_null_recordDensity_pos theta k j hp (lambda s) (omega s) o).le)]
  have hc : 0 < (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn : 0 < ∑ s, ∏ i : Fin n,
      lowerRecordDensity (lowerNullLaw theta k j hp (lambda s) (omega s)) (o i) :=
    Finset.sum_pos (fun s _ => Finset.prod_pos (fun i _ =>
      lower_null_recordDensity_pos theta k j hp (lambda s) (omega s) (o i))) Finset.univ_nonempty
  rw [← ENNReal.ofReal_div_of_pos (mul_pos (inv_pos.mpr hc) hn),
    mul_div_mul_left _ _ (ne_of_gt (inv_pos.mpr hc))]

/-- The null experiment does not use the redundant outcome-sign vector. -/
-- @node: lower_null_record_density_outcome_sign_irrel
lemma lower_null_record_density_outcome_sign_irrel (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool)
    (omega omega' : Fin j → Bool) (o : Omega) :
    lowerRecordDensity (lowerNullLaw theta k j hp lambda omega) o =
      lowerRecordDensity (lowerNullLaw theta k j hp lambda omega') o := rfl

/-- Average the product likelihood over the single common outcome-sign vector,
which is retained across every covariate cell. -/
-- @node: lowerOutcomeAveragedSampleRatio
def lowerOutcomeAveragedSampleRatio (theta : ℝ) (k j n : ℕ) (hk : 0 < k) (o : Data n) : ℝ :=
  (Fintype.card (Fin j → Bool) : ℝ)⁻¹ *
    ∑ omega : Fin j → Bool, lowerSampleCellRatio theta k j n hk omega o

/-- The likelihood quotient of both actual finite priors is the outcome-sign average
of products of cell likelihoods. This is the ordered-sample likelihood preceding (40). -/
-- @node: lower_full_sample_density_quotient_eq_cell_average
lemma lower_full_sample_density_quotient_eq_cell_average (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (o : Data n) :
    lowerUniformSampleDensity
      (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerAlternativeLaw theta k j hp s.1 s.2) n o /
    lowerUniformSampleDensity
      (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerNullLaw theta k j hp s.1 s.2) n o =
      ENNReal.ofReal (lowerOutcomeAveragedSampleRatio theta k j n hk o) := by
  rw [lower_sign_prior_density_quotient_real theta k j n hp Prod.fst Prod.snd]
  congr 1
  let D := ∑ lambda : Fin k → Bool, ∏ i : Fin n,
    lowerRecordDensity (lowerNullLaw theta k j hp lambda (fun _ => false)) (o i)
  have hden :
      (∑ s : (Fin k → Bool) × (Fin j → Bool), ∏ i : Fin n,
        lowerRecordDensity (lowerNullLaw theta k j hp s.1 s.2) (o i)) =
      (Fintype.card (Fin j → Bool) : ℝ) * D := by
    rw [Fintype.sum_prod_type_right]
    simp_rw [lower_null_record_density_outcome_sign_irrel theta k j hp _ _ (fun _ => false)]
    simp only [D, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hquot (omega : Fin j → Bool) :
      (∑ lambda : Fin k → Bool, ∏ i : Fin n,
        lowerRecordDensity (lowerAlternativeLaw theta k j hp lambda omega) (o i)) / D =
      lowerSampleCellRatio theta k j n hk omega o := by
    have h := lower_sample_sign_quotient_eq_cell_product theta k j n hp hk omega o
    simp_rw [lower_null_record_density_outcome_sign_irrel theta k j hp _ omega
      (fun _ => false)] at h
    exact h
  rw [hden, Fintype.sum_prod_type_right]
  unfold lowerOutcomeAveragedSampleRatio
  simp_rw [← hquot]
  rw [← Finset.sum_div]
  ring

/-- Both complete actual sign priors are compared using the outcome-average of cell
likelihood products, with the true null mixture as the reference measure. -/
-- @node: lower_full_ordered_mixture_withDensity_cell_average
lemma lower_full_ordered_mixture_withDensity_cell_average (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) :
    uniformSampleMixture n (fun s : (Fin k → Bool) × (Fin j → Bool) =>
      lowerAlternativeLaw theta k j hp s.1 s.2) =
    (uniformSampleMixture n (fun s : (Fin k → Bool) × (Fin j → Bool) =>
      lowerNullLaw theta k j hp s.1 s.2)).withDensity
      (fun o => ENNReal.ofReal (lowerOutcomeAveragedSampleRatio theta k j n hk o)) := by
  rw [lower_sign_mixture_withDensity_quotient theta k j hp
    (fun s : (Fin k → Bool) × (Fin j → Bool) => s.1) (fun s => s.2) n]
  congr 1
  funext o
  exact lower_full_sample_density_quotient_eq_cell_average theta k j n hp hk o

/-- The complete ordered-mixture Radon--Nikodym derivative retains the common outcome
sign average outside the product over covariate cells. -/
-- @node: lower_full_ordered_mixture_rnDeriv_cell_average
lemma lower_full_ordered_mixture_rnDeriv_cell_average (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) :
    (uniformSampleMixture n (fun s : (Fin k → Bool) × (Fin j → Bool) =>
      lowerAlternativeLaw theta k j hp s.1 s.2)).rnDeriv
    (uniformSampleMixture n (fun s : (Fin k → Bool) × (Fin j → Bool) =>
      lowerNullLaw theta k j hp s.1 s.2)) =ᵐ[
    uniformSampleMixture n (fun s : (Fin k → Bool) × (Fin j → Bool) =>
      lowerNullLaw theta k j hp s.1 s.2)]
      (fun o => ENNReal.ofReal (lowerOutcomeAveragedSampleRatio theta k j n hk o)) := by
  exact (lower_sign_mixture_rnDeriv theta k j hp
    (fun s : (Fin k → Bool) × (Fin j → Bool) => s.1) (fun s => s.2) n).trans
    (Filter.Eventually.of_forall
      (lower_full_sample_density_quotient_eq_cell_average theta k j n hp hk))

end CausalSmith.Stat.DensityEffectRoughNull
