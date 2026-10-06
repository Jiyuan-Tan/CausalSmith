module
public import Causalean.Stat.CLT.FiniteIidTriangular.Basic
public import Causalean.Stat.CLT.Martingale.Independent
public import Causalean.Stat.Quantile.CdfConvergence

/-!
Gaussian limits for bounded finite iid triangular rows. It pads finite rows into independent triangular arrays, verifies the Lyapunov hypotheses from the uniform bound, and transfers the resulting law convergence to CDF convergence.
-/

@[expose] public section

namespace Causalean.Stat.CLT.FiniteIidTriangular

open MeasureTheory ProbabilityTheory

/-- An independent family indexed by `Fin d` remains independent as a family indexed by
all natural numbers when every index at least `d` is assigned the constant zero variable. -/
theorem iIndepFun_nat_pad {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : ℕ) (X : Fin d → Ω → ℝ)
    (hX : iIndepFun X μ) :
    iIndepFun (fun k ω => if h : k < d then X ⟨k, h⟩ ω else 0) μ := by
  have hfun : (fun k ω => if h : k < d then X ⟨k, h⟩ ω else (0 : ℝ)) =
      (fun k : ℕ => if hk : k < d then X ⟨k, hk⟩ else fun _ => 0) := by
    funext k ω
    split_ifs <;> rfl
  rw [hfun]
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  let T : Finset (Fin d) := Finset.univ.filter (fun j => (j : ℕ) ∈ S)
  let U : Finset ℕ := S.filter (fun k => k < d)
  have hTU : T.image Fin.val = U := by
    ext k
    rw [Finset.mem_image]
    simp only [U, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(Finset.mem_filter.mp hj).2, j.isLt⟩
    · rintro ⟨hkS, hkD⟩
      exact ⟨⟨k, hkD⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkS⟩, rfl⟩
  have hprob : μ Set.univ = 1 := by
    have h := hX.measure_inter_preimage_eq_mul (∅ : Finset (Fin d))
      (sets := fun _ => Set.univ) (by simp)
    simpa using h
  have hT := hX.measure_inter_preimage_eq_mul T
    (sets := fun j : Fin d => sets j.val)
    (by intro j hj; exact hsets j.val ((Finset.mem_filter.mp hj).2))
  have hbelow :
      μ (⋂ k ∈ U, (if hk : k < d then X ⟨k, hk⟩ else fun _ => 0) ⁻¹' sets k) =
        ∏ k ∈ U, μ ((if hk : k < d then X ⟨k, hk⟩ else fun _ => 0) ⁻¹' sets k) := by
    have hI : (⋂ k ∈ U, (if hk : k < d then X ⟨k, hk⟩ else fun _ => 0) ⁻¹' sets k) =
        ⋂ j ∈ T, X j ⁻¹' sets j.val := by
      ext ω
      simp only [Set.mem_iInter]
      constructor
      · intro h j hj
        have hjS : j.val ∈ S := (Finset.mem_filter.mp hj).2
        have hjU : j.val ∈ U := Finset.mem_filter.mpr ⟨hjS, j.isLt⟩
        simpa [j.isLt] using h j.val hjU
      · intro h k hk
        have hkD : k < d := (Finset.mem_filter.mp hk).2
        have hkS : k ∈ S := (Finset.mem_filter.mp hk).1
        simpa [hkD] using h ⟨k, hkD⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkS⟩)
    rw [hI]
    convert hT using 1
    rw [← hTU, Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro j hj
      simp [j.isLt]
    · exact Fin.val_injective.injOn
  by_cases hbad : ∃ k ∈ S, ¬ k < d ∧ (0 : ℝ) ∉ sets k
  · obtain ⟨k, hkS, hkD, hk0⟩ := hbad
    have hzero : ((if hk : k < d then X ⟨k, hk⟩ else fun _ => 0) ⁻¹' sets k) = ∅ := by
      simp [hkD, hk0]
    have hmem : (⋂ i ∈ S, (if hi : i < d then X ⟨i, hi⟩ else fun _ => 0) ⁻¹' sets i) = ∅ := by
      ext ω
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hω
      have := Set.mem_iInter.mp (Set.mem_iInter.mp hω k) hkS
      simp [hzero] at this
    rw [hmem, measure_empty, Finset.prod_eq_zero hkS]
    simp [hzero]
  · have hout : ∀ k ∈ S, ¬ k < d → (0 : ℝ) ∈ sets k := by
      intro k hkS hkD
      by_contra hk0
      exact hbad ⟨k, hkS, hkD, hk0⟩
    have hI : (⋂ k ∈ S, (if hk : k < d then X ⟨k, hk⟩ else fun _ => 0) ⁻¹' sets k) =
        ⋂ k ∈ U, (if hk : k < d then X ⟨k, hk⟩ else fun _ => 0) ⁻¹' sets k := by
      ext ω
      simp only [Set.mem_iInter]
      constructor
      · intro h k hk
        exact h k (Finset.mem_filter.mp hk).1
      · intro h k hkS
        by_cases hkD : k < d
        · exact h k (Finset.mem_filter.mpr ⟨hkS, hkD⟩)
        · simp [hkD, hout k hkS hkD]
    rw [hI, hbelow]
    have hprod : (∏ k ∈ S, μ ((if hk : k < d then X ⟨k, hk⟩ else fun _ => 0) ⁻¹' sets k)) =
        ∏ k ∈ U, μ ((if hk : k < d then X ⟨k, hk⟩ else fun _ => 0) ⁻¹' sets k) := by
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro k hkS
      by_cases hkD : k < d
      · simp [hkD]
      · simp [hkD, hout k hkS hkD, hprob]
    exact hprod.symm

open MeasureTheory ProbabilityTheory

namespace RowModel

variable {Y : Type*} [Fintype Y] [MeasurableSpace Y]
  [MeasurableSingletonClass Y] (M : RowModel Y)

/-- The standardized increment at natural index `k` is the corresponding coordinate score
divided by the row-length and limiting-variance square roots when `k` is active, and zero
otherwise. -/
noncomputable def standardizedIncrement (n k : ℕ) (ys : Fin (M.N n) → Y) : ℝ :=
  if h : k < M.N n then
    (Real.sqrt (M.N n : ℝ) * Real.sqrt (M.v₀ : ℝ))⁻¹ * M.f n (ys ⟨k, h⟩)
  else 0

/-- Every standardized row increment is strongly measurable under the finite row sample
space. -/
theorem standardizedIncrement_stronglyMeasurable (n k : ℕ) :
    StronglyMeasurable (M.standardizedIncrement n k) := by
  exact (measurable_of_finite _).stronglyMeasurable

/-- Every active standardized coordinate score has a finite second moment under its row's
product probability measure. -/
theorem standardizedIncrement_memLp (n k : ℕ) (hk : k < M.N n) :
    MemLp (M.standardizedIncrement n k) 2 (M.rowMeasure n) := by
  have : IsProbabilityMeasure (M.rowMeasure n) := by
    change IsProbabilityMeasure (M.productDesign n).toMeasure
    infer_instance
  exact MemLp.of_discrete

/-- Every active standardized coordinate score has mean zero under its row's product
probability measure. -/
theorem standardizedIncrement_mean_zero (n k : ℕ) (hk : k < M.N n) :
    ∫ ys, M.standardizedIncrement n k ys ∂M.rowMeasure n = 0 := by
  rw [M.integral_rowMeasure_eq_expect]
  have hcoord := M.expect_coordinate n ⟨k, hk⟩ (M.f n)
  have hcenter := M.centered n
  calc
    M.expect n (M.standardizedIncrement n k) =
        (Real.sqrt (M.N n : ℝ) * Real.sqrt (M.v₀ : ℝ))⁻¹ *
          M.expect n (fun ys => M.f n (ys ⟨k, hk⟩)) := by
            simp only [expect, standardizedIncrement, dif_pos hk, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ys _
            ring
    _ = 0 := by rw [hcoord, hcenter, mul_zero]

/-- The natural-index family of standardized increments is independent under each row's
finite product law, including the zero increments beyond the row length. -/
theorem standardizedIncrement_independent (n : ℕ) :
    iIndepFun (M.standardizedIncrement n) (M.rowMeasure n) := by
  let X : Fin (M.N n) → (Fin (M.N n) → Y) → ℝ :=
    fun i ys => (Real.sqrt (M.N n : ℝ) * Real.sqrt (M.v₀ : ℝ))⁻¹ * M.f n (ys i)
  have hX : iIndepFun X (M.rowMeasure n) := by
    apply (M.rowMeasure_independent n).comp
      (fun _ y => (Real.sqrt (M.N n : ℝ) * Real.sqrt (M.v₀ : ℝ))⁻¹ * M.f n y)
    intro i
    exact measurable_of_finite _
  have : IsProbabilityMeasure (M.rowMeasure n) := by
    change IsProbabilityMeasure (M.productDesign n).toMeasure
    infer_instance
  have hpad := iIndepFun_nat_pad (M.rowMeasure n) (M.N n) X hX
  convert hpad using 1
  funext k ys
  simp only [standardizedIncrement, X]

/-- An active standardized coordinate has second moment equal to the row's
one-coordinate variance divided by row length and limiting variance. -/
theorem standardizedIncrement_integral_sq (n k : ℕ) (hk : k < M.N n) :
    (∫ ys, (M.standardizedIncrement n k ys) ^ 2 ∂M.rowMeasure n) =
      M.oneSecond n / ((M.N n : ℝ) * (M.v₀ : ℝ)) := by
  -- Rewrite the integral as `expect`, extract the constant square, and use
  -- `expect_coordinate` for the score square. `hk` and `variance_pos` make
  -- both denominator factors nonzero.
  have hscale : ((Real.sqrt (M.N n : ℝ) * Real.sqrt (M.v₀ : ℝ))⁻¹) ^ 2 =
      ((M.N n : ℝ) * (M.v₀ : ℝ))⁻¹ := by
    rw [inv_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (show 0 ≤ (M.v₀ : ℝ) by positivity)]
  rw [M.integral_rowMeasure_eq_expect]
  calc
    M.expect n (fun ys => (M.standardizedIncrement n k ys) ^ 2) =
        ((Real.sqrt (M.N n : ℝ) * Real.sqrt (M.v₀ : ℝ))⁻¹) ^ 2 *
          M.expect n (fun ys => (M.f n (ys ⟨k, hk⟩)) ^ 2) := by
            simp only [expect, standardizedIncrement, dif_pos hk, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ys _
            ring
    _ = M.oneSecond n / ((M.N n : ℝ) * (M.v₀ : ℝ)) := by
      rw [M.expect_coordinate n ⟨k, hk⟩ (fun y => (M.f n y) ^ 2), ← oneSecond, hscale]
      ring

/-- An active standardized coordinate has fourth moment at most the fourth
power of the common score bound divided by the squared row length and squared
limiting variance. -/
theorem standardizedIncrement_integral_fourth_le (n k : ℕ) (hk : k < M.N n) :
    (∫ ys, (M.standardizedIncrement n k ys) ^ 4 ∂M.rowMeasure n) ≤
      M.B ^ 4 / ((M.N n : ℝ) ^ 2 * (M.v₀ : ℝ) ^ 2) := by
  -- Use `expect_coordinate` after extracting the scale. The mass-weighted
  -- fourth score moment is at most `B ^ 4` by `bound`, `mass_nonneg`, and
  -- `mass_one`. Both denominator factors are positive.
  have hscale : ((Real.sqrt (M.N n : ℝ) * Real.sqrt (M.v₀ : ℝ))⁻¹) ^ 4 =
      (((M.N n : ℝ) ^ 2) * ((M.v₀ : ℝ) ^ 2))⁻¹ := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, inv_pow, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (show 0 ≤ (M.v₀ : ℝ) by positivity)]
    rw [inv_pow, mul_pow]
  have hfour : (∑ y, M.w n y * (M.f n y) ^ 4) ≤ M.B ^ 4 := by
    calc
      (∑ y, M.w n y * (M.f n y) ^ 4) ≤
          ∑ y, M.w n y * M.B ^ 4 := by
            apply Finset.sum_le_sum
            intro y _
            apply mul_le_mul_of_nonneg_left _ (M.mass_nonneg n y)
            have hB : 0 ≤ M.B := (abs_nonneg _).trans (M.bound n y)
            have hf2 : (M.f n y) ^ 2 ≤ M.B ^ 2 := by
              have hp : 0 ≤ (M.B - |M.f n y|) * (M.B + |M.f n y|) :=
                mul_nonneg (sub_nonneg.mpr (M.bound n y))
                  (add_nonneg hB (abs_nonneg _))
              nlinarith [sq_abs (M.f n y)]
            calc
              (M.f n y) ^ 4 = ((M.f n y) ^ 2) ^ 2 := by ring
              _ ≤ (M.B ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hf2 2
              _ = M.B ^ 4 := by ring
      _ = M.B ^ 4 := by rw [← Finset.sum_mul, M.mass_one n]; ring
  rw [M.integral_rowMeasure_eq_expect]
  calc
    M.expect n (fun ys => (M.standardizedIncrement n k ys) ^ 4) =
        ((Real.sqrt (M.N n : ℝ) * Real.sqrt (M.v₀ : ℝ))⁻¹) ^ 4 *
          M.expect n (fun ys => (M.f n (ys ⟨k, hk⟩)) ^ 4) := by
            simp only [expect, standardizedIncrement, dif_pos hk, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ys _
            ring
    _ = (∑ y, M.w n y * (M.f n y) ^ 4) /
          ((M.N n : ℝ) ^ 2 * (M.v₀ : ℝ) ^ 2) := by
            rw [M.expect_coordinate n ⟨k, hk⟩ (fun y => (M.f n y) ^ 4), hscale]
            ring
    _ ≤ M.B ^ 4 / ((M.N n : ℝ) ^ 2 * (M.v₀ : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_right hfour (by positivity)

end RowModel

open Filter MeasureTheory ProbabilityTheory Topology

namespace RowModel

variable {Y : Type*} [Fintype Y] [MeasurableSpace Y]
  [MeasurableSingletonClass Y] (M : RowModel Y)

/-- The standardized finite iid row is an independent triangular array whose active
increments are the coordinate scores divided by both square-root scales. -/
noncomputable def standardizedArray :
    Causalean.Stat.IndependentTriangularArray
      (fun n => Fin (M.N n) → Y) (fun n => M.rowMeasure n) := by
  exact {
    rowLength := M.N
    increment := M.standardizedIncrement
    measurable := M.standardizedIncrement_stronglyMeasurable
    squareIntegrable := M.standardizedIncrement_memLp
    mean_zero := M.standardizedIncrement_mean_zero
    independent := M.standardizedIncrement_independent
  }

/-- The total increment variance of the standardized array tends to one. -/
theorem standardizedArray_varianceSum_tendsto :
    Tendsto M.standardizedArray.varianceSum atTop (𝓝 1) := by
  have hlim : Tendsto (fun n => M.oneSecond n / (M.v₀ : ℝ)) atTop (𝓝 1) := by
    have hv : (M.v₀ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast M.variance_pos)
    simpa only [oneSecond, div_self hv] using
      M.variance_tendsto.div_const (M.v₀ : ℝ)
  have hpositive : ∀ᶠ n in atTop, 0 < M.N n :=
    M.length_tendsto.eventually (eventually_gt_atTop 0)
  apply hlim.congr'
  filter_upwards [hpositive] with n hn
  symm
  change (∑ k ∈ Finset.range (M.N n),
    ∫ ys, (M.standardizedIncrement n k ys) ^ 2 ∂M.rowMeasure n) =
      M.oneSecond n / (M.v₀ : ℝ)
  rw [Finset.sum_congr rfl (fun k hk =>
    M.standardizedIncrement_integral_sq n k (Finset.mem_range.mp hk))]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hN : (M.N n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hv : (M.v₀ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast M.variance_pos)
  field_simp

/-- The sum of fourth absolute moments of the standardized increments tends to
zero, as required by Lyapunov with moment surplus two. -/
theorem standardizedArray_lyapunovSum_two_tendsto :
    Tendsto (M.standardizedArray.lyapunovSum 2) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun n => (M.B ^ 4 / (M.v₀ : ℝ) ^ 2) / (M.N n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat (M.B ^ 4 / (M.v₀ : ℝ) ^ 2)).comp
        M.length_tendsto
  have hnonneg : ∀ n, 0 ≤ M.standardizedArray.lyapunovSum 2 n := by
    intro n
    change 0 ≤ ∑ k ∈ Finset.range (M.N n),
      ∫ ys, |M.standardizedIncrement n k ys| ^ (2 + (2 : ℝ)) ∂M.rowMeasure n
    apply Finset.sum_nonneg
    intro k hk
    apply integral_nonneg
    intro ys
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hpositive : ∀ᶠ n in atTop, 0 < M.N n :=
    M.length_tendsto.eventually (eventually_gt_atTop 0)
  have hbound : ∀ᶠ n in atTop,
      M.standardizedArray.lyapunovSum 2 n ≤
        (M.B ^ 4 / (M.v₀ : ℝ) ^ 2) / (M.N n : ℝ) := by
    filter_upwards [hpositive] with n hn
    change (∑ k ∈ Finset.range (M.N n),
      ∫ ys, |M.standardizedIncrement n k ys| ^ (2 + (2 : ℝ)) ∂M.rowMeasure n) ≤ _
    calc
      (∑ k ∈ Finset.range (M.N n),
          ∫ ys, |M.standardizedIncrement n k ys| ^ (2 + (2 : ℝ)) ∂M.rowMeasure n) ≤
          ∑ k ∈ Finset.range (M.N n),
            M.B ^ 4 / ((M.N n : ℝ) ^ 2 * (M.v₀ : ℝ) ^ 2) := by
              apply Finset.sum_le_sum
              intro k hk
              calc
                (∫ ys, |M.standardizedIncrement n k ys| ^ (2 + (2 : ℝ))
                  ∂M.rowMeasure n) =
                    ∫ ys, (M.standardizedIncrement n k ys) ^ 4 ∂M.rowMeasure n := by
                      congr 1
                      funext ys
                      rw [show (2 : ℝ) + 2 = (4 : ℕ) by norm_num,
                        Real.rpow_natCast]
                      have hpow : 0 ≤ (M.standardizedIncrement n k ys) ^ 4 := by positivity
                      rw [← abs_pow, abs_of_nonneg hpow]
                _ ≤ _ := M.standardizedIncrement_integral_fourth_le n k
                  (Finset.mem_range.mp hk)
      _ = (M.B ^ 4 / (M.v₀ : ℝ) ^ 2) / (M.N n : ℝ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hN : (M.N n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
        have hv : (M.v₀ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast M.variance_pos)
        field_simp
  exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hbound hsmall

end RowModel

open Filter MeasureTheory ProbabilityTheory Topology

namespace RowModel

variable {Y : Type*} [Fintype Y] (M : RowModel Y)

/-- The finite-product CDF at a threshold is the mass of row outcomes whose normalized score
sum is at most that threshold. -/
noncomputable def normalizedCDF (n : ℕ) (t : ℝ) : ℝ :=
  M.expect n (fun ys => if M.normalizedSum n ys ≤ t then 1 else 0)

/-- The law of the normalized score sum is the pushforward of the finite product row measure. -/
noncomputable def normalizedSumLaw [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (n : ℕ) : Measure ℝ :=
  (M.rowMeasure n).map (M.normalizedSum n)

/-- The literal finite-product CDF equals the CDF of the normalized-sum pushforward law. -/
theorem normalizedCDF_eq_cdf [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (n : ℕ) (t : ℝ) :
    M.normalizedCDF n t = cdf (M.normalizedSumLaw n) t := by
  classical
  have : IsProbabilityMeasure (M.rowMeasure n) := by
    change IsProbabilityMeasure (M.productDesign n).toMeasure
    infer_instance
  have : IsProbabilityMeasure (M.normalizedSumLaw n) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite (M.normalizedSum n)).aemeasurable
  rw [cdf_eq_real, normalizedSumLaw, measureReal_def,
    Measure.map_apply (measurable_of_finite (M.normalizedSum n)) measurableSet_Iic]
  change M.normalizedCDF n t =
    (M.rowMeasure n).real (M.normalizedSum n ⁻¹' Set.Iic t)
  rw [← integral_indicator_one
    ((measurable_of_finite (M.normalizedSum n)) measurableSet_Iic)]
  rw [normalizedCDF, ← M.integral_rowMeasure_eq_expect]
  congr 1

/-- Every positive threshold eventually exceeds all individual score increments after
normalization by the square root of the growing row length. -/
theorem eventually_small_normalized_coordinate (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ y, |(Real.sqrt (M.N n : ℝ))⁻¹ * M.f n y| < ε := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (M.N n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp M.length_tendsto)
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt (M.N n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hlim : Tendsto
      (fun n : ℕ => (Real.sqrt (M.N n : ℝ))⁻¹ * max M.B 0) atTop (𝓝 0) := by
    simpa using hinv.mul_const (max M.B 0)
  have hsmall : ∀ᶠ n in atTop,
      (Real.sqrt (M.N n : ℝ))⁻¹ * max M.B 0 < ε := by
    exact hlim.eventually_lt_const hε
  filter_upwards [hsmall] with n hn y
  calc
    |(Real.sqrt (M.N n : ℝ))⁻¹ * M.f n y| =
        (Real.sqrt (M.N n : ℝ))⁻¹ * |M.f n y| := by
          rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    _ ≤ (Real.sqrt (M.N n : ℝ))⁻¹ * max M.B 0 := by
      exact mul_le_mul_of_nonneg_left ((M.bound n y).trans (le_max_left _ _))
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ < ε := hn

set_option maxHeartbeats 1000000 in
-- The CLT/CDF conversion elaborates several finite-space measure instances.
/-- [At each real threshold](hyp:t), [the normalized finite iid score CDF converges to the
centered Gaussian CDF with the positive limiting one-coordinate variance](goal). -/
theorem normalizedCDF_tendsto_gaussian (t : ℝ) :
    Tendsto (fun n => M.normalizedCDF n t) atTop
      (𝓝 (cdf (gaussianReal 0 M.v₀) t)) := by
  /-
  Give the finite alphabet its discrete measurable space locally; the
  statement itself needs no measurable-space assumption. Then obtain
  `∀ n, IsProbabilityMeasure (M.rowMeasure n)` from
  `productDesign.toMeasure`. For Lyapunov integrability, every active
  increment is integrable to fourth power on the finite probability space.
  Apply `Causalean.Stat.IndependentTriangularArray.lyapunov_clt` with `δ = 2`
  using the two limits from `GaussianArray`.

  The martingale row sum is pointwise `normalizedSum / sqrt (v₀ : ℝ)`:
  rewrite the range sum as a `Fin` sum, expand `standardizedIncrement`,
  and factor the constant. Obtain convergence of the standard-normal CDF
  at `t / sqrt (v₀ : ℝ)` from the CLT's `TendstoInLaw.tendsto` field and
  `Causalean.Stat.tendsto_cdf_at_of_tendsto`. Positive `sqrt v₀` makes
  the event for this threshold exactly `normalizedSum ≤ t`; finish with
  `normalizedCDF_eq_cdf` and `Causalean.Stat.cdf_gaussianReal_zero`.
  Directly comparing the two preimage events avoids a separate pushforward
  scaling lemma.
  -/
  classical
  letI : MeasurableSpace Y := ⊤
  haveI : MeasurableSingletonClass Y := ⟨fun _ => trivial⟩
  haveI hprob (n : ℕ) : IsProbabilityMeasure (M.rowMeasure n) := by
    change IsProbabilityMeasure (M.productDesign n).toMeasure
    infer_instance
  let A := M.standardizedArray
  have hclt := Causalean.Stat.IndependentTriangularArray.lyapunov_clt
    (A := A) (δ := 2) (by norm_num) (by
      intro n k hk
      exact Integrable.of_finite)
    M.standardizedArray_varianceSum_tendsto
    M.standardizedArray_lyapunovSum_two_tendsto
  have hspos : 0 < Real.sqrt (M.v₀ : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast M.variance_pos)
  have hsum (n : ℕ) (ys : Fin (M.N n) → Y) :
      A.toMartingale.rowSum n ys =
        M.normalizedSum n ys / Real.sqrt (M.v₀ : ℝ) := by
    simp only [Causalean.Stat.MartingaleDifferenceArray.rowSum,
      Causalean.Stat.IndependentTriangularArray.toMartingale,
      A, standardizedArray]
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [Finset.sum_apply]
    rw [show (∑ i : Fin (M.N n), M.standardizedIncrement n (i : ℕ) ys) =
        ∑ i : Fin (M.N n),
          (Real.sqrt (M.N n : ℝ) * Real.sqrt (M.v₀ : ℝ))⁻¹ * M.f n (ys i) by
      apply Finset.sum_congr rfl
      intro i hi
      simp [standardizedIncrement, i.isLt]]
    rw [← Finset.mul_sum]
    unfold normalizedSum scoreSum
    rw [mul_comm (Real.sqrt (M.N n : ℝ))⁻¹]
    ring
  have hcont : ContinuousAt (cdf (gaussianReal 0 (1 : NNReal)))
      (t / Real.sqrt (M.v₀ : ℝ)) :=
    (Causalean.Stat.continuous_cdf_gaussianReal_zero (by norm_num : (0 : NNReal) < 1)).continuousAt
  have hcdf := Causalean.Stat.tendsto_cdf_at_of_tendsto
    (νs := fun n => ⟨(M.rowMeasure n).map (A.toMartingale.rowSum n),
      Measure.isProbabilityMeasure_map (hclt.forall_aemeasurable n)⟩)
    (ν := ⟨gaussianReal 0 1, inferInstance⟩)
    (by simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using hclt.tendsto)
    hcont
  have hevent (n : ℕ) :
      (M.rowMeasure n).map (A.toMartingale.rowSum n) =
        (M.normalizedSumLaw n).map (fun x => x / Real.sqrt (M.v₀ : ℝ)) := by
    rw [normalizedSumLaw, Measure.map_map]
    · congr 1
      funext ys
      exact hsum n ys
    · exact (continuous_id.div_const _).measurable
    · exact measurable_of_finite _
  have hcdf_eq (n : ℕ) :
      cdf ((M.rowMeasure n).map (A.toMartingale.rowSum n))
        (t / Real.sqrt (M.v₀ : ℝ)) = M.normalizedCDF n t := by
    haveI : IsProbabilityMeasure (M.normalizedSumLaw n) :=
      Measure.isProbabilityMeasure_map (measurable_of_finite (M.normalizedSum n)).aemeasurable
    haveI : IsProbabilityMeasure
        ((M.normalizedSumLaw n).map (fun x => x / Real.sqrt (M.v₀ : ℝ))) :=
      Measure.isProbabilityMeasure_map (continuous_id.div_const _).measurable.aemeasurable
    rw [hevent, cdf_eq_real,
      MeasureTheory.map_measureReal_apply
        (f := fun x : ℝ => x / Real.sqrt (M.v₀ : ℝ))
        (continuous_id.div_const _).measurable measurableSet_Iic]
    have hset : (fun x : ℝ => x / Real.sqrt (M.v₀ : ℝ)) ⁻¹'
        Set.Iic (t / Real.sqrt (M.v₀ : ℝ)) = Set.Iic t := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic]
      exact div_le_div_iff_of_pos_right hspos
    rw [hset, ← cdf_eq_real, ← M.normalizedCDF_eq_cdf]
  simpa only [ProbabilityMeasure.coe_mk, hcdf_eq, Causalean.Stat.cdf_gaussianReal_zero
    (by norm_num : (0 : NNReal) < 1), Causalean.Stat.cdf_gaussianReal_zero M.variance_pos,
    NNReal.coe_one, Real.sqrt_one, div_one] using hcdf

end RowModel
end Causalean.Stat.CLT.FiniteIidTriangular
