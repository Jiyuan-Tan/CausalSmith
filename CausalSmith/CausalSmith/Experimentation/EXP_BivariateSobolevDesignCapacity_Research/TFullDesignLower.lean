module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CosineLegality
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.SigningPartition

/-! # The full-design prior lower bound

The explicit lower constant is chosen outside the sample and dimension quantifiers.
Every admissible covariate-dependent randomized original-sign law is covered. Finite
coefficient averaging gives the exact feature-energy identity, which is compared with
the pointwise minimum and the isotropic signing lemma. The explicit ceiling cutoff
then gives the published lower constant. Prior legality and isotropic signing retain
their separate proof obligations in the imported modules.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Uniform coefficient signs have diagonal second moments for any finite index type.](goal) -/
-- @node: coefficientSigns_product_integral
lemma coefficientSigns_product_integral {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    (∫ ξ, sgn (ξ i) * sgn (ξ j)
      ∂(PMF.uniformOfFintype (ι → Bool)).toMeasure) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    have hsq (ξ : ι → Bool) : sgn (ξ i) * sgn (ξ i) = 1 := by
      cases ξ i <;> norm_num [sgn]
    simp [hsq]
  · rw [if_neg hij, integral_fintype (Integrable.of_finite)]
    simp only [Measure.real,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply, smul_eq_mul]
    let e : (ι → Bool) ≃ (ι → Bool) :=
      { toFun := fun ξ => Function.update ξ i (!(ξ i))
        invFun := fun ξ => Function.update ξ i (!(ξ i))
        left_inv := by intro ξ; funext k; by_cases hk : k = i <;> simp [hk]
        right_inv := by intro ξ; funext k; by_cases hk : k = i <;> simp [hk] }
    have hsum := e.sum_comp (fun ξ =>
      ((Fintype.card (ι → Bool) : ℝ≥0∞)⁻¹).toReal * (sgn (ξ i) * sgn (ξ j)))
    have hi (ξ : ι → Bool) : sgn (e ξ i) = -sgn (ξ i) := by
      change sgn (Function.update ξ i (!(ξ i)) i) = _
      simp only [Function.update_self]
      cases ξ i <;> norm_num [sgn]
    have hj (ξ : ι → Bool) : e ξ j = ξ j :=
      Function.update_of_ne (Ne.symm hij) _ _
    simp only [hi, hj, neg_mul, mul_neg, Finset.sum_neg_distrib] at hsum
    linarith

/-- [ A finite independent coefficient prior averages a square to its diagonal energy.](goal) -/
-- @node: coefficientSigns_sum_second_moment
lemma coefficientSigns_sum_second_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) :
    (∫ ξ, (∑ i, sgn (ξ i) * u i) ^ 2
      ∂(PMF.uniformOfFintype (ι → Bool)).toMeasure) = ∑ i, u i ^ 2 := by
  have hexpand (ξ : ι → Bool) : (∑ i, sgn (ξ i) * u i) ^ 2 =
      ∑ i, ∑ j, u i * (sgn (ξ i) * sgn (ξ j)) * u j := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => Integrable.of_finite)]
  simp_rw [integral_mul_const, integral_const_mul, coefficientSigns_product_integral]
  simp [pow_two]

/-- [ The nonnegative finite prior has the same diagonal-energy identity.](goal) -/
-- @node: coefficientSigns_sum_second_moment_ennreal
lemma coefficientSigns_sum_second_moment_ennreal {ι : Type} [Fintype ι]
    [DecidableEq ι] (u : ι → ℝ) :
    (∑ ξ : ι → Bool, PMF.uniformOfFintype (ι → Bool) ξ *
      ENNReal.ofReal ((∑ i, sgn (ξ i) * u i) ^ 2)) =
        ENNReal.ofReal (∑ i, u i ^ 2) := by
  rw [← coefficientSigns_sum_second_moment u,
    ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
      (Filter.Eventually.of_forall (fun ξ => sq_nonneg _)), lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]

/-- [ Before averaging over the sample, coefficient averaging produces precisely the
squared feature-signing norm with the stated normalization.](goal) -/
-- @node: mXi_signed_sum_prior_second_moment
lemma mXi_signed_sum_prior_second_moment (n d L : ℕ) (s : ℝ)
    (x : Covariates n d) (z : Signs n) :
    (∑ ξ : PairIdx d L → Bool, PMF.uniformOfFintype (PairIdx d L → Bool) ξ *
      ENNReal.ofReal ((∑ i, sgn (z i) * mXi s L ξ (x i)) ^ 2)) =
    ENNReal.ofReal ((C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹ ^ 2) *
      ENNReal.ofReal (∑ α : PairIdx d L,
        (∑ i, sgn (z i) * pairFeature α (x i)) ^ 2) := by
  classical
  let c := (C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹
  have hexpand (ξ : PairIdx d L → Bool) :
      (∑ i, sgn (z i) * mXi s L ξ (x i)) =
        c * ∑ α, sgn (ξ α) * ∑ i, sgn (z i) * pairFeature α (x i) := by
    simp only [mXi, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro i _
    dsimp [c]
    ring
  simp_rw [hexpand, mul_pow, ENNReal.ofReal_mul (sq_nonneg c)]
  simp_rw [mul_left_comm _ (ENNReal.ofReal (c ^ 2))]
  rw [← Finset.mul_sum, coefficientSigns_sum_second_moment_ennreal]


/-- [ Coefficient averaging commutes with the fixed design and covariate integrals,
giving the exact prior-risk identity from the lower-bound roadmap.](goal) -/
-- @node: priorRisk_eq_feature_energy
lemma priorRisk_eq_feature_energy {n d : ℕ} (π : Design n d) (s : ℝ) :
    priorRisk π s =
      ENNReal.ofReal (4 / (n : ℝ)) *
      ENNReal.ofReal ((C0 * (priorCutoff n d : ℝ) ^ s *
        Real.sqrt (priorDimension d (priorCutoff n d)))⁻¹ ^ 2) *
      ∫⁻ x, ∫⁻ z, ENNReal.ofReal (∑ α : PairIdx d (priorCutoff n d),
        (∑ i, sgn (z i) * pairFeature α (x i)) ^ 2) ∂π.val x ∂covLaw n d := by
  classical
  let : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  let : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  let : IsProbabilityMeasure (covLaw n d) := by unfold covLaw; infer_instance
  let := π.property
  let L := priorCutoff n d
  let c := ENNReal.ofReal ((C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹ ^ 2)
  let μ := covLaw n d ⊗ₘ π.val
  have hm (ξ : PairIdx d L → Bool) : Measurable
      (fun ω : Covariates n d × Signs n =>
        ENNReal.ofReal ((∑ i, sgn (ω.2 i) * mXi s L ξ (ω.1 i)) ^ 2)) := by
    fun_prop
  have he : Measurable (fun ω : Covariates n d × Signs n =>
      ENNReal.ofReal (∑ α : PairIdx d L,
        (∑ i, sgn (ω.2 i) * pairFeature α (ω.1 i)) ^ 2)) := by
    fun_prop
  have hloss (ξ : PairIdx d L → Bool) : loss π (mXi s L ξ) =
      ENNReal.ofReal (4 / (n : ℝ)) * ∫⁻ ω,
        ENNReal.ofReal ((∑ i, sgn (ω.2 i) * mXi s L ξ (ω.1 i)) ^ 2) ∂μ := by
    rw [Measure.lintegral_compProd (hm ξ)]
    rfl
  change (∑ ξ, PMF.uniformOfFintype (PairIdx d L → Bool) ξ * loss π (mXi s L ξ)) = _
  simp_rw [hloss, mul_left_comm _ (ENNReal.ofReal (4 / (n : ℝ)))]
  rw [← Finset.mul_sum]
  have havg : (∑ ξ : PairIdx d L → Bool,
      PMF.uniformOfFintype (PairIdx d L → Bool) ξ *
        ∫⁻ ω, ENNReal.ofReal ((∑ i, sgn (ω.2 i) * mXi s L ξ (ω.1 i)) ^ 2) ∂μ) =
      c * ∫⁻ ω, ENNReal.ofReal (∑ α : PairIdx d L,
        (∑ i, sgn (ω.2 i) * pairFeature α (ω.1 i)) ^ 2) ∂μ := by
    simp_rw [← lintegral_const_mul' _ _ (PMF.apply_ne_top _ _)]
    rw [← lintegral_finsetSum Finset.univ (fun ξ _ => (hm ξ).const_mul _)]
    simp_rw [mXi_signed_sum_prior_second_moment]
    exact lintegral_const_mul c he
  rw [havg, Measure.lintegral_compProd he]
  simp only [c, L, mul_assoc]

/-- [ Any covariate-dependent randomized design dominates the pointwise minimum
over all original sign vectors. Fairness is not needed for this comparison.](goal) -/
-- @node: priorRisk_ge_min_feature_energy
lemma priorRisk_ge_min_feature_energy {n d : ℕ} (π : Design n d) (s : ℝ) :
    ENNReal.ofReal (4 / (n : ℝ)) *
      ENNReal.ofReal ((C0 * (priorCutoff n d : ℝ) ^ s *
        Real.sqrt (priorDimension d (priorCutoff n d)))⁻¹ ^ 2) *
      (∫⁻ x : Covariates n d, ⨅ z : Signs n,
        ENNReal.ofReal (∑ α : PairIdx d (priorCutoff n d),
          (∑ i, sgn (z i) * pairFeature α (x i)) ^ 2) ∂covLaw n d) ≤
        priorRisk π s := by
  rw [priorRisk_eq_feature_energy]
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro x
  let := π.property
  calc
    (⨅ z : Signs n, ENNReal.ofReal (∑ α : PairIdx d (priorCutoff n d),
        (∑ i, sgn (z i) * pairFeature α (x i)) ^ 2)) =
      ∫⁻ _z : Signs n, ⨅ z : Signs n,
        ENNReal.ofReal (∑ α : PairIdx d (priorCutoff n d),
          (∑ i, sgn (z i) * pairFeature α (x i)) ^ 2) ∂π.val x := by simp
    _ ≤ _ := lintegral_mono (fun z => iInf_le _ z)

/-- The prescribed cutoff has enough features for the isotropic signing threshold. Under [the stated conditions](hyp:hd), [the asserted mathematical result follows](goal). -/
-- @node: priorCutoff_dimension_lower
lemma priorCutoff_dimension_lower (n d : ℕ) (hd : 2 ≤ d) :
    4096 * n ≤ priorDimension d (priorCutoff n d) := by
  have hB : (0 : ℝ) < pairCount d := by
    exact_mod_cast (Nat.choose_pos hd : 0 < d.choose 2)
  have hL : Real.sqrt (4096 * (n : ℝ) / pairCount d) ≤ (priorCutoff n d : ℝ) := by
    apply (Nat.le_ceil _).trans
    unfold priorCutoff
    exact_mod_cast (le_max_right 1 ⌈Real.sqrt (4096 * (n : ℝ) / pairCount d)⌉₊)
  have hsq := Real.sq_sqrt (show 0 ≤ 4096 * (n : ℝ) / pairCount d by positivity)
  have hdimension : 4096 * (n : ℝ) ≤
      (pairCount d : ℝ) * (priorCutoff n d : ℝ) ^ 2 := by
    have hLsq : 4096 * (n : ℝ) / pairCount d ≤ (priorCutoff n d : ℝ) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (4096 * (n : ℝ) / pairCount d)]
    simpa only [mul_comm] using (div_le_iff₀ hB).mp hLsq
  exact_mod_cast hdimension

/-- The ceiling cutoff loses only the explicit factor 16384 in squared frequency. [The asserted mathematical result follows](goal). -/
-- @node: priorCutoff_sq_upper
lemma priorCutoff_sq_upper (n d : ℕ) :
    (priorCutoff n d : ℝ) ^ 2 ≤ 16384 * max 1 ((n : ℝ) / pairCount d) := by
  let q : ℝ := 4096 * (n : ℝ) / pairCount d
  let R : ℝ := max 1 ((n : ℝ) / pairCount d)
  have hR : 1 ≤ R := le_max_left _ _
  have hratio : (n : ℝ) / pairCount d ≤ R := le_max_right _ _
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hs : Real.sqrt q ≤ 64 * Real.sqrt R := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ R)]
      dsimp [q]
      rw [mul_div_assoc]
      nlinarith
  have hceil : (⌈Real.sqrt q⌉₊ : ℝ) ≤ Real.sqrt q + 1 :=
    (Nat.ceil_lt_add_one (Real.sqrt_nonneg q)).le
  have hL : (priorCutoff n d : ℝ) ≤ 64 * Real.sqrt R + 1 := by
    simp only [priorCutoff, Nat.cast_max, Nat.cast_one]
    apply max_le
    · have hsR := Real.sqrt_nonneg R
      linarith
    · exact hceil.trans (by linarith)
  have hsR : 1 ≤ Real.sqrt R := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by simpa using hR)
  have hL' : (priorCutoff n d : ℝ) ≤ 128 * Real.sqrt R := by linarith
  have hRsq := Real.sq_sqrt (by positivity : 0 ≤ R)
  change (priorCutoff n d : ℝ) ^ 2 ≤ 16384 * R
  nlinarith [mul_nonneg (sub_nonneg.mpr hL')
    (show 0 ≤ 128 * Real.sqrt R + (priorCutoff n d : ℝ) by positivity)]

/-- The cosine feature map transports independent uniform rows to the isotropic
row law, so the signing lemma lower-bounds the original-sample minimum. Under [the stated conditions](hyp:hContraction_of_gate,hn,hd), [the asserted mathematical result follows](goal). -/
-- @node: prior_min_feature_energy_lower
lemma prior_min_feature_energy_lower (hContraction_of_gate : ClassicalRademacherContraction)
    (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) :
    ENNReal.ofReal ((n : ℝ) * priorDimension d (priorCutoff n d) / 2) ≤
      ∫⁻ x : Covariates n d, ⨅ z : Signs n,
        ENNReal.ofReal (∑ α : PairIdx d (priorCutoff n d),
          (∑ i, sgn (z i) * pairFeature α (x i)) ^ 2) ∂covLaw n d := by
  classical
  let : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  let : IsProbabilityMeasure (cubeMeasure d) := by unfold cubeMeasure; infer_instance
  let : IsProbabilityMeasure (covLaw n d) := by unfold covLaw; infer_instance
  let L := priorCutoff n d
  let M := priorDimension d L
  let e : PairIdx d L ≃ Fin M := Fintype.equivFinOfCardEq (pairIdx_card d L)
  let V : Cube d → EuclideanSpace ℝ (Fin M) :=
    fun x => WithLp.toLp 2 (fun a => pairFeature (e.symm a) x)
  have hV : Measurable V := by dsimp [V]; fun_prop
  let P := (cubeMeasure d).map V
  let : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map hV.aemeasurable
  have hmom (a : Fin M) : MemLp (fun v : EuclideanSpace ℝ (Fin M) => v a) 2 P := by
    apply (memLp_map_measure_iff (by fun_prop) hV.aemeasurable).mpr
    exact pairFeature_memLp (e.symm a)
  have hiso (a b : Fin M) : (∫ v, v a * v b ∂P) = if a = b then 1 else 0 := by
    rw [integral_map hV.aemeasurable (by fun_prop)]
    change (∫ x, pairFeature (e.symm a) x * pairFeature (e.symm b) x
      ∂cubeMeasure d) = _
    rw [pairFeature_cube_inner_product]
    simp only [e.symm.injective.eq_iff]
  have hlarge : 4096 * n ≤ M := priorCutoff_dimension_lower n d hd
  have hM : 0 < M := lt_of_lt_of_le (by omega) hlarge
  have hbound := (isotropic_row_signing hContraction_of_gate M n hM P hmom hiso).2 hlarge
  have hmap : (covLaw n d).map (fun x i => V (x i)) =
      Measure.pi (fun _ : Fin n => P) := by
    exact Measure.pi_map_pi (fun _ => hV.aemeasurable)
  have hmeas : Measurable (fun vs : Fin n → EuclideanSpace ℝ (Fin M) =>
      ⨅ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ^ 2) := by
    apply Measurable.iInf
    intro z
    fun_prop
  have hVs : Measurable (fun x : Covariates n d => fun i => V (x i)) :=
    measurable_pi_lambda _ (fun i => hV.comp (measurable_pi_apply i))
  rw [← hmap, integral_map hVs.aemeasurable hmeas.aestronglyMeasurable] at hbound
  have hnorm (x : Covariates n d) (z : Signs n) :
      ‖∑ i, sgn (z i) • V (x i)‖ ^ 2 =
        ∑ α : PairIdx d L, (∑ i, sgn (z i) * pairFeature α (x i)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    change (∑ a : Fin M, (∑ i, sgn (z i) * pairFeature (e.symm a) (x i)) ^ 2) = _
    exact e.symm.sum_comp (fun α => (∑ i, sgn (z i) * pairFeature α (x i)) ^ 2)
  simp_rw [hnorm] at hbound
  have hpos : 0 < (n : ℝ) * M / 2 := by positivity
  have hint : Integrable (fun x : Covariates n d =>
      ⨅ z : Signs n, ∑ α : PairIdx d L,
        (∑ i, sgn (z i) * pairFeature α (x i)) ^ 2) (covLaw n d) := by
    by_contra h
    rw [integral_undef h] at hbound
    linarith
  have hnonneg (x : Covariates n d) : 0 ≤
      ⨅ z : Signs n, ∑ α : PairIdx d L,
        (∑ i, sgn (z i) * pairFeature α (x i)) ^ 2 := by
    apply le_ciInf
    intro z
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    ENNReal.ofReal ((n : ℝ) * M / 2) ≤
        ENNReal.ofReal (∫ x : Covariates n d, ⨅ z : Signs n,
          ∑ α : PairIdx d L, (∑ i, sgn (z i) * pairFeature α (x i)) ^ 2 ∂covLaw n d) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = _ := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnonneg)]
      simp only [ENNReal.ofReal_iInf]
      rfl

/-- [ The ceiling comparison yields the paper's explicit lower constant and scale.](goal) Under [the stated conditions](hyp:hn,hd,hs). -/
-- @node: priorCutoff_normalized_lower
lemma priorCutoff_normalized_lower (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (s : ℝ) (hs : 0 < s) :
    cLower s * bScale n d s ≤
      2 / (C0 ^ 2 * ((priorCutoff n d : ℝ) ^ s) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hBpos : (0 : ℝ) < pairCount d := by
    exact_mod_cast (Nat.choose_pos hd : 0 < d.choose 2)
  have hLpos : (0 : ℝ) < priorCutoff n d := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _))
  have hC0 : C0 ^ 2 = 48 + 32 * Real.pi ^ 2 := by
    exact Real.sq_sqrt (by positivity)
  have hCpos : 0 < C0 := by unfold C0; positivity
  let R := max 1 ((n : ℝ) / pairCount d)
  let K := (16384 : ℝ) ^ s
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hpower : ((priorCutoff n d : ℝ) ^ s) ^ 2 ≤ K * R ^ s := by
    rw [Real.rpow_pow_comm (Nat.cast_nonneg _) s 2]
    calc
      ((priorCutoff n d : ℝ) ^ 2) ^ s ≤ (16384 * R) ^ s :=
        Real.rpow_le_rpow (sq_nonneg _) (priorCutoff_sq_upper n d) hs.le
      _ = K * R ^ s := Real.mul_rpow (by norm_num) (by dsimp [R]; positivity)
  have hb : 0 ≤ bScale n d s := by unfold bScale; positivity
  have hscale : bScale n d s * R ^ s ≤ 1 := by
    by_cases hr : (n : ℝ) / pairCount d ≤ 1
    · simp only [R, max_eq_left hr, Real.one_rpow, mul_one]
      exact min_le_left _ _
    · have hr' : 1 ≤ (n : ℝ) / pairCount d := le_of_lt (lt_of_not_ge hr)
      rw [show R = (n : ℝ) / pairCount d from max_eq_right hr']
      calc
        bScale n d s * ((n : ℝ) / pairCount d) ^ s ≤
            ((pairCount d : ℝ) / n) ^ s * ((n : ℝ) / pairCount d) ^ s :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = 1 := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          have hrat : ((pairCount d : ℝ) / n) * ((n : ℝ) / pairCount d) = 1 := by
            field_simp
          rw [hrat, Real.one_rpow]
  have hprod : ((priorCutoff n d : ℝ) ^ s) ^ 2 * bScale n d s ≤ K := by
    calc
      _ ≤ (K * R ^ s) * bScale n d s := mul_le_mul_of_nonneg_right hpower hb
      _ = K * (bScale n d s * R ^ s) := by ring
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hscale hKpos.le
      _ = K := mul_one _
  unfold cLower
  rw [← hC0, div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  convert mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 * C0 ^ 2 by positivity) using 1 <;>
    (try dsimp [K]) <;> ring

/-- [ After isotropic signing, normalization cancels the original sample size and
feature dimension, leaving the inverse-frequency lower bound.](goal) Under [the stated conditions](hyp:hContraction_of_gate,hn,hd). -/
-- @node: priorRisk_ge_normalized_cutoff
lemma priorRisk_ge_normalized_cutoff (hContraction_of_gate : ClassicalRademacherContraction)
    (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) (s : ℝ) (π : Design n d) :
    ENNReal.ofReal (2 / (C0 ^ 2 * ((priorCutoff n d : ℝ) ^ s) ^ 2)) ≤
      priorRisk π s := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLpos : (0 : ℝ) < priorCutoff n d := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _))
  have hMpos : (0 : ℝ) < priorDimension d (priorCutoff n d) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 4096 * n)
      (priorCutoff_dimension_lower n d hd))
  have hCpos : 0 < C0 := by unfold C0; positivity
  have hsqrt := Real.sq_sqrt hMpos.le
  have hcoeff : ENNReal.ofReal (4 / (n : ℝ)) *
      ENNReal.ofReal ((C0 * (priorCutoff n d : ℝ) ^ s *
        Real.sqrt (priorDimension d (priorCutoff n d)))⁻¹ ^ 2) *
      ENNReal.ofReal ((n : ℝ) * priorDimension d (priorCutoff n d) / 2) =
        ENNReal.ofReal (2 / (C0 ^ 2 * ((priorCutoff n d : ℝ) ^ s) ^ 2)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have htpos : 0 < (priorCutoff n d : ℝ) ^ s := Real.rpow_pos_of_pos hLpos s
    have hspos : 0 < Real.sqrt (priorDimension d (priorCutoff n d)) :=
      Real.sqrt_pos.2 hMpos
    field_simp
    nlinarith
  rw [← hcoeff]
  exact (mul_le_mul' le_rfl
    (prior_min_feature_energy_lower hContraction_of_gate n d hn hd)).trans
      (priorRisk_ge_min_feature_energy π s)

/-- [ A finite coefficient prior supported on the legal class cannot exceed the
fixed-function supremum, even when risks are infinite.](goal) Under [the stated conditions](hyp:hlegal). -/
-- @node: priorRisk_le_worstLoss_of_legal
lemma priorRisk_le_worstLoss_of_legal {n d : ℕ} (π : Design n d) (s : ℝ)
    (hlegal : ∀ ξ : PairIdx d (priorCutoff n d) → Bool,
      ∃ hm : Measurable (mXi s (priorCutoff n d) ξ) ∧
        MemLp (mXi s (priorCutoff n d) ξ) 2 (cubeMeasure d) ∧
        (∫ x, mXi s (priorCutoff n d) ξ x ∂cubeMeasure d) = 0,
        SobolevClass d s ⟨mXi s (priorCutoff n d) ξ, hm⟩) :
    priorRisk π s ≤ worstLoss π s := by
  classical
  have hatom (ξ : PairIdx d (priorCutoff n d) → Bool) :
      loss π (mXi s (priorCutoff n d) ξ) ≤ worstLoss π s := by
    obtain ⟨hm, hclass⟩ := hlegal ξ
    exact le_iSup (fun m : {m : CenteredL2Fn d // SobolevClass d s m} =>
      loss π m.val.val) ⟨⟨mXi s (priorCutoff n d) ξ, hm⟩, hclass⟩
  have hmass : (∑ ξ, cosinePrior n d s ξ) = 1 := by
    simpa only [tsum_fintype] using (cosinePrior n d s).tsum_coe
  calc
    priorRisk π s ≤ ∑ ξ, cosinePrior n d s ξ * worstLoss π s :=
      Finset.sum_le_sum (fun ξ _ => mul_le_mul' le_rfl (hatom ξ))
    _ = worstLoss π s := by rw [← Finset.sum_mul, hmass, one_mul]

/-- [ A lower bound for every design's legal finite prior transfers to full capacity.](goal) Under [the stated conditions](hyp:hd,hs,hs1,c,hprior). -/
-- @node: capacity_lower_of_priorRisk
lemma capacity_lower_of_priorRisk (n d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) (c : ℝ≥0∞)
    (hprior : ∀ π : Design n d, DesignClass n d π → c ≤ priorRisk π s) :
    c ≤ capacity n d s := by
  apply Causalean.Stat.le_minimaxValueENNReal
  intro π
  exact (hprior π.val π.property).trans
    (priorRisk_le_worstLoss_of_legal π.val s
      (cosinePrior_legal_and_isotropic.1 d (priorCutoff n d) hd
        (le_max_left _ _) s hs hs1))

-- @node: thm:full-design-lower
/-- The independent legal cosine prior lower-bounds every design and hence capacity. This uses [the hContraction_of_gate hypothesis](hyp:hContraction_of_gate), [the stated conclusion](goal). -/
theorem full_design_lower (hContraction_of_gate : ClassicalRademacherContraction) :
    ∀ s : ℝ, 0 < s → s ≤ 1 →
      0 < cLower s ∧ ∀ n d : ℕ, 2 ≤ n → 2 ≤ d →
        (∀ π : Design n d, DesignClass n d π →
          ENNReal.ofReal (cLower s * bScale n d s) ≤ priorRisk π s) ∧
        ENNReal.ofReal (cLower s * bScale n d s) ≤ capacity n d s := by
  intro s hs hs1
  have hc : 0 < cLower s := by unfold cLower; positivity
  refine ⟨hc, ?_⟩
  intro n d hn hd
  have hprior : ∀ π : Design n d, DesignClass n d π →
      ENNReal.ofReal (cLower s * bScale n d s) ≤ priorRisk π s := by
    intro π _hπ
    exact (ENNReal.ofReal_le_ofReal (priorCutoff_normalized_lower n d hn hd s hs)).trans
      (priorRisk_ge_normalized_cutoff hContraction_of_gate n d hn hd s π)
  exact ⟨hprior, capacity_lower_of_priorRisk n d hd s hs hs1 _ hprior⟩

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
