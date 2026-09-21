import Causalean.Estimation.Efficiency.AsymptoticLanConvolution.IIDDQM

/-!
# LAN expansion for i.i.d. DQM models

This module completes the product-likelihood and triangular-array argument that turns the dominated i.i.d. quadratic-mean differentiability interface into local asymptotic normality.  It supplies the score central-limit step, the log-likelihood expansion, and the reusable LAN theorem.
-/

namespace Causalean.Estimation.Efficiency.AsymptoticLanConvolution

open Filter MeasureTheory Topology
open scoped RealInnerProductSpace

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

variable {M : DominatedIIDModel X H}

namespace IIDQuadraticMeanDifferentiable

private theorem sqrtLikelihoodIncrement_measurable
    (qmd : IIDQuadraticMeanDifferentiable M) (n : ℕ) (h : H) :
    Measurable (qmd.sqrtLikelihoodIncrement n h) := by
  have hsqrt_meas (u : H) : Measurable (M.sqrtDensity u) := by
    unfold DominatedIIDModel.sqrtDensity
    exact Real.continuous_sqrt.measurable.comp
      (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _))
  have hzero : MeasurableSet {x | M.sqrtDensity 0 x = 0} :=
    (hsqrt_meas 0) (measurableSet_singleton 0)
  unfold sqrtLikelihoodIncrement
  apply Measurable.ite hzero measurable_const
  exact (((hsqrt_meas _).div (hsqrt_meas 0)).sub_const 1).const_mul 2

private theorem projectedScore_memLp
    (qmd : IIDQuadraticMeanDifferentiable M) (h : H) :
    MemLp (fun x => inner ℝ h (qmd.score x)) 2 (M.law 0) := by
  apply (memLp_two_iff_integrable_sq_norm
    (qmd.score_measurable.const_inner (c := h)).aestronglyMeasurable).2
  refine Integrable.mono' (qmd.score_squareIntegrable.const_mul (‖h‖ ^ 2))
    ((qmd.score_measurable.const_inner (c := h)).norm.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  simp only [norm_pow, Real.norm_eq_abs, abs_abs]
  calc
    |inner ℝ h (qmd.score x)| ^ 2
        ≤ (‖h‖ * ‖qmd.score x‖) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
        (abs_real_inner_le_norm h (qmd.score x))
    _ = ‖h‖ ^ 2 * ‖qmd.score x‖ ^ 2 := by ring

private theorem sqrtLikelihoodIncrement_memLp
    (qmd : IIDQuadraticMeanDifferentiable M) (n : ℕ) (h : H) :
    MemLp (qmd.sqrtLikelihoodIncrement n h) 2 (M.law 0) := by
  letI : SigmaFinite M.dominating := M.dominating_sigmaFinite
  let _ : IsProbabilityMeasure (M.law 0) := M.probability 0
  have hp_mem (u : H) : MemLp (M.sqrtDensity u) 2 M.dominating := by
    have hpmeas : Measurable (M.sqrtDensity u) := by
      unfold DominatedIIDModel.sqrtDensity
      exact Real.continuous_sqrt.measurable.comp
        (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _))
    apply (memLp_two_iff_integrable_sq_norm hpmeas.aestronglyMeasurable).2
    let _ : IsProbabilityMeasure (M.law u) := M.probability u
    refine (Measure.integrable_toReal_rnDeriv (μ := M.law u)
      (ν := M.dominating)).congr ?_
    filter_upwards [] with x
    simp only [DominatedIIDModel.sqrtDensity, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg]
  let u := (Real.sqrt (n : ℝ))⁻¹ • h
  have hdiff : Integrable (fun x =>
      4 * (M.sqrtDensity u x - M.sqrtDensity 0 x) ^ 2) M.dominating := by
    have hm := (hp_mem u).sub (hp_mem 0)
    have hi := (memLp_two_iff_integrable_sq_norm hm.1).1 hm
    exact (hi.congr (ae_of_all _ fun x => by
      simp only [Pi.sub_apply, Real.norm_eq_abs, sq_abs])).const_mul 4
  have hweighted : Integrable (fun x =>
      ((M.law 0).rnDeriv M.dominating x).toReal *
        qmd.sqrtLikelihoodIncrement n h x ^ 2) M.dominating := by
    refine Integrable.mono' hdiff
      (((ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _)).mul
        ((qmd.sqrtLikelihoodIncrement_measurable n h).pow_const 2)).aestronglyMeasurable) ?_
    filter_upwards [] with x
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)),
      abs_of_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))]
    rw [← Real.sq_sqrt ENNReal.toReal_nonneg]
    change M.sqrtDensity 0 x ^ 2 * qmd.sqrtLikelihoodIncrement n h x ^ 2 ≤ _
    by_cases hp : M.sqrtDensity 0 x = 0
    · simp [hp, sq_nonneg]
    · simp only [sqrtLikelihoodIncrement, hp, if_false, u]
      field_simp
      ring_nf
      exact le_rfl
  apply (memLp_two_iff_integrable_sq_norm
    (qmd.sqrtLikelihoodIncrement_measurable n h).aestronglyMeasurable).2
  have hi := (integrable_toReal_rnDeriv_mul_iff
    (M.absolutelyContinuous 0)).1 hweighted
  exact hi.congr (ae_of_all _ fun x => by
    simp only [Real.norm_eq_abs, sq_abs])

private theorem norm_toLp_sq_eq_integral_sq {f : X → ℝ}
    {μ : Measure X} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, Real.inner_apply, real_inner_self_eq_norm_sq,
    Real.norm_eq_abs, sq_abs]

private theorem sqrtLikelihoodIncrement_moments
    (qmd : IIDQuadraticMeanDifferentiable M) (h : H)
    (hincrement : Tendsto (fun n : ℕ => (n : ℝ) * ∫ x,
      (qmd.sqrtLikelihoodIncrement n h x -
        (Real.sqrt (n : ℝ))⁻¹ * inner ℝ h (qmd.score x)) ^ 2 ∂M.law 0)
      atTop (𝓝 0))
    (hsingular : Tendsto (fun n : ℕ => (n : ℝ) *
      (M.law ((Real.sqrt (n : ℝ))⁻¹ • h)
        {x | M.sqrtDensity 0 x = 0}).toReal) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ x,
      qmd.sqrtLikelihoodIncrement n h x ^ 2 ∂M.law 0)
        atTop (𝓝 (qmd.information M h h)) ∧
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ x,
      qmd.sqrtLikelihoodIncrement n h x ∂M.law 0)
        atTop (𝓝 (-(1 / 4 : ℝ) * qmd.information M h h)) := by
  -- The first limit follows by comparing `Wₙ` in `L²` with the projected score.  For the
  -- mean, integrate the exact identity
  -- `E Wₙ + (1/4) E Wₙ² = - localLaw {sqrtDensity 0 = 0}` and use `hsingular`.
  let _ : IsProbabilityMeasure (M.law 0) := M.probability 0
  let W (n : ℕ) : X → ℝ := qmd.sqrtLikelihoodIncrement n h
  let S : X → ℝ := fun x => inner ℝ h (qmd.score x)
  have hW (n : ℕ) : MemLp (W n) 2 (M.law 0) :=
    qmd.sqrtLikelihoodIncrement_memLp n h
  have hS : MemLp S 2 (M.law 0) := qmd.projectedScore_memLp h
  let F (n : ℕ) : Lp ℝ 2 (M.law 0) :=
    Real.sqrt (n : ℝ) • (hW n).toLp (W n)
  let G : Lp ℝ 2 (M.law 0) := hS.toLp S
  have hnorm (n : ℕ) (hn : 0 < n) :
      ‖F n - G‖ ^ 2 = (n : ℝ) * ∫ x,
        (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂M.law 0 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(hW n).coeFn_toLp, hS.coeFn_toLp,
      Lp.coeFn_smul (Real.sqrt (n : ℝ)) ((hW n).toLp (W n)),
      Lp.coeFn_sub (F n) G] with x hxW hxS hxsmul hxsub
    simp only [F, G, hxsub, Pi.sub_apply, hxsmul, Pi.smul_apply, hxW, hxS, smul_eq_mul,
      Real.inner_apply,
      real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
    rw [show Real.sqrt (n : ℝ) * W n x - S x =
        Real.sqrt (n : ℝ) *
          (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) by field_simp]
    rw [mul_pow, Real.sq_sqrt hnR.le]
  have hFGsq : Tendsto (fun n => ‖F n - G‖ ^ 2) atTop (𝓝 0) := by
    apply hincrement.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hnorm n hn).symm
  have hFGnorm : Tendsto (fun n => ‖F n - G‖) atTop (𝓝 0) := by
    have hs := hFGsq.sqrt
    simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hs
  have hFt : Tendsto F atTop (𝓝 G) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hFGnorm
  have hnormF : Tendsto (fun n => ‖F n‖ ^ 2) atTop (𝓝 (‖G‖ ^ 2)) :=
    hFt.norm.pow 2
  have hF_sq (n : ℕ) : ‖F n‖ ^ 2 =
      (n : ℝ) * ∫ x, W n x ^ 2 ∂M.law 0 := by
    simp only [F, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
    rw [norm_toLp_sq_eq_integral_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hG_sq : ‖G‖ ^ 2 = qmd.information M h h := by
    rw [information_apply]
    simp only [G, norm_toLp_sq_eq_integral_sq, S]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hsecond : Tendsto (fun n : ℕ => (n : ℝ) * ∫ x,
      qmd.sqrtLikelihoodIncrement n h x ^ 2 ∂M.law 0)
      atTop (𝓝 (qmd.information M h h)) := by
    simpa only [W, hF_sq, hG_sq] using hnormF
  refine ⟨hsecond, ?_⟩
  letI : SigmaFinite M.dominating := M.dominating_sigmaFinite
  let Z : Set X := {x | M.sqrtDensity 0 x = 0}
  have hZ : MeasurableSet Z := by
    exact (Real.continuous_sqrt.measurable.comp
      (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _)))
      (measurableSet_singleton 0)
  have hidentity (n : ℕ) :
      (∫ x, W n x ∂M.law 0) + (1 / 4 : ℝ) * ∫ x, W n x ^ 2 ∂M.law 0 =
        -(M.law ((Real.sqrt (n : ℝ))⁻¹ • h) Z).toReal := by
    let u : H := (Real.sqrt (n : ℝ))⁻¹ • h
    let _ : IsProbabilityMeasure (M.law u) := M.probability u
    let d0 : X → ℝ := fun x => ((M.law 0).rnDeriv M.dominating x).toReal
    let du : X → ℝ := fun x => ((M.law u).rnDeriv M.dominating x).toReal
    have hWint : Integrable (W n) (M.law 0) := (hW n).integrable (by norm_num)
    have hWsq : Integrable (fun x => W n x ^ 2) (M.law 0) := by
      have hi := (memLp_two_iff_integrable_sq_norm (hW n).1).1 (hW n)
      exact hi.congr (ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs, sq_abs])
    have hd0int : Integrable d0 M.dominating := by
      exact Measure.integrable_toReal_rnDeriv
    have hduint : Integrable du M.dominating := by
      exact Measure.integrable_toReal_rnDeriv
    have hpoint : (fun x => d0 x * (W n x + (1 / 4 : ℝ) * W n x ^ 2)) =
        fun x => du x - d0 x - Z.indicator du x := by
      funext x
      by_cases hp : M.sqrtDensity 0 x = 0
      · have hd0 : d0 x = 0 := by
          apply (Real.sqrt_eq_zero ENNReal.toReal_nonneg).mp
          exact hp
        simp [W, sqrtLikelihoodIncrement, hp, Z, hd0]
      · have hsq0 : M.sqrtDensity 0 x ^ 2 = d0 x := by
          exact Real.sq_sqrt ENNReal.toReal_nonneg
        have hsqu : M.sqrtDensity u x ^ 2 = du x := by
          exact Real.sq_sqrt ENNReal.toReal_nonneg
        have hxZ : x ∉ Z := hp
        simp only [W, sqrtLikelihoodIncrement, hp, if_false, Z,
          Set.indicator_of_notMem hxZ]
        rw [← hsq0, ← hsqu]
        field_simp
        simp only [u]
        ring
    calc
      (∫ x, W n x ∂M.law 0) + (1 / 4 : ℝ) * ∫ x, W n x ^ 2 ∂M.law 0 =
          ∫ x, W n x + (1 / 4 : ℝ) * W n x ^ 2 ∂M.law 0 := by
        rw [integral_add hWint (hWsq.const_mul _), integral_const_mul]
      _ = ∫ x, d0 x * (W n x + (1 / 4 : ℝ) * W n x ^ 2) ∂M.dominating := by
        exact (integral_toReal_rnDeriv_mul (M.absolutelyContinuous 0)).symm
      _ = ∫ x, du x - d0 x - Z.indicator du x ∂M.dominating := by
        rw [hpoint]
      _ = (∫ x, du x ∂M.dominating) - (∫ x, d0 x ∂M.dominating) -
          ∫ x, Z.indicator du x ∂M.dominating := by
        calc
          (∫ x, du x - d0 x - Z.indicator du x ∂M.dominating) =
              ∫ x, (du - d0) x - Z.indicator du x ∂M.dominating := by rfl
          _ = (∫ x, (du - d0) x ∂M.dominating) -
              ∫ x, Z.indicator du x ∂M.dominating :=
            integral_sub (hduint.sub hd0int) (hduint.indicator hZ)
          _ = _ := by
            rw [show (∫ x, (du - d0) x ∂M.dominating) =
              ∫ x, du x - d0 x ∂M.dominating by rfl,
              integral_sub hduint hd0int]
      _ = -(M.law u Z).toReal := by
        let _ : IsProbabilityMeasure (M.law u) := M.probability u
        rw [integral_indicator hZ,
          Measure.setIntegral_toReal_rnDeriv (M.absolutelyContinuous u),
          Measure.integral_toReal_rnDeriv (M.absolutelyContinuous u),
          Measure.integral_toReal_rnDeriv (M.absolutelyContinuous 0)]
        simp
        rfl
  have hmean_eq (n : ℕ) : (n : ℝ) * ∫ x, W n x ∂M.law 0 =
      -((n : ℝ) * (M.law ((Real.sqrt (n : ℝ))⁻¹ • h) Z).toReal) -
        (1 / 4 : ℝ) * ((n : ℝ) * ∫ x, W n x ^ 2 ∂M.law 0) := by
    have hi := hidentity n
    linear_combination (n : ℝ) * hi
  have ht := hsingular.neg.sub (hsecond.const_mul (1 / 4 : ℝ))
  have ht' : Tendsto (fun n : ℕ =>
      -((n : ℝ) * (M.law ((Real.sqrt (n : ℝ))⁻¹ • h) Z).toReal) -
        (1 / 4 : ℝ) * ((n : ℝ) * ∫ x, W n x ^ 2 ∂M.law 0))
      atTop (𝓝 (-(1 / 4 : ℝ) * qmd.information M h h)) := by
    convert ht using 1
    congr 1
    ring
  exact ht'.congr' (Filter.Eventually.of_forall fun n => (hmean_eq n).symm)

private theorem tendstoInProbability_add_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (A B : ∀ n, Ω n → ℝ)
    (hA : TendstoInProbability P A 0) (hB : TendstoInProbability P B 0) :
    TendstoInProbability P (fun n x => A n x + B n x) 0 := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hAt := hA (ε / 2) hhalf
  have hBt := hB (ε / 2) hhalf
  have hsum : Tendsto (fun n =>
      P n {x | ε / 2 ≤ |A n x|} + P n {x | ε / 2 ≤ |B n x|}) atTop (𝓝 0) := by
    simpa only [sub_zero, zero_add] using hAt.add hBt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun _ : ℕ => (0 : ENNReal))
      (h := fun n => P n {x | ε / 2 ≤ |A n x|} + P n {x | ε / 2 ≤ |B n x|})
      tendsto_const_nhds hsum
  · exact Filter.Eventually.of_forall fun n => bot_le
  · refine Filter.Eventually.of_forall fun n => ?_
    calc
      P n {x | ε ≤ |(A n x + B n x) - 0|} ≤
          P n ({x | ε / 2 ≤ |A n x|} ∪ {x | ε / 2 ≤ |B n x|}) := by
        apply measure_mono
        intro x hx
        simp only [Set.mem_ofPred_eq, sub_zero] at hx
        by_cases hAx : ε / 2 ≤ |A n x|
        · exact Or.inl hAx
        · right
          have hAlt : |A n x| < ε / 2 := lt_of_not_ge hAx
          by_contra hBx
          have hBlt : |B n x| < ε / 2 := lt_of_not_ge hBx
          have habs := abs_add_le (A n x) (B n x)
          linarith
      _ ≤ P n {x | ε / 2 ≤ |A n x|} + P n {x | ε / 2 ≤ |B n x|} :=
        measure_union_le _ _

private theorem tendstoInProbability_const_mul_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (c : ℝ) (A : ∀ n, Ω n → ℝ)
    (hA : TendstoInProbability P A 0) :
    TendstoInProbability P (fun n x => c * A n x) 0 := by
  by_cases hc : c = 0
  · subst c
    intro ε hε
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0)).congr'
      (Filter.Eventually.of_forall fun n => by
        simp [not_le_of_gt hε])
  · intro ε hε
    have hcabs : 0 < |c| := abs_pos.mpr hc
    have ht := hA (ε / |c|) (div_pos hε hcabs)
    convert ht using 1
    funext n
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, sub_zero, abs_mul]
    rw [div_le_iff₀ hcabs]
    rw [mul_comm]

private theorem iid_sqrtLikelihoodIncrement_array_limits
    (qmd : IIDQuadraticMeanDifferentiable M) (h : H)
    (hincrement : Tendsto (fun n : ℕ => (n : ℝ) * ∫ x,
      (qmd.sqrtLikelihoodIncrement n h x -
        (Real.sqrt (n : ℝ))⁻¹ * inner ℝ h (qmd.score x)) ^ 2 ∂M.law 0)
      atTop (𝓝 0))
    (hmoments :
      Tendsto (fun n : ℕ => (n : ℝ) * ∫ x,
        qmd.sqrtLikelihoodIncrement n h x ^ 2 ∂M.law 0)
          atTop (𝓝 (qmd.information M h h)) ∧
      Tendsto (fun n : ℕ => (n : ℝ) * ∫ x,
        qmd.sqrtLikelihoodIncrement n h x ∂M.law 0)
          atTop (𝓝 (-(1 / 4 : ℝ) * qmd.information M h h))) :
    TendstoInProbability (fun n => M.iidLaw 0 n)
      (fun n x => (∑ i, qmd.sqrtLikelihoodIncrement n h (x i)) -
        inner ℝ h (qmd.centralSequence n x) +
          (1 / 4 : ℝ) * qmd.information M h h) 0 ∧
    TendstoInProbability (fun n => M.iidLaw 0 n)
      (fun n x => (∑ i, qmd.sqrtLikelihoodIncrement n h (x i) ^ 2) -
        qmd.information M h h) 0 ∧
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => M.iidLaw 0 n
      {x | ∃ i, ε ≤ |qmd.sqrtLikelihoodIncrement n h (x i)|}) atTop (𝓝 0) := by
  -- Center the row sum and use product independence plus Chebyshev.  The quadratic row sum uses
  -- truncation and the weak law for this infinitesimal triangular array.  The maximum estimate
  -- follows from the `L²` approximation and the vanishing `L²` tail of the projected score.
  let P : Measure X := M.law 0
  let _ : IsProbabilityMeasure P := M.probability 0
  let W : ℕ → X → ℝ := fun n => qmd.sqrtLikelihoodIncrement n h
  let S : X → ℝ := fun x => inner ℝ h (qmd.score x)
  have hWmeas : ∀ n, Measurable (W n) := fun n =>
    qmd.sqrtLikelihoodIncrement_measurable n h
  have hW2 : ∀ n, MemLp (W n) 2 P := fun n =>
    qmd.sqrtLikelihoodIncrement_memLp n h
  have hS : MemLp S 2 P := qmd.projectedScore_memLp h
  have hscoreInt : Integrable qmd.score P :=
    ((memLp_two_iff_integrable_sq_norm qmd.score_measurable.aestronglyMeasurable).2
      qmd.score_squareIntegrable).integrable (by norm_num)
  have hSmean : ∫ x, S x ∂P = 0 := by
    rw [show (∫ x, S x ∂P) = inner ℝ h (∫ x, qmd.score x ∂P) by
      exact integral_inner hscoreInt h]
    simp [P, qmd.score_integral_eq_zero]
  have hlindeberg : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ) *
      ∫ x in {x | ε ≤ |W n x|}, W n x ^ 2 ∂P) atTop (𝓝 0) :=
    @scaledL2Approx_lindeberg X _ P _ W S hWmeas hW2 hS
      (by simpa [P, W, S] using hincrement)
  have hlinear := @iid_sum_approx_tendstoInProbability X _ P _ W S
    (-(1 / 4 : ℝ) * qmd.information M h h) hWmeas hW2 hS hSmean
    (by simpa [P, W, S] using hincrement) (by simpa [P, W] using hmoments.2)
  have hlinear' : TendstoInProbability (fun n => M.iidLaw 0 n)
      (fun n x => (∑ i, qmd.sqrtLikelihoodIncrement n h (x i)) -
        inner ℝ h (qmd.centralSequence n x))
      (-(1 / 4 : ℝ) * qmd.information M h h) := by
    simpa [P, W, S, DominatedIIDModel.iidLaw, centralSequence,
      inner_smul_right, inner_sum] using hlinear
  refine ⟨?_, ?_, ?_⟩
  · unfold TendstoInProbability at hlinear' ⊢
    intro ε hε
    exact (hlinear' ε hε).congr' (Filter.Eventually.of_forall fun n => by
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq]
      ring)
  · simpa [P, W, DominatedIIDModel.iidLaw, TendstoInProbability] using
      (@iid_sum_sq_tendstoInProbability_of_lindeberg X _ P _ W
        (qmd.information M h h) hWmeas hW2
        (by simpa [P, W] using hmoments.1) hlindeberg)
  · simpa [P, W, DominatedIIDModel.iidLaw] using
      (@iid_max_tendsto_zero_of_lindeberg X _ P _ W hWmeas hW2 hlindeberg)

private theorem iid_guardedLogLikelihood_eq_sum_on_small_increments
    (qmd : IIDQuadraticMeanDifferentiable M) (h : H) (n : ℕ) :
    ∀ᵐ x ∂M.iidLaw 0 n,
      (∀ i, |qmd.sqrtLikelihoodIncrement n h (x i)| ≤ 1) →
        (localExperiment M).logLikelihoodRatio n h x =
          ∑ i, 2 * Real.log (1 + qmd.sqrtLikelihoodIncrement n h (x i) / 2) := by
  -- Combine `iidLaw_rnDeriv_eq_prod` with `rnDeriv_eq_div` through the common dominating
  -- measure.  On the small-increment event every square-root density ratio is positive, so the
  -- guarded branch is inactive and `log (∏ rᵢ) = ∑ log rᵢ` applies without zero factors.
  let u : H := (Real.sqrt (n : ℝ))⁻¹ • h
  let _ : IsProbabilityMeasure (M.law u) := M.probability u
  let _ : IsProbabilityMeasure (M.law 0) := M.probability 0
  let _ : SigmaFinite M.dominating := M.dominating_sigmaFinite
  have hcoordinate : ∀ᵐ y ∂M.law 0,
      ((M.law u).rnDeriv (M.law 0) y).toReal =
        (1 + qmd.sqrtLikelihoodIncrement n h y / 2) ^ 2 := by
    have hratio := Measure.rnDeriv_eq_div
      (M.absolutelyContinuous u) (M.absolutelyContinuous 0)
    have hbasePos := Measure.rnDeriv_pos (M.absolutelyContinuous 0)
    have hbaseTop := (M.absolutelyContinuous 0)
      (Measure.rnDeriv_lt_top (M.law 0) M.dominating)
    filter_upwards [hratio, hbasePos, hbaseTop] with y hyratio hypos hytop
    have hd0pos : 0 < ((M.law 0).rnDeriv M.dominating y).toReal :=
      ENNReal.toReal_pos hypos.ne' hytop.ne
    have hsqrt0pos : 0 < M.sqrtDensity 0 y := by
      exact Real.sqrt_pos.2 hd0pos
    have hfactor : 1 + qmd.sqrtLikelihoodIncrement n h y / 2 =
        M.sqrtDensity u y / M.sqrtDensity 0 y := by
      simp only [sqrtLikelihoodIncrement, hsqrt0pos.ne', if_false, u]
      ring
    calc
      ((M.law u).rnDeriv (M.law 0) y).toReal =
          ((M.law u).rnDeriv M.dominating y).toReal /
            ((M.law 0).rnDeriv M.dominating y).toReal := by
        simpa only [ENNReal.toReal_div] using congrArg ENNReal.toReal hyratio
      _ = (M.sqrtDensity u y / M.sqrtDensity 0 y) ^ 2 := by
        simp only [DominatedIIDModel.sqrtDensity]
        rw [div_pow, Real.sq_sqrt ENNReal.toReal_nonneg,
          Real.sq_sqrt ENNReal.toReal_nonneg]
      _ = (1 + qmd.sqrtLikelihoodIncrement n h y / 2) ^ 2 := by rw [hfactor]
  have hcoordinates : ∀ i : Fin n, ∀ᵐ x ∂M.iidLaw 0 n,
      ((M.law u).rnDeriv (M.law 0) (x i)).toReal =
        (1 + qmd.sqrtLikelihoodIncrement n h (x i) / 2) ^ 2 := by
    intro i
    exact (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin n => M.law 0) i).ae_eq_comp hcoordinate
  filter_upwards [iidLaw_rnDeriv_eq_prod M u n, ae_all_iff.2 hcoordinates]
    with x hrn hcoord
  intro hsmall
  have hfactorPos (i : Fin n) :
      0 < 1 + qmd.sqrtLikelihoodIncrement n h (x i) / 2 := by
    have hi := (abs_le.mp (hsmall i)).1
    linarith
  unfold LocalExperiment.logLikelihoodRatio
  change (if ((M.iidLaw u n).rnDeriv (M.iidLaw 0 n) x).toReal = 0 then
      -(n : ℝ) else Real.log ((M.iidLaw u n).rnDeriv (M.iidLaw 0 n) x).toReal) = _
  rw [hrn, ENNReal.toReal_prod]
  have hprod : (∏ i, ((M.law u).rnDeriv (M.law 0) (x i)).toReal) =
      ∏ i, (1 + qmd.sqrtLikelihoodIncrement n h (x i) / 2) ^ 2 := by
    exact Finset.prod_congr rfl fun i _ => hcoord i
  rw [hprod, if_neg (Finset.prod_ne_zero_iff.2
    fun i _ => pow_ne_zero 2 (hfactorPos i).ne')]
  rw [Real.log_prod (fun i _ => pow_ne_zero 2 (hfactorPos i).ne')]
  simp only [Real.log_pow, Nat.cast_ofNat]

private theorem iid_guardedLogLikelihood_taylor_remainder
    (qmd : IIDQuadraticMeanDifferentiable M) (h : H)
    (hlinear : TendstoInProbability (fun n => M.iidLaw 0 n)
      (fun n x => (∑ i, qmd.sqrtLikelihoodIncrement n h (x i)) -
        inner ℝ h (qmd.centralSequence n x) +
          (1 / 4 : ℝ) * qmd.information M h h) 0)
    (hquadratic : TendstoInProbability (fun n => M.iidLaw 0 n)
      (fun n x => (∑ i, qmd.sqrtLikelihoodIncrement n h (x i) ^ 2) -
        qmd.information M h h) 0)
    (hmax : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => M.iidLaw 0 n
      {x | ∃ i, ε ≤ |qmd.sqrtLikelihoodIncrement n h (x i)|}) atTop (𝓝 0)) :
    TendstoInProbability (fun n => M.iidLaw 0 n)
      (fun n x => (localExperiment M).logLikelihoodRatio n h x -
        (∑ i, qmd.sqrtLikelihoodIncrement n h (x i)) +
          (1 / 4 : ℝ) * ∑ i, qmd.sqrtLikelihoodIncrement n h (x i) ^ 2) 0 := by
  -- On the event where every increment is small, `iidLaw_rnDeriv_eq_prod` turns the guarded
  -- likelihood into `∑ i, 2 * log (1 + Wᵢ/2)`.  Apply the generic summed-log Taylor lemma;
  -- the preceding bridge supplies its a.e. identity and the zero-density guard is in the bad event.
  apply sum_log_taylor_remainder_tendstoInProbability
    (fun n => M.iidLaw 0 n)
    (fun n x => (localExperiment M).logLikelihoodRatio n h x)
    (fun n x i => qmd.sqrtLikelihoodIncrement n h (x i))
    (qmd.information M h h)
  · exact fun n => iidLaw_probability M 0 n
  · exact fun n => iid_guardedLogLikelihood_eq_sum_on_small_increments qmd h n
  · intro ε hε
    simpa only [sub_zero] using hquadratic ε hε
  · exact hmax

/-- The triangular-array likelihood Taylor lemma: product-density factorization, the DQM
`L²` increment approximation, and the vanishing singular mass imply the quadratic LAN
expansion of the guarded log likelihood ratio. -/
theorem iid_logLikelihoodRatio_taylor
    (qmd : IIDQuadraticMeanDifferentiable M) (h : H)
    (hincrement : Tendsto (fun n : ℕ => (n : ℝ) * ∫ x,
      (qmd.sqrtLikelihoodIncrement n h x -
        (Real.sqrt (n : ℝ))⁻¹ * inner ℝ h (qmd.score x)) ^ 2 ∂M.law 0)
      atTop (𝓝 0))
    (hsingular : Tendsto (fun n : ℕ => (n : ℝ) *
      (M.law ((Real.sqrt (n : ℝ))⁻¹ • h)
        {x | M.sqrtDensity 0 x = 0}).toReal) atTop (𝓝 0)) :
    TendstoInProbability (fun n => M.iidLaw 0 n)
      (fun n x => (localExperiment M).logLikelihoodRatio n h x -
        inner ℝ h (qmd.centralSequence n x) +
          (1 / 2 : ℝ) * qmd.information M h h) 0 := by
  -- Use `iidLaw_rnDeriv_eq_prod`; expand each `2 * log (1 + W/2)`; show the
  -- maximum increment vanishes, replace the linear sum by the score sum, and apply the
  -- weak law to the quadratic sum.  The three preceding lemmas isolate these steps.
  have hmoments := qmd.sqrtLikelihoodIncrement_moments h hincrement hsingular
  obtain ⟨hlinear, hquadratic, hmax⟩ :=
    qmd.iid_sqrtLikelihoodIncrement_array_limits h hincrement hmoments
  have htaylor := qmd.iid_guardedLogLikelihood_taylor_remainder h
    hlinear hquadratic hmax
  let P := fun n => M.iidLaw 0 n
  let T : ∀ n, (Fin n → X) → ℝ := fun n x =>
    (localExperiment M).logLikelihoodRatio n h x -
      (∑ i, qmd.sqrtLikelihoodIncrement n h (x i)) +
        (1 / 4 : ℝ) * ∑ i, qmd.sqrtLikelihoodIncrement n h (x i) ^ 2
  let L : ∀ n, (Fin n → X) → ℝ := fun n x =>
    (∑ i, qmd.sqrtLikelihoodIncrement n h (x i)) -
      inner ℝ h (qmd.centralSequence n x) +
        (1 / 4 : ℝ) * qmd.information M h h
  let Q : ∀ n, (Fin n → X) → ℝ := fun n x =>
    (∑ i, qmd.sqrtLikelihoodIncrement n h (x i) ^ 2) -
      qmd.information M h h
  have hTL : TendstoInProbability P (fun n x => T n x + L n x) 0 :=
    tendstoInProbability_add_zero P T L (by simpa [P, T] using htaylor)
      (by simpa [P, L] using hlinear)
  have hQ : TendstoInProbability P (fun n x => -(1 / 4 : ℝ) * Q n x) 0 :=
    tendstoInProbability_const_mul_zero P (-(1 / 4 : ℝ)) Q
      (by simpa [P, Q] using hquadratic)
  have hall := tendstoInProbability_add_zero P
    (fun n x => T n x + L n x) (fun n x => -(1 / 4 : ℝ) * Q n x) hTL hQ
  unfold TendstoInProbability at hall ⊢
  intro ε hε
  exact (hall ε hε).congr' (Filter.Eventually.of_forall fun n => by
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, sub_zero]
    simp only [T, L, Q]
    ring)

/-- Under the base product laws, the normalized i.i.d. score sums converge weakly to the centered
Gaussian law whose covariance is the score second moment. -/
theorem centralSequence_weaklyConverges (qmd : IIDQuadraticMeanDifferentiable M) :
    WeaklyConverges (fun n => M.iidLaw 0 n) qmd.centralSequence
      (Causalean.Stat.gaussianLimit qmd.score_measurable qmd.score_squareIntegrable) := by
  -- Use coordinate projections on `(Fin n → X, Measure.pi ...)` as the canonical IID sample,
  -- then apply `IIDSample.clt_normalizedSum_vec` and unfold the bounded-test-function form.
  constructor
  · intro n
    unfold centralSequence
    exact ((Finset.measurable_sum _ fun i _ =>
      qmd.score_measurable.comp (measurable_pi_apply i)).const_smul _).aemeasurable
  · let P : Measure X := M.law 0
    let _ : IsProbabilityMeasure P := M.probability 0
    let μ : Measure (ℕ → X) := Measure.infinitePi (fun _ : ℕ => P)
    let S : Causalean.Stat.IIDSample (ℕ → X) X μ P := {
      Z i ω := ω i
      meas i := measurable_pi_apply i
      indep := ProbabilityTheory.iIndepFun_infinitePi (X := fun _ x => x) (by fun_prop)
      identDist i := ⟨(measurable_pi_apply 0).aemeasurable,
        (measurable_pi_apply i).aemeasurable, by
          simp only [μ, Measure.infinitePi_map_eval]⟩
      law := by simp only [μ, Measure.infinitePi_map_eval] }
    have hclt := S.clt_normalizedSum_vec qmd.score_measurable
      qmd.score_squareIntegrable qmd.score_integral_eq_zero
    unfold Causalean.Stat.Tendsto_dist_vec at hclt
    intro f
    have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hclt) f
    simp only [ProbabilityMeasure.coe_mk] at ht
    have hsum_meas : ∀ n,
        AEMeasurable (Causalean.Stat.IsAsymLinearVec.normalizedSum
          S qmd.score (fun m => Finset.range m) n) μ := by
      intro n
      unfold Causalean.Stat.IsAsymLinearVec.normalizedSum
      exact ((Finset.measurable_sum _ fun i _ =>
        qmd.score_measurable.comp (S.meas i)).const_smul _).aemeasurable
    simp_rw [integral_map (hsum_meas _) f.continuous.aestronglyMeasurable] at ht
    convert ht using 1
    funext n
    let proj : (ℕ → X) → (Fin n → X) := fun ω i => ω i
    have hproj_meas : Measurable proj := by
      unfold proj
      exact measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
    have hproj : μ.map proj = M.iidLaw 0 n := by
      change (Measure.infinitePi (fun _ : ℕ => P)).map
          (fun (ω : ℕ → X) (i : Fin n) => ω (i : ℕ)) =
            Measure.pi (fun _ : Fin n => M.law 0)
      rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
        Measure.infinitePi_eq_pi]
    change (∫ ω, f (qmd.centralSequence n ω) ∂M.iidLaw 0 n) = _
    rw [← hproj, integral_map hproj_meas.aemeasurable]
    · apply integral_congr_ae
      filter_upwards [] with ω
      congr 2
      simp only [centralSequence, proj,
        Causalean.Stat.IsAsymLinearVec.normalizedSum, S, Finset.card_range]
      exact congrArg (fun z : H => (Real.sqrt (n : ℝ))⁻¹ • z)
        (Fin.sum_univ_eq_sum_range (fun i => qmd.score (ω i)) n)
    · apply (f.continuous.measurable.comp _).aestronglyMeasurable
      unfold centralSequence
      exact (Finset.measurable_sum _ fun i _ =>
        qmd.score_measurable.comp (measurable_pi_apply i)).const_smul _

/-- The generalized Radon--Nikodym log likelihood ratio of the finite product experiment admits
the DQM quadratic expansion: normalized score sum minus half the Fisher-information quadratic
form, with a remainder vanishing in base-law probability. -/
theorem iid_logLikelihoodRatio_expansion (qmd : IIDQuadraticMeanDifferentiable M) (h : H) :
    TendstoInProbability (fun n => M.iidLaw 0 n)
      (fun n x => (localExperiment M).logLikelihoodRatio n h x -
        inner ℝ h (qmd.centralSequence n x) +
          (1 / 2 : ℝ) * qmd.information M h h) 0 := by
  exact iid_logLikelihoodRatio_taylor qmd h
    (sqrtLikelihoodIncrement_L2 qmd h) (local_zeroBaseDensity_mass qmd h)

/-- A [quadratic-mean differentiable dominated finite-dimensional i.i.d. model](hyp:qmd) [is locally asymptotically normal at its base parameter](goal), with normalized score-sum central sequence and score-second-moment information form. -/
theorem iidDQM_implies_LAN (qmd : IIDQuadraticMeanDifferentiable M) :
    IsLAN (localExperiment M) qmd.centralSequence (qmd.information M)
      (Causalean.Stat.gaussianLimit qmd.score_measurable qmd.score_squareIntegrable) := by
  rcases qmd.information_isSymm_nonnegative with ⟨hsymm, hnonneg⟩
  refine
    { central_measurable := qmd.centralSequence_weaklyConverges.1
      information_symmetric := hsymm
      information_nonnegative := hnonneg
      gaussian_probability := inferInstance
      gaussian_charFun := fun t => ?_
      central_converges := qmd.centralSequence_weaklyConverges
      expansion := qmd.iid_logLikelihoodRatio_expansion }
  rw [Causalean.Stat.gaussianLimit_charFun]
  congr 2
  rw [qmd.information_apply]
  simp only [pow_two]
  ring

end IIDQuadraticMeanDifferentiable

end Causalean.Estimation.Efficiency.AsymptoticLanConvolution
