module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationRoles

/-! # Causal outcome moments
Exchangeability removes the treatment bit under bounded test functions, and
conditional Bernoulli margins identify the selected potential-outcome moment.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- A Bernoulli law with an admissible probability has unit mass.  Given [the specified input p](hyp:p), [the specified input hp](hyp:hp), [the population bern probability conclusion](goal) holds. -/
lemma population_bern_probability (p : ℝ) (hp : p ∈ Icc 0 1) :
    IsProbabilityMeasure (bern p) := by
  constructor
  simp only [bern, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith [hp.2]) hp.1]
  norm_num

/-- Exchangeability factors the treatment bit from a bounded potential-outcome test.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input hdesign](hyp:hdesign), [the specified input hex](hyp:hex), [the specified input he](hyp:he), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hbound](hyp:hbound), [the specified input hsupp](hyp:hsupp), [the overlap level eps](hyp:eps), [the population exchangeability bit moment conclusion](goal) holds. -/
lemma population_exchangeability_bit_moment {d : ℕ} {eps : ℝ} (P : PrimitiveLaw d)
    (hdesign : UniformDesign P) (hex : ConditionalExchangeability P) (he : Overlap eps P)
    (H : Cov d × (Bool × Bool) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, ‖H z‖ ≤ B)
    (hsupp : ∀ z, z.1 ∉ cube d → H z = 0) :
    (∫ w, H (w.1, w.2.2) * bit w.2.1 ∂P.law) =
      ∫ w, H (w.1, w.2.2) * P.e w.1 ∂P.law := by
  have hPe := P.measurable_e
  obtain ⟨Γ, hΓ, hΓlaw⟩ := hex
  letI := hΓ
  let Q := (P.law.map Prod.fst) ⊗ₘ Γ
  let κ := bernKernel (fun z : Cov d × (Bool × Bool) => P.e z.1)
    (P.measurable_e.comp measurable_fst)
  let T := fun w : FullRecord d => ((w.1, w.2.2), w.2.1)
  have hT : Measurable T := by fun_prop
  have hlaw : P.law.map T = Q ⊗ₘ κ := hΓlaw
  letI : IsSFiniteKernel κ := by
    by_contra hn
    have hz := hlaw
    rw [Measure.compProd_of_not_isSFiniteKernel _ _ hn] at hz
    have hm := congrArg (fun μ => μ univ) hz
    letI := Measure.isProbabilityMeasure_map hT.aemeasurable (μ := P.law)
    simpa using hm
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    rw [hdesign]
    have hu : IsProbabilityMeasure (uniformLaw d) := by
      rw [← hdesign]
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    infer_instance
  have hHe : ∀ z, ‖H z * P.e z.1‖ ≤ B := by
    intro z
    by_cases hx : z.1 ∈ cube d
    · rw [norm_mul, Real.norm_eq_abs (P.e z.1), abs_of_nonneg (by linarith [(he.unit _ hx).1])]
      exact (mul_le_mul_of_nonneg_left (by linarith [(he.unit _ hx).2] : P.e z.1 ≤ 1)
        (norm_nonneg _)).trans (by simpa using hbound z)
    · simp [hsupp z hx, hB]
  have hF : Integrable (fun z : (Cov d × (Bool × Bool)) × Bool => H z.1 * bit z.2)
      (Q ⊗ₘ κ) := by
    rw [← hlaw]
    letI := Measure.isProbabilityMeasure_map hT.aemeasurable (μ := P.law)
    apply population_integrable_bounded _ _ (by fun_prop) B
    intro z
    cases z.2
    · simpa [bit] using hB
    · simpa [bit] using hbound z.1
  have hG : Integrable (fun z : (Cov d × (Bool × Bool)) × Bool => H z.1 * P.e z.1.1)
      (Q ⊗ₘ κ) := by
    rw [← hlaw]
    letI := Measure.isProbabilityMeasure_map hT.aemeasurable (μ := P.law)
    exact population_integrable_bounded _ _ (by fun_prop) B (fun z => hHe z.1)
  have hcube : ∀ᵐ z ∂Q, z.1 ∈ cube d := by
    dsimp [Q]
    apply Measure.ae_compProd_of_ae_fst Γ
    · unfold cube
      simp only [setOf_forall]
      exact MeasurableSet.iInter (fun i => measurableSet_Icc.preimage (by fun_prop))
    · rw [hdesign]
      exact ae_restrict_mem (by
        unfold cube
        simp only [setOf_forall]
        exact MeasurableSet.iInter (fun i => measurableSet_Icc.preimage (by fun_prop)))
  calc
    _ = ∫ z, H z.1 * bit z.2 ∂(Q ⊗ₘ κ) := by
      rw [← hlaw, integral_map hT.aemeasurable (by fun_prop : Measurable _).aestronglyMeasurable]
    _ = ∫ z, (∫ a, H z * bit a ∂κ z) ∂Q := Measure.integral_compProd hF
    _ = ∫ z, H z * P.e z.1 ∂Q := by
      apply integral_congr_ae
      filter_upwards [hcube] with z hz
      exact bern_bit_integral _ _ (by linarith [(he.unit _ hz).1])
    _ = ∫ z, (∫ a, H z * P.e z.1 ∂κ z) ∂Q := by
      apply integral_congr_ae
      filter_upwards [hcube] with z hz
      letI := population_bern_probability (P.e z.1) ⟨by linarith [(he.unit _ hz).1], by linarith [(he.unit _ hz).2]⟩
      change H z * P.e z.1 = ∫ _a, H z * P.e z.1 ∂bern (P.e z.1)
      simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    _ = ∫ z, H z.1 * P.e z.1.1 ∂(Q ⊗ₘ κ) := (Measure.integral_compProd hG).symm
    _ = _ := by rw [← hlaw, integral_map hT.aemeasurable (by fun_prop : Measurable _).aestronglyMeasurable]

/-- A conditional Bernoulli margin identifies bounded potential-outcome test moments.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input hdesign](hyp:hdesign), [the specified input j](hyp:j), [the specified input hj](hyp:hj), [the specified input mu](hyp:mu), [the specified input hmu](hyp:hmu), [the specified input hmu0](hyp:hmu0), [the specified input hmargin](hyp:hmargin), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hfB](hyp:hfB), [the population arm margin moment conclusion](goal) holds. -/
lemma population_arm_margin_moment {d : ℕ} (P : PrimitiveLaw d)
    (hdesign : UniformDesign P) (j : FullRecord d → Bool) (hj : Measurable j)
    (mu : Cov d → ℝ) (hmu : Measurable mu) (hmu0 : ∀ x ∈ cube d, 0 ≤ mu x)
    (hmargin : P.law.map (fun w => (w.1, j w)) =
      (P.law.map Prod.fst) ⊗ₘ bernKernel mu hmu)
    (f : Cov d → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hfB : ∀ x, ‖f x‖ ≤ B) :
    (∫ w, f w.1 * bit (j w) ∂P.law) = ∫ x, f x * mu x ∂uniformLaw d := by
  letI : SFinite (uniformLaw d) := by unfold uniformLaw; infer_instance
  letI := bernKernel_sfinite_of_margin P j hj mu hmu hmargin
  have hm : IsProbabilityMeasure (P.law.map (fun w => (w.1, j w))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI := hm
  have hi : Integrable (fun z : Cov d × Bool => f z.1 * bit z.2)
      (P.law.map (fun w => (w.1, j w))) := by
    apply population_integrable_bounded _ _ (by fun_prop) B
    intro z
    cases z.2
    · simpa [bit] using hB
    · simpa [bit] using hfB z.1
  rw [hmargin, hdesign] at hi
  rw [← integral_map (by fun_prop : Measurable (fun w : FullRecord d => (w.1, j w))).aemeasurable
    (by fun_prop : Measurable (fun z : Cov d × Bool => f z.1 * bit z.2)).aestronglyMeasurable,
    hmargin, hdesign, Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (show MeasurableSet (cube d) from by
    unfold cube; simp only [setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_Icc.preimage (by fun_prop)))] with x hx
  exact bern_bit_integral _ _ (hmu0 x hx)

/-- A bounded cube-supported test remains bounded after multiplication by overlap.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input he](hyp:he), [the specified input f](hyp:f), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hf](hyp:hf), [the specified input hs](hyp:hs), [the overlap level eps](hyp:eps), [the population test mul propensity bound conclusion](goal) holds. -/
lemma population_test_mul_propensity_bound {d : ℕ} {eps : ℝ} (P : PrimitiveLaw d) (he : Overlap eps P)
    (f : Cov d → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B)
    (hs : ∀ x, x ∉ cube d → f x = 0) : ∀ x, ‖f x * P.e x‖ ≤ B := by
  intro x
  by_cases hx : x ∈ cube d
  · rw [norm_mul, Real.norm_eq_abs (P.e x), abs_of_nonneg (by linarith [(he.unit _ hx).1])]
    exact (mul_le_mul_of_nonneg_left (by linarith [(he.unit _ hx).2] : P.e x ≤ 1)
      (norm_nonneg _)).trans (by simpa using hf x)
  · simp [hs x hx, hB]

/-- The treated observed outcome moment is the propensity times the treated arm mean.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input hdesign](hyp:hdesign), [the specified input hex](hyp:hex), [the specified input he](hyp:he), [the specified input hmu](hyp:hmu), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hfB](hyp:hfB), [the specified input hs](hyp:hs), [the overlap level eps](hyp:eps), [the population treated outcome moment conclusion](goal) holds. -/
lemma population_treated_outcome_moment {d : ℕ} {eps : ℝ} (P : PrimitiveLaw d)
    (hdesign : UniformDesign P) (hex : ConditionalExchangeability P) (he : Overlap eps P)
    (hmu : TreatedInterior P)
    (f : Cov d → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hfB : ∀ x, ‖f x‖ ≤ B) (hs : ∀ x, x ∉ cube d → f x = 0) :
    (∫ w, f w.1 * bit w.2.1 * bit w.2.2 ∂obsLaw P) =
      ∫ x, f x * P.e x * P.mu1 x ∂uniformLaw d := by
  have hPe := P.measurable_e
  rw [obsLaw, integral_map population_measurable_observed.aemeasurable
    (by fun_prop : Measurable (fun w : Cov d × Bool × Bool =>
      f w.1 * bit w.2.1 * bit w.2.2)).aestronglyMeasurable]
  have hcons : (fun w : FullRecord d => f (observed w).1 * bit (observed w).2.1 *
      bit (observed w).2.2) = fun w => (f w.1 * bit w.2.2.2) * bit w.2.1 := by
    funext w
    cases ha : w.2.1 <;> simp [observed, ha, bit, mul_comm]
  rw [hcons, population_exchangeability_bit_moment P hdesign hex he
    (fun z => f z.1 * bit z.2.2) (by fun_prop) B hB
    (by intro z; cases z.2.2
        · simpa [bit] using hB
        · simpa [bit] using hfB z.1)
    (by intro z hz; simp [hs z.1 hz])]
  have hcomm : (fun w : FullRecord d => (f w.1 * bit w.2.2.2) * P.e w.1) =
      fun w => (f w.1 * P.e w.1) * bit w.2.2.2 := by funext w; ring
  rw [hcomm]
  exact population_arm_margin_moment P hdesign (fun w => w.2.2.2) (by fun_prop)
    P.mu1 P.measurable_mu1 (by intro x hx; linarith [(hmu x hx).1]) P.margin_mu1
    _ (by fun_prop) B hB (population_test_mul_propensity_bound P he f B hB hfB hs)

/-- The untreated observed outcome moment uses the complementary propensity.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input hdesign](hyp:hdesign), [the specified input hex](hyp:hex), [the specified input he](hyp:he), [the specified input hmu](hyp:hmu), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hfB](hyp:hfB), [the specified input hs](hyp:hs), [the overlap level eps](hyp:eps), [the population control outcome moment conclusion](goal) holds. -/
lemma population_control_outcome_moment {d : ℕ} {eps : ℝ} (P : PrimitiveLaw d)
    (hdesign : UniformDesign P) (hex : ConditionalExchangeability P) (he : Overlap eps P)
    (hmu : ControlInterior P)
    (f : Cov d → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hfB : ∀ x, ‖f x‖ ≤ B) (hs : ∀ x, x ∉ cube d → f x = 0) :
    (∫ w, f w.1 * (1-bit w.2.1) * bit w.2.2 ∂obsLaw P) =
      ∫ x, f x * (1-P.e x) * P.mu0 x ∂uniformLaw d := by
  have hPe := P.measurable_e
  have hPm := P.measurable_mu0
  rw [obsLaw, integral_map population_measurable_observed.aemeasurable
    (by fun_prop : Measurable (fun w : Cov d × Bool × Bool =>
      f w.1 * (1-bit w.2.1) * bit w.2.2)).aestronglyMeasurable]
  have hcons : (fun w : FullRecord d => f (observed w).1 * (1-bit (observed w).2.1) *
      bit (observed w).2.2) = fun w => f w.1 * bit w.2.2.1 -
        (f w.1 * bit w.2.2.1) * bit w.2.1 := by
    funext w
    cases ha : w.2.1 <;> simp [observed, ha, bit]
  have hi : Integrable (fun w : FullRecord d => f w.1 * bit w.2.2.1) P.law := by
    apply population_integrable_bounded _ _ (by fun_prop) B
    intro w
    cases w.2.2.1
    · simpa [bit] using hB
    · simpa [bit] using hfB w.1
  have hj : Integrable (fun w : FullRecord d => (f w.1 * bit w.2.2.1)*bit w.2.1) P.law := by
    apply population_integrable_bounded _ _ (by fun_prop) B
    intro w
    cases w.2.1 <;> cases w.2.2.1
    all_goals simp only [bit, Bool.false_eq_true, ite_false, ite_true, mul_zero, mul_one, norm_zero]
    all_goals first | exact hB | exact hfB w.1
  have hex0 := population_exchangeability_bit_moment P hdesign hex he
    (fun z => f z.1 * bit z.2.1) (by fun_prop) B hB
    (by intro z; cases z.2.1
        · simpa [bit] using hB
        · simpa [bit] using hfB z.1)
    (by intro z hz; simp [hs z.1 hz])
  have hcomm : (fun w : FullRecord d => (f w.1 * bit w.2.2.1) * P.e w.1) =
      fun w => (f w.1 * P.e w.1) * bit w.2.2.1 := by funext w; ring
  rw [hcomm] at hex0
  rw [population_arm_margin_moment P hdesign (fun w => w.2.2.1) (by fun_prop)
    P.mu0 P.measurable_mu0 (by intro x hx; linarith [(hmu x hx).1]) P.margin_mu0
    _ (by fun_prop) B hB (population_test_mul_propensity_bound P he f B hB hfB hs)] at hex0
  rw [hcons, integral_sub hi hj, hex0,
    population_arm_margin_moment P hdesign (fun w => w.2.2.1) (by fun_prop)
      P.mu0 P.measurable_mu0 (by intro x hx; linarith [(hmu x hx).1]) P.margin_mu0
      f hf B hB hfB]
  have hu : IsProbabilityMeasure (uniformLaw d) := by
    rw [← hdesign]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI := hu
  have hfm : ∀ x, ‖f x * P.mu0 x‖ ≤ B := by
    intro x
    by_cases hx : x ∈ cube d
    · rw [norm_mul, Real.norm_eq_abs (P.mu0 x), abs_of_nonneg (by linarith [(hmu x hx).1])]
      exact (mul_le_mul_of_nonneg_left (by linarith [(hmu x hx).2] : P.mu0 x ≤ 1)
        (norm_nonneg _)).trans (by simpa using hfB x)
    · simp [hs x hx, hB]
  have hfe : ∀ x, ‖f x * P.e x * P.mu0 x‖ ≤ B := by
    have hb := population_test_mul_propensity_bound P he f B hB hfB hs
    intro x
    by_cases hx : x ∈ cube d
    · rw [norm_mul, Real.norm_eq_abs (P.mu0 x), abs_of_nonneg (by linarith [(hmu x hx).1])]
      exact (mul_le_mul_of_nonneg_left (by linarith [(hmu x hx).2] : P.mu0 x ≤ 1)
        (norm_nonneg _)).trans (by simpa using hb x)
    · simp [hs x hx, hB]
  rw [← integral_sub (population_integrable_bounded _ _ (by fun_prop) B hfm)
    (population_integrable_bounded _ _ (by fun_prop) B hfe)]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- The observed response moment combines the two identified arm moments.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input hdesign](hyp:hdesign), [the specified input hex](hyp:hex), [the specified input he](hyp:he), [the specified input hm0](hyp:hm0), [the specified input hm1](hyp:hm1), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hfB](hyp:hfB), [the specified input hs](hyp:hs), [the overlap level eps](hyp:eps), [the population outcome moment conclusion](goal) holds. -/
lemma population_outcome_moment {d : ℕ} {eps : ℝ} (P : PrimitiveLaw d)
    (hdesign : UniformDesign P) (hex : ConditionalExchangeability P) (he : Overlap eps P)
    (hm0 : ControlInterior P) (hm1 : TreatedInterior P)
    (f : Cov d → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hfB : ∀ x, ‖f x‖ ≤ B) (hs : ∀ x, x ∉ cube d → f x = 0) :
    (∫ w, f w.1 * bit w.2.2 ∂obsLaw P) =
      ∫ x, f x * (P.mu0 x + P.e x * (P.mu1 x-P.mu0 x)) ∂uniformLaw d := by
  letI := obsLaw_probability P
  letI : IsProbabilityMeasure (uniformLaw d) := by
    rw [← hdesign]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hPe := P.measurable_e
  have hP0 := P.measurable_mu0
  have hP1 := P.measurable_mu1
  have hbits (a y : Bool) : ‖(1-bit a)*bit y‖ ≤ 1 ∧ ‖bit a*bit y‖ ≤ 1 := by
    cases a <;> cases y <;> norm_num [bit]
  have hi : Integrable (fun w : Cov d × Bool × Bool => f w.1*(1-bit w.2.1)*bit w.2.2) (obsLaw P) := by
    apply population_integrable_bounded _ _ (by fun_prop) B
    intro w
    rw [mul_assoc, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hbits _ _).1 (norm_nonneg _)).trans (by simpa using hfB w.1)
  have hj : Integrable (fun w : Cov d × Bool × Bool => f w.1*bit w.2.1*bit w.2.2) (obsLaw P) := by
    apply population_integrable_bounded _ _ (by fun_prop) B
    intro w
    rw [mul_assoc, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hbits _ _).2 (norm_nonneg _)).trans (by simpa using hfB w.1)
  have hsum : (fun w : Cov d × Bool × Bool => f w.1*bit w.2.2) =
      fun w => f w.1*(1-bit w.2.1)*bit w.2.2+f w.1*bit w.2.1*bit w.2.2 := by
    funext w; ring
  rw [hsum, integral_add hi hj,
    population_control_outcome_moment P hdesign hex he hm0 f hf B hB hfB hs,
    population_treated_outcome_moment P hdesign hex he hm1 f hf B hB hfB hs]
  have hbound (mu : Cov d → ℝ) (hmu : ∀ x ∈ cube d, mu x ∈ Icc 0 1)
      (e : Cov d → ℝ) (he : ∀ x ∈ cube d, e x ∈ Icc 0 1) :
      ∀ x, ‖f x * e x * mu x‖ ≤ B := by
    intro x
    by_cases hx : x ∈ cube d
    · rw [norm_mul, norm_mul, Real.norm_eq_abs (e x), Real.norm_eq_abs (mu x),
        abs_of_nonneg (he x hx).1, abs_of_nonneg (hmu x hx).1]
      calc
        _ ≤ ‖f x‖ * e x := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hmu x hx).2
            (mul_nonneg (norm_nonneg (f x)) (he x hx).1)
        _ ≤ ‖f x‖ := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (he x hx).2 (norm_nonneg (f x))
        _ ≤ B := hfB x
    · simp [hs x hx, hB]
  have hb0 := hbound P.mu0 (by intro x hx; constructor <;> linarith [(hm0 x hx).1, (hm0 x hx).2])
    (fun x => 1-P.e x) (by intro x hx; constructor <;> linarith [(he.unit x hx).1, (he.unit x hx).2])
  have hb1 := hbound P.mu1 (by intro x hx; constructor <;> linarith [(hm1 x hx).1, (hm1 x hx).2])
    P.e (by intro x hx; constructor <;> linarith [(he.unit x hx).1, (he.unit x hx).2])
  rw [← integral_add (population_integrable_bounded _ _ (by fun_prop) B hb0)
    (population_integrable_bounded _ _ (by fun_prop) B hb1)]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
