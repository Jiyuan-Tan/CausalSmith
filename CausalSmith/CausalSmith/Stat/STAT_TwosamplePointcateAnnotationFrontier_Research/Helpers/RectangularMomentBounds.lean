module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RectangularBlockLaw

/-! # Original-record rectangular moment bounds
The joint role law transfers the independent rectangular variance calculation to
the actual data. Centered first-order averages and corrections are combined by
the squared-difference inequality, without an independence assertion.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 200000
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- A rectangular average of a record kernel on the original dataset.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input H](hyp:H), [the specified input w](hyp:w), [rectangular average](goal) is the corresponding construction. -/
def rectangularAverage {d n m : ℕ}
    (H : (Cov d × Bool) × (Cov d × Bool × Bool) → ℝ) (w : Sample d n m) : ℝ :=
  ((treatmentCount n m:ℝ)*(outcomeCount n:ℝ))⁻¹ *
    ∑ i ∈ (roleSplit n m).2, ∑ j ∈ (roleSplit n m).1,
      H (treatmentRecords w.1 i, w.1.1 j)

/-- The rectangular average is exactly its finite enumerated counterpart.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input H](hyp:H), [the rectangular average enumeration conclusion](goal) holds. -/
lemma rectangular_average_enumeration {d n m : ℕ}
    (H : (Cov d × Bool) × (Cov d × Bool × Bool) → ℝ) :
    rectangularAverage (n := n) (m := m) H = fun w =>
      ((treatmentCount n m:ℝ)*(outcomeCount n:ℝ))⁻¹ *
        ∑ a : Fin (treatmentCount n m), ∑ b : Fin (outcomeCount n),
          H ((rectangularRoleData w).1 a,(rectangularRoleData w).2 b) := by
  funext w
  exact congrArg (fun x : ℝ => ((treatmentCount n m:ℝ)*(outcomeCount n:ℝ))⁻¹*x)
    (rectangular_role_sum_enumeration w H)

/-- A square-integrable kernel gives a square-integrable original-record rectangular average.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the rectangular original average mem lp conclusion](goal) holds. -/
lemma rectangular_original_average_memLp {d n m : ℕ} (P : PrimitiveLaw d)
    (H : (Cov d × Bool) × (Cov d × Bool × Bool) → ℝ)
    (hH : MemLp H 2 ((xaLaw P).prod (obsLaw P))) :
    MemLp (rectangularAverage (n := n) (m := m) H) 2 (experiment P n m) := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  have hm : MemLp (fun D : (Fin (treatmentCount n m) → Cov d × Bool) ×
      (Fin (outcomeCount n) → Cov d × Bool × Bool) =>
      ((treatmentCount n m:ℝ)*(outcomeCount n:ℝ))⁻¹ *
        ∑ a, ∑ b, H (D.1 a,D.2 b)) 2
      ((Measure.pi (fun _ : Fin (treatmentCount n m) => xaLaw P)).prod
        (Measure.pi (fun _ : Fin (outcomeCount n) => obsLaw P))) := by
    apply MemLp.const_mul
    apply memLp_finsetSum
    intro a _
    apply memLp_finsetSum
    intro b _
    exact hH.comp_measurePreserving ((measurePreserving_eval _ a).prod (measurePreserving_eval _ b))
  rw [rectangular_average_enumeration]
  exact hm.comp_measurePreserving (rectangular_role_data_law P)

/-- The original-record rectangular average has the independent pair expectation.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input hn](hyp:hn), [the specified input H](hyp:H), [the specified input hHm](hyp:hHm), [the specified input hH](hyp:hH), [the rectangular original average mean conclusion](goal) holds. -/
lemma rectangular_original_average_mean {d n m : ℕ} (P : PrimitiveLaw d) (hn : 2 ≤ n)
    (H : (Cov d × Bool) × (Cov d × Bool × Bool) → ℝ) (hHm : Measurable H)
    (hH : MemLp H 2 ((xaLaw P).prod (obsLaw P))) :
    (∫ w, rectangularAverage (n := n) (m := m) H w ∂experiment P n m) =
      ∫ p, H p ∂(xaLaw P).prod (obsLaw P) := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  have hmp := rectangular_role_data_law (n := n) (m := m) P
  rw [rectangular_average_enumeration]
  let G := fun D : (Fin (treatmentCount n m) → Cov d × Bool) ×
      (Fin (outcomeCount n) → Cov d × Bool × Bool) =>
      ((treatmentCount n m:ℝ)*(outcomeCount n:ℝ))⁻¹ * ∑ a, ∑ b, H (D.1 a,D.2 b)
  have hG : Measurable G := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro a _
    apply Finset.measurable_sum
    intro b _
    exact hHm.comp (by fun_prop)
  have hmap := integral_map (μ := experiment P n m) hmp.measurable.aemeasurable hG.aestronglyMeasurable
  rw [hmp.map_eq] at hmap
  rw [← hmap]
  have hi (a : Fin (treatmentCount n m)) (b : Fin (outcomeCount n)) :
      Integrable (fun D => H (D.1 a,D.2 b))
      ((Measure.pi (fun _ : Fin (treatmentCount n m) => xaLaw P)).prod
        (Measure.pi (fun _ : Fin (outcomeCount n) => obsLaw P))) :=
    (hH.comp_measurePreserving ((measurePreserving_eval _ a).prod
      (measurePreserving_eval _ b))).integrable (by norm_num)
  rw [integral_const_mul, integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  simp_rw [integral_finsetSum _ (fun b _ => hi _ b)]
  have he (a : Fin (treatmentCount n m)) (b : Fin (outcomeCount n)) :
      (∫ D, H (D.1 a,D.2 b) ∂(Measure.pi (fun _ : Fin (treatmentCount n m) => xaLaw P)).prod
        (Measure.pi (fun _ : Fin (outcomeCount n) => obsLaw P))) =
        ∫ p, H p ∂(xaLaw P).prod (obsLaw P) := by
    have hp := (measurePreserving_eval (fun _ : Fin (treatmentCount n m) => xaLaw P) a).prod
      (measurePreserving_eval (fun _ : Fin (outcomeCount n) => obsLaw P) b)
    rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hHm.aestronglyMeasurable]
    rfl
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hl : (outcomeCount n:ℝ) ≠ 0 := by exact_mod_cast (population_role_counts_pos n m hn).1.ne'
  have ht : (treatmentCount n m:ℝ) ≠ 0 := by exact_mod_cast (population_role_counts_pos n m hn).2.ne'
  field_simp

/-- Any independent-block centered variance bound transfers to the original rectangular average.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input H](hyp:H), [the specified input hHm](hyp:hHm), [the specified input B](hyp:B), [the specified input hb](hyp:hb), [the rectangular original average variance le conclusion](goal) holds. -/
lemma rectangular_original_average_variance_le {d n m : ℕ} (P : PrimitiveLaw d)
    (H : (Cov d × Bool) × (Cov d × Bool × Bool) → ℝ) (hHm : Measurable H)
    (B : ℝ)
    (hb : (∫ D, (((treatmentCount n m:ℝ)*(outcomeCount n:ℝ))⁻¹ *
      ∑ a, ∑ b, H (D.1 a,D.2 b) - ∫ p, H p ∂(xaLaw P).prod (obsLaw P))^2
      ∂(Measure.pi (fun _ : Fin (treatmentCount n m) => xaLaw P)).prod
        (Measure.pi (fun _ : Fin (outcomeCount n) => obsLaw P))) ≤ B) :
    (∫ w, (rectangularAverage (n := n) (m := m) H w -
      ∫ p, H p ∂(xaLaw P).prod (obsLaw P))^2 ∂experiment P n m) ≤ B := by
  have hp := rectangular_role_data_law (n := n) (m := m) P
  rw [rectangular_average_enumeration]
  let G := fun D : (Fin (treatmentCount n m) → Cov d × Bool) ×
      (Fin (outcomeCount n) → Cov d × Bool × Bool) =>
      (((treatmentCount n m:ℝ)*(outcomeCount n:ℝ))⁻¹ * ∑ a, ∑ b, H (D.1 a,D.2 b) -
        ∫ p, H p ∂(xaLaw P).prod (obsLaw P))^2
  have hG : Measurable G := by
    apply Measurable.pow_const
    apply Measurable.sub _ measurable_const
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro a _
    apply Finset.measurable_sum
    intro b _
    exact hHm.comp (by fun_prop)
  have hmap := integral_map (μ := experiment P n m) hp.measurable.aemeasurable hG.aestronglyMeasurable
  rw [hp.map_eq] at hmap
  change (∫ w, G (rectangularRoleData w) ∂experiment P n m) ≤ B
  rw [← hmap]
  exact hb

/-- A first-order average over the labeled outcome role.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input f](hyp:f), [the specified input w](hyp:w), [rectangular outcome average](goal) is the corresponding construction. -/
def rectangularOutcomeAverage {d n m : ℕ} (f : Cov d × Bool × Bool → ℝ) (w : Sample d n m) : ℝ :=
  (outcomeCount n:ℝ)⁻¹ * ∑ j ∈ (roleSplit n m).1, f (w.1.1 j)

/-- The outcome average is the ordinary iid average of the enumerated outcome records.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input f](hyp:f), [the specified input w](hyp:w), [the rectangular outcome average enumeration conclusion](goal) holds. -/
lemma rectangular_outcome_average_enumeration {d n m : ℕ} (f : Cov d × Bool × Bool → ℝ)
    (w : Sample d n m) :
    rectangularOutcomeAverage f w = (outcomeCount n:ℝ)⁻¹ *
      ∑ b : Fin (outcomeCount n), f ((rectangularRoleData w).2 b) := by
  classical
  unfold rectangularOutcomeAverage
  rw [← Finset.sum_coe_sort (roleSplit n m).1, ← (rectangularOutcomeEnumeration n m).sum_comp]
  rfl

/-- The first-order outcome average is square-integrable and has the observation-law mean.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input hn](hyp:hn), [the specified input f](hyp:f), [the specified input hfm](hyp:hfm), [the specified input hf](hyp:hf), [the rectangular outcome average moments conclusion](goal) holds. -/
lemma rectangular_outcome_average_moments {d n m : ℕ} (P : PrimitiveLaw d) (hn : 2 ≤ n)
    (f : Cov d × Bool × Bool → ℝ) (hfm : Measurable f) (hf : MemLp f 2 (obsLaw P)) :
    MemLp (rectangularOutcomeAverage (n := n) (m := m) f) 2 (experiment P n m) ∧
    (∫ w, rectangularOutcomeAverage (n := n) (m := m) f w ∂experiment P n m) = ∫ z, f z ∂obsLaw P := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  have hp := measurePreserving_snd.comp (rectangular_role_data_law (n := n) (m := m) P)
  have hm : MemLp (fun D : Fin (outcomeCount n) → Cov d × Bool × Bool =>
      (outcomeCount n:ℝ)⁻¹ * ∑ b, f (D b)) 2 (Measure.pi (fun _ : Fin (outcomeCount n) => obsLaw P)) :=
    (memLp_finsetSum _ (fun b _ => hf.comp_measurePreserving (measurePreserving_eval _ b))).const_mul _
  constructor
  · change MemLp (fun w => rectangularOutcomeAverage f w) 2 _
    simpa only [Function.comp_def, rectangular_outcome_average_enumeration] using hm.comp_measurePreserving hp
  · simp only [rectangular_outcome_average_enumeration]
    have hmap := integral_map (μ := experiment P n m) hp.measurable.aemeasurable
      ((by fun_prop : Measurable (fun D : Fin (outcomeCount n) → Cov d × Bool × Bool =>
        (outcomeCount n:ℝ)⁻¹ * ∑ b, f (D b))).aestronglyMeasurable)
    rw [hp.map_eq] at hmap
    change (∫ w, ((outcomeCount n:ℝ)⁻¹ * ∑ b, f ((Prod.snd ∘ rectangularRoleData) w b)) ∂experiment P n m) = _
    rw [← hmap]
    exact Causalean.Mathlib.Probability.iid_average_integral (obsLaw P) (outcomeCount n)
      (population_role_counts_pos n m hn).1 f (hf.integrable (by norm_num))

/-- The centered difference of the two actual moments obeys the sum of their variance bounds.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input hn](hyp:hn), [the specified input f](hyp:f), [the specified input hfm](hyp:hfm), [the specified input hf](hyp:hf), [the specified input H](hyp:H), [the specified input hHm](hyp:hHm), [the specified input hH](hyp:hH), [the specified input B](hyp:B), [the rectangular-average variance bound](hyp:hb), [the rectangular original moment variance le conclusion](goal) holds. -/
lemma rectangular_original_moment_variance_le {d n m : ℕ} (P : PrimitiveLaw d) (hn : 2 ≤ n)
    (f : Cov d × Bool × Bool → ℝ) (hfm : Measurable f) (hf : MemLp f 2 (obsLaw P))
    (H : (Cov d × Bool) × (Cov d × Bool × Bool) → ℝ) (hHm : Measurable H)
    (hH : MemLp H 2 ((xaLaw P).prod (obsLaw P))) (B : ℝ)
    (hb : (∫ w, (rectangularAverage (n := n) (m := m) H w -
      ∫ p, H p ∂(xaLaw P).prod (obsLaw P))^2 ∂experiment P n m) ≤ B) :
    MemLp (fun w => rectangularOutcomeAverage (n := n) (m := m) f w - rectangularAverage H w)
      2 (experiment P n m) ∧
    (∫ w, (rectangularOutcomeAverage (n := n) (m := m) f w - rectangularAverage H w -
      ∫ z, (rectangularOutcomeAverage f z - rectangularAverage H z) ∂experiment P n m)^2
      ∂experiment P n m) ≤ (6/(n:ℝ))*(∫ z, (f z)^2 ∂obsLaw P) + 2*B := by
  letI := population_experiment_probability P n m
  obtain ⟨hA, hmA⟩ := rectangular_outcome_average_moments P hn f hfm hf
  have hR := rectangular_original_average_memLp (n := n) (m := m) P H hH
  have hmR := rectangular_original_average_mean (n := n) (m := m) P hn H hHm hH
  refine ⟨hA.sub hR, ?_⟩
  rw [integral_sub (hA.integrable (by norm_num)) (hR.integrable (by norm_num)), hmA, hmR]
  have he (w : Sample d n m) : rectangularOutcomeAverage f w - rectangularAverage H w -
      ((∫ z, f z ∂obsLaw P) - ∫ p, H p ∂(xaLaw P).prod (obsLaw P)) =
      (rectangularOutcomeAverage f w - ∫ z, f z ∂obsLaw P) -
        (rectangularAverage H w - ∫ p, H p ∂(xaLaw P).prod (obsLaw P)) := by ring
  simp_rw [he]
  have hv := rectangular_difference_energy_le (experiment P n m)
    (fun w => rectangularOutcomeAverage f w-∫ z, f z ∂obsLaw P)
    (fun w => rectangularAverage H w-∫ p, H p ∂(xaLaw P).prod (obsLaw P))
    (hA.sub (memLp_const _)) (hR.sub (memLp_const _))
  have ha := rectangular_outcome_role_energy_le (n := n) (m := m) P hn f hf
  change (∫ w, (rectangularOutcomeAverage f w-∫ z, f z ∂obsLaw P)^2 ∂experiment P n m) ≤ _ at ha
  calc
    _ ≤ _ := hv
    _ ≤ 2*((3/(n:ℝ))*(∫ z, (f z)^2 ∂obsLaw P)) + 2*B := by gcongr
    _ = _ := by ring

/-- A bounded localized observation feature has inverse-volume second moment.  Given [the specified input W](hyp:W), [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input X](hyp:X), [the specified input hX](hyp:hX), [its uniform pushforward identity](hyp:hμ), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hfB](hyp:hfB), [the rectangular localized mark energy conclusion](goal) holds. -/
lemma rectangular_localized_mark_energy {W : Type*} [MeasurableSpace W]
    (μ : Measure W) [IsProbabilityMeasure μ] (d : ℕ) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (X : W → Cov d) (hX : Measurable X) (hμ : μ.map X = uniformLaw d)
    (f : W → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hfB : ∀ w, X w ∈ locCube d h → |f w| ≤ B) :
    MemLp (fun w => locWeight h (X w)*f w) 2 μ ∧
    (∫ w, (locWeight h (X w)*f w)^2 ∂μ) ≤ B^2/h^d := by
  have hm := (rectangular_localized_mark_memLp_top μ d h hh X hX f hf B hB hfB).mono_exponent (by simp : (2:ℝ≥0∞) ≤ ∞)
  have hw := (rectangular_localized_mark_memLp_top μ d h hh X hX (fun _ => 1) measurable_const
    1 zero_le_one (fun _ _ => by norm_num)).mono_exponent (by simp : (2:ℝ≥0∞) ≤ ∞)
  simp only [mul_one] at hw
  refine ⟨hm, ?_⟩
  calc
    _ ≤ ∫ w, B^2*(locWeight h (X w))^2 ∂μ := by
      apply integral_mono hm.integrable_sq (hw.integrable_sq.const_mul _)
      intro w
      by_cases hx : X w ∈ locCube d h
      · have he := mul_self_le_mul_self (abs_nonneg (f w)) (hfB w hx)
        have hs : (f w)^2 ≤ B^2 := by simpa only [← pow_two, sq_abs] using he
        nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (locWeight h (X w)))]
      · simp [locWeight, hx]
    _ = _ := by rw [integral_const_mul, rectangular_record_locWeight_square_integral μ d h hh hh' X hX hμ]; ring

/-- Localized bounded marks give the sampling envelope for an actual moment coordinate.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input f0](hyp:f0), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf0](hyp:hf0), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input M](hyp:M), [the specified input hM](hyp:hM), [the specified input hf0M](hyp:hf0M), [the specified input hfM](hyp:hfM), [the specified input hgM](hyp:hgM), [the rectangular marked moment bound conclusion](goal) holds. -/
lemma rectangular_marked_moment_bound {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) (hn : 2 ≤ n)
    (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (f0 : Cov d × Bool × Bool → ℝ) (f : Cov d × Bool → ℝ)
    (g : Cov d × Bool × Bool → ℝ) (hf0 : Measurable f0) (hf : Measurable f) (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M)
    (hf0M : ∀ z, z.1 ∈ locCube d h → |f0 z| ≤ M)
    (hfM : ∀ z, z.1 ∈ locCube d h → |f z| ≤ M)
    (hgM : ∀ z, z.1 ∈ locCube d h → |g z| ≤ M) :
    let H := fun p : (Cov d × Bool) × (Cov d × Bool × Bool) =>
      locWeight h p.1.1 * locWeight h p.2.1 * fineKernel d h J p.1.1 p.2.1 * f p.1 * g p.2
    let F := fun w : Sample d n m => rectangularOutcomeAverage (fun z => locWeight h z.1*f0 z) w - rectangularAverage H w
    let K := 6*M^2 + 12*(M*M)^2*(((Fintype.card (PolyIdx d):ℝ)*((4:ℝ)^d)^2)^2+1)
    MemLp F 2 (experiment P n m) ∧
    (∫ w, (F w-∫ z, F z ∂experiment P n m)^2 ∂experiment P n m) ≤
      K*(1/((n:ℝ)*h^d)+(Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d /
        ((n:ℝ)*((n:ℝ)+m)*h^(2*d))) := by
  dsimp only
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  have hμ := rectangular_xaLaw_covariates P hP
  have hν := rectangular_obsLaw_covariates P hP
  obtain ⟨h0, he0⟩ := rectangular_localized_mark_energy (obsLaw P) d h hh hh' Prod.fst
    measurable_fst hν f0 hf0 M hM hf0M
  obtain ⟨hH, _⟩ := rectangular_marked_kernel_energy_le (xaLaw P) (obsLaw P) d h J hh hh' hJ
    Prod.fst Prod.fst measurable_fst measurable_fst hμ hν f g hf hg M M hM hM hfM hgM
  have hv := rectangular_marked_kernel_variance_bound (xaLaw P) (obsLaw P) d n m hn h J hh hh' hJ
    Prod.fst Prod.fst measurable_fst measurable_fst hμ hν f g hf hg M M hM hM hfM hgM
  dsimp only at hv
  let H := fun p : (Cov d × Bool) × (Cov d × Bool × Bool) =>
    locWeight h p.1.1 * locWeight h p.2.1 * fineKernel d h J p.1.1 p.2.1 * f p.1 * g p.2
  have hHm : Measurable H := by dsimp [H]; fun_prop
  have h0m : Measurable (fun z : Cov d × Bool × Bool => locWeight h z.1*f0 z) := by fun_prop
  have hv' := rectangular_original_average_variance_le (n := n) (m := m) P H hHm _ hv
  obtain ⟨hm, he⟩ := rectangular_original_moment_variance_le P hn
    (fun z => locWeight h z.1*f0 z) h0m h0 H hHm hH _ hv' 
  refine ⟨hm, he.trans ?_⟩
  have ha : 0 ≤ 1/((n:ℝ)*h^d) := by positivity
  have hb : 0 ≤ (Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d / ((n:ℝ)*((n:ℝ)+m)*h^(2*d)) := by positivity
  have hcoef : 0 ≤ 6*M^2 := by positivity
  have he0' := mul_le_mul_of_nonneg_left he0 (by positivity : 0 ≤ 6/(n:ℝ))
  calc
    _ ≤ (6/(n:ℝ))*(M^2/h^d) + 2*(6*((M*M)^2*
      (((Fintype.card (PolyIdx d):ℝ)*((4:ℝ)^d)^2)^2+1)))*
      (1/((n:ℝ)*h^d)+(Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d /
        ((n:ℝ)*((n:ℝ)+m)*h^(2*d))) := by linarith only [he0']
    _ ≤ _ := by
      have heq : (6/(n:ℝ))*(M^2/h^d) = 6*M^2*(1/((n:ℝ)*h^d)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]; ring
      rw [heq]
      nlinarith only [mul_nonneg hcoef hb]

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
