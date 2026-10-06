module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Procedure

/-!
Exact quadratic inversion endpoints and the abstract training/evaluation coverage-to-length
transfer.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Lower reported energy endpoint, including the singleton-zero fallback. -/
def invLower (z a d : ℝ) : ℝ :=
  if invDiscriminant z a d < 0 ∨ invUpperV z a d < invLowerV z a d then 0
  else (invLowerV z a d) ^ 2
/-- Upper reported energy endpoint, including the singleton-zero fallback. -/
def invUpper (z a d : ℝ) : ℝ :=
  if invDiscriminant z a d < 0 ∨ invUpperV z a d < invLowerV z a d then 0
  else (invUpperV z a d) ^ 2
/-- Abstract rule on the independent training and evaluation product. -/
def scalarReported {F E : Type*} (m : ℕ) (zeta a d : ℝ) (Z : F × E → ℝ) : F × E → Set ℝ :=
  fun ω => if m < 3 ∨ (1 / 100 : ℝ) < zeta then Set.Icc 0 16 else invSet (Z ω) a d

/-- Completing the square gives the closed interval between the two real roots. -/
-- @node: inversion_quadratic_upper
lemma inversion_quadratic_upper (z a d v : ℝ) :
    v ^ 2 - a * v ≤ z + d ↔
      0 ≤ invDiscriminant z a d ∧
      (a - Real.sqrt (invDiscriminant z a d)) / 2 ≤ v ∧
      v ≤ (a + Real.sqrt (invDiscriminant z a d)) / 2 := by
  constructor
  · intro h
    have hs : (2 * v - a) ^ 2 ≤ invDiscriminant z a d := by
      dsimp [invDiscriminant]
      nlinarith
    have hD : 0 ≤ invDiscriminant z a d := (sq_nonneg _).trans hs
    have habs := abs_le.mp (Real.abs_le_sqrt hs)
    exact ⟨hD, by linarith [habs.1], by linarith [habs.2]⟩
  · rintro ⟨hD, hlo, hhi⟩
    have hs := sq_le_sq' (a := 2 * v - a)
      (b := Real.sqrt (invDiscriminant z a d)) (by linarith) (by linarith)
    rw [Real.sq_sqrt hD] at hs
    dsimp [invDiscriminant] at hs
    nlinarith

/-- The other quadratic is increasing on the nonnegative half-line. -/
-- @node: inversion_quadratic_lower
lemma inversion_quadratic_lower (z a d v : ℝ) (ha : 0 ≤ a) (hv : 0 ≤ v) :
    z - d ≤ v ^ 2 + a * v ↔
      (-a + Real.sqrt (a ^ 2 + 4 * max (z - d) 0)) / 2 ≤ v := by
  have harg : 0 ≤ a ^ 2 + 4 * max (z - d) 0 := by positivity
  have hpos : 0 ≤ 2 * v + a := by positivity
  rw [show (-a + Real.sqrt (a ^ 2 + 4 * max (z - d) 0)) / 2 ≤ v ↔
    Real.sqrt (a ^ 2 + 4 * max (z - d) 0) ≤ 2 * v + a by constructor <;> intro h <;> linarith]
  rw [Real.sqrt_le_left hpos]
  have hprod : 0 ≤ a * v := mul_nonneg ha hv
  constructor
  · intro h
    have hm : max (z - d) 0 ≤ v ^ 2 + a * v := max_le h (by positivity)
    nlinarith
  · intro h
    have hm : z - d ≤ max (z - d) 0 := le_max_left _ _
    nlinarith

/-- In square-root coordinates the acceptance set is precisely the intersection of the
quadratic root interval with the reporting range. -/
-- @node: inversion_feasible_iff
lemma inversion_feasible_iff (z a d v : ℝ) (ha : 0 ≤ a) (hv : 0 ≤ v) :
    (v ^ 2 ∈ Set.Icc (0 : ℝ) 16 ∧ |z - v ^ 2| ≤ a * v + d) ↔
      0 ≤ invDiscriminant z a d ∧
      invLowerV z a d ≤ v ∧ v ≤ invUpperV z a d := by
  have hrange : v ^ 2 ∈ Set.Icc (0 : ℝ) 16 ↔ v ≤ 4 := by
    constructor
    · intro h
      nlinarith [h.2]
    · intro h
      exact ⟨sq_nonneg _, by nlinarith⟩
  rw [hrange, abs_le]
  have hupper := inversion_quadratic_upper z a d v
  have hlower := inversion_quadratic_lower z a d v ha hv
  simp only [invLowerV, invUpperV, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨hr, h1, h2⟩
    obtain ⟨hD, hlo, hhi⟩ := hupper.mp (by linarith)
    exact ⟨hD, ⟨⟨hv, hlower.mp (by linarith)⟩, hlo⟩, hr, hhi⟩
  · rintro ⟨hD, ⟨⟨_, hlo⟩, hroot⟩, hr, hhi⟩
    have h1 := hupper.mpr ⟨hD, hroot, hhi⟩
    have h2 := hlower.mpr hlo
    exact ⟨hr, by linarith, by linarith⟩

/-- The lower square-root endpoint is always nonnegative. -/
-- @node: invLowerV_nonneg
lemma invLowerV_nonneg (z a d : ℝ) : 0 ≤ invLowerV z a d := by
  exact (le_max_left _ _).trans (le_max_left _ _)

/-- Ordered feasible endpoints lie in the square-root reporting range. -/
-- @node: inversion_endpoint_range
lemma inversion_endpoint_range (z a d : ℝ)
    (horder : invLowerV z a d ≤ invUpperV z a d) :
    0 ≤ invLowerV z a d ∧ 0 ≤ invUpperV z a d ∧
      invLowerV z a d ≤ 4 ∧ invUpperV z a d ≤ 4 := by
  have hlo := invLowerV_nonneg z a d
  have hhi : invUpperV z a d ≤ 4 := min_le_left _ _
  exact ⟨hlo, hlo.trans horder, horder.trans hhi, hhi⟩

/-- Nonnegative squaring sends an ordered root interval to the energy interval. -/
-- @node: inversion_square_interval
lemma inversion_square_interval (s lo hi : ℝ) (hs : 0 ≤ s) (hlo : 0 ≤ lo)
    (hhi : 0 ≤ hi) :
    (lo ≤ Real.sqrt s ∧ Real.sqrt s ≤ hi) ↔ s ∈ Set.Icc (lo ^ 2) (hi ^ 2) := by
  rw [Real.le_sqrt hlo hs, Real.sqrt_le_left hhi]
  rfl

/-- The feasible energy set is the squared endpoint interval, or empty exactly on the
stated failure branches. -/
-- @node: inversion_acceptance_set
lemma inversion_acceptance_set (z a d : ℝ) (ha : 0 ≤ a) :
    {s : ℝ | s ∈ Set.Icc 0 16 ∧ |z - s| ≤ a * Real.sqrt s + d} =
      if invDiscriminant z a d < 0 ∨ invUpperV z a d < invLowerV z a d then ∅
      else Set.Icc ((invLowerV z a d) ^ 2) ((invUpperV z a d) ^ 2) := by
  let S := {s : ℝ | s ∈ Set.Icc 0 16 ∧ |z - s| ≤ a * Real.sqrt s + d}
  have hmem (s : ℝ) : s ∈ S ↔ 0 ≤ s ∧ 0 ≤ invDiscriminant z a d ∧
      invLowerV z a d ≤ Real.sqrt s ∧ Real.sqrt s ≤ invUpperV z a d := by
    constructor
    · intro h
      have h' := (inversion_feasible_iff z a d (Real.sqrt s) ha (Real.sqrt_nonneg s)).mp
        (by simpa only [S, Set.mem_ofPred_eq, Real.sq_sqrt h.1.1] using h)
      exact ⟨h.1.1, h'⟩
    · rintro ⟨hs, h⟩
      have h' := (inversion_feasible_iff z a d (Real.sqrt s) ha (Real.sqrt_nonneg s)).mpr h
      simpa only [S, Set.mem_ofPred_eq, Real.sq_sqrt hs] using h'
  by_cases hbad : invDiscriminant z a d < 0 ∨ invUpperV z a d < invLowerV z a d
  · rw [if_pos hbad]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨_, hD, hlo, hhi⟩ := (hmem s).mp hs
    rcases hbad with h | h
    · exact (not_lt_of_ge hD) h
    · exact (not_lt_of_ge (hlo.trans hhi)) h
  · rw [if_neg hbad]
    have hD : 0 ≤ invDiscriminant z a d := le_of_not_gt (fun h => hbad (Or.inl h))
    have horder : invLowerV z a d ≤ invUpperV z a d :=
      le_of_not_gt (fun h => hbad (Or.inr h))
    obtain ⟨hlo, hhi, _, _⟩ := inversion_endpoint_range z a d horder
    ext s
    change s ∈ S ↔ _
    constructor
    · intro hs
      obtain ⟨hs, _, hr⟩ := (hmem s).mp hs
      exact (inversion_square_interval s _ _ hs hlo hhi).mp hr
    · intro hs
      have hs0 : 0 ≤ s := (sq_nonneg _).trans hs.1
      exact (hmem s).mpr ⟨hs0, hD,
        (inversion_square_interval s _ _ hs0 hlo hhi).mpr hs⟩

/-- The empty-set replacement agrees with the total endpoint formula. -/
-- @node: invSet_eq_endpoint_interval
lemma invSet_eq_endpoint_interval (z a d : ℝ) (ha : 0 ≤ a) :
    invSet z a d = Set.Icc (invLower z a d) (invUpper z a d) := by
  rw [invSet, inversion_acceptance_set z a d ha]
  by_cases hbad : invDiscriminant z a d < 0 ∨ invUpperV z a d < invLowerV z a d
  · simp [hbad, invLower, invUpper, Set.Icc_self]
  · have horder : invLowerV z a d ≤ invUpperV z a d :=
      le_of_not_gt (fun h => hbad (Or.inr h))
    obtain ⟨hlo, hhi, _, _⟩ := inversion_endpoint_range z a d horder
    have hsquare : (invLowerV z a d) ^ 2 ≤ (invUpperV z a d) ^ 2 :=
      (sq_le_sq₀ hlo hhi).mpr horder
    have hne := Set.nonempty_Icc.mpr hsquare
    simp [hbad, invLower, invUpper, hne.ne_empty]

/-- The two equivalent ways to write the endpoint failure guard give the same interval. -/
-- @node: invEndpoints_eq_endpoint_interval
lemma invEndpoints_eq_endpoint_interval (z a d : ℝ) :
    invEndpoints z a d = Set.Icc (invLower z a d) (invUpper z a d) := by
  by_cases hD : invDiscriminant z a d < 0
  · simp [invEndpoints, invLower, invUpper, hD, Set.Icc_self]
  · by_cases horder : invLowerV z a d ≤ invUpperV z a d
    · simp [invEndpoints, invLower, invUpper, hD, horder, not_lt_of_ge horder]
    · simp [invEndpoints, invLower, invUpper, hD, horder, lt_of_not_ge horder,
        Set.Icc_self]

/-- The total reported endpoints are Borel measurable in the statistic. -/
-- @node: inversion_endpoints_measurable
lemma inversion_endpoints_measurable (a d : ℝ) :
    Measurable (fun z => invLower z a d) ∧ Measurable (fun z => invUpper z a d) := by
  have hD : Measurable (fun z => invDiscriminant z a d) := by
    unfold invDiscriminant
    fun_prop
  have hlo : Measurable (fun z => invLowerV z a d) := by
    unfold invLowerV invDiscriminant
    fun_prop
  have hhi : Measurable (fun z => invUpperV z a d) := by
    unfold invUpperV invDiscriminant
    fun_prop
  have hbad : MeasurableSet {z | invDiscriminant z a d < 0 ∨
      invUpperV z a d < invLowerV z a d} :=
    (measurableSet_lt hD measurable_const).union (measurableSet_lt hhi hlo)
  exact ⟨measurable_const.ite hbad (hlo.pow_const 2),
    measurable_const.ite hbad (hhi.pow_const 2)⟩

/-- Acceptance and the singleton fallback both stay in the energy reporting range. -/
-- @node: invSet_subset
lemma invSet_subset (z a d : ℝ) : invSet z a d ⊆ Set.Icc 0 16 := by
  intro s hs
  dsimp only [invSet] at hs
  split_ifs at hs with hempty
  · simp only [Set.mem_singleton_iff] at hs
    subst s
    norm_num
  · exact hs.1

/-- An accepted energy obeys the scalar envelope obtained by completing a square. -/
-- @node: inversion_accepted_energy_bound
lemma inversion_accepted_energy_bound (z a d s : ℝ) (hs : 0 ≤ s)
    (haccept : |z - s| ≤ a * Real.sqrt s + d) :
    s ≤ 2 * |z| + a ^ 2 + 2 * d := by
  have herr := (abs_le.mp haccept).1
  have hz := le_abs_self z
  have hsq := sq_nonneg (Real.sqrt s - a)
  nlinarith [Real.sq_sqrt hs]

/-- The reported interval length is bounded by the scalar envelope, including empty
acceptance sets replaced by a singleton. -/
-- @node: invSet_length_bound
lemma invSet_length_bound (z a d : ℝ) (hd : 0 ≤ d) :
    intervalLength (invSet z a d) ≤ 2 * |z| + a ^ 2 + 2 * d := by
  let S := {s : ℝ | s ∈ Set.Icc 0 16 ∧ |z - s| ≤ a * Real.sqrt s + d}
  have hbound : 0 ≤ 2 * |z| + a ^ 2 + 2 * d := by positivity
  by_cases hempty : S = ∅
  · have heq : invSet z a d = {0} := by
      change (if S = ∅ then {0} else S) = {0}
      exact if_pos hempty
    simp [heq, intervalLength, hbound]
  · have hne := Set.nonempty_iff_ne_empty.mpr hempty
    have heq : invSet z a d = S := by
      change (if S = ∅ then {0} else S) = S
      exact if_neg hempty
    have hlo : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
    have hsup : sSup S ≤ 2 * |z| + a ^ 2 + 2 * d :=
      csSup_le hne (fun s hs => inversion_accepted_energy_bound z a d s hs.1.1 hs.2)
    have hinf : 0 ≤ sInf S := le_csInf hne (fun s hs => hs.1.1)
    rw [heq, intervalLength, if_neg hempty]
    linarith

/-- Deterministic inversion certificate: exact measurable endpoints, connectedness,
reporting range, and the envelope used in the null expected-length proof. -/
-- @node: scalar_inversion_geometry
lemma scalar_inversion_geometry (a d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    Measurable (fun z => invLower z a d) ∧ Measurable (fun z => invUpper z a d) ∧
      ∀ z : ℝ, Set.OrdConnected (invSet z a d) ∧ invSet z a d ⊆ Set.Icc 0 16 ∧
        invSet z a d = invEndpoints z a d ∧
        invSet z a d = Set.Icc (invLower z a d) (invUpper z a d) ∧
        intervalLength (invSet z a d) ≤ 2 * |z| + a ^ 2 + 2 * d := by
  obtain ⟨hlo, hhi⟩ := inversion_endpoints_measurable a d
  refine ⟨hlo, hhi, fun z => ?_⟩
  have heq := invSet_eq_endpoint_interval z a d ha
  refine ⟨?_, invSet_subset z a d, ?_, heq, invSet_length_bound z a d hd⟩
  · rw [heq]
    infer_instance
  · exact heq.trans (invEndpoints_eq_endpoint_interval z a d).symm

/-- Ordered inversion endpoints make the interval length a measurable difference. -/
-- @node: inversion_length_eq
lemma inversion_length_eq (z a d : ℝ) (ha : 0 ≤ a) :
    intervalLength (invSet z a d) = invUpper z a d - invLower z a d := by
  have horder : invLower z a d ≤ invUpper z a d := by
    unfold invLower invUpper
    split_ifs with hbad
    · exact le_rfl
    · obtain ⟨hlo, hhi, _, _⟩ := inversion_endpoint_range z a d
        (le_of_not_gt (fun h => hbad (Or.inr h)))
      exact (sq_le_sq₀ hlo hhi).mpr (le_of_not_gt (fun h => hbad (Or.inr h)))
  rw [invSet_eq_endpoint_interval z a d ha, intervalLength,
    if_neg (Set.nonempty_Icc.mpr horder).ne_empty, csSup_Icc horder, csInf_Icc horder]

/-- The inversion length is between zero and sixteen on every statistic realization. -/
-- @node: inversion_length_range
lemma inversion_length_range (z a d : ℝ) :
    intervalLength (invSet z a d) ∈ Set.Icc 0 16 := by
  have hne : (invSet z a d).Nonempty := by
    dsimp only [invSet]
    split_ifs with h
    · exact Set.singleton_nonempty 0
    · exact Set.nonempty_iff_ne_empty.mpr h
  have hr := invSet_subset z a d
  have hlo : BddBelow (invSet z a d) := ⟨0, fun x hx => (hr hx).1⟩
  have hhi : BddAbove (invSet z a d) := ⟨16, fun x hx => (hr hx).2⟩
  rw [intervalLength, if_neg hne.ne_empty]
  have horder := csInf_le_csSup hne hlo hhi
  have hinf := le_csInf hne (fun x hx => (hr hx).1)
  have hsup := csSup_le hne (fun x hx => (hr hx).2)
  constructor <;> linarith

/-- An envelope-accepted target belongs to the total inversion interval. -/
-- @node: inversion_covers_accepted
lemma inversion_covers_accepted (z a d s : ℝ) (hs : s ∈ Set.Icc 0 16)
    (he : |z - s| ≤ a * Real.sqrt s + d) : s ∈ invSet z a d := by
  have hmem : s ∈ {s : ℝ | s ∈ Set.Icc 0 16 ∧ |z - s| ≤ a * Real.sqrt s + d} := ⟨hs, he⟩
  have hne := Set.nonempty_iff_ne_empty.mp ⟨s, hmem⟩
  simpa only [invSet, if_neg hne] using hmem

/-- Integrating a conditional probability floor over good training realizations gives
its probability floor times the good-training probability. -/
-- @node: inversion_product_event_lower
lemma inversion_product_event_lower {F E : Type*} [MeasurableSpace F] [MeasurableSpace E]
    (μ : Measure F) (ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set (F × E)) (G : Set F) (hA : MeasurableSet A) (hG : MeasurableSet G)
    (p : ℝ)
    (hfloor : ∀ᵐ x ∂μ, x ∈ G → p ≤ ν.real (Prod.mk x ⁻¹' A)) :
    p * μ.real G ≤ (μ.prod ν).real A := by
  have hm := measurable_measure_prodMk_left (ν := ν) hA
  have hi : Integrable (fun x => ν.real (Prod.mk x ⁻¹' A)) μ :=
    Integrable.of_bound hm.ennreal_toReal.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one))
  have heq : (μ.prod ν).real A = ∫ x, ν.real (Prod.mk x ⁻¹' A) ∂μ := by
    rw [measureReal_def, Measure.prod_apply hA]
    exact (integral_toReal hm.aemeasurable
      (Filter.Eventually.of_forall (fun x => measure_lt_top _ _))).symm
  rw [heq]
  have hle : G.indicator (fun _ : F => p) ≤ᵐ[μ]
      (fun x => ν.real (Prod.mk x ⁻¹' A)) := by
    filter_upwards [hfloor] with x hx
    by_cases hg : x ∈ G
    · simpa [Set.indicator_of_mem hg] using hx hg
    · simp [Set.indicator_of_notMem hg, measureReal_nonneg]
  have hb := integral_mono_ae ((integrable_const p).indicator hG) hi hle
  simpa only [integral_indicator_const _ hG, smul_eq_mul, mul_comm] using hb

/-- A bounded loss costs at most its good-training mean allowance plus its uniform
bound times the bad-training probability. -/
-- @node: inversion_product_mean_upper
lemma inversion_product_mean_upper {F E : Type*} [MeasurableSpace F] [MeasurableSpace E]
    (μ : Measure F) (ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : F × E → ℝ) (hf : Measurable f) (G : Set F) (hG : MeasurableSet G)
    (C M : ℝ) (hC : 0 ≤ C)
    (hrange : ∀ ω, f ω ∈ Set.Icc 0 M)
    (hgood : ∀ᵐ x ∂μ, x ∈ G → (∫ y, f (x, y) ∂ν) ≤ C) :
    (∫ ω, f ω ∂μ.prod ν) ≤ C + M * μ.real Gᶜ := by
  have hi : Integrable f (μ.prod ν) := Integrable.of_bound hf.aestronglyMeasurable M
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hrange ω).1]
      exact (hrange ω).2))
  have hsec (x : F) : (∫ y, f (x, y) ∂ν) ≤ M := by
    have him : Integrable (fun y => f (x, y)) ν :=
      Integrable.of_bound (hf.comp measurable_prodMk_left).aestronglyMeasurable M
        (Filter.Eventually.of_forall (fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hrange (x, y)).1]
          exact (hrange (x, y)).2))
    simpa using integral_mono him (integrable_const M) (fun y => (hrange (x, y)).2)
  rw [integral_prod f hi]
  have hb := integral_mono_ae hi.integral_prod_left
    (((integrable_const C).indicator hG).add ((integrable_const M).indicator hG.compl))
    (by
      filter_upwards [hgood] with x hx
      by_cases hg : x ∈ G
      · simpa [hg] using hx hg
      · simpa [hg] using hsec x)
  simp only [Pi.add_apply] at hb
  rw [integral_add ((integrable_const C).indicator hG)
    ((integrable_const M).indicator hG.compl), integral_indicator_const _ hG,
    integral_indicator_const _ hG.compl, smul_eq_mul, smul_eq_mul] at hb
  have hmass : μ.real G ≤ 1 := measureReal_le_one
  nlinarith

/-- A finite nonnegative first-moment allowance supplies integrability and the real
expectation bound needed for the length envelope. -/
-- @node: inversion_first_moment_real
lemma inversion_first_moment_real {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (f : E → ℝ) (hf : Measurable f) (d : ℝ) (hd : 0 ≤ d)
    (h : (∫⁻ y, ENNReal.ofReal |f y| ∂ν) ≤ ENNReal.ofReal d) :
    Integrable (fun y => |f y|) ν ∧ (∫ y, |f y| ∂ν) ≤ d := by
  have hn : 0 ≤ᵐ[ν] (fun y => |f y|) := Filter.Eventually.of_forall (fun y => abs_nonneg _)
  have hi : Integrable (fun y => |f y|) ν :=
    ⟨(show Measurable (fun y => |f y|) by fun_prop).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hn).mpr
      (h.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn] at h
  exact (ENNReal.ofReal_le_ofReal_iff hd).mp h

-- @node: lem:scalar-inversion
/-- Scalar inversion is exactly the explicit connected endpoint interval; conditional error
and first-moment antecedents transfer to full coverage and null length with constant four. -/
lemma scalar_inversion :
    (∀ a d : ℝ, 0 ≤ a → 0 ≤ d →
      Measurable (fun z => invLower z a d) ∧ Measurable (fun z => invUpper z a d) ∧
      ∀ z : ℝ, Set.OrdConnected (invSet z a d) ∧ invSet z a d ⊆ Set.Icc 0 16 ∧
        invSet z a d = invEndpoints z a d ∧
        invSet z a d = Set.Icc (invLower z a d) (invUpper z a d) ∧
        intervalLength (invSet z a d) ≤ 2 * |z| + a ^ 2 + 2 * d) ∧
    (∀ (F E : Type) [MeasurableSpace F] [MeasurableSpace E]
      (μ : Measure F) (ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      (m : ℕ) (zeta a d s : ℝ) (Z : F × E → ℝ) (G : Set F),
      Measurable Z → MeasurableSet G → 0 ≤ zeta → zeta ≤ 1 / 100 →
      μ.real Gᶜ ≤ zeta → 0 ≤ a → 0 ≤ d → s ∈ Set.Icc 0 16 →
      (∀ᵐ train ∂μ, train ∈ G → (19 / 20 : ℝ) ≤ ν.real
        {eval | |Z (train, eval) - s| ≤ a * Real.sqrt s + d}) →
      (∀ᵐ train ∂μ, train ∈ G → (∫⁻ eval, ENNReal.ofReal |Z (train, eval) - s| ∂ν) ≤
        ENNReal.ofReal (a * Real.sqrt s + d)) →
      (9 / 10 : ℝ) ≤ (μ.prod ν).real {ω | s ∈ scalarReported m zeta a d Z ω} ∧
      (s = 0 → 3 ≤ m →
        (∫ ω, intervalLength (scalarReported m zeta a d Z ω) ∂μ.prod ν) ≤
          4 * (a ^ 2 + d) + 16 * zeta)) := by
  refine ⟨scalar_inversion_geometry, ?_⟩
  intro F E _ _ μ ν _ _ m zeta a d s Z G hZ hG hzeta hzetaSmall hbad ha hd hs hcov hmom
  have hfallback : ¬ (1 / 100 : ℝ) < zeta := not_lt_of_ge hzetaSmall
  constructor
  · by_cases hsmall : m < 3
    · have heq : {ω | s ∈ scalarReported m zeta a d Z ω} = Set.univ := by
        ext ω
        simp only [scalarReported, if_pos (Or.inl hsmall), Set.mem_ofPred_eq,
          Set.mem_univ, iff_true]
        exact hs
      rw [heq, probReal_univ]
      norm_num
    · let A : Set (F × E) := {ω | |Z ω - s| ≤ a * Real.sqrt s + d}
      have hA : MeasurableSet A := by
        dsimp [A]
        exact measurableSet_le (by fun_prop) measurable_const
      have hlower : (19 / 20 : ℝ) * μ.real G ≤ (μ.prod ν).real A :=
        inversion_product_event_lower μ ν A G hA hG (19 / 20)
          (by simpa only [A, Set.preimage_ofPred_eq] using hcov)
      have hsubset : A ⊆ {ω | s ∈ scalarReported m zeta a d Z ω} := by
        intro ω hω
        simp only [scalarReported, if_neg (not_or.mpr ⟨hsmall, hfallback⟩),
          Set.mem_ofPred_eq]
        exact inversion_covers_accepted (Z ω) a d s hs hω
      have hmono := measureReal_mono (μ := μ.prod ν) hsubset
      have hmass := measureReal_add_measureReal_compl hG (μ := μ)
      rw [probReal_univ] at hmass
      linarith
  · intro hs0 hm
    have hbranch : ¬ (m < 3 ∨ (1 / 100 : ℝ) < zeta) :=
      not_or.mpr ⟨Nat.not_lt.mpr hm, hfallback⟩
    have heq : scalarReported m zeta a d Z = (fun ω => invSet (Z ω) a d) := by
      funext ω
      exact if_neg hbranch
    rw [heq]
    let f : F × E → ℝ := fun ω => intervalLength (invSet (Z ω) a d)
    have hmeas : Measurable f := by
      have hlo := (inversion_endpoints_measurable a d).1.comp hZ
      have hhi := (inversion_endpoints_measurable a d).2.comp hZ
      have he : f = (fun ω => invUpper (Z ω) a d - invLower (Z ω) a d) :=
        funext (fun ω => inversion_length_eq (Z ω) a d ha)
      rw [he]
      fun_prop
    have hgood : ∀ᵐ x ∂μ, x ∈ G → (∫ y, f (x, y) ∂ν) ≤ a ^ 2 + 4 * d := by
      filter_upwards [hmom] with x hx hxG
      have herr : (∫⁻ y, ENNReal.ofReal |Z (x, y)| ∂ν) ≤ ENNReal.ofReal d := by
        simpa [hs0] using hx hxG
      obtain ⟨hierr, hmean⟩ := inversion_first_moment_real ν (fun y => Z (x, y))
        (by fun_prop) d hd herr
      have hif : Integrable (fun y => f (x, y)) ν :=
        Integrable.of_bound (hmeas.comp measurable_prodMk_left).aestronglyMeasurable 16
          (Filter.Eventually.of_forall (fun y => by
            have hr := inversion_length_range (Z (x, y)) a d
            rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
            exact hr.2))
      have hib : Integrable (fun y => 2 * |Z (x, y)| + a ^ 2 + 2 * d) ν :=
        ((hierr.const_mul 2).add (integrable_const _)).add (integrable_const _)
      have hb := integral_mono hif hib (fun y => invSet_length_bound (Z (x, y)) a d hd)
      rw [integral_add (show Integrable (fun y => 2 * |Z (x, y)| + a ^ 2) ν from
        (hierr.const_mul 2).add (integrable_const (a ^ 2))) (integrable_const (2 * d)),
        integral_add (hierr.const_mul 2) (integrable_const (a ^ 2)), integral_const_mul,
        integral_const, integral_const, probReal_univ, one_smul, one_smul] at hb
      linarith
    have hb := inversion_product_mean_upper μ ν f hmeas G hG (a ^ 2 + 4 * d) 16
      (by positivity) (fun ω => inversion_length_range (Z ω) a d) hgood
    change (∫ ω, f ω ∂μ.prod ν) ≤ _
    nlinarith [sq_nonneg a]


end CausalSmith.Stat.DensityEffectRoughNull
