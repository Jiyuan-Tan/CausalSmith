module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.Welfare

/-! # Bounded policy risks

The bounded conditional effect makes canonical welfare integrable and bounds
raw regret even for policy representatives that are not measurable globally.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory

-- @node: sampleLaw_isProbability
/-- A well-formed row law has a probability-valued observable sample law. -/
lemma sampleLaw_isProbability (P : RowLaw) (n : ℕ) (hwf : WellFormed P) :
    IsProbabilityMeasure (sampleLaw P n) := by
  haveI : IsProbabilityMeasure P.full := hwf.1
  have hmap : Measurable (fun o : FullRow =>
      (⟨o.X, o.A, o.Y⟩ : Observation)) := by
    apply measurable_comap_iff.mpr
    have hfull : Measurable (fun o : FullRow =>
        (o.X, o.A, o.Y, o.Y0, o.Y1)) := comap_measurable _
    have hproj : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ =>
        (t.1, t.2.1, t.2.2.1)) := by fun_prop
    exact hproj.comp hfull
  haveI : IsProbabilityMeasure P.obsLaw := by
    unfold RowLaw.obsLaw
    exact Measure.isProbabilityMeasure_map hmap.aemeasurable
  unfold sampleLaw
  infer_instance

/-- The score marginal of a well-formed row law is a probability measure. -/
-- @node: scoreLaw_isProbability
lemma scoreLaw_isProbability (P : RowLaw) (hwf : WellFormed P) :
    IsProbabilityMeasure P.PX := by
  haveI : IsProbabilityMeasure P.full := hwf.1
  exact Measure.isProbabilityMeasure_map fullRow_X_measurable.aemeasurable

/-- The canonical welfare integrand is integrable under the bounded-effect clause. -/
-- @node: canonicalWelfare_integrable
@[fun_prop] lemma canonicalWelfare_integrable (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e) :
    Integrable (fun x => (if canonicalPolicy P x then (1:ℝ) else 0) * P.tau x)
      P.PX := by
  haveI : IsProbabilityMeasure P.PX := scoreLaw_isProbability P hP.wf
  have hsupport : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0:ℝ) 1 :=
    (ae_map_iff fullRow_X_measurable.aemeasurable measurableSet_Icc).2
      (ae_iff.mpr hP.wf.2.1)
  have ht : AEMeasurable P.tau P.PX := by
    have hr := aemeasurable_restrict_of_measurable_subtype (μ := P.PX)
      measurableSet_Icc hP.wf.2.2.2.2.1
    rwa [Measure.restrict_eq_self_of_ae_mem hsupport] at hr
  have hm : AEStronglyMeasurable
      (fun x => (if canonicalPolicy P x then (1:ℝ) else 0) * P.tau x) P.PX := by
    have hi : AEMeasurable (fun x => max (P.tau x) 0) P.PX := by
      fun_prop
    convert hi.aestronglyMeasurable using 1
    ext x
    by_cases h : 0 ≤ P.tau x
    · simp [canonicalPolicy, h, max_eq_left h]
    · simp [canonicalPolicy, h, max_eq_right (le_of_not_ge h)]
  refine Integrable.mono' (integrable_const (2:ℝ)) hm ?_
  filter_upwards [hP.effectBound] with x hx
  cases canonicalPolicy P x <;> simpa using (le_trans (by simp) hx)

/-- Raw binary-policy regret lies between zero and four, including representatives
whose welfare integral is assigned zero by the Bochner convention. -/
-- @node: rawRegret_bounds
lemma rawRegret_bounds (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (φ : ℝ → Bool) : 0 ≤ rawRegret P φ ∧ rawRegret P φ ≤ 4 := by
  haveI : IsProbabilityMeasure P.PX := scoreLaw_isProbability P hP.wf
  have hstar := canonicalWelfare_integrable α γ θ n P e hP
  have hnonneg (x : ℝ) :
      0 ≤ (if canonicalPolicy P x then (1:ℝ) else 0) * P.tau x := by
    by_cases h : 0 ≤ P.tau x <;> simp [canonicalPolicy, h]
  have hle (x : ℝ) :
      (if φ x then (1:ℝ) else 0) * P.tau x ≤
        (if canonicalPolicy P x then (1:ℝ) else 0) * P.tau x := by
    by_cases h : 0 ≤ P.tau x <;> cases φ x <;>
      simp [canonicalPolicy, h] <;> linarith
  have hw (ψ : ℝ → Bool) : |rawWelfare P ψ| ≤ 2 := by
    have h := norm_integral_le_of_norm_le_const (μ := P.PX) (C := 2)
      (f := fun x => (if ψ x then (1:ℝ) else 0) * P.tau x) (by
        filter_upwards [hP.effectBound] with x hx
        cases ψ x <;> simpa using (le_trans (by simp) hx))
    simpa [rawWelfare, Real.norm_eq_abs] using h
  constructor
  · unfold rawRegret rawWelfare
    by_cases hi : Integrable (fun x => (if φ x then (1:ℝ) else 0) * P.tau x) P.PX
    · exact sub_nonneg.mpr (integral_mono hi hstar hle)
    · rw [integral_undef hi, sub_zero]
      exact integral_nonneg hnonneg
  · have hs := (abs_le.mp (hw (canonicalPolicy P))).2
    have hφ := (abs_le.mp (hw φ)).1
    unfold rawRegret
    linarith

/-- The sample and independent uniform randomizer form a probability experiment. -/
-- @node: experiment_isProbability
lemma experiment_isProbability (P : RowLaw) (n : ℕ) (hwf : WellFormed P) :
    IsProbabilityMeasure (experiment P n) := by
  haveI : IsProbabilityMeasure (sampleLaw P n) := sampleLaw_isProbability P n hwf
  haveI : IsProbabilityMeasure uniformRandomizer := by
    unfold uniformRandomizer
    constructor
    simp
  unfold experiment
  infer_instance

/-- Every randomized binary-policy risk lies between zero and four. -/
-- @node: expectedRawRegret_bounds
lemma expectedRawRegret_bounds (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (Φ : Learner n) :
    0 ≤ (∫ du, rawRegret P (fun x => Φ e du.1 du.2 x) ∂experiment P n) ∧
    (∫ du, rawRegret P (fun x => Φ e du.1 du.2 x) ∂experiment P n) ≤ 4 := by
  haveI : IsProbabilityMeasure (experiment P n) := experiment_isProbability P n hP.wf
  constructor
  · exact integral_nonneg (fun du => (rawRegret_bounds α γ θ n P e hP _).1)
  · have h := norm_integral_le_of_norm_le_const (μ := experiment P n) (C := 4)
      (f := fun du => rawRegret P (fun x => Φ e du.1 du.2 x)) (by
        filter_upwards with du
        rw [Real.norm_eq_abs, abs_of_nonneg (rawRegret_bounds α γ θ n P e hP _).1]
        exact (rawRegret_bounds α γ θ n P e hP _).2)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)

/-- Both threshold orientations and constants are Borel policies on the score space. -/
-- @node: thresholdClass_subset_binaryPolicyClass
lemma thresholdClass_subset_binaryPolicyClass (π : ℝ → Bool)
    (hπ : π ∈ thresholdClass) :
    Measurable (fun x : Set.Icc (0:ℝ) 1 => π x) := by
  change Measurable (fun x : Set.Icc (0:ℝ) 1 => π x)
  rcases hπ with h | h | ⟨t, ht, h⟩ | ⟨t, ht, h⟩
  · have heq : (fun x : Set.Icc (0:ℝ) 1 => π x) = fun _ => false :=
      funext (fun x => h x x.2)
    rw [heq]
    fun_prop
  · have heq : (fun x : Set.Icc (0:ℝ) 1 => π x) = fun _ => true :=
      funext (fun x => h x x.2)
    rw [heq]
    fun_prop
  · have heq : (fun x : Set.Icc (0:ℝ) 1 => π x) = fun x : Set.Icc (0:ℝ) 1 => leftThr t x :=
      funext (fun x => h x x.2)
    rw [heq]
    unfold leftThr
    apply measurable_to_bool
    convert (measurableSet_le measurable_subtype_coe measurable_const :
      MeasurableSet {x : Set.Icc (0:ℝ) 1 | (x:ℝ) ≤ t}) using 1
    ext x
    simp
  · have heq : (fun x : Set.Icc (0:ℝ) 1 => π x) = fun x : Set.Icc (0:ℝ) 1 => rightThr t x :=
      funext (fun x => h x x.2)
    rw [heq]
    unfold rightThr
    apply measurable_to_bool
    convert (measurableSet_le measurable_const measurable_subtype_coe :
      MeasurableSet {x : Set.Icc (0:ℝ) 1 | t ≤ (x:ℝ)}) using 1
    ext x
    simp

/-- A measurable binary policy has an integrable effect-weighted disagreement loss. -/
@[fun_prop]
-- @node: effectDisagreement_integrable
lemma effectDisagreement_integrable (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (φ : ℝ → Bool) (hφ : φ ∈ binaryPolicyClass) :
    Integrable (fun x => effectMagnitude P x *
      (if φ x = canonicalPolicy P x then (0:ℝ) else 1)) P.PX := by
  haveI : IsProbabilityMeasure P.PX := scoreLaw_isProbability P hP.wf
  have hs : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0:ℝ) 1 := ae_iff.mpr hP.score.2
  have hm : Measurable (fun x : Set.Icc (0:ℝ) 1 => effectMagnitude P x *
      (if φ x = canonicalPolicy P x then (0:ℝ) else 1)) := by
    have ht : Measurable (fun x : Set.Icc (0:ℝ) 1 => P.tau x) :=
      hP.wf.2.2.2.2.1
    have hp : Measurable (fun x : Set.Icc (0:ℝ) 1 => φ x) := hφ
    have hc : Measurable (fun x : Set.Icc (0:ℝ) 1 => canonicalPolicy P x) := by
      unfold canonicalPolicy
      apply measurable_to_bool
      simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
        (measurableSet_le measurable_const ht :
          MeasurableSet {x : Set.Icc (0:ℝ) 1 | 0 ≤ P.tau x})
    unfold effectMagnitude
    exact ht.norm.mul (Measurable.ite (measurableSet_eq_fun hp hc)
      measurable_const measurable_const)
  have ha : AEMeasurable (fun x => effectMagnitude P x *
      (if φ x = canonicalPolicy P x then (0:ℝ) else 1)) P.PX := by
    have hr := aemeasurable_restrict_of_measurable_subtype
      (f := fun x => effectMagnitude P x *
        (if φ x = canonicalPolicy P x then (0:ℝ) else 1)) (μ := P.PX)
      measurableSet_Icc hm
    rwa [Measure.restrict_eq_self_of_ae_mem hs] at hr
  refine Integrable.mono' (integrable_const (2:ℝ)) ha.aestronglyMeasurable ?_
  filter_upwards [hP.effectBound] with x hx
  split_ifs
  · simp
  · simpa [effectMagnitude, Real.norm_eq_abs] using hx

/-- A jointly Borel family of policies has measurable regret as a function of
its parameter. Only measurability on the supported score interval is needed. -/
-- @node: rawRegret_family_measurable
@[fun_prop] lemma rawRegret_family_measurable {Ω : Type*} [MeasurableSpace Ω]
    (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ)
    (hP : LawClass α γ θ n P e) (ψ : Ω → ℝ → Bool)
    (hψ : Measurable (fun z : Ω × Set.Icc (0:ℝ) 1 => ψ z.1 z.2)) :
    Measurable (fun w => rawRegret P (ψ w)) := by
  haveI : IsProbabilityMeasure P.PX := scoreLaw_isProbability P hP.wf
  have hs : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0:ℝ) 1 := ae_iff.mpr hP.score.2
  have ht : Measurable (fun x : Set.Icc (0:ℝ) 1 => P.tau x) :=
    hP.wf.2.2.2.2.1
  have hm : Measurable (fun z : Ω × Set.Icc (0:ℝ) 1 =>
      (if ψ z.1 z.2 then (1:ℝ) else 0) * P.tau z.2) := by
    have hb : Measurable (fun z : Ω × Set.Icc (0:ℝ) 1 =>
        if ψ z.1 z.2 then (1:ℝ) else 0) := by
      exact measurable_const.ite (hψ (measurableSet_singleton true)) measurable_const
    exact hb.mul (ht.comp measurable_snd)
  have hi : Measurable (fun w => ∫ x : Set.Icc (0:ℝ) 1,
      (if ψ w x then (1:ℝ) else 0) * P.tau x
      ∂Measure.comap Subtype.val P.PX) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have heq (w : Ω) : rawWelfare P (ψ w) =
      ∫ x : Set.Icc (0:ℝ) 1, (if ψ w x then (1:ℝ) else 0) * P.tau x
        ∂Measure.comap Subtype.val P.PX := by
    rw [integral_subtype_comap (μ := P.PX) measurableSet_Icc
      (fun x => (if ψ w x then (1:ℝ) else 0) * P.tau x),
      Measure.restrict_eq_self_of_ae_mem hs]
    rfl
  simp_rw [rawRegret, heq]
  exact hi.const_sub _

/-- Bounded effects make each measurable family of policy regrets integrable
under any finite parameter law. -/
-- @node: rawRegret_family_integrable
@[fun_prop] lemma rawRegret_family_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ)
    (hP : LawClass α γ θ n P e) (ψ : Ω → ℝ → Bool)
    (hψ : Measurable (fun z : Ω × Set.Icc (0:ℝ) 1 => ψ z.1 z.2)) :
    Integrable (fun w => rawRegret P (ψ w)) μ := by
  apply Integrable.of_bound
    (rawRegret_family_measurable α γ θ n P e hP ψ hψ).aestronglyMeasurable 4
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (rawRegret_bounds α γ θ n P e hP _).1]
  exact (rawRegret_bounds α γ θ n P e hP _).2

end CausalSmith.Stat.ScorethresholdOverlapRegret
