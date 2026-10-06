module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CountLaplace
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.MassBudget

/-! # Observed subcell masses

Connect the observed treatment-event probabilities in the count Laplace bounds
to the propensity integrals used by the mass-budget argument, roadmap (15)--(16).
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory

/-- The conditional propensity version integrates to the joint treated mass
on each measurable covariate set. -/
-- @node: latent_treated_mass_eq_setIntegral
lemma latent_treated_mass_eq_setIntegral {d : ℕ} (P : Law d) (M : ℝ)
    [IsProbabilityMeasure P.full] (hsem : LawSemantics P M)
    (he : AEMeasurable P.e P.xLaw)
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) :
    P.full.real {u | u.2.1 = true ∧ u.1 ∈ B} = ∫ x in B, P.e x ∂P.xLaw := by
  let X : Full d → (Fin d → ℝ) := Prod.fst
  let T : Set (Full d) := {u | u.2.1 = true}
  let Z : Full d → ℝ := T.indicator (fun _ => 1)
  have hX : Measurable X := by fun_prop
  have hT : MeasurableSet T := (measurableSet_singleton true).preimage (by fun_prop)
  have hZ : Integrable Z P.full := by
    apply Integrable.of_mem_Icc 0 1 (by fun_prop)
    filter_upwards with u
    by_cases hu : u ∈ T <;> simp [Z, hu]
  have hce : P.full[Z | MeasurableSpace.comap X inferInstance] =ᵐ[P.full]
      fun u => P.e (X u) := by
    have hfun : Z = (fun u : Full d => if u.2.1 then (1 : ℝ) else 0) := by
      funext u
      cases h : u.2.1 <;> simp [Z, T, h]
    simpa only [hfun, X] using hsem.1
  have hpre : MeasurableSet[MeasurableSpace.comap X inferInstance] (X ⁻¹' B) :=
    ⟨B, hB, rfl⟩
  calc
    _ = ∫ u in X ⁻¹' B, Z u ∂P.full := by
      rw [show Z = T.indicator (fun _ => (1 : ℝ)) from rfl,
        setIntegral_indicator hT]
      simp only [setIntegral_const, smul_eq_mul, mul_one, Measure.real]
      congr 2
      ext u
      change (u.2.1 = true ∧ u.1 ∈ B) ↔ (u.1 ∈ B ∧ u.2.1 = true)
      exact and_comm
    _ = ∫ u in X ⁻¹' B, P.full[Z | MeasurableSpace.comap X inferInstance] u
        ∂P.full := (setIntegral_condExp (Measurable.comap_le hX) hZ hpre).symm
    _ = ∫ u in X ⁻¹' B, P.e (X u) ∂P.full :=
      setIntegral_congr_ae (hB.preimage hX) (hce.mono (fun _ h _ => h))
    _ = _ := (setIntegral_map hB he.aestronglyMeasurable hX.aemeasurable).symm

/-- Consistency transfers each observed arm-and-covariate event to the latent law. -/
-- @node: observed_arm_mass_eq_latent
lemma observed_arm_mass_eq_latent {d : ℕ} (P : Law d)
    (hcons : Consistency P) (arm : Bool)
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) :
    P.obs.real {o | o.2.1 = arm ∧ o.1 ∈ B} =
      P.full.real {u | u.2.1 = arm ∧ u.1 ∈ B} := by
  have hE : MeasurableSet {o : Obs d | o.2.1 = arm ∧ o.1 ∈ B} :=
    ((measurableSet_singleton arm).preimage (by fun_prop)).inter
      (hB.preimage measurable_fst)
  unfold Measure.real
  congr 1
  rw [hcons.2, Measure.map_apply_of_aemeasurable (observedRecord_aemeasurable P hcons) hE]
  apply measure_congr
  filter_upwards [hcons.1] with u hu
  apply propext
  change ((P.observedRecord u).2.1 = arm ∧ (P.observedRecord u).1 ∈ B) ↔
    (u.2.1 = arm ∧ u.1 ∈ B)
  rw [hu]
  rfl

/-- Under uniform design the observed treated mass is the Lebesgue propensity
integral, without a global measurable version outside the cube. -/
-- @node: observed_treated_mass_eq_integral
lemma observed_treated_mass_eq_integral {d : ℕ} (P : Law d) (M : ℝ)
    [IsProbabilityMeasure P.full] (hsem : LawSemantics P M)
    (hcons : Consistency P) (hdesign : UniformDesign P)
    (hmeas : MeasurablePropensity P)
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) (hsub : B ⊆ cube d) :
    P.obs.real {o | o.2.1 = true ∧ o.1 ∈ B} = ∫ x in B, P.e x ∂volume := by
  have he : AEMeasurable P.e P.xLaw := by
    rw [hdesign]
    exact (propensity_integrableOn_cube P hmeas).aemeasurable
  rw [observed_arm_mass_eq_latent P hcons true B hB,
    latent_treated_mass_eq_setIntegral P M hsem he B hB, hdesign]
  rw [Measure.restrict_restrict hB, Set.inter_eq_self_of_subset_left hsub]

/-- The control event has the complementary propensity mass on every measurable
covariate set, the identity used in roadmap (C5). -/
-- @node: observed_control_mass_eq_integral
lemma observed_control_mass_eq_integral {d : ℕ} (P : Law d) (M : ℝ)
    [IsProbabilityMeasure P.full] (hsem : LawSemantics P M)
    (hcons : Consistency P) (hdesign : UniformDesign P)
    (hmeas : MeasurablePropensity P)
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) (hsub : B ⊆ cube d) :
    P.obs.real {o | o.2.1 = false ∧ o.1 ∈ B} =
      ∫ x in B, 1 - P.e x ∂volume := by
  have htotal : P.xLaw.real B =
      P.full.real {u | u.2.1 = false ∧ u.1 ∈ B} +
      P.full.real {u | u.2.1 = true ∧ u.1 ∈ B} := by
    have hunion : {u : Full d | u.2.1 = false ∧ u.1 ∈ B} ∪
        {u : Full d | u.2.1 = true ∧ u.1 ∈ B} = Prod.fst ⁻¹' B := by
      ext u
      cases h : u.2.1 <;> simp [h]
    have hdis : Disjoint {u : Full d | u.2.1 = false ∧ u.1 ∈ B}
        {u : Full d | u.2.1 = true ∧ u.1 ∈ B} := by
      apply Set.disjoint_left.mpr
      intro u hu hv
      have hf := hu.1
      have ht := hv.1
      rw [hf] at ht
      cases ht
    rw [← measureReal_union hdis
      (((measurableSet_singleton true).preimage (by fun_prop)).inter
        (hB.preimage measurable_fst)), hunion]
    unfold Law.xLaw Measure.real
    rw [Measure.map_apply measurable_fst hB]
  have hvol : P.xLaw.real B = volume.real B := by
    rw [hdesign]
    unfold Measure.real
    rw [Measure.restrict_apply hB, Set.inter_eq_self_of_subset_left hsub]
  have hint := (propensity_integrableOn_cube P hmeas).mono_set hsub
  have hfinite : volume B ≠ ⊤ := ne_top_of_le_ne_top (by simp [cube, Real.volume_Icc_pi])
    (measure_mono hsub)
  have hconst : IntegrableOn (fun _ : Fin d → ℝ => (1 : ℝ)) B volume :=
    integrableOn_const hfinite
  have hsubint : (∫ x in B, 1 - P.e x ∂volume) =
      volume.real B - ∫ x in B, P.e x ∂volume := by
    rw [integral_sub hconst hint]
    simp
  rw [hsubint, observed_arm_mass_eq_latent P hcons false B hB]
  have ht := observed_treated_mass_eq_integral P M hsem hcons hdesign hmeas B hB hsub
  rw [observed_arm_mass_eq_latent P hcons true B hB] at ht
  rw [hvol, ht] at htotal
  linarith

/-- The observed treated probability of a norming subcell equals its
propensity-integral mass. -/
-- @node: observed_treated_subcell_mass
lemma observed_treated_subcell_mass {d : ℕ} (P : Law d) (β γ C L M : ℝ)
    (hP : LawClass d β γ C L M P) (j : ℕ)
    (Q : Fin d → Fin (2 ^ j)) (ℓ : MultiIndex d (polynomialOrder β)) :
    P.obs.real {o | o.2.1 = true ∧ o.1 ∈
      scaledSubcell d j (polynomialOrder β) (normingSubcells d β).radius Q ℓ} =
      treatedSubcellMass P j (polynomialOrder β) (normingSubcells d β).radius Q ℓ := by
  let : IsProbabilityMeasure P.full := hP.iid.1
  exact observed_treated_mass_eq_integral P M hP.semantics hP.consistency
    hP.uniformDesign hP.measurablePropensity _
    (scaledSubcell_measurable d j (polynomialOrder β) (normingSubcells d β) Q ℓ)
    (scaledSubcell_subset_cube d j (polynomialOrder β) (normingSubcells d β) Q ℓ)

/-- Strict control overlap bounds every observed norming-subcell mass below
by its volume times the overlap constant, roadmap (C5). -/
-- @node: observed_control_subcell_mass_lower
lemma observed_control_subcell_mass_lower {d : ℕ} (P : Law d)
    (β γ C L M κ : ℝ) (hP : CATEClass d β γ C L M κ P) (j : ℕ)
    (Q : Fin d → Fin (2 ^ j)) (ℓ : MultiIndex d (polynomialOrder β)) :
    κ * (2 * dyadicWidth j * (normingSubcells d β).radius) ^ d ≤
      P.obs.real {o | o.2.1 = false ∧ o.1 ∈
        scaledSubcell d j (polynomialOrder β) (normingSubcells d β).radius Q ℓ} := by
  let : IsProbabilityMeasure P.full := hP.iid.1
  let B := scaledSubcell d j (polynomialOrder β) (normingSubcells d β).radius Q ℓ
  have hB : MeasurableSet B :=
    scaledSubcell_measurable d j (polynomialOrder β) (normingSubcells d β) Q ℓ
  have hsub : B ⊆ cube d :=
    scaledSubcell_subset_cube d j (polynomialOrder β) (normingSubcells d β) Q ℓ
  have hfinite : volume B ≠ ⊤ := ne_top_of_le_ne_top
    (by simp [cube, Real.volume_Icc_pi]) (measure_mono hsub)
  have hconst : IntegrableOn (fun _ : Fin d → ℝ => (1 : ℝ)) B volume :=
    integrableOn_const hfinite
  have he := (propensity_integrableOn_cube P hP.measurablePropensity).mono_set hsub
  have hoverlap : ∀ᵐ x ∂volume.restrict B, κ ≤ 1 - P.e x := by
    have h := hP.controlOverlap
    unfold ControlOverlap at h
    rw [hP.uniformDesign] at h
    exact ae_restrict_of_ae_restrict_of_subset hsub h
  rw [observed_control_mass_eq_integral P M hP.semantics hP.consistency
    hP.uniformDesign hP.measurablePropensity B hB hsub]
  calc
    _ = ∫ _x in B, κ ∂volume := by
      simp only [setIntegral_const, smul_eq_mul]
      rw [scaledSubcell_volume d j (polynomialOrder β) (normingSubcells d β) Q ℓ]
      ring
    _ ≤ _ := integral_mono_ae (integrableOn_const hfinite) (hconst.sub he) hoverlap

/-- The minimum control count obeys the binomial Laplace bound with the
uniform overlap mass from (C5), including zero-count subcells in (C15). -/
-- @node: minimumControlCount_laplace_le
lemma minimumControlCount_laplace_le {d n : ℕ} (P : Law d)
    (β γ C L M κ : ℝ) (hP : CATEClass d β γ C L M κ P)
    (hn : 0 < n) (j : ℕ) (Q : Fin d → Fin (2 ^ j)) (s : ℝ) (hs : 0 ≤ s) :
    (∫ sample, Real.exp (-s * (minimumCellCount sample false j (polynomialOrder β)
        (normingSubcells d β).radius Q : ℝ)) ∂P.sample n) ≤
      (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
        Real.exp (-(n : ℝ) *
          (κ * (2 * dyadicWidth j * (normingSubcells d β).radius) ^ d) *
          (1 - Real.exp (-s))) := by
  apply minimumCellCount_laplace_le P hP.iid hP.consistency hn false j
    (polynomialOrder β) (normingSubcells d β).radius Q s _ hs
  exact observed_control_subcell_mass_lower P β γ C L M κ hP j Q

/-- Equation (15) in its propensity-integral form, with the zero-count
branch retained and no independence assumption between subcell counts. -/
-- @node: minimumTreatedCount_laplace_le
lemma minimumTreatedCount_laplace_le {d n : ℕ} (P : Law d) (β γ C L M : ℝ)
    (hP : LawClass d β γ C L M P) (hn : 0 < n) (j : ℕ)
    (Q : Fin d → Fin (2 ^ j)) (s : ℝ) (hs : 0 ≤ s) :
    (∫ sample, Real.exp (-s * (minimumCellCount sample true j (polynomialOrder β)
        (normingSubcells d β).radius Q : ℝ)) ∂P.sample n) ≤
      (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
        Real.exp (-(n : ℝ) *
          minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q *
          (1 - Real.exp (-s))) := by
  apply minimumCellCount_laplace_le P hP.iid hP.consistency hn true j
    (polynomialOrder β) (normingSubcells d β).radius Q s _ hs
  intro ℓ
  rw [observed_treated_subcell_mass P β γ C L M hP j Q ℓ]
  exact Finset.inf'_le _ (Finset.mem_univ ℓ)

/-- Count admissibility has an exponential lower-tail bound in the true
minimum propensity mass of the cell. -/
-- @node: minimumTreatedCount_lower_tail
lemma minimumTreatedCount_lower_tail {d n : ℕ} (P : Law d) (β γ C L M : ℝ)
    (hP : LawClass d β γ C L M P) (hn : 0 < n) (j : ℕ)
    (Q : Fin d → Fin (2 ^ j)) (s a : ℝ) (hs : 0 ≤ s) :
    (P.sample n).real {sample | (minimumCellCount sample true j (polynomialOrder β)
      (normingSubcells d β).radius Q : ℝ) ≤ a} ≤
      (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
        Real.exp (s * a - (n : ℝ) *
          minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q *
          (1 - Real.exp (-s))) := by
  apply minimumCellCount_lower_tail_of_tilt P hP.iid hP.consistency hn true j
    (polynomialOrder β) (normingSubcells d β).radius Q s _ a hs
  intro ℓ
  rw [observed_treated_subcell_mass P β γ C L M hP j Q ℓ]
  exact Finset.inf'_le _ (Finset.mem_univ ℓ)

/-- The first ordered-mass bound gives a strictly positive minimum treated
mass in every dyadic cell, uniformly over the law class. -/
-- @node: minimumTreatedMass_uniform_lower
lemma minimumTreatedMass_uniform_lower (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ a : ℝ, 0 < a ∧ ∀ (P : Law d), LawClass d β γ C L M P →
      ∀ (j : ℕ) (Q : Fin d → Fin (2 ^ j)),
        a * (dyadicWidth j) ^ effectiveDimension d γ ≤
          minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q := by
  classical
  obtain ⟨a, ha, horder⟩ := ordered_subcell_mass d β γ C
    hparam.1 hparam.2.1 hparam.2.2.1
    (mass_budget C γ hparam.2.2.2.1 hparam.2.2.1)
  refine ⟨a, ha, ?_⟩
  intro P hP j Q
  have hcard := horder P j hP.uniformDesign hP.measurablePropensity hP.globalTail
    1 (by omega) (Fintype.card_pos_iff.mpr ⟨Q⟩)
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at hcard
  by_contra hbad
  have hmem : Q ∈ Finset.univ.filter (fun Q : Fin d → Fin (2 ^ j) =>
      minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q <
        a * (dyadicWidth j) ^ effectiveDimension d γ) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ Q, lt_of_not_ge hbad⟩
  have hpos := Finset.card_pos.mpr ⟨Q, hmem⟩
  omega

/-- The minimum propensity mass is nonnegative, since each selected subcell
lies in the cube where the propensity version has range `[0,1]`. -/
-- @node: minimumTreatedMass_nonneg
lemma minimumTreatedMass_nonneg {d : ℕ} (P : Law d) (β γ C L M : ℝ)
    (hP : LawClass d β γ C L M P) (j : ℕ) (Q : Fin d → Fin (2 ^ j)) :
    0 ≤ minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q := by
  obtain ⟨ℓ, hℓ⟩ := minimumTreatedMass_attained P j (polynomialOrder β)
    (normingSubcells d β).radius Q
  rw [hℓ]
  unfold treatedSubcellMass
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict
    (scaledSubcell_measurable d j (polynomialOrder β) (normingSubcells d β) Q ℓ)] with x hx
  exact (hP.measurablePropensity.2 x
    (scaledSubcell_subset_cube d j (polynomialOrder β) (normingSubcells d β) Q ℓ hx)).1

/-- The compact-tilt comparison after (15) gives the quadratic deviation
exponent needed in (16), uniformly for thresholds up to twice the outcome bound. -/
-- @node: minimumTreatedCount_quadratic_laplace
lemma minimumTreatedCount_quadratic_laplace (d : ℕ) (β γ C L M c₁ : ℝ)
    (hparam : ParameterDomain d β γ C L M) (hc₁ : 0 < c₁) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (n j : ℕ) (P : Law d),
      LawClass d β γ C L M P → 0 < n → ∀ (Q : Fin d → Fin (2 ^ j))
      (t : ℝ), 0 < t → t ≤ 2 * M →
      (∫ sample, Real.exp (-(c₁ * t ^ 2 / M ^ 2) *
        (minimumCellCount sample true j (polynomialOrder β)
          (normingSubcells d β).radius Q : ℝ)) ∂P.sample n) ≤
        (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
          Real.exp (-c₂ * (n : ℝ) * minimumTreatedMass P j (polynomialOrder β)
            (normingSubcells d β).radius Q * t ^ 2 / M ^ 2) := by
  let c₂ : ℝ := (1 - Real.exp (-(4 * c₁))) / 4
  have hc₂ : 0 < c₂ := by
    have hlt : Real.exp (-(4 * c₁)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    dsimp [c₂]
    positivity
  refine ⟨c₂, hc₂, ?_⟩
  intro n j P hP hn Q t ht htM
  have hM : 0 < M := hparam.2.2.2.2.2
  have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM
  have hs : 0 ≤ c₁ * t ^ 2 / M ^ 2 := by positivity
  have hsS : c₁ * t ^ 2 / M ^ 2 ≤ 4 * c₁ := by
    apply (div_le_iff₀ hM2).mpr
    have ht2 : t ^ 2 ≤ 4 * M ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ht2 hc₁.le]
  have hlinear := one_sub_exp_neg_lower_on_interval (4 * c₁)
    (c₁ * t ^ 2 / M ^ 2) (by positivity) hs hsS
  have hcoef : (1 - Real.exp (-(4 * c₁))) / (4 * c₁) *
      (c₁ * t ^ 2 / M ^ 2) = c₂ * t ^ 2 / M ^ 2 := by
    dsimp [c₂]
    field_simp
  rw [hcoef] at hlinear
  apply (minimumTreatedCount_laplace_le P β γ C L M hP hn j Q _ hs).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  have hmass := minimumTreatedMass_nonneg P β γ C L M hP j Q
  have hmul := mul_le_mul_of_nonneg_left hlinear
    (mul_nonneg (Nat.cast_nonneg n) hmass)
  convert neg_le_neg hmul using 1 <;> first | rfl | ring

/-- The compact-tilt comparison gives the quadratic control count exponent
in roadmap (C15), uniformly up to twice the outcome bound. -/
-- @node: minimumControlCount_quadratic_laplace
lemma minimumControlCount_quadratic_laplace (d : ℕ) (β γ C L M κ c₁ : ℝ)
    (hparam : ParameterDomain d β γ C L M) (hc₁ : 0 < c₁) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (n j : ℕ) (P : Law d),
      CATEClass d β γ C L M κ P → 0 < n → ∀ (Q : Fin d → Fin (2 ^ j))
      (t : ℝ), 0 < t → t ≤ 2 * M →
      (∫ sample, Real.exp (-(c₁ * t ^ 2 / M ^ 2) *
        (minimumCellCount sample false j (polynomialOrder β)
          (normingSubcells d β).radius Q : ℝ)) ∂P.sample n) ≤
        (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
          Real.exp (-c₂ * (n : ℝ) *
            (κ * (2 * dyadicWidth j * (normingSubcells d β).radius) ^ d) *
            t ^ 2 / M ^ 2) := by
  let c₂ : ℝ := (1 - Real.exp (-(4 * c₁))) / 4
  have hc₂ : 0 < c₂ := by
    have hlt : Real.exp (-(4 * c₁)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    dsimp [c₂]
    positivity
  refine ⟨c₂, hc₂, ?_⟩
  intro n j P hP hn Q t ht htM
  have hM : 0 < M := hparam.2.2.2.2.2
  have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM
  have hs : 0 ≤ c₁ * t ^ 2 / M ^ 2 := by positivity
  have hsS : c₁ * t ^ 2 / M ^ 2 ≤ 4 * c₁ := by
    apply (div_le_iff₀ hM2).mpr
    have ht2 : t ^ 2 ≤ 4 * M ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ht2 hc₁.le]
  have hlinear := one_sub_exp_neg_lower_on_interval (4 * c₁)
    (c₁ * t ^ 2 / M ^ 2) (by positivity) hs hsS
  have hcoef : (1 - Real.exp (-(4 * c₁))) / (4 * c₁) *
      (c₁ * t ^ 2 / M ^ 2) = c₂ * t ^ 2 / M ^ 2 := by
    dsimp [c₂]
    field_simp
  rw [hcoef] at hlinear
  apply (minimumControlCount_laplace_le P β γ C L M κ hP hn j Q _ hs).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  have hmass : 0 ≤ κ * (2 * dyadicWidth j * (normingSubcells d β).radius) ^ d := by
    have hκ := hP.controlParameter.1
    have hr := (normingSubcells d β).radius_pos
    have hw : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
    positivity
  have hmul := mul_le_mul_of_nonneg_left hlinear
    (mul_nonneg (Nat.cast_nonneg n) hmass)
  convert neg_le_neg hmul using 1 <;> first | rfl | ring

end CausalSmith.Stat.GlobalTailDesignRobustCate
