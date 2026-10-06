module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Estimators
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Global mass budget and ordered norming-cell masses -/
@[expose] public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped BigOperators

-- @node: scaledSubcell_eq_supBall
/-- An interior norming cube scales to an ordinary closed coordinate cube;
the dyadic ownership condition is automatic in the interior. -/
lemma scaledSubcell_eq_supBall (d j m : ℕ) (ε : ℝ)
    (H : NormingSubcells d m) (hε : ε = H.radius)
    (Q : Fin d → Fin (2 ^ j)) (ℓ : MultiIndex d m) :
    scaledSubcell d j m ε Q ℓ =
      Causalean.Stat.Nonparametric.supBall
        (fun i => cellOrigin d j Q i + dyadicWidth j * normingNode d m ℓ i)
        (dyadicWidth j * ε) := by
  have hw : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have hmul : (2 : ℝ) ^ j * dyadicWidth j = 1 := by
    unfold dyadicWidth
    field_simp
  ext x
  constructor
  · rintro ⟨_, hx⟩
    intro i
    have hi := hx i
    change |(x i - cellOrigin d j Q i) / dyadicWidth j - normingNode d m ℓ i| ≤ ε at hi
    have heq : x i - (cellOrigin d j Q i + dyadicWidth j * normingNode d m ℓ i) =
        dyadicWidth j * ((x i - cellOrigin d j Q i) / dyadicWidth j - normingNode d m ℓ i) := by
      field_simp
      ring
    rw [heq, abs_mul, abs_of_pos hw]
    exact (mul_le_mul_of_nonneg_left hi (le_of_lt hw)).trans_eq (by ring)
  · intro hx
    have hnorm : (fun i => (x i - cellOrigin d j Q i) / dyadicWidth j) ∈
        normingCube d m ε ℓ := by
      intro i
      have hi := hx i
      change |x i - (cellOrigin d j Q i + dyadicWidth j * normingNode d m ℓ i)| ≤
        dyadicWidth j * ε at hi
      have heq : x i - (cellOrigin d j Q i + dyadicWidth j * normingNode d m ℓ i) =
          dyadicWidth j * ((x i - cellOrigin d j Q i) / dyadicWidth j - normingNode d m ℓ i) := by
        field_simp
        ring
      rw [heq, abs_mul, abs_of_pos hw] at hi
      exact (mul_le_mul_iff_of_pos_left hw).mp hi
    refine ⟨?_, hnorm⟩
    have hinterior := H.interior ℓ (by simpa [hε] using hnorm)
    apply funext
    intro i
    have hu := hinterior i (Set.mem_univ i)
    have hq : (Q i).val < 2 ^ j := (Q i).isLt
    have hxi : (Q i : ℝ) < (2 : ℝ) ^ j * x i ∧
        (2 : ℝ) ^ j * x i < (Q i : ℝ) + 1 := by
      dsimp [cellOrigin] at hu ⊢
      have hlo : (Q i : ℝ) * dyadicWidth j < x i := by
        have := (lt_div_iff₀ hw).mp hu.1
        linarith
      have hhi : x i < (Q i : ℝ) * dyadicWidth j + dyadicWidth j := by
        have := (div_lt_iff₀ hw).mp hu.2
        linarith
      have hQeq : (Q i : ℝ) = (2 : ℝ) ^ j * ((Q i : ℝ) * dyadicWidth j) := by
        rw [mul_left_comm, hmul, mul_one]
      have hQeq' : (Q i : ℝ) + 1 =
          (2 : ℝ) ^ j * ((Q i : ℝ) * dyadicWidth j + dyadicWidth j) := by
        rw [mul_add, ← hQeq, hmul]
      constructor
      · rw [hQeq]
        exact mul_lt_mul_of_pos_left hlo hpow
      · rw [hQeq']
        exact mul_lt_mul_of_pos_left hhi hpow
    have hfloor : Nat.floor ((2 : ℝ) ^ j * x i) = (Q i).val :=
      (Nat.floor_eq_iff (le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg _) hxi.1))).2
        ⟨le_of_lt hxi.1, hxi.2⟩
    apply Fin.ext
    simp [cellIndex, hfloor, Nat.min_eq_left (Nat.le_sub_one_of_lt hq)]

-- @node: scaledSubcell_volume
/-- All scaled norming cubes at a fixed radius and scale have the same volume. -/
lemma scaledSubcell_volume (d j m : ℕ) (H : NormingSubcells d m)
    (Q : Fin d → Fin (2 ^ j)) (ℓ : MultiIndex d m) :
    volume.real (scaledSubcell d j m H.radius Q ℓ) =
      (2 * dyadicWidth j * H.radius) ^ d := by
  rw [scaledSubcell_eq_supBall d j m H.radius H rfl]
  change (volume (Causalean.Stat.Nonparametric.supBall
    (fun i => cellOrigin d j Q i + dyadicWidth j * normingNode d m ℓ i)
    (dyadicWidth j * H.radius))).toReal = _
  rw [Causalean.Stat.Nonparametric.volume_supBall]
  have hw : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
  have hr : 0 < H.radius := H.radius_pos
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
  ring

-- @node: scaledSubcell_measurable
lemma scaledSubcell_measurable (d j m : ℕ) (H : NormingSubcells d m)
    (Q : Fin d → Fin (2 ^ j)) (ℓ : MultiIndex d m) :
    MeasurableSet (scaledSubcell d j m H.radius Q ℓ) := by
  rw [scaledSubcell_eq_supBall d j m H.radius H rfl]
  exact Causalean.Stat.Nonparametric.measurableSet_supBall _ _

-- @node: scaledSubcell_subset_cube
lemma scaledSubcell_subset_cube (d j m : ℕ) (H : NormingSubcells d m)
    (Q : Fin d → Fin (2 ^ j)) (ℓ : MultiIndex d m) :
    scaledSubcell d j m H.radius Q ℓ ⊆ cube d := by
  intro x hx i _
  have hw : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
  have hmul : (2 : ℝ) ^ j * dyadicWidth j = 1 := by
    unfold dyadicWidth
    field_simp
  have hu := H.interior ℓ hx.2
  have hui := hu i (Set.mem_univ i)
  have hlo : (Q i : ℝ) * dyadicWidth j < x i := by
    have := (lt_div_iff₀ hw).mp hui.1
    dsimp [cellOrigin] at this
    linarith
  have hhi : x i < ((Q i : ℝ) + 1) * dyadicWidth j := by
    have := (div_lt_iff₀ hw).mp hui.2
    dsimp [cellOrigin] at this
    nlinarith
  have hq : (Q i : ℝ) + 1 ≤ (2 : ℝ) ^ j := by
    exact_mod_cast Nat.succ_le_iff.mpr (Q i).isLt
  constructor
  · have hq0 : (0 : ℝ) ≤ (Q i : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hq0 (le_of_lt hw)]
  · calc
      x i ≤ ((Q i : ℝ) + 1) * dyadicWidth j := le_of_lt hhi
      _ ≤ (2 : ℝ) ^ j * dyadicWidth j :=
        mul_le_mul_of_nonneg_right hq (le_of_lt hw)
      _ = 1 := hmul

-- @node: propensity_integrableOn_cube
lemma propensity_integrableOn_cube {d : ℕ} (P : Law d)
    (hP : MeasurablePropensity P) : IntegrableOn P.e (cube d) volume := by
  have hcubeMeas : MeasurableSet (cube d) := by simp [cube]
  have hcube : volume (cube d) = 1 := by simp [cube, Real.volume_Icc_pi]
  let μ : Measure (Fin d → ℝ) := volume.restrict (cube d)
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simp [μ, hcube]
  have hmeas : AEMeasurable P.e μ :=
    aemeasurable_restrict_of_measurable_subtype hcubeMeas hP.1
  have hrange : ∀ᵐ x ∂μ, P.e x ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [self_mem_ae_restrict hcubeMeas] with x hx
    exact hP.2 x hx
  exact Integrable.of_mem_Icc 0 1 hmeas hrange

-- @node: normingVolume_power
/-- The witness-cube volume exponent is the effective dimension. -/
lemma normingVolume_power (d j : ℕ) (ε γ : ℝ)
    (hε : 0 < ε) (hγ : 1 < γ) :
    ((2 * dyadicWidth j * ε) ^ d) ^ (1 + 1 / tailExponent γ) =
      ((2 * ε) ^ d) ^ (1 + 1 / tailExponent γ) *
        (dyadicWidth j) ^ (effectiveDimension d γ) := by
  have hw : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
  have ha : 0 ≤ 2 * ε := by positivity
  have hdimension : (d : ℝ) * (1 + 1 / tailExponent γ) =
      effectiveDimension d γ := by
    dsimp [effectiveDimension, tailExponent]
    have hne : γ - 1 ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have hfactor : 2 * dyadicWidth j * ε = (2 * ε) * dyadicWidth j := by ring
  rw [hfactor, mul_pow, Real.mul_rpow (pow_nonneg ha _) (pow_nonneg (le_of_lt hw) _)]
  congr 1
  rw [← Real.rpow_natCast (dyadicWidth j) d,
    ← Real.rpow_mul (le_of_lt hw), hdimension]

/-- Treated mass of a selected norming subcell. -/
noncomputable def treatedSubcellMass {d : ℕ} (P : Law d)
    (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (ℓ : MultiIndex d m) : ℝ :=
  ∫ x in scaledSubcell d j m ε Q ℓ, P.e x ∂volume
  -- @realizes pQell(integral of propensity over scaled subcell)

/-- Minimum treated mass across a cell's norming subcells. -/
noncomputable def minimumTreatedMass {d : ℕ} (P : Law d)
    (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j)) : ℝ :=
  Finset.univ.inf' (by simp : (Finset.univ : Finset (MultiIndex d m)).Nonempty)
    (fun ℓ => treatedSubcellMass P j m ε Q ℓ)

-- @node: minimumTreatedMass_attained
/-- A norming subcell attains the minimum treated mass in each dyadic cell. -/
lemma minimumTreatedMass_attained {d : ℕ} (P : Law d)
    (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j)) :
    ∃ ℓ : MultiIndex d m,
      minimumTreatedMass P j m ε Q = treatedSubcellMass P j m ε Q ℓ := by
  unfold minimumTreatedMass
  obtain ⟨ℓ, _, hℓ⟩ := Finset.exists_mem_eq_inf'
    (by simp : (Finset.univ : Finset (MultiIndex d m)).Nonempty)
    (fun ℓ => treatedSubcellMass P j m ε Q ℓ)
  exact ⟨ℓ, hℓ⟩

-- @node: tailMassBudgetOn
/-- A lower-tail envelope forces a mass budget on every measurable set. -/
lemma tailMassBudgetOn {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    (C q : ℝ) (hC : 1 ≤ C) (hq : 0 < q)
    (hf : Integrable f μ) (hfn : 0 ≤ᵐ[μ] f)
    (htail : ∀ t ∈ Set.Ioc (0 : ℝ) 1, μ.real {x | f x ≤ t} ≤ C * t ^ q)
    (B : Set α) (hBmeas : MeasurableSet B) (hB : μ.real B ≤ 1) :
    (1 / 2) * (2 * C) ^ (-(1 / q)) * (μ.real B) ^ (1 + 1 / q) ≤
      ∫ x in B, f x ∂μ := by
  by_cases hv : μ.real B = 0
  · have hexp : 0 < 1 + 1 / q := by positivity
    rw [hv, Real.zero_rpow (ne_of_gt hexp)]
    simp only [mul_zero]
    exact setIntegral_nonneg_of_ae (s := B) hfn
  have hvpos : 0 < μ.real B := lt_of_le_of_ne measureReal_nonneg (Ne.symm hv)
  let t : ℝ := (μ.real B / (2 * C)) ^ (1 / q)
  have htpos : 0 < t := by
    dsimp [t]
    exact Real.rpow_pos_of_pos (div_pos hvpos (by positivity)) _
  have htone : t ≤ 1 := by
    have hbase : μ.real B / (2 * C) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    simpa [t] using (Real.rpow_le_rpow (by positivity : 0 ≤ μ.real B / (2 * C))
      hbase (le_of_lt (one_div_pos.mpr hq)))
  have htailt := htail t ⟨htpos, htone⟩
  have hcover : B ⊆ {x | f x ≤ t} ∪ (B ∩ {x | t ≤ f x}) := by
    intro x hx
    rcases le_total (f x) t with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  have hmass : μ.real B ≤ C * t ^ q + (μ.restrict B).real {x | t ≤ f x} := by
    calc
      μ.real B ≤ μ.real ({x | f x ≤ t} ∪ (B ∩ {x | t ≤ f x})) :=
        measureReal_mono hcover
      _ ≤ μ.real {x | f x ≤ t} + μ.real (B ∩ {x | t ≤ f x}) :=
        measureReal_union_le _ _
      _ ≤ C * t ^ q + (μ.restrict B).real {x | t ≤ f x} := by
        rw [measureReal_restrict_apply' hBmeas]
        rw [Set.inter_comm]
        simpa only [add_comm] using
          (add_le_add_right htailt (μ.real ({x | t ≤ f x} ∩ B)))
  have hmain : t * (μ.restrict B).real {x | t ≤ f x} ≤ ∫ x in B, f x ∂μ := by
    exact mul_meas_ge_le_integral_of_nonneg (ae_restrict_of_ae hfn) hf.integrableOn t
  have htq : C * t ^ q = μ.real B / 2 := by
    dsimp [t]
    rw [← Real.rpow_mul (by positivity : 0 ≤ μ.real B / (2 * C))]
    rw [div_mul_cancel₀ _ (ne_of_gt hq), Real.rpow_one]
    field_simp
  have hhalf : μ.real B / 2 ≤ (μ.restrict B).real {x | t ≤ f x} := by
    rw [htq] at hmass
    linarith
  calc
    (1 / 2) * (2 * C) ^ (-(1 / q)) * (μ.real B) ^ (1 + 1 / q) =
        t * (μ.real B / 2) := by
      dsimp [t]
      rw [Real.div_rpow (le_of_lt hvpos) (by positivity),
        Real.rpow_add hvpos]
      simp only [Real.rpow_one]
      rw [Real.rpow_neg (by positivity : 0 ≤ 2 * C)]
      ring
    _ ≤ t * (μ.restrict B).real {x | t ≤ f x} :=
      mul_le_mul_of_nonneg_left hhalf (le_of_lt htpos)
    _ ≤ ∫ x in B, f x ∂μ := hmain

-- @node: lem:mass-budget
/-- A constant determined by `C` and `q` bounds the propensity mass of every
measurable subset of the cube, uniformly over the laws in the model. -/
lemma mass_budget (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 < γ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (d : ℕ) (P : Law d), UniformDesign P →
        MeasurablePropensity P → GlobalTail P C γ →
        ∀ B : Set (Fin d → ℝ), MeasurableSet B → B ⊆ cube d →
          c₁ * (volume.real B) ^ (1 + 1 / tailExponent γ) ≤
            ∫ x in B, P.e x ∂volume := by
  refine ⟨(1 / 2) * (2 * C) ^ (-(1 / tailExponent γ)), by positivity, ?_⟩
  intro d P hdesign hmeas htail B hBmeas hBsub
  have hcubeMeas : MeasurableSet (cube d) := by simp [cube]
  have hcube : volume (cube d) = 1 := by simp [cube, Real.volume_Icc_pi]
  let μ : Measure (Fin d → ℝ) := volume.restrict (cube d)
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simp [μ, hcube]
  have hmeas' : AEMeasurable P.e μ :=
    aemeasurable_restrict_of_measurable_subtype hcubeMeas hmeas.1
  have hrange : ∀ᵐ x ∂μ, P.e x ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [self_mem_ae_restrict hcubeMeas] with x hx
    exact hmeas.2 x hx
  have hf : Integrable P.e μ := Integrable.of_mem_Icc 0 1 hmeas' hrange
  have hnonneg : 0 ≤ᵐ[μ] P.e := hrange.mono (fun x hx => hx.1)
  have htail' : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      μ.real {x | P.e x ≤ t} ≤ C * t ^ tailExponent γ := by
    intro t ht
    change P.xLaw = volume.restrict (cube d) at hdesign
    simpa [μ, ← hdesign] using htail t ht
  have hμB : μ.real B = volume.real B := by
    change (volume.restrict (cube d)).real B = volume.real B
    rw [measureReal_restrict_apply' hcubeMeas]
    simp [Set.inter_eq_self_of_subset_left hBsub]
  have hvolB : volume.real B ≤ 1 := by
    have hfiniteCube : volume (cube d) ≠ ⊤ := by simp [hcube]
    have hmono : volume.real B ≤ volume.real (cube d) := measureReal_mono hBsub hfiniteCube
    simpa [Measure.real, hcube] using hmono
  have hIntEq : (∫ x in B, P.e x ∂μ) = ∫ x in B, P.e x ∂volume := by
    have hRestrict : (volume.restrict (cube d)).restrict B = volume.restrict B := by
      rw [Measure.restrict_restrict hBmeas]
      rw [Set.inter_eq_self_of_subset_left hBsub]
    exact congrArg (fun ν : Measure (Fin d → ℝ) => ∫ x, P.e x ∂ν) hRestrict
  have h := tailMassBudgetOn μ P.e C (tailExponent γ) hC (by dsimp [tailExponent]; linarith)
    hf hnonneg htail' B hBmeas (by simpa [hμB] using hvolB)
  simpa [hμB, hIntEq] using h

-- @node: finiteWitnessMassBudget
/-- Apply a mass budget once to a finite disjoint family of equal-volume
witness sets, then bound its total treated mass by the individual masses. -/
lemma finiteWitnessMassBudget {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ)
    (c v t r : ℝ) (T : Set α) (s : Finset ι) (B : ι → Set α)
    (hdisj : Set.PairwiseDisjoint (↑s) B)
    (hmeas : ∀ i ∈ s, MeasurableSet (B i))
    (hfinite : ∀ i ∈ s, μ (B i) ≠ ⊤)
    (hint : ∀ i ∈ s, IntegrableOn f (B i) μ)
    (hvol : ∀ i ∈ s, μ.real (B i) = v)
    (hmass : ∀ i ∈ s, ∫ x in B i, f x ∂μ ≤ t)
    (hsub : ∀ i ∈ s, B i ⊆ T)
    (hbudget : ∀ U : Set α, MeasurableSet U → U ⊆ T →
      c * (μ.real U) ^ r ≤ ∫ x in U, f x ∂μ) :
    c * ((s.card : ℝ) * v) ^ r ≤ (s.card : ℝ) * t := by
  classical
  let U : Set α := ⋃ i ∈ s, B i
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact Finset.measurableSet_biUnion s hmeas
  have hUsub : U ⊆ T := by
    intro x hx
    simp only [U, Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact hsub i hi hxi
  have hUvol : μ.real U = (s.card : ℝ) * v := by
    dsimp [U]
    rw [measureReal_biUnion_finset hdisj hmeas hfinite]
    calc
      (∑ i ∈ s, μ.real (B i)) = ∑ _i ∈ s, v :=
        Finset.sum_congr rfl (fun i hi => hvol i hi)
      _ = (s.card : ℝ) * v := by simp
  have hUint : (∫ x in U, f x ∂μ) = ∑ i ∈ s, ∫ x in B i, f x ∂μ := by
    dsimp [U]
    exact integral_biUnion_finset s hmeas hdisj hint
  calc
    c * ((s.card : ℝ) * v) ^ r = c * (μ.real U) ^ r := by rw [hUvol]
    _ ≤ ∫ x in U, f x ∂μ := hbudget U hUmeas hUsub
    _ = ∑ i ∈ s, ∫ x in B i, f x ∂μ := hUint
    _ ≤ ∑ i ∈ s, t := Finset.sum_le_sum (fun i hi => hmass i hi)
    _ = (s.card : ℝ) * t := by simp

-- @node: witnessMassBudgetThreshold
/-- The mass budget for `k` disjoint equal-volume witnesses gives the
order-statistic threshold after cancelling the positive cardinality. -/
lemma witnessMassBudgetThreshold (c v q : ℝ) (k : ℕ)
    (hv : 0 < v) (hk : 0 < k)
    (t : ℝ)
    (hbudget : c * ((k : ℝ) * v) ^ (1 + 1 / q) ≤ (k : ℝ) * t) :
    c * v ^ (1 + 1 / q) * (k : ℝ) ^ (1 / q) ≤ t := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hpow : ((k : ℝ) * v) ^ (1 + 1 / q) =
      (k : ℝ) * (v ^ (1 + 1 / q) * (k : ℝ) ^ (1 / q)) := by
    rw [Real.mul_rpow (le_of_lt hkreal) (le_of_lt hv),
      Real.rpow_add hkreal]
    simp only [Real.rpow_one]
    ring
  rw [hpow] at hbudget
  nlinarith

-- @node: finiteWitnessOrderBound
/-- Equal-volume disjoint witnesses with a common mass budget obey the
sublevel-count form of the order-statistic bound. -/
lemma finiteWitnessOrderBound {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (c v q : ℝ) (T : Set α)
    (hc : 0 < c) (hv : 0 < v)
    (s : Finset ι) (B : ι → Set α) (p : ι → ℝ)
    (hdisj : Set.PairwiseDisjoint (↑s) B)
    (hmeas : ∀ i ∈ s, MeasurableSet (B i))
    (hfinite : ∀ i ∈ s, μ (B i) ≠ ⊤)
    (hint : ∀ i ∈ s, IntegrableOn f (B i) μ)
    (hvol : ∀ i ∈ s, μ.real (B i) = v)
    (hmass : ∀ i ∈ s, ∫ x in B i, f x ∂μ ≤ p i)
    (hsub : ∀ i ∈ s, B i ⊆ T)
    (hbudget : ∀ U : Set α, MeasurableSet U → U ⊆ T →
      c * (μ.real U) ^ (1 + 1 / q) ≤ ∫ x in U, f x ∂μ)
    (k : ℕ) (hk : 0 < k) :
    (s.filter fun i => p i < (c / 2) * v ^ (1 + 1 / q) *
      (k : ℝ) ^ (1 / q)).card < k := by
  classical
  by_contra hbad
  have hcard : k ≤ (s.filter fun i => p i <
      (c / 2) * v ^ (1 + 1 / q) * (k : ℝ) ^ (1 / q)).card := by omega
  obtain ⟨t, hts, htk⟩ := Finset.exists_subset_card_eq hcard
  have hts' : t ⊆ s := hts.trans (Finset.filter_subset _ _)
  have htbound : c * ((t.card : ℝ) * v) ^ (1 + 1 / q) ≤
      (t.card : ℝ) * ((c / 2) * v ^ (1 + 1 / q) *
        (k : ℝ) ^ (1 / q)) := by
    apply finiteWitnessMassBudget μ f c v
      ((c / 2) * v ^ (1 + 1 / q) * (k : ℝ) ^ (1 / q))
      (1 + 1 / q) T t B
    · intro i hi j hj hij
      exact hdisj (hts' hi) (hts' hj) hij
    · exact fun i hi => hmeas i (hts' hi)
    · exact fun i hi => hfinite i (hts' hi)
    · exact fun i hi => hint i (hts' hi)
    · exact fun i hi => hvol i (hts' hi)
    · intro i hi
      exact (hmass i (hts' hi)).trans
        (le_of_lt ((Finset.mem_filter.mp (hts hi)).2))
    · exact fun i hi => hsub i (hts' hi)
    · exact hbudget
  rw [htk] at htbound
  have hlarge := witnessMassBudgetThreshold c v q k hv hk _ htbound
  have hpositive : 0 < c * v ^ (1 + 1 / q) * (k : ℝ) ^ (1 / q) := by
    positivity
  nlinarith

-- @node: lem:ordered-subcell-mass
/-- The sublevel-count form of the ordered-mass lower bound. The mass-budget
premise is the conclusion of `mass_budget`, passed through from upstream. -/
lemma ordered_subcell_mass (d : ℕ) (β γ C : ℝ)
    (hd : 1 ≤ d) (hβ : 0 < β) (hγ : 1 < γ)
    (hmass : ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (d : ℕ) (P : Law d), UniformDesign P →
        MeasurablePropensity P → GlobalTail P C γ →
        ∀ B : Set (Fin d → ℝ), MeasurableSet B → B ⊆ cube d →
          c₁ * (volume.real B) ^ (1 + 1 / tailExponent γ) ≤
            ∫ x in B, P.e x ∂volume) :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ (P : Law d) (j : ℕ), UniformDesign P →
        MeasurablePropensity P → GlobalTail P C γ →
        ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card (Fin d → Fin (2 ^ j)) →
          (Finset.univ.filter (fun Q : Fin d → Fin (2 ^ j) =>
            minimumTreatedMass P j (polynomialOrder β)
              (normingSubcells d β).radius Q <
              c₂ * (dyadicWidth j) ^ (effectiveDimension d γ) *
                (k : ℝ) ^ (1 / tailExponent γ))).card < k := by
  classical
  obtain ⟨c₁, hc₁, hbudget⟩ := hmass
  let H := normingSubcells d β
  let c₂ := (c₁ / 2) * ((2 * H.radius) ^ d) ^
    (1 + 1 / tailExponent γ)
  have hq : 0 < tailExponent γ := by dsimp [tailExponent]; linarith
  have hc₂ : 0 < c₂ := by
    dsimp [c₂]
    have hr := H.radius_pos
    positivity
  refine ⟨c₂, hc₂, ?_⟩
  intro P j hdesign hmeas htail k hk _
  let w : (Fin d → Fin (2 ^ j)) → MultiIndex d (polynomialOrder β) :=
    fun Q => Classical.choose (minimumTreatedMass_attained P j
      (polynomialOrder β) H.radius Q)
  let B : (Fin d → Fin (2 ^ j)) → Set (Fin d → ℝ) :=
    fun Q => scaledSubcell d j (polynomialOrder β) H.radius Q (w Q)
  let p : (Fin d → Fin (2 ^ j)) → ℝ :=
    fun Q => minimumTreatedMass P j (polynomialOrder β) H.radius Q
  let v : ℝ := (2 * dyadicWidth j * H.radius) ^ d
  have hv : 0 < v := by
    dsimp [v]
    have hw : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
    have hr := H.radius_pos
    positivity
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ :
      Finset (Fin d → Fin (2 ^ j)))) B := by
    intro Q _ Q' _ hne
    apply Set.disjoint_left.mpr
    intro x hx hx'
    have hQ : cellIndex d j x = Q := hx.1
    have hQ' : cellIndex d j x = Q' := hx'.1
    exact hne (hQ.symm.trans hQ')
  have hmeasB : ∀ Q ∈ (Finset.univ : Finset (Fin d → Fin (2 ^ j))),
      MeasurableSet (B Q) := by
    intro Q _
    exact scaledSubcell_measurable d j (polynomialOrder β) H Q (w Q)
  have hsubB : ∀ Q ∈ (Finset.univ : Finset (Fin d → Fin (2 ^ j))),
      B Q ⊆ cube d := by
    intro Q _
    exact scaledSubcell_subset_cube d j (polynomialOrder β) H Q (w Q)
  have hfiniteB : ∀ Q ∈ (Finset.univ : Finset (Fin d → Fin (2 ^ j))),
      volume (B Q) ≠ ⊤ := by
    intro Q hQ
    have hcube : volume (cube d) = 1 := by simp [cube, Real.volume_Icc_pi]
    exact ne_top_of_le_ne_top (by simp [hcube])
      (measure_mono (hsubB Q hQ))
  have hintB : ∀ Q ∈ (Finset.univ : Finset (Fin d → Fin (2 ^ j))),
      IntegrableOn P.e (B Q) volume := by
    intro Q hQ
    exact (propensity_integrableOn_cube P hmeas).mono_set (hsubB Q hQ)
  have hvolB : ∀ Q ∈ (Finset.univ : Finset (Fin d → Fin (2 ^ j))),
      volume.real (B Q) = v := by
    intro Q _
    exact scaledSubcell_volume d j (polynomialOrder β) H Q (w Q)
  have hmassB : ∀ Q ∈ (Finset.univ : Finset (Fin d → Fin (2 ^ j))),
      ∫ x in B Q, P.e x ∂volume ≤ p Q := by
    intro Q _
    have hw := Classical.choose_spec (minimumTreatedMass_attained P j
      (polynomialOrder β) H.radius Q)
    change treatedSubcellMass P j (polynomialOrder β) H.radius Q (w Q) ≤ p Q
    simpa [p] using (le_of_eq hw.symm)
  have hbound := finiteWitnessOrderBound volume P.e c₁ v
    (tailExponent γ) (cube d) hc₁ hv Finset.univ B p
    hdisj hmeasB hfiniteB hintB hvolB hmassB hsubB
    (hbudget d P hdesign hmeas htail) k hk
  have hth : (c₁ / 2) * v ^ (1 + 1 / tailExponent γ) *
      (k : ℝ) ^ (1 / tailExponent γ) =
      c₂ * dyadicWidth j ^ (effectiveDimension d γ) *
        (k : ℝ) ^ (1 / tailExponent γ) := by
    dsimp [v, c₂]
    rw [normingVolume_power d j H.radius γ H.radius_pos hγ]
    ring
  simpa only [p, H, hth] using hbound

end CausalSmith.Stat.GlobalTailDesignRobustCate
