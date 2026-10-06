module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedLinearMeshBounds
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedLinearSlice
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedFubiniDensity

/-! # Full-cube density for the beta-one branch -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open scoped ENNReal BigOperators

@[fun_prop]
lemma measurable_linearMeshDensity_family
    {zeta : Type*} [MeasurableSpace zeta] (q : ℕ) (h eps : ℝ)
    (c : zeta → ℕ → ℝ) (hc : ∀ k, Measurable (fun z => c z k)) :
    Measurable (fun zy : zeta × ℝ => linearMeshDensity q h eps (c zy.1) zy.2) := by
  unfold linearMeshDensity linearCellDensity
  apply Finset.measurable_fun_sum
  intro k hk
  apply Measurable.mul measurable_const
  apply Finset.measurable_fun_sum
  intro i hi
  let S : Set (zeta × ℝ) := {zy |
    linearCellLower k h eps (c zy.1 k) i ≤ zy.2 ∧
      zy.2 ≤ linearCellUpper k h eps (c zy.1 k) i}
  have hL : Measurable (fun z => linearCellLower k h eps (c z k) i) := by
    unfold linearCellLower
    fin_cases i <;> simp [linearFoldedBranches] <;> fun_prop
  have hU : Measurable (fun z => linearCellUpper k h eps (c z k) i) := by
    unfold linearCellUpper
    fin_cases i <;> simp [linearFoldedBranches] <;> fun_prop
  have hS : MeasurableSet S :=
    (measurableSet_le (hL.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hU.comp measurable_fst))
  rw [show (fun zy : zeta × ℝ =>
      (Set.Icc (linearCellLower k h eps (c zy.1 k) i)
        (linearCellUpper k h eps (c zy.1 k) i)).indicator
          (fun _ => linearCellWeight h eps (c zy.1 k) i) zy.2) =
      S.indicator (fun zy => linearCellWeight h eps (c zy.1 k) i) by
    funext zy
    have hm : zy.2 ∈ Set.Icc (linearCellLower k h eps (c zy.1 k) i)
        (linearCellUpper k h eps (c zy.1 k) i) ↔ zy ∈ S := by simp [S]
    by_cases hz : zy ∈ S
    · rw [Set.indicator_of_mem (hm.2 hz), Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem (fun h => hz (hm.mp h)),
        Set.indicator_of_notMem hz]]
  apply Measurable.indicator _ hS
  unfold linearCellWeight
  fin_cases i <;> simp [linearFoldedBranches] <;> fun_prop

noncomputable def linearCubeScoreDensity (n q K : ℕ) (h eps : ℝ)
    (idx : Fin K → Fin (n + 1) → ℕ) (theta : Fin K → Bool) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, linearMeshDensity q h eps (foldedTailCoefficient n K h idx theta z) t
    ∂cubeMeasure n

@[fun_prop]
lemma measurable_linearCubeScoreDensity (n q K : ℕ) (h eps : ℝ)
    (idx : Fin K → Fin (n + 1) → ℕ) (theta : Fin K → Bool) :
    Measurable (linearCubeScoreDensity n q K h eps idx theta) := by
  unfold linearCubeScoreDensity
  letI : IsProbabilityMeasure (cubeMeasure n) := cubeMeasure_isProbabilityMeasure n
  exact (measurable_linearMeshDensity_family q h eps
    (fun z k => foldedTailCoefficient n K h idx theta z k)
    (fun k => measurable_foldedTailCoefficient n K h idx theta k)).lintegral_prod_left'

lemma map_betaOne_foldedRawScore_eq_withDensity
    (n q K : ℕ) (hq : 0 < q) {h eps : ℝ} (hhq : h = (q : ℝ)⁻¹)
    (idx : Fin K → Fin (n + 1) → ℕ) (hinj : Function.Injective idx)
    (theta : Fin K → Bool) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128) :
    Measure.map
        (foldedRawScore (Nat.zero_lt_succ n) 1 h 1 eps K
          (fun j => meshBump (Nat.zero_lt_succ n) h (idx j)) theta)
        (cubeMeasure (n + 1)) =
      (volume : Measure ℝ).withDensity
        (linearCubeScoreDensity n q K h eps idx theta) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let g := foldedRawScore (Nat.zero_lt_succ n) 1 h 1 eps K
    (fun j => meshBump (Nat.zero_lt_succ n) h (idx j)) theta
  let F : ℝ × (Fin n → ℝ) → ℝ := fun xz => g (e.symm xz)
  have hg : Measurable g := measurable_foldedRawScore_of_measurable_bumps
    (Nat.zero_lt_succ n) 1 h 1 eps K _ (fun j => measurable_meshBump _ _ _) theta
  have hF : Measurable F := hg.comp e.symm.measurable
  have htransport : Measure.map g (cubeMeasure (n + 1)) =
      Measure.map F (((volume : Measure ℝ).restrict (Set.Icc 0 1)).prod
        (cubeMeasure n)) := by
    calc
      Measure.map g (cubeMeasure (n + 1)) =
          Measure.map F (Measure.map e (cubeMeasure (n + 1))) := by
        rw [Measure.map_map hF e.measurable]
        congr 1
        funext x
        exact congrArg g (e.symm_apply_apply x).symm
      _ = _ := by rw [cubeMeasure_map_piFinSuccAbove_prod]
  rw [htransport]
  letI : IsProbabilityMeasure (cubeMeasure n) := cubeMeasure_isProbabilityMeasure n
  apply map_prod_eq_withDensity_lintegral_slices hF
    (measurable_linearMeshDensity_family q h eps
      (fun z k => foldedTailCoefficient n K h idx theta z k)
      (fun k => measurable_foldedTailCoefficient n K h idx theta k))
  intro z
  exact map_linearFoldedSlice_eq_withDensity n q K hq hhq idx hinj theta z
    heps0 heps

lemma linearMeshDensity_ne_top (q : ℕ) (h eps : ℝ) (c : ℕ → ℝ) (y : ℝ) :
    linearMeshDensity q h eps c y ≠ ∞ := by
  unfold linearMeshDensity linearCellDensity
  apply ENNReal.sum_ne_top.mpr
  intro k hk
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  apply ENNReal.sum_ne_top.mpr
  intro i hi
  by_cases hy : y ∈ Set.Icc (linearCellLower k h eps (c k) i)
      (linearCellUpper k h eps (c k) i) <;> simp [hy, linearCellWeight]

/-- Averaging the slice densities preserves the beta-one Jacobian envelope. -/
lemma linearCubeScoreDensity_error_ae
    (n q K : ℕ) (hq : 0 < q) {h eps : ℝ} (hhq : h = (q : ℝ)⁻¹)
    (idx : Fin K → Fin (n + 1) → ℕ) (hinj : Function.Injective idx)
    (theta : Fin K → Bool) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128) :
    ∀ᵐ t ∂(volume : Measure ℝ).restrict scoreInterval,
      |(linearCubeScoreDensity n q K h eps idx theta t).toReal - 2| ≤
        256 * eps := by
  let c : (Fin n → ℝ) → ℕ → ℝ :=
    fun z k => foldedTailCoefficient n K h idx theta z k
  let E : ℝ := 256 * eps
  let lo : ℝ := 2 - E
  let hi : ℝ := 2 + E
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hEle : E ≤ 2 := by dsimp [E]; nlinarith
  have hlo0 : 0 ≤ lo := by dsimp [lo]; linarith
  have hhi0 : 0 ≤ hi := by dsimp [hi]; positivity
  have hc (z : Fin n → ℝ) (k : ℕ) : c z k ∈ Set.Icc (-1 : ℝ) 1 :=
    foldedTailCoefficient_mem_Icc n K h hinj theta z k
  have hslices (z : Fin n → ℝ) :
      ∀ᵐ t ∂(volume : Measure ℝ).restrict scoreInterval,
        |(linearMeshDensity q h eps (c z) t).toReal - 2| ≤ E := by
    simpa [E] using linearMeshDensity_error_ae q hq hhq (c z) (hc z) heps0 heps
  have hjoint : Measurable (fun zt : (Fin n → ℝ) × ℝ =>
      |(linearMeshDensity q h eps (c zt.1) zt.2).toReal - 2|) := by
    exact ((measurable_linearMeshDensity_family q h eps c
      (fun k => measurable_foldedTailCoefficient n K h idx theta k)).ennreal_toReal.sub
        measurable_const).abs
  have hset : MeasurableSet {zt : (Fin n → ℝ) × ℝ |
      |(linearMeshDensity q h eps (c zt.1) zt.2).toReal - 2| ≤ E} :=
    measurableSet_le hjoint measurable_const
  letI : IsProbabilityMeasure (cubeMeasure n) := cubeMeasure_isProbabilityMeasure n
  have hswap : ∀ᵐ t ∂(volume : Measure ℝ).restrict scoreInterval,
      ∀ᵐ z ∂cubeMeasure n,
        |(linearMeshDensity q h eps (c z) t).toReal - 2| ≤ E := by
    apply (Measure.ae_ae_comm hset).1
    exact Filter.Eventually.of_forall hslices
  filter_upwards [hswap] with t ht
  have hsliceLo : ∀ᵐ z ∂cubeMeasure n,
      ENNReal.ofReal lo ≤ linearMeshDensity q h eps (c z) t := by
    filter_upwards [ht] with z hz
    apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
      (linearMeshDensity_ne_top q h eps (c z) t)).1
    rw [ENNReal.toReal_ofReal hlo0]
    have := (abs_le.mp hz).1
    dsimp [lo]
    linarith
  have hsliceHi : ∀ᵐ z ∂cubeMeasure n,
      linearMeshDensity q h eps (c z) t ≤ ENNReal.ofReal hi := by
    filter_upwards [ht] with z hz
    apply (ENNReal.toReal_le_toReal
      (linearMeshDensity_ne_top q h eps (c z) t) ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal hhi0]
    have := (abs_le.mp hz).2
    dsimp [hi]
    linarith
  have havgLo : ENNReal.ofReal lo ≤ linearCubeScoreDensity n q K h eps idx theta t := by
    unfold linearCubeScoreDensity
    calc
      ENNReal.ofReal lo = ∫⁻ _z : (Fin n → ℝ), ENNReal.ofReal lo ∂cubeMeasure n := by simp
      _ ≤ _ := lintegral_mono_ae hsliceLo
  have havgHi : linearCubeScoreDensity n q K h eps idx theta t ≤ ENNReal.ofReal hi := by
    unfold linearCubeScoreDensity
    calc
      _ ≤ ∫⁻ _z : (Fin n → ℝ), ENNReal.ofReal hi ∂cubeMeasure n :=
        lintegral_mono_ae hsliceHi
      _ = ENNReal.ofReal hi := by simp
  have htop : linearCubeScoreDensity n q K h eps idx theta t ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top havgHi
  rw [abs_le]
  constructor
  · have hr := (ENNReal.ofReal_le_iff_le_toReal htop).mp havgLo
    dsimp [lo, E] at hr ⊢
    linarith
  · have hr := (ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top).2 havgHi
    rw [ENNReal.toReal_ofReal hhi0] at hr
    dsimp [hi, E] at hr ⊢
    linarith

end CausalSmith.Experimentation.PilotscorePairingFrontier
