module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ChainRegularity

/-! Joint measurability of the trained histogram construction and its observable energy.
The normalization and coefficient integrals retain measurability in the training data. -/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

-- @node: observableHjMeasurableSpace
local instance observableHjMeasurableSpace (J : ℕ) : MeasurableSpace (Hj J) := borel _

-- @node: observableHjBorelSpace
local instance observableHjBorelSpace (J : ℕ) : BorelSpace (Hj J) := ⟨rfl⟩

-- @node: observableUnitVolumeFinite
local instance observableUnitVolumeFinite : IsFiniteMeasure unitVolume := by
  unfold unitVolume
  infer_instance

/-- Counts are jointly measurable in training data and the queried covariate. -/
-- @node: measurable_cellCount_joint
@[fun_prop] lemma measurable_cellCount_joint (m mx : ℕ) :
    Measurable (fun p : Data m × ℝ => cellCount p.1 mx p.2) := by
  unfold cellCount
  simp only [Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite (measurableSet_eq_fun ?_ ?_) measurable_const measurable_const
  · unfold X
    fun_prop
  · fun_prop

/-- Arm counts are jointly measurable in training data and the query. -/
-- @node: measurable_armCellCount_joint
@[fun_prop] lemma measurable_armCellCount_joint (m mx : ℕ) (a : Bool) :
    Measurable (fun p : Data m × ℝ => armCellCount p.1 mx a p.2) := by
  unfold armCellCount
  simp only [Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite ((measurableSet_eq_fun ?_ ?_).inter
    (measurableSet_eq_fun ?_ measurable_const)) measurable_const measurable_const
  · unfold X
    fun_prop
  · fun_prop
  · unfold A
    fun_prop

/-- Outcome counts are jointly measurable in training data and both queries. -/
-- @node: measurable_outcomeCellCount_joint
@[fun_prop] lemma measurable_outcomeCellCount_joint (m mx my : ℕ) (a : Bool) :
    Measurable (fun p : (Data m × ℝ) × ℝ => outcomeCellCount p.1.1 mx my a p.1.2 p.2) := by
  unfold outcomeCellCount
  simp only [Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite ((measurableSet_eq_fun ?_ ?_).inter
    ((measurableSet_eq_fun ?_ measurable_const).inter (measurableSet_eq_fun ?_ ?_)))
    measurable_const measurable_const
  · unfold X
    fun_prop
  · fun_prop
  · unfold A
    fun_prop
  · unfold Y
    fun_prop
  · fun_prop

/-- The clipped propensity pilot is jointly measurable in training data and covariate. -/
-- @node: measurable_propensityPilot_joint
@[fun_prop] lemma measurable_propensityPilot_joint (m mx : ℕ) :
    Measurable (fun p : Data m × ℝ => propensityPilot p.1 mx p.2) := by
  unfold propensityPilot clip
  have hc := measurable_cellCount_joint m mx
  have ha := measurable_armCellCount_joint m mx true
  have hr : Measurable (fun p : Data m × ℝ => if cellCount p.1 mx p.2 = 0
      then (1 / 2 : ℝ) else (armCellCount p.1 mx true p.2 : ℝ) / cellCount p.1 mx p.2) :=
    Measurable.ite (hc (measurableSet_singleton 0)) measurable_const (by fun_prop)
  fun_prop

/-- Both fitted arm probabilities are jointly measurable. -/
-- @node: measurable_pilotPi_joint
@[fun_prop] lemma measurable_pilotPi_joint (m mx : ℕ) (a : Bool) :
    Measurable (fun p : Data m × ℝ => pilotPi p.1 mx a p.2) := by
  unfold pilotPi armProbability
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

/-- The raw clipped density is measurable in all its observed inputs. -/
-- @node: measurable_clippedDensityPilot_joint
@[fun_prop] lemma measurable_clippedDensityPilot_joint (m mx my : ℕ) (a : Bool) :
    Measurable (fun p : (Data m × ℝ) × ℝ => clippedDensityPilot p.1.1 mx my a p.1.2 p.2) := by
  unfold clippedDensityPilot clip
  have hc : Measurable (fun p : (Data m × ℝ) × ℝ => armCellCount p.1.1 mx a p.1.2) :=
    (measurable_armCellCount_joint m mx a).comp measurable_fst
  have hr : Measurable (fun p : (Data m × ℝ) × ℝ =>
      if armCellCount p.1.1 mx a p.1.2 = 0 then (1 : ℝ) else
        (my : ℝ) * outcomeCellCount p.1.1 mx my a p.1.2 p.2 /
          armCellCount p.1.1 mx a p.1.2) :=
    Measurable.ite (hc (measurableSet_singleton 0)) measurable_const (by fun_prop)
  fun_prop

/-- Integrating the raw histogram gives a measurable normalization in the training data. -/
-- @node: measurable_densityPilot_training_joint
@[fun_prop] lemma measurable_densityPilot_training_joint (m mx my : ℕ) (a : Bool) :
    Measurable (fun p : (Data m × ℝ) × ℝ => densityPilot p.1.1 mx my a p.1.2 p.2) := by
  have hn : Measurable (fun p : Data m × ℝ =>
      ∫ y, clippedDensityPilot p.1 mx my a p.2 y ∂unitVolume) := by
    have hc := measurable_clippedDensityPilot_joint m mx my a
    exact hc.stronglyMeasurable.integral_prod_right'.measurable
  unfold densityPilot
  exact (measurable_clippedDensityPilot_joint m mx my a).div (hn.comp measurable_fst)

/-- The normalized pilot coefficient vector is jointly measurable. -/
-- @node: measurable_pilotCoefficients_joint
@[fun_prop] lemma measurable_pilotCoefficients_joint (m mx my J : ℕ) (a : Bool) :
    Measurable (fun p : Data m × ℝ => pilotCoefficients p.1 mx my J a p.2) := by
  unfold pilotCoefficients coefficients
  apply (PiLp.continuous_toLp 2 (fun _ : Fin J => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  apply Measurable.const_mul
  exact ((measurable_densityPilot_training_joint m mx my a).stronglyMeasurable.integral_prod_right'
    (ν := unitVolume.restrict (histogramCell J (i.val + 1)))).measurable

/-- The propensity residual is measurable jointly with its fitted training sample. -/
-- @node: measurable_Rres_joint
@[fun_prop] lemma measurable_Rres_joint (m mx : ℕ) (a : Bool) :
    Measurable (fun p : Data m × Omega => Rres p.1 mx a p.2) := by
  unfold Rres X A
  have hi : Measurable (fun p : Data m × Omega => if p.2.2.1 = a then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      measurable_const measurable_const
  fun_prop

/-- The vector outcome residual is measurable jointly with training. -/
-- @node: measurable_Vres_joint
@[fun_prop] lemma measurable_Vres_joint (m mx my J : ℕ) (a : Bool) :
    Measurable (fun p : Data m × Omega => Vres p.1 mx my J a p.2) := by
  unfold Vres X A Y
  have hi : Measurable (fun p : Data m × Omega => if p.2.2.1 = a then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      measurable_const measurable_const
  fun_prop

/-- The first-order average remains measurable when training varies. -/
-- @node: measurable_Uone_joint
@[fun_prop] lemma measurable_Uone_joint (m mx my J : ℕ) (b : Fin 2) (a : Bool) :
    Measurable (fun p : Data m × EvalData m => Uone p.1 mx my J p.2 b a) := by
  unfold Uone
  fun_prop

/-- The multiband correction remains measurable when training varies. -/
-- @node: measurable_Utwo_joint
@[fun_prop] lemma measurable_Utwo_joint (m mx my L T J : ℕ) (kt : ℕ → ℕ)
    (b : Fin 2) (a : Bool) :
    Measurable (fun p : Data m × EvalData m => Utwo p.1 mx my L T J kt p.2 b a) := by
  unfold Utwo X
  fun_prop

/-- The third-order correction remains measurable when training varies. -/
-- @node: measurable_Uthree_joint
@[fun_prop] lemma measurable_Uthree_joint (m mx my J q : ℕ) (b : Fin 2) (a : Bool) :
    Measurable (fun p : Data m × EvalData m => Uthree p.1 mx my J q p.2 b a) := by
  unfold Uthree X
  fun_prop

/-- The full coefficient chain is jointly measurable in training and evaluation blocks. -/
-- @node: measurable_coefficientChain_joint
@[fun_prop] lemma measurable_coefficientChain_joint (m mx my L T J q : ℕ) (kt : ℕ → ℕ)
    (b : Fin 2) :
    Measurable (fun p : Data m × EvalData m => coefficientChain p.1 mx my L T J q kt p.2 b) := by
  have hp (a : Bool) : Measurable (fun train : Data m =>
      ∫ x, pilotCoefficients train mx my J a x ∂unitVolume) :=
    (measurable_pilotCoefficients_joint m mx my J a).stronglyMeasurable.integral_prod_right'.measurable
  unfold coefficientChain
  apply Finset.measurable_sum
  intro a _
  have hh : Measurable (fun p : Data m × EvalData m =>
      (∫ x, pilotCoefficients p.1 mx my J a x ∂unitVolume) + Uone p.1 mx my J p.2 b a -
        Utwo p.1 mx my L T J kt p.2 b a + Uthree p.1 mx my J q p.2 b a) :=
    ((((hp a).comp measurable_fst).add (measurable_Uone_joint m mx my J b a)).sub
      (measurable_Utwo_joint m mx my L T J kt b a)).add
        (measurable_Uthree_joint m mx my J q b a)
  exact hh.const_smul (if a then (1 : ℝ) else -1)

/-- Both fitted chains give a jointly measurable energy statistic. -/
-- @node: measurable_energy_joint
@[fun_prop] lemma measurable_energy_joint (m mx my L T J q : ℕ) (kt : ℕ → ℕ) :
    Measurable (fun p : Data m × EvalData m => energy p.1 mx my L T J q kt p.2) := by
  unfold energy
  fun_prop

/-- Arbitrary fixed coordinate selections yield an observable measurable energy. -/
-- @node: measurable_selectedEnergy
@[fun_prop] lemma measurable_selectedEnergy (n m mx my L T J q : ℕ) (kt : ℕ → ℕ)
    (indices : Fin 13 → Fin m → Fin n) :
    Measurable (fun data : Data n => energy (fun i => data (indices 0 i)) mx my L T J q kt
      (fun b i => data (indices (Fin.ofNat 13 (b.val + 1)) i))) := by
  have hm : Measurable (fun data : Data n =>
      ((fun i => data (indices 0 i)),
        (fun (b : Fin 12) i => data (indices (Fin.ofNat 13 (b.val + 1)) i)))) := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro i
      exact measurable_pi_apply (indices 0 i)
    · apply measurable_pi_lambda
      intro b
      apply measurable_pi_lambda
      intro i
      exact measurable_pi_apply (indices (Fin.ofNat 13 (b.val + 1)) i)
  simpa only [Function.comp_def] using (measurable_energy_joint m mx my L T J q kt).comp hm

/-- Extracting the thirteen disjoint roles preserves measurability for any fixed ranks. -/
-- @node: measurable_foldEnergy
@[fun_prop] lemma measurable_foldEnergy (n mx my L T J q : ℕ) (kt : ℕ → ℕ) :
    Measurable (fun data : Data n => energy (foldData n data 0) mx my L T J q kt
      (fun b => foldData n data (Fin.ofNat 13 (b.val + 1)))) := by
  exact measurable_selectedEnergy n (roleSize n) mx my L T J q kt (foldIndex n)

/-- The frozen statistic is measurable in the original observed data. -/
-- @node: measurable_tunedEnergy
@[fun_prop] lemma measurable_tunedEnergy (n : ℕ) : Measurable (tunedEnergy n) := by
  exact measurable_foldEnergy n (tunedMx (roleSize n)) (tunedMy (roleSize n))
    (tunedL (roleSize n)) (tunedT (roleSize n)) (tunedJ (roleSize n))
    (tunedQ (roleSize n)) (tunedKt (roleSize n))

end CausalSmith.Stat.DensityEffectRoughNull
