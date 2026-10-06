module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ResidualMoments

/-!
Measurability of fixed-training histogram residuals and the observable coefficient chains.
The covariate dependence of integrated pilot coefficients factors through a countable cell label.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

-- @node: chainRegularityHjMeasurableSpace
local instance chainRegularityHjMeasurableSpace (J : ℕ) : MeasurableSpace (Hj J) := borel _

-- @node: chainRegularityHjBorelSpace
local instance chainRegularityHjBorelSpace (J : ℕ) : BorelSpace (Hj J) := ⟨rfl⟩

/-- Fixed-training covariate counts are measurable cell functions. -/
-- @node: measurable_cellCount_covariate
@[fun_prop] lemma measurable_cellCount_covariate {m : ℕ} (train : Fin m → Omega)
    (mx : ℕ) : Measurable (cellCount train mx) := by
  let g : ℕ → ℕ := fun c =>
    (Finset.univ.filter (fun i => cell mx (X (train i)) = c)).card
  exact (measurable_of_countable g).comp (measurable_histogram_cell mx)

/-- Fixed-training arm counts are measurable cell functions. -/
-- @node: measurable_armCellCount_covariate
@[fun_prop] lemma measurable_armCellCount_covariate {m : ℕ} (train : Fin m → Omega)
    (mx : ℕ) (a : Bool) : Measurable (armCellCount train mx a) := by
  let g : ℕ → ℕ := fun c =>
    (Finset.univ.filter (fun i => cell mx (X (train i)) = c ∧ A (train i) = a)).card
  exact (measurable_of_countable g).comp (measurable_histogram_cell mx)

/-- Fixed-training clipped arm probabilities are measurable in the covariate. -/
@[fun_prop] lemma measurable_pilotPi_covariate {m : ℕ} (train : Fin m → Omega)
    (mx : ℕ) (a : Bool) : Measurable (pilotPi train mx a) := by
  unfold pilotPi armProbability propensityPilot clip
  have hc := measurable_cellCount_covariate train mx
  have ha := measurable_armCellCount_covariate train mx true
  have hs : MeasurableSet {x | cellCount train mx x = 0} :=
    hc (measurableSet_singleton 0)
  have hr : Measurable (fun x => if cellCount train mx x = 0 then (1 / 2 : ℝ)
      else (armCellCount train mx true x : ℝ) / cellCount train mx x) :=
    Measurable.ite hs measurable_const (by fun_prop)
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

/-- Integrating a fixed-training pilot leaves only its countable covariate cell dependence. -/
-- @node: measurable_pilotCoefficients_covariate
@[fun_prop] lemma measurable_pilotCoefficients_covariate {m : ℕ}
    (train : Fin m → Omega) (mx my J : ℕ) (a : Bool) :
    Measurable (pilotCoefficients train mx my J a) := by
  let raw : ℕ → ℝ → ℝ := fun c y => clip (1 / 8) 8
    (if (Finset.univ.filter (fun i => cell mx (X (train i)) = c ∧
      A (train i) = a)).card = 0 then 1 else
      (my : ℝ) * (Finset.univ.filter (fun i => cell mx (X (train i)) = c ∧
        A (train i) = a ∧ cell my (Y (train i)) = cell my y)).card /
        (Finset.univ.filter (fun i => cell mx (X (train i)) = c ∧ A (train i) = a)).card)
  let g : ℕ → Hj J := fun c => coefficients J
    (fun y => raw c y / (∫ yp, raw c yp ∂unitVolume))
  exact (measurable_of_countable g).comp (measurable_histogram_cell mx)

/-- The outcome representer is measurable as a finite coefficient vector. -/
-- @node: measurable_phiCoefficients
@[fun_prop] lemma measurable_phiCoefficients (J : ℕ) : Measurable (phiCoefficients J) := by
  let g : ℕ → Hj J := fun c => WithLp.toLp 2
    (fun i => if c = i.val + 1 then Real.sqrt J else 0)
  exact (measurable_of_countable g).comp (measurable_histogram_cell J)

/-- Coarse coefficient averaging is a measurable finite-dimensional linear map. -/
-- @node: measurable_coefficientProjection
@[fun_prop] lemma measurable_coefficientProjection (j J : ℕ) :
    Measurable (coefficientProjection j J) := by
  unfold coefficientProjection
  apply (PiLp.continuous_toLp 2 (fun _ : Fin J => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro l _
  split_ifs <;> fun_prop

/-- Every band map is measurable. -/
-- @node: measurable_Qband
@[fun_prop] lemma measurable_Qband (L J t : ℕ) : Measurable (Qband L J t) := by
  unfold Qband
  split_ifs <;> fun_prop

/-- The cell matching kernel is jointly measurable. -/
-- @node: measurable_covariateKernel
@[fun_prop] lemma measurable_covariateKernel (k : ℕ) :
    Measurable (fun z : ℝ × ℝ => covariateKernel k z.1 z.2) := by
  unfold covariateKernel
  exact Measurable.ite (measurableSet_eq_fun (by fun_prop) (by fun_prop))
    measurable_const measurable_const

/-- The observable propensity residual is measurable for every fixed training sample. -/
-- @node: measurable_Rres
@[fun_prop] lemma measurable_Rres {m : ℕ} (train : Fin m → Omega) (mx : ℕ)
    (a : Bool) : Measurable (Rres train mx a) := by
  unfold Rres X A
  have hi : Measurable (fun o : Omega => if o.2.1 = a then (1 : ℝ) else 0) :=
    Measurable.ite ((measurable_fst.comp measurable_snd) (measurableSet_singleton a))
      measurable_const measurable_const
  fun_prop

/-- The observable outcome coefficient residual is measurable. -/
-- @node: measurable_Vres
@[fun_prop] lemma measurable_Vres {m : ℕ} (train : Fin m → Omega) (mx my J : ℕ)
    (a : Bool) : Measurable (Vres train mx my J a) := by
  unfold Vres X A Y
  have hi : Measurable (fun o : Omega => if o.2.1 = a then (1 : ℝ) else 0) :=
    Measurable.ite ((measurable_fst.comp measurable_snd) (measurableSet_singleton a))
      measurable_const measurable_const
  fun_prop

/-- Each first-order chain average is measurable. -/
-- @node: measurable_Uone
@[fun_prop] lemma measurable_Uone {m : ℕ} (train : Fin m → Omega) (mx my J : ℕ)
    (b : Fin 2) (a : Bool) : Measurable (fun eval => Uone train mx my J eval b a) := by
  unfold Uone
  fun_prop

/-- Each multiband second-order chain average is measurable. -/
-- @node: measurable_Utwo
@[fun_prop] lemma measurable_Utwo {m : ℕ} (train : Fin m → Omega)
    (mx my L T J : ℕ) (kt : ℕ → ℕ) (b : Fin 2) (a : Bool) :
    Measurable (fun eval => Utwo train mx my L T J kt eval b a) := by
  unfold Utwo X
  fun_prop

/-- Each third-order chain average is measurable. -/
-- @node: measurable_Uthree
@[fun_prop] lemma measurable_Uthree {m : ℕ} (train : Fin m → Omega)
    (mx my J q : ℕ) (b : Fin 2) (a : Bool) :
    Measurable (fun eval => Uthree train mx my J q eval b a) := by
  unfold Uthree X
  fun_prop

/-- The complete arm-difference coefficient chain is measurable. -/
-- @node: measurable_coefficientChain
@[fun_prop] lemma measurable_coefficientChain {m : ℕ} (train : Fin m → Omega)
    (mx my L T J q : ℕ) (kt : ℕ → ℕ) (b : Fin 2) :
    Measurable (fun eval => coefficientChain train mx my L T J q kt eval b) := by
  unfold coefficientChain
  fun_prop

/-- The inner product of the two observable chains is measurable. -/
-- @node: measurable_energy
@[fun_prop] lemma measurable_energy {m : ℕ} (train : Fin m → Omega)
    (mx my L T J q : ℕ) (kt : ℕ → ℕ) :
    Measurable (energy train mx my L T J q kt) := by
  unfold energy
  fun_prop

end CausalSmith.Stat.DensityEffectRoughNull
