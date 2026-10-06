module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.CalibratedDensityDerivatives
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.CalibratedEffects
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.CalibratedModelProperties
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairPrognosisEnvelope
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairSpatialOscillation
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedAlternativePrognosisLinear
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedDensityRanges
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedNullPrognosisLinear
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedPrognosisOscillation
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedPropensityLinear
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedPropensityOscillation
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedSingletonMatching
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.SpatialGluing
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.SpatialLipschitz

/-! # T CalibratedSupport

Paper-owned scaffold obligations; proofs are filled in Stage 3. -/
@[expose] public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The one-record reference is uniform covariate and uniform four-label measure. -/
def recordReference : Measure Record := jointLaw uniformLaw (fun _ _ _ => 1/4)
/-- Actual mixed-law density, with roots and construction fully substituted. -/
def mixedDensity (b : Bool) (k : ℕ) (σ : Fin (k + 1) → Bool) (a y : Bool) (x : Covariate) (v : Fin 2 → ℝ) : ℝ :=
  4*(mixedLaw b k σ (v 0) (v 1)).cells a y x
/-- Actual fair-law density, including the comparator. -/
def fairDensity (random : Bool) (k : ℕ) (σ : Fin (k + 1) → Bool) (t : ℝ) (a y : Bool) (x : Covariate) (δ : ℝ) : ℝ :=
  4*(if random then fairLaw k σ t δ else fairComparator k t δ).cells a y x
/-- Substantive membership, effect, and singleton-matching claims at the rate-scaled amplitudes. -/
def CalibratedMembership (ε : ℝ) : Prop :=
  ∀ α β : ℝ, ExponentDomain α β → ∀ k : ℕ, 1 ≤ k → -- @realizes h(1 ≤ k ensures 0 < h = 1/(k : ℝ) ≤ 1)
    let η := ε*(k : ℝ)^(-α)
    let ζ := ε*(k : ℝ)^(-β)
    let δ := ε*(k : ℝ)^(-β)
    (∀ σ : Fin (k + 1) → Bool,
      Model α β (mixedLaw false k σ η ζ) ∧ Model α β (mixedLaw true k σ η ζ) ∧
      effect (mixedLaw false k σ η ζ) = 0 ∧ effect (mixedLaw true k σ η ζ) = 32*η*ζ) ∧
    (∀ a y x,
      (∑ σ : Fin (k + 1) → Bool, (mixedLaw false k σ η ζ).cells a y x) =
      (∑ σ : Fin (k + 1) → Bool, (mixedLaw true k σ η ζ).cells a y x)) ∧
    (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) →
      (∀ σ : Fin (k + 1) → Bool,
        Model α β (fairLaw k σ t δ) ∧ effect (fairLaw k σ t δ) = t) ∧
      Model α β (fairComparator k t δ) ∧ effect (fairComparator k t δ) = comparatorEffect t δ ∧
      ∀ a y x,
        ((Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹ *
          ∑ σ : Fin (k + 1) → Bool, (fairLaw k σ t δ).cells a y x) =
          (fairComparator k t δ).cells a y x)
/-- The model and homogeneous-effect obligations, separated from singleton
matching, which follows from the exact calibration equations. -/
-- @node: CalibratedModels
def CalibratedModels (ε : ℝ) : Prop :=
  ∀ α β : ℝ, ExponentDomain α β → ∀ k : ℕ, 1 ≤ k →
    let η := ε*(k : ℝ)^(-α)
    let ζ := ε*(k : ℝ)^(-β)
    let δ := ε*(k : ℝ)^(-β)
    (∀ σ : Fin (k + 1) → Bool,
      Model α β (mixedLaw false k σ η ζ) ∧ Model α β (mixedLaw true k σ η ζ) ∧
      effect (mixedLaw false k σ η ζ) = 0 ∧ effect (mixedLaw true k σ η ζ) = 32*η*ζ) ∧
    (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) →
      (∀ σ : Fin (k + 1) → Bool,
        Model α β (fairLaw k σ t δ) ∧ effect (fairLaw k σ t δ) = t) ∧
      Model α β (fairComparator k t δ) ∧ effect (fairComparator k t δ) = comparatorEffect t δ)
/-- On one fixed signed neighbourhood the actual cell laws are valid, and their relative
 densities and first two amplitude derivatives have one universal envelope. -/
def DensityNeighbourhood (ε M : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ σ : Fin (k + 1) → Bool,
    (∀ η ζ : ℝ, |η| ≤ ε → |ζ| ≤ ε → ∀ b,
      ValidCells (mixedCells b k σ η ζ) ∧
      (∀ a y x,
        (1/2 : ℝ) ≤ mixedDensity b k σ a y x ![η,ζ] ∧
        mixedDensity b k σ a y x ![η,ζ] ≤ 2 ∧
        ∀ m : ℕ, 1 ≤ m → m ≤ 2 →
          ‖iteratedFDeriv ℝ m (mixedDensity b k σ a y x) ![η,ζ]‖ ≤ M)) ∧
    (∀ t δ : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε → ∀ b,
      ValidCells (fairCells b k σ t δ) ∧
      (∀ a y x,
        (1/2 : ℝ) ≤ fairDensity b k σ t a y x δ ∧ fairDensity b k σ t a y x δ ≤ 2 ∧
        ∀ m : ℕ, 1 ≤ m → m ≤ 2 →
          ‖iteratedFDeriv ℝ m (fairDensity b k σ t a y x) δ‖ ≤ M))
/-- Actual fair record densities are twice continuously differentiable on the
closed support neighborhood, inside the smooth signed calibration domain. -/
-- @node: FairDensitySmoothness
def FairDensitySmoothness (ε : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ σ : Fin (k + 1) → Bool,
    ∀ t δ : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε →
      ∀ b a y x, ContDiffAt ℝ 2 (fairDensity b k σ t a y x) δ

/-- Actual mixed record densities are twice continuously differentiable on the
signed support square, including full neighborhoods of its boundary. -/
-- @node: MixedDensitySmoothness
def MixedDensitySmoothness (ε : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ σ : Fin (k + 1) → Bool,
    ∀ η ζ : ℝ, |η| ≤ ε → |ζ| ≤ ε →
      ∀ b a y x, ContDiffAt ℝ 2 (mixedDensity b k σ a y x) ![η,ζ]

/-- The actual one-record densities are infinitely differentiable on open
amplitude neighborhoods containing the very same closed signed support box.
The fair clause includes both the random law and the deterministic comparator. -/
-- @node: DensitySmoothNeighbourhood
def DensitySmoothNeighbourhood (ε : ℝ) : Prop :=
  (∃ U : Set (Fin 2 → ℝ), IsOpen U ∧
    {v : Fin 2 → ℝ | |v 0| ≤ ε ∧ |v 1| ≤ ε} ⊆ U ∧
    ∀ k : ℕ, 1 ≤ k → ∀ σ : Fin (k + 1) → Bool,
      ∀ b a y x, ContDiffOn ℝ ∞ (mixedDensity b k σ a y x) U) ∧
  (∃ U : Set ℝ, IsOpen U ∧ {δ : ℝ | |δ| ≤ ε} ⊆ U ∧
    ∀ k : ℕ, 1 ≤ k → ∀ σ : Fin (k + 1) → Bool,
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) →
        ∀ b a y x, ContDiffOn ℝ ∞ (fairDensity b k σ t a y x) U)

/-- Exact singleton cancellation throughout the signed support neighborhood. -/
-- @node: SingletonNeighbourhood
def SingletonNeighbourhood (ε : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (∀ η ζ : ℝ, |η| ≤ ε → |ζ| ≤ ε → ∀ a y x,
      (∑ σ : Fin (k + 1) → Bool, (mixedLaw false k σ η ζ).cells a y x) =
        ∑ σ : Fin (k + 1) → Bool, (mixedLaw true k σ η ζ).cells a y x) ∧
    (∀ t δ : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε → ∀ a y x,
      (Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹ *
        (∑ σ : Fin (k + 1) → Bool, (fairLaw k σ t δ).cells a y x) =
          (fairComparator k t δ).cells a y x)

/-- The actual fair laws inherit the literal four-cell bounds, even on totalization fallback inputs. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:ht,hδ) hold, and [the stated conclusion follows](goal). -/
-- @node: fairDensity_bounds
lemma fairDensity_bounds (b : Bool) (k : ℕ) (σ : Fin (k + 1) → Bool)
    (t δ : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100)
    (a y : Bool) (x : Covariate) :
    (1/2 : ℝ) ≤ fairDensity b k σ t a y x δ ∧
      fairDensity b k σ t a y x δ ≤ 2 := by
  cases b
  · exact totalCellLaw_density_bounds _
      (fairCells_density_bounds false k (fun _ => false) t δ ht hδ) a y x
  · exact totalCellLaw_density_bounds _
      (fairCells_density_bounds true k σ t δ ht hδ) a y x

/-- [The actual mixed laws inherit the literal four-cell bounds, including fallback inputs.](goal) Under [the stated assumptions](hyp:hη,hζ,x). -/
-- @node: mixedDensity_bounds
lemma mixedDensity_bounds (b : Bool) (k : ℕ) (σ : Fin (k + 1) → Bool)
    (η ζ : ℝ) (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100)
    (a y : Bool) (x : Covariate) :
    (1/2 : ℝ) ≤ mixedDensity b k σ a y x ![η,ζ] ∧
      mixedDensity b k σ a y x ![η,ζ] ≤ 2 := by
  exact totalCellLaw_density_bounds _ (mixedCells_density_bounds b k σ η ζ hη hζ) a y x

/-- [The established mixed density bounds and exact table normalization
reduce validity to spatial continuity. [the documented result](goal) Under [the stated assumptions](hyp:hη,hζ,hc). -/
-- @node: mixedCells_valid_of_continuous
lemma mixedCells_valid_of_continuous (b : Bool) (k : ℕ)
    (σ : Fin (k + 1) → Bool) (η ζ : ℝ)
    (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100)
    (hc : ∀ a y, Continuous (mixedCells b k σ η ζ a y)) :
    ValidCells (mixedCells b k σ η ζ) := by
  refine ⟨hc, ?_, ?_⟩
  · intro a y x
    obtain ⟨hlo,hhi⟩ := mixedCells_density_bounds b k σ η ζ hη hζ a y x
    constructor <;> linarith
  · intro x
    simp only [mixedCells, tableCell, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    ring

/-- [The established fair density bounds and exact arm normalization reduce
validity, for the random law and comparator alike, to spatial continuity. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hc). -/
-- @node: fairCells_valid_of_continuous
lemma fairCells_valid_of_continuous (b : Bool) (k : ℕ)
    (σ : Fin (k + 1) → Bool) (t δ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100)
    (hc : ∀ a y, Continuous (fairCells b k σ t δ a y)) :
    ValidCells (fairCells b k σ t δ) := by
  refine ⟨hc, ?_, ?_⟩
  · intro a y x
    obtain ⟨hlo,hhi⟩ := fairCells_density_bounds b k σ t δ ht hδ a y x
    constructor <;> linarith
  · intro x
    simp only [fairCells, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    ring

/-- [A valid mixed construction on a neighborhood has the smooth amplitude
slice of its fully substituted local cell formula. [the documented result](goal) Under [the stated assumptions](hyp:x,hvalid,hsmooth). -/
-- @node: mixedDensity_contDiffAt_of_valid
lemma mixedDensity_contDiffAt_of_valid {n : ℕ∞ω} (b : Bool) (k : ℕ)
    (σ : Fin (k + 1) → Bool) (a y : Bool) (x : Covariate) (v : Fin 2 → ℝ)
    (hvalid : ∀ᶠ w in nhds v, ValidCells (mixedCells b k σ (w 0) (w 1)))
    (hsmooth : ∀ s, ContDiffAt ℝ n (localMixedCell b s a y)
      ![v 0,v 1,cellCoord k x]) :
    ContDiffAt ℝ n (mixedDensity b k σ a y x) v := by
  let s : Bool × Bool :=
    (σ ⟨min (cellIndex k x) k, Nat.lt_succ_of_le (min_le_right _ _)⟩,
     σ ⟨min (cellIndex k x + 1) k, Nat.lt_succ_of_le (min_le_right _ _)⟩)
  have hmap : ContDiffAt ℝ n
      (fun w : Fin 2 → ℝ => ![w 0,w 1,cellCoord k x]) v := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · change ContDiffAt ℝ n (fun w : Fin 2 → ℝ => w 0) v
      fun_prop
    · change ContDiffAt ℝ n (fun w : Fin 2 → ℝ => w 1) v
      fun_prop
    · change ContDiffAt ℝ n (fun _ : Fin 2 → ℝ => cellCoord k x) v
      fun_prop
  have hslice := (hsmooth s).comp v hmap
  have hd : ContDiffAt ℝ n (fun w : Fin 2 → ℝ =>
      4 * localMixedCell b s a y ![w 0,w 1,cellCoord k x]) v :=
    contDiffAt_const.mul hslice
  apply hd.congr_of_eventuallyEq
  filter_upwards [hvalid] with w hw
  simp only [mixedDensity, mixedLaw, totalCellLaw_cells_of_valid _ hw]
  rfl

/-- [Both fair constructions inherit amplitude smoothness from the local
calibration formula wherever their cell-law constructor is valid nearby. [the documented result](goal) Under [the stated assumptions](hyp:x,hvalid,hsmooth). -/
-- @node: fairDensity_contDiffAt_of_valid
lemma fairDensity_contDiffAt_of_valid {n : ℕ∞ω} (b : Bool) (k : ℕ)
    (σ : Fin (k + 1) → Bool) (t : ℝ) (a y : Bool) (x : Covariate) (δ : ℝ)
    (hvalid : ∀ᶠ d in nhds δ,
      ValidCells (fairCells b k (if b then σ else fun _ => false) t d))
    (hsmooth : ∀ s, ContDiffAt ℝ n (localFairCell b s a y)
      ![t,δ,cellCoord k x]) :
    ContDiffAt ℝ n (fairDensity b k σ t a y x) δ := by
  let τ : Fin (k + 1) → Bool := if b then σ else fun _ => false
  let s : Bool × Bool :=
    (τ ⟨min (cellIndex k x) k, Nat.lt_succ_of_le (min_le_right _ _)⟩,
     τ ⟨min (cellIndex k x + 1) k, Nat.lt_succ_of_le (min_le_right _ _)⟩)
  have hmap : ContDiffAt ℝ n (fun d : ℝ => ![t,d,cellCoord k x]) δ := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · change ContDiffAt ℝ n (fun _ : ℝ => t) δ
      fun_prop
    · change ContDiffAt ℝ n (fun d : ℝ => d) δ
      fun_prop
    · change ContDiffAt ℝ n (fun _ : ℝ => cellCoord k x) δ
      fun_prop
  have hslice := (hsmooth s).comp δ hmap
  have hd : ContDiffAt ℝ n (fun d : ℝ =>
      4 * localFairCell b s a y ![t,d,cellCoord k x]) δ :=
    contDiffAt_const.mul hslice
  apply hd.congr_of_eventuallyEq
  filter_upwards [hvalid] with d hd
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hd ⊢
  all_goals
    simp only [fairDensity, Bool.false_eq_true, ↓reduceIte, fairComparator, fairLaw,
      totalCellLaw_cells_of_valid _ hd]
    rfl

/-- [A smaller closed amplitude region lies strictly inside the validity
region. Smooth local calibration formulas therefore give smooth actual record
densities even at the boundary of the closed region. [the documented result](goal) -/
-- @node: calibrated_density_smoothness_of_valid
lemma calibrated_density_smoothness_of_valid : ∃ ρ : ℝ, 0 < ρ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ρ →
      (∀ k : ℕ, 1 ≤ k → ∀ σ : Fin (k + 1) → Bool,
        (∀ η ζ : ℝ, |η| ≤ 2*ε → |ζ| ≤ 2*ε → ∀ b,
          ValidCells (mixedCells b k σ η ζ)) ∧
        (∀ t δ : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ 2*ε → ∀ b,
          ValidCells (fairCells b k σ t δ))) →
      FairDensitySmoothness ε ∧ MixedDensitySmoothness ε ∧
        DensitySmoothNeighbourhood ε := by
  obtain ⟨ρm,hρm,hm⟩ := localMixedCell_uniform_contDiffAt
  obtain ⟨ρf,hρf,hsmall,hf⟩ := fairRoot_uniform_contDiffAt
  refine ⟨min ρm ρf / 2, by positivity, ?_⟩
  intro ε hε hρ hv
  have hem : 2*ε ≤ ρm := by linarith [min_le_left ρm ρf]
  have hef : 2*ε ≤ ρf := by linarith [min_le_right ρm ρf]
  have hfair (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k+1) → Bool)
      (t δ : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| < 2*ε)
      (b a y : Bool) (x : Covariate) :
      ContDiffAt ℝ ∞ (fairDensity b k σ t a y x) δ := by
    apply fairDensity_contDiffAt_of_valid
    · have hn : ∀ᶠ d : ℝ in nhds δ, |d| < 2*ε :=
        (by fun_prop : ContinuousAt (fun d : ℝ => |d|) δ).eventually_lt_const hδ
      filter_upwards [hn] with d hd
      exact (hv k hk (if b then σ else fun _ => false)).2 t d ht hd.le b
    · intro s
      have hroot := hf ![t,δ,cellCoord k x]
        ⟨ht,hδ.le.trans hef,cellCoord_mem_unit k hk x⟩
      exact (localFairCell_contDiffAt_of_root _ ht
        ((hδ.le.trans hef).trans hsmall) hroot b s a y)
  have hmixed (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k+1) → Bool)
      (v : Fin 2 → ℝ) (hη : |v 0| < 2*ε) (hζ : |v 1| < 2*ε)
      (b a y : Bool) (x : Covariate) :
      ContDiffAt ℝ ∞ (mixedDensity b k σ a y x) v := by
    apply mixedDensity_contDiffAt_of_valid
    · have hn0 : ∀ᶠ w : Fin 2 → ℝ in nhds v, |w 0| < 2*ε :=
        ((continuous_apply 0).abs.continuousAt).eventually_lt_const hη
      have hn1 : ∀ᶠ w : Fin 2 → ℝ in nhds v, |w 1| < 2*ε :=
        ((continuous_apply 1).abs.continuousAt).eventually_lt_const hζ
      filter_upwards [hn0,hn1] with w h0 h1
      exact (hv k hk σ).1 (w 0) (w 1) h0.le h1.le b
    · intro s
      exact (hm ![v 0,v 1,cellCoord k x]
        ⟨hη.le.trans hem,hζ.le.trans hem,cellCoord_mem_unit k hk x⟩ b s a y).of_le le_top
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk σ t δ ht hδ b a y x
    exact (hfair k hk σ t δ ht (by linarith) b a y x).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · intro k hk σ η ζ hη hζ b a y x
    exact (hmixed k hk σ ![η,ζ] (by simpa using (show |η| < 2*ε by linarith))
      (by simpa using (show |ζ| < 2*ε by linarith)) b a y x).of_le
        (WithTop.coe_le_coe.mpr le_top)
  · refine ⟨{v : Fin 2 → ℝ | |v 0| < 2*ε ∧ |v 1| < 2*ε}, ?_, ?_, ?_⟩
    · exact (isOpen_lt (continuous_apply 0).abs continuous_const).inter
        (isOpen_lt (continuous_apply 1).abs continuous_const)
    · intro v hv
      exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
    · intro k hk σ b a y x v hv
      exact (hmixed k hk σ v hv.1 hv.2 b a y x).contDiffWithinAt
  · refine ⟨{δ : ℝ | |δ| < 2*ε}, ?_, ?_, ?_⟩
    · exact isOpen_lt continuous_abs continuous_const
    · intro δ hδ
      change |δ| ≤ ε at hδ
      exact lt_of_le_of_lt hδ (by linarith)
    · intro k hk σ t ht b a y x δ hδ
      exact (hfair k hk σ t δ ht hδ b a y x).contDiffWithinAt

/-- Nearby validity identifies the derivatives of an actual mixed density
with the derivatives of its local formula, with the spatial coordinate fixed. [the documented result](goal) Under [the stated assumptions](hyp:x,hvalid). -/
-- @node: mixedDensity_iteratedFDeriv_of_valid
lemma mixedDensity_iteratedFDeriv_of_valid (b : Bool) (k : ℕ)
    (σ : Fin (k + 1) → Bool) (a y : Bool) (x : Covariate) (v : Fin 2 → ℝ)
    (hvalid : ∀ᶠ w in nhds v, ValidCells (mixedCells b k σ (w 0) (w 1)))
    (m : ℕ) :
    ∃ s : Bool × Bool, iteratedFDeriv ℝ m (mixedDensity b k σ a y x) v =
      iteratedFDeriv ℝ m
        (fun w : Fin 2 → ℝ => 4*localMixedCell b s a y ![w 0,w 1,cellCoord k x]) v := by
  let s : Bool × Bool :=
    (σ ⟨min (cellIndex k x) k, Nat.lt_succ_of_le (min_le_right _ _)⟩,
     σ ⟨min (cellIndex k x + 1) k, Nat.lt_succ_of_le (min_le_right _ _)⟩)
  refine ⟨s,?_⟩
  have heq : mixedDensity b k σ a y x =ᶠ[nhds v]
      (fun w : Fin 2 → ℝ => 4*localMixedCell b s a y ![w 0,w 1,cellCoord k x]) := by
    filter_upwards [hvalid] with w hw
    simp only [mixedDensity, mixedLaw, totalCellLaw_cells_of_valid _ hw]
    rfl
  exact (heq.iteratedFDeriv ℝ m).eq_of_nhds

/-- [Nearby validity identifies an actual fair or comparator density with its
local amplitude slice to every derivative order. [the documented result](goal) Under [the stated assumptions](hyp:x,hvalid). -/
-- @node: fairDensity_iteratedFDeriv_of_valid
lemma fairDensity_iteratedFDeriv_of_valid (b : Bool) (k : ℕ)
    (σ : Fin (k + 1) → Bool) (t : ℝ) (a y : Bool) (x : Covariate) (δ : ℝ)
    (hvalid : ∀ᶠ d in nhds δ,
      ValidCells (fairCells b k (if b then σ else fun _ => false) t d)) (m : ℕ) :
    ∃ s : Bool × Bool, iteratedFDeriv ℝ m (fairDensity b k σ t a y x) δ =
      iteratedFDeriv ℝ m (fun d : ℝ => 4*localFairCell b s a y ![t,d,cellCoord k x]) δ := by
  let τ : Fin (k + 1) → Bool := if b then σ else fun _ => false
  let s : Bool × Bool :=
    (τ ⟨min (cellIndex k x) k, Nat.lt_succ_of_le (min_le_right _ _)⟩,
     τ ⟨min (cellIndex k x + 1) k, Nat.lt_succ_of_le (min_le_right _ _)⟩)
  refine ⟨s,?_⟩
  have heq : fairDensity b k σ t a y x =ᶠ[nhds δ]
      (fun d : ℝ => 4*localFairCell b s a y ![t,d,cellCoord k x]) := by
    filter_upwards [hvalid] with d hd
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hd ⊢
    all_goals
      simp only [fairDensity, Bool.false_eq_true, ↓reduceIte, fairComparator, fairLaw,
        totalCellLaw_cells_of_valid _ hd]
      rfl
  exact (heq.iteratedFDeriv ℝ m).eq_of_nhds

/-- Validity on the larger signed box transfers the compact local density
envelopes to both actual density families on every smaller closed box. [the documented result](goal) -/
-- @node: calibrated_density_derivative_envelopes_of_valid
lemma calibrated_density_derivative_envelopes_of_valid : ∃ r M : ℝ, 0 < r ∧ 1 ≤ M ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ r →
      (∀ k : ℕ, 1 ≤ k → ∀ σ : Fin (k + 1) → Bool,
        (∀ η ζ : ℝ, |η| ≤ 2*ε → |ζ| ≤ 2*ε → ∀ b,
          ValidCells (mixedCells b k σ η ζ)) ∧
        (∀ t δ : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ 2*ε → ∀ b,
          ValidCells (fairCells b k σ t δ))) →
      (∀ k : ℕ, 1 ≤ k → ∀ σ : Fin (k + 1) → Bool,
        ∀ η ζ : ℝ, |η| ≤ ε → |ζ| ≤ ε → ∀ b a y x,
          ∀ m : ℕ, 1 ≤ m → m ≤ 2 →
            ‖iteratedFDeriv ℝ m (mixedDensity b k σ a y x) ![η,ζ]‖ ≤ M) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ σ : Fin (k + 1) → Bool,
        ∀ t δ : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε → ∀ b a y x,
          ∀ m : ℕ, 1 ≤ m → m ≤ 2 →
            ‖iteratedFDeriv ℝ m (fairDensity b k σ t a y x) δ‖ ≤ M) := by
  obtain ⟨r,M,hr,hM,hm,hf⟩ := calibrated_local_density_derivative_envelopes
  refine ⟨r,M,hr,hM,?_⟩
  intro ε hε her hv
  constructor
  · intro k hk σ η ζ hη hζ b a y x m hmlo hmhi
    have hvalid : ∀ᶠ w : Fin 2 → ℝ in nhds ![η,ζ],
        ValidCells (mixedCells b k σ (w 0) (w 1)) := by
      have hn0 : ∀ᶠ w : Fin 2 → ℝ in nhds ![η,ζ], |w 0| < 2*ε :=
        ((continuous_apply 0).abs.continuousAt).eventually_lt_const
          (by simpa using (show |η| < 2*ε by linarith))
      have hn1 : ∀ᶠ w : Fin 2 → ℝ in nhds ![η,ζ], |w 1| < 2*ε :=
        ((continuous_apply 1).abs.continuousAt).eventually_lt_const
          (by simpa using (show |ζ| < 2*ε by linarith))
      filter_upwards [hn0,hn1] with w h0 h1
      exact (hv k hk σ).1 (w 0) (w 1) h0.le h1.le b
    obtain ⟨s,heq⟩ := mixedDensity_iteratedFDeriv_of_valid b k σ a y x ![η,ζ] hvalid m
    rw [heq]
    exact hm η ζ (cellCoord k x) (hη.trans her) (hζ.trans her)
      (cellCoord_mem_unit k hk x) b s a y m hmlo hmhi
  · intro k hk σ t δ ht hδ b a y x m hmlo hmhi
    have hvalid : ∀ᶠ d in nhds δ,
        ValidCells (fairCells b k (if b then σ else fun _ => false) t d) := by
      have hn : ∀ᶠ d : ℝ in nhds δ, |d| < 2*ε :=
        (by fun_prop : ContinuousAt (fun d : ℝ => |d|) δ).eventually_lt_const
          (by linarith)
      filter_upwards [hn] with d hd
      exact (hv k hk (if b then σ else fun _ => false)).2 t d ht hd.le b
    obtain ⟨s,heq⟩ := fairDensity_iteratedFDeriv_of_valid b k σ t a y x δ hvalid m
    rw [heq]
    exact hf t δ (cellCoord k x) ht (hδ.trans her)
      (cellCoord_mem_unit k hk x) b s a y m hmlo hmhi

-- @node: lem:calibrated-support
/-- One absolute calibration radius and derivative envelope support every legal
exponent pair and certify infinitely differentiable densities on open
neighborhoods containing that same closed signed amplitude box. [the documented result](goal) -/
lemma calibrated_support : ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
  CalibratedMembership ε ∧ DensityNeighbourhood ε M ∧ SingletonNeighbourhood ε ∧
  ε ≤ 1/100 ∧ 1 ≤ M ∧ FairDensitySmoothness ε ∧ MixedDensitySmoothness ε ∧
  DensitySmoothNeighbourhood ε := by
  obtain ⟨εcal, Mcal, hεcal, hMcal, hSmooth, hDerivatives, hBranch,
    hMixedCalibration, hFairCalibration⟩ := exact_calibrations
  obtain ⟨ρ, hρ, hDensitySmooth⟩ := calibrated_density_smoothness_of_valid
  obtain ⟨rD, M, hrD, hM, hDensityDeriv⟩ := calibrated_density_derivative_envelopes_of_valid
  obtain ⟨rE, hrE, _, hFairEnvelope⟩ := fairCells_uniform_prognosis_envelope
  obtain ⟨rO, hrO, _, hFairOscillation⟩ := fairCells_uniform_prognosis_oscillation
  obtain ⟨rL, hrL, _, hFairLinear⟩ := fairCells_uniform_prognosis_linear
  obtain ⟨rP, hrP, _, hMixedLinear⟩ := mixedCells_uniform_propensity_linear
  obtain ⟨rN, hrN, _, hAlternativeLinear⟩ := mixedCells_uniform_alternative_prognosis_linear
  obtain ⟨ε, hε, hsmall, hcalSmall, hModelBounds,
    hSmoothRadius, hDerivRadius, hEnvelopeRadius, hWideSmall, hCalWide, hOscRadius, hLinRadius⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/100 ∧ ε ≤ εcal ∧
        (∀ α β : ℝ, ExponentDomain α β → ∀ k : ℕ, 1 ≤ k →
          (∀ σ : Fin (k+1) → Bool,
            CalibratedSpatialBounds α β k (mixedLaw false k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) ∧
            CalibratedSpatialBounds α β k (mixedLaw true k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))))) ∧
        ε ≤ ρ ∧ ε ≤ rD ∧ ε ≤ rE ∧ 2*ε ≤ 1/100 ∧ 2*ε ≤ εcal ∧ ε ≤ rO ∧ ε ≤ rL := by
    obtain ⟨ε, hε, hsmall, hcal, hRemaining, hs, hd, he, hw, hc, ho, hl, hpRadius⟩ :
        ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/100 ∧ ε ≤ εcal ∧
          (∀ α β : ℝ, ExponentDomain α β → ∀ k : ℕ, 1 ≤ k →
            ∀ σ : Fin (k+1) → Bool,
              let P := mixedLaw true k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))
              (∀ x z, |prognosisLogit P x-prognosisLogit P z| ≤
                (k : ℝ)^(1-β)*|(x : ℝ)-(z : ℝ)|)) ∧
          ε ≤ ρ ∧ ε ≤ rD ∧ ε ≤ rE ∧ 2*ε ≤ 1/100 ∧
          2*ε ≤ εcal ∧ ε ≤ rO ∧ ε ≤ rL ∧ ε ≤ rP := by
      let R := min εcal (min ρ (min rD (min rE (min rO (min rL (min rP (min rN (1/100))))))))
      have hR : 0 < R := by
        dsimp [R]
        positivity
      have hRs : R ≤ εcal ∧ R ≤ ρ ∧ R ≤ rD ∧ R ≤ rE ∧
          R ≤ rO ∧ R ≤ rL ∧ R ≤ rP ∧ R ≤ rN ∧ R ≤ 1/100 := by
        simp [R,min_le_iff]
      refine ⟨R/2,by positivity,by linarith [hRs.2.2.2.2.2.2.2.2],by linarith [hRs.1],
        ?_,by linarith [hRs.2.1],by linarith [hRs.2.2.1],by linarith [hRs.2.2.2.1],
        by linarith [hRs.2.2.2.2.2.2.2.2],by linarith [hRs.1],
        by linarith [hRs.2.2.2.2.1],by linarith [hRs.2.2.2.2.2.1],
        by linarith [hRs.2.2.2.2.2.2.1]⟩
      intro α β hab k hk σ
      exact hAlternativeLinear (R/2) (by positivity)
        (by linarith [hRs.2.2.2.2.2.2.2.1]) α β hab k hk σ
    refine ⟨ε, hε, hsmall, hcal, ?_, hs, hd, he, hw, hc, ho, hl⟩
    intro α β hab k hk σ
    have hsp (b : Bool) : CalibratedSpatialBounds α β k
        (mixedLaw b k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) := by
      have hn : ∀ x z,
          |prognosisLogit (mixedLaw b k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) x-
            prognosisLogit (mixedLaw b k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) z| ≤
            (k : ℝ)^(1-β)*|(x : ℝ)-(z : ℝ)| := by
        cases b
        · exact mixedCells_uniform_null_prognosis_linear ε hε hsmall α β
            (hab.1.trans hab.2.2.1).le hab.1.le k hk σ
        · exact hRemaining α β hab k hk σ
      exact ⟨hMixedLinear ε hε hpRadius α β
        (hab.1.trans hab.2.2.1).le hab.1.le k hk σ b,
        mixedCells_uniform_propensity_oscillation ε hε hsmall α β
          (hab.1.trans hab.2.2.1).le hab.1.le k hk σ b,
        hn, mixedCells_uniform_prognosis_oscillation ε hε hsmall α β
          (hab.1.trans hab.2.2.1).le hab.1.le k hk σ b⟩
    exact ⟨hsp false, hsp true⟩
  have hContinuousWide (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k + 1) → Bool) :
      (∀ η ζ : ℝ, |η| ≤ 2*ε → |ζ| ≤ 2*ε → ∀ b,
        ∀ a y, Continuous (mixedCells b k σ η ζ a y)) ∧
      (∀ t δ : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ 2*ε → ∀ b,
        ∀ a y, Continuous (fairCells b k σ t δ a y)) := by
    constructor
    · intro η ζ hη hζ b a y
      exact mixedCells_continuous_of_smooth εcal hSmooth k hk σ η ζ
        (hη.trans hCalWide) (hζ.trans hCalWide) b a y
    · intro t δ ht hδ b a y
      exact fairCells_continuous_of_smooth εcal hSmooth k hk σ t δ ht
        (hδ.trans hCalWide) b a y
  have hValidWide (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k + 1) → Bool) :
      (∀ η ζ : ℝ, |η| ≤ 2*ε → |ζ| ≤ 2*ε → ∀ b,
        ValidCells (mixedCells b k σ η ζ)) ∧
      (∀ t δ : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ 2*ε → ∀ b,
        ValidCells (fairCells b k σ t δ)) := by
    constructor
    · intro η ζ hη hζ b
      exact mixedCells_valid_of_continuous b k σ η ζ (hη.trans hWideSmall)
        (hζ.trans hWideSmall) ((hContinuousWide k hk σ).1 η ζ hη hζ b)
    · intro t δ ht hδ b
      exact fairCells_valid_of_continuous b k σ t δ ht (hδ.trans hWideSmall)
        ((hContinuousWide k hk σ).2 t δ ht hδ b)
  obtain ⟨hMixedDeriv,hFairDeriv⟩ := hDensityDeriv ε hε hDerivRadius hValidWide
  have hMixed (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k + 1) → Bool)
      (η ζ : ℝ) (hη : |η| ≤ ε) (hζ : |ζ| ≤ ε) (b : Bool) :
      ValidCells (mixedCells b k σ η ζ) ∧
      (∀ a y x, ∀ m : ℕ, 1 ≤ m → m ≤ 2 →
        ‖iteratedFDeriv ℝ m (mixedDensity b k σ a y x) ![η,ζ]‖ ≤ M) :=
    ⟨(hValidWide k hk σ).1 η ζ (by linarith) (by linarith) b,
      hMixedDeriv k hk σ η ζ hη hζ b⟩
  have hFair (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k + 1) → Bool)
      (t δ : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ ε) (b : Bool) :
      ValidCells (fairCells b k σ t δ) ∧
      (∀ a y x, ∀ m : ℕ, 1 ≤ m → m ≤ 2 →
        ‖iteratedFDeriv ℝ m (fairDensity b k σ t a y x) δ‖ ≤ M) :=
    ⟨(hValidWide k hk σ).2 t δ ht (by linarith) b,
      hFairDeriv k hk σ t δ ht hδ b⟩
  obtain ⟨hFairSmooth, hMixedSmooth, hDensitySmoothNeighbourhood⟩ :=
    hDensitySmooth ε hε hSmoothRadius hValidWide
  have hModels : CalibratedModels ε := by
    intro α β hab k hk
    dsimp only
    have hη : |ε*(k : ℝ)^(-α)| ≤ ε :=
      calibrated_amplitude_abs_le ε α hε.le (hab.1.trans hab.2.2.1).le k hk
    have hζ : |ε*(k : ℝ)^(-β)| ≤ ε :=
      calibrated_amplitude_abs_le ε β hε.le hab.1.le k hk
    have hm := hModelBounds α β hab k hk
    constructor
    · intro σ
      obtain ⟨hm0, hm1⟩ := hm σ
      have hm0 := calibrated_model_of_bounds α β k _ hab hk
        (mixedCells_model_bounds_of_spatial α β false k σ _ _
          (hη.trans hsmall) (hζ.trans hsmall)
          (hMixed k hk σ _ _ hη hζ false).1 hm0)
      have hm1 := calibrated_model_of_bounds α β k _ hab hk
        (mixedCells_model_bounds_of_spatial α β true k σ _ _
          (hη.trans hsmall) (hζ.trans hsmall)
          (hMixed k hk σ _ _ hη hζ true).1 hm1)
      have he0 := (mixedCells_homogeneous_effect false k σ _ _
        (hη.trans hsmall) (hζ.trans hsmall)
        (hMixed k hk σ _ _ hη hζ false).1).1
      have he1 := (mixedCells_homogeneous_effect true k σ _ _
        (hη.trans hsmall) (hζ.trans hsmall)
        (hMixed k hk σ _ _ hη hζ true).1).1
      exact ⟨hm0, hm1, he0, he1⟩
    · intro t ht
      have hr (σ : Fin (k+1) → Bool) :=
        hFairLinear ε hε hLinRadius β hab.1.le k hk σ t ht true
      have hc := hFairLinear ε hε hLinRadius β hab.1.le k hk (fun _ => false) t ht false
      have hc := fairCells_model_bounds_of_prognosis α β false k (fun _ => false)
        t _ ht (hζ.trans hsmall) (hFair k hk (fun _ => false) t _ ht hζ false).1
        ⟨hFairEnvelope k hk (fun _ => false) t _ ht (hζ.trans hEnvelopeRadius) false,
          hc, hFairOscillation ε hε hOscRadius β hab.1.le k hk (fun _ => false) t ht false⟩
      refine ⟨?_, calibrated_model_of_bounds α β k _ hab hk hc, ?_⟩
      · intro σ
        have hr := fairCells_model_bounds_of_prognosis α β true k σ
          t _ ht (hζ.trans hsmall) (hFair k hk σ t _ ht hζ true).1
          ⟨hFairEnvelope k hk σ t _ ht (hζ.trans hEnvelopeRadius) true,
            hr σ, hFairOscillation ε hε hOscRadius β hab.1.le k hk σ t ht true⟩
        exact ⟨calibrated_model_of_bounds α β k _ hab hk hr, (fairCells_homogeneous_effect true k σ t _ (hζ.trans hsmall)
          (hFair k hk σ t _ ht hζ true).1).1⟩
      · exact (fairCells_homogeneous_effect false k (fun _ => false) t _
          (hζ.trans hsmall) (hFair k hk (fun _ => false) t _ ht hζ false).1).1
  have hMembership : CalibratedMembership ε := by
    intro α β hab k hk
    dsimp only
    obtain ⟨hm, hf⟩ := hModels α β hab k hk
    have hη : |ε*(k : ℝ)^(-α)| ≤ ε :=
      calibrated_amplitude_abs_le ε α hε.le (hab.1.trans hab.2.2.1).le k hk
    have hζ : |ε*(k : ℝ)^(-β)| ≤ ε :=
      calibrated_amplitude_abs_le ε β hε.le hab.1.le k hk
    refine ⟨hm, ?_, ?_⟩
    · intro a y x
      have hroot := hMixedCalibration _ _ (cellCoord k x)
        (hη.trans hcalSmall) (hζ.trans hcalSmall) (cellCoord_mem_unit k hk x)
      apply mixedLaw_singleton_matching k hk _ _
        (fun b σ => (hMixed k hk σ _ _ hη hζ b).1) x hroot.2.2.1 a y
    · intro t ht
      obtain ⟨hmodels, hcomp, heffect⟩ := hf t ht
      refine ⟨hmodels, hcomp, heffect, ?_⟩
      intro a y x
      obtain ⟨_, _, _, _, _, _, _, hmatch, _⟩ := hFairCalibration t _ (cellCoord k x)
        ht (hζ.trans hcalSmall) (cellCoord_mem_unit k hk x)
      exact fairLaw_singleton_matching k hk t _
        (fun σ => (hFair k hk σ t _ ht hζ true).1)
        (hFair k hk (fun _ => false) t _ ht hζ false).1 x hmatch a y
  have hSingletons : SingletonNeighbourhood ε := by
    intro k hk
    constructor
    · intro η ζ hη hζ a y x
      have hroot := hMixedCalibration η ζ (cellCoord k x)
        (hη.trans hcalSmall) (hζ.trans hcalSmall) (cellCoord_mem_unit k hk x)
      exact mixedLaw_singleton_matching k hk η ζ
        (fun b σ => (hMixed k hk σ η ζ hη hζ b).1) x hroot.2.2.1 a y
    · intro t δ ht hδ a y x
      obtain ⟨_, _, _, _, _, _, _, hmatch, _⟩ := hFairCalibration t δ (cellCoord k x)
        ht (hδ.trans hcalSmall) (cellCoord_mem_unit k hk x)
      exact fairLaw_singleton_matching k hk t δ
        (fun σ => (hFair k hk σ t δ ht hδ true).1)
        (hFair k hk (fun _ => false) t δ ht hδ false).1 x hmatch a y
  refine ⟨ε, M, hε, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hM,
    hMembership, ?_, hSingletons, hsmall, hM, hFairSmooth, hMixedSmooth,
    hDensitySmoothNeighbourhood⟩
  intro k hk σ
  constructor
  · intro η ζ hη hζ b
    obtain ⟨hValid, hDeriv⟩ := hMixed k hk σ η ζ hη hζ b
    refine ⟨hValid, ?_⟩
    intro a y x
    obtain ⟨hLower, hUpper⟩ := mixedDensity_bounds b k σ η ζ
      (hη.trans hsmall) (hζ.trans hsmall) a y x
    exact ⟨hLower, hUpper, hDeriv a y x⟩
  · intro t δ ht hδ b
    obtain ⟨hValid, hDeriv⟩ := hFair k hk σ t δ ht hδ b
    refine ⟨hValid, ?_⟩
    intro a y x
    obtain ⟨hLower, hUpper⟩ := fairDensity_bounds b k σ t δ ht (hδ.trans hsmall) a y x
    exact ⟨hLower, hUpper, hDeriv a y x⟩
/-- The support radius chosen from the actual support theorem. -/
def calibEps : ℝ := Classical.choose calibrated_support
/-- The derivative envelope chosen together with that same radius. -/
def calibM : ℝ := Classical.choose (Classical.choose_spec calibrated_support)
/-- Export the jointly selected constants, rather than mismatching separate existential witnesses. [the stated conclusion](goal) holds. -/
-- @node: calib_constants_spec
lemma calib_constants_spec : 0 < calibEps ∧ 0 < calibM ∧
  CalibratedMembership calibEps ∧ DensityNeighbourhood calibEps calibM := by
  obtain ⟨hε, hM, hMembership, hDensity, _, _⟩ :=
    Classical.choose_spec (Classical.choose_spec calibrated_support)
  exact ⟨hε, hM, hMembership, hDensity⟩

/-- The same chosen support radius supplies exact singleton matching, with no
rate scaling restriction on the signed amplitudes. [the documented result](goal) -/
-- @node: calib_singletons_spec
lemma calib_singletons_spec : SingletonNeighbourhood calibEps := by
  exact (Classical.choose_spec (Classical.choose_spec calibrated_support)).2.2.2.2.1
/-- The jointly chosen radius is inside the explicit cell-bound square, its
common derivative envelope is at least one, and fair densities are smooth. [the documented result](goal) -/
-- @node: calib_regularity_spec
lemma calib_regularity_spec : calibEps ≤ 1/100 ∧ 1 ≤ calibM ∧
    FairDensitySmoothness calibEps := by
  obtain ⟨hsmall, hM, hFair, hMixed⟩ :=
    (Classical.choose_spec (Classical.choose_spec calibrated_support)).2.2.2.2.2
  exact ⟨hsmall, hM, hFair⟩

/-- The same selected support square supplies mixed-density smoothness. [the stated conclusion](goal) holds. -/
-- @node: calib_mixed_smoothness_spec
lemma calib_mixed_smoothness_spec : MixedDensitySmoothness calibEps := by
  exact (Classical.choose_spec (Classical.choose_spec calibrated_support)).2.2.2.2.2.2.2.2.1

end CausalSmith.Stat.LogoddsLowsmoothFrontier
