module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # Scalar calibrations, continuous sign priors, and full-data extensions

Local root selectors are totalized outside their brackets. Probability laws are
constructed from the displayed cells, with a fixed harmless default outside the
positive-cell neighbourhood; neighbourhood validity is a theorem obligation.
-/
@[expose] public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier
attribute [local instance] Classical.propDecidable

/-- [Uniform design is a probability measure. [the stated conclusion](goal) holds. -/
-- @node: uniformLaw_probability
lemma uniformLaw_probability : IsProbabilityMeasure uniformLaw := by
  constructor
  rw [uniformLaw, comap_subtype_coe_apply measurableSet_Icc]
  rw [Set.image_univ, Subtype.range_coe, Real.volume_Icc]
  norm_num
/-- [The anonymous instance result](goal) states the corresponding mathematical identity, bound, or structural property. -/
instance : IsProbabilityMeasure uniformLaw := uniformLaw_probability
/-- Continuous, normalized, strictly interior conditional cells. -/
def ValidCells (p : Bool → Bool → Covariate → ℝ) : Prop :=
  (∀ a y, Continuous (p a y)) ∧ (∀ a y x, 0 < p a y x ∧ p a y x < 1) ∧
  (∀ x, ∑ a : Bool, ∑ y : Bool, p a y x = 1)
/-- Marginal of the explicitly constructed cell law. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: jointLaw_uniform
lemma jointLaw_uniform (p : Bool → Bool → Covariate → ℝ) (h : ValidCells p) :
  Measure.map covariate (jointLaw uniformLaw p) = uniformLaw := by
  have hm (a y : Bool) : Measurable (fun x => ENNReal.ofReal (p a y x)) :=
    ENNReal.measurable_ofReal.comp (h.1 a y).measurable
  have hc : Measurable covariate := by unfold covariate; fun_prop
  simp only [jointLaw, Fintype.sum_bool, Measure.map_add _ _ hc,
    Measure.map_map hc (by fun_prop : Measurable (fun x : Covariate => (x, false, false))),
    Measure.map_map hc (by fun_prop : Measurable (fun x : Covariate => (x, false, true))),
    Measure.map_map hc (by fun_prop : Measurable (fun x : Covariate => (x, true, false))),
    Measure.map_map hc (by fun_prop : Measurable (fun x : Covariate => (x, true, true))),
    covariate, Function.comp_def, Measure.map_id']
  rw [← withDensity_add_left (hm true true),
    ← withDensity_add_left (hm false true),
    ← withDensity_add_left ((hm true true).add (hm true false))]
  convert withDensity_one (μ := uniformLaw) using 1
  congr 1
  funext x
  have hn := h.2.2 x
  simp only [Fintype.sum_bool] at hn
  simp only [Pi.add_apply, Pi.one_apply]
  rw [← ENNReal.ofReal_add (h.2.1 true true x).1.le (h.2.1 true false x).1.le,
    ← ENNReal.ofReal_add (h.2.1 false true x).1.le (h.2.1 false false x).1.le,
    ← ENNReal.ofReal_add
      (add_nonneg (h.2.1 true true x).1.le (h.2.1 true false x).1.le)
      (add_nonneg (h.2.1 false true x).1.le (h.2.1 false false x).1.le),
    hn, ENNReal.ofReal_one]
/-- [The law of valid cells is a probability law.](goal) Under [the stated assumptions](hyp:h). -/
-- @node: jointLaw_probability
lemma jointLaw_probability (p : Bool → Bool → Covariate → ℝ) (h : ValidCells p) :
  IsProbabilityMeasure (jointLaw uniformLaw p) := by
  constructor
  have hm := congrArg (fun μ : Measure Covariate => μ Set.univ) (jointLaw_uniform p h)
  rw [Measure.map_apply (by unfold covariate; fun_prop) MeasurableSet.univ] at hm
  simpa using hm
/-- [The explicitly constructed law has the required disintegration identity.](goal) Under [the stated assumptions](hyp:h). -/
-- @node: jointLaw_disintegration
lemma jointLaw_disintegration (p : Bool → Bool → Covariate → ℝ) (h : ValidCells p) :
  jointLaw uniformLaw p = jointLaw (Measure.map covariate (jointLaw uniformLaw p)) p := by
  rw [jointLaw_uniform p h]
/-- [Uniform laws have full support.](goal) Under [the stated assumptions](hyp:h). -/
-- @node: jointLaw_full_support
lemma jointLaw_full_support (p : Bool → Bool → Covariate → ℝ) (h : ValidCells p) :
  ∀ G : Set Covariate, IsOpen G → G.Nonempty →
    0 < (Measure.map covariate (jointLaw uniformLaw p)) G := by
  intro G hG hNonempty
  rw [jointLaw_uniform p h, uniformLaw,
    comap_subtype_coe_apply measurableSet_Icc]
  obtain ⟨U, hU, hUG⟩ := isOpen_induced_iff.mp hG
  obtain ⟨x, hx⟩ := hNonempty
  have hxU : (x : ℝ) ∈ U := by
    change x ∈ Subtype.val ⁻¹' U
    rw [hUG]
    exact hx
  have hxClosure : (x : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact x.property
  have hIntersection : (U ∩ Set.Ioo (0 : ℝ) 1).Nonempty :=
    mem_closure_iff.mp hxClosure U hU hxU
  have hPositive : 0 < volume (U ∩ Set.Ioo (0 : ℝ) 1) :=
    (hU.inter isOpen_Ioo).measure_pos volume hIntersection
  apply lt_of_lt_of_le hPositive
  apply measure_mono
  intro z hz
  refine ⟨⟨z, hz.2.1.le, hz.2.2.le⟩, ?_, rfl⟩
  rw [← hUG]
  exact hz.1
/-- [Pack the concrete cell construction into the ambient carrier. -/
def lawFromCells (p : Bool → Bool → Covariate → ℝ) (h : ValidCells p) : ObservedLaw where
  measure := jointLaw uniformLaw p
  probability := jointLaw_probability p h
  cells := p
  continuous_cells := h.1
  interior_cells := h.2.1
  normalized_cells := h.2.2
  disintegration := jointLaw_disintegration p h
  full_support := jointLaw_full_support p h
/-- A fixed interior table for totalization outside the calibration neighbourhood. [the stated conclusion](goal) holds. -/
-- @node: fairDefault_valid
lemma fairDefault_valid : ValidCells (fun _ _ _ => (1/4 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a y
    fun_prop
  · intro a y x
    norm_num
  · intro x
    norm_num [Fintype.sum_bool]
/-- Total cell-law constructor; on valid cells it is literally the given cell law. -/
def totalCellLaw (p : Bool → Bool → Covariate → ℝ) : ObservedLaw :=
  if h : ValidCells p then lawFromCells p h else lawFromCells (fun _ _ _ => 1/4) fairDefault_valid

-- @env: S4
variable (t ξ υ η ζ δ u : ℝ)
/-- Smooth exponential divided difference through zero. -/
def dividedExp (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, Real.exp (s*t)
/-- Binary-table covariance branch with the prescribed positive square root. -/
def covarianceBranch (t ξ υ : ℝ) : ℝ :=
  let d := Real.exp t - 1
  let v := ξ*(1-ξ)*υ*(1-υ)
  let L := 1+d*(ξ*(1-υ)+(1-ξ)*υ)
  2*d*v/(L+Real.sqrt (L^2-4*d^2*v)) -- @realizes \mathfrak c(binary-table covariance branch) @realizes \xi(first scalar margin) @realizes \upsilon(second scalar margin)
/-- Smooth normalized covariance branch. -/
def normalizedBranch (t ξ υ : ℝ) : ℝ :=
  let d := Real.exp t - 1
  let v := ξ*(1-ξ)*υ*(1-υ)
  let L := 1+d*(ξ*(1-υ)+(1-ξ)*υ)
  2*dividedExp t*v/(L+Real.sqrt (L^2-4*d^2*v)) -- @realizes \mathfrak B(normalized branch)
/-- A sign as a real number. -/
def signValue (b : Bool) : ℝ := if b then 1 else -1
/-- Two auxiliary signs at a within-cell coordinate. -/
def localSignField (u : ℝ) (s : Bool × Bool) : ℝ :=
  signValue s.1 * Real.cos (Real.pi*u/2) + signValue s.2 * Real.sin (Real.pi*u/2)
/-- Expectation over the two auxiliary independent fair signs. -/
def signAverage (F : (Bool × Bool) → ℝ) : ℝ := (1/4)*∑ s, F s
/-- Normalized mixed-prior root equation. -/
def mixedEquation (η ζ u q : ℝ) : ℝ :=
  16*signAverage (fun s => normalizedBranch (32*η*ζ)
    (1/2-η*q*localSignField u s) (1/2+ζ*localSignField u s))-q
/-- Choose the local mixed root in its prescribed bracket, otherwise use one. -/
def mixedRoot (η ζ u : ℝ) : ℝ :=
  if h : ∃ q : ℝ, q ∈ Set.Ioo (3/4) (5/4) ∧ mixedEquation η ζ u q = 0 then Classical.choose h else 1
  -- @realizes \mathfrak q(local root) @realizes \eta(signed propensity amplitude) @realizes \zeta(signed outcome amplitude)
/-- Logistic risk shift. -/
def riskShift (t ξ : ℝ) : ℝ := Real.exp t*ξ/(1+(Real.exp t-1)*ξ) -- @realizes \mathsf G(logistic risk shift)
/-- Fair comparator effect. -/
def comparatorEffect (t δ : ℝ) : ℝ :=
  let p : ℝ := 2/5
  let B := 1+(Real.exp t-1)*p
  t+Real.log (1-(Real.exp t-1)*δ^2/(p*B))-
    Real.log (1+(Real.exp t-1)*δ^2/((1-p)*B)) -- @realizes \mathsf T(comparator effect) @realizes \delta(signed control-risk amplitude)
/-- Numerator of the normalized fair equation. -/
def fairNumerator (t δ ξ u : ℝ) : ℝ :=
  signAverage (fun s => riskShift t (ξ+δ*localSignField u s))-riskShift (comparatorEffect t δ) ξ
/-- Double-integral Taylor form is the removable extension, including both zero axes. -/
def fairEquation (t δ ξ u : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
    (1-v)*deriv (fun T => deriv (fun D => deriv (fun D' => fairNumerator T D' ξ u) D) (v*δ)) (s*t)
  -- @realizes \mathfrak H(removable normalized equation)
/-- Choose the local fair centering root; outside its neighbourhood use 2/5. -/
def fairRoot (t δ u : ℝ) : ℝ :=
  if h : ∃ p : ℝ, p ∈ Set.Ioo (3/10) (1/2) ∧ fairEquation t δ p u = 0 then Classical.choose h else 2/5
  -- @realizes \mathfrak p(local fair centering root)
-- @node: def:calibration-maps
/-- All seven calibration maps, with their literal defining formulas. -/
def calibrationMaps (t ξ υ η ζ δ u : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  (covarianceBranch t ξ υ, normalizedBranch t ξ υ, mixedRoot η ζ u,
    riskShift t ξ, comparatorEffect t δ, fairEquation t δ ξ u, fairRoot t δ u)
/-- Cell number, taking the left cell at the rightmost endpoint. -/
def cellIndex (k : ℕ) (x : Covariate) : ℕ := min (k-1) (⌊(k : ℝ)*(x : ℝ)⌋ : ℤ).toNat -- @realizes h(diagnostic grid width h = 1/(k : ℝ))
/-- Within-cell coordinate. -/
def cellCoord (k : ℕ) (x : Covariate) : ℝ := (k : ℝ)*(x : ℝ)-cellIndex k x -- @realizes u(within-cell coordinate k*x - cellIndex k x)
/-- Endpoint signs are extended by zero-index fallback only for k=0. -/
def endpointSign (k : ℕ) (σ : Fin (k + 1) → Bool) (j : ℕ) : ℝ :=
  signValue (σ ⟨min j k, Nat.lt_succ_of_le (min_le_right _ _)⟩)
/-- Continuous shared-endpoint sign field. -/
def signFieldZ (k : ℕ) (σ : Fin (k + 1) → Bool) (x : Covariate) : ℝ :=
  let j := cellIndex k x
  let u := cellCoord k x
  endpointSign k σ j*Real.cos (Real.pi*u/2)+endpointSign k σ (j+1)*Real.sin (Real.pi*u/2)
  -- @realizes \mathsf Z(shared-endpoint field) @realizes \sigma(finite endpoint sign vector)
/-- A four-cell table from margins and covariance. -/
def tableCell (e m c : ℝ) (a y : Bool) : ℝ :=
  if a then (if y then e*m+c else e*(1-m)-c)
  else (if y then (1-e)*m-c else (1-e)*(1-m)+c)
/-- Mixed-prior conditional cell formula. -/
def mixedCells (b : Bool) (k : ℕ) (σ : Fin (k + 1) → Bool) (η ζ : ℝ) (a y : Bool) (x : Covariate) : ℝ :=
  let Z := signFieldZ k σ x
  let u := cellCoord k x
  let q := mixedRoot η ζ u
  let e := if b then 1/2-η*q*Z else 1/2+η*q*Z
  let m := 1/2+ζ*Z
  let c := if b then covarianceBranch (32*η*ζ) e m else 0
  tableCell e m c a y
/-- Fair random and deterministic-comparator cells. -/
def fairCells (random : Bool) (k : ℕ) (σ : Fin (k + 1) → Bool) (t δ : ℝ) (a y : Bool) (x : Covariate) : ℝ :=
  let p := fairRoot t δ (cellCoord k x)
  let μ0 := if random then p+δ*signFieldZ k σ x else p
  let μ1 := riskShift (if random then t else comparatorEffect t δ) μ0
  (1/2)*(if y then (if a then μ1 else μ0) else 1-(if a then μ1 else μ0))
/-- Construct the ambient mixed law from its explicit conditional cells. -/
def mixedLaw (b : Bool) (k : ℕ) (σ : Fin (k + 1) → Bool) (η ζ : ℝ) : ObservedLaw :=
  totalCellLaw (mixedCells b k σ η ζ)
/-- Construct a fair random law from its explicit cells. -/
def fairLaw (k : ℕ) (σ : Fin (k + 1) → Bool) (t δ : ℝ) : ObservedLaw :=
  totalCellLaw (fairCells true k σ t δ)
/-- Deterministic comparator, whose cells do not depend on the supplied sign vector. -/
def fairComparator (k : ℕ) (t δ : ℝ) : ObservedLaw :=
  totalCellLaw (fairCells false k (fun _ => false) t δ)
/-- Uniform finite mixture with signs drawn once for the whole iid sample. -/
def finiteSignMixture (n k : ℕ) (laws : (Fin (k + 1) → Bool) → ObservedLaw) : Measure (Fin n → Record) :=
  (ENNReal.ofReal ((2 : ℝ)^(-(k+1 : ℕ) : ℤ))) •
    ∑ σ : Fin (k + 1) → Bool, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (laws σ).measure n
/-- Mixed original-record mixture. -/
def mixedMixture (b : Bool) (n k : ℕ) (η ζ : ℝ) : Measure (Fin n → Record) :=
  finiteSignMixture n k (fun σ => mixedLaw b k σ η ζ)
/-- Fair original-record mixture. -/
def fairMixture (n k : ℕ) (t δ : ℝ) : Measure (Fin n → Record) :=
  finiteSignMixture n k (fun σ => fairLaw k σ t δ)
-- @node: def:continuous-calibrated-priors
/-- Both mixed and fair prior experiments contain exactly n original records. -/
def calibratedPriors (n k : ℕ) (η ζ t δ : ℝ) :
    Measure (Fin n → Record) × Measure (Fin n → Record) × Measure (Fin n → Record) :=
  (mixedMixture false n k η ζ, mixedMixture true n k η ζ, fairMixture n k t δ)

/-- Full data contain two binary potential outcomes and a treatment. -/
abbrev FullRecord := (Covariate × (Bool × Bool)) × Bool
/-- Potential control outcome. -/
def potentialControl (o : FullRecord) : ℝ := if o.1.2.1 then 1 else 0 -- @realizes Y^0(binary control potential outcome)
/-- Potential treated outcome. -/
def potentialTreated (o : FullRecord) : ℝ := if o.1.2.2 then 1 else 0 -- @realizes Y^1(binary treated potential outcome)
/-- Observation by literal consistency. -/
def observedMap (o : FullRecord) : Record := (o.1.1, o.2, if o.2 then o.1.2.2 else o.1.2.1)
/-- Binary law at a success probability. -/
def bernoulliLaw (p : ℝ) : Measure Bool :=
  ENNReal.ofReal (1-p) • Measure.dirac false + ENNReal.ofReal p • Measure.dirac true
/-- A coupling is admissible exactly when both conditional margins are the law's arm risks. -/
def AdmissibleCoupling (P : ObservedLaw) (Γ : Kernel Covariate (Bool × Bool)) : Prop :=
  IsMarkovKernel Γ ∧ ∀ x,
    Measure.map Prod.fst (Γ x) = bernoulliLaw (armRisk P false x) ∧
    Measure.map Prod.snd (Γ x) = bernoulliLaw (armRisk P true x)
  -- @realizes \Gamma(measurable coupling; exact risk margins)
/-- The treatment probability is strictly interior by cell normalization. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: propensity_interior
lemma propensity_interior (P : ObservedLaw) (x : Covariate) :
    0 < propensity P x ∧ propensity P x < 1 := by
  have h := P.normalized_cells x
  simp only [Fintype.sum_bool] at h
  have h00 := (P.interior_cells false false x).1
  have h01 := (P.interior_cells false true x).1
  have h10 := (P.interior_cells true false x).1
  have h11 := (P.interior_cells true true x).1
  unfold propensity
  constructor <;> linarith

/-- [An interior Bernoulli parameter defines a probability measure.](goal) Under [the stated assumptions](hyp:hp,hp1). -/
-- @node: bernoulliLaw_probability
lemma bernoulliLaw_probability (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliLaw p) := by
  apply (isProbabilityMeasure_iff).2
  simp only [bernoulliLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) hp]
  simp

/-- [Conditional treatment kernel is measurable. [the documented result](goal) -/
-- @node: treatmentKernel_measurable
@[fun_prop]
lemma treatmentKernel_measurable (P : ObservedLaw) :
  Measurable (fun z : Covariate × (Bool × Bool) => bernoulliLaw (propensity P z.1)) := by
  unfold bernoulliLaw propensity
  apply Measurable.add
  · apply Measurable.smul_measure
    exact ENNReal.measurable_ofReal.comp
      ((measurable_const.sub ((P.continuous_cells true false).measurable.add
        (P.continuous_cells true true).measurable)).comp measurable_fst)
  · apply Measurable.smul_measure
    exact ENNReal.measurable_ofReal.comp
      (((P.continuous_cells true false).measurable.add
        (P.continuous_cells true true).measurable).comp measurable_fst)
/-- Treatment is drawn independently of the potential outcomes given X. -/
def treatmentKernel (P : ObservedLaw) : Kernel (Covariate × (Bool × Bool)) Bool where
  toFun := fun z => bernoulliLaw (propensity P z.1)
  measurable' := treatmentKernel_measurable P
/-- The conditional factorization defining exchangeability. -/
def fullConditionalLaw (P : ObservedLaw) (Γ : Kernel Covariate (Bool × Bool)) (x : Covariate) : Measure ((Bool × Bool) × Bool) :=
  (Γ x).prod (bernoulliLaw (propensity P x))
/-- The conditional product is the fibre of the sequential kernel composition. Under the stated assumptions. [The stated hypotheses](hyp:hΓ) hold, and [the stated conclusion follows](goal). -/
-- @node: fullConditionalLaw_eq_compProd
lemma fullConditionalLaw_eq_compProd (P : ObservedLaw)
    (Γ : Kernel Covariate (Bool × Bool)) (hΓ : AdmissibleCoupling P Γ)
    (x : Covariate) :
    fullConditionalLaw P Γ x = (Γ ⊗ₖ treatmentKernel P) x := by
  let : IsMarkovKernel Γ := hΓ.1
  let : IsMarkovKernel (treatmentKernel P) := ⟨fun z =>
    bernoulliLaw_probability _ (propensity_interior P z.1).1.le
      (propensity_interior P z.1).2.le⟩
  ext s hs
  rw [Kernel.compProd_apply hs, fullConditionalLaw, Measure.prod_apply hs]
  rfl

/-- [The full conditional laws of an admissible coupling form a measurable kernel. [the documented result](goal) Under [the stated assumptions](hyp:hΓ). -/
@[fun_prop]
-- @node: fullConditionalLaw_measurable
lemma fullConditionalLaw_measurable (P : ObservedLaw)
    (Γ : Kernel Covariate (Bool × Bool)) (hΓ : AdmissibleCoupling P Γ) :
    Measurable (fullConditionalLaw P Γ) := by
  have heq : fullConditionalLaw P Γ = (Γ ⊗ₖ treatmentKernel P) := by
    funext x
    exact fullConditionalLaw_eq_compProd P Γ hΓ x
  rw [heq]
  exact Kernel.measurable _
-- @node: def:causal-extension
/-- X uniform, the supplied potential-outcome coupling, then independent Bernoulli treatment. -/
def causalExtension (P : ObservedLaw) (Γ : Kernel Covariate (Bool × Bool)) : Measure FullRecord :=
  (uniformLaw.compProd Γ).compProd (treatmentKernel P) -- @realizes \widetilde P(full-data kernel-composition law)
end CausalSmith.Stat.LogoddsLowsmoothFrontier
