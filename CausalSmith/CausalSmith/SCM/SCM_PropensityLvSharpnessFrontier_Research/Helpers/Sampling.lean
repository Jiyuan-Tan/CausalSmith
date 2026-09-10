import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.CdfMaps
import Causalean.Stat.Sample
import Causalean.Stat.Quantile.EmpiricalCDF

/-! # Fixed-stratum empirical estimators and confidence bands -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open Set
open scoped BigOperators

/-- A realized sample of treatment/outcome pairs. -/
abbrev ObservedSample (n : ℕ) := Fin n → Bool × ℝ

/-- A simultaneous endpoint band computed from an `n`-observation sample. -/
abbrev FiniteSampleBand :=
  (n : ℕ) → ObservedSample n → ℝ → Set (ℝ × ℝ)

/-- Read the `i`th coordinate of a finite sample, using a harmless value outside
the first `n` indices. -/
def sampleCoordinate (n i : ℕ) (S : ObservedSample n) : Bool × ℝ :=
  if h : i < n then S ⟨i, h⟩ else (false, 0)

/-- Number of observations in an arm. -/
def armCount {n : ℕ} (S : ObservedSample n) (a : Bool) : ℕ :=
  ∑ i, if (S i).1 = a then 1 else 0

/-- Empirical arm propensity. -/
noncomputable def empiricalArmPropensity {n : ℕ}
    (S : ObservedSample n) (a : Bool) : ℝ :=
  (armCount S a : ℝ) / n
  -- @realizes \widehat e_n(empirical arm fraction)

/-- Arm-conditional empirical CDF, set to zero when the arm count vanishes. -/
noncomputable def empiricalArmCDF {n : ℕ}
    (S : ObservedSample n) (a : Bool) (y : ℝ) : ℝ :=
  if armCount S a = 0 then 0 else
    (∑ i, if (S i).1 = a ∧ (S i).2 ≤ y then (1 : ℝ) else 0) / armCount S a
  -- @realizes \widehat e_n,\widehat F_{P,n}(arm-conditional empirical CDF component)

/-- The coordinatewise rectangular hull of a set of endpoint pairs. -/
noncomputable def rectangularHull (C : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  Set.Icc (sInf (Prod.fst '' C)) (sSup (Prod.fst '' C)) ×ˢ
    Set.Icc (sInf (Prod.snd '' C)) (sSup (Prod.snd '' C))

/-- The finite-sample simultaneous endpoint band. -/
-- @node: def:honest-band
noncomputable def honestBand {Omega : Type*}
    (Z : ℕ → Omega → Bool × ℝ) (a : Bool) (n : ℕ)
    (alpha : ℝ) (omega : Omega) (y : ℝ) : Set (ℝ × ℝ) :=
  let S : ObservedSample n := fun i => Z i omega
  if armCount S a = 0 then Set.Icc 0 1 ×ˢ Set.Icc 0 1 else
    let deltaE := Real.sqrt (Real.log (4 / alpha) / (2 * n))
    let deltaF := Real.sqrt (Real.log (4 / alpha) / (2 * armCount S a))
    let Ie : Set (Set.Icc (0 : ℝ) 1) :=
      {eta | eta.1 ∈ Set.Icc (empiricalArmPropensity S a - deltaE)
        (empiricalArmPropensity S a + deltaE)}
    let IF : Set (Set.Icc (0 : ℝ) 1) :=
      {p | p.1 ∈ Set.Icc (empiricalArmCDF S a y - deltaF)
        (empiricalArmCDF S a y + deltaF)}
    rectangularHull ((fun ep => cdfEndpoints ep.1 ep.2) '' (Ie ×ˢ IF))
  -- @realizes \widehat{\mathcal C}_{n,\alpha}(rectangular hull propagated through endpoints)
  -- @realizes \alpha(miscoverage parameter)

/-- The honest band as a function of the finite sample it actually uses. -/
noncomputable def honestFiniteSampleBand (a : Bool) (n : ℕ) (alpha : ℝ)
    (S : ObservedSample n) (y : ℝ) : Set (ℝ × ℝ) :=
  honestBand (sampleCoordinate n) a n alpha S y

/-- A band is rectangular at every sample size, sample, and threshold. -/
def IsRectangularBand (band : FiniteSampleBand) : Prop :=
  ∀ n S y, ∃ lL uL lU uU : ℝ,
    band n S y = Set.Icc lL uL ×ˢ Set.Icc lU uU

/-- Rectangularity of the bands emitted by a directional-inference procedure. -/
def DirectionalHandle (band : FiniteSampleBand) : Prop :=
  IsRectangularBand band
  -- @realizes \mathsf H_{\mathrm{dir}}(handle produces rectangular simultaneous bands)

/-- Descriptive, nonasserting recipe attached to the directional handle. -/
-- @node: def:directional-handle
def directionalHandleRecipe : String :=
  "Linearize the joint pre-endpoint empirical process (eHat,FHat); apply the Hadamard \
  directional derivative of (e,F) ↦ (L_e ∘ F,U_e ∘ F); estimate it with a \
  Fang--Santos multiplier or numerical-delta bootstrap; then take the supremum over \
  thresholds and arms."

end CausalSmith.SCM.PropensityLvSharpnessFrontier
