module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Basic
public import Causalean.Mathlib.Analysis.Duality.MomentPrior
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Weighted scalar approximation and constrained moment priors
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators ENNReal

-- @env: S4
variable (K : ℕ) (M ε z w : ℝ)
  -- @realizes \(K\)(degree) @realizes \(M\)(endpoint)
  -- @realizes \(z\)(first intensity) @realizes \(w\)(second intensity)
variable (hK : 2 ≤ K) -- @realizes \(K\)(degree at least two)
variable (hMlo : 2 ≤ M) (hMhi : M ≤ (K : ℝ) ^ 2)
  -- @realizes \(M\)(endpoint in [2, K²])
variable (hz : z ∈ Set.Icc 0 M) (hw : w ∈ Set.Icc 0 M)
  -- @realizes \(z\)(in [0, M]) @realizes \(w\)(in [0, M])

/-- For [the displayed parameters](hyp:z), [phiEpsFormula](goal) is the object specified by this definition. -/
noncomputable def phiEpsFormula (ε z : ℝ) : ℝ :=
  ((1 - ε) + ε * z) * max (z - 1) 0 / (1 + z)

/-- For [the displayed parameters](hyp:M,z,h,hz), [phiEps](goal) is the object specified by this definition. -/
noncomputable def phiEps (ε M z : ℝ) (_hε : 0 ≤ ε ∧ ε ≤ 1 / 2)
    (_hz : z ∈ Set.Icc 0 M) : ℝ :=
  phiEpsFormula ε z
  -- @realizes \(\phi_\epsilon(z)\)(weighted positive part; 0≤ε≤1/2 and z∈[0,M])


-- @node: def:weighted-error
/-- For [the displayed parameters](hyp:K,M), [weightedApproxError](goal) is the object specified by this definition. -/
noncomputable def weightedApproxError (K : ℕ) (M ε : ℝ) : ℝ :=
  sInf {e : ℝ | ∃ p : Polynomial ℝ, p.natDegree ≤ K ∧
    e = sSup ((fun z : ℝ => |phiEpsFormula ε z - p.eval z| / (1 + z)) '' Set.Icc 0 M)}
  -- @realizes \(\mathcal E_{K,M,\epsilon}^{w}\)(best weighted error)

/-- For [the displayed parameters](hyp:K,M), [ConstrainedPriorPair](goal) is the object specified by this definition. -/
structure ConstrainedPriorPair (K : ℕ) (M : ℝ) where
  ν₀ : Measure ℝ
  ν₁ : Measure ℝ
  prob₀ : IsProbabilityMeasure ν₀
  prob₁ : IsProbabilityMeasure ν₁
  supp₀ : ν₀ (Set.Icc 0 M)ᶜ = 0
  supp₁ : ν₁ (Set.Icc 0 M)ᶜ = 0
  mean₀ : (∫ z, z ∂ν₀) = 1
  mean₁ : (∫ z, z ∂ν₁) = 1
  moments : ∀ j : ℕ, j ≤ K →
    (∫ z, z ^ j ∂ν₀) = (∫ z, z ^ j ∂ν₁)

/-- For [the displayed parameters](hyp:p,m), [CommonAtomDomain](goal) is the object specified by this definition. -/
def CommonAtomDomain (σp σm : Measure ℝ) : Prop :=
  IsFiniteMeasure σp ∧ IsFiniteMeasure σm ∧
    Integrable (fun z : ℝ => z) σp ∧ Integrable (fun z : ℝ => z) σm ∧
    σp Set.univ < 1

-- @node: def:weighted-handle
/-- For [the displayed parameters](hyp:p,m,hdom), [commonAtomCompletion](goal) is the object specified by this definition. -/
noncomputable def commonAtomCompletion (σp σm : Measure ℝ)
    (_hdom : CommonAtomDomain σp σm) : Measure ℝ × Measure ℝ :=
  let t := (σp Set.univ).toReal
  let u := ∫ z, z ∂σp
  let z₀ := (1 - u) / (1 - t)
  (σm + ENNReal.ofReal (1 - t) • Measure.dirac z₀,
   σp + ENNReal.ofReal (1 - t) • Measure.dirac z₀)
  -- @realizes \(\mathscr H^{w}\)(common-atom completion)

/-- For [the displayed parameters](hyp:K,M), [constrainedPriorSeparationFormula](goal) is the object specified by this definition. -/
noncomputable def constrainedPriorSeparationFormula (K : ℕ) (M ε : ℝ) : ℝ :=
  sSup (Set.range fun p : ConstrainedPriorPair K M =>
    |(∫ z, phiEpsFormula ε z ∂p.ν₁) - (∫ z, phiEpsFormula ε z ∂p.ν₀)|)


-- @node: def:constrained-prior-separation
/-- For [the displayed parameters](hyp:K,M,hK,hM,hMhi,h,hi), [constrainedPriorSeparation](goal) is the object specified by this definition. -/
noncomputable def constrainedPriorSeparation (K : ℕ) (M ε : ℝ)
    (_hK : 2 ≤ K) (_hM : 2 ≤ M) (_hMhi : M ≤ (K : ℝ) ^ 2)
    (_hε : 0 ≤ ε) (_hεhi : ε ≤ 1 / 2) : ℝ :=
  constrainedPriorSeparationFormula K M ε
  -- @realizes \(\Delta_{K,M,\epsilon}\)(supremal prior gap; K≥2, 2≤M≤K², 0≤ε≤1/2)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
