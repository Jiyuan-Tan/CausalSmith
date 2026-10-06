module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.CloneClass
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.UnitOverlapUpper
public import Causalean.Stat.Minimax.LeCam
public import Causalean.Stat.Minimax.ChiSquared

/-! # The parametric stationary-law-invariance submodel at overlap radius one. -/

public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory

-- @node: invariance_stationaryOverlap_one
/-- Equal stationary laws satisfy the radius-one overlap condition. -/
lemma invariance_stationaryOverlap_one {T nX nH k : Nat} {t0 zeta : ℝ}
    {M : PomdpModel T nX nH k}
    (hM : InvarianceClass t0 zeta M) : FixedOverlapClass t0 zeta 1 M := by
  refine ⟨hM.1, ?_⟩
  refine ⟨le_refl 1, ?_⟩
  intro s
  rw [hM.2]
  simp

-- @node: stationaryOverlap_one_eq
/-- Equal total mass turns pointwise radius-one overlap into equality of laws. -/
lemma stationaryOverlap_one_eq {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (hOverlap : StationaryOverlap 1 M)
    (hBehavior : ProbabilityVector (stationaryLaw (policyKernel M M.b)))
    (hTarget : ProbabilityVector (stationaryLaw (policyKernel M M.e))) :
    stationaryLaw (policyKernel M M.e) = stationaryLaw (policyKernel M M.b) := by
  funext s
  have hle : ∀ s ∈ (Finset.univ : Finset (JointState nX nH)),
      stationaryLaw (policyKernel M M.e) s ≤ stationaryLaw (policyKernel M M.b) s := by
    intro s _
    simpa using hOverlap.2 s
  have hsum : (∑ s, stationaryLaw (policyKernel M M.e) s) =
      ∑ s, stationaryLaw (policyKernel M M.b) s := by
    rw [hTarget.2, hBehavior.2]
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum s (Finset.mem_univ s)

-- @node: fixedOverlap_one_iff_invariance
/-- Radius-one stationary overlap is equivalent to equality of the stationary laws. -/
lemma fixedOverlap_one_iff_invariance {T nX nH k : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k)
    (hTarget : ProbabilityVector (stationaryLaw (policyKernel M M.e))) :
    FixedOverlapClass t0 zeta 1 M ↔ InvarianceClass t0 zeta M := by
  constructor
  · intro hM
    refine ⟨hM.1, ?_⟩
    have hb : ProbabilityVector (stationaryLaw (policyKernel M M.b)) :=
      hM.1.start.1.1
    exact stationaryOverlap_one_eq M hM.2 hb hTarget
  · exact invariance_stationaryOverlap_one

-- @node: prop:unit-overlap-sanity
/-- The radius-one class equals the stationary-law-invariance class. The immediate
importance-weighted estimator and nested minimax risk have uniform parametric rates. -/
theorem unit_overlap_sanity {t0 zeta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    (∀ (T nX nH k : Nat) (M : PomdpModel T nX nH k),
      FixedOverlapClass t0 zeta 1 M ↔ InvarianceClass t0 zeta M) ∧
    (∀ (T : Nat), 1 ≤ T → ∀ (eta : ℝ), eta ∈ Set.Icc (0 : ℝ) 1 →
      (∀ i : HWIndex T t0 zeta, InvarianceClass t0 zeta i.raw →
        Causalean.Stat.sqRisk (auditedLaw eta i.raw)
          (iwEstimator i.raw.b i.raw.e)
          (targetValue i.raw) ≤
          (policyFactor zeta + 4 / (1 - mixingAlpha t0)) / (T : ℝ)) ∧
      (3 / (512 * (T : ℝ)) ≤ invarianceMinimaxRisk T t0 zeta eta ∧
        invarianceMinimaxRisk T t0 zeta eta ≤
          (policyFactor zeta + 4 / (1 - mixingAlpha t0)) / (T : ℝ))) := by
  constructor
  · intro T nX nH k M
    constructor
    · intro hM
      have hTarget : ProbabilityVector (stationaryLaw (policyKernel M M.e)) :=
        (target_stationary_law_of_class M ht0 hM.1).1
      exact (fixedOverlap_one_iff_invariance M hTarget).mp hM
    · exact invariance_stationaryOverlap_one
  · intro T hT eta heta
    constructor
    · intro i hi
      exact audited_iw_invariance_risk_le hT i.raw hi i.nX_pos i.nH_pos eta heta
    · constructor
      · exact invarianceMinimaxRisk_lower_parametric hT ht0 hzeta heta
      · exact invarianceMinimaxRisk_upper_iw hT ht0 hzeta heta

end CausalSmith.Stat.PomdpStateauditMinimax
