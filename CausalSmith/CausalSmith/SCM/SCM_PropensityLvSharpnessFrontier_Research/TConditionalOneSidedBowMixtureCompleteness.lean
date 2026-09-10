import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.ConditionalConstruction
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.CapBridge

/-! # Conditional one-sided bow-mixture completeness -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set

/-- On one common covariate-conull set, globally realizable conditional bow
kernels are exactly residual-kernel mixtures and exactly the fiberwise cap class.  For the specified model objects, [the stated conditions](hyp:hOverlap,hP), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:conditional-one-sided-bow-mixture-completeness
theorem condBowCompatibleOneSided_eq_condMixtureClassOneSided
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [PolishSpace X]
    [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] [PolishSpace Y]
    (kappa : ℝ) (muX : Measure X) [IsProbabilityMeasure muX]
    (e : Bool → X → ℝ) (P : Bool → Kernel X Y)
    (hOverlap : CondOverlap kappa e) (hP : ∀ a, IsMarkovKernel (P a)) :
    condBowCompatibleOneSidedSet kappa muX e P =
      condMixtureClassOneSidedSet kappa muX e P ∧
    condMixtureClassOneSidedSet kappa muX e P = condCapSet muX e P := by
  have heIoo (x : X) (a : Bool) : e a x ∈ Set.Ioo 0 1 := by
    have hr := hOverlap.2.2.2 x a
    constructor <;> linarith [hOverlap.1, hr.1, hr.2]
  have hMixCap : condMixtureClassOneSidedSet kappa muX e P = condCapSet muX e P := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨R, hR, S, hS, hSc, hrep⟩ := hQ.representation
      refine ⟨hQ.candidate_markov, S, hS, hSc, ?_⟩
      intro x hx a
      have hle : ENNReal.ofReal (e a x) • P a x ≤ Q a x := by
        rw [hrep x hx a]
        exact Measure.le_add_right (le_refl _)
      have hAC : P a x ≪ Q a x :=
        (Measure.absolutelyContinuous_smul
          (ENNReal.ofReal_ne_zero_iff.mpr (heIoo x a).1)).trans
          (Measure.absolutelyContinuous_of_le hle)
      letI := hP a
      letI := hQ.candidate_markov a
      exact ⟨hle, hAC, (cap_iff_measure_le (e a x) (P a x) (Q a x)
        ⟨(heIoo x a).1, (heIoo x a).2⟩ hAC).2 hle⟩
    · intro hQ
      obtain ⟨S, hS, hSc, hcap⟩ := hQ.2
      let R : Bool → Kernel X Y := fun a =>
        conditionalResidualKernel S hS (e a) (hOverlap.2.2.1.1 a) (P a) (Q a)
          (hP a) (hQ.1 a) (fun x hx => (hcap x hx a).1)
      refine CondMixtureClassOneSided.mk hOverlap inferInstance hP hQ.1
        ⟨R, ?_, S, hS, hSc, ?_⟩
      · intro a
        exact conditionalResidualKernel_markov S hS (e a) (hOverlap.2.2.1.1 a)
          (P a) (Q a) (fun x hx => (hcap x hx a).1) (fun x => heIoo x a)
          (hP a) (hQ.1 a)
      · intro x hx a
        exact conditionalResidualKernel_mixture S hS (e a) (hOverlap.2.2.1.1 a)
          (P a) (Q a) (fun x hx => (hcap x hx a).1) (hP a) (hQ.1 a)
          (fun x => heIoo x a) x hx
  refine ⟨?_, hMixCap⟩
  ext Q
  constructor
  · intro hQ
    rw [hMixCap]
    obtain ⟨_, _, hCompat⟩ := hQ
    obtain ⟨w, hArch, hCons, hwMu, S, hS, hSc, hagree⟩ := hCompat.realization
    have hSin : ∀ᵐ x ∂muX, x ∈ S := mem_ae_iff.mpr hSc
    have hCaps : ∀ a, ∀ᵐ x ∂muX,
        ENNReal.ofReal (e a x) • P a x ≤ Q a x := by
      intro a
      have heq : e a =ᵐ[w.covariateLaw] w.condProp a := by
        rw [hwMu]
        filter_upwards [hSin] with x hx
        exact (hagree x hx a).1.symm
      have hc := conditional_measureCap_ae w hArch hCons a (e a)
        (hOverlap.2.2.1.1 a) heq
      rw [hwMu] at hc
      filter_upwards [hSin, hc] with x hxS hxcap
      rw [(hagree x hxS a).2.1, (hagree x hxS a).2.2] at hxcap
      exact hxcap
    have hCapsAll : ∀ᵐ x ∂muX, ∀ a,
        ENNReal.ofReal (e a x) • P a x ≤ Q a x := by
      rw [ae_all_iff]
      exact hCaps
    have hbad : muX {x | ¬ ∀ a,
        ENNReal.ofReal (e a x) • P a x ≤ Q a x} = 0 := ae_iff.mp hCapsAll
    obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hbad
    refine ⟨hCompat.candidate_markov, Nᶜ, hNm.compl, by simpa, ?_⟩
    intro x hx a
    have hle : ENNReal.ofReal (e a x) • P a x ≤ Q a x := by
      by_contra hn
      apply hx
      apply hsub
      intro hall
      exact hn (hall a)
    have hAC : P a x ≪ Q a x :=
      (Measure.absolutelyContinuous_smul
        (ENNReal.ofReal_ne_zero_iff.mpr (heIoo x a).1)).trans
        (Measure.absolutelyContinuous_of_le hle)
    letI := hP a
    letI := hCompat.candidate_markov a
    exact ⟨hle, hAC, (cap_iff_measure_le (e a x) (P a x) (Q a x)
      ⟨(heIoo x a).1, (heIoo x a).2⟩ hAC).2 hle⟩
  · intro hQ
    obtain ⟨R, hR, S, hS, hSc, hrep⟩ := hQ.representation
    let w := conditionalCanonicalBowWitness muX e P R hOverlap.2.2.1 hP hR
    have hwArch : CondBowArchitecture w :=
      conditionalCanonicalBowWitness_architecture muX e P R hOverlap.2.2.1 hP hR
    have hwCons : CondConsistency w :=
      conditionalCanonicalBowWitness_consistency muX e P R hOverlap.2.2.1 hP hR
    refine ⟨inferInstance, hOverlap, {
      realization := ⟨w, hwArch, hwCons, rfl, S, hS, hSc, ?_⟩
      architecture := ⟨w, hwArch⟩
      overlap := hOverlap
      consistency := ⟨w, hwCons⟩
      observed_markov := hP
      candidate_markov := hQ.candidate_markov }⟩
    intro x hx a
    refine ⟨rfl, rfl, ?_⟩
    rw [show w.condIntervLaw a x =
        conditionalCanonicalMixtureKernel e hOverlap.2.2.1.1 P R a x by rfl,
      conditionalCanonicalMixtureKernel_apply]
    have hcomp : e (!a) x = 1 - e a x := by
      cases a
      · simp only [Bool.not_false]
        linarith [hOverlap.2.2.1.2.2 x]
      · simp only [Bool.not_true]
        linarith [hOverlap.2.2.1.2.2 x]
    rw [hcomp]
    exact (hrep x hx a).symm

end CausalSmith.SCM.PropensityLvSharpnessFrontier
