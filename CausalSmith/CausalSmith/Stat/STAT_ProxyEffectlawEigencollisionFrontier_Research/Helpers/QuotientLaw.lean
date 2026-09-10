import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TObservedVMWMarginInclusion

/-!
Validity and bundling of the quotient latent-effect law, after the observed-margin
consequences needed for its support bound are available.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set

-- @node: quotientLawRaw_valid
lemma quotientLawRaw_valid {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    AtomicLaw.Valid (quotientLawRaw P (effectRadius dz L sigma0)) := by
  rcases hM.coreDomain with
    ⟨hk, hkx, hkz, hL, hpi, hpiMax, hsigma, hsigmaMax⟩
  refine ⟨fun u => measureReal_nonneg, ?_, ?_⟩
  · change (∑ u : Fin k, latentMass P u) = 1
    rw [show (∑ u : Fin k, latentMass P u) = P.real Set.univ by
      rw [show Set.univ = ⋃ u : Fin k, latentClass (dx := dx) (dz := dz) u by
        ext w
        simp [latentClass]]
      symm
      apply measureReal_iUnion_fintype
        (h' := fun u => measure_ne_top P (latentClass u))
      · intro u v huv
        unfold Function.onFun
        rw [Set.disjoint_left]
        intro w hwu hwv
        exact huv (hwu.symm.trans hwv)
      · exact fun u => measurableSet_latentClass u]
    simp
  · intro u
    have hu : |latentEffect P u| ≤ effectRadius dz L sigma0 :=
      latentEffect_abs_le_of_model P hk hkx hkz hL hpi hsigma hM u
    exact (abs_le.mp hu)

/-- Quotient latent-effect probability law, supported at the derived radius; its represented
measure automatically aggregates coincident effect values.
    @realizes \(\nu_P\)(valid probability law at latent effects) -/
-- @node: def:quotient-law
noncomputable def quotientLaw {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    AtomicLaw.LawModulo k (effectRadius dz L sigma0) :=
  AtomicLaw.LawModulo.ofProbabilityLaw
    ⟨quotientLawRaw P (effectRadius dz L sigma0), quotientLawRaw_valid P hM⟩

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
