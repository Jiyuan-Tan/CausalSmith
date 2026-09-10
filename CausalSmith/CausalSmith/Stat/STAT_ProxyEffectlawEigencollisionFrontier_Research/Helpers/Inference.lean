import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.LatticeEstimator

/-! The theoretical and computable confidence sets and the cluster-adaptive report. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators ENNReal
open Set

/-- Both confidence-set constructions at a fixed sample. -/
structure ConfidenceSetData (k dx dz n : ℕ) (radius : ℝ) where
  Ctheory : Set (AtomicLaw.LawModulo k radius)
    -- @realizes \(\mathcal C_{n,\alpha}\)(theoretical image set)
  Calg : Set (AtomicLaw.LawModulo k radius)
    -- @realizes \(\mathcal C^{\mathrm{alg}}_{n,\alpha}\)(outer W1 set)
  pi0 : ℝ
  mStar : ℝ -- @realizes \(m_\star\)(pi0)
  mStar_eq_pi0 : mStar = pi0 -- @realizes \(m_\star\)(mStar = pi0)
  mStar_pos : 0 < mStar
  mStar_max : mStar ≤ 1 / (2 * k : ℝ)
  Ralpha : ℝ -- @realizes \(R_{n,\alpha}\)(lattice confidence radius)
  Ralpha_pos : 0 < Ralpha

/-- The retained sharp summary-inversion image, independent of the computable outer set. -/
noncomputable def theoreticalConfidenceSet {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (R : SummaryRepairData k dx dz n L pi0 sigma0)
    (sample : Fin n → Obs dx dz) (alpha C0 : ℝ) :
    Set (AtomicLaw.LawModulo k (effectRadius dz L sigma0)) :=
  let r := summaryRadius n alpha C0 L
  if summaryClosure k dx dz L pi0 sigma0 = ∅ then
    {AtomicLaw.LawModulo.deltaZeroLaw R.k_pos R.radius_nonneg}
  else {ν | ∃ q : {q // q ∈ summaryClosure k dx dz L pi0 sigma0},
    dS q.1 (R.Pi (empSummary sample)) ≤ 2 * r ∧ ν = R.Fbar q}

lemma confidenceRadius_pos {n : ℕ} {alpha C0 L Clat : ℝ}
    (hn : 0 < n) (halpha : 0 < alpha) (halphaHalf : alpha < 1 / 2)
    (hC0 : 1 ≤ C0) (hL : 1 ≤ L) (hClat : 0 < Clat) :
    0 < Clat * (summaryRadius n alpha C0 L + (Real.sqrt n)⁻¹) := by
  positivity [summaryRadius_pos n alpha C0 L hn halpha halphaHalf hC0 hL]

/-- The original summary-inversion image and the separate computable Wasserstein outer set.
    @realizes \(\xi\)(candidate law in Calg) -/
-- @node: def:wasserstein-confidence-set
noncomputable def confidenceSets {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (R : SummaryRepairData k dx dz n L pi0 sigma0)
    (A : LatticeEstimator k dx dz n (effectRadius dz L sigma0))
    (_hA : IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A)
    (sample : Fin n → Obs dx dz) (alpha C0 Clat : ℝ)
    (hn : 0 < n) (halpha : 0 < alpha) (halphaHalf : alpha < 1 / 2)
    (hC0 : 1 ≤ C0) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hpiMax : pi0 ≤ 1 / (2 * k : ℝ)) (hClat : 0 < Clat) :
    ConfidenceSetData k dx dz n (effectRadius dz L sigma0) :=
  let r := summaryRadius n alpha C0 L
  let center := latticeLaw A sample
  let Rα := Clat * (r + (Real.sqrt n)⁻¹)
  { Ctheory := theoreticalConfidenceSet R sample alpha C0
    Calg := {ν | AtomicLaw.AtomFloor pi0 ν.representative.1 ∧
      AtomicLaw.LawModulo.wass1 ν center ≤ Rα}
    pi0 := pi0
    mStar := pi0
    mStar_eq_pi0 := rfl
    mStar_pos := hpi
    mStar_max := hpiMax
    Ralpha := Rα
    Ralpha_pos := confidenceRadius_pos hn halpha halphaHalf hC0 hL hClat }

/-- The finite transport-plan constraint representation of the computable outer set. -/
def CalgHasConstrainedRepresentation {k dx dz n : ℕ} {radius : ℝ}
    (CS : ConfidenceSetData k dx dz n radius)
    (center : AtomicLaw.LawModulo k radius) : Prop :=
  ∀ ν, ν ∈ CS.Calg ↔ AtomicLaw.AtomFloor CS.mStar ν.representative.1 ∧
    ∃ γ : AtomicLaw.TransportPlan ν.representative.1 center.representative.1,
      AtomicLaw.transportCost γ ≤ CS.Ralpha

-- @node: confidenceSets_constrainedRepresentation
lemma confidenceSets_constrainedRepresentation {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (R : SummaryRepairData k dx dz n L pi0 sigma0)
    (A : LatticeEstimator k dx dz n (effectRadius dz L sigma0))
    (hA : IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A)
    (sample : Fin n → Obs dx dz) (alpha C0 Clat : ℝ)
    (hn : 0 < n) (halpha : 0 < alpha) (halphaHalf : alpha < 1 / 2)
    (hC0 : 1 ≤ C0) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hpiMax : pi0 ≤ 1 / (2 * k : ℝ)) (hClat : 0 < Clat) :
    CalgHasConstrainedRepresentation
      (confidenceSets R A hA sample alpha C0 Clat hn halpha halphaHalf hC0 hL hpi hpiMax hClat)
      (latticeLaw A sample) := by
  intro ν
  simp only [confidenceSets, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hfloor, hwass⟩
    obtain ⟨γ, hγ⟩ := AtomicLaw.wass1_optimal_plan
      ν.representative.2 (latticeLaw A sample).representative.2
    exact ⟨hfloor, γ, hγ.symm ▸ hwass⟩
  · rintro ⟨hfloor, γ, hγ⟩
    exact ⟨hfloor, le_trans (AtomicLaw.wass1_le_of_plan γ) hγ⟩

def linked {k : ℕ} {radius rho : ℝ} (ν : AtomicLaw k radius) (x y : ℝ) : Prop :=
  x ∈ ν.support ∧ y ∈ ν.support ∧ |x - y| ≤ 4 * rho

noncomputable def componentOf {k : ℕ} {radius rho : ℝ}
    (ν : AtomicLaw k radius) (x : ℝ) : Finset ℝ := by
  classical
  exact ν.support.filter fun y => Relation.ReflTransGen (linked (rho := rho) ν) x y

noncomputable def components {k : ℕ} {radius rho : ℝ}
    (ν : AtomicLaw k radius) : Finset (Finset ℝ) :=
  ν.support.image (componentOf (rho := rho) ν)

noncomputable def clusterMass {k : ℕ} {radius : ℝ} (rho : ℝ)
    (ν : AtomicLaw k radius) (C : Finset ℝ) : ℝ :=
  ∑ i, if AtomicLaw.distToFinset (ν.atom i) C ≤ rho then ν.weight i else 0

-- @node: associatedSupport
noncomputable def associatedSupport {k : ℕ} {radius rho : ℝ}
    (ν : AtomicLaw k radius) (C : Finset ℝ) : Finset ℝ :=
  ν.support.filter fun x => AtomicLaw.distToFinset x C ≤ rho

-- @node: clusterExternalGap
noncomputable def clusterExternalGap {k : ℕ} {radius rho : ℝ}
    (ν : AtomicLaw k radius) (C : Finset ℝ) : EReal :=
  if (ν.support \ associatedSupport (rho := rho) ν C).Nonempty then
    sInf {d : EReal | ∃ x ∈ associatedSupport (rho := rho) ν C,
      ∃ y ∈ ν.support, y ∉ associatedSupport (rho := rho) ν C ∧ d = |x - y|}
  else ⊤

/-- Feasible objective values in the ordered-support/weight/transport representation of one
cluster-mass endpoint. -/
def ClusterEndpointFeasible {k dx dz n : ℕ} {radius : ℝ}
    (CS : ConfidenceSetData k dx dz n radius) (center : AtomicLaw.LawModulo k radius)
    (rho : ℝ) (C : Finset ℝ) (m : ℝ) : Prop :=
  ∃ ν : AtomicLaw.LawModulo k radius,
    AtomicLaw.AtomFloor CS.mStar ν.representative.1 ∧
    (∃ γ : AtomicLaw.TransportPlan ν.representative.1 center.representative.1,
      AtomicLaw.transportCost γ ≤ CS.Ralpha) ∧
    m = clusterMass rho ν.representative.1 C

lemma clusterEndpoint_extrema_of_representation {k dx dz n : ℕ} {radius rho : ℝ}
    (CS : ConfidenceSetData k dx dz n radius) (center : AtomicLaw.LawModulo k radius)
    (hrep : CalgHasConstrainedRepresentation CS center) (C : Finset ℝ) :
    (sInf {m | ∃ ν ∈ CS.Calg, m = clusterMass rho ν.representative.1 C},
      sSup {m | ∃ ν ∈ CS.Calg, m = clusterMass rho ν.representative.1 C}) =
    (sInf {m | ClusterEndpointFeasible CS center rho C m},
      sSup {m | ClusterEndpointFeasible CS center rho C m}) := by
  congr 1 <;> apply congrArg <;> ext m <;> simp only [Set.mem_setOf_eq]
  all_goals
    constructor
    · rintro ⟨ν, hν, rfl⟩
      exact ⟨ν, (hrep ν).mp hν |>.1, (hrep ν).mp hν |>.2, rfl⟩
    · rintro ⟨ν, hf, hp, rfl⟩
      exact ⟨ν, (hrep ν).mpr ⟨hf, hp⟩, rfl⟩

/-- One cluster report at a fixed sample. -/
structure ClusterReportData (k dx dz n : ℕ) (radius : ℝ) where
  EP : SummarySpace dx dz → Set (Fin n → Obs dx dz)
    -- @realizes \(E_P\)(summary concentration event as a function of S(P))
  rho : ℝ -- @realizes \(\rho_{n,\alpha}\)(Ralpha/mStar)
  rho_pos : 0 < rho
  Kcomponents : Finset (Finset ℝ) -- @realizes \(\widehat{\mathscr K}_{n,\alpha}\)(components)
  Ktrue : AtomicLaw k radius → Finset ℝ → Finset ℝ -- @realizes \(K_C(P)\)(true association)
  Kcand : AtomicLaw k radius → Finset ℝ → Finset ℝ -- @realizes \(K_C(\xi)\)(candidate association)
  supportInterval : Finset ℝ → ℝ × ℝ
  massInterval : Finset ℝ → ℝ × ℝ -- @realizes \(I_C\)(infimum/supremum masses)
  massInterval_valid : ∀ C, 0 ≤ (massInterval C).1 ∧
    (massInterval C).1 ≤ (massInterval C).2 ∧ (massInterval C).2 ≤ 1
  endpointFeasible : Finset ℝ → ℝ → Prop
  massInterval_program : ∀ C,
    massInterval C = (sInf {m | endpointFeasible C m}, sSup {m | endpointFeasible C m})
  externalGap : AtomicLaw k radius → Finset ℝ → EReal -- @realizes \(\Delta_C(P)\)(external gap)
  externalGap_range : ∀ ν, AtomicLaw.Valid ν → ∀ C, externalGap ν C = ⊤ ∨
    (0 : EReal) ≤ externalGap ν C ∧ externalGap ν C ≤ (2 * radius : ℝ)

-- @node: clusterReport_side_conditions
lemma clusterReport_side_conditions {k : ℕ} {radius rho : ℝ}
    (hradius : 0 ≤ radius) (hrho : 0 < rho)
    (Calg : Set (AtomicLaw.LawModulo k radius)) :
    (∀ C : Finset ℝ,
      let I :=
        (sInf {m | ∃ ν ∈ Calg, m = clusterMass rho ν.representative.1 C},
         sSup {m | ∃ ν ∈ Calg, m = clusterMass rho ν.representative.1 C})
      0 ≤ I.1 ∧ I.1 ≤ I.2 ∧ I.2 ≤ 1) ∧
    ∀ (ν : AtomicLaw k radius), AtomicLaw.Valid ν → ∀ C,
      (if (ν.support \ (ν.support.filter fun x => AtomicLaw.distToFinset x C ≤ rho)).Nonempty
       then sInf {d : EReal | ∃ x ∈ ν.support.filter fun x =>
          AtomicLaw.distToFinset x C ≤ rho,
          ∃ y ∈ ν.support, y ∉ ν.support.filter (fun x =>
            AtomicLaw.distToFinset x C ≤ rho) ∧ d = |x - y|}
       else ⊤) = ⊤ ∨
      (0 : EReal) ≤ (if (ν.support \ (ν.support.filter fun x =>
        AtomicLaw.distToFinset x C ≤ rho)).Nonempty then
          sInf {d : EReal | ∃ x ∈ ν.support.filter fun x =>
            AtomicLaw.distToFinset x C ≤ rho,
            ∃ y ∈ ν.support, y ∉ ν.support.filter (fun x =>
              AtomicLaw.distToFinset x C ≤ rho) ∧ d = |x - y|} else ⊤) ∧
      (if (ν.support \ (ν.support.filter fun x =>
        AtomicLaw.distToFinset x C ≤ rho)).Nonempty then
          sInf {d : EReal | ∃ x ∈ ν.support.filter fun x =>
            AtomicLaw.distToFinset x C ≤ rho,
            ∃ y ∈ ν.support, y ∉ ν.support.filter (fun x =>
              AtomicLaw.distToFinset x C ≤ rho) ∧ d = |x - y|} else ⊤) ≤
        (2 * radius : ℝ) := by
  classical
  have clusterMass_nonneg (nu : AtomicLaw k radius) (hnu : AtomicLaw.Valid nu)
      (C : Finset ℝ) : 0 ≤ clusterMass rho nu C := by
    unfold clusterMass
    exact Finset.sum_nonneg fun i _ => by
      split_ifs
      · exact hnu.1 i
      · exact le_rfl
  have clusterMass_le_one (nu : AtomicLaw k radius) (hnu : AtomicLaw.Valid nu)
      (C : Finset ℝ) : clusterMass rho nu C ≤ 1 := by
    unfold clusterMass
    calc
      ∑ i, (if AtomicLaw.distToFinset (nu.atom i) C ≤ rho then nu.weight i else 0)
          ≤ ∑ i, nu.weight i := by
            apply Finset.sum_le_sum
            intro i _
            split_ifs
            · exact le_rfl
            · exact hnu.1 i
      _ = 1 := hnu.2.1
  constructor
  · intro C
    let S : Set ℝ := {m | ∃ nu ∈ Calg, m = clusterMass rho nu.representative.1 C}
    change 0 ≤ sInf S ∧ sInf S ≤ sSup S ∧ sSup S ≤ 1
    by_cases hS : S.Nonempty
    · have hlower : ∀ m ∈ S, 0 ≤ m := by
        rintro m ⟨nu, -, rfl⟩
        exact clusterMass_nonneg nu.representative.1 nu.representative.2 C
      have hupper : ∀ m ∈ S, m ≤ 1 := by
        rintro m ⟨nu, -, rfl⟩
        exact clusterMass_le_one nu.representative.1 nu.representative.2 C
      refine ⟨le_csInf hS hlower, ?_, csSup_le hS hupper⟩
      obtain ⟨m, hm⟩ := hS
      exact le_trans (csInf_le ⟨0, hlower⟩ hm) (le_csSup ⟨1, hupper⟩ hm)
    · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
      simp [hEmpty, Real.sInf_empty, Real.sSup_empty]
  · intro nu hnu C
    let A : Finset ℝ := nu.support.filter fun x => AtomicLaw.distToFinset x C ≤ rho
    let D : Set EReal := {d | ∃ x ∈ A, ∃ y ∈ nu.support, y ∉ A ∧ d = |x - y|}
    by_cases hcomp : (nu.support \ A).Nonempty
    · rw [if_pos (by simpa [A] using hcomp)]
      change sInf D = ⊤ ∨ (0 : EReal) ≤ sInf D ∧ sInf D ≤ (2 * radius : ℝ)
      by_cases hD : D.Nonempty
      · right
        constructor
        · apply le_sInf
          intro d hd
          rcases hd with ⟨x, hx, y, hy, hyA, rfl⟩
          positivity
        · obtain ⟨d, hd⟩ := hD
          refine (sInf_le hd).trans ?_
          rcases hd with ⟨x, hxA, y, hy, hyA, rfl⟩
          have hxSupp : x ∈ nu.support := (Finset.mem_filter.mp hxA).1
          rcases Finset.mem_image.mp hxSupp with ⟨i, hi, rfl⟩
          rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
          have hxi := hnu.2.2 i
          have hyj := hnu.2.2 j
          rw [EReal.coe_le_coe_iff]
          rw [abs_le]
          constructor <;> linarith [hxi.1, hxi.2, hyj.1, hyj.2]
      · left
        have hEmpty : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hD
        simp [hEmpty]
    · left
      rw [if_neg (by simpa [A] using hcomp)]

/-- Computable cluster-adaptive report.
    @realizes \(\mathfrak R_{n,\alpha}\)(support and mass report) -/
-- @node: def:cluster-report
noncomputable def clusterReport {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (R : SummaryRepairData k dx dz n L pi0 sigma0)
    (A : LatticeEstimator k dx dz n (effectRadius dz L sigma0))
    (hA : IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A)
    (sample : Fin n → Obs dx dz) (alpha C0 Clat : ℝ)
    (hn : 0 < n) (halpha : 0 < alpha) (halphaHalf : alpha < 1 / 2)
    (hC0 : 1 ≤ C0) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hpiMax : pi0 ≤ 1 / (2 * k : ℝ)) (hClat : 0 < Clat) :
    ClusterReportData k dx dz n (effectRadius dz L sigma0) :=
  let CS := confidenceSets R A hA sample alpha C0 Clat hn halpha halphaHalf hC0 hL hpi hpiMax hClat
  let rho := CS.Ralpha / CS.mStar
  let center := latticeLaw A sample
  let assoc := fun (ν : AtomicLaw k (effectRadius dz L sigma0)) (C : Finset ℝ) =>
    associatedSupport (rho := rho) ν C
  { EP := fun s => {sample' | dS (empSummary sample') s ≤ summaryRadius n alpha C0 L}
    rho := rho
    rho_pos := div_pos CS.Ralpha_pos CS.mStar_pos
    Kcomponents := components (rho := rho) center.representative.1
    Ktrue := assoc
    Kcand := assoc
    supportInterval := fun C => (sInf (C : Set ℝ) - rho, sSup (C : Set ℝ) + rho)
    massInterval := fun C =>
      (sInf {m | ∃ ν ∈ CS.Calg, m = clusterMass rho ν.representative.1 C},
       sSup {m | ∃ ν ∈ CS.Calg, m = clusterMass rho ν.representative.1 C})
    massInterval_valid := (clusterReport_side_conditions R.radius_nonneg
      (div_pos CS.Ralpha_pos CS.mStar_pos) CS.Calg).1
    endpointFeasible := ClusterEndpointFeasible CS center rho
    massInterval_program := fun C => clusterEndpoint_extrema_of_representation CS center
      (confidenceSets_constrainedRepresentation R A hA sample alpha C0 Clat hn halpha
        halphaHalf hC0 hL hpi hpiMax hClat) C
    externalGap := fun ν C => clusterExternalGap (rho := rho) ν C
    externalGap_range := (clusterReport_side_conditions R.radius_nonneg
      (div_pos CS.Ralpha_pos CS.mStar_pos) CS.Calg).2 }

-- @env: S6
-- @realizes \(R_{n,\alpha}\)(computable radius) @realizes \(\rho_{n,\alpha}\)(association radius)
variable {alpha C0 Clat : ℝ}

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
