import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ClusterGeometry
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ClusterTransport

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set

-- @node: cluster_effectGap_nonneg
lemma cluster_effectGap_nonneg {k dx dz : ℕ} (P : Measure (FullData k dx dz)) :
    (0 : EReal) ≤ effectGap P := by
  unfold effectGap
  apply le_sInf
  intro d hd
  rcases hd with ⟨u, v, hu, hv, huv, rfl⟩
  positivity

-- @node: cluster_effectGap_le_support_distance
lemma cluster_effectGap_le_support_distance {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    {x y : ℝ} (hx : x ∈ (quotientLaw P hM).representative.1.support)
    (hy : y ∈ (quotientLaw P hM).representative.1.support) (hxy : x ≠ y) :
    effectGap P ≤ (|x - y| : ℝ) := by
  let raw : AtomicLaw.ProbabilityLaw k (effectRadius dz L sigma0) :=
    ⟨quotientLawRaw P (effectRadius dz L sigma0), quotientLawRaw_valid P hM⟩
  have heq : (quotientLaw P hM).representative.1.support = raw.1.support := by
    apply cluster_support_eq_of_measureEquivalent
    exact (Quotient.eq_mk_iff_out (x := quotientLaw P hM) (y := raw)).mp rfl
  rw [heq] at hx hy
  rcases Finset.mem_image.mp hx with ⟨u, hu, hux⟩
  rcases Finset.mem_image.mp hy with ⟨v, hv, hvy⟩
  change latentEffect P u = x at hux
  change latentEffect P v = y at hvy
  have huPos : 0 < latentMass P u := by
    simpa [raw, quotientLawRaw] using (Finset.mem_filter.mp hu).2
  have hvPos : 0 < latentMass P v := by
    simpa [raw, quotientLawRaw] using (Finset.mem_filter.mp hv).2
  apply sInf_le
  refine ⟨u, v, huPos, hvPos, ?_, ?_⟩
  · intro huv
    exact hxy (hux.symm.trans (huv.trans hvy))
  · rw [← hux, ← hvy]

-- @node: cluster_effectGap_le_externalGap
lemma cluster_effectGap_le_externalGap {k dx dz : ℕ} {L pi0 sigma0 rho : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    {C : Finset ℝ}
    (hcard : (associatedSupport (rho := rho) (quotientLaw P hM).representative.1 C).card = 1) :
    effectGap P ≤ clusterExternalGap (rho := rho) (quotientLaw P hM).representative.1 C := by
  let nu := (quotientLaw P hM).representative.1
  unfold clusterExternalGap
  split_ifs with hcomp
  · apply le_sInf
    intro d hd
    rcases hd with ⟨x, hx, y, hy, hyout, rfl⟩
    apply cluster_effectGap_le_support_distance P hM
    · exact (Finset.mem_filter.mp hx).1
    · exact hy
    · intro hxy
      subst y
      exact hyout hx
  · exact le_top

-- @node: cluster_effectGap_toReal_pos_of_external_ne_top
lemma cluster_effectGap_toReal_pos_of_external_ne_top
    {k dx dz : ℕ} {L pi0 sigma0 rho : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    {C : Finset ℝ}
    (hcard : (associatedSupport (rho := rho) (quotientLaw P hM).representative.1 C).card = 1)
    (htop : clusterExternalGap (rho := rho) (quotientLaw P hM).representative.1 C ≠ ⊤) :
    0 < (effectGap P).toReal := by
  let nu := (quotientLaw P hM).representative.1
  let A := associatedSupport (rho := rho) nu C
  have hAcard : A.card = 1 := by simpa [A, nu] using hcard
  have hA : A.Nonempty := Finset.card_pos.mp (by rw [hAcard]; norm_num)
  have hcomp : (nu.support \ A).Nonempty := by
    by_contra he
    apply htop
    rw [clusterExternalGap, if_neg]
    simpa [nu, A] using he
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hyDiff⟩ := hcomp
  have hxSupp : x ∈ nu.support := (Finset.mem_filter.mp hx).1
  have hySupp : y ∈ nu.support := (Finset.mem_sdiff.mp hyDiff).1
  have hxy : x ≠ y := fun h => (Finset.mem_sdiff.mp hyDiff).2 (h ▸ hx)
  let raw : AtomicLaw.ProbabilityLaw k (effectRadius dz L sigma0) :=
    ⟨quotientLawRaw P (effectRadius dz L sigma0), quotientLawRaw_valid P hM⟩
  have heq : nu.support = raw.1.support := by
    apply cluster_support_eq_of_measureEquivalent
    exact (Quotient.eq_mk_iff_out (x := quotientLaw P hM) (y := raw)).mp rfl
  rw [heq] at hxSupp hySupp
  rcases Finset.mem_image.mp hxSupp with ⟨u, hu, hux⟩
  rcases Finset.mem_image.mp hySupp with ⟨v, hv, hvy⟩
  change latentEffect P u = x at hux
  change latentEffect P v = y at hvy
  have huPos : 0 < latentMass P u := by
    simpa [raw, quotientLawRaw] using (Finset.mem_filter.mp hu).2
  have hvPos : 0 < latentMass P v := by
    simpa [raw, quotientLawRaw] using (Finset.mem_filter.mp hv).2
  have huv : latentEffect P u ≠ latentEffect P v := by
    intro h
    exact hxy (hux.symm.trans (h.trans hvy))
  let D : Set EReal := {d | ∃ a b : Fin k,
    0 < latentMass P a ∧ 0 < latentMass P b ∧ latentEffect P a ≠ latentEffect P b ∧
      d = |latentEffect P a - latentEffect P b|}
  have hDne : D.Nonempty := ⟨(|latentEffect P u - latentEffect P v| : ℝ),
    u, v, huPos, hvPos, huv, rfl⟩
  have hDfin : D.Finite := by
    let F := (Finset.univ : Finset (Fin k)).product (Finset.univ : Finset (Fin k))
    have hsub : D ⊆ (fun p : Fin k × Fin k =>
        ((|latentEffect P p.1 - latentEffect P p.2| : ℝ) : EReal)) '' (F : Set (Fin k × Fin k)) := by
      rintro d ⟨a, b, ha, hb, hab, rfl⟩
      exact ⟨(a, b), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩
    exact (F.finite_toSet.image _).subset hsub
  have hmin := hDne.csInf_mem hDfin
  rcases hmin with ⟨a, b, ha, hb, hab, hEq⟩
  have hpos : (0 : EReal) < sInf D := by
    rw [hEq]
    exact_mod_cast (abs_pos.mpr (sub_ne_zero.mpr hab))
  apply EReal.toReal_pos
  · simpa [effectGap, D] using hpos
  · have hle : effectGap P ≤ (|latentEffect P u - latentEffect P v| : ℝ) :=
      sInf_le ⟨u, v, huPos, hvPos, huv, rfl⟩
    intro he
    rw [he] at hle
    exact (not_le_of_gt (EReal.coe_lt_top _)) hle

-- @node: cluster_singleton_width_from_external
lemma cluster_singleton_width_from_external
    {k dx dz : ℕ} {L pi0 sigma0 rho R width : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    {C : Finset ℝ}
    (hcard : (associatedSupport (rho := rho) (quotientLaw P hM).representative.1 C).card = 1)
    (hR : 0 ≤ R) (hpi : 0 < pi0)
    (htopZero : clusterExternalGap (rho := rho) (quotientLaw P hM).representative.1 C = ⊤ →
      width = 0)
    (hwidth : width ≤ 8 / pi0 * min 1
      (R / (clusterExternalGap (rho := rho) (quotientLaw P hM).representative.1 C).toReal)) :
    width ≤ 8 / pi0 * min 1 (R / (effectGap P).toReal) := by
  by_cases htop :
      clusterExternalGap (rho := rho) (quotientLaw P hM).representative.1 C = ⊤
  · rw [htopZero htop]
    apply mul_nonneg
    · exact div_nonneg (by norm_num) hpi.le
    · apply le_min (by norm_num)
      exact div_nonneg hR (EReal.toReal_nonneg (cluster_effectGap_nonneg P))
  · have hdeltaPos := cluster_effectGap_toReal_pos_of_external_ne_top P hM hcard htop
    have hle := cluster_effectGap_le_externalGap P hM hcard
    have hdeltaNotBot : effectGap P ≠ ⊥ := by
      intro he
      rw [he] at hdeltaPos
      simp at hdeltaPos
    have hreal : (effectGap P).toReal ≤
        (clusterExternalGap (rho := rho) (quotientLaw P hM).representative.1 C).toReal :=
      EReal.toReal_le_toReal hle hdeltaNotBot htop
    calc
      width ≤ 8 / pi0 * min 1
          (R / (clusterExternalGap (rho := rho)
            (quotientLaw P hM).representative.1 C).toReal) := hwidth
      _ ≤ 8 / pi0 * min 1 (R / (effectGap P).toReal) := by
        gcongr

-- @node: clusterMass_mem_unitInterval
lemma clusterMass_mem_unitInterval {k : ℕ} {radius rho : ℝ}
    (ν : AtomicLaw k radius) (hν : AtomicLaw.Valid ν) (C : Finset ℝ) :
    0 ≤ clusterMass rho ν C ∧ clusterMass rho ν C ≤ 1 := by
  constructor
  · unfold clusterMass
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp_all [hν.1]
  · unfold clusterMass
    calc
      (∑ i, if AtomicLaw.distToFinset (ν.atom i) C ≤ rho then ν.weight i else 0)
          ≤ ∑ i, ν.weight i := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs <;> simp_all [hν.1]
      _ = 1 := hν.2.1

-- @node: clusterMass_eq_one_of_support_subset
lemma clusterMass_eq_one_of_support_subset {k : ℕ} {radius rho : ℝ}
    (ν : AtomicLaw k radius) (hν : AtomicLaw.Valid ν) (C : Finset ℝ)
    (hsub : ν.support ⊆ associatedSupport (rho := rho) ν C) :
    clusterMass rho ν C = 1 := by
  unfold clusterMass
  rw [← hν.2.1]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hwi : 0 < ν.weight i
  · have hsupp : ν.atom i ∈ ν.support := Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwi⟩, rfl⟩
    rw [if_pos (Finset.mem_filter.mp (hsub hsupp)).2]
  · have hw0 : ν.weight i = 0 := le_antisymm (le_of_not_gt hwi) (hν.1 i)
    simp [hw0]

-- @node: cluster_mass_gap_cost
lemma cluster_mass_gap_cost {k : ℕ} {radius rho : ℝ}
    {center nu xi : AtomicLaw k radius}
    (hcenter : AtomicLaw.Valid center) (hnu : AtomicLaw.Valid nu)
    (hxi : AtomicLaw.Valid xi) (hrho : 0 ≤ rho)
    (hcloseNu : (∀ x ∈ nu.support, AtomicLaw.distToFinset x center.support ≤ rho) ∧
      ∀ y ∈ center.support, AtomicLaw.distToFinset y nu.support ≤ rho)
    (hcloseXi : (∀ x ∈ xi.support, AtomicLaw.distToFinset x center.support ≤ rho) ∧
      ∀ y ∈ center.support, AtomicLaw.distToFinset y xi.support ≤ rho)
    {C : Finset ℝ} (hC : C ∈ components (rho := rho) center)
    (hgapTop : clusterExternalGap (rho := rho) nu C ≠ ⊤)
    (hgapLarge : 2 * rho ≤ (clusterExternalGap (rho := rho) nu C).toReal)
    (γ : AtomicLaw.TransportPlan xi nu) :
    ((clusterExternalGap (rho := rho) nu C).toReal - 2 * rho) *
        |clusterMass rho xi C - clusterMass rho nu C| ≤ AtomicLaw.transportCost γ := by
  classical
  let gap := (clusterExternalGap (rho := rho) nu C).toReal
  have hCne : C.Nonempty := by
    obtain ⟨z, hz, hCz⟩ := Finset.mem_image.mp hC
    rw [← hCz]
    exact ⟨z, cluster_componentOf_mem_self hz⟩
  have hpartNu := cluster_association_partition hcenter hnu hrho hcloseNu
  have hpartXi := cluster_association_partition hcenter hxi hrho hcloseXi
  have hpos_support_left (i : Fin k) (j : Fin k) (hγ : 0 < γ.mass i j) :
      xi.atom i ∈ xi.support := by
    have hwi : 0 < xi.weight i := by
      rw [← γ.fst_marginal i]
      exact lt_of_lt_of_le hγ (Finset.single_le_sum (fun l _ => γ.nonneg i l)
        (Finset.mem_univ j))
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwi⟩, rfl⟩
  have hpos_support_right (i : Fin k) (j : Fin k) (hγ : 0 < γ.mass i j) :
      nu.atom j ∈ nu.support := by
    have hwj : 0 < nu.weight j := by
      rw [← γ.snd_marginal j]
      exact lt_of_lt_of_le hγ (Finset.single_le_sum (fun l _ => γ.nonneg l j)
        (Finset.mem_univ i))
    exact Finset.mem_image.mpr
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwj⟩, rfl⟩
  apply AtomicLaw.test_mass_gap γ
    (fun i => AtomicLaw.distToFinset (xi.atom i) C ≤ rho)
    (fun j => AtomicLaw.distToFinset (nu.atom j) C ≤ rho)
    (by linarith)
  intro i j hγ hcross
  have hxiSupp := hpos_support_left i j hγ
  have hnuSupp := hpos_support_right i j hγ
  rcases hcross with hcross | hcross
  · have hxiAssoc : xi.atom i ∈ associatedSupport (rho := rho) xi C :=
      Finset.mem_filter.mpr ⟨hxiSupp, hcross.1⟩
    obtain ⟨z, hzC, hxiz⟩ := cluster_distToFinset_attained (xi.atom i) hCne
    have hxiz_le : |xi.atom i - z| ≤ rho := hxiz ▸ hcross.1
    have hzSupp : z ∈ center.support := by
      obtain ⟨root, hroot, hCr⟩ := Finset.mem_image.mp hC
      apply cluster_componentOf_subset_support center root
      rw [hCr]
      exact hzC
    obtain ⟨y, hySupp, hzy⟩ := cluster_distToFinset_attained z
      (cluster_support_nonempty hnu)
    have hzy_le : |z - y| ≤ rho := hzy ▸ hcloseNu.2 z hzSupp
    have hyAssoc : y ∈ associatedSupport (rho := rho) nu C := by
      apply Finset.mem_filter.mpr
      refine ⟨hySupp, (cluster_distToFinset_le_of_mem y hzC).trans ?_⟩
      simpa [abs_sub_comm] using hzy_le
    have hgap := cluster_externalGap_le_cross hgapTop hyAssoc hnuSupp
      (by exact fun hj => hcross.2 (Finset.mem_filter.mp hj).2)
    have hyxi : |y - xi.atom i| ≤ 2 * rho := by
      calc
        |y - xi.atom i| ≤ |y - z| + |z - xi.atom i| := abs_sub_le y z (xi.atom i)
        _ ≤ 2 * rho := by
          rw [abs_sub_comm y z, abs_sub_comm z (xi.atom i)]
          linarith
    calc
      gap - 2 * rho ≤ |y - nu.atom j| - 2 * rho := sub_le_sub_right hgap _
      _ ≤ |xi.atom i - nu.atom j| := by
        have ht := abs_sub_le y (xi.atom i) (nu.atom j)
        linarith
  · obtain ⟨z, hzSupp, hxiz⟩ := cluster_distToFinset_attained (xi.atom i)
      (cluster_support_nonempty hcenter)
    have hxiz_le : |xi.atom i - z| ≤ rho := hxiz ▸ hcloseXi.1 (xi.atom i) hxiSupp
    let D := componentOf (rho := rho) center z
    have hD : D ∈ components (rho := rho) center :=
      Finset.mem_image.mpr ⟨z, hzSupp, rfl⟩
    have hzD : z ∈ D := cluster_componentOf_mem_self hzSupp
    obtain ⟨y, hySupp, hzy⟩ := cluster_distToFinset_attained z
      (cluster_support_nonempty hnu)
    have hzy_le : |z - y| ≤ rho := hzy ▸ hcloseNu.2 z hzSupp
    have hyD : y ∈ associatedSupport (rho := rho) nu D := by
      exact Finset.mem_filter.mpr ⟨hySupp,
        (cluster_distToFinset_le_of_mem y hzD).trans (by simpa [abs_sub_comm] using hzy_le)⟩
    have hyNotC : y ∉ associatedSupport (rho := rho) nu C := by
      intro hyC
      obtain ⟨E, hE, huniq⟩ := (hpartNu y).mp hySupp
      have hCu : C = D := (huniq C ⟨hC, hyC⟩).trans
        (huniq D ⟨hD, hyD⟩).symm
      have hzC : z ∈ C := hCu ▸ hzD
      exact hcross.1 ((cluster_distToFinset_le_of_mem (xi.atom i) hzC).trans hxiz_le)
    have hnuAssoc : nu.atom j ∈ associatedSupport (rho := rho) nu C :=
      Finset.mem_filter.mpr ⟨hnuSupp, hcross.2⟩
    have hgap := cluster_externalGap_le_cross hgapTop hnuAssoc hySupp hyNotC
    have hyxi : |y - xi.atom i| ≤ 2 * rho := by
      calc
        |y - xi.atom i| ≤ |y - z| + |z - xi.atom i| := abs_sub_le y z (xi.atom i)
        _ ≤ 2 * rho := by
          rw [abs_sub_comm y z, abs_sub_comm z (xi.atom i)]
          linarith
    calc
      gap - 2 * rho ≤ |nu.atom j - y| - 2 * rho := sub_le_sub_right hgap _
      _ ≤ |xi.atom i - nu.atom j| := by
        have ht := abs_sub_le (nu.atom j) (xi.atom i) y
        rw [abs_sub_comm (nu.atom j) (xi.atom i), abs_sub_comm (xi.atom i) y] at ht
        linarith

-- @node: cluster_candidate_mass_error
lemma cluster_candidate_mass_error {k : ℕ} {radius m R rho : ℝ}
    {center nu xi : AtomicLaw k radius}
    (hcenter : AtomicLaw.Valid center) (hnu : AtomicLaw.Valid nu)
    (hxi : AtomicLaw.Valid xi) (hm : 0 < m) (hmOne : m ≤ 1)
    (hR : 0 < R) (hrho : rho = R / m)
    (hcenterFloor : AtomicLaw.AtomFloor m center)
    (hnuFloor : AtomicLaw.AtomFloor m nu)
    (hxiFloor : AtomicLaw.AtomFloor m xi)
    (hWnu : AtomicLaw.wass1 nu center ≤ R)
    (hWxi : AtomicLaw.wass1 xi center ≤ R)
    {C : Finset ℝ} (hC : C ∈ components (rho := rho) center) :
    if clusterExternalGap (rho := rho) nu C = ⊤ then
      clusterMass rho xi C = clusterMass rho nu C
    else
      |clusterMass rho xi C - clusterMass rho nu C| ≤
        4 / m * min 1 (R / (clusterExternalGap (rho := rho) nu C).toReal) := by
  classical
  have hrho0 : 0 ≤ rho := by rw [hrho]; positivity
  have hscale : m * rho = R := by rw [hrho]; field_simp
  have hcloseNu := AtomicLaw.support_close_of_wass1_le hnu hcenter hnuFloor hcenterFloor
    hm (by rw [hscale]; exact hWnu)
  have hcloseXi := AtomicLaw.support_close_of_wass1_le hxi hcenter hxiFloor hcenterFloor
    hm (by rw [hscale]; exact hWxi)
  split_ifs with htop
  · have hcompEmpty : nu.support \ associatedSupport (rho := rho) nu C = ∅ := by
      by_contra hne
      have hcomp : (nu.support \ associatedSupport (rho := rho) nu C).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hne
      have hassoc : (associatedSupport (rho := rho) nu C).Nonempty := by
        obtain ⟨z, hz, hCz⟩ := Finset.mem_image.mp hC
        obtain ⟨x, hx, hzx⟩ := cluster_distToFinset_attained z
          (cluster_support_nonempty hnu)
        refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩⟩
        have hzC : z ∈ C := by rw [← hCz]; exact cluster_componentOf_mem_self hz
        exact (cluster_distToFinset_le_of_mem x hzC).trans
          (by simpa [abs_sub_comm] using (hzx ▸ hcloseNu.2 z hz))
      obtain ⟨x, hx⟩ := hassoc
      obtain ⟨y, hyDiff⟩ := hcomp
      have hy := (Finset.mem_sdiff.mp hyDiff).1
      have hyout := (Finset.mem_sdiff.mp hyDiff).2
      have hfinite :
          (sInf {d : EReal | ∃ a ∈ associatedSupport (rho := rho) nu C,
            ∃ b ∈ nu.support, b ∉ associatedSupport (rho := rho) nu C ∧
              d = |a - b|}) ≤ (|x - y| : ℝ) := by
        apply sInf_le
        exact ⟨x, hx, y, hy, hyout, rfl⟩
      have hnotTop : sInf {d : EReal | ∃ a ∈ associatedSupport (rho := rho) nu C,
          ∃ b ∈ nu.support, b ∉ associatedSupport (rho := rho) nu C ∧
            d = |a - b|} ≠ ⊤ := by
        intro heq
        rw [heq] at hfinite
        exact (not_le_of_gt (EReal.coe_lt_top _)) hfinite
      have hdef : clusterExternalGap (rho := rho) nu C =
          sInf {d : EReal | ∃ a ∈ associatedSupport (rho := rho) nu C,
            ∃ b ∈ nu.support, b ∉ associatedSupport (rho := rho) nu C ∧
              d = |a - b|} := by
        rw [clusterExternalGap, if_pos ⟨y, hyDiff⟩]
      exact hnotTop (hdef.symm.trans htop)
    have hnuAll : nu.support ⊆ associatedSupport (rho := rho) nu C := by
      intro x hx
      by_contra hout
      have : x ∈ nu.support \ associatedSupport (rho := rho) nu C :=
        Finset.mem_sdiff.mpr ⟨hx, hout⟩
      simpa [hcompEmpty] using this
    have hpartNu := cluster_association_partition hcenter hnu hrho0 hcloseNu
    have hpartXi := cluster_association_partition hcenter hxi hrho0 hcloseXi
    have huniqueComp : ∀ D ∈ components (rho := rho) center, D = C := by
      intro D hD
      obtain ⟨z, hz, hDz⟩ := Finset.mem_image.mp hD
      obtain ⟨x, hx, hzx⟩ := cluster_distToFinset_attained z
        (cluster_support_nonempty hnu)
      have hzD : z ∈ D := by rw [← hDz]; exact cluster_componentOf_mem_self hz
      have hxD : x ∈ associatedSupport (rho := rho) nu D :=
        Finset.mem_filter.mpr ⟨hx, (cluster_distToFinset_le_of_mem x hzD).trans
          (by simpa [abs_sub_comm] using (hzx ▸ hcloseNu.2 z hz))⟩
      obtain ⟨E, hE, huniq⟩ := (hpartNu x).mp hx
      exact (huniq D ⟨hD, hxD⟩).trans
        (huniq C ⟨hC, hnuAll hx⟩).symm
    have hxiAll : xi.support ⊆ associatedSupport (rho := rho) xi C := by
      intro x hx
      obtain ⟨D, hD, huniq⟩ := (hpartXi x).mp hx
      have := hD.2
      rwa [huniqueComp D hD.1] at this
    rw [clusterMass_eq_one_of_support_subset xi hxi C hxiAll,
      clusterMass_eq_one_of_support_subset nu hnu C hnuAll]
  · let gap := (clusterExternalGap (rho := rho) nu C).toReal
    have hgap0 : 0 ≤ gap := by
      exact EReal.toReal_nonneg (cluster_externalGap_nonneg nu C)
    have hWxin : AtomicLaw.wass1 xi nu ≤ 2 * R := by
      calc
        AtomicLaw.wass1 xi nu ≤ AtomicLaw.wass1 xi center +
            AtomicLaw.wass1 center nu := by
          simpa using AtomicLaw.wass1_triangle
            (⟨xi, hxi⟩ : AtomicLaw.ProbabilityLaw k radius)
            (⟨center, hcenter⟩ : AtomicLaw.ProbabilityLaw k radius)
            (⟨nu, hnu⟩ : AtomicLaw.ProbabilityLaw k radius)
        _ ≤ R + R := add_le_add hWxi (by
          rw [AtomicLaw.wass1_comm]
          exact hWnu)
        _ = 2 * R := by ring
    by_cases hlarge : 4 * rho < gap
    · obtain ⟨γ, hγ⟩ := AtomicLaw.wass1_optimal_plan hxi hnu
      have hcost := cluster_mass_gap_cost hcenter hnu hxi hrho0 hcloseNu hcloseXi
        hC htop (by linarith) γ
      have habs : |clusterMass rho xi C - clusterMass rho nu C| ≤ 4 * R / gap := by
        rw [← hγ] at hWxin
        have hden : 0 < gap - 2 * rho := by linarith
        change (gap - 2 * rho) * _ ≤ _ at hcost
        rw [le_div_iff₀ (by linarith : 0 < gap)]
        nlinarith [hcost, hWxin,
          abs_nonneg (clusterMass rho xi C - clusterMass rho nu C)]
      have hratio : R / gap < 1 := by
        rw [hrho] at hlarge
        have hm0 := hm
        have : R / gap < m / 4 := by
          rw [div_lt_div_iff₀ (by linarith : 0 < gap) (by norm_num : (0:ℝ)<4)]
          field_simp at hlarge ⊢
          nlinarith
        linarith
      rw [min_eq_right hratio.le]
      calc
        _ ≤ 4 * R / gap := habs
        _ ≤ 4 / m * (R / gap) := by
          rw [show 4 * R / gap = 4 * (R / gap) by ring]
          gcongr
          rw [le_div_iff₀ hm]
          linarith
    · have habsOne : |clusterMass rho xi C - clusterMass rho nu C| ≤ 1 := by
        have hxiI := clusterMass_mem_unitInterval (rho := rho) xi hxi C
        have hnuI := clusterMass_mem_unitInterval (rho := rho) nu hnu C
        rw [abs_le]
        constructor <;> linarith
      by_cases hratio : 1 ≤ R / gap
      · rw [min_eq_left hratio]
        calc
          _ ≤ 1 := habsOne
          _ ≤ 4 / m := by
            rw [le_div_iff₀ hm]
            linarith
          _ = 4 / m * 1 := by ring
      · rw [min_eq_right (le_of_not_ge hratio)]
        calc
          _ ≤ 1 := habsOne
          _ ≤ 4 / m * (R / gap) := by
            have hgapPos : 0 < gap := by
              have hassoc : (associatedSupport (rho := rho) nu C).Nonempty := by
                obtain ⟨z, hz, hCz⟩ := Finset.mem_image.mp hC
                obtain ⟨x, hx, hzx⟩ := cluster_distToFinset_attained z
                  (cluster_support_nonempty hnu)
                refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩⟩
                have hzC : z ∈ C := by rw [← hCz]; exact cluster_componentOf_mem_self hz
                exact (cluster_distToFinset_le_of_mem x hzC).trans
                  (by simpa [abs_sub_comm] using (hzx ▸ hcloseNu.2 z hz))
              exact cluster_externalGap_toReal_pos hassoc htop
            rw [hrho] at hlarge
            have hRg : m / 4 ≤ R / gap := by
              rw [div_le_div_iff₀ (by norm_num : (0:ℝ)<4) hgapPos]
              field_simp at hlarge ⊢
              nlinarith
            calc
              1 = 4 / m * (m / 4) := by field_simp
              _ ≤ 4 / m * (R / gap) := by gcongr

-- @node: cluster_deterministic_report
lemma cluster_deterministic_report {k : ℕ} {radius m R rho : ℝ}
    {center nu : AtomicLaw k radius}
    (hcenter : AtomicLaw.Valid center) (hnu : AtomicLaw.Valid nu)
    (hm : 0 < m) (hmOne : m ≤ 1) (hR : 0 < R) (hrho : rho = R / m)
    (hcenterFloor : AtomicLaw.AtomFloor m center)
    (hnuFloor : AtomicLaw.AtomFloor m nu)
    (Calg : Set (AtomicLaw.LawModulo k radius))
    (hCalg : ∀ q ∈ Calg, AtomicLaw.AtomFloor m q.representative.1 ∧
      AtomicLaw.wass1 q.representative.1 center ≤ R)
    (hnuCalg : AtomicLaw.LawModulo.ofProbabilityLaw ⟨nu, hnu⟩ ∈ Calg)
    (hnuRep : (AtomicLaw.LawModulo.ofProbabilityLaw ⟨nu, hnu⟩).representative.1 = nu) :
    (∀ x, x ∈ nu.support ↔ ∃! C, C ∈ components (rho := rho) center ∧
      x ∈ associatedSupport (rho := rho) nu C) ∧
    (∀ C ∈ components (rho := rho) center,
      associatedSupport (rho := rho) nu C ⊆ nu.support) ∧
    (∀ C ∈ components (rho := rho) center, ∀ x ∈ associatedSupport (rho := rho) nu C,
      sInf (C : Set ℝ) - rho ≤ x ∧ x ≤ sSup (C : Set ℝ) + rho) ∧
    (∀ C ∈ components (rho := rho) center,
      sInf {v | ∃ q ∈ Calg, v = clusterMass rho q.representative.1 C} ≤
        clusterMass rho nu C ∧
      clusterMass rho nu C ≤
        sSup {v | ∃ q ∈ Calg, v = clusterMass rho q.representative.1 C}) ∧
    (∀ C ∈ components (rho := rho) center,
      (associatedSupport (rho := rho) nu C).card = 1 →
      (sSup (C : Set ℝ) + rho) - (sInf (C : Set ℝ) - rho) ≤ 4 * rho) ∧
    (∀ C ∈ components (rho := rho) center,
      clusterExternalGap (rho := rho) nu C = ⊤ →
      sSup {v | ∃ q ∈ Calg, v = clusterMass rho q.representative.1 C} -
        sInf {v | ∃ q ∈ Calg, v = clusterMass rho q.representative.1 C} = 0) ∧
    (∀ C ∈ components (rho := rho) center,
      sSup {v | ∃ q ∈ Calg, v = clusterMass rho q.representative.1 C} -
        sInf {v | ∃ q ∈ Calg, v = clusterMass rho q.representative.1 C} ≤
          8 / m * min 1 (R / (clusterExternalGap (rho := rho) nu C).toReal)) := by
  classical
  have hrho0 : 0 ≤ rho := by rw [hrho]; positivity
  have hscale : m * rho = R := by rw [hrho]; field_simp
  have hWnu : AtomicLaw.wass1 nu center ≤ R := by
    have h := (hCalg _ hnuCalg).2
    rwa [hnuRep] at h
  have hcloseNu := AtomicLaw.support_close_of_wass1_le hnu hcenter hnuFloor hcenterFloor
    hm (by rw [hscale]; exact hWnu)
  have hpart := cluster_association_partition hcenter hnu hrho0 hcloseNu
  refine ⟨hpart, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C hC x hx
    exact (Finset.mem_filter.mp hx).1
  · intro C hC x hx
    have hCne : C.Nonempty := by
      obtain ⟨z, hz, hCz⟩ := Finset.mem_image.mp hC
      rw [← hCz]
      exact ⟨z, cluster_componentOf_mem_self hz⟩
    obtain ⟨y, hy, hxy⟩ := cluster_distToFinset_attained x hCne
    have hdist : |x - y| ≤ rho := hxy ▸ (Finset.mem_filter.mp hx).2
    have hbelow : BddBelow (C : Set ℝ) := C.finite_toSet.bddBelow
    have habove : BddAbove (C : Set ℝ) := C.finite_toSet.bddAbove
    have hinf : sInf (C : Set ℝ) ≤ y := csInf_le hbelow hy
    have hsup : y ≤ sSup (C : Set ℝ) := le_csSup habove hy
    rw [abs_le] at hdist
    constructor <;> linarith
  · intro C hC
    let S : Set ℝ := {v | ∃ q ∈ Calg, v = clusterMass rho q.representative.1 C}
    have hmS : clusterMass rho nu C ∈ S := by
      refine ⟨AtomicLaw.LawModulo.ofProbabilityLaw ⟨nu, hnu⟩, hnuCalg, ?_⟩
      rw [hnuRep]
    have hbound : ∀ x ∈ S, |x - clusterMass rho nu C| ≤ 1 := by
      rintro x ⟨q, hq, rfl⟩
      have hqI := clusterMass_mem_unitInterval (rho := rho) q.representative.1
        q.representative.2 C
      have hnuI := clusterMass_mem_unitInterval (rho := rho) nu hnu C
      rw [abs_le]
      constructor <;> linarith
    have hext := cluster_extrema_contain_and_width hmS (by norm_num) hbound
    exact ⟨hext.1, hext.2.1⟩
  · intro C hC hcard
    have hCne : C.Nonempty := by
      obtain ⟨z, hz, hCz⟩ := Finset.mem_image.mp hC
      rw [← hCz]
      exact ⟨z, cluster_componentOf_mem_self hz⟩
    obtain ⟨x, hxAssoc⟩ : (associatedSupport (rho := rho) nu C).Nonempty := by
      obtain ⟨z, hzC⟩ := hCne
      have hzSupp : z ∈ center.support := by
        obtain ⟨root, hroot, hCr⟩ := Finset.mem_image.mp hC
        apply cluster_componentOf_subset_support center root
        rw [hCr]
        exact hzC
      obtain ⟨x, hx, hzx⟩ := cluster_distToFinset_attained z
        (cluster_support_nonempty hnu)
      refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩⟩
      exact (cluster_distToFinset_le_of_mem x hzC).trans
        (by simpa [abs_sub_comm] using (hzx ▸ hcloseNu.2 z hzSupp))
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have hax : a = x := by
      have : x ∈ ({a} : Finset ℝ) := by rwa [← ha]
      have hxa : x = a := by simpa using this
      exact hxa.symm
    have hsingleton : associatedSupport (rho := rho) nu C = {x} := by
      rw [ha, hax]
    have hcenterClose : ∀ z ∈ C, |z - x| ≤ rho := by
      intro z hz
      have hzSupp : z ∈ center.support := by
        obtain ⟨root, hroot, hCr⟩ := Finset.mem_image.mp hC
        apply cluster_componentOf_subset_support center root
        rw [hCr]
        exact hz
      obtain ⟨y, hy, hzy⟩ := cluster_distToFinset_attained z
        (cluster_support_nonempty hnu)
      have hyAssoc : y ∈ associatedSupport (rho := rho) nu C :=
        Finset.mem_filter.mpr ⟨hy, (cluster_distToFinset_le_of_mem y hz).trans
          (by simpa [abs_sub_comm] using (hzy ▸ hcloseNu.2 z hzSupp))⟩
      have : y = x := by simpa [hsingleton] using hyAssoc
      subst y
      exact hzy ▸ hcloseNu.2 z hzSupp
    have hinfMem := hCne.csInf_mem
    have hsupMem := hCne.csSup_mem
    have h1 := hcenterClose (sInf (C : Set ℝ)) hinfMem
    have h2 := hcenterClose (sSup (C : Set ℝ)) hsupMem
    rw [abs_le] at h1 h2
    linarith
  · intro C hC htop
    let S : Set ℝ := {v | ∃ q ∈ Calg, v = clusterMass rho q.representative.1 C}
    have hmS : clusterMass rho nu C ∈ S := by
      refine ⟨AtomicLaw.LawModulo.ofProbabilityLaw ⟨nu, hnu⟩, hnuCalg, ?_⟩
      rw [hnuRep]
    have hzero : ∀ x ∈ S, |x - clusterMass rho nu C| ≤ 0 := by
      rintro x ⟨q, hq, rfl⟩
      have herr := cluster_candidate_mass_error hcenter hnu q.representative.2 hm hmOne
        hR hrho hcenterFloor hnuFloor (hCalg q hq).1 hWnu (hCalg q hq).2 hC
      rw [if_pos htop] at herr
      rw [herr, sub_self, abs_zero]
    have hext := cluster_extrema_contain_and_width hmS (le_refl 0) hzero
    change sSup S - sInf S = 0
    linarith
  · intro C hC
    let S : Set ℝ := {v | ∃ q ∈ Calg, v = clusterMass rho q.representative.1 C}
    let B := 4 / m * min 1 (R / (clusterExternalGap (rho := rho) nu C).toReal)
    have hmS : clusterMass rho nu C ∈ S := by
      refine ⟨AtomicLaw.LawModulo.ofProbabilityLaw ⟨nu, hnu⟩, hnuCalg, ?_⟩
      rw [hnuRep]
    have hB : 0 ≤ B := by
      dsimp [B]
      apply mul_nonneg
      · exact div_nonneg (by norm_num) hm.le
      · apply le_min (by norm_num)
        exact div_nonneg hR.le
          (EReal.toReal_nonneg (cluster_externalGap_nonneg nu C))
    have hbound : ∀ x ∈ S, |x - clusterMass rho nu C| ≤ B := by
      rintro x ⟨q, hq, rfl⟩
      have herr := cluster_candidate_mass_error hcenter hnu q.representative.2 hm hmOne
        hR hrho hcenterFloor hnuFloor (hCalg q hq).1 hWnu (hCalg q hq).2 hC
      split_ifs at herr with htop
      · rw [herr, sub_self, abs_zero]
        exact hB
      · exact herr
    have hext := cluster_extrema_contain_and_width hmS hB hbound
    change sSup S - sInf S ≤ _
    calc
      _ ≤ 2 * B := hext.2.2
      _ = 8 / m * min 1 (R / (clusterExternalGap (rho := rho) nu C).toReal) := by
        dsimp [B]
        ring

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
