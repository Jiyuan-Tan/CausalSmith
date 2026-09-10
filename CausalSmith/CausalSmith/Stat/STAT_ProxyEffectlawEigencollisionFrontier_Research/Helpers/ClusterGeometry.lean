import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Inference

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open Set

-- @node: cluster_support_nonempty
lemma cluster_support_nonempty {k : ℕ} {radius : ℝ} {ν : AtomicLaw k radius}
    (hν : AtomicLaw.Valid ν) : ν.support.Nonempty := by
  by_contra he
  have hempty : ν.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
  have hzero : ∑ i, ν.weight i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hnpos : ¬ 0 < ν.weight i := by
      intro hp
      have hx : ν.atom i ∈ ν.support := Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩
      simpa [hempty] using hx
    exact le_antisymm (le_of_not_gt hnpos) (hν.1 i)
  linarith [hν.2.1]

-- @node: cluster_support_eq_of_measureEquivalent
lemma cluster_support_eq_of_measureEquivalent {k : ℕ} {radius : ℝ}
    (ν ξ : AtomicLaw.ProbabilityLaw k radius)
    (h : ν.MeasureEquivalent ξ) : ν.1.support = ξ.1.support := by
  classical
  have oneSide (a b : AtomicLaw.ProbabilityLaw k radius)
      (hab : a.MeasureEquivalent b) : a.1.support ⊆ b.1.support := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hipos := (Finset.mem_filter.mp hi).2
    have hleft : 0 < ∑ l with a.1.atom l = a.1.atom i, a.1.weight l :=
      Finset.sum_pos' (fun l _ => a.2.1 l) ⟨i, by simp, hipos⟩
    have hright : 0 < ∑ l with b.1.atom l = a.1.atom i, b.1.weight l := by
      rw [← hab.aggregate_weight]
      exact hleft
    obtain ⟨j, hjmem, hjpos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun l _ => b.2.1 l)).mp hright
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hjpos⟩, (Finset.mem_filter.mp hjmem).2⟩
  ext x
  exact ⟨fun hx => oneSide ν ξ h hx, fun hx => oneSide ξ ν h.symm hx⟩

-- @node: cluster_distToFinset_attained
lemma cluster_distToFinset_attained (x : ℝ) {C : Finset ℝ} (hC : C.Nonempty) :
    ∃ y ∈ C, AtomicLaw.distToFinset x C = |x - y| := by
  let S : Set ℝ := {d | ∃ y ∈ C, d = |x - y|}
  have hSne : S.Nonempty := by
    obtain ⟨y, hy⟩ := hC
    exact ⟨|x - y|, y, hy, rfl⟩
  have hSfin : S.Finite := by
    have himg : S = (fun y : ℝ => |x - y|) '' (C : Set ℝ) := by
      ext d
      simp [S, eq_comm]
    rw [himg]
    exact C.finite_toSet.image _
  have hm := hSne.csInf_mem hSfin
  simpa [AtomicLaw.distToFinset, S] using hm

-- @node: cluster_distToFinset_nonneg
lemma cluster_distToFinset_nonneg (x : ℝ) {C : Finset ℝ} (hC : C.Nonempty) :
    0 ≤ AtomicLaw.distToFinset x C := by
  obtain ⟨y, hy, hxy⟩ := cluster_distToFinset_attained x hC
  rw [hxy]
  exact abs_nonneg _

-- @node: cluster_distToFinset_le_of_mem
lemma cluster_distToFinset_le_of_mem (x : ℝ) {C : Finset ℝ} {y : ℝ} (hy : y ∈ C) :
    AtomicLaw.distToFinset x C ≤ |x - y| := by
  unfold AtomicLaw.distToFinset
  apply csInf_le
  · exact ⟨0, by rintro d ⟨z, hz, rfl⟩; exact abs_nonneg _⟩
  · exact ⟨y, hy, rfl⟩

-- @node: cluster_linked_symmetric
lemma cluster_linked_symmetric {k : ℕ} {radius rho : ℝ} (ν : AtomicLaw k radius) :
    Symmetric (linked (rho := rho) ν) := by
  intro x y hxy
  exact ⟨hxy.2.1, hxy.1, by simpa [abs_sub_comm] using hxy.2.2⟩

-- @node: cluster_componentOf_mem_self
lemma cluster_componentOf_mem_self {k : ℕ} {radius rho : ℝ} {ν : AtomicLaw k radius}
    {x : ℝ} (hx : x ∈ ν.support) : x ∈ componentOf (rho := rho) ν x := by
  simp [componentOf, hx, Relation.ReflTransGen.refl]

-- @node: cluster_componentOf_subset_support
lemma cluster_componentOf_subset_support {k : ℕ} {radius rho : ℝ}
    (ν : AtomicLaw k radius) (x : ℝ) : componentOf (rho := rho) ν x ⊆ ν.support := by
  classical
  intro y hy
  exact (Finset.mem_filter.mp (by simpa [componentOf] using hy)).1

-- @node: cluster_componentOf_eq_of_connected
lemma cluster_componentOf_eq_of_connected {k : ℕ} {radius rho : ℝ}
    {ν : AtomicLaw k radius} {x y : ℝ}
    (hxy : Relation.ReflTransGen (linked (rho := rho) ν) x y) :
    componentOf (rho := rho) ν x = componentOf (rho := rho) ν y := by
  classical
  haveI : Std.Symm (linked (rho := rho) ν) := ⟨cluster_linked_symmetric ν⟩
  ext z
  simp only [componentOf, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hxz⟩
    exact ⟨hz, (Std.Symm.symm x y hxy).trans hxz⟩
  · rintro ⟨hz, hyz⟩
    exact ⟨hz, hxy.trans hyz⟩

-- @node: cluster_componentOf_eq_of_linked
lemma cluster_componentOf_eq_of_linked {k : ℕ} {radius rho : ℝ}
    {ν : AtomicLaw k radius} {x y : ℝ} (hxy : linked (rho := rho) ν x y) :
    componentOf (rho := rho) ν x = componentOf (rho := rho) ν y :=
  cluster_componentOf_eq_of_connected (Relation.ReflTransGen.single hxy)

-- @node: cluster_component_eq_componentOf_of_mem
lemma cluster_component_eq_componentOf_of_mem {k : ℕ} {radius rho : ℝ}
    {ν : AtomicLaw k radius} {C : Finset ℝ} (hC : C ∈ components (rho := rho) ν)
    {x : ℝ} (hx : x ∈ C) : C = componentOf (rho := rho) ν x := by
  classical
  obtain ⟨y, hy, hCy⟩ := Finset.mem_image.mp hC
  have hxComp : x ∈ componentOf (rho := rho) ν y := by rw [hCy]; exact hx
  have hyx : Relation.ReflTransGen (linked (rho := rho) ν) y x :=
    (Finset.mem_filter.mp (by simpa [componentOf] using hxComp)).2
  exact hCy.symm.trans (cluster_componentOf_eq_of_connected hyx)

-- @node: cluster_components_partition_support
lemma cluster_components_partition_support {k : ℕ} {radius rho : ℝ}
    (ν : AtomicLaw k radius) :
    ∀ x, x ∈ ν.support ↔ ∃! C, C ∈ components (rho := rho) ν ∧ x ∈ C := by
  classical
  intro x
  constructor
  · intro hx
    refine ⟨componentOf (rho := rho) ν x, ?_, ?_⟩
    · exact ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, cluster_componentOf_mem_self hx⟩
    · intro C hC
      obtain ⟨y, hy, hCy⟩ := Finset.mem_image.mp hC.1
      have hxComp : x ∈ componentOf (rho := rho) ν y := by
        rw [hCy]
        exact hC.2
      have hyx : Relation.ReflTransGen (linked (rho := rho) ν) y x :=
        (Finset.mem_filter.mp (by simpa [componentOf] using hxComp)).2
      exact hCy.symm.trans (cluster_componentOf_eq_of_connected hyx)
  · rintro ⟨C, ⟨hCcomp, hxC⟩, huniq⟩
    obtain ⟨y, hy, hCy⟩ := Finset.mem_image.mp hCcomp
    apply cluster_componentOf_subset_support ν y
    rw [hCy]
    exact hxC

-- @node: cluster_association_partition
lemma cluster_association_partition {k : ℕ} {radius rho : ℝ}
    {center ν : AtomicLaw k radius} (hcenter : AtomicLaw.Valid center)
    (hν : AtomicLaw.Valid ν) (hrho : 0 ≤ rho)
    (hclose : (∀ x ∈ ν.support, AtomicLaw.distToFinset x center.support ≤ rho) ∧
      ∀ y ∈ center.support, AtomicLaw.distToFinset y ν.support ≤ rho) :
    ∀ x, x ∈ ν.support ↔ ∃! C,
      C ∈ components (rho := rho) center ∧
        x ∈ ν.support.filter (fun z => AtomicLaw.distToFinset z C ≤ rho) := by
  classical
  have hcenter_ne : center.support.Nonempty := cluster_support_nonempty hcenter
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, hdist⟩ := cluster_distToFinset_attained x hcenter_ne
    have hxy : |x - y| ≤ rho := hdist ▸ hclose.1 x hx
    let C := componentOf (rho := rho) center y
    have hyC : y ∈ C := cluster_componentOf_mem_self hy
    refine ⟨C, ⟨Finset.mem_image.mpr ⟨y, hy, rfl⟩,
      Finset.mem_filter.mpr ⟨hx, (cluster_distToFinset_le_of_mem x hyC).trans hxy⟩⟩, ?_⟩
    intro D hD
    have hDne : D.Nonempty := by
      obtain ⟨root, hroot, hDr⟩ := Finset.mem_image.mp hD.1
      rw [← hDr]
      exact ⟨root, cluster_componentOf_mem_self hroot⟩
    obtain ⟨z, hz, hxz⟩ := cluster_distToFinset_attained x hDne
    have hxz_le : |x - z| ≤ rho := hxz ▸ (Finset.mem_filter.mp hD.2).2
    have hzSupp : z ∈ center.support := by
      obtain ⟨root, hroot, hDr⟩ := Finset.mem_image.mp hD.1
      apply cluster_componentOf_subset_support center root
      rw [hDr]
      exact hz
    have hlink : linked (rho := rho) center y z := by
      refine ⟨hy, hzSupp, ?_⟩
      calc
        |y - z| ≤ |y - x| + |x - z| := abs_sub_le y x z
        _ ≤ 2 * rho := by rw [abs_sub_comm y x]; linarith
        _ ≤ 4 * rho := by linarith
    calc
      D = componentOf (rho := rho) center z :=
        cluster_component_eq_componentOf_of_mem hD.1 hz
      _ = C := (cluster_componentOf_eq_of_linked hlink).symm
  · rintro ⟨C, ⟨hC, hx⟩, huniq⟩
    exact (Finset.mem_filter.mp hx).1

-- @node: cluster_extrema_contain_and_width
lemma cluster_extrema_contain_and_width {S : Set ℝ} {m B : ℝ}
    (hm : m ∈ S) (hB : 0 ≤ B) (hbound : ∀ x ∈ S, |x - m| ≤ B) :
    sInf S ≤ m ∧ m ≤ sSup S ∧ sSup S - sInf S ≤ 2 * B := by
  have hbelow : BddBelow S := by
    refine ⟨m - B, ?_⟩
    intro x hx
    have := hbound x hx
    rw [abs_le] at this
    linarith
  have habove : BddAbove S := by
    refine ⟨m + B, ?_⟩
    intro x hx
    have := hbound x hx
    rw [abs_le] at this
    linarith
  refine ⟨csInf_le hbelow hm, le_csSup habove hm, ?_⟩
  have hsup : sSup S ≤ m + B := csSup_le ⟨m, hm⟩ fun x hx => by
    have := hbound x hx
    rw [abs_le] at this
    linarith
  have hinf : m - B ≤ sInf S := le_csInf ⟨m, hm⟩ fun x hx => by
    have := hbound x hx
    rw [abs_le] at this
    linarith
  linarith

-- @node: cluster_externalGap_le_cross
lemma cluster_externalGap_le_cross {k : ℕ} {radius rho : ℝ}
    {ν : AtomicLaw k radius} {C : Finset ℝ}
    (hgapTop : clusterExternalGap (rho := rho) ν C ≠ ⊤)
    {x y : ℝ} (hx : x ∈ associatedSupport (rho := rho) ν C)
    (hy : y ∈ ν.support) (hyout : y ∉ associatedSupport (rho := rho) ν C) :
    (clusterExternalGap (rho := rho) ν C).toReal ≤ |x - y| := by
  have hcomp : (ν.support \ associatedSupport (rho := rho) ν C).Nonempty := by
    exact ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyout⟩⟩
  have hle : clusterExternalGap (rho := rho) ν C ≤ (|x - y| : ℝ) := by
    rw [clusterExternalGap, if_pos hcomp]
    apply sInf_le
    exact ⟨x, hx, y, hy, hyout, rfl⟩
  apply EReal.toReal_le_toReal hle
  · intro hbot
    have hnonneg : (0 : EReal) ≤ clusterExternalGap (rho := rho) ν C := by
      rw [clusterExternalGap, if_pos hcomp]
      apply le_sInf
      intro d hd
      rcases hd with ⟨a, ha, b, hb, hbout, rfl⟩
      positivity
    rw [hbot] at hnonneg
    exact (not_le_of_gt EReal.bot_lt_zero) hnonneg
  · simp

-- @node: cluster_externalGap_nonneg
lemma cluster_externalGap_nonneg {k : ℕ} {radius rho : ℝ}
    (ν : AtomicLaw k radius) (C : Finset ℝ) :
    (0 : EReal) ≤ clusterExternalGap (rho := rho) ν C := by
  unfold clusterExternalGap
  split_ifs
  · apply le_sInf
    intro d hd
    rcases hd with ⟨x, hx, y, hy, hyout, rfl⟩
    positivity
  · exact le_top

-- @node: cluster_externalGap_toReal_pos
lemma cluster_externalGap_toReal_pos {k : ℕ} {radius rho : ℝ}
    {ν : AtomicLaw k radius} {C : Finset ℝ}
    (hA : (associatedSupport (rho := rho) ν C).Nonempty)
    (htop : clusterExternalGap (rho := rho) ν C ≠ ⊤) :
    0 < (clusterExternalGap (rho := rho) ν C).toReal := by
  let A := associatedSupport (rho := rho) ν C
  let B := ν.support
  let D : Set EReal := {d | ∃ x ∈ A, ∃ y ∈ B, y ∉ A ∧ d = |x - y|}
  have hcomp : (B \ A).Nonempty := by
    by_contra he
    have hempty : B \ A = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have : clusterExternalGap (rho := rho) ν C = ⊤ := by
      rw [clusterExternalGap, if_neg]
      simpa [A, B, hempty]
    exact htop this
  have hDne : D.Nonempty := by
    obtain ⟨x, hx⟩ := hA
    obtain ⟨y, hy⟩ := hcomp
    exact ⟨(|x - y| : ℝ), x, hx, y, (Finset.mem_sdiff.mp hy).1,
      (Finset.mem_sdiff.mp hy).2, rfl⟩
  have hDfin : D.Finite := by
    let F := A.product B
    have hsub : D ⊆ (fun p : ℝ × ℝ => ((|p.1 - p.2| : ℝ) : EReal)) '' (F : Set (ℝ × ℝ)) := by
      rintro d ⟨x, hx, y, hy, hyout, rfl⟩
      exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
    exact (F.finite_toSet.image _).subset hsub
  have hmin := hDne.csInf_mem hDfin
  rcases hmin with ⟨x, hx, y, hy, hyout, hEq⟩
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hyout hx
  have hInfPos : (0 : EReal) < sInf D := by
    rw [hEq]
    exact_mod_cast (abs_pos.mpr (sub_ne_zero.mpr hxy))
  have hdef : clusterExternalGap (rho := rho) ν C = sInf D := by
    rw [clusterExternalGap, if_pos (by simpa [A, B] using hcomp)]
  apply EReal.toReal_pos
  · rwa [hdef]
  · exact htop

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
