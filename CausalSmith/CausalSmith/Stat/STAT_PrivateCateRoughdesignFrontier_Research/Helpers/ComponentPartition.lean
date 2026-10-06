module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentCoupling
/-! The ordered shared-sign components partition the dataset indices. Distinct components
use disjoint active sign coordinates. Conditional likelihoods depend only on those coordinates. -/
public section
open MeasureTheory ProbabilityTheory Set
namespace CausalSmith.Stat.PrivateCateRoughdesign
variable (hL : ℝ) (n : ℕ)

/-- Component membership is exactly reachability in the shared-sign graph.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,i,l). -/
-- @node: mem_componentVertices
lemma mem_componentVertices (x : Fin n → Covariate) (i l : Fin n) :
    l ∈ componentVertices hL n x i ↔ (sharedGraph hL n x).Reachable i l := by
  classical
  simp [componentVertices]

/-- Every vertex belongs to its own component.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,i). -/
-- @node: self_mem_componentVertices
lemma self_mem_componentVertices (x : Fin n → Covariate) (i : Fin n) :
    i ∈ componentVertices hL n x i :=
  (mem_componentVertices hL n x i i).mpr .rfl

/-- Reachable vertices select the same component. The result uses [the stated assumptions](hyp:hil) and establishes [the displayed conclusion](goal). -/
-- @node: componentVertices_eq_of_reachable
lemma componentVertices_eq_of_reachable (x : Fin n → Covariate) (i l : Fin n)
    (hil : (sharedGraph hL n x).Reachable i l) :
    componentVertices hL n x i = componentVertices hL n x l := by
  ext v
  rw [mem_componentVertices, mem_componentVertices]
  exact ⟨fun hiv => hil.symm.trans hiv, fun hlv => hil.trans hlv⟩

/-- Two components either coincide or are disjoint.  [the theorem's stated inputs and assumptions](hyp:hil), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,i,l). -/
-- @node: componentVertices_disjoint_of_not_reachable
lemma componentVertices_disjoint_of_not_reachable (x : Fin n → Covariate) (i l : Fin n)
    (hil : ¬(sharedGraph hL n x).Reachable i l) :
    Disjoint (componentVertices hL n x i) (componentVertices hL n x l) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hiv hlv
  exact hil (((mem_componentVertices hL n x i v).mp hiv).trans
    ((mem_componentVertices hL n x l v).mp hlv).symm)

/-- Component roots are precisely the least vertices of their reachable classes.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,i). -/
-- @node: mem_componentRoots
lemma mem_componentRoots (x : Fin n → Covariate) (i : Fin n) :
    i ∈ componentRoots hL n x ↔ ∀ l, (sharedGraph hL n x).Reachable i l → i ≤ l := by
  classical
  simp [componentRoots]

/-- Every vertex has a component root in its reachable class.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,i). -/
-- @node: exists_componentRoot
lemma exists_componentRoot (x : Fin n → Covariate) (i : Fin n) :
    ∃ r ∈ componentRoots hL n x, i ∈ componentVertices hL n x r := by
  classical
  let C := componentVertices hL n x i
  have hC : C.Nonempty := ⟨i, self_mem_componentVertices hL n x i⟩
  let r := C.min' hC
  have hir : (sharedGraph hL n x).Reachable i r :=
    (mem_componentVertices hL n x i r).mp (C.min'_mem hC)
  refine ⟨r, (mem_componentRoots hL n x r).mpr ?_,
    (mem_componentVertices hL n x r i).mpr hir.symm⟩
  intro l hrl
  exact C.min'_le l ((mem_componentVertices hL n x i l).mpr (hir.trans hrl))

/-- A reachable class has at most one selected least vertex.  [the theorem's stated inputs and assumptions](hyp:hi,hl,hil), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,i,l). -/
-- @node: componentRoots_eq_of_reachable
lemma componentRoots_eq_of_reachable (x : Fin n → Covariate) (i l : Fin n)
    (hi : i ∈ componentRoots hL n x) (hl : l ∈ componentRoots hL n x)
    (hil : (sharedGraph hL n x).Reachable i l) : i = l := by
  exact le_antisymm ((mem_componentRoots hL n x i).mp hi l hil)
    ((mem_componentRoots hL n x l).mp hl i hil.symm)

/-- Distinct selected roots have disjoint component vertex sets.  [the theorem's stated inputs and assumptions](hyp:hi,hl,hne), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,i,l). -/
-- @node: componentRoots_pairwise_disjoint
lemma componentRoots_pairwise_disjoint (x : Fin n → Covariate) (i l : Fin n)
    (hi : i ∈ componentRoots hL n x) (hl : l ∈ componentRoots hL n x) (hne : i ≠ l) :
    Disjoint (componentVertices hL n x i) (componentVertices hL n x l) := by
  apply componentVertices_disjoint_of_not_reachable
  intro hil
  exact hne (componentRoots_eq_of_reachable hL n x i l hi hl hil)

/-- The ordered list contains exactly the components of selected roots.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,C). -/
-- @node: mem_orderedComponents
lemma mem_orderedComponents (x : Fin n → Covariate) (C : Finset (Fin n)) :
    C ∈ orderedComponents hL n x ↔
      ∃ r ∈ componentRoots hL n x, componentVertices hL n x r = C := by
  classical
  simp [orderedComponents]

/-- The ordered components cover every dataset index.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,i). -/
-- @node: orderedComponents_cover
lemma orderedComponents_cover (x : Fin n → Covariate) (i : Fin n) :
    ∃ C ∈ orderedComponents hL n x, i ∈ C := by
  obtain ⟨r, hr, hi⟩ := exists_componentRoot hL n x i
  exact ⟨componentVertices hL n x r,
    (mem_orderedComponents hL n x _).mpr ⟨r, hr, rfl⟩, hi⟩

/-- Sharing an active sign connects the two records, including the identical-record case.  [the theorem's stated inputs and assumptions](hyp:j,hi,hl), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,i,l). -/
-- @node: reachable_of_shared_activeSign
lemma reachable_of_shared_activeSign (x : Fin n → Covariate) (i l : Fin n)
    (j : activeSigns hL)
    (hi : envelope hL (x i) * frame hL j (x i) ≠ 0)
    (hl : envelope hL (x l) * frame hL j (x l) ≠ 0) :
    (sharedGraph hL n x).Reachable i l := by
  by_cases heq : i = l
  · subst l
    exact .rfl
  · exact SimpleGraph.Adj.reachable (show (sharedGraph hL n x).Adj i l from
      ⟨heq, j, j.property, hi, hl⟩)

/-- Distinct graph components cannot use the same active sign coordinate.  [the theorem's stated inputs and assumptions](hyp:hrs,hi,hl,j,hij), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,r,s,i,l). -/
-- @node: component_activeSigns_disjoint
lemma component_activeSigns_disjoint (x : Fin n → Covariate) (r s i l : Fin n)
    (hrs : ¬(sharedGraph hL n x).Reachable r s)
    (hi : i ∈ componentVertices hL n x r) (hl : l ∈ componentVertices hL n x s)
    (j : activeSigns hL) (hij : envelope hL (x i) * frame hL j (x i) ≠ 0) :
    envelope hL (x l) * frame hL j (x l) = 0 := by
  by_contra hlj
  exact hrs (((mem_componentVertices hL n x r i).mp hi).trans
    ((reachable_of_shared_activeSign hL n x i l j hij hlj).trans
      ((mem_componentVertices hL n x s l).mp hl).symm))

/-- The perturbation depends only on signs with a nonzero envelope-weighted frame.  [the theorem's stated inputs and assumptions](hyp:hagree), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,lam',x). -/
-- @node: perturbation_eq_of_activeSigns_agree
lemma perturbation_eq_of_activeSigns_agree (lam lam' : SignVector hL) (x : Covariate)
    (hagree : ∀ j : activeSigns hL,
      envelope hL x * frame hL j x ≠ 0 → lam j = lam' j) :
    perturbation hL lam x = perturbation hL lam' x := by
  classical
  simp only [perturbation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : envelope hL x * frame hL j x = 0
  · calc
      _ = (2*bit (lam j)-1)*(envelope hL x * frame hL j x) := by ring
      _ = (2*bit (lam' j)-1)*(envelope hL x * frame hL j x) := by rw [hj]; ring
      _ = _ := by ring
  · rw [hagree j hj]

/-- The entire conditional likelihood, including its quadratic term, uses only active signs.  [the theorem's stated inputs and assumptions](hyp:x,a,y,hagree), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,lam'). -/
-- @node: conditionalLikelihood_eq_of_activeSigns_agree
lemma conditionalLikelihood_eq_of_activeSigns_agree (lam lam' : SignVector hL)
    (x : Covariate) (a y : Bool)
    (hagree : ∀ j : activeSigns hL,
      envelope hL x * frame hL j x ≠ 0 → lam j = lam' j) :
    conditionalLikelihood hL lam x a y = conditionalLikelihood hL lam' x a y := by
  simp only [conditionalLikelihood, altE, altMu0, altMu1,
    perturbation_eq_of_activeSigns_agree hL lam lam' x hagree]

/-- Every component in the ordered list contains its selected root.  [the theorem's stated inputs and assumptions](hyp:hC), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,C). -/
-- @node: orderedComponents_nonempty
lemma orderedComponents_nonempty (x : Fin n → Covariate) (C : Finset (Fin n))
    (hC : C ∈ orderedComponents hL n x) : C.Nonempty := by
  obtain ⟨r, _, rfl⟩ := (mem_orderedComponents hL n x C).mp hC
  exact ⟨r, self_mem_componentVertices hL n x r⟩

/-- Distinct members of the ordered component list are disjoint.  [the theorem's stated inputs and assumptions](hyp:hC,hD,hne), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,C,D). -/
-- @node: orderedComponents_disjoint
lemma orderedComponents_disjoint (x : Fin n → Covariate) (C D : Finset (Fin n))
    (hC : C ∈ orderedComponents hL n x) (hD : D ∈ orderedComponents hL n x)
    (hne : C ≠ D) : Disjoint C D := by
  obtain ⟨r, hr, rfl⟩ := (mem_orderedComponents hL n x C).mp hC
  obtain ⟨s, hs, rfl⟩ := (mem_orderedComponents hL n x D).mp hD
  apply componentRoots_pairwise_disjoint hL n x r s hr hs
  intro heq
  exact hne (congrArg (componentVertices hL n x) heq)

/-- The deterministic component ordering never repeats a component.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: orderedComponents_nodup
lemma orderedComponents_nodup (x : Fin n → Covariate) :
    (orderedComponents hL n x).Nodup := by
  classical
  apply List.Nodup.map_on _ (Finset.sort_nodup _ _)
  intro r hr s hs heq
  have hr' : r ∈ componentRoots hL n x := (Finset.mem_sort _).mp hr
  have hs' : s ∈ componentRoots hL n x := (Finset.mem_sort _).mp hs
  apply componentRoots_eq_of_reachable hL n x r s hr' hs'
  apply (mem_componentVertices hL n x r s).mp
  rw [heq]
  exact self_mem_componentVertices hL n x s

/-- Agreement on a component's active signs preserves its entire conditional mark product.  [the theorem's stated inputs and assumptions](hyp:C,z,lam,lam',hagree), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: componentLikelihood_eq_of_activeSigns_agree
lemma componentLikelihood_eq_of_activeSigns_agree (x : Fin n → Covariate)
    (C : Finset (Fin n)) (z : Marks C) (lam lam' : SignVector hL)
    (hagree : ∀ i : C, ∀ j : activeSigns hL,
      envelope hL (x i) * frame hL j (x i) ≠ 0 → lam j = lam' j) :
    (∏ i : C, conditionalLikelihood hL lam (x i) (z i).1 (z i).2 / 4) =
      ∏ i : C, conditionalLikelihood hL lam' (x i) (z i).1 (z i).2 / 4 := by
  classical
  apply Finset.prod_congr rfl
  intro i _
  rw [conditionalLikelihood_eq_of_activeSigns_agree hL lam lam' (x i)
    (z i).1 (z i).2 (hagree i)]
end CausalSmith.Stat.PrivateCateRoughdesign
