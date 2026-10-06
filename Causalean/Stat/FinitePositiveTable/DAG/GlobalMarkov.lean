module
public import Causalean.Stat.FinitePositiveTable.DAG.Fixing
public import Causalean.Stat.FinitePositiveTable.DAG.KernelMarkov

/-!
# Global Markov theorems for sequentially fixed finite DAG tables

This module exposes the headline API.  Sequential graph-independent fixing of distinct DAG
vertices is first identified with the truncated local-factor product; d-separation in the DAG
with incoming arrows to those fixed vertices removed then yields multiplicative finite-kernel
conditional independence.  Both a set-valued core and singleton consumer forms are provided.
-/

public section

open Finset

noncomputable section

namespace Causalean.Stat.FinitePositiveTable.DAG

open Causalean.Graph
open Causalean.Stat.FinitePositiveTable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {r : V → ℕ}
variable {G : DAG V} {p : PositiveTable r}

namespace PositiveDAGTableFactorization

/-- A [factorized table](hyp:fac), [distinct fixed-vertex list](hyp:vertices,hvertices), [three
remaining coordinate sets](hyp:X,Y,Z), [proofs that each is remaining](hyp:hX,hY,hZ), and
[d-separation after removing incoming arrows to fixed vertices](hyp:hdSep) give [the atomwise
multiplicative conditional-independence identity for the sequentially fixed kernel](goal). -/
theorem fixSequence_globalMarkov
    (fac : PositiveDAGTableFactorization G p) (vertices : List V)
    (hvertices : vertices.Nodup) (X Y Z : Finset V)
    (hX : X ⊆ Finset.univ \ vertices.toFinset)
    (hY : Y ⊆ Finset.univ \ vertices.toFinset)
    (hZ : Z ⊆ Finset.univ \ vertices.toFinset)
    (hdSep : (arrowheadRemovedDAG G vertices.toFinset).dSep
      X Y (Z ∪ vertices.toFinset)) :
    FixedKernelCondIndep
      (fixSequence p (parentFixingSteps G vertices)) vertices.toFinset X Y Z := by
  rw [fixSequence_eq_remainingFactorKernel fac vertices hvertices]
  exact fac.remainingFactorKernel_globalMarkov vertices.toFinset X Y Z
    hX hY hZ hdSep

/-- A [factorized table](hyp:fac), [distinct fixed-vertex list](hyp:vertices,hvertices), [two
vertices and a random conditioning set](hyp:a,b,Z), [proofs that both vertices remain](hyp:ha,hb),
[proof that the conditioning set remains random](hyp:hZ), and [the corresponding d-separation](hyp:hdSep)
give [singleton multiplicative conditional independence after sequential fixing](goal). -/
theorem fixSequence_singleton_globalMarkov
    (fac : PositiveDAGTableFactorization G p) (vertices : List V)
    (hvertices : vertices.Nodup) (a b : V) (Z : Finset V)
    (ha : a ∉ vertices.toFinset) (hb : b ∉ vertices.toFinset)
    (hZ : Z ⊆ Finset.univ \ vertices.toFinset)
    (hdSep : (arrowheadRemovedDAG G vertices.toFinset).dSep
      {a} {b} (Z ∪ vertices.toFinset)) :
    FixedKernelCondIndep
      (fixSequence p (parentFixingSteps G vertices))
      vertices.toFinset {a} {b} Z := by
  exact fac.fixSequence_globalMarkov vertices hvertices {a} {b} Z
    (by
      intro v hv
      rw [Finset.mem_singleton] at hv
      subst v
      simp [ha])
    (by
      intro v hv
      rw [Finset.mem_singleton] at hv
      subst v
      simp [hb])
    hZ hdSep

/-- A [factorized table](hyp:fac), [distinct fixed-vertex list](hyp:vertices,hvertices), [two
distinct remaining vertices](hyp:a,b,ha,hb,hab), and [d-separation by all other random and fixed
vertices](hyp:hdSep) give [the existing singleton kernel cross-product identity after sequential
fixing](goal). -/
theorem fixSequence_kernelCondIndep
    (fac : PositiveDAGTableFactorization G p) (vertices : List V)
    (hvertices : vertices.Nodup) (a b : V)
    (ha : a ∉ vertices.toFinset) (hb : b ∉ vertices.toFinset)
    (hab : a ≠ b)
    (hdSep : (arrowheadRemovedDAG G vertices.toFinset).dSep {a} {b}
      ((((Finset.univ \ vertices.toFinset).erase a).erase b) ∪
        vertices.toFinset)) :
    KernelCondIndep (fixSequence p (parentFixingSteps G vertices)) a b := by
  apply (fixedKernelCondIndep_complement_iff_kernelCondIndep
    (fixSequence p (parentFixingSteps G vertices)) vertices.toFinset a b
    ha hb hab).mp
  exact fac.fixSequence_singleton_globalMarkov vertices hvertices a b
    (((Finset.univ \ vertices.toFinset).erase a).erase b) ha hb
    (by intro v hv; simp only [Finset.mem_erase] at hv ⊢; exact hv.2.2) hdSep

end PositiveDAGTableFactorization

end Causalean.Stat.FinitePositiveTable.DAG
