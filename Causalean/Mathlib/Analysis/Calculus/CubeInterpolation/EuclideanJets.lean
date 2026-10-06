module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ProductJetSymmetry
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Multiindex

/-!
# Euclidean coordinate expansion and symmetry of within jets

Arbitrary-order Euclidean within derivatives expand along coordinate words.
On uniquely differentiable sets, finite within smoothness and approach from
the interior give permutation invariance. These analytic prerequisites use
neither word-fiber cardinality nor Taylor polynomial grouping, allowing their
proofs to be filled independently of the combinatorial and Legendre layers.

The coordinate expansion uses the multilinearity argument of
CubeInterpolation.Directional.diagonal_derivative_coordinate_expansion.
Permutation invariance reuses CubeExtension.ProductJetSymmetry through the
continuous linear equivalence between Euclidean and ordinary Pi coordinates.
-/

@[expose] public section

open scoped BigOperators Topology
noncomputable section
namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

open Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- The [ordered coordinate partial](goal) of [a function on its derivative domain](hyp:S,u) along
[a word of coordinates](hyp:w) at [an evaluation point](hyp:x) is [the iterated derivative taken
within the domain at that point, in the coordinate directions listed by the word](step:1). -/
def wordPartialWithin {d k : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (w : Fin k → Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  iteratedFDerivWithin ℝ k u S x (fun r => EuclideanSpace.single (w r) 1)

/-- For [a function on its derivative domain](hyp:S,u) and [a point a and a direction z](hyp:a,z),
[the order-k derivative within the domain at a, taken k times in the direction z, equals the sum
over all length-k coordinate words of the product of the matching coordinates of z times the
ordered coordinate partial along that word at a](goal). -/
theorem within_diagonal_derivative_coordinate_expansion {d k : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (a z : EuclideanSpace ℝ (Fin d)) :
    iteratedFDerivWithin ℝ k u S a (fun _ => z) =
      ∑ w : Fin k → Fin d, (∏ r, z (w r)) * wordPartialWithin S u w a := by
  -- Directional.diagonal_derivative_coordinate_expansion gives the existing
  -- Pi-space argument. Here apply ContinuousMultilinearMap.map_sum and
  -- map_smul_univ directly to F = iteratedFDerivWithin; reconstruct z as
  -- the sum of EuclideanSpace.single i (z i). This needs no regularity
  -- premise, since F is multilinear even when the derivative defaults to zero.
  classical
  let F := iteratedFDerivWithin ℝ k u S a
  have hz : (∑ i : Fin d, EuclideanSpace.single i (z i)) = z := by
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).injective
    rw [map_sum]
    change (∑ i : Fin d, Pi.single i (z i)) = (fun i => z i)
    exact Finset.univ_sum_single _
  calc
    F (fun _ => z) = F (fun _ => ∑ i : Fin d, EuclideanSpace.single i (z i)) := by
      rw [hz]
    _ = ∑ w : Fin k → Fin d, F (fun r => EuclideanSpace.single (w r) (z (w r))) :=
      F.map_sum (fun _ i => EuclideanSpace.single i (z i))
    _ = ∑ w : Fin k → Fin d, (∏ r, z (w r)) * wordPartialWithin S u w a := by
      apply Finset.sum_congr rfl
      intro w _
      have heq : (fun r => EuclideanSpace.single (w r) (z (w r))) =
          (fun r => z (w r) • EuclideanSpace.single (w r) (1 : ℝ)) := by
        funext r
        ext i
        simp [PiLp.single_apply]
      rw [heq, F.map_smul_univ]
      rfl

/-- If [a function is k times continuously differentiable on a set](hyp:hu) [on which derivatives
are unique](hyp:huniq), then at [a point of the set](hyp:ha) [lying in the closure of the set's
interior](hyp:hacl), [the order-k derivative within the set is unchanged when its directions are
reordered](goal) by [any permutation](hyp:σ) of [any k directions](hyp:v). -/
theorem euclidean_within_jet_perm {d k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin d))} (huniq : UniqueDiffOn ℝ S)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ k u S)
    {a : EuclideanSpace ℝ (Fin d)} (ha : a ∈ S)
    (hacl : a ∈ closure (interior S)) (σ : Equiv.Perm (Fin k))
    (v : Fin k → EuclideanSpace ℝ (Fin d)) :
    iteratedFDerivWithin ℝ k u S a (v ∘ σ) = iteratedFDerivWithin ℝ k u S a v := by
  -- Reuse ProductJetSymmetry.iteratedFDerivWithin_comp_perm_of_contDiffOn
  -- across e = PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ).
  -- ContinuousLinearEquiv.iteratedFDerivWithin_comp_right (ContDiff/Basic)
  -- transports evaluations through e and needs no added smoothness.
  -- Transport UniqueDiffOn and closure(interior S) through e.toHomeomorph;
  -- apply the Pi-space theorem to u ∘ e.symm on e.symm ⁻¹' S.
  -- Do not replace finite ContDiffOn regularity by analyticity or infinity.
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
  have huniq' : UniqueDiffOn ℝ (e.symm ⁻¹' S) :=
    e.symm.uniqueDiffOn_preimage_iff.mpr huniq
  have hu' : ContDiffOn ℝ k (u ∘ e.symm) (e.symm ⁻¹' S) :=
    e.symm.contDiffOn_comp_iff.mpr hu
  have ha' : e a ∈ e.symm ⁻¹' S := by simpa using ha
  have hacl' : e a ∈ closure (interior (e.symm ⁻¹' S)) := by
    change e a ∈ closure (interior (e.symm.toHomeomorph ⁻¹' S))
    rw [← e.symm.toHomeomorph.preimage_interior,
      ← e.symm.toHomeomorph.preimage_closure]
    change e.symm (e a) ∈ closure (interior S)
    simpa using hacl
  have hperm := iteratedFDerivWithin_comp_perm_of_contDiffOn
    huniq' hu' ha' hacl' σ (e ∘ v)
  rw [e.symm.iteratedFDerivWithin_comp_right u huniq (by simpa using ha) k] at hperm
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_def]
    using hperm

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
