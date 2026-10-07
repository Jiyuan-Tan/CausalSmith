module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.Curve
public import Causalean.Mathlib.Topology.SpaceFillingCurve.Pairing

/-!
# Finite cube matching from a Hölder traversal

Pull finite cube points back to interval parameters, sort the parameters,
pair adjacent values, and apply the squared Hölder modulus and concavity.
-/

public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- Given [a cube dimension and family size](hyp:d,N), [a dimension of at least two](hyp:hd), [an even family of at least two labels](hyp:hN,hN2),
and [unit-cube points at those labels](hyp:x,hx), [there is a perfect pairing of the labels whose total squared Euclidean distance between paired points is at most 16·d·N^(1 − 2/d)](goal). -/
theorem exists_perfectPairing_sqEuclidean_cost_le
    (d N : ℕ) (hd : 2 ≤ d) (hN : Even N) (hN2 : 2 ≤ N)
    (x : Fin N → Fin d → ℝ) (hx : ∀ i, InUnitCube (x i)) :
    ∃ M : PerfectPairing N,
      (∑ j : Fin (N / 2),
        sqEuclideanDist (x (M.edge j).1) (x (M.edge j).2)) ≤
        16 * (d : ℝ) * (N : ℝ) ^ (1 - (2 : ℝ) / d) := by
  obtain ⟨C⟩ := exists_holderCubeCurve d hd
  let t : Fin N → ℝ := fun i => Classical.choose (C.surjectiveOn (x i) (hx i))
  have ht (i : Fin N) : t i ∈ Set.Icc (0 : ℝ) 1 :=
    (Classical.choose_spec (C.surjectiveOn (x i) (hx i))).1
  have hxt (i : Fin N) : C.toFun (t i) = x i :=
    (Classical.choose_spec (C.surjectiveOn (x i) (hx i))).2
  obtain ⟨M, hgap⟩ := exists_pairing_gap_le_one N hN hN2 t ht
  refine ⟨M, ?_⟩
  let p : ℝ := (2 : ℝ) / d
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_iff₀ hdpos).2
    norm_num
    exact_mod_cast hd
  have hq : 0 ≤ 1 - p := by linarith
  have hm : 0 < N / 2 := by omega
  have hnonneg (j : Fin (N / 2)) :
      0 ≤ |t (M.edge j).1 - t (M.edge j).2| := abs_nonneg _
  have hpow := sum_rpow_le_card_rpow hm p hp0 hp1
    (fun j => |t (M.edge j).1 - t (M.edge j).2|) hnonneg hgap
  have hedge (j : Fin (N / 2)) :
      sqEuclideanDist (x (M.edge j).1) (x (M.edge j).2) ≤
        16 * (d : ℝ) * |t (M.edge j).1 - t (M.edge j).2| ^ p := by
    rw [← hxt (M.edge j).1, ← hxt (M.edge j).2]
    exact C.modulus (ht _) (ht _)
  have hcoeff : 0 ≤ 16 * (d : ℝ) := by positivity
  have hbase : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_le_self N 2
  calc
    (∑ j : Fin (N / 2), sqEuclideanDist (x (M.edge j).1) (x (M.edge j).2))
        ≤ ∑ j : Fin (N / 2), 16 * (d : ℝ) *
            |t (M.edge j).1 - t (M.edge j).2| ^ p :=
      Finset.sum_le_sum (fun j _ => hedge j)
    _ = 16 * (d : ℝ) * (∑ j : Fin (N / 2),
          |t (M.edge j).1 - t (M.edge j).2| ^ p) := by
      rw [Finset.mul_sum]
    _ ≤ 16 * (d : ℝ) * ((N / 2 : ℕ) : ℝ) ^ (1 - p) :=
      mul_le_mul_of_nonneg_left hpow hcoeff
    _ ≤ 16 * (d : ℝ) * (N : ℝ) ^ (1 - p) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbase hq) hcoeff
    _ = _ := rfl

end Causalean.Mathlib.Topology.SpaceFillingCurve
