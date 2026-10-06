module
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedSimplex
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ScalarMomentPriors

/-!
# Product priors on balanced multinomial pairs

Independent finite scalar moment priors are replicated across balanced pairs
of alphabet cells. The product weights and exact target mean provide the
finite combinatorial layer of the large-sample fuzzy construction.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open scoped BigOperators ENNReal

/-- Select the scalar mass of a node from one of the two moment priors. -/
noncomputable def scalarPriorWeight {L : ℕ} (P : ScalarMomentPriors L)
    (side : Bool) (i : Fin P.m) : ℝ :=
  if side then P.w₁ i else P.w₀ i

/-- The independent product weight assigned to one vector of scalar nodes. -/
noncomputable def pairedProductWeight {L : ℕ} (P : ScalarMomentPriors L)
    (b : ℕ) (side : Bool) (u : Fin b → Fin P.m) : ℝ≥0∞ :=
  ∏ j, ENNReal.ofReal (scalarPriorWeight P side (u j))

/-- The real perturbation at each pair is the scalar node selected by the
corresponding coordinate of a product-prior index. -/
def pairedNodeVector {L : ℕ} (P : ScalarMomentPriors L)
    {b : ℕ} (u : Fin b → Fin P.m) : Fin b → ℝ :=
  fun j => P.node (u j)

/-- Each coordinate of a product-prior perturbation lies in `[-1,1]`. -/
theorem pairedNodeVector_abs_le_one {L : ℕ} (P : ScalarMomentPriors L)
    {b : ℕ} (u : Fin b → Fin P.m) (j : Fin b) :
    |pairedNodeVector P u j| ≤ 1 := by
  have h := P.node_mem (u j)
  exact abs_le.mpr ⟨h.1, h.2⟩

/-- The finite weights of either independent product prior sum to one.

`Fintype.prod_sum` factors the sum over coordinate functions. Convert each
real scalar weight sum to `ENNReal` using nonnegativity and `P.w₀_sum` or
`P.w₁_sum`; the resulting product is one, including when `b = 0`.
-/
theorem pairedProductWeight_sum {L : ℕ} (P : ScalarMomentPriors L)
    (b : ℕ) (side : Bool) :
    ∑ u : Fin b → Fin P.m, pairedProductWeight P b side u = 1 := by
  classical
  have hnonneg (i : Fin P.m) : 0 ≤ scalarPriorWeight P side i := by
    cases side <;> simp [scalarPriorWeight, P.w₀_nonneg, P.w₁_nonneg]
  have hscalar : ∑ i : Fin P.m, scalarPriorWeight P side i = 1 := by
    cases side <;> simp [scalarPriorWeight, P.w₀_sum, P.w₁_sum]
  have hsum : ∑ i : Fin P.m, ENNReal.ofReal (scalarPriorWeight P side i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i), hscalar]
    simp
  calc
    _ = ∏ _j : Fin b, ∑ i : Fin P.m, ENNReal.ofReal (scalarPriorWeight P side i) := by
      simpa [pairedProductWeight] using
        (Fintype.prod_sum (fun _j : Fin b => fun i : Fin P.m =>
          ENNReal.ofReal (scalarPriorWeight P side i))).symm
    _ = 1 := by simp [hsum]

/-- Given [a scalar moment prior](hyp:P), [a positive balanced pair count](hyp:b,hb), [a bounded nonnegative tilt](hyp:t,ht,ht1), and [a prior side](hyp:side), [the paired-product mean L1 target equals the scalar absolute-moment expression](goal). -/
theorem pairedProductTarget_mean {L : ℕ} (P : ScalarMomentPriors L)
    (b : ℕ) (hb : 0 < b)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (side : Bool) :
    ∑ u : Fin b → Fin P.m,
        (pairedProductWeight P b side u).toReal *
          simplexL1 (pairedBaseVector b hb)
            (pairedTiltVector b hb t ht ht1 (pairedNodeVector P u)
              (pairedNodeVector_abs_le_one P u)) =
      t * ∑ i : Fin P.m, scalarPriorWeight P side i * |P.node i| := by
  classical
  let w : Fin P.m → ℝ := scalarPriorWeight P side
  have hw (i : Fin P.m) : 0 ≤ w i := by
    dsimp [w]
    cases side <;> simp [scalarPriorWeight, P.w₀_nonneg, P.w₁_nonneg]
  have hwsum : ∑ i : Fin P.m, w i = 1 := by
    dsimp [w]
    cases side <;> simp [scalarPriorWeight, P.w₀_sum, P.w₁_sum]
  have hweight (u : Fin b → Fin P.m) :
      (pairedProductWeight P b side u).toReal = ∏ j : Fin b, w (u j) := by
    simp [pairedProductWeight, ENNReal.toReal_prod, ENNReal.toReal_ofReal (hw _), w]
  have hmarg (j : Fin b) :
      ∑ u : Fin b → Fin P.m, (∏ k : Fin b, w (u k)) * |P.node (u j)| =
        ∑ i : Fin P.m, w i * |P.node i| := by
    have hfactor (u : Fin b → Fin P.m) :
        (∏ k : Fin b, w (u k)) * |P.node (u j)| =
          ∏ k : Fin b, (if k = j then w (u k) * |P.node (u k)| else w (u k)) := by
      calc
        _ = (∏ k : Fin b, w (u k)) *
              ∏ k : Fin b, (if k = j then |P.node (u k)| else 1) := by simp
        _ = ∏ k : Fin b, w (u k) * (if k = j then |P.node (u k)| else 1) := by
          rw [Finset.prod_mul_distrib]
        _ = _ := by simp
    calc
      _ = ∑ u : Fin b → Fin P.m,
            ∏ k : Fin b, (if k = j then w (u k) * |P.node (u k)| else w (u k)) := by
          apply Finset.sum_congr rfl
          intro u _
          exact hfactor u
      _ = ∏ k : Fin b,
            ∑ i : Fin P.m, (if k = j then w i * |P.node i| else w i) := by
          exact (Fintype.prod_sum (fun k : Fin b => fun i : Fin P.m =>
            if k = j then w i * |P.node i| else w i)).symm
      _ = ∑ i : Fin P.m, w i * |P.node i| := by
          simp [hwsum, Finset.prod_ite_eq']
  simp_rw [pairedBase_tilt_l1, hweight]
  calc
    _ = (t / (b : ℝ)) * ∑ j : Fin b,
          ∑ u : Fin b → Fin P.m, (∏ k : Fin b, w (u k)) * |P.node (u j)| := by
      rw [Finset.mul_sum]
      calc
        _ = ∑ u : Fin b → Fin P.m, ∑ j : Fin b,
              t / (b : ℝ) * ((∏ k : Fin b, w (u k)) * |P.node (u j)|) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.mul_sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [pairedNodeVector]
          ring
        _ = ∑ j : Fin b, ∑ u : Fin b → Fin P.m,
              t / (b : ℝ) * ((∏ k : Fin b, w (u k)) * |P.node (u j)|) :=
          Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.mul_sum]
    _ = t * ∑ i : Fin P.m, scalarPriorWeight P side i * |P.node i| := by
      simp [hmarg, w]
      have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
      field_simp

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1
