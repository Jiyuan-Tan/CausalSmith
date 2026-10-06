module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedCellPushforward
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedScoreAlgebra

/-! # Identification of folded-score one-dimensional slices -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

noncomputable def meshTransverseBump (h : ℝ) (k : Fin d → ℕ)
    (x : XSpace d) : ℝ :=
  ∏ i : Fin d, if i.val = 0 then (1 : ℝ)
    else foldedTransverseBump (x i / h - k i)

lemma meshBump_factor_first_transverse (hd : 0 < d) (h : ℝ)
    (k : Fin d → ℕ) (x : XSpace d) :
    meshBump hd h k x =
      foldedFirstBump (x ⟨0, hd⟩ / h - k ⟨0, hd⟩) *
        meshTransverseBump h k x := by
  unfold meshBump meshTransverseBump
  rfl

lemma meshTransverseBump_mem_Icc (h : ℝ) (k : Fin d → ℕ) (x : XSpace d) :
    meshTransverseBump h k x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold meshTransverseBump
  constructor
  · exact Finset.prod_nonneg fun i _ => by
      split
      · norm_num
      · exact foldedTransverseBump_nonneg _
  · apply Finset.prod_le_one
    · exact fun i _ => by
        split
        · norm_num
        · exact foldedTransverseBump_nonneg _
    · exact fun i _ => by
        split
        · norm_num
        · exact foldedTransverseBump_le_one _

lemma foldedFirstBump_eq_zero_off_nat_cell {z : ℝ} (k l : ℕ)
    (hz : z ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) (hkl : l ≠ k) :
    foldedFirstBump (z - l) = 0 := by
  rcases lt_or_gt_of_ne hkl with hlk | hkl'
  · apply foldedFirstBump_eq_zero_of_ge
    have hsucc : l + 1 ≤ k := Nat.succ_le_of_lt hlk
    have hsuccR : (l : ℝ) + 1 ≤ k := by exact_mod_cast hsucc
    linarith [hz.1]
  · apply foldedFirstBump_eq_zero_of_le
    have hsucc : k + 1 ≤ l := Nat.succ_le_of_lt hkl'
    have hsuccR : (k : ℝ) + 1 ≤ l := by exact_mod_cast hsucc
    linarith [hz.2]

noncomputable def meshCellTransverseCoefficient (hd : 0 < d) (h : ℝ)
    (idx : Fin K → Fin d → ℕ) (θ : Fin K → Bool) (x : XSpace d)
    (k : ℕ) : ℝ :=
  ∑ j : Fin K, if idx j ⟨0, hd⟩ = k then
    localSign (θ j) * meshTransverseBump h (idx j) x else 0

lemma signed_meshBump_sum_factor_cell (hd : 0 < d) {h : ℝ}
    (idx : Fin K → Fin d → ℕ) (θ : Fin K → Bool) (x : XSpace d) (k : ℕ)
    (hx : x ⟨0, hd⟩ / h ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) :
    (∑ j : Fin K, localSign (θ j) * meshBump hd h (idx j) x) =
      meshCellTransverseCoefficient hd h idx θ x k *
        foldedFirstBump (x ⟨0, hd⟩ / h - k) := by
  classical
  unfold meshCellTransverseCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [meshBump_factor_first_transverse]
  by_cases heq : idx j ⟨0, hd⟩ = k
  · simp only [heq, if_true]
    ring
  · simp only [heq, if_false, zero_mul]
    rw [foldedFirstBump_eq_zero_off_nat_cell k (idx j ⟨0, hd⟩) hx]
    · ring
    · exact heq

lemma meshTransverseBump_disjoint_same_first (hd : 0 < d) {h : ℝ}
    {idx : Fin K → Fin d → ℕ} (hinj : Function.Injective idx)
    {i j : Fin K} (hij : i ≠ j)
    (hfirst : idx i ⟨0, hd⟩ = idx j ⟨0, hd⟩) (x : XSpace d)
    (hi : meshTransverseBump h (idx i) x ≠ 0) :
    meshTransverseBump h (idx j) x = 0 := by
  classical
  by_contra hj
  have hidx : idx i ≠ idx j := fun heq => hij (hinj heq)
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hidx
  have ht0 : t.val ≠ 0 := by
    intro htzero
    have teq : t = ⟨0, hd⟩ := Fin.ext htzero
    subst t
    exact ht hfirst
  have hit : foldedTransverseBump (x t / h - idx i t) ≠ 0 := by
    have hp := Finset.prod_ne_zero_iff.mp hi t (Finset.mem_univ t)
    simpa [meshTransverseBump, ht0] using hp
  have hjt : foldedTransverseBump (x t / h - idx j t) ≠ 0 := by
    have hp := Finset.prod_ne_zero_iff.mp hj t (Finset.mem_univ t)
    simpa [meshTransverseBump, ht0] using hp
  have hiS := foldedTransverseBump_support hit
  have hjS := foldedTransverseBump_support hjt
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · have hsucc : idx i t + 1 ≤ idx j t := Nat.succ_le_of_lt hlt
    have hsuccR : (idx i t : ℝ) + 1 ≤ idx j t := by exact_mod_cast hsucc
    linarith [hiS.2, hjS.1]
  · have hsucc : idx j t + 1 ≤ idx i t := Nat.succ_le_of_lt hgt
    have hsuccR : (idx j t : ℝ) + 1 ≤ idx i t := by exact_mod_cast hsucc
    linarith [hiS.1, hjS.2]

lemma meshCellTransverseCoefficient_abs_le_one (hd : 0 < d) {h : ℝ}
    {idx : Fin K → Fin d → ℕ} (hinj : Function.Injective idx)
    (θ : Fin K → Bool) (x : XSpace d) (k : ℕ) :
    |meshCellTransverseCoefficient hd h idx θ x k| ≤ 1 := by
  classical
  by_cases hex : ∃ j : Fin K,
      idx j ⟨0, hd⟩ = k ∧ meshTransverseBump h (idx j) x ≠ 0
  · obtain ⟨j, hjfirst, hjne⟩ := hex
    unfold meshCellTransverseCoefficient
    rw [Finset.sum_eq_single j]
    · simp only [hjfirst, if_true, abs_mul, abs_localSign, one_mul]
      rw [abs_of_nonneg (meshTransverseBump_mem_Icc h (idx j) x).1]
      exact (meshTransverseBump_mem_Icc h (idx j) x).2
    · intro i hi hij
      by_cases hifirst : idx i ⟨0, hd⟩ = k
      · have hzero := meshTransverseBump_disjoint_same_first hd hinj hij.symm
          (hjfirst.trans hifirst.symm) x hjne
        simp [hifirst, hzero]
      · simp [hifirst]
    · simp
  · unfold meshCellTransverseCoefficient
    have hz (j : Fin K) :
        (if idx j ⟨0, hd⟩ = k then
          localSign (θ j) * meshTransverseBump h (idx j) x else 0) = 0 := by
      by_cases hj : idx j ⟨0, hd⟩ = k
      · simp only [hj, if_true]
        have : meshTransverseBump h (idx j) x = 0 := by
          by_contra hn
          exact hex ⟨j, hj, hn⟩
        rw [this, mul_zero]
      · simp [hj]
    simp_rw [hz]
    simp

lemma FoldedGeometry.exists_signed_cell_coefficient {hd : 0 < d} {q K : ℕ}
    {Q : Fin K → Set (XSpace d)} {ψ : Fin K → XSpace d → ℝ}
    {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q ψ B) (θ : Fin K → Bool)
    (x : XSpace d) (k : ℕ)
    (hx : x ⟨0, hd⟩ / (q : ℝ)⁻¹ ∈
      Set.Icc (k : ℝ) ((k : ℝ) + 1)) :
    ∃ c ∈ Set.Icc (-1 : ℝ) 1,
      (∑ j : Fin K, localSign (θ j) * ψ j x) =
        c * foldedFirstBump (x ⟨0, hd⟩ / (q : ℝ)⁻¹ - k) := by
  rcases hgeo with ⟨hq, idx, hinj, hcomplete, hdefs⟩
  let c := meshCellTransverseCoefficient hd (q : ℝ)⁻¹ idx θ x k
  refine ⟨c, ?_, ?_⟩
  · exact (abs_le).mp (meshCellTransverseCoefficient_abs_le_one hd hinj θ x k)
  · simp_rw [(hdefs _).2.1]
    exact signed_meshBump_sum_factor_cell hd idx θ x k hx

/-- Algebraic bridge from the multivariate hypercube formula to the signed
one-cell map.  Geometry is used separately only to produce the factorization
`hpert` and the bound `|c| ≤ 1`. -/
-- keep: reusable algebraic bridge from multivariate scores to one-cell maps
lemma foldedRawScore_eq_perturbed_cell {d K : ℕ} (hd : 0 < d)
    {β h κ ε : ℝ} (hβ : β < 1) (hh : 0 < h) (ψ : Fin K → XSpace d → ℝ)
    (θ : Fin K → Bool) (x : XSpace d) (k : ℕ) (r c : ℝ)
    (hx1 : x ⟨0, hd⟩ = ((k : ℝ) + r) * h)
    (hpert : (∑ j : Fin K, localSign (θ j) * ψ j x) =
      c * foldedFirstBump r) :
    foldedRawScore hd β h κ ε K ψ θ x =
      1 / 4 + 1 / 2 * triangularFold
        (perturbedTriangularCell k h (κ * h ^ β) ε c r) := by
  simp only [foldedRawScore, hβ, if_pos]
  rw [hx1, hpert]
  have hratio : ((k : ℝ) + r) * h / h = (k : ℝ) + r := by
    field_simp [hh.ne']
  rw [hratio]
  rw [perturbedTriangularCell_def]
  ring

/-- The signed transverse coefficient is automatically bounded when it is a
single hypercube sign times a `[0,1]` transverse bump. -/
-- keep: reusable coefficient bound for signed transverse bumps
lemma signed_transverse_coefficient_mem_Icc (b : Bool) {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) : localSign b * c ∈ Set.Icc (-1 : ℝ) 1 := by
  apply (abs_le).mp
  rw [abs_mul, abs_localSign, abs_of_nonneg hc.1, one_mul]
  exact hc.2

end CausalSmith.Experimentation.PilotscorePairingFrontier
