module
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Data.ENNReal.Inv

/-! # Finite positive-semidefinite contrast information

This module gives a finite-index interface for constrained quadratic information and
generalized contrast variance of real positive-semidefinite matrices.  It includes the exact
reciprocal identity in singular cases, range and positivity characterizations, and monotonicity
under positive-semidefinite order.
-/

@[expose] public section

noncomputable section

namespace Causalean.Stat

open Matrix

variable {ι : Type*} [Fintype ι]

/-- A [real finite matrix](hyp:I) and [contrast](hyp:c) determine the
[constrained quadratic information](goal), [given by its quadratic-form infimum over
unit-contrast directions](step:1). -/
def constrainedInformation (I : Matrix ι ι ℝ) (c : ι → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ d : ι → ℝ, c ⬝ᵥ d = 1 ∧ r = d ⬝ᵥ I.mulVec d}

/-- A [real finite matrix](hyp:I) and [contrast](hyp:c) determine the
[generalized contrast variance](goal), [given by the least contrast pairing among solutions
and by infinity when no solution exists](step:1). -/
def generalizedContrastVariance (I : Matrix ι ι ℝ) (c : ι → ℝ) : ENNReal :=
  by
    classical
    exact if ∃ v : ι → ℝ, I.mulVec v = c then
      ENNReal.ofReal (sInf {r : ℝ | ∃ v : ι → ℝ, I.mulVec v = c ∧ r = c ⬝ᵥ v})
    else ⊤

/-- A [finite contrast](hyp:c) that is [nonzero](hyp:hc) has
[a direction with unit contrast pairing](goal). -/
theorem exists_unitContrastDirection (c : ι → ℝ) (hc : c ≠ 0) :
    ∃ d : ι → ℝ, c ⬝ᵥ d = 1 := by
  classical
  have hi : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  obtain ⟨i, hi⟩ := hi
  refine ⟨Pi.single i (c i)⁻¹, ?_⟩
  rw [dotProduct_single]
  exact mul_inv_cancel₀ hi

/-- A [positive-semidefinite matrix](hyp:hI) and a [nonzero contrast](hyp:hc)
have [nonnegative constrained quadratic information](goal). -/
theorem constrainedInformation_nonneg {I : Matrix ι ι ℝ} (hI : I.PosSemidef)
    {c : ι → ℝ} (hc : c ≠ 0) : 0 ≤ constrainedInformation I c := by
  unfold constrainedInformation
  apply le_csInf
  · obtain ⟨d, hd⟩ := exists_unitContrastDirection c hc
    exact ⟨d ⬝ᵥ I.mulVec d, d, hd, rfl⟩
  · rintro r ⟨d, -, rfl⟩
    simpa using hI.dotProduct_mulVec_nonneg d

/-- A [positive-semidefinite matrix](hyp:hI), a [nonzero contrast](hyp:hc), and
[a unit-contrast direction](hyp:hd) have [constrained information no larger than that
direction's quadratic energy](goal). -/
theorem constrainedInformation_le_quad {I : Matrix ι ι ℝ} (hI : I.PosSemidef)
    {c d : ι → ℝ} (hc : c ≠ 0) (hd : c ⬝ᵥ d = 1) :
    constrainedInformation I c ≤ d ⬝ᵥ I.mulVec d := by
  unfold constrainedInformation
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨e, -, rfl⟩
    simpa using hI.dotProduct_mulVec_nonneg e
  · exact ⟨d, hd, rfl⟩

/-- Two [positive-semidefinite matrices](hyp:hI,hJ) whose [difference in the stated
order is positive semidefinite](hyp:hIJ), at a [nonzero contrast](hyp:hc), have
[ordered constrained information](goal). -/
theorem constrainedInformation_mono {I J : Matrix ι ι ℝ} (hI : I.PosSemidef)
    (hJ : J.PosSemidef) (hIJ : (J - I).PosSemidef)
    {c : ι → ℝ} (hc : c ≠ 0) : constrainedInformation I c ≤ constrainedInformation J c := by
  unfold constrainedInformation
  apply le_csInf
  · obtain ⟨d, hd⟩ := exists_unitContrastDirection c hc
    exact ⟨d ⬝ᵥ J.mulVec d, d, hd, rfl⟩
  · rintro r ⟨d, hd, rfl⟩
    calc
      sInf {r : ℝ | ∃ e : ι → ℝ, c ⬝ᵥ e = 1 ∧ r = e ⬝ᵥ I.mulVec e}
          ≤ d ⬝ᵥ I.mulVec d := by
            apply csInf_le
            · refine ⟨0, ?_⟩
              rintro x ⟨e, -, rfl⟩
              simpa using hI.dotProduct_mulVec_nonneg e
            · exact ⟨d, hd, rfl⟩
      _ ≤ d ⬝ᵥ J.mulVec d := by
        have h := hIJ.dotProduct_mulVec_nonneg d
        simpa [Matrix.sub_mulVec, dotProduct_sub] using h

/-- A [real finite matrix](hyp:I) and [contrast](hyp:c) have
[nonnegative generalized contrast variance](goal). -/
theorem generalizedContrastVariance_nonneg (I : Matrix ι ι ℝ) (c : ι → ℝ) :
    0 ≤ generalizedContrastVariance I c :=
  bot_le

/-- A [positive-semidefinite matrix](hyp:hI) for which [the contrast equation has no
solution](hyp:hnone) has [a kernel direction with nonzero contrast pairing](goal). -/
theorem exists_kernel_nonorthogonal {I : Matrix ι ι ℝ} (hI : I.PosSemidef)
    {c : ι → ℝ} (hnone : ¬ ∃ v : ι → ℝ, I.mulVec v = c) :
    ∃ k : ι → ℝ, I.mulVec k = 0 ∧ c ⬝ᵥ k ≠ 0 := by
  classical
  let T := I.toEuclideanLin
  have hT : T.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hI.isHermitian
  by_contra h
  push Not at h
  have hcorth : (WithLp.toLp 2 c : EuclideanSpace ℝ ι) ∈ T.kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    have hk : I.mulVec (WithLp.ofLp x) = 0 := by
      have hx0 : T x = 0 := hx
      have := congrArg WithLp.ofLp hx0
      simpa [T, Matrix.toEuclideanLin_apply] using this
    have hck : c ⬝ᵥ WithLp.ofLp x = 0 := h _ hk
    simpa [EuclideanSpace.inner_eq_star_dotProduct] using hck
  rw [T.orthogonal_ker, hT.adjoint_eq] at hcorth
  obtain ⟨v, hv⟩ := hcorth
  apply hnone
  refine ⟨WithLp.ofLp v, ?_⟩
  have := congrArg WithLp.ofLp hv
  simpa [T, Matrix.toEuclideanLin_apply] using this

/-- A [positive-semidefinite matrix](hyp:hI), [nonzero contrast](hyp:hc), and
[kernel direction](hyp:hk) with [nonzero contrast pairing](hyp:hck) have
[zero constrained information](goal). -/
theorem constrainedInformation_eq_zero_of_kernel {I : Matrix ι ι ℝ} (hI : I.PosSemidef)
    {c k : ι → ℝ} (hc : c ≠ 0) (hk : I.mulVec k = 0)
    (hck : c ⬝ᵥ k ≠ 0) : constrainedInformation I c = 0 := by
  let d : ι → ℝ := (c ⬝ᵥ k)⁻¹ • k
  have hd : c ⬝ᵥ d = 1 := by
    simp [d, dotProduct_smul, inv_mul_cancel₀ hck]
  have hId : I.mulVec d = 0 := by
    simp [d, mulVec_smul, hk]
  apply le_antisymm
  · simpa [hId] using constrainedInformation_le_quad hI hc hd
  · exact constrainedInformation_nonneg hI hc

/-- A [positive-semidefinite matrix](hyp:hI), [nonzero contrast](hyp:hc), and
[unsolvable contrast equation](hyp:hnone) have [zero constrained information](goal). -/
theorem constrainedInformation_eq_zero_of_no_solution {I : Matrix ι ι ℝ} (hI : I.PosSemidef)
    {c : ι → ℝ} (hc : c ≠ 0)
    (hnone : ¬ ∃ v : ι → ℝ, I.mulVec v = c) : constrainedInformation I c = 0 := by
  obtain ⟨k, hk, hck⟩ := exists_kernel_nonorthogonal hI hnone
  exact constrainedInformation_eq_zero_of_kernel hI hc hk hck

/-- A [positive-semidefinite matrix](hyp:hI) and [two solutions to its contrast
equation](hyp:hv,hw) have [the same contrast pairing](goal). -/
theorem solution_dot_eq {I : Matrix ι ι ℝ} (hI : I.PosSemidef)
    {c v w : ι → ℝ} (hv : I.mulVec v = c) (hw : I.mulVec w = c) :
    c ⬝ᵥ v = c ⬝ᵥ w := by
  have hs : Iᵀ = I := by simpa using hI.isHermitian.eq
  calc
    c ⬝ᵥ v = (I.mulVec w) ⬝ᵥ v := by rw [hw]
    _ = w ⬝ᵥ I.mulVec v := by
      rw [dotProduct_comm]
      simpa [hs] using (Matrix.dotProduct_transpose_mulVec I w v).symm
    _ = c ⬝ᵥ w := by rw [hv, dotProduct_comm]

/-- A [positive-semidefinite matrix](hyp:hI), [nonzero contrast](hyp:hc), and
[solution to its contrast equation](hyp:hv) have [a strictly positive contrast pairing](goal). -/
theorem solution_dot_pos {I : Matrix ι ι ℝ} (hI : I.PosSemidef)
    {c v : ι → ℝ} (hc : c ≠ 0) (hv : I.mulVec v = c) :
    0 < c ⬝ᵥ v := by
  have hn : 0 ≤ c ⬝ᵥ v := by
    rw [← hv]
    simpa [dotProduct_comm] using hI.dotProduct_mulVec_nonneg v
  rcases hn.eq_or_lt with hz | hp
  · have hz' : v ⬝ᵥ I.mulVec v = 0 := by simpa [← hv, dotProduct_comm] using hz.symm
    exact False.elim (hc ((hI.dotProduct_mulVec_zero_iff v).mp hz' ▸ hv.symm))
  · exact hp

/-- A [positive-semidefinite matrix](hyp:hI), [nonzero contrast](hyp:hc), and
[solution to its contrast equation](hyp:hv) have [generalized contrast variance equal to
that solution's contrast pairing](goal). -/
theorem generalizedContrastVariance_eq_of_solution {I : Matrix ι ι ℝ} (hI : I.PosSemidef)
    {c v : ι → ℝ} (hc : c ≠ 0) (hv : I.mulVec v = c) :
    generalizedContrastVariance I c = ENNReal.ofReal (c ⬝ᵥ v) := by
  unfold generalizedContrastVariance
  rw [if_pos ⟨v, hv⟩]
  congr 1
  have hs : {r : ℝ | ∃ w : ι → ℝ, I.mulVec w = c ∧ r = c ⬝ᵥ w} =
      {c ⬝ᵥ v} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (solution_dot_eq hI hv hw).symm
    · rintro rfl
      exact ⟨v, hv, rfl⟩
  rw [hs, csInf_singleton]

/-- A [positive-semidefinite matrix](hyp:hI), [nonzero contrast](hyp:hc),
[solution to its contrast equation](hyp:hv), and [unit-contrast direction](hyp:hd) have
[the reciprocal solution pairing no greater than that direction's energy](goal). -/
theorem inv_solution_dot_le_quad {I : Matrix ι ι ℝ} (hI : I.PosSemidef)
    {c v d : ι → ℝ} (hc : c ≠ 0) (hv : I.mulVec v = c)
    (hd : c ⬝ᵥ d = 1) :
    (c ⬝ᵥ v)⁻¹ ≤ d ⬝ᵥ I.mulVec d := by
  let a := (c ⬝ᵥ v)⁻¹
  have hp := solution_dot_pos hI hc hv
  have ha : a * (c ⬝ᵥ v) = 1 := inv_mul_cancel₀ (ne_of_gt hp)
  have hs : Iᵀ = I := by simpa using hI.isHermitian.eq
  have hcross : v ⬝ᵥ I.mulVec d = 1 := by
    calc
      v ⬝ᵥ I.mulVec d = d ⬝ᵥ I.mulVec v := by
        simpa [hs] using Matrix.dotProduct_transpose_mulVec I v d
      _ = 1 := by rw [hv, dotProduct_comm, hd]
  have hsq : 0 ≤ (d - a • v) ⬝ᵥ I.mulVec (d - a • v) := by
    simpa only [TrivialStar.star_trivial] using hI.dotProduct_mulVec_nonneg (d - a • v)
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] at hsq
  simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul] at hsq
  have hdc : d ⬝ᵥ c = 1 := by simpa [dotProduct_comm] using hd
  rw [hv, hcross, hdc, dotProduct_comm v c] at hsq
  dsimp [a] at *
  nlinarith

/-- A [positive-semidefinite matrix](hyp:hI), [nonzero contrast](hyp:hc), and
[solution to its contrast equation](hyp:hv) have [a unit-contrast direction attaining
reciprocal solution energy](goal). -/
theorem exists_unitContrastDirection_energy_inv {I : Matrix ι ι ℝ} (hI : I.PosSemidef)
    {c v : ι → ℝ} (hc : c ≠ 0) (hv : I.mulVec v = c) :
    ∃ d : ι → ℝ, c ⬝ᵥ d = 1 ∧
      d ⬝ᵥ I.mulVec d = (c ⬝ᵥ v)⁻¹ := by
  let a := (c ⬝ᵥ v)⁻¹
  have hp := solution_dot_pos hI hc hv
  have ha : a * (c ⬝ᵥ v) = 1 := inv_mul_cancel₀ (ne_of_gt hp)
  refine ⟨a • v, ?_, ?_⟩
  · rw [dotProduct_smul, smul_eq_mul]
    exact ha
  · rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul, hv, dotProduct_comm]
    change a * (a * (c ⬝ᵥ v)) = a
    rw [ha, mul_one]

/-- A [positive-semidefinite matrix](hyp:hI), [nonzero contrast](hyp:hc), and
[solution to its contrast equation](hyp:hv) have [constrained information equal to
the reciprocal solution pairing](goal). -/
theorem constrainedInformation_eq_inv_of_solution {I : Matrix ι ι ℝ} (hI : I.PosSemidef)
    {c v : ι → ℝ} (hc : c ≠ 0) (hv : I.mulVec v = c) :
    constrainedInformation I c = (c ⬝ᵥ v)⁻¹ := by
  apply le_antisymm
  · obtain ⟨d, hd, he⟩ := exists_unitContrastDirection_energy_inv hI hc hv
    rw [← he]
    exact constrainedInformation_le_quad hI hc hd
  · unfold constrainedInformation
    apply le_csInf
    · obtain ⟨d, hd⟩ := exists_unitContrastDirection c hc
      exact ⟨d ⬝ᵥ I.mulVec d, d, hd, rfl⟩
    · rintro r ⟨d, hd, rfl⟩
      exact inv_solution_dot_le_quad hI hc hv hd

/-- A [positive-semidefinite matrix](hyp:hI) and [nonzero contrast](hyp:hc) have
[generalized contrast variance equal to the extended reciprocal of constrained information](goal). -/
theorem generalizedContrastVariance_eq_inv_constrainedInformation {I : Matrix ι ι ℝ}
    (hI : I.PosSemidef) {c : ι → ℝ} (hc : c ≠ 0) :
    generalizedContrastVariance I c = (ENNReal.ofReal (constrainedInformation I c))⁻¹ := by
  classical
  by_cases h : ∃ v : ι → ℝ, I.mulVec v = c
  · obtain ⟨v, hv⟩ := h
    rw [generalizedContrastVariance_eq_of_solution hI hc hv,
      constrainedInformation_eq_inv_of_solution hI hc hv,
      ENNReal.ofReal_inv_of_pos (solution_dot_pos hI hc hv), inv_inv]
  · simp [generalizedContrastVariance, h, constrainedInformation_eq_zero_of_no_solution hI hc h]

/-- A [positive-semidefinite matrix](hyp:hI) and [nonzero contrast](hyp:hc) have
[strictly positive constrained information exactly when their contrast equation is solvable](goal). -/
theorem constrainedInformation_pos_iff_solution {I : Matrix ι ι ℝ} (hI : I.PosSemidef)
    {c : ι → ℝ} (hc : c ≠ 0) :
    0 < constrainedInformation I c ↔ ∃ v : ι → ℝ, I.mulVec v = c := by
  constructor
  · intro hq
    by_contra h
    exact (ne_of_gt hq) (constrainedInformation_eq_zero_of_no_solution hI hc h)
  · rintro ⟨v, hv⟩
    rw [constrainedInformation_eq_inv_of_solution hI hc hv]
    exact inv_pos.mpr (solution_dot_pos hI hc hv)

/-- A [positive-semidefinite matrix](hyp:hI) and [nonzero contrast](hyp:hc) have
[infinite generalized contrast variance exactly when their contrast equation has no solution](goal). -/
theorem generalizedContrastVariance_eq_top_iff_no_solution {I : Matrix ι ι ℝ}
    (hI : I.PosSemidef) {c : ι → ℝ} (hc : c ≠ 0) :
    generalizedContrastVariance I c = ⊤ ↔ ¬ ∃ v : ι → ℝ, I.mulVec v = c := by
  classical
  constructor
  · intro htop h
    obtain ⟨v, hv⟩ := h
    rw [generalizedContrastVariance_eq_of_solution hI hc hv] at htop
    exact ENNReal.ofReal_ne_top htop
  · intro h
    simp [generalizedContrastVariance, h]

/-- A [positive-semidefinite matrix](hyp:hI), [nonzero contrast](hyp:hc), and
[strictly positive constrained information](hyp:hq) have [generalized contrast variance
equal to the extended-real reciprocal](goal). -/
theorem generalizedContrastVariance_eq_ofReal_inv_of_constrainedInformation_pos
    {I : Matrix ι ι ℝ} (hI : I.PosSemidef) {c : ι → ℝ} (hc : c ≠ 0)
    (hq : 0 < constrainedInformation I c) :
    generalizedContrastVariance I c = ENNReal.ofReal (constrainedInformation I c)⁻¹ := by
  rw [generalizedContrastVariance_eq_inv_constrainedInformation hI hc,
    ENNReal.ofReal_inv_of_pos hq]

/-- Two [positive-semidefinite matrices](hyp:hI,hJ) whose [difference in the stated
order is positive semidefinite](hyp:hIJ), at a [nonzero contrast](hyp:hc), have
[generalized contrast variance antitone under that order](goal). -/
theorem generalizedContrastVariance_antitone {I J : Matrix ι ι ℝ} (hI : I.PosSemidef)
    (hJ : J.PosSemidef) (hIJ : (J - I).PosSemidef)
    {c : ι → ℝ} (hc : c ≠ 0) :
    generalizedContrastVariance J c ≤ generalizedContrastVariance I c := by
  rw [generalizedContrastVariance_eq_inv_constrainedInformation hJ hc,
    generalizedContrastVariance_eq_inv_constrainedInformation hI hc]
  exact ENNReal.inv_le_inv'
    (ENNReal.ofReal_le_ofReal (constrainedInformation_mono hI hJ hIJ hc))

end Causalean.Stat
