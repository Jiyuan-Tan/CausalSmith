import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Basic.Occupancy
import Causalean.Mathlib.LinearAlgebra.MonomialMatrix
import Mathlib.Algebra.Module.Submodule.Union

/-!
# Uniqueness on overlapping environment sets

Two normalized BACKSHIFT explanations agreeing on a sufficiently rich overlap have the same
structural matrix.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

-- @node: overlap_card_lower_bound
/-- Two fitted environment sets, each missing at most `c` of the `m` labels, overlap in at
least `m - 2 * c` labels. [Under the stated hypotheses](hyp:H1,H2,h1,h2) [this conclusion](goal) applies. -/
lemma overlap_card_lower_bound {m c : ℕ}
    (H1 H2 : Finset (Environment m))
    (h1 : honestCount m c ≤ H1.card) (h2 : honestCount m c ≤ H2.card) :
    m - 2 * c ≤ (H1 ∩ H2).card := by
  have hunion : (H1 ∪ H2).card ≤ m := by
    simpa using (Finset.card_le_univ (s := H1 ∪ H2))
  have hcard := Finset.card_union_add_card_inter H1 H2
  simp only [honestCount] at h1 h2
  omega

/-- One fitted explanation satisfying the closed part of BACKSHIFT normalization. -/
structure WeakBackshiftExplanation (p m c : ℕ)
    (covarianceFamily : Environment m → RealMatrix p) where
  fitted : Finset (Environment m)
  fitted_card : honestCount m c ≤ fitted.card
  structural : RealMatrix p
  structural_invertible : IsUnit structural.det
  structural_unit_diagonal : ∀ i, structural i i = 1
  cycle_bound : cycleProduct (1 - structural) ≤ 1
  invariantNoise : RealMatrix p
  invariantNoise_psd : invariantNoise.PosSemidef
  shifts : Environment m → Fin p → ℝ
  shifts_nonnegative : ∀ e ∈ fitted, ∀ k, 0 ≤ shifts e k
  covariance_eq : ∀ e ∈ fitted,
    covarianceFamily e = structural⁻¹ *
      (invariantNoise + Matrix.diagonal (shifts e)) * structural⁻¹.transpose

/-- A fitted BACKSHIFT explanation with the strict cycle-product normalization. -/
structure BackshiftExplanation (p m c : ℕ)
    (covarianceFamily : Environment m → RealMatrix p)
    extends WeakBackshiftExplanation p m c covarianceFamily where
  cycle_strict : cycleProduct (1 - structural) < 1

-- @node: BackshiftExplanation.transformed_covariance_eq
/-- [For an environment included in the fitted set](hyp:he), [the fitted covariance equation is
equivalent to its congruence-transformed form](goal). -/
lemma WeakBackshiftExplanation.transformed_covariance_eq {p m c : ℕ}
    {covarianceFamily : Environment m → RealMatrix p}
    (X : WeakBackshiftExplanation p m c covarianceFamily) (e : Environment m)
    (he : e ∈ X.fitted) :
    X.structural * covarianceFamily e * X.structural.transpose =
      X.invariantNoise + Matrix.diagonal (X.shifts e) := by
  have hleft : X.structural * X.structural⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ X.structural_invertible
  have hright : X.structural⁻¹.transpose * X.structural.transpose = 1 := by
    rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
  rw [X.covariance_eq e he]
  calc
    _ = (X.structural * X.structural⁻¹) *
        (X.invariantNoise + Matrix.diagonal (X.shifts e)) *
          (X.structural⁻¹.transpose * X.structural.transpose) := by noncomm_ring
    _ = X.invariantNoise + Matrix.diagonal (X.shifts e) := by
      rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]

-- @node: centeredShiftCombination
/-- A linear combination of shift differences based at one overlap environment. -/
def centeredShiftCombination {p m : ℕ} (J : Finset (Environment m))
    (e0 : Environment m) (s : Environment m → Fin p → ℝ)
    (β : Environment m → ℝ) (k : Fin p) : ℝ :=
  ∑ e ∈ J, β e * (s e k - s e0 k)

-- @node: centeredShiftCombination_single
/-- A singleton coefficient extracts its centered shift vector. [Under the stated hypotheses](hyp:he) [this conclusion](goal) applies. -/
lemma centeredShiftCombination_single {p m : ℕ} (J : Finset (Environment m))
    (e0 e : Environment m) (s : Environment m → Fin p → ℝ) (he : e ∈ J)
    (k : Fin p) :
    centeredShiftCombination J e0 s (Pi.single e 1) k = s e k - s e0 k := by
  classical
  unfold centeredShiftCombination
  rw [Finset.sum_eq_single e]
  · simp
  · intro b hb hbe
    simp [hbe]
  · exact fun h => (h he).elim

-- @node: exists_centeredShiftCombination_ne_zero
/-- If every coordinate varies on the overlap, one linear combination of centered shifts is
nonzero in every coordinate. [Under the stated hypotheses](hyp:hvar) [this conclusion](goal) applies. -/
lemma exists_centeredShiftCombination_ne_zero {p m : ℕ}
    (J : Finset (Environment m)) (e0 : Environment m)
    (s : Environment m → Fin p → ℝ)
    (hvar : ∀ k, ∃ e ∈ J, s e k ≠ s e0 k) :
    ∃ β : Environment m → ℝ, ∀ k,
      centeredShiftCombination J e0 s β k ≠ 0 := by
  classical
  let f : Fin p → Module.Dual ℝ (Environment m → ℝ) := fun k ↦
    { toFun := fun β ↦ centeredShiftCombination J e0 s β k
      map_add' := by
        intro β γ
        simp only [centeredShiftCombination, Pi.add_apply]
        simp_rw [add_mul]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro r β
        simp only [centeredShiftCombination, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum] }
  apply Module.Dual.exists_forall_ne_zero_of_forall_exists f
  intro k
  obtain ⟨e, heJ, he⟩ := hvar k
  refine ⟨Pi.single e 1, ?_⟩
  change centeredShiftCombination J e0 s (Pi.single e 1) k ≠ 0
  rw [centeredShiftCombination_single J e0 e s heJ k]
  exact sub_ne_zero.mpr he

-- @node: exists_centeredShiftCombination_distinctRatios
/-- Once a centered combination has no zero coordinate, noncollinearity supplies another
combination whose coordinatewise ratios are pairwise distinct. [Under the stated hypotheses](hyp:hb,hnc) [this conclusion](goal) applies. -/
lemma exists_centeredShiftCombination_distinctRatios {p m : ℕ}
    (J : Finset (Environment m)) (e0 : Environment m)
    (s : Environment m → Fin p → ℝ) (b : Fin p → ℝ)
    (hb : ∀ k, b k ≠ 0)
    (hnc : ∀ k l : Fin p, k < l → ¬ CollinearPairs s k l J) :
    ∃ α : Environment m → ℝ, ∀ k l : Fin p, k < l →
      centeredShiftCombination J e0 s α k / b k ≠
        centeredShiftCombination J e0 s α l / b l := by
  classical
  let pairType := {kl : Fin p × Fin p // kl.1 < kl.2}
  let f : pairType → Module.Dual ℝ (Environment m → ℝ) := fun kl ↦
    { toFun := fun α ↦
        b kl.1.2 * centeredShiftCombination J e0 s α kl.1.1 -
          b kl.1.1 * centeredShiftCombination J e0 s α kl.1.2
      map_add' := by
        intro α β
        simp only [centeredShiftCombination, Pi.add_apply]
        simp_rw [add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro r α
        simp only [centeredShiftCombination, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        simp_rw [mul_assoc, ← Finset.mul_sum]
        ring }
  obtain ⟨α, hα⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f (by
    intro kl
    by_contra hex
    push_neg at hex
    apply hnc kl.1.1 kl.1.2 kl.2
    intro e he f' hf g hg
    have hcross (x : Environment m) (hx : x ∈ J) :
        b kl.1.2 * (s x kl.1.1 - s e0 kl.1.1) -
          b kl.1.1 * (s x kl.1.2 - s e0 kl.1.2) = 0 := by
      simpa [f, centeredShiftCombination_single J e0 x s hx] using
        hex (Pi.single x 1)
    have hdet (x : Environment m) (hx : x ∈ J)
        (y : Environment m) (hy : y ∈ J) :
        (s x kl.1.1 - s e0 kl.1.1) * (s y kl.1.2 - s e0 kl.1.2) -
          (s y kl.1.1 - s e0 kl.1.1) * (s x kl.1.2 - s e0 kl.1.2) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (hb kl.1.2)
      calc
        b kl.1.2 *
            ((s x kl.1.1 - s e0 kl.1.1) * (s y kl.1.2 - s e0 kl.1.2) -
              (s y kl.1.1 - s e0 kl.1.1) * (s x kl.1.2 - s e0 kl.1.2)) =
            (b kl.1.2 * (s x kl.1.1 - s e0 kl.1.1) -
                b kl.1.1 * (s x kl.1.2 - s e0 kl.1.2)) *
                (s y kl.1.2 - s e0 kl.1.2) -
              (b kl.1.2 * (s y kl.1.1 - s e0 kl.1.1) -
                b kl.1.1 * (s y kl.1.2 - s e0 kl.1.2)) *
                (s x kl.1.2 - s e0 kl.1.2) := by ring
        _ = 0 := by rw [hcross x hx, hcross y hy]; ring
    unfold affineMinor
    linear_combination hdet f' hf g hg - hdet e he g hg + hdet e he f' hf)
  refine ⟨α, ?_⟩
  intro k l hkl heq
  have hz := hα ⟨(k, l), hkl⟩
  apply hz
  dsimp [f]
  apply (div_eq_div_iff (hb k) (hb l)).mp at heq
  nlinarith

-- @node: noncollinear_card_at_least_three
/-- A finite indexed planar cloud that is not collinear contains at least three indices. [This is the asserted conclusion](goal). -/
lemma noncollinear_card_at_least_three {p : ℕ} {s : Environment m → Fin p → ℝ}
    {k l : Fin p} {S : Finset (Environment m)}
    (h : ¬ CollinearPairs s k l S) : 3 ≤ S.card := by
  classical
  by_contra hcard
  push Not at hcard
  apply h
  intro e he f hf g hg
  have hdup : e = f ∨ e = g ∨ f = g := by
    by_contra hne
    push Not at hne
    have hsub : {e, f, g} ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact he
      · exact hf
      · exact hg
    have hthree : ({e, f, g} : Finset (Environment m)).card = 3 := by
      simp [hne.1, hne.2.1, hne.2.2]
    have := Finset.card_le_card hsub
    omega
  rcases hdup with rfl | rfl | rfl <;> simp [affineMinor]

-- @node: exists_nonzero_affineMinor_of_noncollinear
/-- Noncollinearity is witnessed by three indices with a nonzero affine minor. [This is the asserted conclusion](goal). -/
lemma exists_nonzero_affineMinor_of_noncollinear {p : ℕ}
    {s : Environment m → Fin p → ℝ} {k l : Fin p}
    {S : Finset (Environment m)} (h : ¬ CollinearPairs s k l S) :
    ∃ e ∈ S, ∃ f ∈ S, ∃ g ∈ S, affineMinor s k l e f g ≠ 0 := by
  unfold CollinearPairs at h
  push Not at h
  exact h

/-- A strictly normalized reference and a weakly cycle-normalized candidate agree structurally
when the reference shift cloud is pairwise noncollinear on their overlap. [Under the stated hypotheses](hyp:hp,hc,covariance_psd,first_cycle_strict) [this conclusion](goal) applies. -/
lemma weak_boundary_overlap_uniqueness {p m c : ℕ} (hp : 2 ≤ p) (hc : c < m)
    (covarianceFamily : Environment m → RealMatrix p)
    (covariance_psd : ∀ e, (covarianceFamily e).PosSemidef)
    (first second : WeakBackshiftExplanation p m c covarianceFamily)
    (first_cycle_strict : cycleProduct (1 - first.structural) < 1) :
    let H1 := first.fitted -- @realizes H1(first fitted set, card at least h)
    let H2 := second.fitted -- @realizes H2(second fitted set, card at least h)
    let J := H1 ∩ H2 -- @realizes J(J = H1 ∩ H2)
    let D1 := first.structural -- @realizes D1(first invertible normalized matrix)
    let D2 := second.structural -- @realizes D2(second invertible normalized matrix)
    let s1 := first.shifts -- @realizes s1(first nonnegative shift array)
    let s2 := second.shifts -- @realizes s2(second nonnegative shift array)
    m - 2 * c ≤ J.card ∧
      ((∀ k l : Fin p, k < l →
        ¬ CollinearPairs first.shifts k l (first.fitted ∩ second.fitted)) →
        D1 = D2) := by
  dsimp only
  refine ⟨overlap_card_lower_bound first.fitted second.fitted
    first.fitted_card second.fitted_card, ?_⟩
  intro h_noncollinear
  let k0 : Fin p := ⟨0, by omega⟩
  let k1 : Fin p := ⟨1, by omega⟩
  have hzero_lt_one : k0 < k1 := by
    exact Fin.mk_lt_mk.mpr (by omega)
  have hJcard : 3 ≤ (first.fitted ∩ second.fitted).card :=
    noncollinear_card_at_least_three
      (h_noncollinear k0 k1 hzero_lt_one)
  let J := first.fitted ∩ second.fitted
  obtain ⟨e0, he0⟩ : ∃ e0, e0 ∈ J := by
    exact Finset.card_pos.mp (by dsimp [J]; omega)
  have hvar : ∀ k, ∃ e ∈ J, first.shifts e k ≠ first.shifts e0 k := by
    intro k
    obtain ⟨l, hkl⟩ : ∃ l : Fin p, k ≠ l := by
      by_cases hk : k = k0
      · exact ⟨k1, by simpa [hk] using ne_of_lt hzero_lt_one⟩
      · exact ⟨k0, hk⟩
    by_contra hv
    push Not at hv
    rcases lt_or_gt_of_ne hkl with hlt | hgt
    · apply h_noncollinear k l hlt
      intro e he f hf g hg
      unfold affineMinor
      rw [hv e he, hv f hf, hv g hg]
      ring
    · apply h_noncollinear l k hgt
      intro e he f hf g hg
      unfold affineMinor
      rw [hv e he, hv f hf, hv g hg]
      ring
  obtain ⟨β, hβ⟩ :=
    exists_centeredShiftCombination_ne_zero J e0 first.shifts hvar
  let b : Fin p → ℝ := centeredShiftCombination J e0 first.shifts β
  obtain ⟨α, hα⟩ := exists_centeredShiftCombination_distinctRatios
    J e0 first.shifts b hβ h_noncollinear
  let a : Fin p → ℝ := centeredShiftCombination J e0 first.shifts α
  let ρ : Fin p → ℝ := fun k ↦ a k / b k
  have hρ : ∀ k l : Fin p, k ≠ l → ρ k ≠ ρ l := by
    intro k l hkl
    rcases lt_or_gt_of_ne hkl with hlt | hgt
    · exact hα k l hlt
    · exact (hα l k hgt).symm
  let Q : RealMatrix p := second.structural * first.structural⁻¹
  have hQdet : Q.det ≠ 0 := by
    simp [Q, Matrix.det_mul, Matrix.det_nonsing_inv,
      IsUnit.ne_zero second.structural_invertible,
      IsUnit.ne_zero first.structural_invertible]
  have hrelation (e : Environment m) :
      second.structural * covarianceFamily e * second.structural.transpose =
        Q * (first.structural * covarianceFamily e * first.structural.transpose) *
          Q.transpose := by
    have hleft : first.structural⁻¹ * first.structural = 1 :=
      Matrix.nonsing_inv_mul _ first.structural_invertible
    have hright : first.structural.transpose * first.structural⁻¹.transpose = 1 := by
      rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
    symm
    dsimp [Q]
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc first.structural⁻¹ first.structural, hleft,
      Matrix.one_mul, ← Matrix.mul_assoc first.structural.transpose
        first.structural⁻¹.transpose, hright, Matrix.one_mul]
  have hdifference (e : Environment m) (he : e ∈ J) :
      Q * Matrix.diagonal (fun k ↦ first.shifts e k - first.shifts e0 k) * Q.transpose =
        Matrix.diagonal (fun k ↦ second.shifts e k - second.shifts e0 k) := by
    have he' : e ∈ first.fitted ∩ second.fitted := by simpa [J] using he
    have he0' : e0 ∈ first.fitted ∩ second.fitted := by simpa [J] using he0
    have he1 : e ∈ first.fitted := (Finset.mem_inter.mp he').1
    have he2 : e ∈ second.fitted := (Finset.mem_inter.mp he').2
    have he01 : e0 ∈ first.fitted := (Finset.mem_inter.mp he0').1
    have he02 : e0 ∈ second.fitted := (Finset.mem_inter.mp he0').2
    have h1e := first.transformed_covariance_eq e he1
    have h1e0 := first.transformed_covariance_eq e0 he01
    have h2e := second.transformed_covariance_eq e he2
    have h2e0 := second.transformed_covariance_eq e0 he02
    calc
      _ = Q * ((first.invariantNoise + Matrix.diagonal (first.shifts e)) -
          (first.invariantNoise + Matrix.diagonal (first.shifts e0))) * Q.transpose := by
            congr 2
            ext i j
            by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
      _ = Q * ((first.structural * covarianceFamily e * first.structural.transpose) -
          (first.structural * covarianceFamily e0 * first.structural.transpose)) *
          Q.transpose := by rw [h1e, h1e0]
      _ = (second.structural * covarianceFamily e * second.structural.transpose) -
          (second.structural * covarianceFamily e0 * second.structural.transpose) := by
            rw [hrelation e, hrelation e0]
            noncomm_ring
      _ = (second.invariantNoise + Matrix.diagonal (second.shifts e)) -
          (second.invariantNoise + Matrix.diagonal (second.shifts e0)) := by rw [h2e, h2e0]
      _ = _ := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  have hcombination (γ : Environment m → ℝ) :
      Q * Matrix.diagonal (centeredShiftCombination J e0 first.shifts γ) * Q.transpose =
        Matrix.diagonal (centeredShiftCombination J e0 second.shifts γ) := by
    have hdiaglin :
        Matrix.diagonal (centeredShiftCombination J e0 first.shifts γ) =
          ∑ e ∈ J, γ e •
            Matrix.diagonal (fun k ↦ first.shifts e k - first.shifts e0 k) := by
      ext i j
      by_cases hij : i = j <;>
        simp [centeredShiftCombination, Matrix.diagonal_apply, Matrix.sum_apply,
          Matrix.smul_apply, hij]
    rw [hdiaglin]
    calc
      _ = ∑ e ∈ J, γ e •
          (Q * Matrix.diagonal (fun k ↦ first.shifts e k - first.shifts e0 k) *
            Q.transpose) := by
            simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
              Matrix.smul_mul]
      _ = ∑ e ∈ J, γ e •
          Matrix.diagonal (fun k ↦ second.shifts e k - second.shifts e0 k) := by
            apply Finset.sum_congr rfl
            intro e he
            rw [hdifference e he]
      _ = _ := by
        ext i j
        by_cases hij : i = j <;>
          simp [centeredShiftCombination, Matrix.diagonal_apply, Matrix.sum_apply,
            Matrix.smul_apply, hij]
  have hGa := hcombination α
  have hKb := hcombination β
  let a2 : Fin p → ℝ := centeredShiftCombination J e0 second.shifts α
  let b2 : Fin p → ℝ := centeredShiftCombination J e0 second.shifts β
  have hb2 : ∀ i, b2 i ≠ 0 := by
    have hdet_left :
        (Matrix.diagonal b2).det =
          (Q * Matrix.diagonal b * Q.transpose).det := by rw [hKb]
    have hdiagb : (Matrix.diagonal b).det ≠ 0 := by
      rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hβ i
    have hdiagb2 : (Matrix.diagonal b2).det ≠ 0 := by
      rw [hdet_left, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      exact mul_ne_zero (mul_ne_zero hQdet hdiagb) hQdet
    intro i hi
    apply hdiagb2
    rw [Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  let R : RealMatrix p := Q⁻¹.transpose
  have hQunit : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQdet
  have hRdet : R.det ≠ 0 := by
    simp [R, Matrix.det_transpose, Matrix.det_nonsing_inv, hQdet]
  have hGR : Matrix.diagonal a2 * R = Q * Matrix.diagonal a := by
    rw [← hGa]
    have hcancel : Q.transpose * R = 1 := by
      dsimp [R]
      rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul Q hQunit,
        Matrix.transpose_one]
    rw [Matrix.mul_assoc, hcancel, Matrix.mul_one]
  have hKR : Matrix.diagonal b2 * R = Q * Matrix.diagonal b := by
    rw [← hKb]
    have hcancel : Q.transpose * R = 1 := by
      dsimp [R]
      rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul Q hQunit,
        Matrix.transpose_one]
    rw [Matrix.mul_assoc, hcancel, Matrix.mul_one]
  have hrowR : ∀ i j k : Fin p, j ≠ k → R i j = 0 ∨ R i k = 0 := by
    intro i j k hjk
    by_contra hn
    push Not at hn
    have hGRij := congrArg (fun M : RealMatrix p ↦ M i j) hGR
    have hKRij := congrArg (fun M : RealMatrix p ↦ M i j) hKR
    have hGRik := congrArg (fun M : RealMatrix p ↦ M i k) hGR
    have hKRik := congrArg (fun M : RealMatrix p ↦ M i k) hKR
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hGRij hKRij hGRik hKRik
    have hjcross : a j * b2 i = a2 i * b j := by
      have hz : R i j * (a2 i * b j - b2 i * a j) = 0 := by
        calc
          _ = b j * (a2 i * R i j) - a j * (b2 i * R i j) := by ring
          _ = b j * (Q i j * a j) - a j * (Q i j * b j) := by
            rw [hGRij, hKRij]
          _ = 0 := by ring
      have hc := (mul_eq_zero.mp hz).resolve_left hn.1
      nlinarith
    have hkcross : a k * b2 i = a2 i * b k := by
      have hz : R i k * (a2 i * b k - b2 i * a k) = 0 := by
        calc
          _ = b k * (a2 i * R i k) - a k * (b2 i * R i k) := by ring
          _ = b k * (Q i k * a k) - a k * (Q i k * b k) := by
            rw [hGRik, hKRik]
          _ = 0 := by ring
      have hc := (mul_eq_zero.mp hz).resolve_left hn.2
      nlinarith
    apply hρ j k hjk
    dsimp [ρ]
    rw [div_eq_div_iff (hβ j) (hβ k)]
    apply (mul_left_cancel₀ (hb2 i))
    calc
      b2 i * (a j * b k) = (a j * b2 i) * b k := by ring
      _ = (a2 i * b j) * b k := by rw [hjcross]
      _ = (a2 i * b k) * b j := by ring
      _ = (a k * b2 i) * b j := by rw [hkcross]
      _ = b2 i * (a k * b j) := by ring
  obtain ⟨τ, d, hd, hRmono⟩ :=
    Causalean.Mathlib.LinearAlgebra.genPerm_of_det_ne_zero_of_colSupport
      (W := R.transpose) (by simpa [Matrix.det_transpose] using hRdet) (by
        intro j i k hik
        simpa [Matrix.transpose_apply] using hrowR j i k hik)
  let π : Equiv.Perm (Fin p) := τ.symm
  let q : Fin p → ℝ := fun i ↦ (d (π i))⁻¹
  have hQinvmono : ∀ i j, Q⁻¹ i j = if j = τ i then d i else 0 := by
    intro i j
    simpa [R] using hRmono i j
  have hQmono : ∀ i j, Q i j = if j = π i then q i else 0 := by
    intro i j
    have htaupi : τ (π i) = i := by simp [π]
    have hinv := Matrix.nonsing_inv_mul Q hQunit
    have hij := congrArg (fun M : RealMatrix p ↦ M (π i) j) hinv
    rw [Matrix.mul_apply] at hij
    have hsum : ∑ x, Q⁻¹ (π i) x * Q x j = d (π i) * Q i j := by
      change (Finset.univ.sum fun x ↦ Q⁻¹ (π i) x * Q x j) =
        d (π i) * Q i j
      rw [Finset.sum_eq_single i]
      · rw [hQinvmono, if_pos htaupi.symm]
      · intro x hx hxi
        have hne : x ≠ τ (π i) := by rw [htaupi]; exact hxi
        rw [hQinvmono]
        simp [hne]
      · simp
    rw [hsum] at hij
    by_cases hji : j = π i
    · subst j
      have hdpi := hd (π i)
      simp only [Matrix.one_apply, if_pos] at hij
      simp only [if_pos rfl]
      change Q i (π i) = q i
      dsimp [q]
      rw [← one_div]
      exact (eq_div_iff hdpi).2 (by simpa [mul_comm] using hij)
    · have hjne : (π i : Fin p) ≠ j := Ne.symm hji
      simp only [Matrix.one_apply, if_neg hjne] at hij
      have hzero : Q i j = 0 := by
        exact (mul_eq_zero.mp hij).resolve_left (hd (π i))
      simp [hji, hzero]
  have hq : ∀ i, q i ≠ 0 := by
    intro i
    simp [q, hd (π i)]
  have hD2eq : second.structural = Q * first.structural := by
    dsimp [Q]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ first.structural_invertible,
      Matrix.mul_one]
  have hroweq : ∀ i j,
      second.structural i j = q i * first.structural (π i) j := by
    intro i j
    rw [hD2eq, Matrix.mul_apply]
    change (Finset.univ.sum fun x ↦ Q i x * first.structural x j) = _
    rw [Finset.sum_eq_single (π i)]
    · rw [hQmono, if_pos rfl]
    · intro x hx hxi
      rw [hQmono, if_neg hxi]
      simp
    · simp
  have hdiagrel (j : Fin p) : q j * first.structural (π j) j = 1 := by
    rw [← hroweq, second.structural_unit_diagonal]
  by_contra hD
  have hπne : π ≠ 1 := by
    intro hπ
    have hq1 : ∀ i, q i = 1 := by
      intro i
      have h := hdiagrel i
      simpa [hπ, first.structural_unit_diagonal] using h
    have hQone : Q = 1 := by
      ext i j
      rw [hQmono]
      by_cases hij : i = j <;> simp [hπ, hq1, Matrix.one_apply, hij, eq_comm]
    apply hD
    rw [hD2eq, hQone, Matrix.one_mul]
  obtain ⟨i, hi⟩ : ∃ i, π i ≠ i := by
    simpa [Equiv.ext_iff] using hπne
  let σ := π.cycleOf i
  have hσ : σ.IsCycle := Equiv.Perm.isCycle_cycleOf π hi
  have hσcard : 2 ≤ σ.support.card := by simpa [σ] using hi
  have hσapply (j : Fin p) (hj : j ∈ σ.support) : σ j = π j := by
    rw [Equiv.Perm.cycleOf_apply]
    rw [if_pos ((Equiv.Perm.mem_support_cycleOf_iff' hi).mp (by simpa [σ] using hj))]
  have hcycle_lt (D : RealMatrix p) (hDadm : D ∈ admissibleSet p)
      (κ : Equiv.Perm (Fin p)) (hκ : κ.IsCycle) (hκcard : 2 ≤ κ.support.card) :
      simpleCycleWeight (1 - D) κ < 1 := by
    have hall := (Finset.fold_max_lt (s := (Finset.univ : Finset (Equiv.Perm (Fin p))))
      (b := (0 : ℝ)) (f := simpleCycleWeight (1 - D)) (c := 1)).mp hDadm.2.2
    exact hall.2 κ (Finset.mem_univ κ)
  have hcycle_le (D : RealMatrix p) (hDcycle : cycleProduct (1 - D) ≤ 1)
      (κ : Equiv.Perm (Fin p)) (hκ : κ.IsCycle) (hκcard : 2 ≤ κ.support.card) :
      simpleCycleWeight (1 - D) κ ≤ 1 := by
    have hall := (Finset.fold_max_le (s := (Finset.univ : Finset (Equiv.Perm (Fin p))))
      (b := (0 : ℝ)) (f := simpleCycleWeight (1 - D)) (c := 1)).mp hDcycle
    exact hall.2 κ (Finset.mem_univ κ)
  have hw2 : simpleCycleWeight (1 - second.structural) σ =
      ∏ j ∈ σ.support, |q j| := by
    unfold simpleCycleWeight
    rw [if_pos ⟨hσ, hσcard⟩]
    apply Finset.prod_congr rfl
    intro j hj
    have hjne : j ≠ σ j := (Equiv.Perm.mem_support.mp hj).symm
    simp only [Matrix.sub_apply, Matrix.one_apply, if_neg hjne]
    rw [hσapply j hj, hroweq, first.structural_unit_diagonal]
    simp
  have hw1 : simpleCycleWeight (1 - first.structural) σ⁻¹ =
      ∏ j ∈ σ.support, |q (σ⁻¹ j)|⁻¹ := by
    unfold simpleCycleWeight
    rw [if_pos ⟨hσ.inv, by simpa using hσcard⟩]
    rw [Equiv.Perm.support_inv]
    apply Finset.prod_congr rfl
    intro j hj
    have hjpre : σ⁻¹ j ∈ σ.support := by
      have happ := Equiv.Perm.apply_mem_support (f := σ⁻¹) (x := j)
      simpa [Equiv.Perm.support_inv] using happ.mpr (by
        simpa [Equiv.Perm.support_inv] using hj)
    have hjne : j ≠ σ⁻¹ j := by
      simpa using (Equiv.Perm.mem_support.mp hjpre)
    have hπpre : π (σ⁻¹ j) = j := by
      rw [← hσapply (σ⁻¹ j) hjpre]
      simp
    have hrel := hdiagrel (σ⁻¹ j)
    rw [hπpre] at hrel
    rw [Matrix.sub_apply]
    simp only [Matrix.one_apply, if_neg hjne]
    rw [zero_sub, abs_neg]
    have habs : |q (σ⁻¹ j)| * |first.structural j (σ⁻¹ j)| = 1 := by
      rw [← abs_mul, hrel, abs_one]
    have hquot : |first.structural j (σ⁻¹ j)| = 1 / |q (σ⁻¹ j)| :=
      (eq_div_iff (abs_ne_zero.mpr (hq (σ⁻¹ j)))).2 (by
        simpa [mul_comm] using habs)
    simpa [one_div] using hquot
  have hprod_reindex :
      (∏ j ∈ σ.support, |q (σ⁻¹ j)|⁻¹) =
        (∏ j ∈ σ.support, |q j|)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_equiv σ.symm
    · intro j
      have happ := Equiv.Perm.apply_mem_support (f := σ⁻¹) (x := j)
      simpa [Equiv.Perm.support_inv] using happ.symm
    · intro j hj
      rfl
  have hle2 : (∏ j ∈ σ.support, |q j|) ≤ 1 := by
    rw [← hw2]
    exact hcycle_le second.structural second.cycle_bound σ hσ hσcard
  have hlt1 : (∏ j ∈ σ.support, |q j|)⁻¹ < 1 := by
    rw [← hprod_reindex, ← hw1]
    exact hcycle_lt first.structural
      ⟨first.structural_invertible, first.structural_unit_diagonal, first_cycle_strict⟩
      σ⁻¹ hσ.inv (by simpa using hσcard)
  have hpos : 0 < ∏ j ∈ σ.support, |q j| := by
    exact Finset.prod_pos fun j _ ↦ abs_pos.mpr (hq j)
  have hinvpos : 0 < (∏ j ∈ σ.support, |q j|)⁻¹ := inv_pos.mpr hpos
  have hone := inv_mul_cancel₀ (ne_of_gt hpos)
  nlinarith

-- @node: lem:overlap-uniqueness
/-- Two normalized covariance explanations agree structurally when the first shift cloud is
pairwise noncollinear on their overlap. [Under the stated hypotheses](hyp:hp,hc,covariance_psd) [this conclusion](goal) applies. -/
lemma overlap_uniqueness {p m c : ℕ} (hp : 2 ≤ p) (hc : c < m)
    (covarianceFamily : Environment m → RealMatrix p)
    (covariance_psd : ∀ e, (covarianceFamily e).PosSemidef)
    (first : BackshiftExplanation p m c covarianceFamily)
    (second : BackshiftExplanation p m c covarianceFamily) :
    let H1 := first.fitted
    let H2 := second.fitted
    let J := H1 ∩ H2
    let D1 := first.structural
    let D2 := second.structural
    let s1 := first.shifts
    let s2 := second.shifts
    m - 2 * c ≤ J.card ∧
      ((∀ k l : Fin p, k < l →
        ¬ CollinearPairs first.shifts k l (first.fitted ∩ second.fitted)) →
        D1 = D2) := by
  exact weak_boundary_overlap_uniqueness hp hc covarianceFamily covariance_psd
    first.toWeakBackshiftExplanation second.toWeakBackshiftExplanation first.cycle_strict

end CausalSmith.ExactID.RobustBackshiftUniformDistance
