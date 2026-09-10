import CausalSmith.Substrate.CollisionSafeSpectralLaw.FunctionalCalculus
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.SetTheory.Cardinal.Embedding

/-!
# Collision-safe finite spectral enumeration

This module turns a real diagonalization into an injective list of its distinct spectral values,
padding unused slots by distinct points in a prescribed interval.  It also identifies the
associated Lagrange matrix polynomials with aggregate spectral projectors, so repeated diagonal
coordinates contribute once rather than being overcounted.
-/

namespace CausalSmith.Substrate.CollisionSafeSpectralLaw

open Set
open scoped BigOperators

/-- A complex right eigenvalue of a real square matrix. -/
def ComplexMatrixEigenvalue {n : ℕ} (A : RectMatrix n n) (z : ℂ) : Prop :=
  ∃ v : Fin n → ℂ, v ≠ 0 ∧ ∀ i, ∑ j, (A i j : ℂ) * v j = z * v i

/-- The Lagrange matrix polynomial attached to one slot of a proposed spectral enumeration. -/
noncomputable def polynomialSpectralProjector {n : ℕ} (A : RectMatrix n n)
    (value : Fin n → ℝ) (i : Fin n) : RectMatrix n n :=
  (Finset.univ.filter (fun j => value j ≠ value i)).toList.foldl
    (fun E j => E * ((value i - value j)⁻¹ •
      (A - value j • (1 : RectMatrix n n)))) 1

/-- The scalar Lagrange polynomial evaluated at `x`. -/
noncomputable def scalarLagrange {n : ℕ} (value : Fin n → ℝ) (i : Fin n)
    (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j => value j ≠ value i),
    (value i - value j)⁻¹ * (x - value j)

private theorem applyFunction_one {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) :
    D.applyFunction (fun _ => 1) = 1 := by
  unfold RealDiagonalization.applyFunction
  rw [show Matrix.diagonal ((fun _ => 1) ∘ D.eigenvalue) =
      (1 : RectMatrix n n) by ext i j <;> simp [Matrix.diagonal_apply, Matrix.one_apply]]
  simpa using D.basis_mul_inv

private theorem applyFunction_mul {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) (f g : ℝ → ℝ) :
    D.applyFunction (fun x => f x * g x) = D.applyFunction f * D.applyFunction g := by
  unfold RealDiagonalization.applyFunction
  rw [show Matrix.diagonal ((fun x => f x * g x) ∘ D.eigenvalue) =
      Matrix.diagonal (f ∘ D.eigenvalue) * Matrix.diagonal (g ∘ D.eigenvalue) by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc D.basisInv D.basis, D.inv_mul_basis, Matrix.one_mul]

private theorem applyFunction_linearFactor {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) (a b : ℝ) :
    D.applyFunction (fun x => a * (x - b)) =
      a • (A - b • (1 : RectMatrix n n)) := by
  unfold RealDiagonalization.applyFunction
  have hdiag : Matrix.diagonal ((fun x => a * (x - b)) ∘ D.eigenvalue) =
      a • (Matrix.diagonal D.eigenvalue - b • (1 : RectMatrix n n)) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, hij, Function.comp_apply] <;> ring
  rw [hdiag]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub]
  rw [Matrix.sub_mul, Matrix.mul_one]
  simp only [Matrix.smul_mul]
  rw [D.basis_mul_inv]
  rw [← D.reconstruct]

private theorem polynomialSpectralProjector_eq_applyFunction
    {n : ℕ} {A : RectMatrix n n} (D : RealDiagonalization A)
    (value : Fin n → ℝ) (i : Fin n) :
    polynomialSpectralProjector A value i = D.applyFunction (scalarLagrange value i) := by
  classical
  let s := Finset.univ.filter (fun j => value j ≠ value i)
  have hfold : ∀ (l : List (Fin n)),
      l.foldl
          (fun E j => E * ((value i - value j)⁻¹ •
            (A - value j • (1 : RectMatrix n n)))) 1 =
        D.applyFunction (fun x => (l.map (fun j =>
          (value i - value j)⁻¹ * (x - value j))).prod) := by
    intro l
    induction l using List.reverseRecOn with
    | nil => simpa using (applyFunction_one D).symm
    | append_singleton l j ih =>
        rw [List.foldl_append, ih]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [← applyFunction_linearFactor D]
        rw [← applyFunction_mul]
        congr 1
        funext x
        simp
  unfold polynomialSpectralProjector scalarLagrange
  change s.toList.foldl
      (fun E j => E * ((value i - value j)⁻¹ •
        (A - value j • (1 : RectMatrix n n)))) 1 = _
  rw [hfold]
  congr 1
  funext x
  simp [s]

private theorem scalarLagrange_on_value {n : ℕ} (value : Fin n → ℝ)
    (hinj : Function.Injective value) (i u : Fin n) :
    scalarLagrange value i (value u) = if u = i then 1 else 0 := by
  classical
  by_cases hui : u = i
  · subst u
    unfold scalarLagrange
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro j hj
    have hne : value j ≠ value i := (Finset.mem_filter.mp hj).2
    field_simp
  · unfold scalarLagrange
    rw [if_neg hui]
    apply (Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩))
    · simp
    · exact fun h => hui (hinj h)

/-- For an injective enumeration containing every spectral value, a Lagrange matrix polynomial is
the aggregate projector at its slot when the slot is spectral, and is zero at every dummy slot. -/
theorem polynomialSpectralProjector_eq_projector_or_zero
    {n : ℕ} {A : RectMatrix n n} (D : RealDiagonalization A)
    (value : Fin n → ℝ) (hinj : Function.Injective value)
    (hcomplete : ∀ u, ∃ i, value i = D.eigenvalue u) (i : Fin n) :
    polynomialSpectralProjector A value i =
      if value i ∈ D.spectralValues then D.projector (value i) else 0 := by
  rw [polynomialSpectralProjector_eq_applyFunction D]
  unfold RealDiagonalization.applyFunction RealDiagonalization.projector
  split_ifs with hi
  · have hscalar (u : Fin n) : scalarLagrange value i (D.eigenvalue u) =
        if D.eigenvalue u = value i then 1 else 0 := by
      obtain ⟨j, hj⟩ := hcomplete u
      rw [← hj, scalarLagrange_on_value value hinj]
      by_cases hji : j = i
      · subst j
        simp
      · have hne : value j ≠ value i := fun h => hji (hinj h)
        simp [hji, hne]
    rw [show Matrix.diagonal (scalarLagrange value i ∘ D.eigenvalue) =
        Matrix.diagonal (fun u => if D.eigenvalue u = value i then 1 else 0) by
      ext u v
      by_cases huv : u = v
      · subst v
        simp [Matrix.diagonal_apply, Function.comp_apply, hscalar]
      · simp [Matrix.diagonal_apply, huv]]
  · have hnone (u : Fin n) : D.eigenvalue u ≠ value i := by
      intro h
      apply hi
      simp [RealDiagonalization.spectralValues, ← h]
    rw [show Matrix.diagonal (scalarLagrange value i ∘ D.eigenvalue) =
        (0 : RectMatrix n n) by
      ext u v
      by_cases huv : u = v
      · subst v
        obtain ⟨j, hj⟩ := hcomplete u
        have hji : j ≠ i := fun h => hnone u (hj ▸ congrArg value h)
        have hscalar := scalarLagrange_on_value value hinj i j
        rw [if_neg hji] at hscalar
        simp [Matrix.diagonal_apply, Function.comp_apply, ← hj, hscalar]
      · simp [Matrix.diagonal_apply, huv]]
    simp

/-- Completeness alone identifies the Lagrange polynomial with the aggregate projector at every
listed spectral value.  Injectivity is unnecessary here: repeated listed values give the same
aggregate projector, while nonspectral dummy values give zero. -/
theorem polynomialSpectralProjector_eq_projector_or_zero_of_complete
    {n : ℕ} {A : RectMatrix n n} (D : RealDiagonalization A)
    (value : Fin n → ℝ) (hcomplete : ∀ u, ∃ i, value i = D.eigenvalue u)
    (i : Fin n) :
    polynomialSpectralProjector A value i =
      if value i ∈ D.spectralValues then D.projector (value i) else 0 := by
  rw [polynomialSpectralProjector_eq_applyFunction D]
  unfold RealDiagonalization.applyFunction RealDiagonalization.projector
  split_ifs with hi
  · have hscalar (u : Fin n) : scalarLagrange value i (D.eigenvalue u) =
        if D.eigenvalue u = value i then 1 else 0 := by
      classical
      unfold scalarLagrange
      by_cases hu : D.eigenvalue u = value i
      · rw [if_pos hu]
        apply Finset.prod_eq_one
        intro j hj
        have hne : value j ≠ value i := (Finset.mem_filter.mp hj).2
        rw [hu]
        field_simp
      · rw [if_neg hu]
        obtain ⟨j, hj⟩ := hcomplete u
        apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ j, by
          intro h
          exact hu (hj.symm.trans h)⟩)
        simp [hj]
    rw [show Matrix.diagonal (scalarLagrange value i ∘ D.eigenvalue) =
        Matrix.diagonal (fun u => if D.eigenvalue u = value i then 1 else 0) by
      ext u v
      by_cases huv : u = v
      · subst v
        simp [Matrix.diagonal_apply, Function.comp_apply, hscalar]
      · simp [Matrix.diagonal_apply, huv]]
  · have hnone (u : Fin n) : D.eigenvalue u ≠ value i := by
      intro h
      apply hi
      simp [RealDiagonalization.spectralValues, ← h]
    rw [show Matrix.diagonal (scalarLagrange value i ∘ D.eigenvalue) =
        (0 : RectMatrix n n) by
      ext u v
      by_cases huv : u = v
      · subst v
        classical
        obtain ⟨j, hj⟩ := hcomplete u
        have hz : scalarLagrange value i (D.eigenvalue u) = 0 := by
          unfold scalarLagrange
          apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ j, by
            intro h
            exact hnone u (hj.symm.trans h)⟩)
          simp [hj]
        simp [Matrix.diagonal_apply, Function.comp_apply, hz]
      · simp [Matrix.diagonal_apply, huv]]
    simp

/-- A complete `n`-slot enumeration whose cluster masses normalize to one cannot repeat a
positive spectral cluster.  Consequently it integrates every test function exactly as the
underlying diagonal coordinates do; zero-mass dummy slots are harmless. -/
theorem complete_clusterMass_integral_eq
    {n : ℕ} (mass eig value : Fin n → ℝ)
    (hmasspos : ∀ u, 0 < mass u) (hmasssum : ∑ u, mass u = 1)
    (hcomplete : ∀ u, ∃ i, eig u = value i)
    (houtsum : ∑ i, (∑ u, if eig u = value i then mass u else 0) = 1) :
    ∀ f : ℝ → ℝ,
      ∑ i, (∑ u, if eig u = value i then mass u else 0) * f (value i) =
        ∑ u, mass u * f (eig u) := by
  classical
  let c : Fin n → ℝ := fun u => ∑ i, if eig u = value i then 1 else 0
  have hc1 (u : Fin n) : 1 ≤ c u := by
    obtain ⟨i, hi⟩ := hcomplete u
    dsimp [c]
    calc
      1 = (if eig u = value i then 1 else 0 : ℝ) := by simp [hi]
      _ ≤ ∑ j, (if eig u = value j then 1 else 0 : ℝ) :=
        Finset.single_le_sum
          (fun j _ => show (0 : ℝ) ≤ (if eig u = value j then 1 else 0) by positivity)
          (Finset.mem_univ i)
  have hweighted : ∑ u, mass u * c u = 1 := by
    rw [← houtsum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    dsimp [c]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hzero : ∑ u, mass u * (c u - 1) = 0 := by
    calc
      _ = ∑ u, (mass u * c u - mass u) := by
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = (∑ u, mass u * c u) - ∑ u, mass u := by
        rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hweighted, hmasssum]; ring
  have hc (u : Fin n) : c u = 1 := by
    have hnonneg (v : Fin n) : 0 ≤ mass v * (c v - 1) :=
      mul_nonneg (hmasspos v).le (sub_nonneg.mpr (hc1 v))
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v _ => hnonneg v)).mp hzero u (Finset.mem_univ u)
    rcases mul_eq_zero.mp hz with hm | hh
    · exact False.elim ((hmasspos u).ne' hm)
    · linarith
  intro f
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  calc
    (∑ i, (if eig u = value i then mass u else 0) * f (value i)) =
        mass u * f (eig u) * c u := by
      dsimp [c]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with h
      · rw [h]; ring
      · ring
    _ = mass u * f (eig u) := by rw [hc u, mul_one]

/-- Every listed diagonal coordinate is an actual complex eigenvalue of the reconstructed real
matrix. -/
theorem RealDiagonalization.diagonal_eigenvalue_is_complexEigenvalue
    {n : ℕ} {A : RectMatrix n n} (D : RealDiagonalization A) (u : Fin n) :
    ComplexMatrixEigenvalue A (D.eigenvalue u) := by
  classical
  let v : Fin n → ℂ := fun i => D.basis i u
  refine ⟨v, ?_, ?_⟩
  · intro hv
    have hentry := congrArg (fun M : RectMatrix n n => M u u) D.inv_mul_basis
    have hzero : ∑ j, D.basisInv u j * D.basis j u = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hj := congrFun hv j
      change (D.basis j u : ℂ) = 0 at hj
      have hjR : D.basis j u = 0 := by exact_mod_cast hj
      simp [hjR]
    rw [Matrix.mul_apply, hzero] at hentry
    simpa [Matrix.one_apply] using hentry
  · intro i
    have hcol : ∑ j, A i j * D.basis j u = D.eigenvalue u * D.basis i u := by
      have hmat : A * D.basis = D.basis * Matrix.diagonal D.eigenvalue := by
        calc
          A * D.basis = (D.basis * Matrix.diagonal D.eigenvalue * D.basisInv) *
              D.basis := congrArg (fun M => M * D.basis) D.reconstruct
          _ = D.basis * Matrix.diagonal D.eigenvalue * (D.basisInv * D.basis) := by
            simp only [Matrix.mul_assoc]
          _ = _ := by rw [D.inv_mul_basis, Matrix.mul_one]
      have h := congrArg (fun M : RectMatrix n n => M i u) hmat
      simpa [Matrix.mul_apply, Matrix.diagonal_apply, mul_comm] using h
    change ∑ j, (A i j : ℂ) * (D.basis j u : ℂ) =
      (D.eigenvalue u : ℂ) * (D.basis i u : ℂ)
    exact_mod_cast hcol

/-- If the diagonal values lie in a nondegenerate symmetric interval, their distinct values have
an injective `Fin n` enumeration in that interval; unused slots are necessarily nonspectral. -/
theorem exists_injective_spectralEnumeration
    {n : ℕ} {A : RectMatrix n n} (D : RealDiagonalization A)
    {radius : ℝ} (hradius : 0 < radius)
    (hbound : ∀ u, D.eigenvalue u ∈ Set.Icc (-radius) radius) :
    ∃ value : Fin n → ℝ,
      Function.Injective value ∧
      (∀ u, ∃ i, value i = D.eigenvalue u) ∧
      ∀ i, value i ∈ Set.Icc (-radius) radius := by
  classical
  let S := D.spectralValues
  let m := S.card
  have hmn : m ≤ n := by
    dsimp [m, S, RealDiagonalization.spectralValues]
    simpa using (Finset.card_image_le
      (s := (Finset.univ : Finset (Fin n))) (f := D.eigenvalue))
  let specEnum : Fin m ≃ S := (S.orderIsoOfFin (show S.card = m from rfl)).toEquiv
  let base : Fin m ↪ {x : ℝ // x ∈ Set.Icc (-radius) radius} :=
    ⟨fun j => ⟨(specEnum j).1, by
        rcases Finset.mem_image.mp (specEnum j).2 with ⟨u, -, hu⟩
        rw [← hu]
        exact hbound u⟩,
      fun i j h => by
        apply specEnum.injective
        apply Subtype.ext
        exact congrArg (fun q : {x : ℝ // x ∈ Set.Icc (-radius) radius} => q.1) h⟩
  have hinfinite : Infinite {x : ℝ // x ∈ Set.Icc (-radius) radius} :=
    Set.Icc.infinite (by linarith)
  letI := hinfinite
  obtain ⟨full, hfull⟩ := Fin.Embedding.restrictSurjective_of_le_ENatCard
    hmn (by rw [ENat.card_eq_top_of_infinite]; simp) base
  let value : Fin n → ℝ := fun i => full i
  refine ⟨value, fun i j h => full.injective (Subtype.ext h), ?_, fun i => (full i).2⟩
  intro u
  let x : S := ⟨D.eigenvalue u, by simp [S, RealDiagonalization.spectralValues]⟩
  let j : Fin m := (S.orderIsoOfFin rfl).symm x
  refine ⟨Fin.castLE hmn j, ?_⟩
  have hj := congrArg (fun f => f j) hfull
  have hj' := congrArg Subtype.val hj
  have hx : (specEnum j).1 = D.eigenvalue u := by
    simp [j, x, specEnum]
  have hb : (base j).1 = (specEnum j).1 := rfl
  have hv : value (Fin.castLE hmn j) = (base j).1 := by
    simpa [value, Function.Embedding.trans_apply] using hj'
  exact hv.trans (hb.trans hx)

/-- The coordinate functional of an aggregate projector is exactly the total mass in the
corresponding repeated-eigenvalue cluster. -/
theorem anchor_projector_eq_clusterMass
    {n : ℕ} {A : RectMatrix n n} (D : RealDiagonalization A)
    (mass left right : Fin n → ℝ)
    (hleft : left = Matrix.mulVec D.basisInv.transpose mass)
    (hright : Matrix.mulVec D.basisInv right = fun _ => 1) (x : ℝ) :
    ∑ a, left a * (∑ b, D.projector x a b * right b) =
      ∑ u, if D.eigenvalue u = x then mass u else 0 := by
  rw [hleft]
  change dotProduct (Matrix.mulVec D.basisInv.transpose mass)
      (Matrix.mulVec (D.projector x) right) = _
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
  unfold RealDiagonalization.projector
  have hmat : D.basisInv *
      (D.basis * Matrix.diagonal (fun i => if D.eigenvalue i = x then 1 else 0) *
        D.basisInv) =
      Matrix.diagonal (fun i => if D.eigenvalue i = x then 1 else 0) * D.basisInv := by
    calc
      _ = (D.basisInv * D.basis) *
          (Matrix.diagonal (fun i => if D.eigenvalue i = x then 1 else 0) *
            D.basisInv) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [D.inv_mul_basis, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, hmat, ← Matrix.mulVec_mulVec, hright]
  unfold dotProduct
  simp [Matrix.mulVec_diagonal]

/-- Collision-safe Lagrange projector weights form a valid finite probability vector.  Genuine
slots carry aggregate coordinate masses and dummy slots carry zero. -/
theorem exists_polynomialSpectralLaw
    {n : ℕ} {A : RectMatrix n n} (D : RealDiagonalization A)
    {radius : ℝ} (hradius : 0 < radius)
    (mass left right : Fin n → ℝ)
    (hmass : (∀ u, 0 ≤ mass u) ∧ ∑ u, mass u = 1)
    (hbound : ∀ u, D.eigenvalue u ∈ Set.Icc (-radius) radius)
    (hleft : left = Matrix.mulVec D.basisInv.transpose mass)
    (hright : Matrix.mulVec D.basisInv right = fun _ => 1) :
    ∃ value : Fin n → ℝ,
      Function.Injective value ∧
      (∀ u, ∃ i, value i = D.eigenvalue u) ∧
      (∀ i, value i ∈ Set.Icc (-radius) radius) ∧
      (∀ i, 0 ≤ ∑ a, left a *
        (∑ b, polynomialSpectralProjector A value i a b * right b)) ∧
      ∑ i, (∑ a, left a *
        (∑ b, polynomialSpectralProjector A value i a b * right b)) = 1 := by
  classical
  obtain ⟨value, hinj, hcomplete, hvalueBound⟩ :=
    exists_injective_spectralEnumeration D hradius hbound
  refine ⟨value, hinj, hcomplete, hvalueBound, ?_, ?_⟩
  · intro i
    rw [polynomialSpectralProjector_eq_projector_or_zero D value hinj hcomplete i]
    split_ifs with hi
    · rw [anchor_projector_eq_clusterMass D mass left right hleft hright]
      exact Finset.sum_nonneg fun u _ => by
        split_ifs
        · exact hmass.1 u
        · exact le_rfl
    · simp
  · have hslot (i : Fin n) :
        (∑ a, left a *
          (∑ b, polynomialSpectralProjector A value i a b * right b)) =
        ∑ u, if D.eigenvalue u = value i then mass u else 0 := by
      rw [polynomialSpectralProjector_eq_projector_or_zero D value hinj hcomplete i]
      split_ifs with hi
      · exact anchor_projector_eq_clusterMass D mass left right hleft hright _
      · have hnone (u : Fin n) : D.eigenvalue u ≠ value i := by
          intro h
          apply hi
          simp [RealDiagonalization.spectralValues, ← h]
        simp [hnone]
    simp_rw [hslot]
    rw [Finset.sum_comm]
    calc
      ∑ u, ∑ i, (if D.eigenvalue u = value i then mass u else 0) =
          ∑ u, mass u := by
        apply Finset.sum_congr rfl
        intro u _
        obtain ⟨i, hi⟩ := hcomplete u
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro j _ hji
          simp only [ite_eq_right_iff]
          intro h
          exact (hji (hinj (h.symm.trans hi.symm))).elim
        · simp
      _ = 1 := hmass.2

/-- Every complex eigenvalue of a real-diagonalized matrix is one of its real diagonal values. -/
theorem complexEigenvalue_mem_diagonal
    {n : ℕ} {A : RectMatrix n n} (D : RealDiagonalization A)
    {z : ℂ} (hz : ComplexMatrixEigenvalue A z) :
    ∃ u, z = D.eigenvalue u := by
  classical
  rcases hz with ⟨v, hv, hev⟩
  let w : Fin n → ℂ := fun i => ∑ j, (D.basisInv i j : ℂ) * v j
  have hw : w ≠ 0 := by
    intro hw0
    apply hv
    funext i
    have hrecover : ∑ j, (D.basis i j : ℂ) * w j = v i := by
      calc
        ∑ j, (D.basis i j : ℂ) * w j =
            ∑ j, ∑ r, (D.basis i j : ℂ) * (D.basisInv j r : ℂ) * v r := by
              simp [w, Finset.mul_sum, mul_assoc]
        _ = ∑ r, ((D.basis * D.basisInv) i r : ℝ) * v r := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro r _
              simp [Matrix.mul_apply, Finset.sum_mul, mul_assoc]
        _ = v i := by
          rw [D.basis_mul_inv]
          rw [Finset.sum_eq_single i]
          · simp [Matrix.one_apply]
          · intro r _ hri
            simp [Matrix.one_apply, Ne.symm hri]
          · simp
    rw [hw0] at hrecover
    simpa using hrecover.symm
  obtain ⟨u, hu⟩ : ∃ u, w u ≠ 0 := by
    by_contra h
    push_neg at h
    apply hw
    funext i
    exact h i
  have hsim : D.basisInv * A = Matrix.diagonal D.eigenvalue * D.basisInv := by
    calc
      D.basisInv * A = D.basisInv *
          (D.basis * Matrix.diagonal D.eigenvalue * D.basisInv) :=
        congrArg (fun M => D.basisInv * M) D.reconstruct
      _ = Matrix.diagonal D.eigenvalue * D.basisInv := by
        calc
          _ = (D.basisInv * D.basis) *
              (Matrix.diagonal D.eigenvalue * D.basisInv) := by
                simp only [Matrix.mul_assoc]
          _ = _ := by rw [D.inv_mul_basis, Matrix.one_mul]
  have hcoord (j : Fin n) :
      (D.eigenvalue u : ℂ) * (D.basisInv u j : ℂ) =
        ∑ r, (D.basisInv u r : ℂ) * (A r j : ℂ) := by
    have h := congrArg (fun M : RectMatrix n n => M u j) hsim
    simpa [Matrix.mul_apply, Matrix.diagonal_apply] using congrArg ((↑) : ℝ → ℂ) h.symm
  have hew : (D.eigenvalue u : ℂ) * w u = z * w u := by
    calc
      (D.eigenvalue u : ℂ) * w u =
          ∑ j, ((D.eigenvalue u : ℂ) * (D.basisInv u j : ℂ)) * v j := by
            simp [w, Finset.mul_sum, mul_assoc]
      _ = ∑ j, (∑ r, (D.basisInv u r : ℂ) * (A r j : ℂ)) * v j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hcoord]
      _ = ∑ r, (D.basisInv u r : ℂ) *
          (∑ j, (A r j : ℂ) * v j) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro r _
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ r, (D.basisInv u r : ℂ) * (z * v r) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [hev]
      _ = z * w u := by
            simp only [w, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r _
            ring
  exact ⟨u, (mul_right_cancel₀ hu hew.symm)⟩

end CausalSmith.Substrate.CollisionSafeSpectralLaw
