module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.LocalPolynomial.ResidualControl

/-! # Polynomial copies on fine cells
Affine changes of the degree-two Legendre basis preserve total degree. Thus
cellwise scalar multiples of coarse polynomials belong to the fine space.
-/

@[expose] public section
open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Triangular coefficients for a one-dimensional affine Legendre change.  Given [the specified input k](hyp:k), [the specified input j](hyp:j), [the specified input a](hyp:a), [the specified input b](hyp:b), [legendre affine coeff](goal) is the corresponding construction. -/
def legendreAffineCoeff (k j : ℕ) (a b : ℝ) : ℝ :=
  if k = 0 then (if j = 0 then 1 else 0)
  else if k = 1 then (if j = 0 then Real.sqrt 12*a else if j = 1 then b else 0)
  else (if j = 0 then Real.sqrt 5*(6*a^2+b^2/2-1/2)
    else if j = 1 then Real.sqrt 5*Real.sqrt 12*a*b else if j = 2 then b^2 else 0)

/-- An affine substitution in a Legendre entry uses only lower degrees.  Given [the specified input k](hyp:k), [the specified input hk](hyp:hk), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input t](hyp:t), [the legendre affine expansion conclusion](goal) holds. -/
lemma legendre_affine_expansion (k : ℕ) (hk : k ≤ 2) (a b t : ℝ) :
    legendre k (a+b*t) = ∑ j ∈ Finset.range (k+1),
      legendreAffineCoeff k j a b * legendre j t := by
  interval_cases k <;> norm_num [legendre, legendreAffineCoeff, Finset.sum_range_succ]
  · ring
  · ring_nf
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 12)]

/-- The change-of-basis matrix is triangular.  Given [the specified input k](hyp:k), [the specified input j](hyp:j), [the specified input hk](hyp:hk), [the specified input hj](hyp:hj), [the specified input a](hyp:a), [the specified input b](hyp:b), [the legendre affine coeff above conclusion](goal) holds. -/
lemma legendreAffineCoeff_above (k j : ℕ) (hk : k ≤ 2) (hj : k < j) (a b : ℝ) :
    legendreAffineCoeff k j a b = 0 := by
  interval_cases k
  · simp [legendreAffineCoeff, show j ≠ 0 by omega]
  · simp [legendreAffineCoeff, show j ≠ 0 by omega, show j ≠ 1 by omega]
  · simp [legendreAffineCoeff, show j ≠ 0 by omega, show j ≠ 1 by omega,
      show j ≠ 2 by omega]

/-- The tensor expansion keeps only multiindices of total degree at most two.  Given [the specified input d](hyp:d), [the specified input u](hyp:u), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input t](hyp:t), [the legendre tensor affine expansion conclusion](goal) holds. -/
lemma legendre_tensor_affine_expansion {d : ℕ} (u : PolyIdx d)
    (a b t : Fin d → ℝ) :
    (∏ i, legendre (u.1 i) (a i+b i*t i)) =
      ∑ v : PolyIdx d, ∏ i, legendreAffineCoeff (u.1 i) (v.1 i) (a i) (b i) *
        legendre (v.1 i) (t i) := by
  classical
  have hu (i : Fin d) : u.1 i ≤ 2 :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (u.1 j)) (Finset.mem_univ i)).trans u.2
  simp_rw [legendre_affine_expansion _ (hu _) ]
  rw [Finset.prod_univ_sum]
  let s := Fintype.piFinset (fun i => Finset.range (u.1 i+1))
  have hs {v : Fin d → ℕ} : v ∈ s ↔ ∀ i, v i ≤ u.1 i := by
    simp [s, Fintype.mem_piFinset, Nat.lt_succ_iff]
  let toPoly := fun v (hv : v ∈ s) =>
    (⟨v, (Finset.sum_le_sum (fun i _ => (hs.mp hv) i)).trans u.2⟩ : PolyIdx d)
  calc
    _ = ∑ v ∈ Finset.univ.filter (fun v : PolyIdx d => ∀ i, v.1 i ≤ u.1 i),
        ∏ i, legendreAffineCoeff (u.1 i) (v.1 i) (a i) (b i) * legendre (v.1 i) (t i) := by
      apply Finset.sum_bij toPoly
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hs.mp hv
      · intro v hv w hw he
        exact congrArg Subtype.val he
      · intro v hv
        exact ⟨v.1, hs.mpr (Finset.mem_filter.mp hv).2, Subtype.ext (by rfl)⟩
      · intro v hv
        rfl
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro v _ hv
      have hn : ¬ ∀ i, v.1 i ≤ u.1 i := by simpa using hv
      obtain ⟨i, hi⟩ := not_forall.mp hn
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [legendreAffineCoeff_above _ _ (hu i) (Nat.lt_of_not_ge hi), zero_mul]

/-- A separate scalar on each cell times a coarse entry is a fine-basis expansion.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the specified input c](hyp:c), [the cellwise coarse expansion conclusion](goal) holds. -/
lemma cellwise_coarse_expansion {d : ℕ} (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hJ : 1 ≤ J) (u : PolyIdx d) (c : (Fin d → Fin J) → ℝ) :
    ∃ v : FineIdx d J → ℝ, ∀ (z : Fin d → Fin J) (x : Cov d),
      x ∈ cell h J z → (∑ i, fineBasis h J x i*v i) = c z*coarseBasis h x u := by
  classical
  let center := fun (z : Fin d → Fin J) (i : Fin d) =>
    1/2-h/2+((z i:ℝ)+1/2)*(h/J)
  let a := fun z i => (center z i-1/2)/h
  let b : ℝ := 1/(J:ℝ)
  let coeff := fun z (w : PolyIdx d) => ∏ i,
    legendreAffineCoeff (u.1 i) (w.1 i) (a z i) b
  let root := Real.sqrt ((J:ℝ)^d)
  have hj : (J:ℝ) ≠ 0 := by exact_mod_cast (show J ≠ 0 by omega)
  have hr : root ≠ 0 := (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < (J:ℝ)^d)).ne'
  refine ⟨fun i => c i.1*coeff i.1 i.2/root, ?_⟩
  intro z x hx
  rw [Fintype.sum_prod_type, Finset.sum_eq_single z]
  · have ht (i : Fin d) : a z i+b*((x i-center z i)/(h/J)) = (x i-1/2)/h := by
      dsimp [a, b]
      field_simp
      <;> ring
    have he := legendre_tensor_affine_expansion u (a z) (fun _ => b)
      (fun i => (x i-center z i)/(h/J))
    simp_rw [ht] at he
    change coarseBasis h x u = _ at he
    rw [he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp only [fineBasis, hx, if_true]
    change root*(∏ i, legendre (w.1 i) ((x i-center z i)/(h/J)))*
      (c z*coeff z w/root) = _
    rw [Finset.prod_mul_distrib]
    dsimp [coeff]
    field_simp
    simp only [mul_comm]
    ring
  · intro w _ hw
    have hn : x ∉ cell h J w := fun hw' => hw (cell_index_unique d h J hh hJ x w z hw' hx)
    simp [fineBasis, hn]
  · simp

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
