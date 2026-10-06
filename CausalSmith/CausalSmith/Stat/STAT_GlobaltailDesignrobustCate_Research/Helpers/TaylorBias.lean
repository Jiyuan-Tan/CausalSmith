module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Estimators
public import Causalean.Stat.Nonparametric.Approximation.HolderTaylorMonomial

/-! # Boundary-valid tensor Taylor approximation

The whole-space extension of a cube Hölder function supplies a polynomial in
the estimator's tensor basis at every centre. The error constant is uniform in
the centre, function, and bandwidth, including boundary cells.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open scoped BigOperators

/-- Every exponent vector of total degree at most the polynomial order occurs
in the tensor basis, including the constant monomial. -/
-- @node: tensorMultiIndex_covers_totalDegree
lemma tensorMultiIndex_covers_totalDegree {d m : ℕ} (e : Fin d → ℕ)
    (he : (∑ i, e i) ≤ m) :
    ∃ a : MultiIndex d m, ∀ i, (a i).val = e i := by
  classical
  refine ⟨fun i => ⟨e i, ?_⟩, fun _ => rfl⟩
  have hi : e i ≤ ∑ k, e k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
  omega

/-- Roadmap (3)--(7): one positive Taylor constant works for every cube-class
function, every expansion centre, and all widths up to one. Evaluation uses
only points in the original cube; the Taylor segment uses the ambient extension. -/
-- @node: holderOnCube_tensor_approx
lemma holderOnCube_tensor_approx (d : ℕ) (β L : ℝ) (hβ : 0 < β) (hL : 0 < L) :
    ∃ B : ℝ, 0 < B ∧
      ∀ f : (Fin d → ℝ) → ℝ, holderOnCube f β L →
        ∀ (b : Fin d → ℝ) (h : ℝ), 0 < h → h ≤ 1 →
          ∃ θ : MultiIndex d (polynomialOrder β) → ℝ,
            ∀ u : Fin d → ℝ, (∀ i, |u i| ≤ 1) → b + h • u ∈ cube d →
              |f (b + h • u) - ∑ a, θ a * monomial d (polynomialOrder β) u a| ≤
                B * L * h ^ β := by
  classical
  obtain ⟨A, hA, hext⟩ := holderOnCube_std_extension d β hβ
  let E := Fintype.equivFin (MultiIndex d (polynomialOrder β))
  let expo : Fin (Fintype.card (MultiIndex d (polynomialOrder β))) → (Fin d → ℕ) :=
    fun k i => (E.symm k i).val
  have hcover : ∀ e : Fin d → ℕ, (∑ i, e i) ≤ ⌈β⌉₊ - 1 → ∃ k, expo k = e := by
    intro e he
    have he' : (∑ i, e i) ≤ polynomialOrder β := he
    obtain ⟨a, ha⟩ := tensorMultiIndex_covers_totalDegree e he'
    refine ⟨E a, ?_⟩
    funext i
    change (E.symm (E a) i).val = e i
    rw [Equiv.symm_apply_apply]
    exact ha i
  obtain ⟨Cb, hCb, happrox⟩ :=
    Causalean.Stat.Nonparametric.holder_taylor_monomial_approx_uniform_center
      (L := A * L) (r := 2) hβ (mul_pos hA hL) (by norm_num) expo hcover
  refine ⟨(Cb + 1) * A, by positivity, ?_⟩
  intro f hf b h hh hh1
  obtain ⟨g, hg, hfg⟩ := hext f L hf
  obtain ⟨θ, hθ⟩ := happrox b Set.univ (by simp) g hg h hh (by linarith)
  refine ⟨fun a => θ (E a), ?_⟩
  intro u hu hucube
  have ht := hθ u hu
  rw [hfg _ hucube]
  have hsum : (∑ a, θ (E a) * monomial d (polynomialOrder β) u a) =
      ∑ k, θ k * ∏ i, u i ^ expo k i := by
    simpa [monomial, expo] using
      E.sum_comp (fun k => θ k * ∏ i, u i ^ expo k i)
  rw [hsum]
  apply ht.trans
  have hscale : Cb * (A * L) ≤ ((Cb + 1) * A) * L := by
    nlinarith [mul_pos hA hL]
  exact mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hh.le _)

/-- Every dyadic width is positive and at most one. -/
-- @node: dyadicWidth_mem_Ioc
lemma dyadicWidth_mem_Ioc (j : ℕ) : dyadicWidth j ∈ Set.Ioc (0 : ℝ) 1 := by
  unfold dyadicWidth
  constructor
  · positivity
  · exact (div_le_one (by positivity : (0 : ℝ) < 2 ^ j)).mpr
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

/-- The entire closed cell, including an outer face, lies in the unit cube. -/
-- @node: closedDyadicCell_subset_cube
lemma closedDyadicCell_subset_cube (d j : ℕ) (Q : Fin d → Fin (2 ^ j))
    (u : Fin d → ℝ) (hu : u ∈ cube d) :
    cellOrigin d j Q + dyadicWidth j • u ∈ cube d := by
  have hh := (dyadicWidth_mem_Ioc j).1
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  intro i _
  have hui : u i ∈ Set.Icc (0 : ℝ) 1 := hu i (by simp)
  have hQi : ((Q i).val : ℝ) + 1 ≤ (2 : ℝ) ^ j := by
    exact_mod_cast (show (Q i).val + 1 ≤ 2 ^ j by omega)
  rcases hui with ⟨hui0, hui1⟩
  change ((Q i).val : ℝ) * dyadicWidth j + dyadicWidth j * u i ∈ Set.Icc (0 : ℝ) 1
  constructor
  · positivity
  · calc
      _ ≤ ((Q i).val + 1 : ℝ) * dyadicWidth j := by nlinarith
      _ ≤ ((2 : ℝ) ^ j) * dyadicWidth j := mul_le_mul_of_nonneg_right hQi hh.le
      _ = 1 := by unfold dyadicWidth; exact mul_one_div_cancel hpow.ne'

/-- Truncating the floor to the last cell includes the right endpoint while
keeping the point between its cell's two closed faces. -/
-- @node: clippedFloor_bounds
lemma clippedFloor_bounds (N : ℕ) (hN : 0 < N) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    let k := min (Nat.floor ((N : ℝ) * x)) (N - 1)
    (k : ℝ) ≤ (N : ℝ) * x ∧ (N : ℝ) * x ≤ (k : ℝ) + 1 := by
  dsimp only
  constructor
  · exact (Nat.cast_le.mpr (min_le_left _ _)).trans
      (Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) hx.1))
  · by_cases hk : Nat.floor ((N : ℝ) * x) ≤ N - 1
    · rw [min_eq_left hk]
      exact (Nat.lt_floor_add_one _).le
    · rw [min_eq_right (by omega)]
      have hcast : ((N - 1 : ℕ) : ℝ) + 1 = N := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
        ring
      rw [hcast]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) hx.2

/-- Normalizing a point in its owned dyadic cell gives a unit-cube direction,
including points on the outer boundary. -/
-- @node: normalizedDyadicPoint_mem_cube
lemma normalizedDyadicPoint_mem_cube (d j : ℕ) (Q : Fin d → Fin (2 ^ j))
    (x : Fin d → ℝ) (hx : x ∈ cube d) (hQ : x ∈ dyadicCell d j Q) :
    (fun i => (x i - cellOrigin d j Q i) / dyadicWidth j) ∈ cube d := by
  have hindex : cellIndex d j x = Q := hQ
  intro i _
  have hfaces := clippedFloor_bounds (2 ^ j) (by positivity) (x i) (hx i (by simp))
  have hval : (Q i).val = min (Nat.floor ((2 : ℝ) ^ j * x i)) (2 ^ j - 1) := by
    rw [← hindex]
    rfl
  have hfaces' : ((Q i).val : ℝ) ≤ (2 : ℝ) ^ j * x i ∧
      (2 : ℝ) ^ j * x i ≤ ((Q i).val : ℝ) + 1 := by
    simpa only [hval, Nat.cast_pow, Nat.cast_ofNat] using hfaces
  have heq : (x i - cellOrigin d j Q i) / dyadicWidth j =
      (2 : ℝ) ^ j * x i - (Q i).val := by
    unfold cellOrigin dyadicWidth
    have hp : (2 : ℝ) ^ j ≠ 0 := by positivity
    field_simp
  change (x i - cellOrigin d j Q i) / dyadicWidth j ∈ Set.Icc (0 : ℝ) 1
  rw [heq]
  exact ⟨sub_nonneg.mpr hfaces'.1, by linarith [hfaces'.2]⟩

/-- The roadmap's cell Taylor polynomial has uniformly bounded error on every
closed dyadic cell; hence the same coefficient vector works on each owned subcell. -/
-- @node: holderOnCube_dyadic_tensor_approx
lemma holderOnCube_dyadic_tensor_approx (d : ℕ) (β L : ℝ)
    (hβ : 0 < β) (hL : 0 < L) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : (Fin d → ℝ) → ℝ, holderOnCube f β L →
      ∀ (j : ℕ) (Q : Fin d → Fin (2 ^ j)),
        ∃ θ : MultiIndex d (polynomialOrder β) → ℝ,
          ∀ u ∈ cube d,
            |f (cellOrigin d j Q + dyadicWidth j • u) -
              ∑ a, θ a * monomial d (polynomialOrder β) u a| ≤
                B * L * (dyadicWidth j) ^ β := by
  obtain ⟨B, hB, happrox⟩ := holderOnCube_tensor_approx d β L hβ hL
  refine ⟨B, hB, ?_⟩
  intro f hf j Q
  obtain ⟨θ, hθ⟩ := happrox f hf (cellOrigin d j Q) (dyadicWidth j)
    (dyadicWidth_mem_Ioc j).1 (dyadicWidth_mem_Ioc j).2
  refine ⟨θ, ?_⟩
  intro u hu
  apply hθ u _ (closedDyadicCell_subset_cube d j Q u hu)
  intro i
  have hi : u i ∈ Set.Icc (0 : ℝ) 1 := hu i (by simp)
  rw [abs_of_nonneg hi.1]
  exact hi.2

/-- Roadmap (7) in the exact normalized coordinates used by the estimator:
one coefficient vector controls every cube point owned by a given cell. -/
-- @node: holderOnCube_ownedCell_tensor_approx
lemma holderOnCube_ownedCell_tensor_approx (d : ℕ) (β L : ℝ)
    (hβ : 0 < β) (hL : 0 < L) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : (Fin d → ℝ) → ℝ, holderOnCube f β L →
      ∀ (j : ℕ) (Q : Fin d → Fin (2 ^ j)),
        ∃ θ : MultiIndex d (polynomialOrder β) → ℝ,
          ∀ x ∈ cube d, x ∈ dyadicCell d j Q →
            |f x - ∑ a, θ a * monomial d (polynomialOrder β)
              (fun i => (x i - cellOrigin d j Q i) / dyadicWidth j) a| ≤
                B * L * (dyadicWidth j) ^ β := by
  obtain ⟨B, hB, happrox⟩ := holderOnCube_dyadic_tensor_approx d β L hβ hL
  refine ⟨B, hB, ?_⟩
  intro f hf j Q
  obtain ⟨θ, hθ⟩ := happrox f hf j Q
  refine ⟨θ, ?_⟩
  intro x hx hQ
  have h := hθ _ (normalizedDyadicPoint_mem_cube d j Q x hx hQ)
  have heq : cellOrigin d j Q + dyadicWidth j •
      (fun i => (x i - cellOrigin d j Q i) / dyadicWidth j) = x := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_div_cancel₀ _ (dyadicWidth_mem_Ioc j).1.ne']
    ring
  simpa only [heq] using h

/-- Roadmap (7) for the treated regression, with a constant uniform over laws,
levels, and cells in the fixed class. -/
-- @node: treated_dyadic_tensor_approx
lemma treated_dyadic_tensor_approx (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B : ℝ, 0 < B ∧ ∀ P : Law d, LawClass d β γ C L M P →
      ∀ (j : ℕ) (Q : Fin d → Fin (2 ^ j)),
        ∃ θ : MultiIndex d (polynomialOrder β) → ℝ,
          ∀ x ∈ cube d, x ∈ dyadicCell d j Q →
            |P.mu1 x - ∑ a, θ a * monomial d (polynomialOrder β)
              (fun i => (x i - cellOrigin d j Q i) / dyadicWidth j) a| ≤
                B * L * (dyadicWidth j) ^ β := by
  obtain ⟨B, hB, happrox⟩ := holderOnCube_ownedCell_tensor_approx d β L
    hparam.2.1 hparam.2.2.2.2.1
  exact ⟨B, hB, fun P hP => happrox P.mu1 hP.treatedHolder⟩

/-- Roadmap (C7)--(C9) for the control regression uses the same ambient
Taylor argument and the same tensor geometry as the treated arm. -/
-- @node: control_dyadic_tensor_approx
lemma control_dyadic_tensor_approx (d : ℕ) (β L : ℝ)
    (hβ : 0 < β) (hL : 0 < L) :
    ∃ B : ℝ, 0 < B ∧ ∀ P : Law d, ControlHolder P β L →
      ∀ (j : ℕ) (Q : Fin d → Fin (2 ^ j)),
        ∃ θ : MultiIndex d (polynomialOrder β) → ℝ,
          ∀ x ∈ cube d, x ∈ dyadicCell d j Q →
            |P.mu0 x - ∑ a, θ a * monomial d (polynomialOrder β)
              (fun i => (x i - cellOrigin d j Q i) / dyadicWidth j) a| ≤
                B * L * (dyadicWidth j) ^ β := by
  obtain ⟨B, hB, happrox⟩ := holderOnCube_ownedCell_tensor_approx d β L hβ hL
  exact ⟨B, hB, fun P hP => happrox P.mu0 hP⟩

end CausalSmith.Stat.GlobalTailDesignRobustCate
