module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.CompactHull

/-!
# Finite-dimensional constrained feature separation

A compact joint target-and-constraint range has a fiber with quantitative
target width whenever affine functions of the constraint coordinates cannot
uniformly approximate the target coordinate.
-/

public section

namespace Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/- The set is a closed slice of the product of two compact convex hulls.
  It is the domain on which the maximal target width of a constraint fiber
  is attained. -/

/-- A [compact joint feature set](hyp:hS) has [a compact set of pairs in its convex hull with matching constraint coordinates](goal). -/
theorem isCompact_matchingFiberPairs
    {m : ℕ} {S : Set (ℝ × (Fin m → ℝ))} (hS : IsCompact S) :
    IsCompact {p : (ℝ × (Fin m → ℝ)) × (ℝ × (Fin m → ℝ)) |
      p.1 ∈ convexHull ℝ S ∧ p.2 ∈ convexHull ℝ S ∧ p.1.2 = p.2.2} := by
  have hC : IsCompact (convexHull ℝ S) :=
    isCompact_convexHull_finiteDimensional hS
  have hEq : IsClosed {p : (ℝ × (Fin m → ℝ)) × (ℝ × (Fin m → ℝ)) |
      p.1.2 = p.2.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  convert (hC.prod hC).inter_right hEq using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod, and_assoc]

/- Let `C = convexHull ℝ S`, compact by the preceding module. If every
  fiber of the projection `C → (Fin m → ℝ)` has target width below `δ`,
  separate the compact convex set of differences `C-C` from the vertical
  segment at height `δ`. The separating functional has a nonzero target
  coefficient; normalize it to obtain an affine approximant with uniform
  error below `δ` on `S`, contradicting `hgap`. Keep the endpoint case by
  taking maxima on compact fibers rather than a strict approximation bound. -/

/-- A [compact set of points consisting of a real target coordinate and finitely many constraint coordinates](hyp:hS), with a [positive gap size](hyp:hδ) such that [every constant plus linear combination of the constraint coordinates differs from the target coordinate by at least the gap at some point of the set](hyp:hgap), has [two convex-hull points sharing all constraint coordinates while their target coordinates are separated by that gap](goal). -/
theorem exists_matching_convexHull_of_compact_feature_gap
    {m : ℕ} {S : Set (ℝ × (Fin m → ℝ))} {δ : ℝ}
    (hS : IsCompact S) (hδ : 0 < δ)
    (hgap : ∀ α : ℝ, ∀ c : Fin m → ℝ,
      ∃ z ∈ S, δ ≤ |z.1 - (α + ∑ i, c i * z.2 i)|) :
    ∃ y₀ y₁ : ℝ × (Fin m → ℝ),
      y₀ ∈ convexHull ℝ S ∧ y₁ ∈ convexHull ℝ S ∧
      y₀.2 = y₁.2 ∧ δ ≤ |y₀.1 - y₁.1| := by
  classical
  let C : Set (ℝ × (Fin m → ℝ)) := convexHull ℝ S
  let d : ℝ × (Fin m → ℝ) := (δ, 0)
  let T : Set (ℝ × (Fin m → ℝ)) := (fun z => d + z) '' C
  have hC : IsCompact C := isCompact_convexHull_finiteDimensional hS
  have hconv : Convex ℝ C := convex_convexHull ℝ S
  have hS' : S.Nonempty := by
    obtain ⟨z, hz, _⟩ := hgap 0 0
    exact ⟨z, hz⟩
  have hC' : C.Nonempty := hS'.mono (subset_convexHull ℝ S)
  by_contra hno
  let P : Set ((ℝ × (Fin m → ℝ)) × (ℝ × (Fin m → ℝ))) :=
    {p | p.1 ∈ C ∧ p.2 ∈ C ∧ p.1.2 = p.2.2}
  have hP : IsCompact P := isCompact_matchingFiberPairs hS
  have hP' : P.Nonempty := by
    obtain ⟨z, hz⟩ := hC'
    exact ⟨(z, z), hz, hz, rfl⟩
  obtain ⟨p, hp, hpmax⟩ := hP.exists_isMaxOn hP'
    ((continuous_fst.fst.sub continuous_snd.fst).abs.continuousOn)
  have hpδ : |p.1.1 - p.2.1| < δ := by
    rcases hp with ⟨hp₁, hp₂, hpeq⟩
    by_contra hn
    apply hno
    exact ⟨p.1, p.2, hp₁, hp₂, hpeq, le_of_not_gt hn⟩
  have hwidth : ∀ x ∈ C, ∀ y ∈ C, x.2 = y.2 → |x.1 - y.1| < δ := by
    intro x hx y hy hxy
    have hle : |x.1 - y.1| ≤ |p.1.1 - p.2.1| := by
      simpa [Pi.sub_apply] using
        (hpmax (show (x, y) ∈ P from ⟨hx, hy, hxy⟩))
    exact hle.trans_lt hpδ
  have hT : IsCompact T := hC.image (continuous_const.add continuous_id)
  have hTconv : Convex ℝ T := hconv.translate d
  have hdisj : Disjoint C T := Set.disjoint_left.mpr (by
    intro x hx hxt
    obtain ⟨y, hy, rfl⟩ := hxt
    have heq : (d + y).2 = y.2 := by simp [d]
    have hw := hwidth (d + y) hx y hy heq
    have : |(d + y).1 - y.1| = δ := by simp [d, abs_of_pos hδ]
    linarith)
  obtain ⟨f, u, v, hfu, huv, hvf⟩ :=
    geometric_hahn_banach_compact_closed hconv hC hTconv hT.isClosed hdisj
  let a : ℝ := f (1, (0 : Fin m → ℝ))
  have hd : f d = δ * a := by
    have hd' : d = δ • (1, (0 : Fin m → ℝ)) := by ext <;> simp [d]
    rw [hd', map_smul]
    simp [a, smul_eq_mul]
  obtain ⟨z₀, hz₀⟩ := hC'
  have ha : 0 < a := by
    have h₁ := hfu z₀ hz₀
    have h₂ := hvf (d + z₀) ⟨z₀, hz₀, rfl⟩
    rw [map_add, hd] at h₂
    by_contra! hna
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hδ) hna]
  have hcoord (z : ℝ × (Fin m → ℝ)) :
      f z = a * z.1 + ∑ i, (f (0, Pi.single i 1)) * z.2 i := by
    have hz : z = (z.1, (0 : Fin m → ℝ)) + (0, z.2) := by ext <;> simp
    have hfirst : f (z.1, (0 : Fin m → ℝ)) = a * z.1 := by
      have he : (z.1, (0 : Fin m → ℝ)) = z.1 • (1, (0 : Fin m → ℝ)) := by
        ext <;> simp
      rw [he, map_smul]
      simp [a, smul_eq_mul, mul_comm]
    have hsecond : f (0, z.2) = ∑ i, (f (0, Pi.single i 1)) * z.2 i := by
      have he : ((0 : ℝ), z.2) = ∑ i, z.2 i • ((0 : ℝ), Pi.single i (1 : ℝ)) := by
        apply Prod.ext
        · simp only [Prod.fst_sum, Prod.smul_fst, smul_zero,
            Finset.sum_const_zero]
        · funext j
          simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply]
          simpa using congrFun (pi_eq_sum_univ' z.2) j
      rw [he, map_sum]
      simp only [map_smul, smul_eq_mul]
      congr 1
      ext i
      ring
    calc
      f z = f ((z.1, 0) + (0, z.2)) := congrArg f hz
      _ = f (z.1, 0) + f (0, z.2) := map_add f _ _
      _ = _ := by rw [hfirst, hsecond]
  let α : ℝ := u / a
  let c : Fin m → ℝ := fun i => -(f (0, Pi.single i 1) / a)
  obtain ⟨z, hz, hgapz⟩ := hgap α c
  have hzC : z ∈ C := subset_convexHull ℝ S hz
  have hupper := hfu z hzC
  have hlower := hvf (d + z) ⟨z, hzC, rfl⟩
  rw [map_add, hd] at hlower
  have herror : z.1 - (α + ∑ i, c i * z.2 i) = (f z - u) / a := by
    rw [hcoord z]
    dsimp [α, c]
    have hsum : (∑ i, -(f (0, Pi.single i 1) / a) * z.2 i) =
        -(∑ i, f (0, Pi.single i 1) * z.2 i) / a := by
      calc
        _ = ∑ i, -(f (0, Pi.single i 1) * z.2 i) / a := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by simp [div_eq_mul_inv, Finset.sum_mul, Finset.sum_neg_distrib]
    rw [hsum]
    field_simp
    ring
  rw [herror] at hgapz
  have hlow : -(δ * a) < f z - u := by linarith
  have hupp : f z - u < δ * a := by linarith
  have habs : |(f z - u) / a| < δ := by
    rw [abs_lt]
    constructor
    · apply (lt_div_iff₀ ha).2
      nlinarith
    · apply (div_lt_iff₀ ha).2
      nlinarith
  linarith

end Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
