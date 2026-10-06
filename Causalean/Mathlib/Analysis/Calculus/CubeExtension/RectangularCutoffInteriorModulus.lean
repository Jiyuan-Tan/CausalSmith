module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ConvexJetLipschitz
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ProductJetDifference
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoffJetBounds

/-!
# Interior top jet modulus for a cutoff response

This module isolates the product estimate at pairs of points strictly inside
the cutoff box. A separate closure argument transfers it to the box faces.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open scoped ContDiff

/-- Uniform bounds and a Lipschitz estimate imply a Hölder estimate with twice
the uniform constant when the exponent lies in `(0, 1]`. -/
private theorem norm_sub_le_two_mul_rpow_of_lipschitz
    {E : Type*} [NormedAddCommGroup E] {a b : E}
    {A t s : ℝ} (hA : 0 ≤ A) (ht : 0 ≤ t) (hs : 0 < s) (hs1 : s ≤ 1)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ A)
    (hlip : ‖a - b‖ ≤ A * t) :
    ‖a - b‖ ≤ (2 * A) * t ^ s := by
  by_cases hsmall : t ≤ 1
  · have hpow : t ≤ t ^ s := Real.self_le_rpow_of_le_one ht hsmall hs1
    have hnonneg : 0 ≤ t ^ s := Real.rpow_nonneg ht _
    calc
      ‖a - b‖ ≤ A * t := hlip
      _ ≤ A * t ^ s := mul_le_mul_of_nonneg_left hpow hA
      _ ≤ (2 * A) * t ^ s := by nlinarith
  · have hone : 1 ≤ t := le_of_lt (lt_of_not_ge hsmall)
    have hpow : 1 ≤ t ^ s := Real.one_le_rpow hone hs.le
    have htri : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
    have hnonneg : 0 ≤ A := hA
    calc
      ‖a - b‖ ≤ ‖a‖ + ‖b‖ := htri
      _ ≤ 2 * A := by linarith
      _ ≤ (2 * A) * t ^ s := by nlinarith

/-- If [0 < s](hyp:hs) and [s ≤ 1](hyp:hs1), [the box with corners lo, hi
strictly contains the normalized cube](hyp:hmargin), [χ is smooth](hyp:hχ)
[with closed support inside the open box](hyp:hsupp), and [its ambient
derivatives of every order up to m + 1 are bounded in operator norm by
B ≥ 0](hyp:hB,hχbound), then [there is a positive constant C such that for every
response v in the intrinsic Hölder ball of order m, exponent s and radius R ≥ 0
on the closed box, the order-m ambient derivatives of the zero extension of χ·v
at any two points x, y of the open box differ in norm by at most
C·R·‖x − y‖^s](goal).

Use `norm_iteratedFDerivWithin_mul_sub_le` for the cutoff product. For lower
response jets, apply `norm_iteratedFDerivWithin_sub_le_of_succ_bound` on the
convex box; for cutoff jets, use the next derivative bound. Convert Lipschitz
bounds to `s`-Hölder bounds at distances below one and use the global jet
bounds at distances at least one. At interior points the within-set product
jet equals the ambient jet of the zero extension. The coefficient can be chosen
explicitly from `B`, the coordinate-to-full-jet constant, and the finite
binomial sum. First establish uniform full-jet bounds for `v` from
`hv.derivBound`, plus a full top-jet modulus from `hv.modulus`. For `j < m`,
the `j + 1` bound gives a Lipschitz estimate on `rectBox`; use the two-range
argument to get an `s`-Hölder estimate for every `j ≤ m`. Apply the same
argument globally to smooth cutoff jets through order `m`, using `hχbound`
through `m + 1`. Then bound each summand of the product-jet difference theorem;
only after this convert interior within-box jets to ambient jets by local
equality of `rectCutoffExtension` with `χ * v`. -/
theorem exists_rectCutoffExtension_interior_modulus_constant (d m : ℕ) (s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (lo hi : Fin d → ℝ) (hmargin : ∀ i, lo i < -1 ∧ 1 < hi i)
    (χ : (Fin d → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ rectOpenBox lo hi)
    (B : ℝ) (hB : 0 ≤ B)
    (hχbound : ∀ j ≤ m + 1, ∀ x,
      ‖iteratedFDeriv ℝ j χ x‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v : (Fin d → ℝ) → ℝ) (R : ℝ), 0 ≤ R →
        HolderBallOn (rectBox lo hi) m s R v →
        ∀ x ∈ rectOpenBox lo hi, ∀ y ∈ rectOpenBox lo hi,
          ‖iteratedFDeriv ℝ m (rectCutoffExtension lo hi χ v) x -
            iteratedFDeriv ℝ m (rectCutoffExtension lo hi χ v) y‖
              ≤ C * R * ‖x - y‖ ^ s := by
  classical
  obtain ⟨K, hK, hcoord⟩ := exists_coord_multilinear_norm_constant d m
  let C : ℝ := 4 * B * K * (2 : ℝ) ^ m + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro v R hR hv x hx y hy
  let S := rectBox lo hi
  have hwidth : ∀ i, lo i < hi i := by
    intro i
    have h := hmargin i
    linarith
  have huniq : UniqueDiffOn ℝ S := uniqueDiffOn_rectBox lo hi hwidth
  have hconv : Convex ℝ S := by
    have hbox : S = Set.univ.pi (fun i : Fin d => Set.Icc (lo i) (hi i)) := by
      ext z
      simp [S, rectBox, Pi.le_def, forall_and]
    rw [hbox]
    exact convex_pi (fun i _ => convex_Icc _ _)
  have hopen : IsOpen (rectOpenBox lo hi) := by
    have h := isOpen_set_pi (Set.finite_univ : (Set.univ : Set (Fin d)).Finite)
      (s := fun i => Set.Ioo (lo i) (hi i)) (fun i _ => isOpen_Ioo)
    simpa [rectOpenBox, Set.pi, Set.mem_Ioo] using h
  have hsub : rectOpenBox lo hi ⊆ S := by
    intro z hz i
    exact ⟨(hz i).1.le, (hz i).2.le⟩
  have hxS : x ∈ S := hsub hx
  have hyS : y ∈ S := hsub hy
  have hinterior : rectOpenBox lo hi ⊆ interior S :=
    interior_maximal hsub hopen
  have hxcl : x ∈ closure (interior S) :=
    subset_closure (hinterior hx)
  have hycl : y ∈ closure (interior S) :=
    subset_closure (hinterior hy)
  have hχreg : ContDiffOn ℝ m χ S :=
    hχ.contDiffOn.of_le (by exact_mod_cast le_top)
  have hχreg' : ContDiffOn ℝ (m + 1) χ S :=
    hχ.contDiffOn.of_le (by exact_mod_cast le_top)
  have hχjet (j : ℕ) (hj : j ≤ m + 1) (z : Fin d → ℝ) (hz : z ∈ S) :
      ‖iteratedFDerivWithin ℝ j χ S z‖ ≤ B := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv huniq
      (hχ.contDiffAt.of_le (by exact_mod_cast le_top)) hz]
    exact hχbound j hj z
  have hvjet (j : ℕ) (hj : j ≤ m) (z : Fin d → ℝ) (hz : z ∈ S) :
      ‖iteratedFDerivWithin ℝ j v S z‖ ≤ K * R := by
    apply hcoord j hj _ R hR
    intro f
    simpa only [coordJetOn, Real.norm_eq_abs] using hv.derivBound j hj f z hz
  have hvtop :
      ‖iteratedFDerivWithin ℝ m v S x -
        iteratedFDerivWithin ℝ m v S y‖ ≤ K * R * ‖x - y‖ ^ s := by
    have hnonneg : 0 ≤ R * ‖x - y‖ ^ s := by positivity
    have h := hcoord m le_rfl
      (iteratedFDerivWithin ℝ m v S x -
        iteratedFDerivWithin ℝ m v S y)
      (R * ‖x - y‖ ^ s) hnonneg
    have hc : ∀ f : Fin m → Fin d,
        |(iteratedFDerivWithin ℝ m v S x -
          iteratedFDerivWithin ℝ m v S y)
          (fun k => Pi.single (f k) (1 : ℝ))| ≤
          R * ‖x - y‖ ^ s := by
      intro f
      simpa only [sub_apply, coordJetOn] using hv.modulus f x hxS y hyS
    exact (h hc).trans_eq (by ring)
  have hvmod (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDerivWithin ℝ j v S x -
        iteratedFDerivWithin ℝ j v S y‖ ≤
          (2 * (K * R)) * ‖x - y‖ ^ s := by
    by_cases htop : j = m
    · subst j
      have hp : 0 ≤ ‖x - y‖ ^ s := by positivity
      calc
        _ ≤ K * R * ‖x - y‖ ^ s := hvtop
        _ ≤ (2 * (K * R)) * ‖x - y‖ ^ s := by
          have hKR : 0 ≤ K * R := mul_nonneg hK.le hR
          nlinarith
    · have hjlt : j < m := Nat.lt_of_le_of_ne hj htop
      have hnext (z : Fin d → ℝ) (hz : z ∈ S) :
          ‖iteratedFDerivWithin ℝ (j + 1) v S z‖ ≤ K * R :=
        hvjet (j + 1) (by omega) z hz
      have hlip := norm_iteratedFDerivWithin_sub_le_of_succ_bound
        hconv huniq hv.regularity hjlt hnext hxS hyS
      exact norm_sub_le_two_mul_rpow_of_lipschitz
        (mul_nonneg hK.le hR) (norm_nonneg _) hs hs1
        (hvjet j hj x hxS) (hvjet j hj y hyS) hlip
  have hχmod (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDerivWithin ℝ j χ S x -
        iteratedFDerivWithin ℝ j χ S y‖ ≤
          (2 * B) * ‖x - y‖ ^ s := by
    have hnext (z : Fin d → ℝ) (hz : z ∈ S) :
        ‖iteratedFDerivWithin ℝ (j + 1) χ S z‖ ≤ B :=
      hχjet (j + 1) (by omega) z hz
    have hlip := norm_iteratedFDerivWithin_sub_le_of_succ_bound
      hconv huniq hχreg' (by omega : j < m + 1) hnext hxS hyS
    exact norm_sub_le_two_mul_rpow_of_lipschitz hB (norm_nonneg _) hs hs1
      (hχjet j (by omega) x hxS) (hχjet j (by omega) y hyS) hlip
  have hproduct := norm_iteratedFDerivWithin_mul_sub_le
    huniq hχreg hv.regularity hxS hyS hxcl hycl
  have hsum :
      (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (‖iteratedFDerivWithin ℝ i χ S x -
          iteratedFDerivWithin ℝ i χ S y‖ *
            ‖iteratedFDerivWithin ℝ (m - i) v S x‖ +
         ‖iteratedFDerivWithin ℝ i χ S y‖ *
            ‖iteratedFDerivWithin ℝ (m - i) v S x -
              iteratedFDerivWithin ℝ (m - i) v S y‖)) ≤
        (2 : ℝ) ^ m * ((4 * B * K * R) * ‖x - y‖ ^ s) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ((4 * B * K * R) * ‖x - y‖ ^ s) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hmi : m - i ≤ m := Nat.sub_le _ _
        have hp : 0 ≤ ‖x - y‖ ^ s := by positivity
        have hleft :
            ‖iteratedFDerivWithin ℝ i χ S x -
              iteratedFDerivWithin ℝ i χ S y‖ *
                ‖iteratedFDerivWithin ℝ (m - i) v S x‖ ≤
              ((2 * B) * ‖x - y‖ ^ s) * (K * R) := by
          gcongr
          · exact hχmod i hi'
          · exact hvjet (m - i) hmi x hxS
        have hright :
            ‖iteratedFDerivWithin ℝ i χ S y‖ *
              ‖iteratedFDerivWithin ℝ (m - i) v S x -
                iteratedFDerivWithin ℝ (m - i) v S y‖ ≤
              B * ((2 * (K * R)) * ‖x - y‖ ^ s) := by
          gcongr
          · exact hχjet i (by omega) y hyS
          · exact hvmod (m - i) hmi
        have hcoeff : 0 ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
        apply mul_le_mul_of_nonneg_left _ hcoeff
        calc
          _ ≤ ((2 * B) * ‖x - y‖ ^ s) * (K * R) +
              B * ((2 * (K * R)) * ‖x - y‖ ^ s) :=
                add_le_add hleft hright
          _ = (4 * B * K * R) * ‖x - y‖ ^ s := by ring
      _ = (2 : ℝ) ^ m * ((4 * B * K * R) * ‖x - y‖ ^ s) := by
        rw [← Finset.sum_mul]
        norm_cast
        rw [Nat.sum_range_choose]
  have heq : Set.EqOn (rectCutoffExtension lo hi χ v)
      (fun z => χ z * v z) S := by
    intro z hz
    simp [rectCutoffExtension, hz, S]
  have hfull : ContDiff ℝ m (rectCutoffExtension lo hi χ v) :=
    rectCutoffExtension_contDiff m lo hi χ v hχ hsupp hv.regularity
  have hjet (z : Fin d → ℝ) (hz : z ∈ S) :
      iteratedFDeriv ℝ m (rectCutoffExtension lo hi χ v) z =
        iteratedFDerivWithin ℝ m (fun w => χ w * v w) S z := by
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv huniq
      (hfull.contDiffAt.of_le le_rfl) hz]
    exact iteratedFDerivWithin_congr heq hz m
  rw [hjet x hxS, hjet y hyS]
  calc
    _ ≤ (2 : ℝ) ^ m * ((4 * B * K * R) * ‖x - y‖ ^ s) :=
      hproduct.trans hsum
    _ ≤ C * R * ‖x - y‖ ^ s := by
      dsimp [C]
      have hp : 0 ≤ ‖x - y‖ ^ s := by positivity
      nlinarith [mul_nonneg hR hp]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
