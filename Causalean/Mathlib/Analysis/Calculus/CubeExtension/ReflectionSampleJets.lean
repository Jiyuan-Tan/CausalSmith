module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.JetNorm
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionQuantitative

/-!
# Jets of inward samples and one-face reflections

This module bounds ambient jets of each inward sample on the open exterior
collar, then combines them into the corresponding finite one-face reflection.
Every sample point lies in the open cube, where ambient and intrinsic jets
agree. The affine map's operator norm is bounded by its dilation factor.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- For [the left face in coordinate i](hyp:i) and [a dilation index
q](hyp:q), [there is a positive constant C such that, for every response u in the
intrinsic Hölder ball of order m, exponent s and radius L ≥ 0 on the normalized
cube, every ambient derivative of order at most m of the composite
y ↦ u(inward sample of y) has operator norm at most C·L on the open exterior
collar](goal). The constant does not depend on the response or the radius. -/
theorem exists_leftFaceSample_jet_bound (d m : ℕ) (s : ℝ)
    (i : Fin d) (q : Fin (m + 1)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        ∀ j ≤ m, ∀ x ∈ leftOpenCubeCollar d m i,
          ‖iteratedFDeriv ℝ j (fun y => u (leftFaceSample d i q y)) x‖
            ≤ C * L := by
  classical
  obtain ⟨K, hK, hKbound⟩ := exists_full_intrinsic_jet_bounds d m s
  let a : Fin d → ℝ := leftFaceSample d i q 0
  let g : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) := {
    toFun := fun x j => if j = i then -((q : ℝ) + 1) * x j else x j
    map_add' := by
      intro x y
      ext j
      by_cases hj : j = i <;> simp [hj, mul_add]
    map_smul' := by
      intro c x
      ext j
      by_cases hj : j = i <;> simp [hj]
      ring
    cont := by
      apply continuous_pi
      intro j
      by_cases hj : j = i
      · subst j
        simp only
        exact (continuous_const.mul (continuous_apply i) :
          Continuous (fun x : Fin d → ℝ => -((q : ℝ) + 1) * x i))
      · simpa [hj] using (continuous_apply j)
  }
  have hsamp (y : Fin d → ℝ) : leftFaceSample d i q y = g y + a := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [g, a, leftFaceSample]
      ring
    · simp [g, a, leftFaceSample, hj]
  have hg : ‖g‖ ≤ (q : ℝ) + 1 := by
    apply g.opNorm_le_bound (by positivity)
    intro y
    have heq : g y = leftFaceSample d i q y - leftFaceSample d i q 0 := by
      rw [hsamp]
      simp [a]
    rw [heq]
    simpa using leftFaceSample_lipschitz d i q y 0
  refine ⟨K * ((q : ℝ) + 1) ^ m, mul_pos hK (pow_pos (by positivity) _), ?_⟩
  intro u L hL hu j hj x hx
  let S : Set (Fin d → ℝ) := {z | z + a ∈ openCube d}
  let f : (Fin d → ℝ) → ℝ := fun z => u (z + a)
  have hopen : IsOpen (openCube d) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hsub : openCube d ⊆ cube d := by
    intro z hz k
    exact ⟨(hz k trivial).1.le, (hz k trivial).2.le⟩
  have hSopen : IsOpen S := hopen.preimage (continuous_id.add continuous_const)
  have hSf : ContDiffOn ℝ m f S := by
    have htrans : ContDiff ℝ m (fun z : Fin d → ℝ => z + a) :=
      contDiff_id.add contDiff_const
    exact (hu.regularity.mono hsub).comp htrans.contDiffOn (fun z hz => hz)
  have hsrc : g x ∈ S := by
    change g x + a ∈ openCube d
    rw [← hsamp]
    exact leftFaceSample_mem_openCube i q x hx
  have htarget : ContDiffAt ℝ j (f ∘ g) x :=
    (hSf.comp_continuousLinearMap g).contDiffAt
      ((hSopen.preimage g.continuous).mem_nhds hsrc) |>.of_le
        (by exact_mod_cast hj)
  have hsource : ContDiffAt ℝ j f (g x) :=
    hSf.contDiffAt (hSopen.mem_nhds hsrc) |>.of_le
      (by exact_mod_cast hj)
  have hchain := g.iteratedFDerivWithin_comp_right hSf hSopen.uniqueDiffOn
    (hSopen.preimage g.continuous).uniqueDiffOn hsrc
    (show j ≤ (m : WithTop ℕ∞) by exact_mod_cast hj)
  have hjet : iteratedFDeriv ℝ j (fun y => u (leftFaceSample d i q y)) x =
      (iteratedFDeriv ℝ j u (leftFaceSample d i q x)).compContinuousLinearMap
        (fun _ => g) := by
    have hfun : (fun y => u (leftFaceSample d i q y)) = f ∘ g := by
      funext y
      simp [f, hsamp]
    rw [hfun, ← iteratedFDerivWithin_eq_iteratedFDeriv
      (hSopen.preimage g.continuous).uniqueDiffOn htarget hsrc]
    rw [hchain]
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hSopen.uniqueDiffOn hsource hsrc]
    rw [iteratedFDeriv_comp_add_right j a (g x)]
    rw [hsamp]
  rw [hjet]
  have hs : leftFaceSample d i q x ∈ cube d :=
    hsub (leftFaceSample_mem_openCube i q x hx)
  have hfull : ‖iteratedFDeriv ℝ j u (leftFaceSample d i q x)‖ ≤ K * L := by
    have hreg : ContDiffAt ℝ j u (leftFaceSample d i q x) :=
      (hu.regularity.mono hsub).contDiffAt
        (hopen.mem_nhds (leftFaceSample_mem_openCube i q x hx)) |>.of_le
          (by exact_mod_cast hj)
    have hcube : UniqueDiffOn ℝ (cube d) := by
      have hc : cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) := by
        ext z
        simp [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
          Pi.le_def, forall_and]
      rw [hc]
      exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num))
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv hcube hreg hs]
    exact (hKbound u L hL hu).1 j hj _ hs
  calc
    _ ≤ ‖iteratedFDeriv ℝ j u (leftFaceSample d i q x)‖ * ∏ _k : Fin j, ‖g‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ j u (leftFaceSample d i q x)‖ * ‖g‖ ^ j := by simp
    _ ≤ (K * L) * ((q : ℝ) + 1) ^ j := by gcongr
    _ ≤ (K * L) * ((q : ℝ) + 1) ^ m := by
      gcongr
      have hq : 0 ≤ ((q : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    _ = (K * ((q : ℝ) + 1) ^ m) * L := by ring

/-- If [s > 0](hyp:hs), then for [the left face in coordinate i](hyp:i) and [a
dilation index q](hyp:q) [there is a positive constant C such that, for every
response u in the intrinsic Hölder ball of order m, exponent s and radius L ≥ 0
on the normalized cube, the order-m ambient derivative of the composite
z ↦ u(inward sample of z) is s-Hölder with coefficient C·L between any two
points of the open exterior collar](goal). -/
theorem exists_leftFaceSample_top_modulus (d m : ℕ) (s : ℝ)
    (hs : 0 < s) (i : Fin d) (q : Fin (m + 1)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        ∀ x ∈ leftOpenCubeCollar d m i,
          ∀ y ∈ leftOpenCubeCollar d m i,
            ‖iteratedFDeriv ℝ m (fun z => u (leftFaceSample d i q z)) x -
              iteratedFDeriv ℝ m (fun z => u (leftFaceSample d i q z)) y‖
              ≤ C * L * ‖x - y‖ ^ s := by
  classical
  obtain ⟨K, hK, hKbound⟩ := exists_full_intrinsic_jet_bounds d m s
  let a : Fin d → ℝ := leftFaceSample d i q 0
  let g : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) := {
    toFun := fun x j => if j = i then -((q : ℝ) + 1) * x j else x j
    map_add' := by
      intro x y
      ext j
      by_cases hj : j = i <;> simp [hj, mul_add]
    map_smul' := by
      intro c x
      ext j
      by_cases hj : j = i <;> simp [hj]
      ring
    cont := by
      apply continuous_pi
      intro j
      by_cases hj : j = i
      · subst j
        simp only
        exact (continuous_const.mul (continuous_apply i) :
          Continuous (fun x : Fin d → ℝ => -((q : ℝ) + 1) * x i))
      · simpa [hj] using (continuous_apply j)
  }
  have hsamp (z : Fin d → ℝ) : leftFaceSample d i q z = g z + a := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [g, a, leftFaceSample]
      ring
    · simp [g, a, leftFaceSample, hj]
  have hg : ‖g‖ ≤ (q : ℝ) + 1 := by
    apply g.opNorm_le_bound (by positivity)
    intro z
    have heq : g z = leftFaceSample d i q z - leftFaceSample d i q 0 := by
      rw [hsamp]
      simp [a]
    rw [heq]
    simpa using leftFaceSample_lipschitz d i q z 0
  let S : Set (Fin d → ℝ) := {z | z + a ∈ openCube d}
  have hopen : IsOpen (openCube d) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hsub : openCube d ⊆ cube d := by
    intro z hz k
    exact ⟨(hz k trivial).1.le, (hz k trivial).2.le⟩
  have hSopen : IsOpen S := hopen.preimage (continuous_id.add continuous_const)
  have hcube : UniqueDiffOn ℝ (cube d) := by
    have hc : cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) := by
      ext z
      simp [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
        Pi.le_def, forall_and]
    rw [hc]
    exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num))
  refine ⟨K * ((q : ℝ) + 1) ^ m * ((q : ℝ) + 1) ^ s,
    mul_pos (mul_pos hK (pow_pos (by positivity) _))
      (Real.rpow_pos_of_pos (by positivity) _), ?_⟩
  intro u L hL hu x hx y hy
  let f : (Fin d → ℝ) → ℝ := fun z => u (z + a)
  have hSf : ContDiffOn ℝ m f S := by
    have htrans : ContDiff ℝ m (fun z : Fin d → ℝ => z + a) :=
      contDiff_id.add contDiff_const
    exact (hu.regularity.mono hsub).comp htrans.contDiffOn (fun z hz => hz)
  have hjet (z : Fin d → ℝ) (hz : z ∈ leftOpenCubeCollar d m i) :
      iteratedFDeriv ℝ m (fun w => u (leftFaceSample d i q w)) z =
        (iteratedFDeriv ℝ m u (leftFaceSample d i q z)).compContinuousLinearMap
          (fun _ => g) := by
    have hsrc : g z ∈ S := by
      change g z + a ∈ openCube d
      rw [← hsamp]
      exact leftFaceSample_mem_openCube i q z hz
    have htarget : ContDiffAt ℝ m (f ∘ g) z :=
      (hSf.comp_continuousLinearMap g).contDiffAt
        ((hSopen.preimage g.continuous).mem_nhds hsrc)
    have hsource : ContDiffAt ℝ m f (g z) :=
      hSf.contDiffAt (hSopen.mem_nhds hsrc)
    have hchain := g.iteratedFDerivWithin_comp_right hSf hSopen.uniqueDiffOn
      (hSopen.preimage g.continuous).uniqueDiffOn hsrc
      (show m ≤ (m : WithTop ℕ∞) by exact_mod_cast le_rfl)
    have hfun : (fun w => u (leftFaceSample d i q w)) = f ∘ g := by
      funext w
      simp [f, hsamp]
    rw [hfun, ← iteratedFDerivWithin_eq_iteratedFDeriv
      (hSopen.preimage g.continuous).uniqueDiffOn htarget hsrc]
    rw [hchain]
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hSopen.uniqueDiffOn hsource hsrc]
    rw [iteratedFDeriv_comp_add_right m a (g z)]
    rw [hsamp]
  have hxy : ‖iteratedFDeriv ℝ m u (leftFaceSample d i q x) -
      iteratedFDeriv ℝ m u (leftFaceSample d i q y)‖ ≤
      K * L * ‖leftFaceSample d i q x - leftFaceSample d i q y‖ ^ s := by
    have hreg (z : Fin d → ℝ) (hz : z ∈ leftOpenCubeCollar d m i) :
        ContDiffAt ℝ m u (leftFaceSample d i q z) :=
      (hu.regularity.mono hsub).contDiffAt
        (hopen.mem_nhds (leftFaceSample_mem_openCube i q z hz))
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv hcube (hreg x hx)
      (hsub (leftFaceSample_mem_openCube i q x hx))]
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv hcube (hreg y hy)
      (hsub (leftFaceSample_mem_openCube i q y hy))]
    exact (hKbound u L hL hu).2 _
      (hsub (leftFaceSample_mem_openCube i q x hx)) _
      (hsub (leftFaceSample_mem_openCube i q y hy))
  rw [hjet x hx, hjet y hy]
  have hcomp :
      (iteratedFDeriv ℝ m u (leftFaceSample d i q x)).compContinuousLinearMap
          (fun _ => g) -
        (iteratedFDeriv ℝ m u (leftFaceSample d i q y)).compContinuousLinearMap
          (fun _ => g) =
        (iteratedFDeriv ℝ m u (leftFaceSample d i q x) -
          iteratedFDeriv ℝ m u (leftFaceSample d i q y)).compContinuousLinearMap
            (fun _ => g) := by
    ext v
    simp
  rw [hcomp]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m u (leftFaceSample d i q x) -
          iteratedFDeriv ℝ m u (leftFaceSample d i q y)‖ *
          ∏ _k : Fin m, ‖g‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ m u (leftFaceSample d i q x) -
          iteratedFDeriv ℝ m u (leftFaceSample d i q y)‖ * ‖g‖ ^ m := by simp
    _ ≤ (K * L * ‖leftFaceSample d i q x -
          leftFaceSample d i q y‖ ^ s) * ((q : ℝ) + 1) ^ m := by gcongr
    _ ≤ (K * L * (((q : ℝ) + 1) * ‖x - y‖) ^ s) *
          ((q : ℝ) + 1) ^ m := by
      gcongr
      exact leftFaceSample_lipschitz d i q x y
    _ = (K * ((q : ℝ) + 1) ^ m * ((q : ℝ) + 1) ^ s) *
          L * ‖x - y‖ ^ s := by
      rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
      ring

/-- If [a response u is m times continuously differentiable within the closed
cube](hyp:hu), [j ≤ m](hyp:hj), and [x lies in the open exterior
collar](hyp:hx), then [the order-j ambient derivative of the one-face reflection
of u at x equals the weighted sum over q of a_q times the order-j ambient
derivative at x of the composite z ↦ u(inward sample of z with dilation index
q)](goal). -/
theorem leftFaceReflection_iteratedFDeriv_eq_sum
    (d m : ℕ) (i : Fin d) (a : Fin (m + 1) → ℝ)
    (u : (Fin d → ℝ) → ℝ) (hu : ContDiffOn ℝ m u (cube d))
    (j : ℕ) (hj : j ≤ m) (x : Fin d → ℝ)
    (hx : x ∈ leftOpenCubeCollar d m i) :
    iteratedFDeriv ℝ j (leftFaceReflection d m i a u) x =
      ∑ q : Fin (m + 1), a q •
        iteratedFDeriv ℝ j (fun z => u (leftFaceSample d i q z)) x := by
  classical
  have hcollar : IsOpen (leftOpenCubeCollar d m i) := by
    have hc : leftOpenCubeCollar d m i = Set.univ.pi (fun k : Fin d =>
        if k = i then Set.Ioo (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1)
        else Set.Ioo (-1 : ℝ) 1) := by
      ext z
      simp [leftOpenCubeCollar]
      constructor <;> intro h k <;> by_cases hk : k = i <;>
        simpa [hk] using h k
    rw [hc]
    apply isOpen_set_pi Set.finite_univ
    intro k hk
    split_ifs <;> exact isOpen_Ioo
  have hsub : openCube d ⊆ cube d := by
    intro z hz k
    exact ⟨(hz k trivial).1.le, (hz k trivial).2.le⟩
  have hsample (q : Fin (m + 1)) :
      ContDiffOn ℝ m (fun z => u (leftFaceSample d i q z))
        (leftOpenCubeCollar d m i) := by
    have hmap : ContDiff ℝ m (leftFaceSample d i q) := by
      rw [contDiff_pi]
      intro k
      by_cases h : k = i
      · subst k
        simpa [leftFaceSample] using
          (show ContDiff ℝ m (fun z : Fin d → ℝ =>
            -1 + ((q : ℝ) + 1) * (-1 - z i)) by fun_prop)
      · simpa [leftFaceSample, h] using
          (show ContDiff ℝ m (fun z : Fin d → ℝ => z k) by fun_prop)
    exact (hu.mono hsub).comp hmap.contDiffOn
      (fun z hz => leftFaceSample_mem_openCube i q z hz)
  have hxi : x i < -1 := by
    have hmem : x i ∈ Set.Ioo
        (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1) := by
      simpa [leftOpenCubeCollar] using hx i
    exact hmem.2
  have heq : leftFaceReflection d m i a u =ᶠ[nhds x]
      (fun z => ∑ q : Fin (m + 1), a q * u (leftFaceSample d i q z)) := by
    filter_upwards [(isOpen_lt (continuous_apply i) continuous_const).mem_nhds hxi]
      with z hz
    simp [leftFaceReflection, hz]
  rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
  rw [iteratedFDeriv_fun_sum_apply]
  · apply Finset.sum_congr rfl
    intro q hq
    have hreg : ContDiffAt ℝ j
        (fun z => u (leftFaceSample d i q z)) x :=
      ((hsample q).contDiffAt (hcollar.mem_nhds hx)).of_le
        (by exact_mod_cast hj)
    simpa only [smul_eq_mul] using
      (iteratedFDeriv_const_smul_apply' (a := a q) hreg)
  · intro q hq
    have hreg : ContDiffAt ℝ j
        (fun z => u (leftFaceSample d i q z)) x :=
      ((hsample q).contDiffAt (hcollar.mem_nhds hx)).of_le
        (by exact_mod_cast hj)
    simpa only [smul_eq_mul] using (hreg.const_smul (a q))

/-- For [the left face in coordinate i](hyp:i) and [fixed reflection
weights a](hyp:a), [there is a positive constant C such that, for every response
u in the intrinsic Hölder ball of order m, exponent s and radius L ≥ 0 on the
normalized cube, every ambient derivative of order at most m of the one-face
reflection of u has operator norm at most C·L on the open exterior
collar](goal). The constant may depend on the weights. -/
theorem exists_leftFaceReflection_jet_bound (d m : ℕ) (s : ℝ)
    (i : Fin d) (a : Fin (m + 1) → ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        ∀ j ≤ m, ∀ x ∈ leftOpenCubeCollar d m i,
          ‖iteratedFDeriv ℝ j (leftFaceReflection d m i a u) x‖ ≤ C * L := by
  classical
  choose C hC hbound using
    (fun q : Fin (m + 1) => exists_leftFaceSample_jet_bound d m s i q)
  refine ⟨1 + ∑ q : Fin (m + 1), |a q| * C q, ?_, ?_⟩
  · have hsum : 0 ≤ ∑ q : Fin (m + 1), |a q| * C q := by
      apply Finset.sum_nonneg
      intro q hq
      exact mul_nonneg (abs_nonneg _) (le_of_lt (hC q))
    linarith
  intro u L hL hu j hj x hx
  calc
    ‖iteratedFDeriv ℝ j (leftFaceReflection d m i a u) x‖ =
        ‖∑ q : Fin (m + 1), a q •
          iteratedFDeriv ℝ j (fun z => u (leftFaceSample d i q z)) x‖ := by
      rw [leftFaceReflection_iteratedFDeriv_eq_sum d m i a u hu.regularity j hj x hx]
    _ ≤ ∑ q : Fin (m + 1), ‖a q •
        iteratedFDeriv ℝ j (fun z => u (leftFaceSample d i q z)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q : Fin (m + 1), |a q| * (C q * L) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbound q u L hL hu j hj x hx) (abs_nonneg _)
    _ = (∑ q : Fin (m + 1), |a q| * C q) * L := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ (1 + ∑ q : Fin (m + 1), |a q| * C q) * L := by
      nlinarith

/-- If [s > 0](hyp:hs), then for [the left face in coordinate i](hyp:i) and [fixed
reflection weights a](hyp:a) [there is a positive constant C such that, for every
response u in the intrinsic Hölder ball of order m, exponent s and radius L ≥ 0
on the normalized cube, the order-m ambient derivative of the one-face
reflection of u is s-Hölder with coefficient C·L between any two points of the
open exterior collar](goal). -/
theorem exists_leftFaceReflection_top_modulus (d m : ℕ) (s : ℝ)
    (hs : 0 < s) (i : Fin d) (a : Fin (m + 1) → ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        ∀ x ∈ leftOpenCubeCollar d m i,
          ∀ y ∈ leftOpenCubeCollar d m i,
            ‖iteratedFDeriv ℝ m (leftFaceReflection d m i a u) x -
              iteratedFDeriv ℝ m (leftFaceReflection d m i a u) y‖
              ≤ C * L * ‖x - y‖ ^ s := by
  classical
  choose C hC hbound using
    (fun q : Fin (m + 1) => exists_leftFaceSample_top_modulus d m s hs i q)
  refine ⟨1 + ∑ q : Fin (m + 1), |a q| * C q, ?_, ?_⟩
  · have hsum : 0 ≤ ∑ q : Fin (m + 1), |a q| * C q := by
      apply Finset.sum_nonneg
      intro q hq
      exact mul_nonneg (abs_nonneg _) (le_of_lt (hC q))
    linarith
  intro u L hL hu x hx y hy
  have hjetx := leftFaceReflection_iteratedFDeriv_eq_sum d m i a u
    hu.regularity m le_rfl x hx
  have hjety := leftFaceReflection_iteratedFDeriv_eq_sum d m i a u
    hu.regularity m le_rfl y hy
  rw [hjetx, hjety, ← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  calc
    ‖∑ q : Fin (m + 1), a q •
        (iteratedFDeriv ℝ m (fun z => u (leftFaceSample d i q z)) x -
          iteratedFDeriv ℝ m (fun z => u (leftFaceSample d i q z)) y)‖
      ≤ ∑ q : Fin (m + 1), ‖a q •
          (iteratedFDeriv ℝ m (fun z => u (leftFaceSample d i q z)) x -
            iteratedFDeriv ℝ m (fun z => u (leftFaceSample d i q z)) y)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q : Fin (m + 1), |a q| * (C q * L * ‖x - y‖ ^ s) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbound q u L hL hu x hx y hy) (abs_nonneg _)
    _ = (∑ q : Fin (m + 1), |a q| * C q) * L * ‖x - y‖ ^ s := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ (1 + ∑ q : Fin (m + 1), |a q| * C q) * L * ‖x - y‖ ^ s := by
      have hp : 0 ≤ ‖x - y‖ ^ s := Real.rpow_nonneg (norm_nonneg _) _
      nlinarith

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
